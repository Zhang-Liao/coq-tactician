open Ltac_plugin
open Tacexpr
open Libobject
open CAst
open Equality
open Locus

type tac_ast = Then | Dispatch | Extend | Thens | Thens3parts | First | Complete | Solve | Or
             | Once | ExactlyOnce | IfThenCatch | Orelse | Do | Timeout | Repeat | Progress
             | Abstract | LetIn | Match | MatchGoal | Arg | Select | ML | Alias | Call
             | IntroPattern | Apply | Elim | Case | MutualFix | MutualCofix | Assert
             | Generalize | LetTac | InductionDestruct | Reduce | Change | Rewrite | RewriteMulti
             | Inversion

type tac_decomposition = Decompose | Keep | Both | Discard

module TacAstMap = Map.Make(struct
    type t = tac_ast
    let compare = compare
  end)
type tac_ast_map = tac_decomposition TacAstMap.t

let tac_ast_map_ref = Summary.ref TacAstMap.empty ~name:"DecompositionMap"

let get_ast_settings () = !tac_ast_map_ref

let tac_ast_setting : tac_ast_map -> obj =
  declare_object @@ global_object_nodischarge "TacticianDecompositionSetting"
    ~cache:(fun (_,m) -> tac_ast_map_ref := m)
    ~subst:None

let ast_setting_lookup ast = Option.default Keep (TacAstMap.find_opt ast (get_ast_settings ()))

let modify_ast_setting ast dec = Lib.add_anonymous_leaf
    (tac_ast_setting (TacAstMap.add ast dec (get_ast_settings ())))

let outer_record ast = match ast_setting_lookup ast with
  | Keep | Both -> true
  | Decompose | Discard -> false

let inner_record ast = match ast_setting_lookup ast with
  | Decompose | Both -> true
  | Keep | Discard -> false

let decompose_annotate (tac : glob_tactic_expr) (r : glob_tactic_expr -> glob_tactic_expr -> glob_tactic_expr) : glob_tactic_expr =
  let mkatom loc atom =
    let t = TacAtom (CAst.make ?loc:loc atom) in
    r t t in
  let tacthenfirst t1 t2 = TacThens3parts (t1, Array.of_list [t2], TacId [], Array.of_list []) in
  let tacthenlast  t1 t2 = TacThens3parts (t1, Array.of_list [], TacId [], Array.of_list [t2]) in
  let decompose_apply flg1 flg2 intro loc (ls : 'trm with_bindings_arg list) =
    let intro' = Option.map (fun (n, _) -> (n, None)) intro in
    let combiner = match intro with | None -> tacthenlast | Some _ -> tacthenfirst in
    let rec aux = function
      | [] -> assert false
      | [s] -> mkatom loc (TacApply (flg1, flg2, [s], intro))
      | s::ls -> combiner (mkatom loc (TacApply (flg1, flg2, [s], intro'))) (aux ls)
    in aux ls in
  let decompose_generalize loc ls =
    let rec aux = function
      | [] -> assert false
      | [s] -> mkatom loc (TacGeneralize [s])
      | s::ls -> TacThen (mkatom loc (TacGeneralize [s]), aux ls)
    in aux ls in
  let decompose_induction_destruct loc flg1 flg2 ls =
    let rec aux = function
      | [] -> assert false
      | [s] -> mkatom loc (TacInductionDestruct (flg1, flg2, ([s], None)))
      | s::ls -> TacThen (mkatom loc (TacInductionDestruct (flg1, flg2, ([s], None))), aux ls)
    in aux ls in
  let decompose_multi loc flg inc b trm by byorig mult = (* TODO: Maybe replace this with an OCaml-level tactic? *)
    let recname = CAst.make @@ Names.Id.of_string "rec" in
    let recname' = CAst.make @@ Names.Name.mk_name recname.v in
    let reccall = TacArg (CAst.make (Reference (ArgVar recname))) in
    let repeat tac = TacLetIn (true, [(recname', Tacexp (TacTry (tacthenfirst tac reccall)))], reccall) in
    let rec don n tac = if n > 0 then tacthenfirst tac (don (n-1) tac) else TacId [] in
    let onerewrite = TacRewrite (flg, [(b, Precisely 1, trm)], inc, by) in
    let at r = match mult with
      | Precisely 1 -> mkatom loc onerewrite
      | Precisely n -> r (don n (mkatom loc onerewrite))
      | RepeatStar -> r (repeat (mkatom loc onerewrite))
      | RepeatPlus -> r (tacthenfirst (mkatom loc onerewrite) (repeat (mkatom loc onerewrite)))
      | UpTo n -> r (don n (TacTry (mkatom loc onerewrite))) in
    let r = if outer_record RewriteMulti then r (TacAtom (CAst.make ?loc:loc (TacRewrite (flg, [(b, mult, trm)], inc, byorig)))) else fun x -> x in
    if inner_record RewriteMulti then at r else r (TacAtom (CAst.make ?loc:loc (TacRewrite (flg, [(b, mult, trm)], inc, by)))) in
  let decompose_rewrite loc flg inc ls by byorig =
    let rec aux = function
      | [] -> assert false
      | [(b, mult, trm)] -> decompose_multi loc flg inc b trm by byorig mult
      | (b, mult, trm)::ls -> TacTry (tacthenfirst (decompose_multi loc flg inc b trm by byorig mult) (aux ls))
    in aux ls in
  let rec annotate_atomic a : glob_tactic_expr =
    let router ast t = if outer_record ast then r (TacAtom a) t else t in
    let at = TacAtom a in
    match a.v with
    | TacIntroPattern _ -> router IntroPattern at
    | TacApply (flg1, flg2, ls, intro) ->
      let at = if (inner_record Apply) then decompose_apply flg1 flg2 intro a.loc ls else at in
      router Apply at
    | TacElim _ -> router Elim at
    | TacCase _ -> router Case at
    | TacMutualFix _ -> router MutualFix at
    | TacMutualCofix _ -> router MutualCofix at
    | TacAssert (flg, b, by, pat, term) ->
      let by = if inner_record Assert then Option.map (Option.map annotate) by else by in
      router Assert (TacAtom (CAst.make ?loc:a.loc (TacAssert (flg, b, by, pat, term))))
    | TacGeneralize gs ->
      let at = if inner_record Generalize then decompose_generalize a.loc (List.rev gs) else at in
      router Generalize at
    | TacLetTac _ -> router LetTac at
    (* This is induction .. using .., which is not decomposable *)
    | TacInductionDestruct (_, _, (_, Some _)) -> router InductionDestruct at
    (* TODO: induction a, b is not equal to induction a; induction b due to name mangling *)
    | TacInductionDestruct (true, _, _) -> router InductionDestruct at
    | TacInductionDestruct (flg1, flg2, (ts, None)) ->
      let at = if inner_record InductionDestruct then decompose_induction_destruct a.loc flg1 flg2 ts else at in
      router InductionDestruct at
    | TacReduce _ -> router Reduce at
    | TacChange _ -> router Change at
    | TacRewrite (flg1, ts, i, d) ->
      let at = if inner_record Rewrite then decompose_rewrite a.loc flg1 i ts (Option.map annotate d) d else at in
      router Rewrite at
    | TacInversion _ -> router Inversion at
  and annotate_arg x = match x with
    | TacGeneric _ -> x, r (* TODO: Deal with ssreflect stuff *)
    | ConstrMayEval _ -> x, r
    | Reference _ -> x, r
    | TacCall c -> (if inner_record Call then
        TacCall (CAst.map (fun (a, b) -> (a, List.map (fun a -> fst (annotate_arg x)) b)) c) else x), r
    | TacFreshId _ -> x, r
    | Tacexp t -> Tacexp (annotate t), fun x _ -> x
    | TacPretype _ -> x, r
    | TacNumgoals -> x, r
  (* TODO: Improve efficiency of the annotation recursion *)
  and annotate (tac : glob_tactic_expr) : glob_tactic_expr =
    let router ast t = if outer_record ast then r tac t else t in
    let rinner ast t = if inner_record ast then annotate t else t in
    match tac with
    | TacAtom a         ->                 annotate_atomic a
    | TacThen (t1, t2)  ->                 router Then (TacThen (rinner Then t1, rinner Then t2))
    | TacDispatch tl    ->                 router Dispatch (TacDispatch (List.map (rinner Dispatch) tl))
    | TacExtendTac (tl1, t, tl2) ->        router Extend (TacExtendTac (Array.map (rinner Extend) tl1,
                                                                        rinner Extend t,
                                                                        Array.map (rinner Extend) tl2))
    | TacThens (t1, tl) ->                 router Thens (TacThens (rinner Thens t1, List.map (rinner Thens) tl))
    | TacThens3parts (t1, tl1, t2, tl2) ->
      router Thens3parts (TacThens3parts (rinner Thens3parts t1,
                                           Array.map (rinner Thens3parts) tl1,
                                           rinner Thens3parts t2,
                                           Array.map (rinner Thens3parts) tl2))
    | TacFirst ts       ->                 router First (TacFirst (List.map (rinner First) ts))
    | TacComplete t     ->                 router Complete (TacComplete (rinner Complete t))
    | TacSolve ts       ->                 router Solve (TacSolve (List.map (rinner Solve) ts))
    | TacTry t          ->                 TacTry (annotate t) (* No need to record try *)
    | TacOr (t1, t2)    ->                 router Or (TacOr (rinner Or t1, rinner Or t2))
    | TacOnce t         ->                 router Once (TacOnce (rinner Once t))
    | TacExactlyOnce t  ->                 router ExactlyOnce (TacExactlyOnce (rinner ExactlyOnce t))
    | TacIfThenCatch (t1, t2, t3) ->       router IfThenCatch (TacIfThenCatch (rinner IfThenCatch t1,
                                                                               rinner IfThenCatch t2,
                                                                               rinner IfThenCatch t3))
    | TacOrelse (t1, t2) ->                router Orelse (TacOrelse (rinner Orelse t1, rinner Orelse t2))
    | TacDo (n, t) ->                      router Do (TacDo (n, rinner Do t))
    | TacTimeout (n, t)      ->            router Timeout (TacTimeout (n, rinner Timeout t))
    | TacTime (s, t)         ->            TacTime (s, annotate t) (* No need to record try *)
    | TacRepeat t       ->                 router Repeat (TacRepeat (rinner Repeat t))
    | TacProgress t     ->                 router Progress (TacProgress (rinner Progress t))
    | TacShowHyps t     ->                 TacShowHyps (annotate t) (* No need to record infoH *)
    | TacAbstract (t, id) ->               router Abstract (TacAbstract (rinner Abstract t, id))
    | TacId _           ->                 tac (* No need to record id *)
    | TacFail _         ->                 tac (* No need to record fail *)
    | TacLetIn (flg, ts, t) ->
      let ts = if inner_record LetIn then List.map (fun (a, b) -> (a, fst (annotate_arg b))) ts else ts in
      router LetIn (TacLetIn (flg, ts, rinner LetIn t))
    | TacMatch (flg, t, ts) ->
      router Match (TacMatch (flg, rinner Match t,
                              List.map (function | All t -> All (rinner Match t)
                                                 | Pat (c, p, t) -> Pat (c, p, rinner Match t)) ts))
    | TacMatchGoal (flg, d, ts) ->
      router MatchGoal (TacMatchGoal (
          flg, d, List.map (function | All t -> All (rinner MatchGoal t)
                                     | Pat (c, p, t) -> Pat (c, p, rinner MatchGoal t)) ts))
    | TacFun (args, t) -> TacFun (args, annotate t) (* Probably not outer-recordable *)
    | TacArg x ->
      let x', r = if inner_record Arg then annotate_arg x.v else x.v, r in
      let res = TacArg (CAst.make ?loc:x.loc x') in
      if outer_record Arg then r tac res else res
    | TacSelect (i, t)       ->            router Select (TacSelect (i, rinner Select t))
    | TacML CAst.{loc; v=(e, args)} ->
      let args = if inner_record ML then List.map (fun a -> fst (annotate_arg a)) args else args in
      router ML (TacML (CAst.make ?loc (e, args))) (* TODO: Decompose interesting known tactics (such as ssreflect) *)
    | TacAlias CAst.{loc; v=(e, args)} ->
      let args = if inner_record Alias then List.map (fun a -> fst (annotate_arg a)) args else args in
      router Alias (TacAlias (CAst.make ?loc (e, args))) (* TODO: Decompose user-defined tactics *)
  in annotate tac
