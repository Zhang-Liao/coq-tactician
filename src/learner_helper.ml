open Tactic_learner

module L (TS: TacticianStructures) = struct
  open TS

  let rec sexpr_to_string = function
    | Leaf str -> str
    | Node ls -> "(" ^ (String.concat " " (List.map sexpr_to_string ls)) ^ ")"

  let warn term = Feedback.msg_warning (Pp.str ("Tactician did not know how to handle something. Please report."
                                                ^ sexpr_to_string term))

  let replicate x n =
    let rec aux n ls =
      if n <= 0 then ls else aux (n - 1) (x::ls) in
    aux n []

  let rec last = function
    | [] -> assert false
    | [x] -> x
    | _::ls -> last ls

  let rec removelast = function
    | [] -> assert false
    | [x] -> []
    | x::ls -> x :: removelast ls

  let disting_hyps_goal ls symbol =
    List.map (fun str -> symbol ^ str) ls 

  let get_top_interm interm =
    let flat_interm = List.flatten interm in
    if flat_interm <> [] then
      List.nth flat_interm (List.length flat_interm -1)
    else
      []
    (* List.hd (List.rev flat_interm)  *)
    
  let term_sexpr_to_features maxlength term =
    let atomtypes = ["Evar"; "Rel"; "Construct"; "Ind"; "Const"; "Var"; "Int"; "Float"] in
    let is_atom nodetype = List.exists (String.equal nodetype) atomtypes in
    let atom_to_string atomtype content = match atomtype, content with
      | "Rel", _ -> "R"
      | "Evar", (Leaf i :: _) -> "E"
      | "Construct", Leaf c :: _
      | "Ind", Leaf c :: _
      | "Var", Leaf c :: _
      | "Const", Leaf c :: _ -> c
      | "Int", Leaf c :: _ -> "i" ^ c
      | "Float", Leaf c :: _ -> "f" ^ c
      | _, _ -> warn (Leaf "KAK"); "*"
    in
    let rec aux_horiz term depth =
      if depth = 0 then ["X"]
      else
        match term with
        (* Interesting leafs *)
        | Node (Leaf nt :: ls) when is_atom nt ->
          ["X"]
        (* Uninteresting leafs *)
        | Node (Leaf "Sort" :: _)
        | Node (Leaf "Meta" :: _) -> []
        | Node [Leaf "LetIn"; id; _; body1; typ; body2] ->
          horiz_feat_fold "LetIn" [body1; typ; body2] depth
        | Node (Leaf "Case" :: _ :: term :: typ :: cases) ->
          horiz_feat_fold "Case" (term::typ::cases) depth
        | Node [Leaf "Fix"; _; Node types; Node terms] ->
          horiz_feat_fold "Fix" (types@terms) depth 
        | Node [Leaf "CoFix"; _ ; Node types; Node terms] ->
          horiz_feat_fold "CoFix" (types@terms) depth 
        | Node [Leaf "Prod"  ; _; _; typ; body] ->
          horiz_feat_fold "Prod" [typ;body] depth 
        | Node [Leaf "Lambda"; _; _; typ; body] -> 
          horiz_feat_fold "Lambda" [typ;body] depth 
        | Node [Leaf "Proj"; p; term] -> 
          horiz_feat_fold "Proj" [p; term] depth 
        | Node (Leaf "App" :: head :: args) ->
          horiz_feat_fold "App" (head :: args) depth 
        | Node [Leaf "Cast"; term; _; typ] ->
          horiz_feat_fold "Cast" [term; typ] depth 
        (* Hope and pray *)
        | term -> ["Error"]      
    and horiz_feat_fold binder term_list depth =
      List.fold_left (fun horiz_feats curr_term -> horiz_feats @ aux_horiz curr_term (depth -1)) 
      [binder] term_list
    in    
    (* for a tuple `(interm, acc)`:
       - `interm` is an intermediate list of list of features that are still being assembled
         invariant: `forall i ls, 0<i<=maxlength -> In ls (List.nth (i - 1)) -> List.length ls = i`
       - `acc`: accumulates features that are fully assembled *)
    let add_atom atomtype content (interm, acc) type_constr =
      let atom = (atom_to_string atomtype content) in
      let atom_with_type_constr = atom ^":"^type_constr in     
      let interm' = [[atom_with_type_constr]] :: 
        List.map (List.map (fun fs -> atom_with_type_constr::fs)) interm in 
      (* use removelast to control the length of terms *)
      (removelast interm', (List.flatten interm' @ acc)) in

    let set_interm (interm, acc) x = x, acc in
    let start = replicate [] (maxlength - 1) in
    let reset_interm f = set_interm f start in
    let rec aux_reset f term type_constr = reset_interm (aux (reset_interm f) term type_constr)
    and aux_reset_fold f terms type_constr = 
    List.fold_left (fun f' term -> aux_reset f' term type_constr) f terms 
    (* List.fold_left (fun f' term -> aux_reset f' term type_constr) f terms *)
    (*TODO: specify the binders of each term *)
    and aux ((interm, acc) as f) term type_constr =   
    match term with
      (* Interesting leafs *)
      | Node (Leaf nt :: ls) when is_atom nt ->
        add_atom nt ls f type_constr

      (* Uninteresting leafs *)
      | Node (Leaf "Sort" :: _)
      | Node (Leaf "Meta" :: _) -> f

      (* Recursion for grammar we don't handle *)
      (* TODO: Handle binders with feature substitution *)
      | Node [Leaf "LetIn"; id; _; body1; typ; body2] ->
        aux_reset_fold f [body1; typ; body2] "LetIn"
      | Node (Leaf "Case" :: _ :: term :: typ :: cases) ->
        aux_reset_fold f (term::typ::cases) "Case" 
      | Node [Leaf "Fix"; _; Node types; Node terms] ->
        aux_reset_fold f (terms @ types) "Fix"      
      | Node [Leaf "CoFix"; _ ; Node types; Node terms] ->
        aux_reset_fold f (terms @ types) "CoFix"
      (* TODO: Handle implication separately *)
      | Node [Leaf "Prod"  ; _; _; typ; body] ->
        aux_reset_fold f [typ; body] "Prod"
      | Node [Leaf "Lambda"; _; _; typ; body] -> 
        aux_reset_fold f [typ; body] "Lambda"
      (* The golden path *)
      | Node [Leaf "Proj"; p; term] -> 
        aux (add_atom "Const" [p] f "Proj") term "Proj"
      | Node (Leaf "App" :: head :: args) ->
        let interm', _ as f' = aux f head "App" in
        (* We reset back to `interm'` for every arg *)
        reset_interm (List.fold_left (fun f' t -> set_interm (aux f' t "App") interm') f' args)
      | Node [Leaf "Cast"; term; _; typ] ->
        (* We probably want to have the type of the cast, but isolated *)
        aux (set_interm (aux (reset_interm f) typ "Cast") interm) term "Cast"
      (* Hope and pray *)
      | term -> warn term; f
    in    
    let _, res = aux (start, []) term "Init_Constr" in
    let horiz_feats = aux_horiz term 2 in
    (*TODO: seperate horizontal features and vertical features**)
    List.map (String.concat "-") (horiz_feats::res)

  let proof_state_to_features max_length ps =
    let hyps = proof_state_hypotheses ps in
    let goal = proof_state_goal ps in
    let mkfeats t = term_sexpr_to_features max_length (term_sexpr t) in
    let hyp_feats = List.map (fun (id, term, typ) ->
        mkfeats typ @ Option.default [] (Option.map mkfeats term)
      ) hyps in
    (* seperate the goal from the local context *)  
    (disting_hyps_goal (mkfeats goal) "GOAL-") @ (disting_hyps_goal (List.flatten hyp_feats) "HYPS-")

  let s2s s = Leaf s

  let proof_state_to_sexpr ps =
    let goal = proof_state_goal ps in
    let hyps = proof_state_hypotheses ps in
    let hyps = List.map (fun (id, term, typ) ->
        Node (s2s (Id.to_string id) :: term_sexpr typ ::
              Option.default [] (Option.map (fun t -> [term_sexpr t]) term))) hyps in
    Node [s2s "State"; Node [s2s "Goal"; term_sexpr goal]; Node [s2s "Hypotheses"; Node hyps]]

  let proof_state_to_string ps env evar_map =
    let constr_str t = Pp.string_of_ppcmds (Sexpr.format_oneline (
        Printer.pr_constr_env env evar_map (term_repr t))) in
    let goal = constr_str (proof_state_goal ps) in
    let hyps = proof_state_hypotheses ps in
    let hyps = List.map (fun (id, term, typ) ->
        let id_str = Tactic_learner.Id.to_string id in
        let term_str = Option.default "" (Option.map (fun t -> " := " ^ constr_str t) term) in
        let typ_str = constr_str typ in
        id_str ^ " " ^ term_str ^ " : " ^ typ_str
      ) hyps in
    String.concat ", " hyps ^ " |- " ^ goal
end
