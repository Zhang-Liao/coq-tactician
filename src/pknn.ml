module type FeatureType = sig
    type feature
    type obj
    val compare : feature -> feature -> int
    val equal : feature -> feature -> bool
    val hash : feature -> int
end

module type KnnType = sig
    type feature
    type obj
    type t
    val create : unit -> t
    val add : t -> feature list -> obj -> t
    val knn : t -> feature list -> (float * feature list * obj) list
    val tolist : t -> (feature list * obj) list
    val count : t -> int
end

module MakeNaiveKnn (T : FeatureType): (KnnType with type feature = T.feature and type obj = T.obj) = struct

    type feature = T.feature
    type obj = T.obj
    module FeatureOrd = struct
        type t = feature
        let compare = T.compare
    end
    module Frequencies = Map.Make(FeatureOrd)
    type db_entry =
        { features : T.feature list;
          obj      : obj
        }
    type database =
        { entries : db_entry list
        ; length  : int
        ; frequencies : int Frequencies.t}

    type t = database

    let default d opt = match opt with | None -> d | Some x -> x

    let create () = {entries = []; length = 0; frequencies = Frequencies.empty}

    let add db fl obj =
        let flsort = List.sort_uniq T.compare fl in
        let comb = {features = flsort; obj = obj} in
        let newfreq = List.fold_left
                       (fun freq f ->
                            Frequencies.update f (fun y -> Some (1 + (default 0 y))) freq)
                       db.frequencies
                       flsort in
        {entries = comb::db.entries; length = db.length + 1; frequencies = newfreq}

    let rec intersect l1 l2 =
        match l1 with [] -> []
            | h1::t1 -> (
              match l2 with [] -> []
                  | h2::t2 when T.compare h1 h2 < 0 -> intersect t1 l2
                  | h2::t2 when T.compare h1 h2 > 0 -> intersect l1 t2
                  | h2::t2 -> (
                    match intersect t1 t2 with
                        | [] -> [h1]
                        | h3::t3 as l when T.equal h3 h1 -> l
                        | h3::t3 as l -> h1::l
                  )
            )

    let tfidf db ls1 ls2 =
        let inter = intersect ls1 ls2 in
        let size = db.length in
        List.fold_left (+.) 0.
            (List.map
                (fun f -> Float.log ((Float.of_int (1 + size)) /.
                                     (Float.of_int (1 + (default 0 (Frequencies.find_opt f db.frequencies))))))
                inter)

    let knn db fl =
        let flsort = List.sort_uniq T.compare fl in
        let tdidfs = List.map
                         (fun ent -> let x = tfidf db flsort ent.features in (x, ent.features, ent.obj))
                         db.entries in
        List.sort (fun (x, _, _) (y, _, _) -> Float.compare y x) tdidfs

    let tolist db = List.map (fun ent -> (ent.features, ent.obj)) db.entries

    let count db = db.length

end

module StringNaiveKnn = MakeNaiveKnn (struct
                                          type feature = string
                                          type obj = string
                                          let compare = String.compare
                                          let equal = String.equal
                                          let hash = Hashtbl.hash
                                      end)

module IntNaiveKnn = MakeNaiveKnn (struct
                                          type feature = int
                                          type obj = string
                                          let compare = compare
                                          let equal = (=)
                                          let hash = Hashtbl.hash
                                      end)

module MakeRandomKnn (T : FeatureType): (KnnType with type feature = T.feature and type obj = T.obj) = struct

    type feature = T.feature
    type obj = T.obj
    type db_entry =
        { features : T.feature list;
          obj      : obj
        }
    type database =
        { entries : db_entry list
        ; length  : int}

    type t = database

    let create () = {entries = []; length = 0}

    let add db fl obj =
        let flsort = List.sort T.compare fl in
        let comb = {features = flsort; obj = obj} in
        {entries = comb :: db.entries; length = db.length + 1}

    let shuffle d =
        let nd = List.map (fun c -> (Random.bits (), c)) d in
        let sond = List.sort compare nd in
        List.map snd sond

    let knn db fl =
        let tdidfs = List.map
                         (fun ent -> (0., ent.features, ent.obj))
                         (shuffle db.entries) in
        List.sort (fun (x, _, _) (y, _, _) -> Float.compare y x) tdidfs

    let tolist db = List.map (fun ent -> (ent.features, ent.obj)) db.entries

    let count db = db.length

end

module StringRandomKnn = MakeRandomKnn (struct
                                          type feature = string
                                          type obj = string
                                          let compare = String.compare
                                          let equal = String.equal
                                          let hash = Hashtbl.hash
                                      end)

module IntRandomKnn = MakeRandomKnn (struct
                                          type feature = int
                                          type obj = int
                                          let compare = compare
                                          let equal = (=)
                                          let hash = Hashtbl.hash
                                      end)
