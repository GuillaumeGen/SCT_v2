(** Size change principle.
    This module implements a decision procedure based on the work of
Chin Soon Lee, Neil D. Jones and Amir M. Ben-Amram (POPL 2001).
    Most of this module comes from an implementation of Rodolphe Lepigre
and Christophe Raffalli. *)
open Basic
open Term
open Rule
open Sizematrix
open Callgraph

type Debug.flag += D_sctsummary
let _ = Debug.register_flag D_sctsummary "Summary of SCT"

(** the main function, checking if calls are well-founded *)
let sct_only : unit -> unit =
  fun ()->
    let ftbl= !graph in
    let symbs = !(ftbl.symbols) in
    let num_fun = IMap.cardinal symbs in
    let dname = "" in
    let id_to_name = Array.init num_fun (fun _ -> dname) in
    IMap.iter (fun k sy -> id_to_name.(k) <- sy.name) symbs;
    (* tbl is a num_fun x num_fun Array in which each element is the list of all matrices between the two symbols with the rules which generated this matrix *)
    let tbl = Array.init num_fun (fun _ -> Array.make num_fun []) in
  (* counters to count added and composed edges *)
    let added = ref 0 and composed = ref 0 in
  (* function adding an edge, return a boolean indicating
     if the edge is new or not *)
    let add_edge f g m r =
      let i, _ =
        IMap.find_first (fun k -> (IMap.find k symbs).name = f) symbs in
      let j, _ =
        IMap.find_first (fun k -> (IMap.find k symbs).name = g) symbs in
      let ti = tbl.(i) in
      let ms = ti.(j) in
      if List.exists (fun m' -> subsumes (fst m') m) ms
      then
	false
      else
        begin
          (* test idempotent edges as soon as they are discovered *)
          if i = j && prod m m = m && not (decreasing m) then
            begin
	      Debug.debug Sizematrix.D_matrix
                "edge %a idempotent and looping" (pp_call !graph)
                  {callee = i; caller = j; matrix = m};
              update_result f (SelfLooping r)
	    end;
	  let ms = (m, r) ::
            List.filter (fun m' -> not (subsumes m (fst m'))) ms in
          ti.(j) <- ms;
          true
        end
    in
    (* adding initial edges *)
    Debug.debug Sizematrix.D_matrix "initial edges to be added:";
    List.iter
      (fun c -> (Debug.debug Sizematrix.D_matrix "  %a" pp_call c))
      !(ftbl.calls);
    let new_edges = ref !(ftbl.calls) in
    (* compute the transitive closure of the call graph *)
    Debug.debug Sizematrix.D_matrix "start completion";
    let rec fn () =
      match !new_edges with
      | [] -> ()
      | ({callee = f; caller = g; matrix = m; rules=r} as c)::l ->
        let j = (NMap.find g symbs).ind in
        new_edges := l;
        if add_edge f g m r
        then
          begin
            Debug.debug Sizematrix.D_matrix "  edge %a added" pp_call c;
            incr added;
            let t' = tbl.(j) in
            Array.iteri
              (fun k t ->
                 List.iter
                   (fun (m',r') ->
                      let c' = {callee = g; caller = id_to_name.(k); matrix = m'; rules=r'}
                      in
                      Debug.debug Sizematrix.D_matrix "  compose: %a * %a = "
                          pp_call c
                          pp_call c';
                      let m'' = prod m m' in
                      let r'' = r @ r' in
                      incr composed;
                      let c'' =
                        {callee = f; caller = id_to_name.(k); matrix = m''; rules = r''}
                      in
                      new_edges := c'' :: !new_edges;
                       Debug.debug Sizematrix.D_matrix "%a" pp_call c'';
                   ) t
              ) t'
          end
        else
         Debug.debug Sizematrix.D_matrix " edge %a is old" pp_call c;
        fn ()
    in
    fn ();
    Debug.debug D_sctsummary "SCT passed (%5d edges added, %6d composed)"
             !added !composed


