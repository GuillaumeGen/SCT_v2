open Sizematrix
open Callgraph

let rec frozen : call_graph -> string -> typ -> bool =
  fun gr rn -> function
    | Type 
    | Unhandled -> false
    | Cst f ->
      if definable gr f
      then
        let gr = !graph in
        update_result gr (find_symbol_key gr f) (DefinableType rn);
        false
      else true
    | Prod (l, t) -> List.for_all (frozen gr rn) (t::l)

