(** Size change principle.
    This module implements a decision procedure based on the work of
Chin Soon Lee, Neil D. Jones and Amir M. Ben-Amram (POPL 2001).
    Most of this module comes from an implementation of Rodolphe Lepigre
and Christophe Raffalli. *)
open Basic
open Sizematrix
open Symbols
open Callgraph

type Debug.flag += D_sctsummary
let _ = Debug.register_flag D_sctsummary "Summary of SCT"


let pp_call_graph : call_graph printer =
  fun fmt g ->
  Format.fprintf fmt "@.We print the call graph@.@.@.";
  let nb = !(g.next_index) in
  for i = 0 to nb -1 do
    for j = 0 to nb -1 do
      Format.fprintf fmt "Call between %s and %s@."
        (IMap.find i !(g.symbols)).name
        (IMap.find j !(g.symbols)).name;
      Format.fprintf fmt "%a@."
        (pp_list "\n"
           (fun fmt x -> Format.fprintf fmt "%a"Cmp_matrix.pp (snd x)))
        (!(g.calls).tab.(i).(j))
    done;
  done

                            
let remove_cstr : Cmp.condition -> call_graph -> unit =
  let rec rm a =
    function
    | [] -> []
    | b :: t -> (fun l -> if b = a then l else b::l) (rm a t)
  in
  fun c g ->
  let f : 'a * Cmp_matrix.t -> 'a * Cmp_matrix.t =
    fun (x,mat) ->
    x, {h = mat.h; w= mat.w; tab=Array.map
      (fun lin2 ->
        Array.map
          (fun (sm_l,eq_l) ->
            Cmp.clean (List.map (rm c) sm_l,List.map (rm c) eq_l)
          ) lin2
      ) (mat.tab)}
  in
  let m =
    Array.map
      (fun line ->
        Array.map
          (fun l ->
            List.map f l
          ) line
      ) !(g.calls).tab
  in g.calls := {h = !(g.calls).h; w= !(g.calls).w; tab = m}
      
                            
let rec with_cstr : call_graph -> Cmp.condition list -> call_graph =
  fun g l ->
  Debug.debug D_graph "We study the case where we add the constraint %a" (pp_list "," Cmp.pp_cond) l;
  match l with
  | []         -> g
  | Sm(a,b)::t ->
     let w = arity_of (IMap.find a !(g.symbols)).typ in
     let h = arity_of (IMap.find b !(g.symbols)).typ in
     let tab = Array.init h (fun _ -> Array.init w (fun _ -> Cmp.infi)) in
     let matrix : Cmp_matrix.t = {h; w; tab} in
     let rule_name = Format.asprintf "Sm(%i,%i)" a b in
     let cc = {caller = b; callee = a; matrix; rule_name} in
     add_call g cc;
     remove_cstr (Sm(a,b)) g;
     with_cstr g t
  | Eq(a,b)::t ->
     let w = arity_of (IMap.find a !(g.symbols)).typ in
     let h = arity_of (IMap.find b !(g.symbols)).typ in
     let tab = Array.init h (fun _ -> Array.init w (fun _ -> Cmp.min1)) in
     let matrix : Cmp_matrix.t = {h; w; tab} in
     let rule_name = Format.asprintf "Sm(%i,%i)" a b in
     let cc = {caller = b; callee = a; matrix; rule_name} in
     add_call g cc;
     remove_cstr (Eq(a,b)) g;
     with_cstr g t
                            
(** the main function, checking if calls are well-founded *)
let rec check_sct : call_graph -> bool * (Sizematrix.Cmp.dnf * int * string list) list =
  
  fun gr ->let l= ref [] in
  let rec check_list : int -> (string list * Cmp_matrix.t) list -> unit =
    fun i ->
    function
    | []      -> ()
    | (x,m) :: tl ->
      begin
        let r = Cmp_matrix.decreasing m in
        if r = [[]]
        then
          check_list i tl
        else
          (if Cmp_matrix.is_idempotent m
          then l:= (r,i,x):: !l;
          check_list i tl)
        end
  in
    Debug.debug D_graph "%a" pp_call_graph gr;
    let nb_fun = !(gr.next_index) in
    for i = 0 to nb_fun -1 do
      check_list i !(gr.calls).tab.(i).(i)
    done;
    match !l with
    | []           -> Debug.debug D_graph "TRUE"; (true,[])
    | (r,_,_) :: _ ->
      if List.exists (fun (a,_,_) -> a=[]) !l
      then (Debug.debug D_graph "l=%a@.1FALSE" (pp_list ";" (pp_triple Cmp.pp_dnf Format.pp_print_int (pp_list " " Format.pp_print_string))) !l; (false,!l))
      else
        let bb = 
        (List.exists
           (fun x -> let gg = copy_graph gr in fst (check_sct (with_cstr gg x))) r)
        in (Debug.debug D_graph "%s" (if bb then "TRUE" else "2FALSE"); bb,!l )
