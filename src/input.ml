open Basic
open Sizematrix
open Callgraph

module type Input = sig
  type term
  type pattern
  type typ
  
  val dig_in_rhs : term -> (string * term array) list
  val destruct_lhs : pattern -> (string * pattern array)
  val get_arity : typ -> int
  val compare : pattern -> term -> cmp
end

module StudyRules = functor (In : Input ) -> struct

  (** Declare a symbol to be added in the call graph *)
  let declare : string -> In.typ -> unit =
    fun s t ->
      let sym = { name = s; arity = In.get_arity t; result = []} in
      add_symb !graph sym

  (** Add the calls associated to a rule in the call graph *)
  let add_rule : In.pattern -> In.term -> unit =
    fun p t ->
      let lhs = In.destruct_lhs p in
      let list_rhs = In.dig_in_rhs t in
      let study_call (fun_l, arg_l) (fun_r, arg_r) =
        let ind_l, ari_l = index_and_arity_of !graph fun_l in
        let ind_r, ari_r = index_and_arity_of !graph fun_r in
        let mat = Array.make_matrix ari_l ari_r Infi in
        for i=0 to min ari_l (Array.length arg_l)
        do
          for j=0 to min ari_r (Array.length arg_r)
          do
            mat.(i).(j) <- In.compare arg_l.(i) arg_r.(j)
          done
        done;
        let matrix = {w = ari_l; h = ari_r; tab=mat} in
        add_call !graph {caller = ind_l; callee = ind_r; matrix}
      in
      List.iter (fun c -> study_call lhs c) list_rhs
      
end
