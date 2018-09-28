open Basic
open Sizematrix
open Callgraph

module type Input = sig
  type term
  type pattern
  type typ
  type rule_name
  
  val dig_in_rhs : term -> (string * term array) list
  val destruct_lhs : pattern -> (string * pattern array)
  val get_arity : typ -> int
  val compare : pattern -> term -> Cmp.t
  val rn_to_string : rule_name -> string
end

module StudyRules = functor (In : Input ) -> struct

  (** Declare a symbol to be added in the call graph *)
  let declare : call_graph -> string -> In.typ -> unit =
    fun gr s t ->
      let sym = { name = s; arity = In.get_arity t; result = []} in
      add_symb gr sym

  (** Add the calls associated to a rule in the call graph *)
  let add_rule : call_graph -> In.rule_name -> In.pattern -> In.term -> unit =
    fun gr rn p t ->
      let lhs = In.destruct_lhs p in
      let list_rhs = In.dig_in_rhs t in
      let study_call (fun_l, arg_l) (fun_r, arg_r) =
        let ind_l, h = index_and_arity_of gr fun_l in
        let ind_r, w = index_and_arity_of gr fun_r in
        let matrix : Cmp_matrix.t =
          {h; w; tab = Array.make_matrix h w Cmp.Infi} in
        for i=0 to (min h (Array.length arg_l)) -1
        do
          for j=0 to (min w (Array.length arg_r)) -1
          do
            matrix.tab.(i).(j) <- In.compare arg_l.(i) arg_r.(j)
          done
        done;
        add_call gr {caller = ind_l; callee = ind_r; matrix;
                     rule_name = In.rn_to_string rn }
      in
      List.iter (fun c -> study_call lhs c) list_rhs
      
end

module Dk = struct
  type term = Term.term
  type pattern = Rule.pattern
  type typ = Term.term
  type rule_name = Rule.rule_name

  let string_of_name n =
      (Basic.string_of_mident (Basic.md n))^"."^
      (Basic.string_of_ident (Basic.id n))
  
  let rec dig_in_rhs : term -> (string * term array) list =
    function
    | Kind
    | Type _
    | DB (_, _, _) -> []
    | Const (_, f) -> [string_of_name f, [||]]
    | App (Const(_, f), t1, l) -> (string_of_name f, Array.of_list (t1 :: l)) :: List.concat (List.map dig_in_rhs (t1::l))
    | App (t0, t1, l) ->  List.concat (List.map dig_in_rhs (t0::t1::l))
    | Lam (_, _, None, t) -> dig_in_rhs t
    | Lam (_, _, Some ty, t) -> (dig_in_rhs ty) @ (dig_in_rhs t)
    | Pi (_, _, t1, t2) -> (dig_in_rhs t1) @ (dig_in_rhs t2)
              
  let destruct_lhs : pattern -> (string * pattern array) =
    function
    | Pattern (_,f,l) -> (string_of_name f, Array.of_list l)
    | _ -> failwith "This is not a valid lhs of rule"
                                
  let rec get_arity : typ -> int =
    function
    | Pi (_, _, _, t) -> 1 + (get_arity t)
    | _ -> 0

  let compare : pattern -> term -> Cmp.t =
    (** Compare a term and a pattern, using an int indicating under how many lambdas the comparison occurs *)
    let rec comparison : int -> term -> pattern -> Cmp.t =
      fun nb t p ->
        let rec comp_list : Cmp.t -> pattern list -> term list -> Cmp.t =
          fun cur lp lt ->
            match lp,lt with
            | [], _ | _, [] -> cur
            | a::l1, b::l2  ->
              begin
                match (comparison nb b a), cur with
	        | _   , Infi -> assert false
                (* We are sure, that the current state [cur] cannot contain a Infi, else the Infi would be the result of the function and no recursive call would be needed *)
                | Infi, _    -> Infi
                | Min1, _    -> comp_list Min1 l1 l2
      	        | _   , Min1 -> comp_list Min1 l1 l2
      	        | Zero, Zero -> comp_list Zero l1 l2
      	      end
        in
        match p,t with
        | Var (_,_,n,_), DB (_,_,m) -> if n+nb=m then Zero else Infi (* Two distinct variables are uncomparable *)
        | Var (_,_,n,_), App(DB(_,_,m),_,_) -> if n+nb=m then Zero else Infi (* A variable when applied has the same size as if it was not applied *)
        | Lambda(_,_,Var(_,_,n,_)), DB(_,_,m) -> if n+nb=m+1 then Zero else Infi
        | Lambda(_,_,Var(_,_,n,_)), App(DB(_,_,m),_,_) -> if n+nb=m+1 then Zero else Infi
        | Pattern (_,f,lp), App(Const(_,g),t1,lt) when (name_eq f g) ->
          begin
	    comp_list Zero lp (t1::lt)
          end
        | Pattern (_,_,l),t -> Cmp.minus1 (Cmp.mini (List.map (comparison nb t) l))
        | Lambda(_,_,pp),Lam(_,_,_,tt) -> comparison nb tt pp
        | _ -> Infi
    in fun p t -> comparison 0 t p


  let rn_to_string : rule_name -> string =
    function
    | Beta -> failwith "Beta should not occur in a rule declaration"
    | Delta n -> string_of_name n
    | Gamma(_, n) -> string_of_name n
end

module DkRules = struct
  include StudyRules(Dk)

  let rec import : loc -> mident -> unit =
  fun lc m ->
      begin
        let (deps,ctx,ext) = Signature.read_dko lc (string_of_mident m) in
        let symb (id,_,ty,_) =
          let cst = (string_of_mident m)^"."^(string_of_ident id) in
          declare !graph cst ty;
        in
        let rule (id,_,ty,rul) =
          List.iter
            (fun (r : Rule.rule_infos) ->
               add_rule !graph r.name (Pattern(dloc,r.cst,r.args)) r.rhs
            ) rul
        in
        List.iter symb ctx;
        List.iter rule ctx
      end

  and load_terms : Term.term -> unit =
    function
    | Term.Kind 
    | Term.Type _
    | Term.DB (_, _, _) -> ()
    | Term.Const (lc, n) -> import lc (md n)
    | Term.App (t, u, l) -> List.iter load_terms (t::u::l)
    | Term.Lam (_, _, Some ty, te) -> load_terms ty; load_terms te
    | Term.Lam (_, _, None, te) -> load_terms te
    | Term.Pi (_, _, t1, t2) -> load_terms t1; load_terms t2
end
