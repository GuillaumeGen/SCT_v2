open Terms
open Rules
open Sign
open Sizematrix
open Callgraph

let rec dig_in_rhs : term -> (int * string * obj array) list =
  function
  | Obj(Var(_))     -> []
  | Obj(Const(f))
  | Pred(PConst(f)) -> [0, f, [||]]
  | Obj(App(Const(f),l)) ->
     let ll = List.map (fun x -> Obj x) l in
     (0, f, Array.of_list l)
     :: List.concat (List.map dig_in_rhs ll)
  | Pred(PApp(PConst(f),l)) ->
     let ll = List.map (fun x -> Obj x) l in
     (0, f, Array.of_list l)
     :: List.concat (List.map dig_in_rhs ll)
  | Obj(App(t,l)) ->
     let ll = List.map (fun x -> Obj x) l in
     List.concat (List.map dig_in_rhs (Obj(t)::ll))
  | Pred(PApp(t,l)) ->
     let ll = List.map (fun x -> Obj(x)) l in
     List.concat (List.map dig_in_rhs (Pred(t)::ll))
  | Obj(Abst(x,ty,t)) ->
     (dig_in_rhs (Pred ty))
     @ (List.map (fun (i,b,c) -> (i+1,b,c)) (dig_in_rhs (Obj t)))
  | Pred(PAbst(_,ty,t)) ->
     (dig_in_rhs (Pred ty))
     @ (List.map (fun (i,b,c) -> (i+1,b,c)) (dig_in_rhs (Pred t)))
  | Pred(PProd(_,a,b)) ->
     (dig_in_rhs (Pred a))
     @ (List.map (fun (i,b,c) -> (i+1,b,c)) (dig_in_rhs (Pred b)))

let rec compare_term : int -> obj -> obj -> Cmp.t =
  fun i t_l t_r ->
  let rec comp_list : Cmp.t -> obj list -> obj list -> Cmp.t =
    fun cur lp lt ->
    match lp,lt with
    | [], _ | _, [] -> cur
    | a::l1, b::l2  ->
       begin
         match (compare_term i a b), cur with
	 | _   , Infi -> assert false
         (* We are sure, that the current state [cur] cannot contain a Infi, else the Infi would be the result of the function and no recursive call would be needed *)
         | Infi, _    -> Infi
         | Min1, _    -> comp_list Min1 l1 l2
      	 | _   , Min1 -> comp_list Min1 l1 l2
      	 | Zero, Zero -> comp_list Zero l1 l2
       end
  in
  match t_l,t_r with
  (* Two distinct variables are uncomparable *)
  | Var (_,n), Var (_,m)
  (* A variable when applied has the same size as if it was not applied *)
  | Var (_,n), App(Var(_,m),_) -> if n + i = m then Zero else Infi
  | App (Const f,lp), App(Const g,lt) when f = g ->
     begin
       let res1 = comp_list Zero lp lt in
       let res2 =
         Cmp.minus1 (
             Cmp.mini (
                 List.map (fun t_ll -> compare_term i t_ll t_r) lp
               )
           ) in
       Cmp.plus res1 res2 
     end
  | App (_,l),_ ->
     Cmp.minus1 (Cmp.mini (List.map (fun t_ll -> compare_term i t_ll t_r) l))
  | Abst(_,_,t_ll),Abst(_,_,t_rr) -> compare_term i t_ll t_rr
  | _ -> Infi
  
         
let study_call : signature -> index -> obj array ->
                 int -> index -> obj array -> Cmp_matrix.t =
  fun si fun_l arg_l nb fun_r arg_r ->
  let h = arity_of (find_symb si fun_l).typ in
  let w = arity_of (find_symb si fun_r).typ in
  let matrix : Cmp_matrix.t =
    {h; w; tab = Array.make_matrix h w Cmp.Infi} in
  for i=0 to (min h (Array.length arg_l)) -1
  do
    for j=0 to (min w (Array.length arg_r)) -1
    do
      matrix.tab.(i).(j) <- compare_term nb arg_l.(i) arg_r.(j)
    done
  done;
  matrix
         
(** Add the calls associated to a rule in the call graph *)
let add_rule : call_graph -> rule -> call_graph =
  fun gr r ->
  let sign = gr.signature in
  let ind_l = find_symbol_index sign r.head in
  let new_calls = List.map
    (fun (i,n,a) ->
      let ind_r = find_symbol_index sign n in
      ind_r,study_call sign ind_l r.args i ind_r a
    ) (dig_in_rhs r.rhs)
  in
  { (List.fold_left
       (fun g (callee,matrix) ->
         add_call g {caller = ind_l; callee; matrix; rule_name=r.name }
       ) gr new_calls
    ) with signature = add_rule sign r
  }
