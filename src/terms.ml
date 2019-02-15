type obj =
  (** Variables with de Bruijn index and name *)
  | Var   of string * int
  (** Symbol of the signature *)
  | Const of string
  (** f [a1 ; a2 ; ... an ] , with the guarantee that f is not an App and the list is not empty *)
  | App   of obj * obj list
  (** Lambda abstraction with the name of the variable, its type and the body of the abstraction. *)
  | Abst   of string * predicate * obj

and predicate =
  (** Symbol of the signature *)
  | PConst of string
  (** f [a1 ; a2 ; ... an ] , with the guarantee that f is not an App and the list is not empty *)
  | PApp   of predicate * obj list
  (** Lambda abstraction *)
  | PAbst  of string * predicate * predicate
  (** Pi abstraction *)
  | PProd  of string * predicate * predicate
                                     
type kind =
  (** The sort at the left of an axiom in lambda-pi *)
  | Type
  (** Pi abstraction *)
  | KProd    of string * predicate * kind  

let rec pp_obj : obj Basic.printer =
  fun fmt ->
  function
  | Var(s,_)    -> Format.fprintf fmt "%s" s
  | Const(s)    -> Format.fprintf fmt "%s" s
  | App(t,l)    ->
     Format.fprintf fmt "%a %a" pp_obj t (Basic.pp_list " " pp_obj) l
  | Abst(x,p,o) -> Format.fprintf fmt "λ(%s:%a),%a" x pp_pred p pp_obj o
and pp_pred : predicate Basic.printer =
  fun fmt ->
  function
  | PConst(s)    -> Format.fprintf fmt "%s" s
  | PApp(p,l)    ->
     Format.fprintf fmt "%a %a" pp_pred p (Basic.pp_list " " pp_obj) l
  | PAbst(x,p,t) -> Format.fprintf fmt "λ(%s:%a),%a" x pp_pred p pp_pred t
  | PProd(x,p,t) -> Format.fprintf fmt "Π(%s:%a),%a" x pp_pred p pp_pred t

let rec pp_kind : kind Basic.printer =
  fun fmt ->
  function
  | Type         -> Format.fprintf fmt "Type"
  | KProd(x,p,k) -> Format.fprintf fmt "Π(%s:%a),%a" x pp_pred p pp_kind k
                                   
type term =
  | Obj  of obj
  | Pred of predicate

type typ =
  | Typ  of predicate
  | Kind of kind

let arity_of : typ -> int =
  let rec pred_arity_of : int -> predicate -> int =
    fun i ->
    function
    | PConst _  | PApp _ | PAbst _ -> 0
    | PProd(_,_,p)                 -> pred_arity_of (i+1) p
  in
  let rec kind_arity_of : int -> kind -> int =
    fun i ->
    function
    | Type        -> 0
    | KProd(_,_,k)-> kind_arity_of (i+1) k
  in function
  | Typ p  -> pred_arity_of 0 p
  | Kind k -> kind_arity_of 0 k
