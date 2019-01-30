open Basic
                      
(** Index of a rule. *)
type index = int

(** Conversion to int. *)
let int_of_index : index -> int =
  fun i -> i

(** The pretty printer for the type [index] *)
let pp_index fmt x =
  Format.pp_print_int fmt (int_of_index x)

(** The local result express the result of the termination checker for this symbol *)
type local_result = SelfLooping of string list
                  | DefinableType of string
                  | NotPositive of string

(** The pretty printer for the type [local_result] *)
let pp_local_result : local_result printer =
  fun fmt lr ->
    let st =
      match lr with
      | SelfLooping _ -> "self looping"
      | DefinableType _ -> "a definable type"
      | NotPositive _ -> "not positive"
    in
    Format.fprintf fmt "%s" st

type typ = Type | Cst of string | Prod of (typ list) * typ | Unhandled

let arity_of : typ -> int = function
  | Type
  | Cst _     -> 0
  | Prod(l,_) -> List.length l
  | Unhandled -> failwith "we should never check arity of such a type (I suppose it must be a beta-redex"

let rec pp_typ fmt = function
  | Type -> Format.fprintf fmt "Type"
  | Unhandled -> Format.fprintf fmt "???"
  | Cst f -> Format.fprintf fmt "%s" f
  | Prod (l, t) -> Format.fprintf fmt "%a->%a" (pp_list "->" pp_typ) l pp_typ t 

(** Representation of a function symbol. *)
type symbol =
  {
    name           : string            ; (** The identifier of the symbol *)
    typ            : typ               ; (** Arity of the symbol (number of args). *)
    mutable result : local_result list ; (** The information about non termination for this symbol, initially empty *)
  }

let pp_symb : symbol printer =
  fun fmt s -> Format.fprintf fmt "%s" s.name
