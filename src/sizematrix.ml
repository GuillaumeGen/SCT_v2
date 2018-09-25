(** Tools used for the matrices labeling edges in the call-graph studied by sizechange.ml *)

open Basic

type Debug.flag += D_matrix
let _ = Debug.register_flag D_matrix "Call matrix"

(** Representation of the set {-1, 0, ∞} *)
type cmp = Min1 | Zero | Infi

(** String representation. *)
let cmp_to_string : cmp -> string =
  function
  | Min1 -> "<"
  | Zero -> "="
  | Infi -> "?"

(** The pretty printer for the type [cmp] *)
let pp_cmp fmt c=
  Format.fprintf fmt "%s" (cmp_to_string c)

(** Addition operation (minimum) *)
let (<+>) : cmp -> cmp -> cmp = fun e1 e2 ->
  match (e1, e2) with
  | (Min1, _   ) | (_, Min1) -> Min1
  | (Zero, _   ) | (_, Zero) -> Zero
  | (Infi, Infi)             -> Infi

(** Multiplication operation. *)
let (<*>) : cmp -> cmp -> cmp = fun e1 e2 ->
  match (e1, e2) with
  | (Infi, _   ) | (_, Infi) -> Infi
  | (Min1, _   ) | (_, Min1) -> Min1
  | (Zero, Zero)             -> Zero

(** Reduce by 1 a cmp *)
let minus1 : cmp -> cmp =
  function
  | Zero -> Min1
  | n -> n

(** Compute the minimum of a list *)
let mini : cmp list -> cmp = fun l ->
  List.fold_left (<+>) Infi l

(** Type of a size change matrix. *)
type matrix =
  { w   : int             ; (* Number of argument of callee *)
    h   : int             ; (* Number of argument of caller *)
    tab : cmp array array   (* The matrix of size h*w *)
  }

(** The pretty printer for the type [matrix] *)
let pp_matrix fmt m=
  Format.fprintf fmt "w=%i, h=%i@.tab=[[%a]]" m.w m.h
    (pp_arr "]@.     [" (pp_arr "," pp_cmp)) m.tab
    
(** Matrix product. *)
let prod : matrix -> matrix -> matrix =
  fun m1 m2 ->
    assert (m1.w = m2.h); (* The matrix must be compatible to perform product *)
    let tab =
      Array.init m1.h
        (fun y ->
	   Array.init m2.w
             (fun x ->
                let r = ref Infi in
                for k = 0 to m1.w - 1 do
	          r := !r <+> (m1.tab.(y).(k) <*> m2.tab.(k).(x))
                done; !r
             )
        )
    in
    { w = m2.w ; h = m1.h ; tab }
      
(** Check if a matrix corresponds to a decreasing idempotent call. *)
let decreasing : matrix -> bool = fun m ->
  assert (m.w = m.h); (* Only square matrices labeling a self-looping arrow need to be study *)
  try
    for k = 0 to m.w - 1 do
      if m.tab.(k).(k) = Min1
      then raise Exit
    done;
    false
  with Exit -> true

(** Check if a matrix subsumes another one (i.e. gives more infomation). *)
let subsumes : matrix -> matrix -> bool = fun m1 m2 ->
  try
    Array.iteri
      (fun y l ->
         Array.iteri
           (fun x e ->
              if not (e >= m2.tab.(y).(x))
              then raise Exit
           ) l
      ) m1.tab;
    true
  with Exit -> false
