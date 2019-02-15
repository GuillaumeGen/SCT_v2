type context = (string * Terms.predicate) array

type rule_name = string

type rule =
  { (** An identifier of the rule *)
    name : rule_name
  ; (** Head of the lhs *)
    head : string
  ; (** List of arguments of the lhs *)
    args : Terms.obj array
  ; (** Right-hand-side of the rule *)
    rhs  : Terms.term
  ; (** Context containing the variables in the lhs with their types *)
    ctx  : context
  }
