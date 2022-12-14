module AST

type file = clause list
  (** Toplevel statement *)
and clause =
  | Clause of literal * literal list
and literal =
  | Atom of string * term list
and term =
  | Var of string
  | Const of string
  | Quoted of string
and query =
  | Query of term list * literal list * literal list
  (** Query: projection, positive lits, negative lits *)