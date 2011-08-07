Inductive Exception : Set :=
  | IOException : Exception
  | parse_error_exception : Exception .
Inductive EXCEPT (B A : Set) : Set :=
  | SUCC : A -> B -> EXCEPT B A
  | FAIL : Exception -> B -> EXCEPT B A.
