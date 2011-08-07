Require Import SMTP_applpi_string.

Axiom Rfc821_path : Set.
Axiom string_to_Rfc821path : String -> option Rfc821_path.

(* we assume this function never causes any system failure;
this assumption does not cause any breach since is_not_null_a_d_l
is always used in a "context" that itself assume a system failure may
occur; by context, we mean the "wrapping" instruction (sequence,
conditional, ...)  *)
Axiom is_not_null_a_d_l : Rfc821_path -> bool.

Axiom path_null : Rfc821_path.
Axiom is_validRfc821path : String -> bool.

Inductive bad_Rfc821path : String -> Prop := 
  Rfc821_bad_path : forall s, 
    string_to_Rfc821path s = None -> bad_Rfc821path s.
Inductive invalid_Rfc821path : String -> Prop :=
  Rfc821_invalid_path : forall s p,
    string_to_Rfc821path s = Some p ->
    is_not_null_a_d_l p = true -> invalid_Rfc821path s.
