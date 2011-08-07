Add LoadPath "/home/affeldt/src/coq/applpi".

Require Import libapplpi.
Require Import SMTP_applpi_string.
Require Import SMTP_applpi_rfc821.
Require Import SMTP_applpi.

(** valid SMTP commands *)
Inductive valid_cmd_helo : SMTP_cmd -> Prop :=
    valid_cmd_h : forall arg,
      is_nullstr arg = false -> valid_cmd_helo (cmd_helo arg).
Inductive valid_cmd_mail : SMTP_cmd -> Prop :=
    valid_cmd_m : forall arg p,
      string_to_Rfc821path arg = Some p -> valid_cmd_mail (cmd_mail_from arg).
Inductive valid_cmd_rcpt : SMTP_cmd -> Prop :=
    valid_cmd_r : forall arg p,
      string_to_Rfc821path arg = Some p ->
      is_not_null_a_d_l p = false -> valid_cmd_rcpt (cmd_rcpt_to arg).

Inductive valid_fs : ToFileSystem -> proc -> Prop :=
    save : forall s P,
      (forall x, valid_fs s (P x)) -> valid_fs s (s ?? P) .

Inductive acknowledges_replies : OutputStream -> proc -> Prop :=
  | ack_rep : forall y P,
      (forall x, acknowledges_replies y (P x)) ->
      acknowledges_replies y (y ?? P)
  | ack_rep_ioerror : forall y P,
      acknowledges_replies y P ->
      acknowledges_replies y (IOexn_chan << tt >> P).

(** this inductive predicate represents SMTP clients that speak a valid
protocol; the 1st argument is the incoming stream of SMTP commands,
the 2nd argument represents the client in itself; it is possible for
IO errors to appear after some commands have been sent *)
Inductive speaks_valid_protocol (s : InputStream) : proc -> Prop :=
  | say_helo : forall P c, valid_cmd_helo c ->
    speaks_valid_after_helo s P -> speaks_valid_protocol s (s << c >> P)
  | say_quit : speaks_valid_protocol s (OutAtom s cmd_quit)
  | say_abort : speaks_valid_protocol s (OutAtom s cmd_abort)
  | say_skip : forall P c, ~ valid_cmd_helo c ->
      c <> cmd_quit -> c <> cmd_abort ->
      speaks_valid_protocol s P -> speaks_valid_protocol s (s << c >> P)
  | io_error : forall P, speaks_valid_protocol s P ->
      speaks_valid_protocol s (IOexn_chan << tt >> P)
with speaks_valid_after_helo (s : InputStream) : proc -> Prop :=
  | say_mail_after_helo : forall P c, valid_cmd_mail c ->
      speaks_valid_after_mail s P -> speaks_valid_after_helo s (s << c >> P)
  | say_abort_after_helo : speaks_valid_after_helo s (OutAtom s cmd_quit)
  | say_quit_after_helo : speaks_valid_after_helo s (OutAtom s cmd_abort)
  | say_skip_after_helo : forall P c, ~ valid_cmd_mail c ->
      c <> cmd_quit -> c <> cmd_abort ->
      speaks_valid_after_helo s P -> speaks_valid_after_helo s (s << c >> P)
  | io_error_after_helo : forall P, speaks_valid_after_helo s P ->
      speaks_valid_after_helo s (IOexn_chan << tt >> P)
with speaks_valid_after_mail (s : InputStream) : proc -> Prop :=
  | say_rcpt_after_mail : forall P c, valid_cmd_rcpt c ->
      speaks_valid_after_rcpt s P -> speaks_valid_after_mail s (s << c >> P)
  | say_abort_after_mail : speaks_valid_after_mail s (OutAtom s cmd_quit)
  | say_quit_after_mail : speaks_valid_after_mail s (OutAtom s cmd_abort)
  | say_rset_after_mail : forall P, speaks_valid_after_helo s P ->
      speaks_valid_after_mail s (s << cmd_rset >> P)
  | say_skip_after_mail : forall P c, ~ valid_cmd_rcpt c ->
      c <> cmd_quit -> c <> cmd_abort -> c <> cmd_rset ->
      speaks_valid_after_mail s P -> speaks_valid_after_mail s (s << c >> P)
  | io_error_after_mail : forall P, speaks_valid_after_mail s P ->
      speaks_valid_after_mail s (IOexn_chan << tt >> P)
with speaks_valid_after_rcpt (s : InputStream) : proc -> Prop :=
  | say_data_after_rcpt : forall data P, speaks_valid_after_helo s P ->
      speaks_valid_after_rcpt s (s << cmd_data data >> P)
  | say_abort_after_rcpt : speaks_valid_after_rcpt s (OutAtom s cmd_abort)
  | say_quit_after_rcpt : speaks_valid_after_rcpt s (OutAtom s cmd_quit)
  | say_rset_after_rcpt : forall P, speaks_valid_after_helo s P ->
      speaks_valid_after_rcpt s (s << cmd_rset >> P)
  | say_skip_after_rcpt : forall P c, c <> cmd_quit -> c <> cmd_abort ->
      (forall data, c <> cmd_data data) -> c <> cmd_rset ->
      speaks_valid_after_rcpt s P -> speaks_valid_after_rcpt s (s << c >> P)
  | io_error_after_rcpt : forall P, speaks_valid_after_rcpt s P ->
      speaks_valid_after_rcpt s (IOexn_chan << tt >> P).

(* for instance, a mail client that only send abort commands speaks a 
valid protocol; in other words, the goal:
forall (s:chan SMTP_cmd),
(speaks_valid_protocol s (s << cmd_abort >> zeroP))
is provable
*)

(** a system failure is represented by a process that outputs unit on the
failure channel; an IO exception is represented by a process that outputs
unit on the IOexn_chan channel; a successful computation is represented
by a process sthat outputs unit on the result_chan channel *)
Definition reports_succ_or_error : form :=
  OR (OUTPUTS result_chan tt ISANY)
    (OR (OUTPUTS IOexn_chan tt ISANY) (OUTPUTS system_failure_chan tt ISANY)).
