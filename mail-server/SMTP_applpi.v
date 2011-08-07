Add LoadPath "/Users/mzp/Downloads/applpi".

Require Import libapplpi.
Require Import SMTP_applpi_string.
Require Import SMTP_applpi_rfc821.
Require Import SMTP_applpi_filesystem.
Require Import SMTP_applpi_exceptions.

(** If a system failure does not occur, 
   the server outputs a message on the result channel or reports an IO exception *)
Axiom result_chan : chan unit false.
Definition succ : proc := OutAtom result_chan tt.

(** IO exception is modeled by behavior of the external process 
   (in response to each request for sending a reply message, 
   a message may be sent on an exception channel, 
   in response to a request to the file server, 
   the file server may sent a message on an exception channel) *)
Axiom IOexn_chan : chan unit false.
Definition IOexn := OutAtom IOexn_chan tt.

(** system failure is modeled by running the whole system in parallel to the may_fail process; 
   the assumption that the system failure does not happen is represented by absence of the process "failure" *)
Axiom system_failure_chan : chan unit false.
Definition failure := OutAtom system_failure_chan tt.

Definition may_fail := nuP
  (fun x => parP (InAtom x)
    (parP (OutAtom x tt) (x ?? (fun _ => OutAtom system_failure_chan tt)))).

Record Mail : Set := mail
  { domain : String; 
    rev : Rfc821_path; 
    fwd : list Rfc821_path; 
    body : String}.

(** Definition of SMTP commands from client *)
(* c.f. Smtpdialog.java: l.66-74 *)
Inductive SMTP_cmd : Set :=
  | cmd_helo : String -> SMTP_cmd 
	(* helo takes the client's domain? *)
	(* The command is invalid if the argument is null *)
  | cmd_mail_from : String -> SMTP_cmd
	(* mail_from takes the sender's mail address *)
  | cmd_rcpt_to : String -> SMTP_cmd
	(* rcpt_to takes a receiver's mail address *)
  | cmd_data : String -> SMTP_cmd
	(* cmd_data takes the body of the mail *)
	(* In the actual system, the body is received separately *)
  | cmd_noop : SMTP_cmd
  | cmd_rset : SMTP_cmd
  | cmd_quit : SMTP_cmd
  | cmd_abort : SMTP_cmd
  | cmd_unknown : SMTP_cmd.

Definition InputStream : Set := chan SMTP_cmd true.

(** Reply messages *)
(* In the actual code, reply messages are strings: 
   see Smtpdialong.java: l.536- *)
Inductive ReplyMsg : Set :=
  | rep_ok_helo : ReplyMsg
  | rep_no_helo : ReplyMsg
  | rep_dup_helo : ReplyMsg
  | rep_bad_helo : ReplyMsg
  | rep_ok_mail_from : ReplyMsg
  | rep_no_mail_from : ReplyMsg
  | rep_dup_mail_from : ReplyMsg
  | rep_bad_mail_from : String -> ReplyMsg
  | rep_ok_rcpt_to : ReplyMsg
  | rep_no_rcpt_to : ReplyMsg
  | rep_bad_rcpt_to501 : ReplyMsg
  | rep_bad_rcpt_to553 : ReplyMsg
  | rep_ok_rset : ReplyMsg
  | rep_ok_data : ReplyMsg
  | rep_unknown_cmd : ReplyMsg
  | rep_ok_quit : ReplyMsg
  | rep_ok_noop : ReplyMsg
  | rep_greeting : ReplyMsg
  | rep_msg_accepted : ReplyMsg.

Axiom eqrep : ReplyMsg -> ReplyMsg -> bool.
Axiom eqrep_refl : forall x, eqrep x x = true.
Axiom eqrep_eq : forall x y, eqrep x y = true -> x = y.

Definition OutputStream := chan ReplyMsg true.

Definition type_to_be_defined : Set := bool.
Definition Buffer : Set := type_to_be_defined. 

Definition ToFileSystem : Set := chan Mail true.

(** A state is passed around as an argument of functions in order to model change of the server state. Except for the state of the file system and the output stream, states may be lost by a non-deterministic failure of the computer *)
(* instance variables of SMTPdialog plus system states such as the file system. *)
(* c.f. Smtpdialog.java: l.39-61 *)
Record SMTPstate : Set := smtp_state
  {in_stream : InputStream;
   to_client : OutputStream;
   server_name : String;
   queue_dir : File;
   buf : Buffer;
   from_domain : String;
   rev_path : Rfc821_path;
   fwd_paths : list Rfc821_path;
(* the file system is modeled as a process that runs concurrently with the SMTP server; 
   we however needs a channel to communicate files to be saved to the file system *)
   to_fs : ToFileSystem;
(* Instead of using oracles, non-deterministic failures can be modeled as a non-deterministic behavior of a process:
    see failure and IOexn_chan channels *)
   quit : bool (* TODO: useless? *)}.

(* mutators functions to update states *)
Definition update_from (st : SMTPstate) (dom : String) : SMTPstate :=
  smtp_state (in_stream st) (to_client st) (server_name st) (queue_dir st) (buf st) 
  dom (rev_path st) (fwd_paths st) (to_fs st) (quit st).

Definition update_rev_path (st : SMTPstate) (path : Rfc821_path) : SMTPstate :=
  smtp_state (in_stream st) (to_client st) (server_name st) (queue_dir st) 
  (buf st) (from_domain st) path (fwd_paths st) (to_fs st) (quit st).

Definition update_fwd_paths (st : SMTPstate) (paths : list Rfc821_path) : SMTPstate :=
  smtp_state (in_stream st) (to_client st) (server_name st) (queue_dir st) 
  (buf st) (from_domain st) (rev_path st) paths (to_fs st) (quit st).

Definition fwd_paths_add (st : SMTPstate) (path : Rfc821_path) : SMTPstate :=
  update_fwd_paths st (path :: fwd_paths st).

Definition STATE : Set := SMTPstate.

Definition reply (r : ReplyMsg) (c : OutputStream) (cont : proc) : proc := 
  c << r >> cont.

(* Now get_cmd actually receives a command from the client. *)
Definition get_cmd (c : InputStream) (cont : SMTP_cmd -> proc) : proc :=
  c ?? cont.
Definition get_arg (c : InputStream) (cont : unit -> proc) : proc := 
  cont tt.

(** We assume we have the following sub-procedures. Properties of these functions are described by axioms. *)
Axiom parseRfc821path : String -> EXCEPT unit Rfc821_path.

Axiom ax_parse : forall s : String,
    (forall p : Rfc821_path,
     string_to_Rfc821path s = Some p ->
     parseRfc821path s = SUCC unit Rfc821_path p tt) /\
    (string_to_Rfc821path s = None ->
     parseRfc821path s = FAIL unit Rfc821_path parse_error_exception tt).

Definition save_mail (data : String) (st : STATE) (cont : proc) : proc :=
  let m := mail (from_domain st) (rev_path st) (fwd_paths st) data in
  to_fs st << m >> cont.

(** Functions for sending reply messages *)
(* See Smtpdialog.java: l.274 -- *)
Definition greeting := reply rep_greeting.
Definition reply_unknown_cmd := reply rep_unknown_cmd.
Definition reply_ok_helo := reply rep_ok_helo.
Definition reply_ok_mail_from := reply rep_ok_mail_from.
Definition reply_bad_mail_from (s : String) := reply (rep_bad_mail_from s).
Definition reply_ok_rcpt_to := reply rep_ok_rcpt_to.
Definition reply_bad_rcpt_to501 := reply rep_bad_rcpt_to501.
Definition reply_bad_rcpt_to553 := reply rep_bad_rcpt_to553.
Definition reply_bad_helo := reply rep_bad_helo.
Definition reply_ok_quit := reply rep_ok_quit.
Definition reply_ok_rset := reply rep_ok_rset.
Definition reply_ok_noop := reply rep_ok_noop.
Definition reply_ok_data := reply rep_ok_data.
Definition reply_no_helo := reply rep_no_helo.
Definition reply_no_mail_from := reply rep_no_mail_from.
Definition reply_no_rcpt_to := reply rep_no_rcpt_to.
Definition reply_dup_helo := reply rep_dup_helo.
Definition reply_dup_mail_from := reply rep_dup_mail_from.

(* Smtpdialog.java: l.99-- *)
Definition do_helo (arg : String) (st : STATE) (cont : bool -> STATE -> proc) : proc :=
(*** Strictly speaking, we should wrap (is_nullstr arg) below with
 *** a function that may raise a system failure.
 *** We do not do so, however: Since (is_nullstr arg) does not
 *** change the state, the effect of a system failure occuring
 *** during (is_nullstr arg) is the same as that of a failure 
 *** immediately before execution of do_helo.
 *** We apply similar simplification to other boolean tests.
 ***)
  if is_nullstr arg
  then
  reply_bad_helo (to_client st) (cont false st)
  else
   let st' := update_from st arg in 
   reply_ok_helo (to_client st') (cont true st').

Definition do_mail_from (arg : String) (st : STATE) (cont : bool -> STATE -> proc) : proc :=
  match parseRfc821path arg with
  | SUCC path _ =>
      let st' := update_rev_path st path in
      reply_ok_mail_from (to_client st') (cont true st')
  | FAIL exn _ =>
      match exn with
      | _ =>
          (* it can only be a parse_error_exception *)
          reply_bad_mail_from arg (to_client st) (cont false st) 
      end
  end.

Definition do_rcpt_to (arg : String) (st : STATE) (cont : STATE -> proc) : proc :=
  match parseRfc821path arg with
  | SUCC p _ =>
      if is_not_null_a_d_l p
      then
      reply_bad_rcpt_to553 (to_client st) (cont st)
      else
       let st' := fwd_paths_add st p in
       reply_ok_rcpt_to (to_client st') (cont st')
  | FAIL exn _ =>
      match exn with
      | _ =>
          (* it can only be a parse_error_exception *)
          reply_bad_rcpt_to501 (to_client st) (cont st) 
      end
  end.

Definition fwd_paths_size_gt_0 (paths : list Rfc821_path) : bool :=
  match paths with
  | nil => false
  | _ => true
  end.
Definition file_body := str_body.
Definition file_tmp_envelope := str_tmp_envelope.
Definition file_envelope := str_envelope.

(** Main routines of SMTP server *)
(* c.f. Smtpdialong.java: l.52--67 *)
Definition get_helo_def (heloc mailc : chan STATE true) (st : STATE) : proc :=
  get_cmd (in_stream st)
    (fun c : SMTP_cmd =>
     get_arg (in_stream st)
       (* switch on command *)
       (fun _ : unit =>
        match c with
        | cmd_unknown => reply_unknown_cmd (to_client st) (OutAtom heloc st)
        | cmd_abort => reply_ok_quit (to_client st) succ
        | cmd_quit => reply_ok_quit (to_client st) succ
        | cmd_rset => reply_ok_rset (to_client st) (OutAtom heloc st)
        | cmd_noop => reply_ok_noop (to_client st) (OutAtom heloc st)
        | cmd_helo arg => do_helo arg st
              (fun (x : bool) (st : STATE) =>
               if x then OutAtom mailc st else OutAtom heloc st)
        | cmd_rcpt_to b => reply_no_mail_from (to_client st) (OutAtom heloc st)
        | _ => reply_no_helo (to_client st) (OutAtom heloc st)
        end)).

Definition get_mail_def (mailc rcptc : chan STATE true) (st : STATE) : proc :=
  get_cmd (in_stream st)
    (fun c : SMTP_cmd =>
     get_arg (in_stream st)
       (fun _ : unit =>
        match c with
        | cmd_unknown => reply_unknown_cmd (to_client st) (OutAtom mailc st)
        | cmd_abort => reply_ok_quit (to_client st) succ
        | cmd_quit => reply_ok_quit (to_client st) succ
        | cmd_rset => reply_ok_rset (to_client st) (OutAtom mailc st)
        | cmd_noop => reply_ok_noop (to_client st) (OutAtom mailc st)
        | cmd_helo _ => reply_dup_helo (to_client st) (OutAtom mailc st)
        | cmd_mail_from arg =>
            do_mail_from arg st
              (fun (b : bool) (st : STATE) =>
               if b then OutAtom rcptc st else OutAtom mailc st)
        | _ => reply_no_mail_from (to_client st) (OutAtom mailc st)
        end)).

Definition get_rcpt_def (mailc rcptc : chan STATE true) (st : STATE) : proc :=
  get_cmd (in_stream st)
    (fun c : SMTP_cmd =>
     get_arg (in_stream st)
       (fun _ : unit =>
        match c with
        | cmd_unknown => reply_unknown_cmd (to_client st) (OutAtom rcptc st)
        | cmd_abort => reply_ok_quit (to_client st) succ
        | cmd_quit => reply_ok_quit (to_client st) succ
        | cmd_rset =>
            reply_ok_rset (to_client st)
              (OutAtom mailc (update_fwd_paths st nil))
        | cmd_noop => reply_ok_noop (to_client st) (OutAtom rcptc st)
        | cmd_helo _ => reply_dup_helo (to_client st) (OutAtom rcptc st)
        | cmd_mail_from arg =>
            reply_dup_mail_from (to_client st) (OutAtom rcptc st)
        | cmd_rcpt_to arg =>
            do_rcpt_to arg st (fun st : STATE => OutAtom rcptc st)
        | cmd_data data =>
            if fwd_paths_size_gt_0 (fwd_paths st)
            then
             save_mail data st
               (reply_ok_data (to_client st)
                  (OutAtom mailc (update_fwd_paths st nil)))
            else reply_no_rcpt_to (to_client st) (OutAtom rcptc st)
        end)).

Axiom server_name0 : String.
Axiom queue_dir0 : File. (* TODO: useful? *)
Axiom buf0 : Buffer. (* set to be defined *)

Axiom from_domain0 : String.
Axiom rev_path0 : Rfc821_path.
Axiom fwd_paths0 : list Rfc821_path.

Definition work (c1 : InputStream) (c2 : OutputStream) (tofs : ToFileSystem) : proc :=
  let st :=
    smtp_state c1 c2
      server_name0 (* server_name of type String *)
      queue_dir0 (* queue_dir of type File *)
      buf0 (* buf of type Buffer *)
      from_domain0 (* from_domain of type String *)
      rev_path0 (* rev_path of type Rfc821_path *)
      nil  (* fwd_paths pf type Rfc821_pathlist *)
      tofs false (* quit of type bool *) in
  nuPl (fun heloc : chan STATE _ =>
     nuPl (fun mailc : chan STATE _ =>
        nuPl (fun rcptc : chan STATE _ =>
           parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP (rcptc ??* get_rcpt_def mailc rcptc) (OutAtom heloc st)))))).




