Add LoadPath "/home/affeldt/src/coq/applpi".

Require Import libapplpi.

Require Import SMTP_applpi_string.
Require Import SMTP_applpi_rfc821.
Require Import SMTP_applpi_filesystem.
Require Import SMTP_applpi_exceptions.
Require Import SMTP_applpi_spec.
Require Import SMTP_applpi.

Extract Inlined Constant String => "string".
Extract Constant server_name0 => "String.create 0".
Extract Inlined Constant File => "string".
Extract Constant queue_dir0 => "String.create 0".
Extract Inlined Constant Buffer => "string".
Extract Constant buf0 => "String.create 0".
Extract Inlined Constant Rfc821_path => "string".
Extract Constant from_domain0 => "String.create 0". (*null string*)
Extract Constant rev_path0 => "String.create 0". (*null string*)

Extract Constant is_nullstr =>
 "fun s -> if String.length s = 0 then true else false".
Extract Constant IOexn_chan => "new channel".
Extract Constant result_chan => "new channel".

Extract Constant parseRfc821path => "fun s -> (SUCC (s, ()))".
Extract Constant is_not_null_a_d_l =>
 "fun s -> if String.length s = 0 then false else true".
Extract Inlined Constant OutputStream => "replyMsg channel".
Extract Inlined Constant InputStream => "sMTP_cmd channel".
Extract Inlined Constant ToFileSystem => "mail channel".

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive unit => "unit" [ "()" ].

Recursive Extraction work.

(** various preliminary lemmas *)

Axiom unit_isnot_chan : forall (A : Set) (b : bool), unit <> chan A b.

Lemma myfree_vars' : free_vars 
  (result_chan & IOexn_chan & system_failure_chan & nilC)
  (OR (OUTPUTS result_chan tt ISANY)
    (OR (OUTPUTS IOexn_chan tt ISANY)
      (OUTPUTS system_failure_chan tt ISANY))).
  red in |- *.
  split.
  intros.
  red in H.
  red in |- *.
  apply NNPP.
  intro.
  generalize (not_or_and _ _ H0); clear H0; intro.
  inversion_clear H0.
  generalize (not_or_and _ _ H2); clear H2; intro.
  inversion_clear H0.
  generalize (not_or_and _ _ H3); clear H3; intro.
  inversion_clear H0.
  clear H4.
  apply H.
  apply OR_notin.
  apply OUTPUTS_notin.
  auto.
  generalize (unit_isnot_chan B b'); intros.
  intro.
  generalize (jmeq_types H4); intro.
  tauto.
  apply ISANY_notin.
  apply OR_notin.
  apply OUTPUTS_notin.
  auto.
  generalize (unit_isnot_chan B b'); intros.
  intro.
  generalize (jmeq_types H4); intro.
  tauto.
  apply ISANY_notin.
  apply OUTPUTS_notin.
  auto.
  generalize (unit_isnot_chan B b'); intros.
  intro.
  generalize (jmeq_types H4); intro.
  tauto.
  apply ISANY_notin.
  intros.
  red in |- *.
  intro.
  inversion_clear H0.
  generalize (inv_OUTPUTS_notin H1); intro.
  inversion_clear H2.
  generalize (inv_OUTPUTS_notin H3); intro.
  generalize (inv_OUTPUTS_notin H4); intros.
  decompose [and] H0; clear H0.
  decompose [and] H2; clear H2.
  decompose [and] H5; clear H5.
  clear H13 H11 H9 H8 H10.
  simpl in H.
  inversion_clear H.
  auto.
  inversion_clear H5.
  auto.
  inversion_clear H.
  auto.
  auto.
Qed.

Lemma myfree_vars : tfree_vars 
  (result_chan & IOexn_chan & system_failure_chan & nilC)
  (ALWAYS (STAT reports_succ_or_error)).
  generalize (free_vars_always 
    (result_chan & IOexn_chan & system_failure_chan & nilC) 
    (STAT reports_succ_or_error)); intro.
  inversion_clear H.
  apply H0.
  apply free_vars_tfree_vars.
  apply myfree_vars'.
Qed.

Lemma client_interface_valid_protocol : forall s P,
 speaks_valid_protocol s P ->
 (exists Q, (exists c, P = s << c >> Q)) \/
 (exists Q, P = IOexn_chan << tt >> Q).
intros.
elim H.
intros.
left; exists P0; exists c; auto.
left; exists zeroP; exists cmd_quit; auto.
left; exists zeroP; exists cmd_abort; auto.
intros.
left; exists P0; exists c; auto.
intros.
right; exists P0; auto.
Qed.

Lemma client_interface_after_helo : forall s P,
 speaks_valid_after_helo s P ->
 (exists Q, (exists c, P = s << c >> Q)) \/
 (exists Q, P = IOexn_chan << tt >> Q).
intros.
elim H.
intros.
left.
exists P0; exists c; auto.
left.
exists zeroP; exists cmd_quit; auto.
left.
exists zeroP; exists cmd_abort; auto.
intros.
inversion_clear H4.
left.
exists P0; exists c; auto.
left.
exists P0; exists c; auto.
intros.
right; exists P0; auto.
Qed.

Lemma client_interface_after_mail : forall s P,
 speaks_valid_after_mail s P ->
 (exists Q, (exists c, P = s << c >> Q)) \/
 (exists Q, P = IOexn_chan << tt >> Q).
intros.
elim H.
intros.
left; exists P0; exists c; auto.
left; exists zeroP; exists cmd_quit; auto.
left; exists zeroP; exists cmd_abort; auto.
intros.
left; exists P0; exists cmd_rset; auto.
intros.
left; exists P0; exists c; auto.
intros.
right; exists P0.
auto.
Qed.

Lemma client_interface_after_rcpt : forall s P,
 speaks_valid_after_rcpt s P ->
 (exists Q, (exists c, P = s << c >> Q)) \/
 (exists Q, P = IOexn_chan << tt >> Q).
intros.
elim H.
intros.
left; exists P0; exists (cmd_data data); auto.
intros.
left; exists zeroP; exists cmd_abort; auto.
left; exists zeroP; exists cmd_quit; auto.
intros.
left; exists P0; exists cmd_rset; auto.
intros.
left; exists P0; exists c; auto.
intros.
right; exists P0; auto.
Qed.

Ltac CheckSearchInc :=
  match goal with
  | id0:(incC ?X1 ?X2) |- (incC ?X3 ?X2) =>
      apply incC_trans with X1; [ CheckInc | trivial ]
  end.

Ltac ConfRedNewAlwaysL new_c :=
  match goal with
  |  |- (tsat (FMUSTEV (ALWAYS ?X1)) (?X2 # ?X3)) =>
      let some_pos := search_nul eps X3 in
      let nul_pos := extract_option some_pos in
      let new_P := rep_nul_cont_simp X3 new_c nul_pos in
      (apply conf_red_new_always with (P' := new_P) (c := new_c);
        [ apply red_new; [ tr_nu | apply chanlist_fresh; auto ]
        | idtac
        | idtac ])
  end.

Lemma free_vars_tnotin : forall L f, tfree_vars L f ->
 forall A b (c : chan A b), ~ in_ChanList c L -> tnotin c f.
intros.
apply NNPP.
intro.
fold (tisin c f) in H1.
red in H.
generalize (H _ _ c); intro.
tauto.
Qed.

Ltac ConfRedComAlways :=
  match goal with
  |  |- (tsat (FMUSTEV (ALWAYS ?X1)) (?X2 # ?X3)) =>
      let  (* check the shape of the goal *)
      lst := search_inout X3 in
      let 	(* search in/out couples *)
      c' := unary_IOlist_to_atom lst in
      let 	(* there should be only one *)
      out_pos := unary_IOlist_to_atom_out lst in
      let 	(* position of the output *)
      val := pickup_val X3 out_pos in
      let 	(* value to be send *)
      ns := rep_cont X3 lst in
      let 	(* perform communications *)
      new_P := unary_listT_to_atom ns in
      (	(* pick up the leading process *)
        apply conf_red_com_always with (c := c') (P' := new_P);
        [ 	(* apply lemma *)
           apply red_com; decomp val | idtac ])
  end.		(* prove communication *)

Lemma stable_decompose : forall P1 P2 L,
 Stable (L # P1) ->
 Stable (L # P2) ->
 forall L1 L2 : ChanList,
 guarded L1 P1 ->
 guarded L2 P2 -> inter L1 L2 nilC -> Stable (L # parP P1 P2).
intros.
intro.
inversion_clear H4.
inversion_clear H5.
inversion H4.
clear H5 L0 H7 P.
generalize (inv_trans_tau H9); intro.
inversion_clear H5.
inversion_clear H7.
inversion_clear H5.
inversion_clear H10.
inversion_clear H5.
inversion_clear H10.
inversion_clear H5.
decompose [and] H10; clear H10.
injection H7; intros.
rewrite <- H11 in H5.
rewrite <- H10 in H12.
generalize (guarded_out H1 H5); intro.
generalize (guarded_in H2 H12); intro.
red in H3.
generalize (H3 _ _ x1); intro.
inversion_clear H16.
simpl in H17.
intuition.
inversion_clear H5.
inversion_clear H10.
decompose [and] H5; clear H5.
injection H7; intros.
rewrite <- H5 in H10.
rewrite <- H11 in H12.
generalize (guarded_in H1 H12); intros.
generalize (guarded_out H2 H10); intros.
red in H3.
generalize (H3 _ _ x1); intros; intuition.
inversion_clear H10.
inversion_clear H5.
injection H7; intros.
rewrite <- H12 in H10.
apply H.
exists (L # x4).
exists (epsilon x1).
apply red_com.
auto.
inversion_clear H5.
injection H7; intros.
rewrite <- H5 in H10.
apply H0.
exists (L # x5).
exists (epsilon x1).
apply red_com.
auto.
inversion H7.
clear H11 P0.
apply H.
exists (x1 & L # P').
exists (New x1).
apply red_new.
auto.
auto.
clear H11 H13 P0 Q0.
apply H0.
exists (x1 & L # P').
exists (New x1).
apply red_new.
auto.
auto.
Qed.

Theorem server_accepts_valid_protocol' : 
  forall Client : InputStream -> OutputStream -> proc,
    (forall (s : InputStream) (y : OutputStream),
      exists C1 : proc,
        (exists C2 : proc,
          speaks_valid_protocol s C1 /\
          acknowledges_replies y C2 /\ Client s y = parP C1 C2)) ->
    forall file_system : ToFileSystem -> proc,
      (forall tofs : ToFileSystem, valid_fs tofs (file_system tofs)) ->
      ChanList_is_set (result_chan & IOexn_chan & system_failure_chan & nilC) ->
      (result_chan & IOexn_chan & system_failure_chan & nilC
        # nuPl (fun s1 : InputStream =>
          nuPl (fun s2 : OutputStream =>
            nuPl (fun tofs : ToFileSystem =>
              parP (Client s1 s2)
              (parP (work s1 s2 tofs) 
                (parP (file_system tofs) 
                  may_fail))))))
    |=t (FMUSTEV (ALWAYS (STAT reports_succ_or_error))).
intros Client HClient file_system Hfs SET.
apply cong_resp_tsat with
    (parP zeroP
       (nuPl (fun s1 : InputStream =>
           nuPl (fun s2 : OutputStream =>
              nuPl (fun tofs : ToFileSystem =>
                 parP (Client s1 s2)
                   (parP (work s1 s2 tofs) 
                     (parP (file_system tofs) 
                       may_fail))))))).
apply red_new_deterl.
CheckStable.
simpl in |- *; auto.
auto.
CheckInc.
intros.
generalize (chanlist_is_set_extend _ SET _ _ _ H); clear SET H; intro SET.
apply red_new_deterl.
CheckStable.
simpl in |- *; auto.
auto.
CheckInc.
intros.
generalize (chanlist_is_set_extend _ SET _ _ _ H); clear SET H; intro SET.
rename c0 into c'.
apply red_new_deterl.
CheckStable.
simpl in |- *; auto.
auto.
CheckInc.
intros.
generalize (chanlist_is_set_extend _ SET _ _ _ H); clear SET H; intro SET.
rename c0 into tofs.
clean_zero.
unfold work in |- *.

ChooseFreshL_set STATE ipattern:heloc.

ConfRedNewAlwaysL heloc.

generalize myfree_vars'.
intro.
apply
 free_vars_tnotin
  with (result_chan & IOexn_chan & system_failure_chan & nilC).
apply free_vars_tfree_vars.
auto.
CheckNotInChanList2 Set.
ChooseFreshL_set STATE ipattern:mailc.

ConfRedNewAlwaysL mailc.
generalize myfree_vars'.
intro.
apply
 free_vars_tnotin
  with (result_chan & IOexn_chan & system_failure_chan & nilC).
apply free_vars_tfree_vars.
auto.
CheckNotInChanList2 SET.

ChooseFreshL_set STATE ipattern:rcptc.

ConfRedNewAlwaysL rcptc.
generalize myfree_vars'.
intro.
apply
 free_vars_tnotin
  with (result_chan & IOexn_chan & system_failure_chan & nilC).
apply free_vars_tfree_vars.
auto.
CheckNotInChanList2 SET.

generalize (HClient c c'); intro HClient'.
inversion_clear HClient'.
inversion_clear H.
decompose [and] H0; clear H0.
rename x into Client1.
rename x0 into Client2.
rewrite H3; clear H3.

(* generalize that part of the client that acks replies *)

generalize Client2 H2; clear Client2 H2.

(* generalize the list of channels created so far to any bigger list *)

cut
 (forall Client2 : proc,
  acknowledges_replies c' Client2 ->
  forall L : ChanList,
  ChanList_is_set L ->
  incC
    (rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC) L ->
  tsat (FMUSTEV (ALWAYS (STAT reports_succ_or_error)))
    (L
     # parP (parP Client1 Client2)
         (parP
            (parP (heloc ??*get_helo_def heloc mailc)
               (parP (mailc ??*get_mail_def mailc rcptc)
                  (parP (rcptc ??*get_rcpt_def mailc rcptc)
                     (OutAtom heloc
                        (smtp_state c c' server_name0 queue_dir0 buf0
                           from_domain0 rev_path0 nil tofs false)))))
            (parP (file_system tofs) may_fail)))).
intros.
apply H0.
auto.
auto.
CheckInc.

Scheme speaks_valid_protocol_ind1 := Minimality for speaks_valid_protocol
  Sort Prop
  with speaks_valid_protocol_ind2 := Minimality for speaks_valid_after_helo
  Sort Prop
  with speaks_valid_protocol_ind3 := Minimality for speaks_valid_after_mail
  Sort Prop
  with speaks_valid_protocol_ind4 := Minimality for speaks_valid_after_rcpt
  Sort Prop.

(* to show that P holds we show that
P holds under P0,
P0 holds under P1,
P1 holds under P2,
P2 holds under P0
where Pi are given below *)

elim H using
 speaks_valid_protocol_ind1
  with
    (P0 := fun Client1 : proc =>
           forall L : ChanList,
           incC
             (rcptc &
              mailc &
              heloc &
              tofs &
              c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)
             L ->
           ChanList_is_set L ->
           forall Client2 : proc,
           acknowledges_replies c' Client2 ->
           forall (from : String) (rev_path : Rfc821_path)
             (fwd_p : list Rfc821_path),
           fwd_p = nil -> (* observe the conditions on forward paths *)
           forall FS : proc,
           valid_fs tofs FS ->
           tsat (FMUSTEV (ALWAYS (STAT reports_succ_or_error)))
             (L
              # parP
                  (parP (heloc ??*get_helo_def heloc mailc)
                     (parP (mailc ??*get_mail_def mailc rcptc)
                        (parP (rcptc ??*get_rcpt_def mailc rcptc)
                           (OutAtom mailc
                              (update_from
                                 (smtp_state c c' server_name0 queue_dir0
                                    buf0 from rev_path fwd_p tofs false) from)))))
                  (parP (parP Client1 Client2) (parP FS may_fail))))
    (P1 := fun Client1 : proc =>
           forall L : ChanList,
           incC
             (rcptc &
              mailc &
              heloc &
              tofs &
              c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)
             L ->
           ChanList_is_set L ->
           forall Client2 : proc,
           acknowledges_replies c' Client2 ->
           forall (from : String) (rev_path : Rfc821_path)
             (fwd_p : list Rfc821_path),
           fwd_p = nil -> (* observe the conditions on forward paths *)
           forall FS : proc,
           valid_fs tofs FS ->
           tsat (FMUSTEV (ALWAYS (STAT reports_succ_or_error)))
             (L
              # parP
                  (parP (heloc ??*get_helo_def heloc mailc)
                     (parP (mailc ??*get_mail_def mailc rcptc)
                        (parP (rcptc ??*get_rcpt_def mailc rcptc)
                           (OutAtom rcptc
                              (smtp_state c c' server_name0 queue_dir0 buf0
                                 from rev_path fwd_p tofs false)))))
                  (parP (parP Client1 Client2) (parP FS may_fail))))
    (P2 := fun Client1 : proc =>
           forall L : ChanList,
           incC
             (rcptc &
              mailc &
              heloc &
              tofs &
              c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)
             L ->
           ChanList_is_set L ->
           forall Client2 : proc,
           acknowledges_replies c' Client2 ->
           forall (from : String) (rev_path : Rfc821_path)
             (p : list Rfc821_path),
           p <> nil -> (* observe the conditions on forward paths *)
           forall FS : proc,
           valid_fs tofs FS ->
           tsat (FMUSTEV (ALWAYS (STAT reports_succ_or_error)))
             (L
              # parP
                  (parP (heloc ??*get_helo_def heloc mailc)
                     (parP (mailc ??*get_mail_def mailc rcptc)
                        (parP (rcptc ??*get_rcpt_def mailc rcptc)
                           (OutAtom rcptc
                              (smtp_state c c' server_name0 queue_dir0 buf0
                                 from rev_path p tofs false)))))
                  (parP (parP Client1 Client2) (parP FS may_fail)))).

(* first subgoal : if the client is ok beyond the mail message, then it is ok beyond the helo messagee *)

(* command helo *)

intros P c0 Hc0 HP H0 Client2 HClient2 LST SET' INC.

ConfRedComAlways.

unfold get_helo_def at 2 in |- *.
unfold get_cmd at 1 in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
unfold do_helo in |- *.
inversion Hc0.
rewrite H1.
simpl in |- *.
unfold reply_ok_helo in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??*get_helo_def heloc mailc)
          (parP (mailc ??*get_mail_def mailc rcptc)
             (parP (rcptc ??*get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 arg
                         rev_path0 nil tofs false) arg)))))
       (parP (parP P (P0 rep_ok_helo)) (parP (file_system tofs) may_fail))).
apply H0.
auto.
simpl in SET'.
intuition.
apply H3.
auto.
auto.

EvalRewrite
 (update_from
    (smtp_state c c' server_name0 queue_dir0 buf0 from_domain0 rev_path0 nil
       tofs false) arg).
EvalRewrite
 (update_from
    (smtp_state c c' server_name0 queue_dir0 buf0 arg rev_path0 nil tofs
       false) arg).
ProcCong.

(* cas ou le client renvoie une exception reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP (parP P (IOexn_chan << tt >>P0))
          (parP
             (parP
                (parP (heloc ??*get_helo_def heloc mailc)
                   (c' << rep_ok_helo >>OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0
                            from_domain0 rev_path0 nil tofs false) arg)))
                (parP (mailc ??*get_mail_def mailc rcptc)
                   (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
             (file_system tofs))) may_fail).

unfold may_fail in |- *.

generalize (client_interface_after_helo _ _ HP); intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
rewrite H5.
generalize (Hfs tofs); intro X; inversion_clear X.
unfold OutAtom, InAtom in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).

apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
auto.

apply red_com_nondeter.

CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.

CheckStable.

generalize H6; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.

CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.

apply now_is_FMUSTEV.

apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.

CheckStable.

generalize H6; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.

CheckIncWeak.
CheckSearchInc.

inversion_clear H5.
rewrite H4.
generalize (Hfs tofs); intro X; inversion_clear X.
unfold OutAtom, InAtom in |- *.

apply red_new_deter.
apply
 cong_respects_stable
  with
    (LST
     # parP
         (parP (parP (IOexn_chan << tt >>x) (IOexn_chan << tt >>P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??*get_helo_def heloc mailc)
                  (c' << rep_ok_helo >>(mailc
                    << update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0
                            from_domain0 rev_path0 nil tofs false) arg >>zeroP)))
               (parP (mailc ??*get_mail_def mailc rcptc)
                  (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
            (tofs ??P1))).

eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (LST # IOexn_chan << tt >>x).
intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion H7.
inversion H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.
CheckNotInChanList2 SET.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).

apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
auto.

apply red_com_nondeter.

CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.

apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >>x) (IOexn_chan << tt >>P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??*get_helo_def heloc mailc)
                        (c' << rep_ok_helo >>(mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from_domain0 rev_path0 nil tofs false) arg >>zeroP)))
                     (parP (mailc ??*get_mail_def mailc rcptc)
                        (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ??P1)))
            (parP (failc ??(fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >>zeroP))))).

eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >>x).
intro.
inversion_clear H7.
inversion_clear H8.
inversion_clear H7.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.

CheckIncWeak.

CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.

CheckNotInChanList2 H6.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.

apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.

apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >>x) (IOexn_chan << tt >>P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??*get_helo_def heloc mailc)
                        (c' << rep_ok_helo >>(mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from_domain0 rev_path0 nil tofs false) arg >>zeroP)))
                     (parP (mailc ??*get_mail_def mailc rcptc)
                        (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ??P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ??(fun _ : unit => system_failure_chan << tt >>zeroP)))))).

eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >>x).
intro.
inversion_clear H7.
inversion_clear H8.
inversion_clear H7.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.

CheckNotInChanList2 H6.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* quit message *)

intros Client2 ack_rep0 LST SET' INC.

ConfRedComAlways.

unfold get_helo_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
unfold reply_ok_quit in |- *.
unfold reply in |- *.

inversion_clear ack_rep0.

ConfRedComAlways.

generalize (H0 rep_ok_quit); intro X; inversion_clear X.

apply
 cong_resp_tsat
  with
    (parP
       (parP (parP zeroP (c' ??P0))
          (parP
             (parP (parP (heloc ??*get_helo_def heloc mailc) succ)
                (parP (mailc ??*get_mail_def mailc rcptc)
                   (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
             (file_system tofs))) may_fail).
unfold may_fail in |- *.

generalize (Hfs tofs); intro X; inversion_clear X.
unfold InAtom, OutAtom in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
auto.

apply red_com_nondeter.

CheckExistsGuard.
CheckUnstable.
intros.
unfold succ in H4.
unfold OutAtom in H4.
NextComms.
simpl in |- *.
intro.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.

generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.

CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.

generalize H3; CheckListSet.
apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

(* ioerror when sending to the client *)

apply
 cong_resp_tsat
  with
    (parP
       (parP (parP zeroP (IOexn_chan << tt >>P0))
          (parP
             (parP (parP (heloc ??*get_helo_def heloc mailc) succ)
                (parP (mailc ??*get_mail_def mailc rcptc)
                   (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
             (file_system tofs))) may_fail).

generalize (Hfs tofs); intro X; inversion_clear X.
unfold may_fail in |- *.
unfold OutAtom, InAtom in |- *.

apply red_new_deter.

CheckStable.

generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
auto.

apply red_com_nondeter.

CheckExistsGuard.
CheckUnstable.
intros.
unfold succ, InAtom, OutAtom in H4.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.

generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.

generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

apply
 cong_resp_tsat
  with
    (parP
       (parP (parP zeroP (IOexn_chan << tt >>P))
          (parP
             (parP
                (parP (heloc ??*get_helo_def heloc mailc)
                   (c' << rep_ok_quit >>succ))
                (parP (mailc ??*get_mail_def mailc rcptc)
                   (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
             (file_system tofs))) may_fail).
unfold may_fail in |- *.
generalize (Hfs tofs); intro X; inversion_clear X.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
auto.

apply red_com_nondeter.

CheckExistsGuard.
CheckUnstable.
unfold succ, OutAtom, InAtom in |- *.
intros.
NextComms.
simpl in |- *.
intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

(* command abort *)

intros Client2 ack_rep0 LST SET' INC.

ConfRedComAlways.

unfold get_helo_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
unfold reply_ok_quit in |- *.
unfold reply in |- *.

inversion_clear ack_rep0.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (parP zeroP (P rep_ok_quit))
          (parP
             (parP (parP (heloc ??*get_helo_def heloc mailc) succ)
                (parP (mailc ??*get_mail_def mailc rcptc)
                   (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
             (file_system tofs))) may_fail).

generalize (H0 rep_ok_quit); intro X; inversion_clear X.
generalize (Hfs tofs); intro X; inversion_clear X.
unfold may_fail, succ, InAtom, OutAtom in |- *.

apply red_new_deter.

CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.

CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intro.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.

generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.

generalize H3; CheckListSet.

auto.
apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


generalize (Hfs tofs); intro X; inversion_clear X.
unfold may_fail, InAtom, OutAtom in |- *.

apply red_new_deter.
CheckStable.

generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

unfold succ, OutAtom, InAtom in |- *.

apply red_com_nondeter.

CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.

generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.

generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

apply
 cong_resp_tsat
  with
    (parP
       (parP (parP zeroP (IOexn_chan << tt >>P))
          (parP
             (parP
                (parP (heloc ??*get_helo_def heloc mailc)
                   (c' << rep_ok_quit >>succ))
                (parP (mailc ??*get_mail_def mailc rcptc)
                   (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
             (file_system tofs))) may_fail).
unfold may_fail, succ, InAtom, OutAtom in |- *.
generalize (Hfs tofs); intro X; inversion_clear X.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.

CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
intros.
simpl in H3; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *; SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *; SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


ProcCong.

(* other commands (skip case) *)

intros P c0 not_helo_c0 not_quit_c0 not_abort_c0 HP.
intro.
intros Client2 ack_rep0 LST SET' INC.

ConfRedComAlways.

unfold get_helo_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
inversion_clear ack_rep0.

(* no io error *)

induction c0.

(* heloc command *)

unfold do_helo in |- *.
assert (is_nullstr s = true).
apply NNPP.
intro abs.
assert (valid_cmd_helo (cmd_helo s)).
apply valid_cmd_h.
generalize abs.
case (is_nullstr s).
intro X.
apply NNPP; intro; apply X; auto.
auto.
apply not_helo_c0; auto.
rewrite H2.

unfold reply_bad_helo in |- *.
unfold reply in |- *.

simpl in |- *.
ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP (parP P (P0 rep_bad_helo))
       (parP
          (parP (heloc ??*get_helo_def heloc mailc)
             (parP (mailc ??*get_mail_def mailc rcptc)
                (parP (rcptc ??*get_rcpt_def mailc rcptc)
                   (OutAtom heloc
                      (smtp_state c c' server_name0 queue_dir0 buf0
                         from_domain0 rev_path0 nil tofs false)))))
          (parP (file_system tofs) may_fail))).
apply H0.
apply H1.
auto.
CheckSearchInc.
ProcCong.

(* mail_from command *)

unfold reply_no_helo in |- *.
unfold reply in |- *.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP (parP P (P0 rep_no_helo))
       (parP
          (parP (heloc ??*get_helo_def heloc mailc)
             (parP (mailc ??*get_mail_def mailc rcptc)
                (parP (rcptc ??*get_rcpt_def mailc rcptc)
                   (OutAtom heloc
                      (smtp_state c c' server_name0 queue_dir0 buf0
                         from_domain0 rev_path0 nil tofs false)))))
          (parP (file_system tofs) may_fail))).
apply H0.
apply H1.
auto.
CheckSearchInc.
ProcCong.

(* command rcpt_to *)

unfold reply_no_mail_from in |- *.
unfold reply in |- *.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP (parP P (P0 rep_no_mail_from))
       (parP
          (parP (heloc ??*get_helo_def heloc mailc)
             (parP (mailc ??*get_mail_def mailc rcptc)
                (parP (rcptc ??*get_rcpt_def mailc rcptc)
                   (OutAtom heloc
                      (smtp_state c c' server_name0 queue_dir0 buf0
                         from_domain0 rev_path0 nil tofs false)))))
          (parP (file_system tofs) may_fail))).
apply H0.
apply H1.
auto.
CheckSearchInc.
ProcCong.

(* command cmd_data *)

unfold reply_no_helo in |- *.
unfold reply in |- *.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP (parP P (P0 rep_no_helo))
       (parP
          (parP (heloc ??*get_helo_def heloc mailc)
             (parP (mailc ??*get_mail_def mailc rcptc)
                (parP (rcptc ??*get_rcpt_def mailc rcptc)
                   (OutAtom heloc
                      (smtp_state c c' server_name0 queue_dir0 buf0
                         from_domain0 rev_path0 nil tofs false)))))
          (parP (file_system tofs) may_fail))).
apply H0.
apply H1.
auto.
CheckSearchInc.
ProcCong.

(* command cmd_noop *)

unfold reply_ok_noop in |- *.
unfold reply in |- *.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP (parP P (P0 rep_ok_noop))
       (parP
          (parP (heloc ??*get_helo_def heloc mailc)
             (parP (mailc ??*get_mail_def mailc rcptc)
                (parP (rcptc ??*get_rcpt_def mailc rcptc)
                   (OutAtom heloc
                      (smtp_state c c' server_name0 queue_dir0 buf0
                         from_domain0 rev_path0 nil tofs false)))))
          (parP (file_system tofs) may_fail))).
apply H0.
apply H1.
auto.
CheckSearchInc.
ProcCong.

(* command rset *)

unfold reply_ok_rset in |- *.
unfold reply in |- *.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP (parP P (P0 rep_ok_rset))
       (parP
          (parP (heloc ??*get_helo_def heloc mailc)
             (parP (mailc ??*get_mail_def mailc rcptc)
                (parP (rcptc ??*get_rcpt_def mailc rcptc)
                   (OutAtom heloc
                      (smtp_state c c' server_name0 queue_dir0 buf0
                         from_domain0 rev_path0 nil tofs false)))))
          (parP (file_system tofs) may_fail))).
apply H0.
apply H1.
auto.
CheckSearchInc.
ProcCong.

(* command quit *)

generalize (not_quit_c0 (refl_equal cmd_quit)); contradiction.

(* command abort *)

generalize (not_abort_c0 (refl_equal cmd_abort)); contradiction.

(* command unknown *)

unfold reply_unknown_cmd in |- *.
unfold reply in |- *.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP (parP P (P0 rep_unknown_cmd))
       (parP
          (parP (heloc ??*get_helo_def heloc mailc)
             (parP (mailc ??*get_mail_def mailc rcptc)
                (parP (rcptc ??*get_rcpt_def mailc rcptc)
                   (OutAtom heloc
                      (smtp_state c c' server_name0 queue_dir0 buf0
                         from_domain0 rev_path0 nil tofs false)))))
          (parP (file_system tofs) may_fail))).
apply H0.
apply H1.
auto.
CheckSearchInc.
ProcCong.

apply
 cong_resp_tsat
  with
    (parP
       (parP (parP P (IOexn_chan << tt >>P0))
          (parP
             (parP
                (parP (heloc ??*get_helo_def heloc mailc)
                   match c0 with
                   | cmd_helo arg =>
                       do_helo arg
                         (smtp_state c c' server_name0 queue_dir0 buf0
                            from_domain0 rev_path0 nil tofs false)
                         (fun (x : bool) (st : STATE) =>
                          if x then OutAtom mailc st else OutAtom heloc st)
                   | cmd_mail_from _ =>
                       reply_no_helo c'
                         (OutAtom heloc
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false))
                   | cmd_rcpt_to _ =>
                       reply_no_mail_from c'
                         (OutAtom heloc
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false))
                   | cmd_data _ =>
                       reply_no_helo c'
                         (OutAtom heloc
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false))
                   | cmd_noop =>
                       reply_ok_noop c'
                         (OutAtom heloc
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false))
                   | cmd_rset =>
                       reply_ok_rset c'
                         (OutAtom heloc
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false))
                   | cmd_quit => reply_ok_quit c' succ
                   | cmd_abort => reply_ok_quit c' succ
                   | cmd_unknown =>
                       reply_unknown_cmd c'
                         (OutAtom heloc
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false))
                   end)
                (parP (mailc ??*get_mail_def mailc rcptc)
                   (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
             (file_system tofs))) may_fail).
generalize (Hfs tofs); intro X; inversion_clear X.
unfold may_fail, InAtom, OutAtom in |- *.
generalize (client_interface_valid_protocol _ _ HP); intro X;
 inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.

induction c0 as [s| s| s| s| | | | | ].

(* cmd_helo *)

unfold do_helo in |- *.

cut (is_nullstr s = true \/ is_nullstr s = false).
intro X; inversion_clear X.
rewrite H4.
unfold reply_bad_helo in |- *.
unfold reply in |- *.
simpl in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H5; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H5; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


assert (valid_cmd_helo (cmd_helo s)).
apply valid_cmd_h.
auto.
generalize (not_helo_c0 H5); contradiction.
case (is_nullstr s); [ auto | auto ].

(* cmd_mail *)

unfold reply_no_helo in |- *.
unfold reply in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


(* cmd rcpt *)

unfold reply_no_mail_from in |- *.
unfold reply in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


(* cmd data *)

unfold reply_no_helo in |- *.
unfold reply in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

(* cmd noop *)

unfold reply_ok_noop in |- *.
unfold reply in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

(* cmd rset *)

unfold reply_ok_rset in |- *.
unfold reply in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.
auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.
apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.
apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

(* cmd_quit *)

generalize (not_quit_c0 (refl_equal cmd_quit)); contradiction.

(* cmd_abort *)

generalize (not_abort_c0 (refl_equal cmd_abort)); contradiction.

(* cmd_unknown *)

unfold reply_unknown_cmd in |- *.
unfold reply in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


(* a network has occured on the directed link from the client to the server *)

inversion_clear H3.
rewrite H4.

induction c0 as [s| s| s| s| | | | | ].

(* cmd_helo *)

unfold do_helo in |- *.
cut (is_nullstr s = true \/ is_nullstr s = false).
intro X; inversion_clear X.
rewrite H3.
unfold reply_bad_helo, reply in |- *.
simpl in |- *.

apply red_new_deter.

eapply stable_decompose.
apply
 cong_respects_stable
  with
    (LST # parP (parP (IOexn_chan << tt >>x) (IOexn_chan << tt >>P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (LST # IOexn_chan << tt >>x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.


intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >>x) (IOexn_chan << tt >>P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??*get_helo_def heloc mailc)
                        (c' << rep_bad_helo >>(heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >>zeroP)))
                     (parP (mailc ??*get_mail_def mailc rcptc)
                        (parP (rcptc ??*get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ??P1)))
            (parP (failc ??(fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >>zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >>x).
intro.

inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H5; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_bad_helo >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H5; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].
assert (valid_cmd_helo (cmd_helo s)).
apply valid_cmd_h.
auto.
generalize (not_helo_c0 H5); contradiction.
case (is_nullstr s); [ auto | auto ].

(* cmd_mail_from *)

unfold reply_no_helo, reply in |- *.
simpl in |- *.

apply red_new_deter.
eapply stable_decompose.
apply
 cong_respects_stable
  with
    (LST # parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (LST # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.


intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_no_helo >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_no_helo >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

(* cmd rcpt *) 

unfold reply_no_mail_from, reply in |- *.
simpl in |- *.

apply red_new_deter.
eapply stable_decompose.
apply
 cong_respects_stable
  with
    (LST # parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (LST # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.


intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_no_mail_from >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_no_mail_from >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

(* cmd_data *) 

unfold reply_no_helo, reply in |- *.
simpl in |- *.

apply red_new_deter.
eapply stable_decompose.
apply
 cong_respects_stable
  with
    (LST # parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (LST # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.


intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_no_helo >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_no_helo >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

(* cmd noop *)

unfold reply_ok_noop, reply in |- *.
simpl in |- *.

apply red_new_deter.
eapply stable_decompose.
apply
 cong_respects_stable
  with
    (LST # parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (LST # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.


intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_ok_noop >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_ok_noop >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

(* cmd rset *)

unfold reply_ok_rset, reply in |- *.
simpl in |- *.

apply red_new_deter.
eapply stable_decompose.
apply
 cong_respects_stable
  with
    (LST # parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (LST # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_ok_rset >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_ok_rset >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

(* cmd_quit *)

generalize (not_quit_c0 (refl_equal cmd_quit)); contradiction.

(* cmd_abort *)

generalize (not_abort_c0 (refl_equal cmd_abort)); contradiction.

(* cmd_unknown *)

unfold reply_unknown_cmd, reply in |- *.
simpl in |- *.

apply red_new_deter.
eapply stable_decompose.
apply
 cong_respects_stable
  with
    (LST # parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (LST # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.


intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_unknown_cmd >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP zeroP
               (parP
                  (parP
                     (parP (heloc ??* get_helo_def heloc mailc)
                        (c' << rep_unknown_cmd >>
                         (heloc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from_domain0 rev_path0 nil tofs false >> zeroP)))
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
                  (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.


(* network error *)


intros P HP H0 Client2 HClient2 LST SET' INC.

ConfRedComAlways.

unfold get_helo_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

inversion_clear HClient2.
apply
 cong_resp_tsat
  with
    (parP
       (parP (parP (IOexn_chan << tt >> P) (c' ?? P0))
          (parP
             (parP
                (parP (heloc ??* get_helo_def heloc mailc)
                   (c
                    ?? (fun c0 : SMTP_cmd =>
                        get_arg c
                          (fun _ : unit =>
                           match c0 with
                           | cmd_helo arg =>
                               do_helo arg
                                 (smtp_state c c' server_name0 queue_dir0
                                    buf0 from_domain0 rev_path0 nil tofs
                                    false)
                                 (fun (x : bool) (st : STATE) =>
                                  if x
                                  then OutAtom mailc st
                                  else OutAtom heloc st)
                           | cmd_mail_from _ =>
                               reply_no_helo c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_rcpt_to _ =>
                               reply_no_mail_from c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_data _ =>
                               reply_no_helo c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_noop =>
                               reply_ok_noop c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_rset =>
                               reply_ok_rset c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_quit => reply_ok_quit c' succ
                           | cmd_abort => reply_ok_quit c' succ
                           | cmd_unknown =>
                               reply_unknown_cmd c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           end))))
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
             (file_system tofs))) may_fail).
unfold may_fail in |- *.
generalize (Hfs tofs); intro fs.
inversion_clear fs.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).

apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
auto.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
unfold InAtom, OutAtom in |- *.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.

CheckStable.

generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.

apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.

CheckStable.

generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


ProcCong.

apply
 cong_resp_tsat
  with
    (parP
       (parP (parP (IOexn_chan << tt >> P) (IOexn_chan << tt >> P0))
          (parP
             (parP
                (parP (heloc ??* get_helo_def heloc mailc)
                   (c
                    ?? (fun c0 : SMTP_cmd =>
                        get_arg c
                          (fun _ : unit =>
                           match c0 with
                           | cmd_helo arg =>
                               do_helo arg
                                 (smtp_state c c' server_name0 queue_dir0
                                    buf0 from_domain0 rev_path0 nil tofs
                                    false)
                                 (fun (x : bool) (st : STATE) =>
                                  if x
                                  then OutAtom mailc st
                                  else OutAtom heloc st)
                           | cmd_mail_from _ =>
                               reply_no_helo c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_rcpt_to _ =>
                               reply_no_mail_from c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_data _ =>
                               reply_no_helo c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_noop =>
                               reply_ok_noop c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_rset =>
                               reply_ok_rset c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           | cmd_quit => reply_ok_quit c' succ
                           | cmd_abort => reply_ok_quit c' succ
                           | cmd_unknown =>
                               reply_unknown_cmd c'
                                 (OutAtom heloc
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from_domain0 rev_path0 nil tofs
                                       false))
                           end))))
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
             (file_system tofs))) may_fail).
unfold may_fail in |- *.
generalize (Hfs tofs); intro fs.
inversion_clear fs.

apply red_new_deter.


eapply stable_decompose.
apply
 cong_respects_stable
  with
    (LST # parP (parP (IOexn_chan << tt >> P) (IOexn_chan << tt >> P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (LST # IOexn_chan << tt >> P).
intro.
inversion_clear H3.
inversion_clear H4.
inversion_clear H3.
inversion_clear H4.
inversion_clear H4.
red in |- *.
intuition.
simpl in |- *.
ProcCong.
red in |- *.
intuition.
simpl in |- *.
ProcCong.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).

apply chanlist_is_set_extend.
auto.
apply incC_fresh with LST.
auto.
auto.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
unfold InAtom, OutAtom in |- *.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.

apply
 cong_respects_stable
  with
    (failc & LST
     # parP (parP (IOexn_chan << tt >> P) (IOexn_chan << tt >> P0))
         (parP
            (parP
               (parP
                  (parP (heloc ??* get_helo_def heloc mailc)
                     (c
                      ?? (fun c0 : SMTP_cmd =>
                          get_arg c
                            (fun _ : unit =>
                             match c0 with
                             | cmd_helo arg =>
                                 do_helo arg
                                   (smtp_state c c' server_name0 queue_dir0
                                      buf0 from_domain0 rev_path0 nil tofs
                                      false)
                                   (fun (x : bool) (st : STATE) =>
                                    if x
                                    then mailc << st >> zeroP
                                    else heloc << st >> zeroP)
                             | cmd_mail_from _ =>
                                 reply_no_helo c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_rcpt_to _ =>
                                 reply_no_mail_from c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_data _ =>
                                 reply_no_helo c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_noop =>
                                 reply_ok_noop c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_rset =>
                                 reply_ok_rset c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_quit => reply_ok_quit c' succ
                             | cmd_abort => reply_ok_quit c' succ
                             | cmd_unknown =>
                                 reply_unknown_cmd c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             end))))
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (tofs ?? P1))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP (parP (IOexn_chan << tt >> P) (IOexn_chan << tt >> P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> P).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *.
intuition.
simpl in |- *.
ProcCong.
red in |- *.
intuition.
simpl in |- *.
ProcCong.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *.
intuition.
simpl in |- *; ProcCong.

intro X; rewrite X; clear X.

apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.

apply
 cong_respects_stable
  with
    (failc & LST
     # parP (parP (IOexn_chan << tt >> P) (IOexn_chan << tt >> P0))
         (parP
            (parP
               (parP
                  (parP (heloc ??* get_helo_def heloc mailc)
                     (c
                      ?? (fun c0 : SMTP_cmd =>
                          get_arg c
                            (fun _ : unit =>
                             match c0 with
                             | cmd_helo arg =>
                                 do_helo arg
                                   (smtp_state c c' server_name0 queue_dir0
                                      buf0 from_domain0 rev_path0 nil tofs
                                      false)
                                   (fun (x : bool) (st : STATE) =>
                                    if x
                                    then mailc << st >> zeroP
                                    else heloc << st >> zeroP)
                             | cmd_mail_from _ =>
                                 reply_no_helo c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_rcpt_to _ =>
                                 reply_no_mail_from c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_data _ =>
                                 reply_no_helo c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_noop =>
                                 reply_ok_noop c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_rset =>
                                 reply_ok_rset c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             | cmd_quit => reply_ok_quit c' succ
                             | cmd_abort => reply_ok_quit c' succ
                             | cmd_unknown =>
                                 reply_unknown_cmd c'
                                   (heloc
                                    << smtp_state c c' server_name0
                                         queue_dir0 buf0 from_domain0
                                         rev_path0 nil tofs false >> zeroP)
                             end))))
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (tofs ?? P1))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply
 cong_respects_stable
  with
    (failc & LST
     # parP (parP (IOexn_chan << tt >> P) (IOexn_chan << tt >> P0)) zeroP).
apply stable_outP_dup.
apply cong_respects_stable with (failc & LST # IOexn_chan << tt >> P).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *.
intuition.
simpl in |- *.
ProcCong.
red in |- *.
intuition.
simpl in |- *.
ProcCong.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *.
intuition.
simpl in |- *; ProcCong.
ProcCong.

(* second subgoal : if the behavior is ok beyond the rcpt message, it is ok beyong the mail
message *)

intros P c0 Hc0 HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.

ConfRedComAlways.

unfold get_mail_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
inversion_clear Hc0.
unfold do_mail_from in |- *.
generalize (proj1 (ax_parse arg) p H1); intro.
rewrite H2.
simpl in |- *.
unfold reply_ok_mail_from in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from p fwd_p
                      tofs false)))))
       (parP (parP P (P0 rep_ok_mail_from)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
apply H3.
auto.
auto.

EvalRewrite
 (update_rev_path
    (update_from
       (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p fwd_p tofs
          false) from) p).

ProcCong.

(* cas de l'erreur reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_ok_mail_from >>
                    OutAtom rcptc
                      (update_rev_path
                         (update_from
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) from) p)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) FS)) may_fail).
unfold may_fail in |- *.
apply red_new_deter.
inversion_clear HFS.

generalize (client_interface_after_mail _ _ HP); intro X; inversion_clear X.
inversion_clear H5.
inversion_clear H6.
rewrite H5.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
inversion_clear H5.
rewrite H6.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (c' << rep_ok_mail_from >>
                      OutAtom rcptc
                        (update_rev_path
                           (update_from
                              (smtp_state c c' server_name0 queue_dir0 buf0
                                 from rev_p fwd_p tofs false) from) p)))
                  (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
            (parP zeroP (tofs ?? P1)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H7.
inversion_clear H5.
inversion_clear H7.
inversion_clear H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).

apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
auto.

inversion_clear HFS.
unfold OutAtom, InAtom in |- *.
generalize (client_interface_after_mail _ _ HP); intro X; inversion_clear X.
inversion_clear H6.
inversion_clear H7.
rewrite H6.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *; SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *; SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


inversion_clear H6.
rewrite H7.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intro.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *; SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_ok_mail_from >>
                         (rcptc
                          << update_rev_path
                               (update_from
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p fwd_p tofs false) from)
                               p >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H8.
inversion_clear H6.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *; SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_ok_mail_from >>
                         (rcptc
                          << update_rev_path
                               (update_from
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p fwd_p tofs false) from)
                               p >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H8.
inversion_clear H6.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* cmd_quit *)

intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.

ConfRedComAlways.

unfold get_mail_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
unfold reply_ok_quit in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

generalize (H0 rep_ok_quit); intro X; inversion_clear X.
inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (parP (mailc ??* get_mail_def mailc rcptc) succ)
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP zeroP (c' ?? P0)) (tofs ?? P1))) may_fail).

unfold may_fail in |- *.
apply red_new_deter.
unfold succ in |- *.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

unfold succ, OutAtom, InAtom in |- *.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


ProcCong.

(* cas de l'erreur reseau *)

inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (parP (mailc ??* get_mail_def mailc rcptc) succ)
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P0)) (tofs ?? P1))) may_fail).

unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
unfold succ, InAtom, OutAtom in H4.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

(* cas de l'erreur reseau *)

inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_ok_quit >> succ))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P)) (tofs ?? P0))) may_fail).

unfold may_fail, succ, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


ProcCong.

(* cmd_abort *)

intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.

ConfRedComAlways.

unfold get_mail_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
unfold reply_ok_quit in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

generalize (H0 rep_ok_quit); intro X; inversion_clear X.

inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (parP (mailc ??* get_mail_def mailc rcptc) succ)
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP zeroP (c' ?? P0)) (tofs ?? P1))) may_fail).

unfold may_fail, succ, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

(* cas de l'erreur reseau *)

inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (parP (mailc ??* get_mail_def mailc rcptc) succ)
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P0)) (tofs ?? P1))) may_fail).

unfold may_fail, succ, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


ProcCong.

(* io error *)

inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_ok_quit >> succ))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P)) (tofs ?? P0))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

(* skip case *)

intros P c0 c0_not_mail c0_not_qui c0_not_abort HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.

ConfRedComAlways.

unfold get_mail_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

induction c0.

(* cmd_helo *)

unfold get_arg in |- *.

unfold reply_dup_helo in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p fwd_p tofs false) from)))))
       (parP (parP P (P0 rep_dup_helo)) (parP FS may_fail))).

apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.

ProcCong.

(* cas de l'erreur reseau *)

generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
rewrite H2.
inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_dup_helo >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0)) (tofs ?? P1)))
       may_fail).

unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intros X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intros X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


ProcCong.

inversion_clear H2.
rewrite H3.
inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_dup_helo >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (tofs ?? P1))) may_fail).

unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (c' << rep_dup_helo >>
                      (mailc
                       << update_from
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) from >> zeroP)))
                  (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
            (parP zeroP (tofs ?? P1)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intros X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.

apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_dup_helo >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_dup_helo >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* cmd_mail case *)

unfold get_arg in |- *.
unfold do_mail_from in |- *.
generalize (ax_parse s); intro.
inversion_clear H1.
cut
 ((exists p : Rfc821_path, string_to_Rfc821path s = Some p) \/
  string_to_Rfc821path s = None).
intro X; inversion_clear X.
inversion_clear H1.
assert (valid_cmd_mail (cmd_mail_from s)).
eapply valid_cmd_m.
apply H4.
absurd (valid_cmd_mail (cmd_mail_from s)).
auto.
auto.
rewrite (H3 H1).
unfold reply_bad_mail_from in |- *.
unfold reply in |- *.

simpl in |- *.
inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p fwd_p tofs false) from)))))
       (parP (parP P (P0 (rep_bad_mail_from s))) (parP FS may_fail))).

apply H0.
CheckSearchInc.
auto.
apply H4.
auto.
auto.

ProcCong.

(* cas de l'erreur reseau *)

inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_bad_mail_from s >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (tofs ?? P1))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.

apply red_new_deter.
generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H6.
inversion_clear H7.
rewrite H6.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
inversion_clear H6.
rewrite H7.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (c' << rep_bad_mail_from s >>
                      (mailc
                       << update_from
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) from >> zeroP)))
                  (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
            (parP zeroP (tofs ?? P1)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H8.
inversion_clear H6.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H7.
inversion_clear H8.
rewrite H7.
apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intro.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H6; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H6; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

inversion_clear H7.
rewrite H8.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intro.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_bad_mail_from s >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H7.
inversion_clear H9.
inversion_clear H7.
inversion_clear H9.
inversion_clear H9.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.

CheckNotInChanList2 H6.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_bad_mail_from s >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H7.
inversion_clear H9.
inversion_clear H7.
inversion_clear H9.
inversion_clear H9.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.

CheckNotInChanList2 H6.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

case (string_to_Rfc821path s).
intro.
left; exists r; auto.
auto.

(* cmd_rcpt_to *)

unfold get_arg in |- *.

unfold reply_no_mail_from in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p fwd_p tofs false) from)))))
       (parP (parP P (P0 rep_no_mail_from)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* cas de l'erreur *)

inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_no_mail_from >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (tofs ?? P1))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
inversion_clear H3.
rewrite H4.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (c' << rep_no_mail_from >>
                      (mailc
                       << update_from
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) from >> zeroP)))
                  (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
            (parP zeroP (tofs ?? P1)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H4.
inversion_clear H5.
rewrite H4.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

inversion_clear H4.
rewrite H5.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_no_mail_from >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H6.
inversion_clear H4.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.

CheckNotInChanList2 H3.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_no_mail_from >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H6.
inversion_clear H4.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.

CheckNotInChanList2 H3.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* cmd data case *)

unfold get_arg in |- *.

unfold reply_no_mail_from in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p fwd_p tofs false) from)))))
       (parP (parP P (P0 rep_no_mail_from)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* erreur reseau *)

generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
rewrite H2.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_no_mail_from >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0)) (tofs ?? P1)))
       may_fail).

unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.	   

(* cas ou une erreur reseau apparait dans l'interface du client *)

inversion_clear H2.
rewrite H3.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_no_mail_from >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (tofs ?? P1))) may_fail).

unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (c' << rep_no_mail_from >>
                      (mailc
                       << update_from
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) from >> zeroP)))
                  (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
            (parP zeroP (tofs ?? P1)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_no_mail_from >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_no_mail_from >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* case cmd_noop *)

unfold get_arg in |- *.

unfold reply_ok_noop in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p fwd_p tofs false) from)))))
       (parP (parP P (P0 rep_ok_noop)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* cas de l'erreur reseau *)

generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
rewrite H2.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_ok_noop >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0)) (tofs ?? P1)))
       may_fail).

unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

inversion_clear H2.
rewrite H3.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_ok_noop >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (c' << rep_ok_noop >>
                      (mailc
                       << update_from
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) from >> zeroP)))
                  (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_ok_noop >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_ok_noop >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* case cmd_rset *)

unfold get_arg in |- *.
unfold reply_ok_rset in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p fwd_p tofs false) from)))))
       (parP (parP P (P0 rep_ok_rset)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* network failure *)

generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
rewrite H2.
inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_ok_rset >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

inversion_clear H2.
rewrite H3.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_ok_rset >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (tofs ?? P1))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (c' << rep_ok_rset >>
                      (mailc
                       << update_from
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) from >> zeroP)))
                  (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
            (parP zeroP (tofs ?? P1)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_ok_rset >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_ok_rset >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* case cmd_quit *)

assert (cmd_quit = cmd_quit).
auto.
absurd (cmd_quit = cmd_quit).
auto.
auto.

(* case cmd_abort *)

assert (cmd_abort = cmd_abort).
auto.
absurd (cmd_abort = cmd_abort).
auto.
auto.

(* case cmd_unknown *)

unfold get_arg in |- *.

unfold reply_unknown_cmd in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p fwd_p tofs false) from)))))
       (parP (parP P (P0 rep_unknown_cmd)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* network failure *)

generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
rewrite H2.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_unknown_cmd >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0)) (tofs ?? P1)))
       may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

inversion_clear H2.
rewrite H3.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c' << rep_unknown_cmd >>
                    OutAtom mailc
                      (update_from
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) from)))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (tofs ?? P1))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (c' << rep_unknown_cmd >>
                      (mailc
                       << update_from
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) from >> zeroP)))
                  (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
            (parP zeroP (tofs ?? P1)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].
    
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_unknown_cmd >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c' << rep_unknown_cmd >>
                         (mailc
                          << update_from
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) from >> zeroP)))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.

CheckNotInChanList2 H4.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* case where the client emits a IO error *)

intros P0 HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.

ConfRedComAlways.

unfold get_mail_def at 2 in |- *.
simpl in |- *; unfold get_cmd in |- *.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP
                (parP (mailc ??* get_mail_def mailc rcptc)
                   (c
                    ?? (fun c0 : SMTP_cmd =>
                        get_arg c
                          (fun _ : unit =>
                           match c0 with
                           | cmd_helo _ =>
                               reply_dup_helo c'
                                 (OutAtom mailc
                                    (update_from
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false) from))
                           | cmd_mail_from arg =>
                               do_mail_from arg
                                 (update_from
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from rev_p fwd_p tofs false) from)
                                 (fun (b : bool) (st : STATE) =>
                                  if b
                                  then OutAtom rcptc st
                                  else OutAtom mailc st)
                           | cmd_rcpt_to _ =>
                               reply_no_mail_from c'
                                 (OutAtom mailc
                                    (update_from
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false) from))
                           | cmd_data _ =>
                               reply_no_mail_from c'
                                 (OutAtom mailc
                                    (update_from
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false) from))
                           | cmd_noop =>
                               reply_ok_noop c'
                                 (OutAtom mailc
                                    (update_from
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false) from))
                           | cmd_rset =>
                               reply_ok_rset c'
                                 (OutAtom mailc
                                    (update_from
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false) from))
                           | cmd_quit => reply_ok_quit c' succ
                           | cmd_abort => reply_ok_quit c' succ
                           | cmd_unknown =>
                               reply_unknown_cmd c'
                                 (OutAtom mailc
                                    (update_from
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false) from))
                           end))))
                (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
          (parP (parP (IOexn_chan << tt >> P0) Client2) FS)) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
inversion_clear HFS.
inversion_clear HClient2.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> P0) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (c
                      ?? (fun c0 : SMTP_cmd =>
                          get_arg c
                            (fun _ : unit =>
                             match c0 with
                             | cmd_helo _ =>
                                 reply_dup_helo c'
                                   (mailc
                                    << update_from
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false) from >> zeroP)
                             | cmd_mail_from arg =>
                                 do_mail_from arg
                                   (update_from
                                      (smtp_state c c' server_name0
                                         queue_dir0 buf0 from rev_p fwd_p
                                         tofs false) from)
                                   (fun (b : bool) (st : STATE) =>
                                    if b
                                    then rcptc << st >> zeroP
                                    else mailc << st >> zeroP)
                             | cmd_rcpt_to _ =>
                                 reply_no_mail_from c'
                                   (mailc
                                    << update_from
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false) from >> zeroP)
                             | cmd_data _ =>
                                 reply_no_mail_from c'
                                   (mailc
                                    << update_from
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false) from >> zeroP)
                             | cmd_noop =>
                                 reply_ok_noop c'
                                   (mailc
                                    << update_from
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false) from >> zeroP)
                             | cmd_rset =>
                                 reply_ok_rset c'
                                   (mailc
                                    << update_from
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false) from >> zeroP)
                             | cmd_quit => reply_ok_quit c' succ
                             | cmd_abort => reply_ok_quit c' succ
                             | cmd_unknown =>
                                 reply_unknown_cmd c'
                                   (mailc
                                    << update_from
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false) from >> zeroP)
                             end))))
                  (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
            (parP zeroP (tofs ?? P)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> P0).
intro.
inversion_clear H3.
inversion_clear H4.
inversion_clear H3.
inversion_clear H4.
inversion_clear H4.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

inversion_clear HFS.
inversion_clear HClient2.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H1; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H1; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> P0) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c
                         ?? (fun c0 : SMTP_cmd =>
                             get_arg c
                               (fun _ : unit =>
                                match c0 with
                                | cmd_helo _ =>
                                    reply_dup_helo c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_mail_from arg =>
                                    do_mail_from arg
                                      (update_from
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false) from)
                                      (fun (b : bool) (st : STATE) =>
                                       if b
                                       then rcptc << st >> zeroP
                                       else mailc << st >> zeroP)
                                | cmd_rcpt_to _ =>
                                    reply_no_mail_from c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_data _ =>
                                    reply_no_mail_from c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_noop =>
                                    reply_ok_noop c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_rset =>
                                    reply_ok_rset c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_quit => reply_ok_quit c' succ
                                | cmd_abort => reply_ok_quit c' succ
                                | cmd_unknown =>
                                    reply_unknown_cmd c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                end))))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> P0).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H1; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H1.

CheckNotInChanList2 H1.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> P0) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP
                     (parP (mailc ??* get_mail_def mailc rcptc)
                        (c
                         ?? (fun c0 : SMTP_cmd =>
                             get_arg c
                               (fun _ : unit =>
                                match c0 with
                                | cmd_helo _ =>
                                    reply_dup_helo c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_mail_from arg =>
                                    do_mail_from arg
                                      (update_from
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false) from)
                                      (fun (b : bool) (st : STATE) =>
                                       if b
                                       then rcptc << st >> zeroP
                                       else mailc << st >> zeroP)
                                | cmd_rcpt_to _ =>
                                    reply_no_mail_from c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_data _ =>
                                    reply_no_mail_from c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_noop =>
                                    reply_ok_noop c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_rset =>
                                    reply_ok_rset c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                | cmd_quit => reply_ok_quit c' succ
                                | cmd_abort => reply_ok_quit c' succ
                                | cmd_unknown =>
                                    reply_unknown_cmd c'
                                      (mailc
                                       << update_from
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) from >>
                                       zeroP)
                                end))))
                     (parP (rcptc ??* get_rcpt_def mailc rcptc) zeroP)))
               (parP zeroP (tofs ?? P)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> P0).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H1; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H1.

CheckNotInChanList2 H1.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* third subgoal : if the behavior is ok beyond the rcpt message with
a non-nil list of forward paths, it is ok beyond the rcpt message with
any list of forward paths *)

intros P0 c0 Hc0 HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.

ConfRedComAlways.

unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
inversion_clear Hc0.
unfold do_rcpt_to in |- *.
generalize (proj1 (ax_parse arg) p H1); intro.
rewrite H3.
rewrite H2.
unfold reply_ok_rcpt_to in |- *.
unfold reply in |- *.
simpl in |- *.

inversion_clear HClient2.

ConfRedComAlways.

EvalRewrite
 (fwd_paths_add
    (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p fwd_p tofs false)
    p).

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p
                      (p :: fwd_p) tofs false)))))
       (parP (parP P0 (P rep_ok_rcpt_to)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
intro.
discriminate H5.
auto.
ProcCong.

(* cas de l'erreur reseau *)

generalize (client_interface_after_rcpt _ _ HP); intro X; inversion_clear X.
inversion_clear H5.
inversion_clear H6.
rewrite H5.

inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_rcpt_to >>
                       OutAtom rcptc
                         (fwd_paths_add
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) p))) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P)) (tofs ?? P1)))
       may_fail).

unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H7; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H7; CheckListSet.

apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

ProcCong.

(* erreur reseau *)

inversion_clear H5.
rewrite H6.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_rcpt_to >>
                       OutAtom rcptc
                         (fwd_paths_add
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) p))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P))
             (tofs ?? P1))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_ok_rcpt_to >>
                         (rcptc
                          << fwd_paths_add
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) p >> zeroP)))
                     zeroP))) (parP zeroP (tofs ?? P1)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H7.
inversion_clear H8.
inversion_clear H7.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.

auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.

CheckNotInChanList2 SET.

red in |- *; simpl in |- *; split; [ auto | ProcCong ].
    
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_rcpt_to >>
                            (rcptc
                             << fwd_paths_add
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p fwd_p tofs false) p >>
                             zeroP))) zeroP))) (parP zeroP (tofs ?? P1)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H8.
inversion_clear H9.
inversion_clear H8.
inversion_clear H9.
inversion_clear H9.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H7; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H7.


CheckNotInChanList2 H7.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_rcpt_to >>
                            (rcptc
                             << fwd_paths_add
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p fwd_p tofs false) p >>
                             zeroP))) zeroP))) (parP zeroP (tofs ?? P1)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H8.
inversion_clear H9.
inversion_clear H8.
inversion_clear H9.
inversion_clear H9.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H7; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H7.


CheckNotInChanList2 H7.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* case cmd_quit *)

intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.
ConfRedComAlways.

unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.
unfold get_arg in |- *.
unfold reply_ok_quit, reply, succ in |- *.

inversion_clear HClient2.

ConfRedComAlways.
generalize (H0 rep_ok_quit); intro X; inversion_clear X.
inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (c' ?? P0)) (tofs ?? P1))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.

generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* cas de l'erreur reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P0)) (parP FS zeroP)))
       may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
inversion_clear HFS.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* erreur reseau *)

inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_quit >> OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P))
             (parP (tofs ?? P0) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* cmd abort *)

intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.
ConfRedComAlways.

unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.
unfold get_arg in |- *.
unfold reply_ok_quit, reply, succ in |- *.

inversion_clear HClient2.

ConfRedComAlways.
generalize (H0 rep_ok_quit); intro X; inversion_clear X.
inversion_clear HFS.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (c' ?? P0)) (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* cas de l'erreur reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P0)) (parP FS zeroP)))
       may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
inversion_clear HFS.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* erreur reseau *)

inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_quit >> OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P))
             (parP (tofs ?? P0) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* cmd_rset *)

intros P HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.
ConfRedComAlways.

unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.
unfold get_arg in |- *.
unfold reply_ok_rset, reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p fwd_p tofs false) from)))))
       (parP (parP P (P0 rep_ok_rset)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
apply H1.
auto.
auto.
EvalRewrite
 (update_fwd_paths
    (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p fwd_p tofs false)
    nil).
EvalRewrite
 (update_from
    (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p fwd_p tofs false)
    from).
rewrite Hfwd_p.
ProcCong.

(* cas de l'erreur reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_rset >>
                       OutAtom mailc
                         (update_fwd_paths
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false) nil))) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (parP FS zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
inversion_clear HFS.
generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



(* erreur reseau *)

inversion_clear H3.
rewrite H4.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_ok_rset >>
                         (mailc
                          << update_fwd_paths
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false) nil >> zeroP)))
                     zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_rset >>
                            (mailc
                             << update_fwd_paths
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p fwd_p tofs false) nil >>
                             zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_rset >>
                            (mailc
                             << update_fwd_paths
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p fwd_p tofs false) nil >>
                             zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* skip case *)

intros P c0 c0_isnot_rcpt c0_isnot_quit c0_isnot_abort c0_isnot_rset HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.
ConfRedComAlways.
unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.
ConfRedComAlways.
unfold get_arg in |- *.

induction c0.

(* case cmd_helo *)

unfold reply_dup_helo, reply in |- *.
inversion_clear HClient2.
ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p
                      fwd_p tofs false)))))
       (parP (parP P (P0 rep_dup_helo)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* network failure *)

generalize (client_interface_after_mail _ _ HP); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
rewrite H2.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_dup_helo >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false))) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* erreur reseau *)

inversion_clear H2.
rewrite H3.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_dup_helo >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_dup_helo >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].
    
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_dup_helo >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.


CheckNotInChanList2 H4.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_dup_helo >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.


CheckNotInChanList2 H4.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* dup_mail_from *)

unfold reply_dup_mail_from, reply in |- *.

inversion_clear HClient2.
ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p
                      fwd_p tofs false)))))
       (parP (parP P (P0 rep_dup_mail_from)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* network failure *)

generalize (client_interface_after_mail _ _ HP); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
rewrite H2.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_dup_mail_from >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false))) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0)) (tofs ?? P1)))
       may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

inversion_clear H2.
rewrite H3.
inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_dup_mail_from >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_dup_mail_from >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].
    
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_dup_mail_from >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.


CheckNotInChanList2 H4.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_dup_mail_from >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.


CheckNotInChanList2 H4.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* do rcpt to *)

unfold do_rcpt_to in |- *.
cut
 ((exists p : Rfc821_path, string_to_Rfc821path s = Some p) \/
  string_to_Rfc821path s = None).
intro X; inversion_clear X.
inversion_clear H1.
cut (is_not_null_a_d_l x = false \/ is_not_null_a_d_l x = true).
intro X; inversion_clear X.
assert (valid_cmd_rcpt (cmd_rcpt_to s)).
eapply valid_cmd_r.
apply H2.
auto.
absurd (valid_cmd_rcpt (cmd_rcpt_to s)).
auto.
auto.
rewrite (proj1 (ax_parse s) _ H2).
rewrite H1.
unfold reply_bad_rcpt_to553 in |- *.
unfold reply in |- *.
inversion_clear HClient2.
simpl in |- *.
ConfRedComAlways.
apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p
                      fwd_p tofs false)))))
       (parP (parP P (P0 rep_bad_rcpt_to553)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* cas de l'erreur netowrk *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (to_client
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) << rep_bad_rcpt_to553 >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false))) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (parP FS zeroP))) may_fail).
generalize (client_interface_after_mail _ _ HP); intro X; inversion_clear X.
inversion_clear H4.
inversion_clear H5.
rewrite H4.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



inversion_clear H4.
rewrite H5.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (to_client
                           (smtp_state c c' server_name0 queue_dir0 buf0 from
                              rev_p fwd_p tofs false)
                         << rep_bad_rcpt_to553 >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x0).
intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].
    
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_bad_rcpt_to553 >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x0).
intro.
inversion_clear H7.
inversion_clear H8.
inversion_clear H7.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.


CheckNotInChanList2 H6.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_bad_rcpt_to553 >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x0).
intro.
inversion_clear H7.
inversion_clear H8.
inversion_clear H7.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.


CheckNotInChanList2 H6.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

case (is_not_null_a_d_l x).
auto.
auto.
rewrite (proj2 (ax_parse s) H1).
unfold reply_bad_rcpt_to501, reply in |- *.
inversion_clear HClient2.
simpl in |- *.
ConfRedComAlways.
apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p
                      fwd_p tofs false)))))
       (parP (parP P (P0 rep_bad_rcpt_to501)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.

ProcCong.

(* network failure *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (to_client
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false) << rep_bad_rcpt_to501 >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false))) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (parP FS zeroP))) may_fail).
generalize (client_interface_after_mail _ _ HP); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H5; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H5; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

inversion_clear H3.
rewrite H4.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (to_client
                           (smtp_state c c' server_name0 queue_dir0 buf0 from
                              rev_p fwd_p tofs false)
                         << rep_bad_rcpt_to501 >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].
    
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_bad_rcpt_to501 >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H5; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H5.


CheckNotInChanList2 H5.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_bad_rcpt_to501 >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H5; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H5.


CheckNotInChanList2 H5.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

case (string_to_Rfc821path s).
intro r; left; exists r; auto.
auto.

assert (fwd_paths_size_gt_0 fwd_p = false).
rewrite Hfwd_p; auto.
rewrite H1.
unfold reply_no_rcpt_to in |- *.
unfold reply in |- *.
inversion_clear HClient2.
ConfRedComAlways.
apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p
                      fwd_p tofs false)))))
       (parP (parP P (P0 rep_no_rcpt_to)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.

ProcCong.

(* network failure *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_no_rcpt_to >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false))) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (parP FS zeroP))) may_fail).
generalize (client_interface_after_mail _ _ HP); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H5; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H5; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



inversion_clear H3.
rewrite H4.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_no_rcpt_to >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.



CheckNotInChanList2 SET.



red in |- *; simpl in |- *; split; [ auto | ProcCong ].
    
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_no_rcpt_to >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H5; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H5.


CheckNotInChanList2 H5.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_no_rcpt_to >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H5; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H5.


CheckNotInChanList2 H5.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* case noop *)

unfold reply_ok_noop in |- *.
unfold reply in |- *.
inversion_clear HClient2.
ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p
                      fwd_p tofs false)))))
       (parP (parP P (P0 rep_ok_noop)) (parP FS may_fail))).
apply H0.
auto.
auto.
auto.
auto.
auto.
ProcCong.

(* network error *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_noop >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false))) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (parP FS zeroP))) may_fail).
generalize (client_interface_after_mail _ _ HP); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
rewrite H2.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



inversion_clear H2.
rewrite H3.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_ok_noop >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].
    
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_noop >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.


CheckNotInChanList2 H4.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_noop >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.


CheckNotInChanList2 H4.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* cmd_rset *)

assert (cmd_rset = cmd_rset).
auto.
absurd (cmd_rset = cmd_rset).
auto.
auto.

(* cmd_quit *)

assert (cmd_quit = cmd_quit).
auto.
absurd (cmd_quit = cmd_quit).
auto.
auto.

(* cmd_abort *)

assert (cmd_abort = cmd_abort).
auto.
absurd (cmd_abort = cmd_abort).
auto.
auto.

(* cmd unknown *)

unfold reply_unknown_cmd in |- *.
unfold reply in |- *.
inversion_clear HClient2.
ConfRedComAlways.
apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p
                      fwd_p tofs false)))))
       (parP (parP P (P0 rep_unknown_cmd)) (parP FS may_fail))).
apply H0.
auto.
auto.
auto.
auto.
auto.
ProcCong.

(* network error *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_unknown_cmd >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p fwd_p tofs false))) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (parP FS zeroP))) may_fail).
generalize (client_interface_after_mail _ _ HP); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
rewrite H2.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms; simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



inversion_clear H2.
rewrite H3.
inversion_clear HFS.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_unknown_cmd >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p fwd_p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].
    
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_unknown_cmd >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.


CheckNotInChanList2 H4.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_unknown_cmd >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p fwd_p tofs false >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H4.


CheckNotInChanList2 H4.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* case where the client emits an IO error *)

intros P0 HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.

ConfRedComAlways.

unfold get_rcpt_def at 2 in |- *.
simpl in |- *; unfold get_cmd in |- *.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c
                       ?? (fun c0 : SMTP_cmd =>
                           get_arg c
                             (fun _ : unit =>
                              match c0 with
                              | cmd_helo _ =>
                                  reply_dup_helo c'
                                    (OutAtom rcptc
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false))
                              | cmd_mail_from _ =>
                                  reply_dup_mail_from c'
                                    (OutAtom rcptc
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false))
                              | cmd_rcpt_to arg =>
                                  do_rcpt_to arg
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from rev_p fwd_p tofs false)
                                    (fun st : STATE => OutAtom rcptc st)
                              | cmd_data data =>
                                  if fwd_paths_size_gt_0 fwd_p
                                  then
                                   save_mail data
                                     (smtp_state c c' server_name0 queue_dir0
                                        buf0 from rev_p fwd_p tofs false)
                                     (reply_ok_data c'
                                        (OutAtom mailc
                                           (update_fwd_paths
                                              (smtp_state c c' server_name0
                                                 queue_dir0 buf0 from rev_p
                                                 fwd_p tofs false) nil)))
                                  else
                                   reply_no_rcpt_to c'
                                     (OutAtom rcptc
                                        (smtp_state c c' server_name0
                                           queue_dir0 buf0 from rev_p fwd_p
                                           tofs false))
                              | cmd_noop =>
                                  reply_ok_noop c'
                                    (OutAtom rcptc
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false))
                              | cmd_rset =>
                                  reply_ok_rset c'
                                    (OutAtom mailc
                                       (update_fwd_paths
                                          (smtp_state c c' server_name0
                                             queue_dir0 buf0 from rev_p fwd_p
                                             tofs false) nil))
                              | cmd_quit => reply_ok_quit c' succ
                              | cmd_abort => reply_ok_quit c' succ
                              | cmd_unknown =>
                                  reply_unknown_cmd c'
                                    (OutAtom rcptc
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false))
                              end)))) zeroP)))
          (parP (parP (IOexn_chan << tt >> P0) Client2) (parP FS zeroP)))
       may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
inversion_clear HFS.
inversion_clear HClient2.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> P0) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c
                         ?? (fun c0 : SMTP_cmd =>
                             get_arg c
                               (fun _ : unit =>
                                match c0 with
                                | cmd_helo _ =>
                                    reply_dup_helo c'
                                      (rcptc
                                       << smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false >> zeroP)
                                | cmd_mail_from _ =>
                                    reply_dup_mail_from c'
                                      (rcptc
                                       << smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false >> zeroP)
                                | cmd_rcpt_to arg =>
                                    do_rcpt_to arg
                                      (smtp_state c c' server_name0
                                         queue_dir0 buf0 from rev_p fwd_p
                                         tofs false)
                                      (fun st : STATE => rcptc << st >> zeroP)
                                | cmd_data data =>
                                    if fwd_paths_size_gt_0 fwd_p
                                    then
                                     save_mail data
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false)
                                       (reply_ok_data c'
                                          (mailc
                                           << update_fwd_paths
                                                (smtp_state c c' server_name0
                                                  queue_dir0 buf0 from rev_p
                                                  fwd_p tofs false) nil >>
                                           zeroP))
                                    else
                                     reply_no_rcpt_to c'
                                       (rcptc
                                        << smtp_state c c' server_name0
                                             queue_dir0 buf0 from rev_p fwd_p
                                             tofs false >> zeroP)
                                | cmd_noop =>
                                    reply_ok_noop c'
                                      (rcptc
                                       << smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false >> zeroP)
                                | cmd_rset =>
                                    reply_ok_rset c'
                                      (mailc
                                       << update_fwd_paths
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) nil >> zeroP)
                                | cmd_quit => reply_ok_quit c' succ
                                | cmd_abort => reply_ok_quit c' succ
                                | cmd_unknown =>
                                    reply_unknown_cmd c'
                                      (rcptc
                                       << smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false >> zeroP)
                                end)))) zeroP)))
            (parP zeroP (parP (tofs ?? P) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> P0).
intro.
inversion_clear H3.
inversion_clear H4.
inversion_clear H3.
inversion_clear H4.
inversion_clear H4.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

inversion_clear HFS.
inversion_clear HClient2.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H1; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H1; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> P0) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c
                            ?? (fun c0 : SMTP_cmd =>
                                get_arg c
                                  (fun _ : unit =>
                                   match c0 with
                                   | cmd_helo _ =>
                                       reply_dup_helo c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_mail_from _ =>
                                       reply_dup_mail_from c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_rcpt_to arg =>
                                       do_rcpt_to arg
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false)
                                         (fun st : STATE =>
                                          rcptc << st >> zeroP)
                                   | cmd_data data =>
                                       if fwd_paths_size_gt_0 fwd_p
                                       then
                                        save_mail data
                                          (smtp_state c c' server_name0
                                             queue_dir0 buf0 from rev_p fwd_p
                                             tofs false)
                                          (reply_ok_data c'
                                             (mailc
                                              << update_fwd_paths
                                                  (smtp_state c c'
                                                  server_name0 queue_dir0
                                                  buf0 from rev_p fwd_p tofs
                                                  false) nil >> zeroP))
                                       else
                                        reply_no_rcpt_to c'
                                          (rcptc
                                           << smtp_state c c' server_name0
                                                queue_dir0 buf0 from rev_p
                                                fwd_p tofs false >> zeroP)
                                   | cmd_noop =>
                                       reply_ok_noop c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_rset =>
                                       reply_ok_rset c'
                                         (mailc
                                          << update_fwd_paths
                                               (smtp_state c c' server_name0
                                                  queue_dir0 buf0 from rev_p
                                                  fwd_p tofs false) nil >>
                                          zeroP)
                                   | cmd_quit => reply_ok_quit c' succ
                                   | cmd_abort => reply_ok_quit c' succ
                                   | cmd_unknown =>
                                       reply_unknown_cmd c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   end)))) zeroP)))
               (parP zeroP (parP (tofs ?? P) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> P0).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H1; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H1.


CheckNotInChanList2 H1.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> P0) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c
                            ?? (fun c0 : SMTP_cmd =>
                                get_arg c
                                  (fun _ : unit =>
                                   match c0 with
                                   | cmd_helo _ =>
                                       reply_dup_helo c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_mail_from _ =>
                                       reply_dup_mail_from c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_rcpt_to arg =>
                                       do_rcpt_to arg
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false)
                                         (fun st : STATE =>
                                          rcptc << st >> zeroP)
                                   | cmd_data data =>
                                       if fwd_paths_size_gt_0 fwd_p
                                       then
                                        save_mail data
                                          (smtp_state c c' server_name0
                                             queue_dir0 buf0 from rev_p fwd_p
                                             tofs false)
                                          (reply_ok_data c'
                                             (mailc
                                              << update_fwd_paths
                                                  (smtp_state c c'
                                                  server_name0 queue_dir0
                                                  buf0 from rev_p fwd_p tofs
                                                  false) nil >> zeroP))
                                       else
                                        reply_no_rcpt_to c'
                                          (rcptc
                                           << smtp_state c c' server_name0
                                                queue_dir0 buf0 from rev_p
                                                fwd_p tofs false >> zeroP)
                                   | cmd_noop =>
                                       reply_ok_noop c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_rset =>
                                       reply_ok_rset c'
                                         (mailc
                                          << update_fwd_paths
                                               (smtp_state c c' server_name0
                                                  queue_dir0 buf0 from rev_p
                                                  fwd_p tofs false) nil >>
                                          zeroP)
                                   | cmd_quit => reply_ok_quit c' succ
                                   | cmd_abort => reply_ok_quit c' succ
                                   | cmd_unknown =>
                                       reply_unknown_cmd c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   end)))) zeroP)))
               (parP zeroP (parP (tofs ?? P) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> P0).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H1; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H1.


CheckNotInChanList2 H1.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   

(* fourth subgoal : if the behavior is ok beyond the mail message,
then it is ok beyond the rcpt message with a non-empty list of 
forward paths *)

intros data P HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p p Hp FS HFS.

ConfRedComAlways.

unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
assert (fwd_paths_size_gt_0 p = true).
assert (exists p' : _, (exists p'' : _, p = p' :: p'')).
induction p.
generalize (Hp (refl_equal nil)); contradiction.
exists a; exists p; auto.
inversion_clear H1.
inversion_clear H2.
rewrite H1.
simpl in |- *.
auto.
rewrite H1.

unfold save_mail in |- *.
simpl in |- *.

inversion_clear HFS.

ConfRedComAlways.

unfold reply_ok_data in |- *.
unfold reply in |- *.

inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p nil tofs false) from)))))
       (parP (parP P (P1 rep_ok_data))
          (parP (P0 (mail from rev_p p data)) may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
EvalRewrite
 (update_from
    (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p nil tofs false)
    from).
EvalRewrite
 (update_fwd_paths
    (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p p tofs false)
    nil).
ProcCong.

(* cas de l'erreur reseau du client *)

generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H4.
inversion_clear H5.
rewrite H4.
generalize (H2 (mail from rev_p p data)); intro X; inversion_clear X.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_data >>
                       OutAtom mailc
                         (update_fwd_paths
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false) nil))) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P1))
             (parP (tofs ?? P2) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
generalize SET; CheckListSet.


apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* the client is to do an IO error next *)

inversion_clear H4.
rewrite H5.
generalize (H2 (mail from rev_p p data)); intro X; inversion_clear X.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_data >>
                       OutAtom mailc
                         (update_fwd_paths
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false) nil))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P1))
             (parP (tofs ?? P2) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_ok_data >>
                         (mailc
                          << update_fwd_paths
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false) nil >> zeroP)))
                     zeroP))) (parP zeroP (parP (tofs ?? P2) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H7.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_data >>
                            (mailc
                             << update_fwd_paths
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p p tofs false) nil >>
                             zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P2) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H7.
inversion_clear H8.
inversion_clear H7.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.


CheckNotInChanList2 H6.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_data >>
                            (mailc
                             << update_fwd_paths
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p p tofs false) nil >>
                             zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P2) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H7.
inversion_clear H8.
inversion_clear H7.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.


CheckNotInChanList2 H6.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* cmd_abort *)

intros L INC SET' Client2 HClient2 from rev_p p Hp FS HFS.
ConfRedComAlways.
unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *; simpl in |- *.
ConfRedComAlways.
unfold get_arg, succ in |- *.
unfold reply_ok_quit, reply in |- *.
inversion_clear HClient2.
ConfRedComAlways.
inversion_clear HFS.
generalize (H0 rep_ok_quit); intro X; inversion_clear X.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (c' ?? P1)) (parP (tofs ?? P0) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* cas de l'erreur reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P1))
             (parP (tofs ?? P0) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* le client fait une erreur reseau *)

inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_quit >> OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P))
             (parP (tofs ?? P0) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* cmd_quit case *)

intros L INC SET' Client2 HClient2 from rev_p p Hp FS HFS.
ConfRedComAlways.
unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *; simpl in |- *.
ConfRedComAlways.
unfold get_arg, succ in |- *.
unfold reply_ok_quit, reply in |- *.
inversion_clear HClient2.
ConfRedComAlways.
inversion_clear HFS.
generalize (H0 rep_ok_quit); intro X; inversion_clear X.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (c' ?? P1)) (parP (tofs ?? P0) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* cas de l'erreur reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P1))
             (parP (tofs ?? P0) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
unfold reports_succ_or_error in |- *.
apply STAT_sat.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* le client fait une erreur reseau *)

inversion_clear HFS.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_quit >> OutAtom result_chan tt)) zeroP)))
          (parP (parP zeroP (IOexn_chan << tt >> P))
             (parP (tofs ?? P0) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H2; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


ProcCong.

(* cmd_rset *)

intros P HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p p Hp FS HFS.
ConfRedComAlways.
unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *; simpl in |- *.
ConfRedComAlways.
unfold get_arg, reply_ok_rset, reply in |- *.
inversion_clear HClient2.
ConfRedComAlways.
apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom mailc
                   (update_from
                      (smtp_state c c' server_name0 queue_dir0 buf0 from
                         rev_p nil tofs false) from)))))
       (parP (parP P (P0 rep_ok_rset)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
EvalRewrite
 (update_fwd_paths
    (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p p tofs false)
    nil).
EvalRewrite
 (update_from
    (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p nil tofs false)
    from).
ProcCong.

(* cas de l'erreur reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_rset >>
                       OutAtom mailc
                         (update_fwd_paths
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false) nil))) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (parP FS zeroP))) may_fail).
inversion_clear HFS.
generalize (client_interface_after_helo _ _ HP); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



(* le client fait une erreur reseau *)

inversion_clear H3.
rewrite H4.
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_ok_rset >>
                         (mailc
                          << update_fwd_paths
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false) nil >> zeroP)))
                     zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_rset >>
                            (mailc
                             << update_fwd_paths
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p p tofs false) nil >>
                             zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_rset >>
                            (mailc
                             << update_fwd_paths
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p p tofs false) nil >>
                             zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* skip case *)

intros P c0 c0_isnot_quit c0_isnot_abort c0_isnot_data c0_isnot_rset HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p p Hp FS HFS.

ConfRedComAlways.

unfold get_rcpt_def at 2 in |- *.
unfold get_cmd in |- *.
simpl in |- *.

ConfRedComAlways.

unfold get_arg in |- *.
induction c0.
unfold reply_dup_helo, reply in |- *.
inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p p
                      tofs false)))))
       (parP (parP P (P0 rep_dup_helo)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* cas de l'erreur reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_dup_helo >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP P (IOexn_chan << tt >> P0)) (parP FS zeroP))) may_fail).
inversion_clear HFS.
generalize (client_interface_after_rcpt _ _ HP); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.
unfold may_fail, InAtom, OutAtom in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



(* erreur reseau *)

inversion_clear H3.
rewrite H4.
unfold may_fail, InAtom, OutAtom in |- *.

apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_dup_helo >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_dup_helo >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_dup_helo >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* case dup mail from *)

unfold reply_dup_mail_from in |- *.
unfold reply in |- *.
inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p p
                      tofs false)))))
       (parP (parP P (P0 rep_dup_mail_from)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* cas de l'erreur reseau *)

inversion_clear HFS.
generalize (client_interface_after_rcpt _ _ HP); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_dup_mail_from >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.
apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

inversion_clear H3.
rewrite H4.

(* erreur reseau *)

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_dup_mail_from >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_dup_mail_from >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.
apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_dup_mail_from >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_dup_mail_from >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.
CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* cas de la command rcpt *)

unfold do_rcpt_to in |- *.
generalize (ax_parse s); intro.
inversion_clear H1.
cut
 ((exists p : _, string_to_Rfc821path s = Some p) \/
  string_to_Rfc821path s = None).
intro X; inversion_clear X.
inversion_clear H1.
rewrite (H2 _ H4).
cut (is_not_null_a_d_l x = true \/ is_not_null_a_d_l x = false).
intro X; inversion_clear X.
rewrite H1.
unfold reply_bad_rcpt_to553 in |- *.
unfold reply in |- *.

simpl in |- *.
inversion_clear HClient2.
ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p p
                      tofs false)))))
       (parP (parP P (P0 rep_bad_rcpt_to553)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* cas ou le client renvoie une erreur reseau *)

inversion_clear HFS.
generalize (client_interface_after_rcpt _ _ HP); intro X; inversion_clear X.
inversion_clear H7.
inversion_clear H8.
rewrite H7.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_bad_rcpt_to553 >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (c << x1 >> x0) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H8; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H8; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(*erreur reseau *)

inversion_clear H7.
rewrite H8.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_bad_rcpt_to553 >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_bad_rcpt_to553 >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x0).
intro.
inversion_clear H7.
inversion_clear H9.
inversion_clear H7.
inversion_clear H9.
inversion_clear H9.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_bad_rcpt_to553 >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x0).
intro.
inversion_clear H9.
inversion_clear H10.
inversion_clear H9.
inversion_clear H10.
inversion_clear H10.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H7; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H7.


CheckNotInChanList2 H7.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_bad_rcpt_to553 >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x0).
intro.
inversion_clear H9.
inversion_clear H10.
inversion_clear H9.
inversion_clear H10.
inversion_clear H10.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H7; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H7.


CheckNotInChanList2 H7.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* good rcpt command *)

rewrite H1.
simpl in |- *.
unfold reply_ok_rcpt_to in |- *.
unfold reply in |- *.

inversion_clear HClient2.	   
ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p
                      (x :: p) tofs false)))))
       (parP (parP P (P0 rep_ok_rcpt_to)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
intro X; discriminate X.
auto.

EvalRewrite
 (fwd_paths_add
    (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p p tofs false) x).
ProcCong.

(* cas de l'error reseau *)

inversion_clear HFS.
generalize (client_interface_after_rcpt _ _ HP); intro X; inversion_clear X.
inversion_clear H7.
inversion_clear H8.
rewrite H7.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_rcpt_to >>
                       OutAtom rcptc
                         (fwd_paths_add
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false) x))) zeroP)))
          (parP (parP (c << x1 >> x0) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H8; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H8; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* erreur reseau *)

inversion_clear H7.
rewrite H8.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_rcpt_to >>
                       OutAtom rcptc
                         (fwd_paths_add
                            (smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false) x))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_ok_rcpt_to >>
                         (rcptc
                          << fwd_paths_add
                               (smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false) x >> zeroP)))
                     zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x0).
intro.
inversion_clear H7.
inversion_clear H9.
inversion_clear H7.
inversion_clear H9.
inversion_clear H9.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_rcpt_to >>
                            (rcptc
                             << fwd_paths_add
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p p tofs false) x >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x0).
intro.
inversion_clear H9.
inversion_clear H10.
inversion_clear H9.
inversion_clear H10.
inversion_clear H10.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H7; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H7.


CheckNotInChanList2 H7.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x0) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_rcpt_to >>
                            (rcptc
                             << fwd_paths_add
                                  (smtp_state c c' server_name0 queue_dir0
                                     buf0 from rev_p p tofs false) x >> zeroP)))
                        zeroP))) (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x0).
intro.
inversion_clear H9.
inversion_clear H10.
inversion_clear H9.
inversion_clear H10.
inversion_clear H10.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H7; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H7.


CheckNotInChanList2 H7.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

case (is_not_null_a_d_l x).
auto.
auto.
rewrite (H3 H1).
unfold reply_bad_rcpt_to501 in |- *.
unfold reply in |- *.
simpl in |- *.
inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p p
                      tofs false)))))
       (parP (parP P (P0 rep_bad_rcpt_to501)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* cas de l'erreur reseau *)

inversion_clear HFS.
generalize (client_interface_after_rcpt _ _ HP); intro X; inversion_clear X.
inversion_clear H6.
inversion_clear H7.
rewrite H6.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_bad_rcpt_to501 >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H7; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H7; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* erreur reseau *)

inversion_clear H6.
rewrite H7.

apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_bad_rcpt_to501 >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_bad_rcpt_to501 >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H6.
inversion_clear H8.
inversion_clear H6.
inversion_clear H8.
inversion_clear H8.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_bad_rcpt_to501 >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H8.
inversion_clear H9.
inversion_clear H8.
inversion_clear H9.
inversion_clear H9.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.


CheckNotInChanList2 H6.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_bad_rcpt_to501 >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H8.
inversion_clear H9.
inversion_clear H8.
inversion_clear H9.
inversion_clear H9.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H6; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H6.


CheckNotInChanList2 H6.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

case (string_to_Rfc821path s).
intro r; left; exists r.
auto.
auto.

(* command data *)

generalize (c0_isnot_data s (refl_equal (cmd_data s))); contradiction.

(* command noop *)

unfold reply_ok_noop in |- *.
unfold reply in |- *.
inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p p
                      tofs false)))))
       (parP (parP P (P0 rep_ok_noop)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* cas de l'erreur reseau *)

inversion_clear HFS.
generalize (client_interface_after_rcpt _ _ HP); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_noop >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* erreur reseau *)

inversion_clear H3.
rewrite H4.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_ok_noop >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_ok_noop >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_noop >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_ok_noop >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* command rset: absurd *)

generalize (c0_isnot_rset (refl_equal cmd_rset)); contradiction.

(* command quit: absurd *)

generalize (c0_isnot_quit (refl_equal cmd_quit)); contradiction.

(* command abort: absurd *)

generalize (c0_isnot_abort (refl_equal cmd_abort)); contradiction.

(* command unknown *)

unfold reply_unknown_cmd in |- *.
unfold reply in |- *.
inversion_clear HClient2.

ConfRedComAlways.

apply
 cong_resp_tsat
  with
    (parP
       (parP (heloc ??* get_helo_def heloc mailc)
          (parP (mailc ??* get_mail_def mailc rcptc)
             (parP (rcptc ??* get_rcpt_def mailc rcptc)
                (OutAtom rcptc
                   (smtp_state c c' server_name0 queue_dir0 buf0 from rev_p p
                      tofs false)))))
       (parP (parP P (P0 rep_unknown_cmd)) (parP FS may_fail))).
apply H0.
CheckSearchInc.
auto.
auto.
auto.
auto.
ProcCong.

(* cas de l'erreur reseau *)

inversion_clear HFS.
generalize (client_interface_after_rcpt _ _ HP); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H4.
rewrite H3.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_unknown_cmd >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (c << x0 >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.

apply red_new_deter.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H4; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



ProcCong.

(* erreur reseau *)

inversion_clear H3.
rewrite H4.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c' << rep_unknown_cmd >>
                       OutAtom rcptc
                         (smtp_state c c' server_name0 queue_dir0 buf0 from
                            rev_p p tofs false))) zeroP)))
          (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0))
             (parP (tofs ?? P1) zeroP))) may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c' << rep_unknown_cmd >>
                         (rcptc
                          << smtp_state c c' server_name0 queue_dir0 buf0
                               from rev_p p tofs false >> zeroP))) zeroP)))
            (parP zeroP (parP (tofs ?? P1) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> x).
intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.
assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *; intro; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_unknown_cmd >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> x) (IOexn_chan << tt >> P0)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c' << rep_unknown_cmd >>
                            (rcptc
                             << smtp_state c c' server_name0 queue_dir0 buf0
                                  from rev_p p tofs false >> zeroP))) zeroP)))
               (parP zeroP (parP (tofs ?? P1) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> x).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H6.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H3; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H3.


CheckNotInChanList2 H3.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.

(* erreur reseau *)

intros P HP.
intro.
intros L INC SET' Client2 HClient2 from rev_p fwd_p Hfwd_p FS HFS.

ConfRedComAlways.

unfold get_rcpt_def at 2 in |- *.
simpl in |- *; unfold get_cmd in |- *.
apply
 cong_resp_tsat
  with
    (parP
       (parP
          (parP (heloc ??* get_helo_def heloc mailc)
             (parP (mailc ??* get_mail_def mailc rcptc)
                (parP
                   (parP (rcptc ??* get_rcpt_def mailc rcptc)
                      (c
                       ?? (fun c0 : SMTP_cmd =>
                           get_arg c
                             (fun _ : unit =>
                              match c0 with
                              | cmd_helo _ =>
                                  reply_dup_helo c'
                                    (OutAtom rcptc
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false))
                              | cmd_mail_from _ =>
                                  reply_dup_mail_from c'
                                    (OutAtom rcptc
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false))
                              | cmd_rcpt_to arg =>
                                  do_rcpt_to arg
                                    (smtp_state c c' server_name0 queue_dir0
                                       buf0 from rev_p fwd_p tofs false)
                                    (fun st : STATE => OutAtom rcptc st)
                              | cmd_data data =>
                                  if fwd_paths_size_gt_0 fwd_p
                                  then
                                   save_mail data
                                     (smtp_state c c' server_name0 queue_dir0
                                        buf0 from rev_p fwd_p tofs false)
                                     (reply_ok_data c'
                                        (OutAtom mailc
                                           (update_fwd_paths
                                              (smtp_state c c' server_name0
                                                 queue_dir0 buf0 from rev_p
                                                 fwd_p tofs false) nil)))
                                  else
                                   reply_no_rcpt_to c'
                                     (OutAtom rcptc
                                        (smtp_state c c' server_name0
                                           queue_dir0 buf0 from rev_p fwd_p
                                           tofs false))
                              | cmd_noop =>
                                  reply_ok_noop c'
                                    (OutAtom rcptc
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false))
                              | cmd_rset =>
                                  reply_ok_rset c'
                                    (OutAtom mailc
                                       (update_fwd_paths
                                          (smtp_state c c' server_name0
                                             queue_dir0 buf0 from rev_p fwd_p
                                             tofs false) nil))
                              | cmd_quit => reply_ok_quit c' succ
                              | cmd_abort => reply_ok_quit c' succ
                              | cmd_unknown =>
                                  reply_unknown_cmd c'
                                    (OutAtom rcptc
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false))
                              end)))) zeroP)))
          (parP (parP (IOexn_chan << tt >> P) Client2) (parP FS zeroP)))
       may_fail).
unfold may_fail, InAtom, OutAtom in |- *.
apply red_new_deter.
inversion_clear HFS.
inversion_clear HClient2.
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply
 cong_respects_stable
  with
    (L
     # parP
         (parP (parP (IOexn_chan << tt >> P) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP (heloc ??* get_helo_def heloc mailc)
               (parP (mailc ??* get_mail_def mailc rcptc)
                  (parP
                     (parP (rcptc ??* get_rcpt_def mailc rcptc)
                        (c
                         ?? (fun c0 : SMTP_cmd =>
                             get_arg c
                               (fun _ : unit =>
                                match c0 with
                                | cmd_helo _ =>
                                    reply_dup_helo c'
                                      (rcptc
                                       << smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false >> zeroP)
                                | cmd_mail_from _ =>
                                    reply_dup_mail_from c'
                                      (rcptc
                                       << smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false >> zeroP)
                                | cmd_rcpt_to arg =>
                                    do_rcpt_to arg
                                      (smtp_state c c' server_name0
                                         queue_dir0 buf0 from rev_p fwd_p
                                         tofs false)
                                      (fun st : STATE => rcptc << st >> zeroP)
                                | cmd_data data =>
                                    if fwd_paths_size_gt_0 fwd_p
                                    then
                                     save_mail data
                                       (smtp_state c c' server_name0
                                          queue_dir0 buf0 from rev_p fwd_p
                                          tofs false)
                                       (reply_ok_data c'
                                          (mailc
                                           << update_fwd_paths
                                                (smtp_state c c' server_name0
                                                  queue_dir0 buf0 from rev_p
                                                  fwd_p tofs false) nil >>
                                           zeroP))
                                    else
                                     reply_no_rcpt_to c'
                                       (rcptc
                                        << smtp_state c c' server_name0
                                             queue_dir0 buf0 from rev_p fwd_p
                                             tofs false >> zeroP)
                                | cmd_noop =>
                                    reply_ok_noop c'
                                      (rcptc
                                       << smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false >> zeroP)
                                | cmd_rset =>
                                    reply_ok_rset c'
                                      (mailc
                                       << update_fwd_paths
                                            (smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false) nil >> zeroP)
                                | cmd_quit => reply_ok_quit c' succ
                                | cmd_abort => reply_ok_quit c' succ
                                | cmd_unknown =>
                                    reply_unknown_cmd c'
                                      (rcptc
                                       << smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false >> zeroP)
                                end)))) zeroP)))
            (parP zeroP (parP (tofs ?? P0) zeroP)))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (L # IOexn_chan << tt >> P).
intro.
inversion_clear H3.
inversion_clear H4.
inversion_clear H3.
inversion_clear H4.
inversion_clear H4.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize SET; CheckListSet.


auto.
CheckSearchInc.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 SET.


CheckNotInChanList2 SET.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intros failc failcfresh.

assert
 (ChanList_is_set
    (failc &
     rcptc &
     mailc &
     heloc &
     tofs & c' & c & result_chan & IOexn_chan & system_failure_chan & nilC)).
apply chanlist_is_set_extend.
auto.
apply incC_fresh with L.
auto.
CheckSearchInc.

inversion_clear HFS.
inversion_clear HClient2.

apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H1; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.



intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
CheckStable.
generalize H1; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply red_com_nondeter.
CheckExistsGuard.
CheckUnstable.
intros; NextComms; simpl in |- *; intros; or_false.

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> P) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c
                            ?? (fun c0 : SMTP_cmd =>
                                get_arg c
                                  (fun _ : unit =>
                                   match c0 with
                                   | cmd_helo _ =>
                                       reply_dup_helo c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_mail_from _ =>
                                       reply_dup_mail_from c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_rcpt_to arg =>
                                       do_rcpt_to arg
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false)
                                         (fun st : STATE =>
                                          rcptc << st >> zeroP)
                                   | cmd_data data =>
                                       if fwd_paths_size_gt_0 fwd_p
                                       then
                                        save_mail data
                                          (smtp_state c c' server_name0
                                             queue_dir0 buf0 from rev_p fwd_p
                                             tofs false)
                                          (reply_ok_data c'
                                             (mailc
                                              << update_fwd_paths
                                                  (smtp_state c c'
                                                  server_name0 queue_dir0
                                                  buf0 from rev_p fwd_p tofs
                                                  false) nil >> zeroP))
                                       else
                                        reply_no_rcpt_to c'
                                          (rcptc
                                           << smtp_state c c' server_name0
                                                queue_dir0 buf0 from rev_p
                                                fwd_p tofs false >> zeroP)
                                   | cmd_noop =>
                                       reply_ok_noop c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_rset =>
                                       reply_ok_rset c'
                                         (mailc
                                          << update_fwd_paths
                                               (smtp_state c c' server_name0
                                                  queue_dir0 buf0 from rev_p
                                                  fwd_p tofs false) nil >>
                                          zeroP)
                                   | cmd_quit => reply_ok_quit c' succ
                                   | cmd_abort => reply_ok_quit c' succ
                                   | cmd_unknown =>
                                       reply_unknown_cmd c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   end)))) zeroP)))
               (parP zeroP (parP (tofs ?? P0) zeroP)))
            (parP (failc ?? (fun _ : unit => zeroP))
               (parP zeroP (system_failure_chan << tt >> zeroP))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> P).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H1; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.


apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H1.


CheckNotInChanList2 H1.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

intro X; rewrite X; clear X.
apply now_is_FMUSTEV.
apply now_is_ALWAYS.
apply STAT_sat.
unfold reports_succ_or_error in |- *.
SolveOROUTPUTS.
auto.
apply
 cong_respects_stable
  with
    (failc & L
     # parP
         (parP (parP (IOexn_chan << tt >> P) (IOexn_chan << tt >> P1)) zeroP)
         (parP
            (parP
               (parP (heloc ??* get_helo_def heloc mailc)
                  (parP (mailc ??* get_mail_def mailc rcptc)
                     (parP
                        (parP (rcptc ??* get_rcpt_def mailc rcptc)
                           (c
                            ?? (fun c0 : SMTP_cmd =>
                                get_arg c
                                  (fun _ : unit =>
                                   match c0 with
                                   | cmd_helo _ =>
                                       reply_dup_helo c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_mail_from _ =>
                                       reply_dup_mail_from c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_rcpt_to arg =>
                                       do_rcpt_to arg
                                         (smtp_state c c' server_name0
                                            queue_dir0 buf0 from rev_p fwd_p
                                            tofs false)
                                         (fun st : STATE =>
                                          rcptc << st >> zeroP)
                                   | cmd_data data =>
                                       if fwd_paths_size_gt_0 fwd_p
                                       then
                                        save_mail data
                                          (smtp_state c c' server_name0
                                             queue_dir0 buf0 from rev_p fwd_p
                                             tofs false)
                                          (reply_ok_data c'
                                             (mailc
                                              << update_fwd_paths
                                                  (smtp_state c c'
                                                  server_name0 queue_dir0
                                                  buf0 from rev_p fwd_p tofs
                                                  false) nil >> zeroP))
                                       else
                                        reply_no_rcpt_to c'
                                          (rcptc
                                           << smtp_state c c' server_name0
                                                queue_dir0 buf0 from rev_p
                                                fwd_p tofs false >> zeroP)
                                   | cmd_noop =>
                                       reply_ok_noop c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   | cmd_rset =>
                                       reply_ok_rset c'
                                         (mailc
                                          << update_fwd_paths
                                               (smtp_state c c' server_name0
                                                  queue_dir0 buf0 from rev_p
                                                  fwd_p tofs false) nil >>
                                          zeroP)
                                   | cmd_quit => reply_ok_quit c' succ
                                   | cmd_abort => reply_ok_quit c' succ
                                   | cmd_unknown =>
                                       reply_unknown_cmd c'
                                         (rcptc
                                          << smtp_state c c' server_name0
                                               queue_dir0 buf0 from rev_p
                                               fwd_p tofs false >> zeroP)
                                   end)))) zeroP)))
               (parP zeroP (parP (tofs ?? P0) zeroP)))
            (parP zeroP
               (parP zeroP
                  (failc
                   ?? (fun _ : unit => system_failure_chan << tt >> zeroP)))))).
eapply stable_decompose.
apply stable_outP_dup.
apply cong_respects_stable with (failc & L # IOexn_chan << tt >> P).
intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
inversion_clear H5.
inversion_clear H5.
red in |- *; simpl in |- *; split; [ auto | ProcCong ].
CheckStable.
generalize H1; CheckListSet.


apply chanlist_is_set_extend.
auto.
auto.
CheckIncWeak.
CheckSearchInc.

apply is_guarded_is_guarded.
simpl in |- *; auto.
apply is_guarded_is_guarded.
simpl in |- *; auto.
apply inter_weak.
apply inter_weak.
apply inter_nilC.
CheckNotInChanList2 H1.


CheckNotInChanList2 H1.


red in |- *; simpl in |- *; split; [ auto | ProcCong ].

ProcCong.	   
ProcCong.
Qed.

(** main theorem *)

Theorem server_accepts_valid_protocol :
 forall Client : InputStream -> OutputStream -> proc,
 (forall (s : InputStream) (y : OutputStream),
  exists C1 : proc,
    (exists C2 : proc,
       speaks_valid_protocol s C1 /\
       acknowledges_replies y C2 /\ Client s y = parP C1 C2)) ->
 forall file_system : ToFileSystem -> proc,
 (forall tofs : ToFileSystem, valid_fs tofs (file_system tofs)) ->
 ChanList_is_set (result_chan & IOexn_chan & system_failure_chan & nilC) ->
 tsat (FMUSTEV (STAT reports_succ_or_error))
   (result_chan & IOexn_chan & system_failure_chan & nilC
    # nuPl
        (fun s1 : InputStream =>
         nuPl
           (fun s2 : OutputStream =>
            nuPl
              (fun tofs : ToFileSystem =>
               parP (Client s1 s2)
                 (parP (work s1 s2 tofs) (parP (file_system tofs) may_fail)))))).
intros.
apply FMUSTEV_ALWAYS_FMUSTEV.
apply server_accepts_valid_protocol'.
auto.
auto.
auto.
Qed.
