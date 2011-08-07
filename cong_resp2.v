Require Import chan.
Require Import chanlist.
Require Import applpi.
Require Import inj.
Require Import redseq.
Require Import cong.
Require Import cong_tactic.
Require Import cong_resp.
Require Import inv2.

Set Implicit Arguments.

Inductive is_input : proc -> Prop :=
  is_inP : forall A b (c : chan A b) C,
    is_input (c ?? C).

Lemma cong_respects_trans2_k_single :
  forall P P',
    Cong P P' ->
    (forall R,
      ~ is_input R ->
      forall l Q,
	Trans2 (Single R) P l Q ->
	exists Q', Trans2 (Single R) P' l Q' /\ Cong Q Q') /\
    (forall R,
      ~ is_input R ->
      forall l Q',
	Trans2 (Single R) P' l Q' ->
	exists Q, Trans2 (Single R) P l Q /\ Cong Q Q').
intros.
induction H
 as
  [P|
   P Q|
   P Q R|
   P Q P' Q' H IHCong1 H1 IHCong2|
   A b x C|
   P|
   P Q H IHCong|
   P Q R H IHCong1 H1 IHCong2].
(* case for the zero rule *)
split.
intros R HR l Q H.
exists (parP Q zeroP).
split.
apply tr2_parL.
auto.
apply cong_zero.
intros R HR l Q' H.
inversion H.
exists P'.
split; [ auto | apply cong_zero ].
inversion H5.
(* case for the comm rule *)
split.
intros R HR l Q0 H.
inversion H.
clear H0 H3 P0 Q1 H2 L.
exists (parP Q P').
split.
apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' P).
split.
apply tr2_parL.
auto.
apply cong_comm.
intros R HR l Q' H.
inversion H.
exists (parP P P').
split.
apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' Q).
split.
apply tr2_parL.
auto.
apply cong_comm.
(* cas de la regle assoc *)
split.
intros R0 HR0 l Q0 H.
inversion H.
clear H3 Q1 H0 P0 H2 L H2 L.
inversion H5.
clear H0 P0 H6 Q1 H3 L H2 Ps0.
exists (parP P'0 (parP Q R)).
split.
apply tr2_parL.
auto.
apply cong_assoc.
clear H3 L H6 P0 H0 Q1 H2 Ps0.
exists (parP P (parP P'0 R)).
split.
apply tr2_parR.
apply tr2_parL.
auto.
apply cong_assoc.
clear H3 P0 H2 L H0 Q1 H1 Ps.
exists (parP P (parP Q P')).
split.
apply tr2_parR.
apply tr2_parR.
auto.
apply cong_assoc.
intros R0 HR0 l Q' H.
inversion H.
clear H3 Q0 H0 P0 H1 Ps H2 L.
exists (parP (parP P' Q) R).
split.
apply tr2_parL.
apply tr2_parL.
auto.
apply cong_assoc.
inversion H5.
exists (parP (parP P P'0) R).
split.
apply tr2_parL.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP (parP P Q) P'0).
split.
apply tr2_parR.
auto.
apply cong_assoc.
(* cas de la regle par *)
split.
intros R HR l Q0 H0.
inversion H0.
clear H3 H2 H5 H4 Ps Q1 P0 L.
inversion_clear IHCong1.
generalize (H2 _ HR _ _ H7); intro X; inversion_clear X.
inversion_clear H4.
exists (parP x Q').
split.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
clear H4 L H5 P0 H2 Q1 H3 Ps.
inversion_clear IHCong2.
generalize (H2 _ HR _ _ H7); intro X; inversion_clear X.
inversion_clear H4.
exists (parP P' x).
split.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
intros R HR l Q'0 H0.
inversion H0.
inversion_clear IHCong1.
generalize (H9 _ HR _ _ H7); intro X; inversion_clear X.
inversion_clear H10.
exists (parP x Q).
split.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear IHCong2.
generalize (H9 _ HR _ _ H7); intro X; inversion_clear X.
inversion_clear H10.
exists (parP P x).
split.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
(* cas de la replication *)
split.
intros R HR l Q H.
generalize (inv_trans2_rinP H); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
exists (parP (parP (x ??* C) (C x0)) (x ?? C)).
split.
injection H1.
intro X; rewrite X; clear X.
apply tr2_parL.
rewrite H2.
apply tr2_rin.
rewrite H3.
apply cong_tr with (parP (parP (x ??* C) (x ?? C)) (C x0)).
apply cong_par.
apply cong_rep.
apply cong_refl.
ProcCong.
intros R HR l Q' H.
inversion H.
generalize (inv_trans2_rinP H5); intro X; inversion_clear X.
inversion_clear H7.
inversion_clear H8.
exists (parP (x ??* C) (C x0)).
split.
injection H6; intro X; rewrite X; clear X.
rewrite H7; apply tr2_rin.
rewrite H9.
apply cong_tr with (parP (parP (x ??* C) (x ?? C)) (C x0)).
apply cong_par.
apply cong_rep.
apply cong_refl.
ProcCong.
generalize (inv_trans2_inP H5); intro X; inversion_clear X.
injection H6; intro X; rewrite X in HR.
assert False.
apply HR.
apply is_inP.
contradiction.
(* case de la reflexion *)
split.
intros R HR l Q H.
exists Q.
split.
auto.
apply cong_refl.
intros.
exists Q'.
split.
auto.
apply cong_refl.
(* case de la symetrie *)
split.
intros R HR l Q0 H0.
inversion_clear IHCong.
generalize (H2 _ HR _ _ H0); intro X; inversion_clear X.
exists x.
split; intuition.
apply cong_sym; auto.
intros R HR l Q' H0.
inversion_clear IHCong.
generalize (H1 _ HR _ _ H0); intro X; inversion_clear X.
decompose [and] H3; clear H3.
exists x.
split; [ auto | apply cong_sym; auto ].
(* cas de la transitivity *)
split.
intros R0 HR0 l Q0 H0.
inversion_clear IHCong1.
generalize (H2 _ HR0 _ _ H0); intro X; inversion_clear X.
decompose [and] H4; clear H4.
inversion_clear IHCong2.
generalize (H4 _ HR0 _ _ H5); intro X; inversion_clear X.
decompose [and] H8; clear H8.
exists x0.
split.
auto.
apply cong_tr with (Q := x).
auto.
auto.
intros R0 HR0 l Q' H0.
inversion_clear IHCong2.
generalize (H3 _ HR0 _ _ H0); intro X; inversion_clear X.
decompose [and] H4; clear H4.
inversion_clear IHCong1.
generalize (H7 _ HR0 _ _ H5); intro X; inversion_clear X.
decompose [and] H8; clear H8.
exists x0.
split.
auto.
apply cong_tr with (Q := x).
auto.
auto.
Qed.

Lemma cong_respects_trans2_single :
  forall P Q R,
    ~ is_input R ->
    forall l,
      Trans2 (Single R) P l Q ->
      forall P',
	Cong P P' -> exists Q', Trans2 (Single R) P' l Q' /\ Cong Q Q'.
intros.
generalize (cong_respects_trans2_k_single H1); intro.
decompose [and] H2; clear H2.
apply H3.
auto.
auto.
Qed.

Lemma cong_respects_trans2_k_single_inP :
  forall P P',
    Cong P P' ->
    (forall R A b (c : chan A b) T,
      R = c ?? T ->
      forall l Q,
	Trans2 (Single R) P l Q ->
	exists Q',
	  (Trans2 (Single R) P' l Q' \/ Trans2 (Single (c ??* T)) P' l Q') /\
	  Cong Q Q') /\
    (forall R A b (c : chan A b) T,
      R = c ?? T ->
      forall l Q',
	Trans2 (Single R) P' l Q' ->
	exists Q,
	  (Trans2 (Single R) P l Q \/ Trans2 (Single (c ??* T)) P l Q) /\ Cong Q Q').
intros.
induction H
 as
  [P|
   P Q|
   P Q R|
   P Q P' Q' H IHCong1 H1 IHCong2|
   A b x C|
   P|
   P Q H IHCong|
   P Q R H IHCong1 H1 IHCong2].
(* case for the zero rule *)
split.
intros R A b c T HR l Q H.
exists (parP Q zeroP).
split.
left; apply tr2_parL.
auto.
apply cong_zero.
intros R A b c T HR l Q' H.
inversion H.
exists P'.
split.
left.
auto.
apply cong_zero.
inversion H5.
(* case for the comm rule *)
split.
intros R A b c T HR l Q0 H.
inversion H.
clear H0 H3 P0 Q1 H2 L.
exists (parP Q P').
split.
left; apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' P).
split.
left; apply tr2_parL.
auto.
apply cong_comm.
intros R A b c T HR l Q' H.
inversion H.
exists (parP P P').
split.
left; apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' Q).
split.
left; apply tr2_parL.
auto.
apply cong_comm.
(* cas de la regle assoc *)
split.
intros R0 A b c T HR0 l Q0 H.
inversion H.
clear H3 Q1 H0 P0 H2 L H2 L.
inversion H5.
clear H0 P0 H6 Q1 H3 L H2 Ps0.
exists (parP P'0 (parP Q R)).
split.
left; apply tr2_parL.
auto.
apply cong_assoc.
clear H3 L H6 P0 H0 Q1 H2 Ps0.
exists (parP P (parP P'0 R)).
split.
left; apply tr2_parR.
apply tr2_parL.
auto.
apply cong_assoc.
clear H3 P0 H2 L H0 Q1 H1 Ps.
exists (parP P (parP Q P')).
split.
left; apply tr2_parR.
apply tr2_parR.
auto.
apply cong_assoc.
intros R0 A b c T HR0 l Q' H.
inversion H.
clear H3 Q0 H0 P0 H1 Ps H2 L.
exists (parP (parP P' Q) R).
split.
left; apply tr2_parL.
apply tr2_parL.
auto.
apply cong_assoc.
inversion H5.
exists (parP (parP P P'0) R).
split.
left; apply tr2_parL.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP (parP P Q) P'0).
split.
left; apply tr2_parR.
auto.
apply cong_assoc.
(* cas de la regle par *)
split.
intros R A b c T HR l Q0 H0.
inversion H0.
clear H3 H2 H5 H4 Ps Q1 P0 L.
inversion_clear IHCong1.
generalize (H2 _ _ _ _ _ HR _ _ H7); intro X; inversion_clear X.
inversion_clear H4.
inversion_clear H5.
exists (parP x Q').
split.
left; apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
exists (parP x Q').
split.
right; apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
clear H4 L H5 P0 H2 Q1 H3 Ps.
inversion_clear IHCong2.
generalize (H2 _ _ _ _ _ HR _ _ H7); intro X; inversion_clear X.
inversion_clear H4.
exists (parP P' x).
inversion_clear H5.
split.
left; apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
split.
right; apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
intros R A b c T HR l Q'0 H0.
inversion H0.
inversion_clear IHCong1.
generalize (H9 _ _ _ _ _ HR _ _ H7); intro X; inversion_clear X.
inversion_clear H10.
exists (parP x Q).
inversion_clear H11.
split.
left; apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
split.
right; apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear IHCong2.
generalize (H9 _ _ _ _ _ HR _ _ H7); intro X; inversion_clear X.
inversion_clear H10.
exists (parP P x).
inversion_clear H11.
split.
left; apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
split.
right; apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
(* cas de la replication *)
split.
intros R A0 b0 c0 T HR l Q H.
generalize (inv_trans2_rinP H); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
exists (parP (parP (x ??* C) (C x0)) (x ?? C)).
split.
injection H1.
intro X; rewrite X; clear X.
left; apply tr2_parL.
rewrite H2.
apply tr2_rin.
rewrite H3.
apply cong_tr with (parP (parP (x ??* C) (x ?? C)) (C x0)).
apply cong_par.
apply cong_rep.
apply cong_refl.
ProcCong.
intros R A0 b0 c0 T HR l Q' H.
inversion H.
generalize (inv_trans2_rinP H5); intro X; inversion_clear X.
inversion_clear H7.
inversion_clear H8.
exists (parP (x ??* C) (C x0)).
split.
injection H6; intro X; rewrite X; clear X.
rewrite H7.
left; apply tr2_rin.
rewrite H9.
apply cong_tr with (parP (parP (x ??* C) (x ?? C)) (C x0)).
apply cong_par.
apply cong_rep.
apply cong_refl.
ProcCong.
generalize (inv_trans2_inP H5); intro X; inversion_clear X.
injection H6; intro X; rewrite X in HR.
generalize (inP_inj1 HR); intro Y; inversion_clear Y.
generalize c0 T HR; clear c0 T HR; rewrite <- H8; rewrite <- H9;
 clear H8 H9 A0 b0; intros.
generalize (inP_inj_chan HR); intro Y.
generalize HR; clear HR; rewrite <- Y; clear Y c0; intros.
generalize (inP_inj_cont HR); intro Y.
clear HR; rewrite <- Y; clear Y T.
inversion_clear H7.
exists (parP (x ??* C) (C x0)).
split.
right.
rewrite (proj1 H8).
apply tr2_rin.
rewrite (proj2 H8).
apply cong_refl.
(* case de la reflexion *)
split.
intros R A b c T HR l Q H.
exists Q.
split.
auto.
apply cong_refl.
intros.
exists Q'.
split.
auto.
apply cong_refl.
(* case de la symetrie *)
split.
intros R A b c T HR l Q0 H0.
inversion_clear IHCong.
generalize (H2 _ _ _ _ _ HR _ _ H0); intro X; inversion_clear X.
exists x.
split.
intuition.
apply cong_sym; intuition.
intros R A b c T HR l Q' H0.
inversion_clear IHCong.
generalize (H1 _ _ _ _ _ HR _ _ H0); intro X; inversion_clear X.
decompose [and] H3; clear H3.
exists x.
split; [ intuition | apply cong_sym; intuition ].
(* cas de la transitivity *)
split.
intros R0 A b c T HR0 l Q0 H0.
inversion_clear IHCong1.
generalize (H2 _ _ _ _ _ HR0 _ _ H0); intro X; inversion_clear X.
decompose [and] H4; clear H4.
inversion_clear IHCong2.
inversion_clear H5.
generalize (H4 _ _ _ _ _ HR0 _ _ H8); intro X; inversion_clear X.
decompose [and] H5; clear H5.
exists x0.
split.
auto.
apply cong_tr with (Q := x).
auto.
auto.
assert (~ is_input (c ??* T)).
intro X; inversion_clear X.
generalize (cong_respects_trans2_single H5 H8 H1); intro X;
 inversion_clear X.
inversion_clear H9.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
intros R0 A b c T HR0 l Q' H0.
inversion_clear IHCong2.
generalize (H3 _ _ _ _ _ HR0 _ _ H0); intro X; inversion_clear X.
decompose [and] H4; clear H4.
inversion_clear H5.
inversion_clear IHCong1.
generalize (H7 _ _ _ _ _ HR0 _ _ H4); intro X; inversion_clear X.
decompose [and] H8; clear H8.
exists x0.
split.
auto.
apply cong_tr with (Q := x).
auto.
auto.
assert (~ is_input (c ??* T)).
intro X; inversion_clear X.
generalize (cong_respects_trans2_single H5 H4 (cong_sym H));
 intro X; inversion_clear X.
inversion_clear H7.
exists x0.
split.
auto.
apply cong_tr with x.
apply cong_sym; auto.
auto.
Qed.

Lemma cong_respects_trans2_single_inP :
 forall P Q l A b (c : chan A b) T,
   Trans2 (Single (c ?? T)) P l Q ->
   forall P',
     Cong P P' ->
     exists Q',
       (Trans2 (Single (c ?? T)) P' l Q' \/ Trans2 (Single (c ??* T)) P' l Q') /\
   Cong Q Q'.
intros.
generalize (cong_respects_trans2_k_single_inP H0); intros.
inversion_clear H1.
apply H2.
auto.
auto.
Qed.

Lemma cong_respects_trans2_k_pair :
  forall P P',
    Cong P P' ->
    (forall R S,
      ~ is_input R ->
      ~ is_input S ->
      forall l Q,
	Trans2 (Pair R S) P l Q ->
	exists Q',
	  (Trans2 (Pair R S) P' l Q' \/ Trans2 (Pair S R) P' l Q') /\ Cong Q Q') /\
    (forall R S,
      ~ is_input R ->
      ~ is_input S ->
      forall l Q',
	Trans2 (Pair R S) P' l Q' ->
	exists Q,
	  (Trans2 (Pair R S) P l Q \/ Trans2 (Pair S R) P l Q) /\ Cong Q Q').
intros.
induction H
 as
  [P|
   P Q|
   P Q R|
   P Q P' Q' H IHCong1 H1 IHCong2|
   A b x C|
   P|
   P Q H IHCong|
   P Q R H IHCong1 H1 IHCong2].
(* case for the zero rule *)
split.
intros R S HR HS l Q H.
exists (parP Q zeroP).
split.
left.
apply tr2_parL.
auto.
apply cong_zero.
intros R S HR HS l Q' H.
inversion H.
inversion_clear H7.
inversion_clear H7.
exists P'.
split; [ auto | apply cong_zero ].
inversion H5.
(* case for the comm rule *)
split.
intros R S HR HS l Q0 H.
inversion H.
exists (parP Q' P').
split.
right.
eapply tr2_comIO.
apply H7.
auto.
apply cong_comm.
exists (parP Q' P').
split.
right.
eapply tr2_comOI.
apply H7.
auto.
apply cong_comm.
exists (parP Q P').
split.
left.
apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' P).
split.
left.
apply tr2_parL.
auto.
apply cong_comm.
intros R S HR HS l Q' H.
inversion H.
exists (parP Q'0 P').
split.
right.
eapply tr2_comIO.
apply H7.
auto.
apply cong_comm.
exists (parP Q'0 P').
split.
right.
eapply tr2_comOI.
apply H7.
auto.
apply cong_comm.
exists (parP P P').
split.
left.
apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' Q).
split.
left.
apply tr2_parL.
auto.
apply cong_comm.
(* cas de la regle assoc *)
split.
intros R0 S HR0 HS l Q0 H.
inversion H.
inversion H6.
exists (parP P'0 (parP Q Q')).
split.
left.
eapply tr2_comOI.
apply H13.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP P (parP P'0 Q')).
split.
left.
apply tr2_parR.
eapply tr2_comOI.
apply H13.
auto.
apply cong_assoc.
inversion H6.
exists (parP P'0 (parP Q Q')).
split.
left.
eapply tr2_comIO.
apply H13.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP P (parP P'0 Q')).
split.
left.
apply tr2_parR.
eapply tr2_comIO.
apply H13.
auto.
apply cong_assoc.
inversion H5.
exists (parP P'0 (parP Q' R)).
split.
left.
eapply tr2_comOI.
apply H12.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P'0 (parP Q' R)).
split.
left.
eapply tr2_comIO.
apply H12.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P'0 (parP Q R)).
split.
left.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P (parP P'0 R)).
split.
left.
apply tr2_parR.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P (parP Q P')).
split.
left.
apply tr2_parR.
apply tr2_parR.
auto.
apply cong_assoc.
intros R0 S HR0 HS l Q' H.
inversion H.
inversion H7.
exists (parP (parP P' P'0) R).
split.
left.
apply tr2_parL.
eapply tr2_comOI.
apply H6.
auto.
apply cong_assoc.
exists (parP (parP P' Q) P'0).
split.
left.
eapply tr2_comOI.
apply tr2_parL.
apply H6.
auto.
apply cong_assoc.
inversion H7.
exists (parP (parP P' P'0) R).
split.
left.
apply tr2_parL.
eapply tr2_comIO.
apply H6.
auto.
apply cong_assoc.
exists (parP (parP P' Q) P'0).
split.
left.
eapply tr2_comIO.
apply tr2_parL.
apply H6.
auto.
apply cong_assoc.
exists (parP (parP P' Q) R).
split.
left.
apply tr2_parL.
apply tr2_parL.
auto.
apply cong_assoc.
inversion H5.
exists (parP (parP P P'0) Q'0).
split.
left.
eapply tr2_comOI.
apply tr2_parR.
apply H12.
auto.
apply cong_assoc.
exists (parP (parP P P'0) Q'0).
split.
left.
eapply tr2_comIO.
apply tr2_parR.
apply H12.
auto.
apply cong_assoc.
exists (parP (parP P P'0) R).
split.
left.
apply tr2_parL.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP (parP P Q) P'0).
split.
left.
apply tr2_parR.
auto.
apply cong_assoc.
(* cas de la regle par *)
split.
intros R S HR HS l Q0 H0.
inversion H0.
generalize (cong_respects_trans2_single HR H8 H); intro X;
 inversion_clear X.
generalize (cong_respects_trans2_single HS H9 H1); intro X;
 inversion_clear X.
exists (parP x0 x1).
split.
left.
eapply tr2_comOI.
inversion_clear H10.
apply H12.
inversion_clear H11.
auto.
apply cong_par.
intuition.
intuition.
generalize (cong_respects_trans2_single HR H8 H); intro X;
 inversion_clear X.
generalize (cong_respects_trans2_single HS H9 H1); intro X;
 inversion_clear X.
exists (parP x0 x1).
split.
left.
eapply tr2_comIO.
inversion_clear H10.
apply H12.
inversion_clear H11.
auto.
apply cong_par.
intuition.
intuition.
generalize (proj1 IHCong1 _ _ HR HS _ _ H7); intro X; inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP x Q').
split.
left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
exists (parP x Q').
split.
right.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
generalize (proj1 IHCong2 _ _ HR HS _ _ H7); intro X; inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP P' x).
split.
left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
exists (parP P' x).
split.
right.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
intros R S HR HS l Q'0 H0.
inversion H0.
generalize (cong_respects_trans2_single HR H8 (cong_sym H));
 intro X; inversion_clear X.
generalize (cong_respects_trans2_single HS H9 (cong_sym H1));
 intro X; inversion_clear X.
exists (parP x0 x1).
split.
left.
eapply tr2_comOI.
inversion_clear H10.
apply H12.
intuition.
apply cong_par.
apply cong_sym; intuition.
apply cong_sym; intuition.
generalize (cong_respects_trans2_single HR H8 (cong_sym H));
 intro X; inversion_clear X.
generalize (cong_respects_trans2_single HS H9 (cong_sym H1));
 intro X; inversion_clear X.
inversion_clear H10.
inversion_clear H11.
exists (parP x0 x1).
split.
left.
eapply tr2_comIO.
apply H12.
auto.
apply cong_par.
apply cong_sym; auto.
apply cong_sym; auto.
generalize (proj2 IHCong1 _ _ HR HS _ _ H7); intro X; inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP x Q).
split.
left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
exists (parP x Q).
split.
right.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
generalize (proj2 IHCong2 _ _ HR HS _ _ H7); intro X; inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP P x).
split.
left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
exists (parP P x).
split.
right.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
(* cas de la replication *)
split.
intros R S HR HS l Q H.
inversion_clear H.
intros.
inversion H1.
generalize (inv_trans2_rinP H8); intro X; inversion_clear X.
inversion_clear H11.
inversion_clear H12.
discriminate H11.
generalize (inv_trans2_inP H9); intro X; inversion_clear X.
inversion_clear H11.
inversion_clear H12.
discriminate H11.
generalize (inv_trans2_rinP H7); intro X; inversion_clear X.
discriminate H8.
generalize (inv_trans2_inP H7); intro X; inversion_clear X.
discriminate H8.
(* case de la reflexion *)
split.
intros R S HR HS l Q H.
exists Q.
split.
auto.
apply cong_refl.
intros.
exists Q'.
split.
auto.
apply cong_refl.
(* case de la symetrie *)
split.
intros R S HR HS l Q0 H0.
generalize (proj2 IHCong _ _ HR HS _ _ H0); intro X; inversion_clear X.
inversion_clear H1.
inversion_clear H2.
exists x.
split.
auto.
apply cong_sym; auto.
exists x.
split.
auto.
apply cong_sym; auto.
intros R S HR HS l Q' H0.
generalize (proj1 IHCong _ _ HR HS _ _ H0); intro X; inversion_clear X.
inversion_clear H1.
inversion_clear H2.
exists x.
split.
auto.
apply cong_sym; auto.
exists x.
split.
auto.
apply cong_sym; auto.
(* cas de la transitivity *)
split.
intros R0 S HR0 HS l Q0 H0.
generalize (proj1 IHCong1 _ _ HR0 HS _ _ H0); intro X; inversion_clear X.
decompose [and] H2; clear H2.
inversion_clear H3.
generalize (proj1 IHCong2 _ _ HR0 HS _ _ H2); intro X; inversion_clear X.
inversion_clear H3.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
generalize (proj1 IHCong2 _ _ HS HR0 _ _ H2); intro X; inversion_clear X.
inversion_clear H3.
exists x0.
split.
inversion_clear H5.
auto.
auto.
apply cong_tr with x.
auto.
auto.
intros R0 S HR0 HS l Q0 H0.
generalize (proj2 IHCong2 _ _ HR0 HS _ _ H0); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
generalize (proj2 IHCong1 _ _ HR0 HS _ _ H2); intro X; inversion_clear X.
inversion_clear H3.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
generalize (proj2 IHCong1 _ _ HS HR0 _ _ H2); intro X; inversion_clear X.
inversion_clear H3.
exists x0.
split.
inversion_clear H5.
auto.
auto.
apply cong_tr with x.
auto.
auto.
Qed.

Lemma cong_respects_trans2_pair :
 forall P Q R S,
 ~ is_input R ->
 ~ is_input S ->
 forall l,
 Trans2 (Pair R S) P l Q ->
 forall P',
 Cong P P' ->
 exists Q',
   (Trans2 (Pair R S) P' l Q' \/ Trans2 (Pair S R) P' l Q') /\ Cong Q Q'.
intros.
generalize (cong_respects_trans2_k_pair H2); intro X; inversion_clear X.
apply H3.
auto.
auto.
auto.
Qed.

Lemma cong_respects_trans2_k_pair_inP_outP :
 forall P P',
 Cong P P' ->
 (forall R S A b (c : chan A b) T v U,
  R = c ?? T ->
  S = c << v >> U ->
  forall l Q,
  Trans2 (Pair R S) P l Q \/ Trans2 (Pair S R) P l Q ->
  exists Q',
    (Trans2 (Pair R S) P' l Q' \/
     Trans2 (Pair S R) P' l Q' \/
     Trans2 (Pair (c ??* T) S) P' l Q' \/ Trans2 (Pair S (c ??* T)) P' l Q') /\
    Cong Q Q') /\
 (forall R S A b (c : chan A b) T v U,
  R = c ?? T ->
  S = c << v >> U ->
  forall l Q',
  Trans2 (Pair R S) P' l Q' \/ Trans2 (Pair S R) P' l Q' ->
  exists Q : proc,
    (Trans2 (Pair R S) P l Q \/
     Trans2 (Pair S R) P l Q \/
     Trans2 (Pair (c ??* T) S) P l Q \/ Trans2 (Pair S (c ??* T)) P l Q) /\
    Cong Q Q').
intros.
induction H
 as
  [P|
   P Q|
   P Q R|
   P Q P' Q' H IHCong1 H1 IHCong2|
   A b x C|
   P|
   P Q H IHCong|
   P Q R H IHCong1 H1 IHCong2].
(* case for the zero rule *)
split.
intros R S A b c T v U HR HS l Q H.
inversion_clear H.
exists (parP Q zeroP).
split.
left.
apply tr2_parL.
auto.
apply cong_zero.
exists (parP Q zeroP).
split.
right; left.
apply tr2_parL.
auto.
apply cong_zero.
intros R S A b c T v U HR HS l Q' H.
inversion_clear H.
inversion H0.
inversion_clear H7.
inversion_clear H7.
exists P'.
split; [ auto | apply cong_zero ].
inversion H5.
inversion H0.
inversion_clear H7.
inversion_clear H7.
exists P'.
split; [ auto | apply cong_zero ].
inversion H5.
(* case for the comm rule *)
split.
intros R S A b c T v U HR HS l Q0 H.
inversion_clear H.
inversion H0.
exists (parP Q' P').
split.
right; left.
eapply tr2_comIO.
apply H7.
auto.
apply cong_comm.
exists (parP Q' P').
split.
right; left.
eapply tr2_comOI.
apply H7.
auto.
apply cong_comm.
exists (parP Q P').
split.
left.
apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' P).
split.
left.
apply tr2_parL.
auto.
apply cong_comm.
inversion H0.
exists (parP Q' P').
split.
left.
eapply tr2_comIO.
apply H7.
auto.
apply cong_comm.
exists (parP Q' P').
split.
left.
eapply tr2_comOI.
apply H7.
auto.
apply cong_comm.
exists (parP Q P').
split.
right; left.
apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' P).
split.
right; left.
apply tr2_parL.
auto.
apply cong_comm.
intros R S A b c T v U HR HS l Q' H.
inversion_clear H.
inversion H0.
exists (parP Q'0 P').
split.
right; left.
eapply tr2_comIO.
apply H7.
auto.
apply cong_comm.
exists (parP Q'0 P').
split.
right; left.
eapply tr2_comOI.
apply H7.
auto.
apply cong_comm.
exists (parP P P').
split.
left.
apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' Q).
split.
left.
apply tr2_parL.
auto.
apply cong_comm.
inversion H0.
exists (parP Q'0 P').
split.
left.
eapply tr2_comIO.
apply H7.
auto.
apply cong_comm.
exists (parP Q'0 P').
split.
left.
eapply tr2_comOI.
apply H7.
auto.
apply cong_comm.
exists (parP P P').
split.
right; left.
apply tr2_parR.
auto.
apply cong_comm.
exists (parP P' Q).
split.
right; left.
apply tr2_parL.
auto.
apply cong_comm.
(* cas de la regle assoc *)
split.
intros R0 S A b c T v U HR0 HS l Q0 H.
inversion_clear H.
inversion H0.
inversion H6.
exists (parP P'0 (parP Q Q')).
split.
left.
eapply tr2_comOI.
apply H13.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP P (parP P'0 Q')).
split.
left.
apply tr2_parR.
eapply tr2_comOI.
apply H13.
auto.
apply cong_assoc.
inversion H6.
exists (parP P'0 (parP Q Q')).
split.
left.
eapply tr2_comIO.
apply H13.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP P (parP P'0 Q')).
split.
left.
apply tr2_parR.
eapply tr2_comIO.
apply H13.
auto.
apply cong_assoc.
inversion H5.
exists (parP P'0 (parP Q' R)).
split.
left.
eapply tr2_comOI.
apply H12.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P'0 (parP Q' R)).
split.
left.
eapply tr2_comIO.
apply H12.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P'0 (parP Q R)).
split.
left.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P (parP P'0 R)).
split.
left.
apply tr2_parR.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P (parP Q P')).
split.
left.
apply tr2_parR.
apply tr2_parR.
auto.
apply cong_assoc.
inversion H0.
inversion H6.
exists (parP P'0 (parP Q Q')).
split.
right; left.
eapply tr2_comOI.
apply H13.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP P (parP P'0 Q')).
split.
right; left.
apply tr2_parR.
eapply tr2_comOI.
apply H13.
auto.
apply cong_assoc.
inversion H6.
exists (parP P'0 (parP Q Q')).
split.
right; left.
eapply tr2_comIO.
apply H13.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP P (parP P'0 Q')).
split.
right; left.
apply tr2_parR.
eapply tr2_comIO.
apply H13.
auto.
apply cong_assoc.
inversion H5.
exists (parP P'0 (parP Q' R)).
split.
right; left.
eapply tr2_comOI.
apply H12.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P'0 (parP Q' R)).
split.
right; left.
eapply tr2_comIO.
apply H12.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P'0 (parP Q R)).
split.
right; left.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P (parP P'0 R)).
split.
right; left.
apply tr2_parR.
apply tr2_parL.
auto.
apply cong_assoc.
exists (parP P (parP Q P')).
split.
right; left.
apply tr2_parR.
apply tr2_parR.
auto.
apply cong_assoc.
intros R0 S A b c T v U HR0 HS l Q' H.
inversion_clear H.
inversion H0.
inversion H7.
exists (parP (parP P' P'0) R).
split.
left.
apply tr2_parL.
eapply tr2_comOI.
apply H6.
auto.
apply cong_assoc.
exists (parP (parP P' Q) P'0).
split.
left.
eapply tr2_comOI.
apply tr2_parL.
apply H6.
auto.
apply cong_assoc.
inversion H7.
exists (parP (parP P' P'0) R).
split.
left.
apply tr2_parL.
eapply tr2_comIO.
apply H6.
auto.
apply cong_assoc.
exists (parP (parP P' Q) P'0).
split.
left.
eapply tr2_comIO.
apply tr2_parL.
apply H6.
auto.
apply cong_assoc.
exists (parP (parP P' Q) R).
split.
left.
apply tr2_parL.
apply tr2_parL.
auto.
apply cong_assoc.
inversion H5.
exists (parP (parP P P'0) Q'0).
split.
left.
eapply tr2_comOI.
apply tr2_parR.
apply H12.
auto.
apply cong_assoc.
exists (parP (parP P P'0) Q'0).
split.
left.
eapply tr2_comIO.
apply tr2_parR.
apply H12.
auto.
apply cong_assoc.
exists (parP (parP P P'0) R).
split.
left.
apply tr2_parL.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP (parP P Q) P'0).
split.
left.
apply tr2_parR.
auto.
apply cong_assoc.
inversion H0.
inversion H7.
exists (parP (parP P' P'0) R).
split.
right; left.
apply tr2_parL.
eapply tr2_comOI.
apply H6.
auto.
apply cong_assoc.
exists (parP (parP P' Q) P'0).
split.
right; left.
eapply tr2_comOI.
apply tr2_parL.
apply H6.
auto.
apply cong_assoc.
inversion H7.
exists (parP (parP P' P'0) R).
split.
right; left.
apply tr2_parL.
eapply tr2_comIO.
apply H6.
auto.
apply cong_assoc.
exists (parP (parP P' Q) P'0).
split.
right; left.
eapply tr2_comIO.
apply tr2_parL.
apply H6.
auto.
apply cong_assoc.
exists (parP (parP P' Q) R).
split.
right; left.
apply tr2_parL.
apply tr2_parL.
auto.
apply cong_assoc.
inversion H5.
exists (parP (parP P P'0) Q'0).
split.
right; left.
eapply tr2_comOI.
apply tr2_parR.
apply H12.
auto.
apply cong_assoc.
exists (parP (parP P P'0) Q'0).
split.
right; left.
eapply tr2_comIO.
apply tr2_parR.
apply H12.
auto.
apply cong_assoc.
exists (parP (parP P P'0) R).
split.
right; left.
apply tr2_parL.
apply tr2_parR.
auto.
apply cong_assoc.
exists (parP (parP P Q) P'0).
split.
right; left.
apply tr2_parR.
auto.
apply cong_assoc.
(* cas de la regle par *)
split.
intros R S A b c T v U HR HS l Q0 H0.
elim H0; clear H0; intro H0.
inversion H0.
rewrite HR in H8.
generalize (cong_respects_trans2_single_inP H8 H); intro X;
 inversion_clear X.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_single H11 H9 H1); intro X;
 inversion_clear X.
exists (parP x0 x1).
split.
inversion_clear H10.
inversion_clear H13.
left.
eapply tr2_comOI.
rewrite HR.
apply H10.
inversion_clear H12.
auto.
generalize (inv_trans2_OutL H10); intro X; inversion_clear X.
discriminate H13.
apply cong_par.
intuition.
intuition.
rewrite HR in H8.
generalize (cong_respects_trans2_single_inP H8 H); intro X;
 inversion_clear X.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_single H11 H9 H1); intro X;
 inversion_clear X.
exists (parP x0 x1).
split.
inversion_clear H10.
inversion_clear H13.
left.
eapply tr2_comIO.
rewrite HR.
apply H10.
intuition.
right; right; left.
eapply tr2_comIO.
apply H10.
intuition.
apply cong_par.
intuition.
intuition.
assert (Trans2 (Pair R S) P l P'0 \/ Trans2 (Pair S R) P l P'0).
auto.
clear H7; rename H8 into H7.
generalize (proj1 IHCong1 _ _ _ _ _ _ _ _ HR HS _ _ H7); intro X;
 inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP x Q').
split.
left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear H8.
exists (parP x Q').
split.
right; left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear H9.
exists (parP x Q').
split.
right; right; left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
exists (parP x Q').
split.
right; right; right.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
assert (Trans2 (Pair R S) Q l P'0 \/ Trans2 (Pair S R) Q l P'0).
auto.
clear H7; rename H8 into H7.
generalize (proj1 IHCong2 _ _ _ _ _ _ _ _ HR HS _ _ H7); intro X;
 inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP P' x).
split.
left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion_clear H8.
exists (parP P' x).
split.
right; left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion_clear H9.
exists (parP P' x).
split.
right; right; left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
exists (parP P' x).
split.
right; right; right.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion H0.
rewrite HR in H9.
generalize (cong_respects_trans2_single_inP H9 H1); intro X;
 inversion_clear X.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_single H11 H8 H); intro X;
 inversion_clear X.
exists (parP x1 x0).
split.
inversion_clear H10.
inversion_clear H13.
right; left.
eapply tr2_comOI.
inversion_clear H12.
apply H13.
rewrite HR.
auto.
right; right; right.
eapply tr2_comOI.
inversion_clear H12.
apply H13.
auto.
apply cong_par.
intuition.
intuition.
generalize (inv_trans2_OutL H9); intro X; inversion_clear X.
rewrite HR in H10; discriminate H10.
assert (Trans2 (Pair R S) P l P'0 \/ Trans2 (Pair S R) P l P'0).
auto.
clear H7; rename H8 into H7.
generalize (proj1 IHCong1 _ _ _ _ _ _ _ _ HR HS _ _ H7); intro X;
 inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP x Q').
split.
left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear H8.
exists (parP x Q').
split.
right; left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear H9.
exists (parP x Q').
split.
right; right; left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
exists (parP x Q').
split.
right; right; right.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
assert (Trans2 (Pair R S) Q l P'0 \/ Trans2 (Pair S R) Q l P'0).
auto.
clear H7; rename H8 into H7.
generalize (proj1 IHCong2 _ _ _ _ _ _ _ _ HR HS _ _ H7); intro X;
 inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP P' x).
split.
left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion_clear H8.
exists (parP P' x).
split.
right; left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion_clear H9.
exists (parP P' x).
split.
right; right; left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
exists (parP P' x).
split.
right; right; right.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
intros R S A b c T v U HR HS l Q'0 H0.
elim H0; clear H0; intro H0.
inversion H0.
rewrite HR in H8.
generalize (inv_trans2_OutL H8); intro X; inversion_clear X.
discriminate H10.
rewrite HR in H8.
generalize
 (cong_respects_trans2_single_inP H8 (cong_sym H));
 intro X; inversion_clear X.
inversion_clear H10.
inversion_clear H11.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_single H11 H9 (cong_sym H1));
 intro X; inversion_clear X.
inversion_clear H13.
exists (parP x0 x1).
split.
left.
eapply tr2_comIO.
rewrite HR.
apply H10.
auto.
apply cong_par.
apply cong_sym; intuition.
apply cong_sym; intuition.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_single H11 H9 (cong_sym H1));
 intro X; inversion_clear X.
inversion_clear H13.
exists (parP x0 x1).
split.
right; right; left.
eapply tr2_comIO.
rewrite HR.
apply H10.
auto.
apply cong_par.
apply cong_sym; intuition.
apply cong_sym; intuition.
assert (Trans2 (Pair R S) P' l P'0 \/ Trans2 (Pair S R) P' l P'0).
auto.
clear H7; rename H8 into H7.
generalize (proj2 IHCong1 _ _ _ _ _ _ _ _ HR HS _ _ H7); intro X;
 inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP x Q).
split.
left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear H8.
exists (parP x Q).
split.
right; left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear H9.
exists (parP x Q).
split.
right; right; left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
exists (parP x Q).
split.
right; right; right.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
assert (Trans2 (Pair R S) Q' l P'0 \/ Trans2 (Pair S R) Q' l P'0).
auto.
clear H7; rename H8 into H7.
generalize (proj2 IHCong2 _ _ _ _ _ _ _ _ HR HS _ _ H7); intro X;
 inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP P x).
split.
left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion_clear H8.
exists (parP P x).
split.
right; left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion_clear H9.
exists (parP P x).
split.
right; right; left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
exists (parP P x).
split.
right; right; right.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion H0.
rewrite HR in H9.
generalize
 (cong_respects_trans2_single_inP H9 (cong_sym H1));
 intro X; inversion_clear X.
inversion_clear H10.
inversion_clear H11.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_single H11 H8 (cong_sym H));
 intro X; inversion_clear X.
inversion_clear H13.
exists (parP x1 x0).
split.
right; left.
eapply tr2_comOI.
apply H14.
rewrite HR.
auto.
apply cong_par.
apply cong_sym; intuition.
apply cong_sym; intuition.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_single H11 H8 (cong_sym H));
 intro X; inversion_clear X.
inversion_clear H13.
exists (parP x1 x0).
split.
right; right; right.
eapply tr2_comOI.
apply H14.
auto.
apply cong_par.
apply cong_sym; intuition.
apply cong_sym; intuition.
generalize (inv_trans2_OutL H9); intro X; inversion_clear X.
rewrite HR in H10; discriminate H10.
assert (Trans2 (Pair R S) P' l P'0 \/ Trans2 (Pair S R) P' l P'0).
auto.
clear H7; rename H8 into H7.
generalize (proj2 IHCong1 _ _ _ _ _ _ _ _ HR HS _ _ H7); intro X;
 inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP x Q).
split.
left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear H8.
exists (parP x Q).
split.
right; left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear H9.
exists (parP x Q).
split.
right; right; left.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
exists (parP x Q).
split.
right; right; right.
apply tr2_parL.
auto.
apply cong_par.
auto.
auto.
assert (Trans2 (Pair R S) Q' l P'0 \/ Trans2 (Pair S R) Q' l P'0).
auto.
clear H7; rename H8 into H7.
generalize (proj2 IHCong2 _ _ _ _ _ _ _ _ HR HS _ _ H7); intro X;
 inversion_clear X.
inversion_clear H8.
inversion_clear H9.
exists (parP P x).
split.
left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion_clear H8.
exists (parP P x).
split.
right; left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
inversion_clear H9.
exists (parP P x).
split.
right; right; left.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
exists (parP P x).
split.
right; right; right.
apply tr2_parR.
auto.
apply cong_par.
auto.
auto.
(* cas de la replication *)
split.
intros R S A0 b0 c T v U HR HS l Q H.
inversion_clear H.
inversion_clear H0.
inversion_clear H0.
intros.
inversion_clear H1.
inversion_clear H2.
generalize (inv_trans2_OutL H1); intro X; inversion_clear X.
rewrite H in H2; discriminate H2.
generalize (inv_trans2_inP H3); intro X; inversion_clear X.
rewrite H0 in H2; discriminate H2.
inversion_clear H1.
inversion_clear H1.
inversion_clear H2.
generalize (inv_trans2_rinP H1); intro X; inversion_clear X.
rewrite H0 in H2; discriminate H2.
generalize (inv_trans2_inP H3); intro X; inversion_clear X.
inversion_clear H4.
inversion_clear H5.
discriminate H4.
inversion_clear H1.
inversion_clear H1.
(* cas de l'identite *)
split.
intros R S A b c T v U HR HS l Q0 H0.
exists Q0.
split; [ idtac | apply cong_refl ].
inversion_clear H0.
auto.
auto.
intros R S A b c T v U HR HS l Q0 H0.
exists Q0.
split; [ idtac | apply cong_refl ].
inversion_clear H0.
auto.
auto.
(* cas de la symetrie *)
split.
intros R S A b c T v U HR HS l Q0 H0.
generalize (proj2 IHCong _ _ _ _ _ _ _ _ HR HS _ _ H0); intro X;
 inversion_clear X.
inversion_clear H1.
inversion_clear H2.
exists x.
split; [ auto | apply cong_sym; auto ].
exists x.
split; [ auto | apply cong_sym; auto ].
intros R S A0 b0 c T v U HR HS l Q0 H0.
generalize (proj1 IHCong _ _ _ _ _ _ _ _ HR HS _ _ H0); intro X;
 inversion_clear X.
inversion_clear H1.
inversion_clear H2.
exists x.
split.
auto.
apply cong_sym; auto.
inversion_clear H1.
exists x.
split.
auto.
apply cong_sym; auto.
inversion_clear H2.
exists x.
split.
auto.
apply cong_sym; auto.
exists x.
split.
auto.
apply cong_sym; auto.
(* cas de la transitivity *)
split.
intros R0 S A b c T v U HR0 HS l Q0 H0.
generalize (proj1 IHCong1 _ _ _ _ _ _ _ _ HR0 HS _ _ H0); intro X;
 inversion_clear X.
inversion_clear H2.
inversion_clear H3.
assert (Trans2 (Pair R0 S) Q l x \/ Trans2 (Pair S R0) Q l x).
auto.
clear H2.
generalize (proj1 IHCong2 _ _ _ _ _ _ _ _ HR0 HS _ _ H3); intro X;
 inversion_clear X.
inversion_clear H2.
inversion_clear H5.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
inversion_clear H2.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
inversion_clear H5.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
inversion_clear H2.
assert (Trans2 (Pair R0 S) Q l x \/ Trans2 (Pair S R0) Q l x).
auto.
clear H3.
generalize (proj1 IHCong2 _ _ _ _ _ _ _ _ HR0 HS _ _ H2); intro X;
 inversion_clear X.
inversion_clear H3.
inversion_clear H5.
exists x0.
split; auto.
apply cong_tr with x; [ auto | auto ].
inversion_clear H3.
exists x0.
split; auto.
apply cong_tr with x; [ auto | auto ].
inversion_clear H5.
exists x0.
split; auto.
apply cong_tr with x; [ auto | auto ].
exists x0.
split; auto.
apply cong_tr with x; [ auto | auto ].
inversion_clear H3.
assert (~ is_input (c ??* T)).
intro X; inversion_clear X.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_pair H3 H5 H2 H1); intro X;
 inversion_clear X.
inversion_clear H6.
inversion_clear H7.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
exists x0; split; auto.
apply cong_tr with x.
auto.
auto.
assert (~ is_input (c ??* T)).
intro X; inversion_clear X.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_pair H5 H3 H2 H1); intro X;
 inversion_clear X.
inversion_clear H6.
inversion_clear H7.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
exists x0; split; auto.
apply cong_tr with x.
auto.
auto.
intros R0 S A b c T v U HR0 HS l Q0 H0.
generalize (proj2 IHCong2 _ _ _ _ _ _ _ _ HR0 HS _ _ H0); intro X;
 inversion_clear X.
inversion_clear H2.
inversion_clear H3.
assert (Trans2 (Pair R0 S) Q l x \/ Trans2 (Pair S R0) Q l x).
auto.
clear H2.
generalize (proj2 IHCong1 _ _ _ _ _ _ _ _ HR0 HS _ _ H3); intro X;
 inversion_clear X.
inversion_clear H2.
inversion_clear H5.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
inversion_clear H2.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
inversion_clear H5.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
exists x0.
split.
auto.
apply cong_tr with x.
auto.
auto.
inversion_clear H2.
assert (Trans2 (Pair R0 S) Q l x \/ Trans2 (Pair S R0) Q l x).
auto.
clear H3.
generalize (proj2 IHCong1 _ _ _ _ _ _ _ _ HR0 HS _ _ H2); intro X;
 inversion_clear X.
inversion_clear H3.
inversion_clear H5.
exists x0.
split; auto.
apply cong_tr with x; [ auto | auto ].
inversion_clear H3.
exists x0.
split; auto.
apply cong_tr with x; [ auto | auto ].
inversion_clear H5.
exists x0.
split; auto.
apply cong_tr with x; [ auto | auto ].
exists x0.
split; auto.
apply cong_tr with x; [ auto | auto ].
inversion_clear H3.
assert (~ is_input (c ??* T)).
intro X; inversion_clear X.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_pair H3 H5 H2 (cong_sym H));
 intro X; inversion_clear X.
inversion_clear H6.
inversion_clear H7.
exists x0.
split.
auto.
apply cong_tr with x.
apply cong_sym; auto.
auto.
exists x0; split; auto.
apply cong_tr with x.
apply cong_sym; auto.
auto.
assert (~ is_input (c ??* T)).
intro X; inversion_clear X.
assert (~ is_input S).
rewrite HS; intro X; inversion_clear X.
generalize (cong_respects_trans2_pair H5 H3 H2 (cong_sym H));
 intro X; inversion_clear X.
inversion_clear H6.
inversion_clear H7.
exists x0.
split.
auto.
apply cong_tr with x.
apply cong_sym; auto.
auto.
exists x0; split; auto.
apply cong_tr with x.
apply cong_sym; auto.
auto.
Qed.

Lemma cong_respects_trans2_pair_inP_outP :
 forall P Q A b (c : chan A b) T v U l,
 Trans2 (Pair (c ?? T) (c << v >> U)) P l Q ->
 forall P',
 Cong P P' ->
 exists Q',
   (Trans2 (Pair (c ?? T) (c << v >> U)) P' l Q' \/
    Trans2 (Pair (c << v >> U) (c ?? T)) P' l Q' \/
    Trans2 (Pair (c ??* T) (c << v >> U)) P' l Q' \/
    Trans2 (Pair (c << v >> U) (c ??* T)) P' l Q') /\ 
   Cong Q Q'.
intros.
generalize (proj1 (cong_respects_trans2_k_pair_inP_outP H0)); intro.
generalize
 (H1 (c ?? T) (c << v >> U) _ _ _ _ _ _ (refl_equal (c ?? T))
    (refl_equal (c << v >> U))); intros.
apply H2.
auto.
Qed.

Lemma cong_respects_trans2_pair_outP_inP :
 forall P Q A b (c : chan A b) T v U l,
 Trans2 (Pair (c << v >> U) (c ?? T)) P l Q ->
 forall P',
 Cong P P' ->
 exists Q',
   (Trans2 (Pair (c ?? T) (c << v >> U)) P' l Q' \/
    Trans2 (Pair (c << v >> U) (c ?? T)) P' l Q' \/
    Trans2 (Pair (c ??* T) (c << v >> U)) P' l Q' \/
    Trans2 (Pair (c << v >> U) (c ??* T)) P' l Q') /\ 
   Cong Q Q'.
intros.
generalize (proj1 (cong_respects_trans2_k_pair_inP_outP H0)); intro.
generalize
 (H1 (c ?? T) (c << v >> U) _ _ _ _ _ _ (refl_equal (c ?? T))
    (refl_equal (c << v >> U))); intros.
apply H2.
auto.
Qed.

Lemma cong_respects_reduced :
 forall R,
 ~ is_input R ->
 forall P Q,
 reduced R P Q ->
 forall P',
 Cong_st P P' -> exists Q', reduced R P' Q' /\ Cong_st Q Q'.
intros.
inversion H0.
clear H3 P0.
assert (Cong Q0 (sndT P')).
inversion_clear H1.
apply cong_tr with (sndT P).
rewrite <- H4; apply cong_refl.
auto.
generalize (cong_respects_trans2_single H H2 H3); intro.
inversion_clear H6.
inversion_clear H7.
exists (K # x).
split.
induction P'.
inversion_clear H1.
simpl in H7.
rewrite <- H4 in H7.
simpl in H7.
rewrite <- H7.
apply red_single_in with (c := c) (v := v).
exact H6.
split.
simpl in |- *; auto.
simpl in |- *; auto.
clear H3 P0.
assert (Cong Q0 (sndT P')).
inversion_clear H1.
apply cong_tr with (sndT P).
rewrite <- H4; apply cong_refl.
auto.
generalize (cong_respects_trans2_single H H2 H3); intro.
inversion_clear H6.
inversion_clear H7.
exists (K # x).
split.
induction P'.
inversion_clear H1.
simpl in H7.
rewrite <- H4 in H7.
simpl in H7.
rewrite <- H7.
apply red_single_out with (c := c) (v := v).
exact H6.
split.
simpl in |- *; auto.
simpl in |- *; auto.
clear H3 P0.
assert (Cong Q0 (sndT P')).
inversion_clear H1.
apply cong_tr with (sndT P).
rewrite <- H4; apply cong_refl.
auto.
generalize (cong_respects_trans2_single H H2 H3); intro.
inversion_clear H6.
inversion_clear H7.
exists (c & K # x).
split.
induction P'.
inversion_clear H1.
simpl in H7.
rewrite <- H4 in H7.
simpl in H7.
rewrite <- H7.
apply red_single_nu with (c := c).
exact H6.
split.
simpl in |- *; auto.
simpl in |- *; auto.
generalize (inv_trans2_TauL H2); intros.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
assert (~ is_input S).
rewrite H8; intro.
inversion_clear H6.
inversion_clear H1.
rewrite <- H4 in H10; simpl in H10.
generalize (cong_respects_trans2_pair H H6 H2 H10); intro X;
 inversion_clear X.
inversion_clear H1.
exists (fstT P' # x2).
split.
inversion_clear H11.
induction P'; simpl in |- *.
apply red_pairL with (S := S) (c := c).
exact H1.
induction P'; simpl in |- *.
apply red_pairR with (S := S) (c := c).
exact H1.
split.
simpl in |- *.
rewrite <- H9; rewrite <- H4; simpl in |- *; auto.
simpl in |- *.
auto.
inversion_clear H6.
inversion_clear H7.
rewrite H6 in H.
assert False.
apply H; apply is_inP.
contradiction.
inversion_clear H7.
inversion_clear H6.
assert (~ is_input S).
rewrite H8; intro.
inversion_clear H6.
inversion_clear H1.
rewrite <- H4 in H10; simpl in H10.
generalize (cong_respects_trans2_pair H H6 H2 H10); intro X;
 inversion_clear X.
inversion_clear H1.
exists (fstT P' # x2).
split.
inversion_clear H11.
induction P'.
apply red_pairL with (S := S) (c := c).
exact H1.
induction P'.
apply red_pairR with (S := S) (c := c).
exact H1.
rewrite <- H9; rewrite <- H4; split; [ auto | auto ].
inversion_clear H6.
rewrite H7 in H2.
rewrite H8 in H2.
inversion_clear H1.
rewrite <- H4 in H9.
generalize (cong_respects_trans2_pair_outP_inP H2 H9);
 intro X; inversion_clear X.
inversion_clear H1.
exists (fstT P' # x2).
split.
inversion_clear H10.
induction P'.
apply red_pairR with (S := c ?? x0) (c := c).
rewrite H7.
exact H1.
inversion_clear H1.
induction P'.
apply red_pairL with (S := c ?? x0) (c := c).
rewrite H7.
exact H10.
inversion_clear H10.
induction P'.
apply red_pairR with (S := c ??* x0) (c := c).
rewrite H7.
exact H1.
induction P'.
apply red_pairL with (S := c ??* x0) (c := c).
rewrite H7.
exact H1.
rewrite <- H6; rewrite <- H4; simpl in |- *.
split.
simpl in |- *; auto.
simpl in |- *; auto.
generalize (inv_trans2_TauL H2); intros.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
assert (~ is_input S).
rewrite H7; intro.
inversion_clear H6.
inversion_clear H1.
rewrite <- H4 in H10; simpl in H10.
generalize (cong_respects_trans2_pair H6 H H2 H10); intro X;
 inversion_clear X.
inversion_clear H1.
exists (fstT P' # x2).
split.
inversion_clear H11.
induction P'; simpl in |- *.
apply red_pairR with (S := S) (c := c).
exact H1.
induction P'; simpl in |- *.
apply red_pairL with (S := S) (c := c).
exact H1.
split.
simpl in |- *.
rewrite <- H9; rewrite <- H4; simpl in |- *; auto.
simpl in |- *.
auto.
inversion_clear H6.
inversion_clear H7.
inversion_clear H1.
rewrite <- H4 in H9.
simpl in H9.
rewrite H6 in H2; rewrite H8 in H2.
generalize (cong_respects_trans2_pair_inP_outP H2 H9);
 intro X; inversion_clear X.
inversion_clear H1.
exists (fstT P' # x2).
split.
inversion_clear H10.
induction P'.
apply red_pairR with (S := c ?? x0) (c := c).
rewrite H8.
exact H1.
inversion_clear H1.
induction P'.
apply red_pairL with (S := c ?? x0) (c := c).
rewrite H8.
exact H10.
inversion_clear H10.
induction P'.
apply red_pairR with (S := c ??* x0) (c := c).
rewrite H8.
exact H1.
induction P'.
apply red_pairL with (S := c ??* x0) (c := c).
rewrite H8.
exact H1.
split.
simpl in |- *; auto.
rewrite <- H7; rewrite <- H4; auto.
simpl in |- *; auto.
inversion_clear H7.
inversion_clear H6.
assert (~ is_input S).
rewrite H7; intro.
inversion_clear H6.
inversion_clear H1.
rewrite <- H4 in H10; simpl in H10.
generalize (cong_respects_trans2_pair H6 H H2 H10); intro X;
 inversion_clear X.
inversion_clear H1.
exists (fstT P' # x2).
split.
inversion_clear H11.
induction P'.
apply red_pairR with (S := S) (c := c).
exact H1.
induction P'.
apply red_pairL with (S := S) (c := c).
exact H1.
rewrite <- H9; rewrite <- H4; split; [ auto | auto ].
inversion_clear H6.
rewrite H8 in H.
assert False.
apply H; apply is_inP.
contradiction.
Qed.

Lemma cong_respects_reduced_inP :
    forall A b (c : chan A b) T P Q,
    reduced (c ?? T) P Q ->
    forall P' : state,
    Cong_st P P' ->
    (exists Q', reduced (c ?? T) P' Q' /\ Cong_st Q Q') \/
    (exists Q', reduced (c ??* T) P' Q' /\ Cong_st Q Q').
intros.
inversion H.
clear H2 P0.
generalize (inv_trans2_InL H1); intro X; inversion_clear X.
inversion_clear H2.
generalize (Single_inj H5); clear H5; intros.
generalize (inP_inj1 H2); intro X; inversion_clear X.
generalize c0 v H1 x H2; clear c0 v H1 x H2; rewrite <-H5; rewrite <-H6; clear H5 H6 A0 b0; intros.
generalize (inP_inj_chan H2); intro.
generalize H1 H2; clear H1 H2; rewrite <-H5; clear H5 c0; intros.
generalize (inP_inj_cont H2); intro.
generalize H1 H2; clear H1 H2; rewrite <-H5; clear H5; intros.
clear H2.
assert (Cong Q0 (sndT P')).
inversion_clear H0.
apply cong_tr with (sndT P).
rewrite <-H3; apply cong_refl.
auto.
generalize (cong_respects_trans2_single_inP H1 H2); intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
left.
exists (K#x0).
split.
induction P'.
inversion_clear H0.
simpl in H5.
rewrite <-H3 in H5.
simpl in H5.
rewrite <-H5.
apply red_single_in with (c:=c) (v:=v).
exact H6.
split.
simpl; auto.
simpl; auto.
right.
exists (K#x0).
split.
induction P'.
inversion_clear H0.
simpl in H5.
rewrite <-H3 in H5.
simpl in H5.
rewrite <-H5.
apply red_single_in with (c:=c) (v:=v).
exact H6.
split.
simpl; auto.
simpl; auto.
discriminate H5.
generalize (inv_trans2_OutL H1); intro.
inversion_clear H5.
discriminate H6.                
generalize (inv_trans2_NewL H1); intro.
inversion_clear H5.
inversion_clear H6.
discriminate H5.
inversion_clear H6.
discriminate H5.
generalize (inv_trans2_TauL H1); intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
discriminate H6.
inversion_clear H5.
inversion_clear H6.
generalize (inP_inj1 H5); intro X; inversion_clear X.
generalize c0 H1 x x0 H5 H7; clear c0 H1 x x0 H5 H7; rewrite <-H6; rewrite <-H8; clear H6 H8; intros.
generalize (inP_inj_chan H5); intro.
generalize H1 H5 H7; clear H1 H5 H7.
elim H6.
clear H6 c0.
intros.
clear H5 x0.
inversion_clear H0.
rewrite <-H3 in H6; simpl in H6.
rewrite H7 in H1.
generalize (cong_respects_trans2_pair_inP_outP H1 H6); intro X; inversion_clear X.
inversion_clear H0.
inversion_clear H8.
left.
exists ((fstT P')#x0).
split.
induction P'.
apply red_pairL with (S:=S) (c:=c).
rewrite H7; auto.
split; simpl.
rewrite <-H5; rewrite <-H3; auto.
auto.
inversion_clear H0.
left.
exists ((fstT P')#x0).
split.
induction P'.
apply red_pairR with (S:=S) (c:=c).
rewrite H7; auto.
split; simpl.
rewrite <-H5; rewrite <-H3; auto.
auto.
inversion_clear H8.
right.
exists ((fstT P')#x0).
split.
induction P'.
apply red_pairL with (S:=S) (c:=c).
rewrite H7; auto.
split; simpl.
rewrite <-H5; rewrite <-H3; auto.
auto.
right.
exists ((fstT P')#x0).
split.
induction P'.
apply red_pairR with (S:=S) (c:=c).
rewrite H7; auto.
split; simpl.
rewrite <-H5; rewrite <-H3; auto.
auto.
inversion_clear H6.
inversion_clear H5.
discriminate H6.
inversion_clear H5.
discriminate H6.
generalize (inv_trans2_TauL H1); intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
discriminate H7.
inversion_clear H5.
inversion_clear H6.
discriminate H7.
inversion_clear H6.
inversion_clear H5.
discriminate H7.
inversion_clear H5.
generalize (inP_inj1 H7); intro X; inversion_clear X.
generalize c0 H1 x x0 H6 H7; clear c0 H1 x x0 H6 H7; rewrite <-H5; rewrite <-H8; clear H5 H8 A0 b0; intros.
generalize (inP_inj_chan H7); intro.
generalize H1 H6 H7; clear H1 H6 H7; elim H5; clear H5 c0; intros.
clear H7 x0.
rewrite H6 in H1.
inversion_clear H0.
rewrite <-H3 in H7; simpl in H7.
generalize (cong_respects_trans2_pair_outP_inP H1 H7); intro X; inversion_clear X.
inversion_clear H0.
inversion_clear H8.
left.
exists ((fstT P')#x0).
split.
rewrite <-H5; induction P'.
rewrite H5; simpl.
apply red_pairL with (S:=S) (c:=c).
rewrite H6; auto.
rewrite <-H5; rewrite <-H3; simpl.
split.
auto.
auto.
inversion_clear H0.
left.
exists ((fstT P')#x0).
split.
rewrite <-H5; induction P'.
rewrite H5; simpl.
apply red_pairR with (S:=S) (c:=c).
rewrite H6; auto.
rewrite <-H5; rewrite <-H3; simpl.
split.
auto.
auto.
inversion_clear H8.
right.
exists ((fstT P')#x0).
split.
rewrite <-H5; induction P'.
rewrite H5; simpl.
apply red_pairL with (S:=S) (c:=c).
rewrite H6; auto.
rewrite <-H5; rewrite <-H3; simpl.
split.
auto.
auto.
right.
exists ((fstT P')#x0).
split.
rewrite <-H5; induction P'.
rewrite H5; simpl.
apply red_pairR with (S:=S) (c:=c).
rewrite H6; auto.
rewrite <-H5; rewrite <-H3; simpl.
split.
auto.
auto.
Qed.

Unset Implicit Arguments.

