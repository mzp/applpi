Require Import Classical.
Require Import chan.
Require Import chanlist.
Require Import applpi.
Require Import redseq.

Axiom no_self_sender : forall A b, A <> chan A b.

Lemma in_ChanList_reds :
 forall P0 P',
 Reds P0 P' ->
 forall A b (c : chan A b),
 notinp c (sndT P0) /\ in_ChanList c (fstT P0) -> in_ChanList c (fstT P').
intros.
apply (proj2 (notinp_reds' H H0)).
Qed.

Lemma inversion_parP_inP' : forall PP PP' LL,
  (Trans PP LL PP') ->
  forall P A b (c:(chan A b)) A' b' (succ:(chan A' b')) v' P' Q A'' b'' (d:(chan A'' b'')), 
    PP=(parP P (c ?? (fun _ : A => succ << v' >> Q))) ->
    PP'=(parP P' (succ << v' >> Q)) ->
    LL=(TauL d) ->
    exists v,
      exists P1,
	exists P2,
	  (Cong P (parP (c<<v>>P1) P2)).
do 4 intro.
inversion H.
intros.
discriminate H5.
intros.
discriminate H5.
intros.
discriminate H5.
intros.
discriminate H5.
intros.
discriminate H5.
intros.
injection H5; clear H5; intros; subst P0 Q.
injection H6; clear H6; intros; subst P'0 Q'.
generalize (inv_trans_inP1 H1); intro.
subst A0.
generalize (inv_trans_inP_bool H1); intro.
subst b0.
generalize (inv_trans_inP_chan H1); intro.
subst x.
generalize (inv_trans_OutL H0); intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
exists v.
exists x.
exists x0.
apply cong_tr with (parP x0 (c << v >> x)).
auto.
ProcCong.
intros.
injection H5; clear H5; intros; subst P0 Q.
injection H6; clear H6; intros; subst P'0 Q'.
inversion H1.
intros.
injection H4; clear H4; intros; subst P0 Q.
discriminate H5.
intros.
injection H4; clear H4; intros; subst P0 P.
rewrite H6 in H0.
inversion H0.
Qed.

Lemma non_interference : forall ps,
  (isRedSeq ps) ->
  forall n L P A b (c:(chan A b)) v Q,
    (ps n) = (SomeT _ (L#(parP P (c<<v>>Q)))) ->
    (notinp c P) ->
    (in_ChanList c L) ->
    forall m, m > n ->
      forall K R, (ps m) = (SomeT _ (K#R)) ->
	exists T, 
	  (notinp c T) /\ (Reds (L#P) (K#T)) /\ R=(parP T (c<<v>>Q)).
intros until m.
induction m.
(* base case *)
intro.
inversion H3.
(* induction case *)
intro.
assert (m > n \/ m=n).
omega.
inversion_clear H4.
clear H3.
generalize (IHm H5); clear H5 IHm; intro.
intros.
generalize (ps_some_succ _ H _ _ H4 m (le_S m m (le_n m))); intro X; inversion_clear X.
induction x as [K' R'].
generalize (H3 _ _ H5); clear H3; intro X; inversion_clear X.
decompose [and] H3; clear H3.
subst R'.
generalize (ps_n_ps_Sn_red _ H _ _ H5 _ H4); intro X; inversion_clear X.
inversion H3.
subst L0 P0 K' Q0.
generalize (inv_trans_tau H11); intro.
inversion_clear H7 as [P1 X]; inversion_clear X as [P2 Y]; inversion_clear Y.
injection H7; clear H7; intros; subst P1 P2.
inversion_clear H10 as [P1' X]; inversion_clear X as [P2' Y]; inversion_clear Y.
inversion_clear H7 as [v0 X]; decompose [and] X; clear X.
inversion_clear H12.
inversion_clear H7.
inversion_clear H10 as [v0 X]; decompose [and] X; clear X.
generalize (inv_trans_outP1 H7); intros; subst A0.
generalize (inv_trans_outP_bool H7); intros; subst b0.
generalize (inv_trans_outP_chan_val H7); intro X; inversion_clear X; subst x1 v0.
assert (~(v %% c)).
intro.
generalize (jmeq_types H10); intro.
apply (no_self_sender _ _ H14).
generalize (notinp_trans_InL H6 H10 H12); intro.
inversion_clear H14.
tauto.
inversion_clear H10.
exists P1'.
split.
eapply notinp_trans_TauL with (d:=x1) (P:=x).
auto.
intuition.
split; intuition.
apply reds_i2 with (K#x).
auto.
exists (epsilon x1).
apply red_com.
intuition.
inversion_clear H7.
inversion_clear H10.
subst Q0 P0 L0 K.
inversion_clear H12.
exists P'.
split.
apply notinp_trans_NewL with (d:=x1) (P:=x); auto.
assert (in_ChanList c K').
fold (fstT (K'#x)).
apply in_ChanList_reds with (L#P).
auto.
auto.
red in H14.
auto.
split; auto.
apply reds_i2 with (K'#x); auto.
exists (New x1).
apply red_new; auto.
inversion_clear H7.
subst m.
clear IHm.
intros.
generalize (ps_n_ps_Sn_red _ H _ _ H0 _ H4); intro X; inversion_clear X.
inversion H5.
subst Q0 L P0 L0.
generalize (inv_trans_tau H9); intro X; inversion_clear X.
inversion_clear H6 as [P2 X]; inversion_clear X.
injection H6; clear H6; intros; subst x1 P2.
inversion_clear H8 as [P1' X]; inversion_clear X as [P2'].
inversion_clear H6.
inversion_clear H8 as [v0].
decompose [and] H6.
inversion_clear H11.
inversion_clear H8.
inversion_clear H6 as [v0].
inversion_clear H8.
generalize (inv_trans_outP1 H6); intros.
subst A0.
generalize (inv_trans_outP_bool H6); intros.
subst b0.
generalize (inv_trans_outP_chan_val H6); intros.
inversion_clear H8.
subst x0 v0.
inversion_clear H10.
assert (~ (v%%c)).
intro.
generalize (jmeq_types H10); intro.
apply (no_self_sender _ _ H12).
generalize (notinp_trans_InL H1 H10 H8); intro.
tauto.
inversion_clear H6.
exists P1'.
split.
eapply notinp_trans_TauL with (d:=x0) (P:=P); intuition.
split; intuition.
apply reds_i2 with (K#P).
apply reds_b.
exists (epsilon x0).
apply red_com.
auto.
inversion_clear H8.
inversion_clear H6.
subst Q0 K P0 L0.
inversion_clear H10.
exists P'.
split.
apply notinp_trans_NewL with (d:=x0) (P:=P); auto.
split; auto.
apply reds_i2 with (L#P).
apply reds_b.
exists (New x0).
apply red_new.
auto.
auto.
inversion_clear H6.
Qed.

Lemma backward'' : forall ps,
  (isRedSeq ps) ->
  forall L0 P0 (A:Set) (b:bool) (c:(chan A b)) (B:Set) (b':bool) (d:(chan B b')) w Q,
    ps O = SomeT _ (L0#(parP P0 (c ?? fun x => d << w >> Q))) ->
    (notinp d P0) /\ (in_ChanList d L0) ->
    forall n LSn PSn,
      ps (S n) = SomeT _ (LSn#(parP PSn (d << w >> Q))) ->
      (forall Ln Pn, ps n <> SomeT _ (Ln#(parP Pn (d << w >> Q)))) ->
	forall m, m <= n ->
	  exists Lm, exists Pm,
	    ps m = SomeT _ (Lm#(parP Pm (c ?? fun x => d << w >> Q))) /\ 
	    (Reds (L0#P0) (Lm#Pm)).
induction m.
(* base case *)
intros.
exists L0; exists P0.
split; auto.
apply reds_b.
(* inductive case *)
intro.
assert (m <= n).
omega.
generalize (IHm H5); clear H5 IHm; intro X; inversion_clear X as [L'' Y].
inversion_clear Y as [P'' X].
inversion_clear X.
generalize (H m); intro X; inversion_clear X.
clear H8.
generalize (H7 _ H5); clear H7; intros.
inversion_clear H7.
inversion_clear H8 as [Sm].
inversion_clear H7.
induction Sm as [LSm PSm].
inversion_clear H9.
inversion H7.
subst Q0 L'' L x P.
generalize (inv_trans_tau H12); intro X.
inversion_clear X as [P1 Y]; inversion_clear Y as [P2 X]; inversion_clear X.
injection H9; clear H9; intros; subst P1 P2.
inversion_clear H10 as [P1' Y]; inversion_clear Y as [P2' X].
inversion_clear X.
inversion_clear H9 as [v].
inversion_clear H10.
inversion_clear H11.
subst PSm.
generalize (inv_trans_inP1 H10); intro.
subst A0.
generalize (inv_trans_inP_bool H10); intro.
subst b0.
generalize (inv_trans_inP_chan H10); intro.
subst x0.
generalize (inv_trans_inP_cont H10); intro.
subst P2'.
generalize (notinp_reds' H6 H1); intro.
inversion_clear H11.
assert (notinp d P1').
generalize (notinp_trans_OutL H13 H9); intro X; decompose [and] X; clear X.
auto.
compare n (S m); intro.
subst n.
assert False.
apply (H3 LSm P1').
auto.
contradiction.
assert (n > S m).
omega.
generalize (non_interference _ H _ _ _ _ _ _ _ _ H8 H11 H14 _ H15); intro.
generalize (ps_some_succ _ H _ _ H2 n (le_S n n (le_n n))); intro.
inversion_clear H17.
induction x.
generalize (H16 _ _ H18); clear H16; intros.
inversion_clear H16.
decompose [and] H17; clear H17.
assert False.
apply (H3 a x).
subst b0.
auto.
contradiction.
inversion_clear H9.
inversion_clear H10 as [v].
inversion_clear H9.
inversion_clear H10.
inversion_clear H10.
inversion_clear H9.
subst PSm.
exists LSm.
exists P1'.
split.
auto.
apply reds_i2 with (LSm#P'').
auto.
exists (epsilon x0).
apply red_com.
auto.
inversion_clear H9.
inversion_clear H10.
subst Q0 LSm x P L''.
inversion H13.
subst PSm L1 Q0 P''.
exists (x0&L).
exists P'.
split; auto.
apply reds_i2 with (L#P).
auto.
exists (New x0).
apply red_new.
auto.
auto.
inversion_clear H14.
assert (S m <= S n).
omega.
generalize (ps_some_succ _ H _ _ H2 (S m) H7); intro.
inversion_clear H9.
rewrite H8 in H10; discriminate H10.
Qed.

Lemma inversion_parP_inP : forall A b (c:(chan A b)) A' b' (succ:(chan A' b')) v' P P' Q L L',
  (Red (L#(parP P (c??(fun x => succ<<v'>>Q)))) (L'#(parP P' (succ<<v'>>Q)))) ->
  exists v,
    exists P1,
      exists P2,
	(Cong P (parP (c<<v>>P1) P2)).
intros.
inversion_clear H.
inversion_clear H0.
eapply inversion_parP_inP' with (v':=v') (succ:=succ) (P':=P') (Q:=Q) (d:=x0).
apply H.
auto.
auto.
auto.
auto.
inversion H.
inversion H4.
Qed.

Lemma backward' : forall A' b' (succ:(chan A' b')) P L,
  (notinp succ P)/\(in_ChanList succ L) ->
  forall ps,
    (isRedSeq ps) ->
    forall A b (c:(chan A b)) v' Q,
      ps O = SomeT _ (L#(parP P (c??(fun x => succ<<v'>>Q)))) ->
      forall n L' P',
	ps n = SomeT _ (L'#(parP P' (succ<<v'>>Q))) ->
	exists m,
	  m < n /\
	  exists v,
	    exists P1,
	      exists P2,
		exists L'',
		  exists P'',
		    ps m = SomeT _ (L''#(parP P'' (c??(fun x => succ<<v'>>Q)))) /\ 
		    (Cong P'' (parP (c<<v>>P1) P2)) /\
		    (Reds (L#P) (L''#P'')).
induction n.
(* base case *)
intros.
rewrite H1 in H2.
discriminate H2.
(* inductive case *)
intros.

elim (classic (exists L'', exists P'', (ps n)=(SomeT _ (L''#(parP P'' (succ<<v'>>Q)))))).

(* case Pn = succ!() | ... *)

intro X; inversion_clear X as [L'' Y].
inversion_clear Y as [P''].
generalize (IHn _ _ H3); intro X; inversion_clear X as [m Y].
inversion_clear Y.
inversion_clear H5 as [v].
inversion_clear H6 as [P1].
inversion_clear H5 as [P2].
inversion_clear H6 as [L'''].
inversion_clear H5 as [P'''].
inversion_clear H6.
inversion_clear H7.
exists m.
split.
omega.
exists v; exists P1; exists P2; exists L'''; exists P'''; intuition.

(* case Pn =/= succ!() | ... *)

intro.

cut (forall m, m <= n -> 
  exists L'', exists P'', 
    ps m = SomeT _ (L''#(parP P'' (c??(fun _ => succ<<v'>>Q)))) /\ (Reds (L#P) (L''#P''))).
intro.

assert (n <= n).
omega.
generalize (H4 _ H5); clear H5 H4; intro.

inversion_clear H4 as [L''].
inversion_clear H5 as [P''].
inversion_clear H4.

generalize (ps_n_ps_Sn_red _ H0 _ _ H5 _ H2); intros.

generalize (inversion_parP_inP _ _ _ _ _ _ _ _ _ _ _ _ H4). 

intro X.
inversion_clear X as [v].
inversion_clear H7 as [P1].
inversion_clear H8 as [P2].
exists n; split; auto.
exists v; exists P1; exists P2; exists L''; exists P''; auto.

assert (forall (Ln : ChanList) (Pn : proc),
     ps n <> SomeT (prodT ChanList proc) (Ln # parP Pn (succ << v' >> Q))).
intros.
intro.
apply H3.
exists Ln; exists Pn; auto.

apply (backward'' _ H0 _ _ _ _ _ _ _ _ _ _ H1 H _ _ _ H2 H4).
Qed.

Lemma backward : forall A b (c:(chan A b)) A' b' (succ:(chan A' b')) v' P P' Q L L',
  (notinp succ P)/\(in_ChanList succ L) -> 
  (Reds (L#(parP P (c??(fun x => succ<<v'>>P')))) (L'#(parP Q (succ<<v'>>P')))) ->
  exists v,
    exists P1,
      exists P2,
	exists L'',
	  exists P'',
	    (Reds (L#P) (L''#P'')) /\ (Cong P'' (parP (c<<v>>P1) P2)).
intros.
generalize (reds_to_redseq _ _ H0); intros.
inversion_clear H1 as [ps X]; inversion_clear X as [n Y]; decompose [and] Y; clear Y.
generalize (backward' _ _ _ _ _ H _ H1 _ _ _ _ _ H3 _ _ _ H4); intro.
inversion_clear H2 as [m X]; inversion_clear X.
inversion_clear H5 as [v]; exists v.
inversion_clear H6 as [P1]; exists P1.
inversion_clear H5 as [P2]; exists P2.
inversion_clear H6 as [L'']; exists L''.
inversion_clear H5 as [P'']; exists P''.
intuition.
Qed.

