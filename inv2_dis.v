Lemma dis_trans2_rinP_inP' :
 forall (R : procs) (L : TrLabel) (P Q : proc),
 Trans2 R P L Q ->
 forall (A : Set) (b : bool) (x : chan A b) (C : A -> proc),
 R = Single (x ??* C) ->
 forall (A0 : Set) (b0 : bool) (c : chan A0 b0) (D : A0 -> proc),
 P = c ?? D -> False.
do 5 intro.
induction H
 as
  [A b x v P|
   A b x v C|
   A b x v C|
   A x C|
   A x C|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   Ps P P' Q L H IHTrans2|
   Ps P P' Q L H IHTrans2].
intros.
discriminate H0.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma dis_trans2_rinP_inP :
 forall (A : Set) (b : bool) (x : chan A b) (C : A -> proc) 
   (A0 : Set) (b0 : bool) (c : chan A0 b0) (D : A0 -> proc) 
   (L : TrLabel) (Q : proc), Trans2 (Single (x ??* C)) (c ?? D) L Q -> False.
intros.
inversion H.

apply
 (dis_trans2_rinP_inP' _ _ _ _ H _ _ _ _ (refl_equal (Single (x ??* C))) _ _
    _ _ (refl_equal (c ?? D))).
Qed.

Lemma dis_trans2_rinP_outP' :
 forall (L : TrLabel) (P Q : proc) (R : procs),
 Trans2 R P L Q ->
 forall (A : Set) (b : bool) (x : chan A b) (C : A -> proc),
 R = Single (x ??* C) ->
 forall (A0 : Set) (b0 : bool) (c : chan A0 b0) (v : A0) (D : proc),
 P = c << v >> D -> False.
do 5 intro.
induction H
 as
  [A b x v P|
   A b x v C|
   A b x v C|
   A x C|
   A x C|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   Ps P P' Q L H IHTrans2|
   Ps P P' Q L H IHTrans2].
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma dis_trans2_rinP_outP :
 forall (A : Set) (b : bool) (x : chan A b) (C : A -> proc) 
   (A0 : Set) (b0 : bool) (c : chan A0 b0) (v : A0) 
   (D : proc) (L : TrLabel) (Q : proc),
 Trans2 (Single (x ??* C)) (c << v >> D) L Q -> False.
intros.
apply
 (dis_trans2_rinP_outP' _ _ _ _ H _ _ _ _ (refl_equal (Single (x ??* C))) _ _
    _ _ _ (refl_equal (c << v >> D))).
Qed.

Lemma dis_trans2_rinP_nuP' :
 forall (L : TrLabel) (P Q : proc) (R : procs),
 Trans2 R P L Q ->
 forall (A : Set) (b : bool) (x : chan A b) (C : A -> proc),
 R = Single (x ??* C) ->
 forall (A0 : Set) (D : chan A0 false -> proc), P = nuP D -> False.
do 5 intro.
induction H
 as
  [A b x v P|
   A b x v C|
   A b x v C|
   A x C|
   A x C|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   Ps P P' Q L H IHTrans2|
   Ps P P' Q L H IHTrans2].
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma dis_trans2_rinP_nuP :
 forall (A : Set) (b : bool) (x : chan A b) (C : A -> proc) 
   (A0 : Set) (D : chan A0 false -> proc) (L : TrLabel) 
   (Q : proc), Trans2 (Single (x ??* C)) (nuP D) L Q -> False.
intros.
apply
 (dis_trans2_rinP_nuP' _ _ _ _ H _ _ _ _ (refl_equal (Single (x ??* C))) _ _
    (refl_equal (nuP D))).
Qed.


Lemma dis_trans2_rinP_nuPl' :
 forall (L : TrLabel) (P Q : proc) (R : procs),
 Trans2 R P L Q ->
 forall (A : Set) (b : bool) (x : chan A b) (C : A -> proc),
 R = Single (x ??* C) ->
 forall (A0 : Set) (D : chan A0 true -> proc), P = nuPl D -> False.
do 5 intro.
induction H
 as
  [A b x v P|
   A b x v C|
   A b x v C|
   A x C|
   A x C|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   Ps P P' Q L H IHTrans2|
   Ps P P' Q L H IHTrans2].
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma dis_trans2_rinP_nuPl :
 forall (A : Set) (b : bool) (x : chan A b) (C : A -> proc) 
   (A0 : Set) (D : chan A0 true -> proc) (L : TrLabel) 
   (Q : proc), Trans2 (Single (x ??* C)) (nuPl D) L Q -> False.
intros.
apply
 (dis_trans2_rinP_nuPl' _ _ _ _ H _ _ _ _ (refl_equal (Single (x ??* C))) _ _
    (refl_equal (nuPl D))).
Qed.

Lemma dis_trans2_single_tau' :
 forall (R : procs) (P Q : proc) (L : TrLabel),
 Trans2 R P L Q ->
 forall R' : proc,
 R = Single R' ->
 forall (A : Set) (b : bool) (c : chan A b), L = TauL c -> False.
do 5 intro.
induction H
 as
  [A b x v P|
   A b x v C|
   A b x v C|
   A x C|
   A x C|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   Ps P P' Q L H IHTrans2|
   Ps P P' Q L H IHTrans2].
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
auto.
auto.
Qed.

Lemma dis_trans2_single_tau :
 forall (R' P Q : proc) (A : Set) (b : bool) (c : chan A b),
 Trans2 (Single R') P (TauL c) Q -> False.
intros.
apply
 (dis_trans2_single_tau' _ _ _ _ H _ (refl_equal (Single R')) _ _ _
    (refl_equal (TauL c))).
Qed.






