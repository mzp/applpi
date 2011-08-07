 Lemma forall_not_exists :
 forall (T : Type) (p : T -> Prop),
 (forall P : T, p P) -> ~ (exists Q : T, ~ p Q).
intros.
intro.
inversion_clear H0.
apply H1.
apply H.
Qed.

Lemma not_forall_exists :
 forall (T : Type) (p : T -> Prop),
 ~ (forall P : T, p P) -> exists Q : T, ~ p Q.
intros.
apply NNPP.
intro.
apply H.
intro.
assert (p P \/ ~ p P).
apply classic.
inversion_clear H1.
auto.
assert (exists Q : T, ~ p Q).
exists P.
auto.
generalize (H0 H1); contradiction.
Qed.

Lemma not_exists_forall :
 forall (T : Type) (p : T -> Prop),
 ~ (exists Q : T, p Q) -> forall P : T, ~ p P.
intros.
intro.
apply H.
exists P.
auto.
Qed.

Lemma exists_not_forall :
 forall (T : Type) (p : T -> Prop),
 (exists Q : T, p Q) -> ~ (forall P : T, ~ p P).
intros.
intro.
inversion_clear H.
generalize (H0 x); intro.
apply H; auto.
Qed.