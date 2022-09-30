From iris.bi Require Import interface.
From iris.proofmode Require Import tactics.

From TLA Require Import defs automation.

Section tla.

Context [Σ: Type].

Notation tlaProp := (predicate Σ).

Section ofe.
  Inductive tlaProp_equiv' (P Q : tlaProp) : Prop :=
    { tlaProp_in_equiv : ∀ σ, P σ ↔ Q σ }.
  Local Instance tlaProp_equiv : Equiv tlaProp := tlaProp_equiv'.
  Local Instance tlaProp_equivalence : Equivalence (≡@{tlaProp}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure tlaPropO := discreteO tlaProp.
End ofe.

(** logical entailement *)
Notation tlaProp_entails := pred_impl.

(** logical connectives *)
Notation tlaProp_emp := tla_true.

Local Definition tlaProp_pure_def (φ : Prop) : tlaProp := λ _, φ.
Local Definition tlaProp_pure_aux : seal (@tlaProp_pure_def). Proof. by eexists. Qed.
Definition tlaProp_pure := unseal tlaProp_pure_aux.
Local Definition tlaProp_pure_unseal :
  @tlaProp_pure = @tlaProp_pure_def := seal_eq tlaProp_pure_aux.

Notation tlaProp_and := tla_and.

Notation tlaProp_or := tla_or.

Notation tlaProp_impl := tla_implies.

Notation tlaProp_forall := tla_forall.

Notation tlaProp_exist := tla_exists.

Notation tlaProp_sep := tla_and.
Notation tlaProp_wand := tla_implies.

Definition tlaProp_persistently (P : tlaProp) : tlaProp := P.

(** Iris's [bi] class requires the presence of a later modality, but for non
step-indexed logics, it can be defined as the identity. *)
Definition tlaProp_later (P : tlaProp) : tlaProp := P.

Section mixins.
  Ltac unseal :=
    autounfold with tla;
    rewrite ?tlaProp_pure_unseal /tlaProp_pure_def /=.

  Lemma tlaProp_bi_mixin :
    BiMixin
      tlaProp_entails tlaProp_emp tlaProp_pure tlaProp_and tlaProp_or
      tlaProp_impl (@tlaProp_forall Σ) (@tlaProp_exist Σ)
      tlaProp_sep tlaProp_wand tlaProp_persistently.
  Proof.
    split.
    - (* [PreOrder tlaProp_entails] *)
      split; hnf; repeat destruct 1; unseal; naive_solver.
    - (* [P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P)] *)
      intros P Q; split.
      + intros [HPQ]; split; naive_solver.
      + intros [HPQ HQP]; split; naive_solver.
    - (* [Proper (iff ==> dist n) bi_pure] *)
      unseal=> n φ1 φ2 Hφ; split; naive_solver.
    - (* [NonExpansive2 bi_and] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_or] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_impl] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [Proper (pointwise_relation _ (dist n) ==> dist n) (bi_forall A)] *)
      unseal=> A n Φ1 Φ2 HΦ; split=> σ /=; split=> ? x; by apply HΦ.
    - (* [Proper (pointwise_relation _ (dist n) ==> dist n) (bi_exist A)] *)
      unseal=> A n Φ1 Φ2 HΦ; split=> σ /=; split=> -[x ?]; exists x; by apply HΦ.
    - (* [NonExpansive2 bi_sep] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_wand] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_persistently] *)
      unseal=> n P1 P2 [HP]; split; naive_solver.
    - (* [φ → P ⊢ ⌜ φ ⌝] *)
      unseal=> φ P ?; naive_solver.
    - (* [(φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P] *)
      unseal=> φ P HP; move=> σ ?. by apply HP.
    - (* [P ∧ Q ⊢ P] *)
      unseal=> P Q; move=> σ [??]; done.
    - (* [P ∧ Q ⊢ Q] *)
      unseal=> P Q; move=> σ [??]; done.
    - (* [(P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R] *)
      unseal=> P Q R HPQ HPR; move=> σ; split; auto.
    - (* [P ⊢ P ∨ Q] *)
      unseal=> P Q; move=> σ; by left.
    - (* [Q ⊢ P ∨ Q] *)
      unseal=> P Q; move=> σ; by right.
    - (* [(P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R] *)
      unseal=> P Q R HPQ HQR; move=> σ [?|?]; auto.
    - (* [(P ∧ Q ⊢ R) → P ⊢ Q → R] *)
      unseal=> P Q R HPQR; move=> σ ??. by apply HPQR.
    - (* [(P ⊢ Q → R) → P ∧ Q ⊢ R] *)
      unseal=> P Q R HPQR; move=> σ [??]. by apply HPQR.
    - (* [(∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a] *)
      unseal=> A P Ψ HPΨ; move=> σ ? a. by apply HPΨ.
    - (* [(∀ a, Ψ a) ⊢ Ψ a] *)
      unseal=> A Ψ a; move=> σ ?; done.
    - (* [Ψ a ⊢ ∃ a, Ψ a] *)
      unseal=> A Ψ a; move=> σ ?. by exists a.
    - (* [(∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q] *)
      unseal=> A Φ Q HΦQ; move=> σ [a ?]. by apply (HΦQ a).
    - (* [(P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'] *)
      unseal=> P P' Q Q' HPQ HP'Q'; move; naive_solver.
    - (* [P ⊢ emp ∗ P] *)
      unseal=> P; move=> σ ? /=. naive_solver.
    - (* [emp ∗ P ⊢ P] *)
      unseal=> P; move; naive_solver.
    - (* [P ∗ Q ⊢ Q ∗ P] *)
      unseal=> P Q; split; naive_solver.
    - (* [(P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)] *)
      unseal=> P Q R; split; naive_solver.
    - (* [(P ∗ Q ⊢ R) → P ⊢ Q -∗ R] *)
      unseal=> P Q R HPQR; naive_solver.
    - (* [(P ⊢ Q -∗ R) → P ∗ Q ⊢ R] *)
      unseal=> P Q R HPQR; naive_solver.
    - (* [(P ⊢ Q) → <pers> P ⊢ <pers> Q] *)
      unseal=> P Q HPQ; move=> σ. apply HPQ.
    - (* [<pers> P ⊢ <pers> <pers> P] *)
      unseal=> P; move=> σ; done.
    - (* [emp ⊢ <pers> emp] *)
      unseal; split=> σ; done.
    - (* [(∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a)] *)
      unseal=> A Ψ; move=> σ; done.
    - (* [<pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a)] *)
      unseal=> A Ψ; move=> σ; done.
    - (* [<pers> P ∗ Q ⊢ <pers> P] *)
      unseal=> P Q; move; naive_solver.
    - (* [<pers> P ∧ Q ⊢ P ∗ Q] *)
      unseal=> P Q; move=> σ [??]. naive_solver.
  Qed.

  Lemma tlaProp_bi_later_mixin :
    BiLaterMixin
      tlaProp_entails tlaProp_pure tlaProp_or tlaProp_impl
      (@tlaProp_forall Σ) (@tlaProp_exist Σ)
      tlaProp_sep tlaProp_persistently tlaProp_later.
  Proof. eapply bi_later_mixin_id; [done|apply tlaProp_bi_mixin]. Qed.
End mixins.

End tla.

Canonical Structure tlaPropI (Σ: Type) : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (predicate Σ);
     bi_bi_mixin := @tlaProp_bi_mixin Σ; bi_bi_later_mixin := @tlaProp_bi_later_mixin Σ |}.

Global Instance tlaProp_pure_forall (Σ: Type) : BiPureForall (tlaPropI Σ).
Proof.
  intros A φ. rewrite /bi_forall /bi_pure /=.
  autounfold with tla. rewrite tlaProp_pure_unseal /tlaProp_pure_def.
  eauto.
Qed.

(* every TLA predicate is persistent because this isn't a linear/affine logic *)
Global Instance tlaProp_persistent (Σ: Type) (p: predicate Σ) : Persistent p.
Proof.
  rewrite /Persistent.
  rewrite /bi_persistently //=.
Qed.

Lemma tlaProp_proofmode_test {Σ} {A} (P Q R : predicate Σ) (Φ Ψ : A → predicate Σ) :
  P ∗ Q -∗
  □ R -∗
  □ (R -∗ ∃ x, Φ x) -∗
  ∃ x, Φ x ∗ Φ x ∗ P ∗ Q.
Proof.
  iIntros "[HP HQ] #HR #HRΦ".
  iDestruct ("HRΦ" with "HR") as (x) "#HΦ".
  iExists x. iFrame. by iSplitL.
Qed.
