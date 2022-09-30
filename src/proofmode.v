From iris.bi Require Import interface.
From iris.proofmode Require Export tactics.

From TLA Require Import defs automation.

Section tla.

Context [Σ: Type].

Notation tlaProp := (predicate Σ).

Section ofe.
  Local Instance tlaProp_equiv : Equiv tlaProp := eq.
  Local Instance tlaProp_equivalence : Equivalence (≡@{tlaProp}) := _.
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
  Lemma equiv_expand (P Q: tlaProp) :
    (P ≡ Q) = (∀ n, P n ↔ Q n).
  Proof.
    change (P ≡ Q) with (P = Q).
    apply PropExtensionality.propositional_extensionality.
    split; [ by intros -> | ].
    intros. apply predicate_ext; intuition.
  Qed.

  Lemma dist_expand (P Q: tlaProp) (n: nat) :
    (P ≡{n}≡ Q) = (∀ n, P n ↔ Q n).
  Proof.
    apply equiv_expand.
  Qed.

  Ltac unseal :=
    autounfold with tla;
    rewrite /Proper /respectful /pointwise_relation;
    rewrite ?tlaProp_pure_unseal /tlaProp_pure_def /=;
    repeat setoid_rewrite equiv_expand at 1;
    repeat setoid_rewrite dist_expand at 1.

  Lemma tlaProp_bi_mixin :
    BiMixin
      tlaProp_entails tlaProp_emp tlaProp_pure tlaProp_and tlaProp_or
      tlaProp_impl (@tlaProp_forall Σ) (@tlaProp_exist Σ)
      tlaProp_sep tlaProp_wand tlaProp_persistently.
  Proof.
    split; unseal; try naive_solver.
    - split; naive_solver.
    - move=> A n Φ1 Φ2 HΦ.
      rewrite dist_expand => e.
      split => ? x; specialize (HΦ x);
        rewrite dist_expand in HΦ; naive_solver.
    - (* [P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P)] *)
      move=> A n Φ1 Φ2 HΦ.
      rewrite dist_expand => e.
      split; move => [x Hx]; specialize (HΦ x);
        rewrite dist_expand in HΦ; naive_solver.
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
