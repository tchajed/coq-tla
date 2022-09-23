From Coq.Logic Require Import
  PropExtensionality FunctionalExtensionality
  Classical_Prop Classical_Pred_Type.
From Coq.ssr Require Import ssreflect.
From Coq Require Import Lia.

From stdpp Require Import base.

Module classical_logic.

  Lemma not_forall {A: Type} (P: A → Prop) :
    (∃ x, ¬ P x) ↔ ¬ (∀ x, P x).
  Proof.
    split.
    - intros [x HP] H.
      eauto.
    - apply not_all_ex_not.
  Qed.

  Lemma not_exists {A: Type} (P: A → Prop) :
    (∀ x, ¬ P x) ↔ ¬ (∃ x, P x).
  Proof.
    split.
    - intros HnotP [x HP].
      eapply HnotP; eauto.
    - apply not_ex_all_not.
  Qed.

  Lemma double_negation (P: Prop) : (~~P) ↔ P.
  Proof.
    tauto.
  Qed.

End classical_logic.

Import classical_logic.

Section TLA.

Context {Σ: Type}.

Definition exec := nat → Σ.
Definition predicate := exec → Prop.

Implicit Types (e: exec) (p q: predicate).
Implicit Types (n m k: nat).

Lemma predicate_ext p1 p2 : (∀ e, p1 e ↔ p2 e) → p1 = p2.
Proof.
  intros H.  extensionality e.  apply propositional_extensionality.
  auto.
Qed.

Delimit Scope tla with L.

Definition valid p := ∀ e, p e.
Notation "⊢  p" := (valid p%L) (at level 99, p at level 200).

Definition tla_not p : predicate := λ e, ¬ p e.
Notation "¬  p" := (tla_not p%L) : tla.

Definition tla_or p1 p2 : predicate := λ e, p1 e ∨ p2 e.
Notation "p  ∨  q" := (tla_or p%L q%L) : tla.

Definition tla_and p1 p2 : predicate := λ e, p1 e ∧ p2 e.
Notation "p  ∧  q" := (tla_and p%L q%L) : tla.

Definition tla_implies p1 p2 : predicate := λ e, p1 e → p2 e.
Notation "p  →  q" := (tla_implies p%L q%L) : tla.
Notation "p  ->  q" := (tla_implies p%L q%L) : tla.

Definition cut k e : exec := λ n, e (n + k).

Lemma cut_cut k1 k2 e : cut k1 (cut k2 e) = cut (k1 + k2) e.
Proof.
  extensionality n.  rewrite /cut.
  f_equal; lia.
Qed.

Lemma cut_0 e : cut 0 e = e.
Proof.
  extensionality n. rewrite /cut.
  f_equal; lia.
Qed.

Definition always p : predicate := λ e, ∀ k, p (cut k e).
Notation "□  p" := (always p%L) (at level 50, left associativity) : tla .

Definition eventually p : predicate := λ e, ∃ k, p (cut k e).
Notation "◇  p" := (eventually p%L) (at level 50, left associativity) : tla .

Theorem eventually_to_always p :
  (◇ p = ¬ (□ (¬ p)))%L.
Proof.
  apply predicate_ext => e; rewrite /eventually /always /tla_not.
  rewrite -not_forall.
  setoid_rewrite double_negation.
  reflexivity.
Qed.

Theorem always_to_eventually p :
  (□ p = ¬ (◇ (¬ p)))%L.
Proof.
  apply predicate_ext => e; rewrite /eventually /always /tla_not.
  rewrite <- not_exists.
  setoid_rewrite double_negation.
  reflexivity.
Qed.

Lemma not_not p :
  (¬ ¬ p)%L = p.
Proof.
  apply predicate_ext => e; rewrite /tla_not.
  rewrite double_negation //.
Qed.

Lemma not_inj p q :
  (¬ p)%L = (¬ q)%L →
  p = q.
Proof.
  intros.
  rewrite  -(not_not p) -(not_not q).
  rewrite H //.
Qed.

Theorem not_eventually p :
  (¬ ◇ p)%L = (□ ¬ p)%L.
Proof.
  rewrite eventually_to_always not_not //.
Qed.

Theorem not_always p :
  (¬ □ p)%L = (◇ ¬ p)%L.
Proof.
  rewrite eventually_to_always not_not //.
Qed.

End TLA.
