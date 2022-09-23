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

  Lemma prop_not_or (P Q: Prop) : ~(P ∨ Q) ↔ (~P) ∧ (~Q).
  Proof.
    tauto.
  Qed.

  Lemma prop_not_and (P Q: Prop) : ~(P ∧ Q) ↔ (~P) ∨ (~Q).
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

Declare Scope tla.
Delimit Scope tla with L.

Definition valid p := ∀ e, p e.
Notation "⊢  p" := (valid p%L) (at level 99, p at level 200).

Definition tla_not p : predicate := λ e, ¬ p e.
Notation "!  p" := (tla_not p%L) (at level 51, right associativity) : tla.

Definition tla_or p1 p2 : predicate := λ e, p1 e ∨ p2 e.
Notation "p  ∨  q" := (tla_or p%L q%L) : tla.

Definition tla_and p1 p2 : predicate := λ e, p1 e ∧ p2 e.
Notation "p  ∧  q" := (tla_and p%L q%L) : tla.

Definition tla_implies p1 p2 : predicate := λ e, p1 e → p2 e.
Notation "p  →  q" := (tla_implies p%L q%L) : tla.
Notation "p  ->  q" := (tla_implies p%L q%L) : tla.

Definition drop k e : exec := λ n, e (n + k).

Lemma drop_drop k1 k2 e : drop k1 (drop k2 e) = drop (k1 + k2) e.
Proof.
  extensionality n.  rewrite /drop.
  f_equal; lia.
Qed.

Lemma drop_0 e : drop 0 e = e.
Proof.
  extensionality n. rewrite /drop.
  f_equal; lia.
Qed.

Definition always p : predicate := λ e, ∀ k, p (drop k e).
Notation "□  p" := (always p%L) (at level 51, right associativity) : tla .

Definition eventually p : predicate := λ e, ∃ k, p (drop k e).
Notation "◇  p" := (eventually p%L) (at level 51, right associativity) : tla .

(* this is just to force parsing in tla scope *)
Notation "p == q" := (@eq predicate p%L q%L) (at level 70, only parsing).

Theorem eventually_to_always p :
  ◇ p == ! (□ (! p)).
Proof.
  apply predicate_ext => e; rewrite /eventually /always /tla_not.
  rewrite -not_forall.
  setoid_rewrite double_negation.
  reflexivity.
Qed.

Theorem always_to_eventually p :
  □ p == ! (◇ (! p)).
Proof.
  apply predicate_ext => e; rewrite /eventually /always /tla_not.
  rewrite <- not_exists.
  setoid_rewrite double_negation.
  reflexivity.
Qed.

Lemma not_not p :
  (! ! p) == p.
Proof.
  apply predicate_ext => e; rewrite /tla_not.
  rewrite double_negation //.
Qed.

Lemma not_inj p q :
  !p == !q →
  p = q.
Proof.
  intros.
  rewrite  -(not_not p) -(not_not q).
  rewrite H //.
Qed.

Theorem not_eventually p :
  ! ◇p == □ !p.
Proof.
  rewrite eventually_to_always not_not //.
Qed.

Theorem not_always p :
  ! □p == ◇ !p.
Proof.
  rewrite eventually_to_always not_not //.
Qed.

Lemma not_or p1 p2 :
  !(p1 ∨ p2) == (!p1 ∧ !p2).
Proof.
  apply predicate_ext => e; rewrite /tla_or /tla_and /tla_not /=.
  tauto.
Qed.

Lemma not_and p1 p2 :
  !(p1 ∧ p2) == (!p1 ∨ !p2).
Proof.
  apply predicate_ext => e; rewrite /tla_or /tla_and /tla_not /=.
  tauto.
Qed.

Lemma implies_to_or p1 p2 :
  (p1 → p2) == (!p1 ∨ p2).
Proof.
  apply predicate_ext => e; rewrite /tla_implies /tla_or /tla_not /=.
  tauto.
Qed.

Lemma not_implies p1 p2 :
  !(p1 → p2) == (p1 ∧ !p2).
Proof.
  rewrite implies_to_or.
  rewrite not_or not_not //.
Qed.

Ltac dual0 :=
  apply not_inj;
  repeat first [
    rewrite !not_eventually |
    rewrite !not_always |
    rewrite !not_and |
    rewrite !not_or |
    rewrite !not_not |
    rewrite !not_implies
  ].

Tactic Notation "dual" := dual0.
Tactic Notation "dual" constr(lem) := dual0; rewrite lem; done.

Theorem always_idem p :
  □ □ p == □ p.
Proof.
  apply predicate_ext => e; rewrite /always.
  split.
  - intros H k.
    specialize (H 0 k).
    rewrite drop_0 // in H.
  - intros H k k'.
    rewrite drop_drop.
    eauto.
Qed.

Theorem eventually_idem p :
  ◇ ◇ p == ◇ p.
Proof.
  dual always_idem.
Qed.

Theorem always_intro p :
  (⊢ p) ↔ ⊢ □ p.
Proof.
  rewrite /valid /always.
  split; intros H e; eauto.
  specialize (H e 0).
  rewrite drop_0 // in H.
Qed.

Theorem always_and p1 p2 :
  □(p1 ∧ p2) == (□p1 ∧ □ p2).
Proof.
  apply predicate_ext => e; rewrite /always /tla_and.
  intuition eauto.
  - destruct (H k); auto.
  - destruct (H k); auto.
Qed.

Theorem eventually_or p1 p2 :
  ◇(p1 ∨ p2) == (◇p1 ∨ ◇ p2).
Proof.
  dual always_and.
Qed.

Theorem always_eventually_distrib p1 p2 :
  □◇ (p1 ∨ p2) == ((□◇ p1) ∨ (□◇ p2)).
Proof.
  apply predicate_ext => e; rewrite /always /eventually /tla_or.
  setoid_rewrite drop_drop.
  split.
  - intros H.
    apply NNPP.
    intros H1.
    apply prop_not_or in H1.
    rewrite -!not_forall in H1.
    setoid_rewrite <- not_exists in H1.
    destruct H1 as [[x1 Hnot1] [x2 Hnot2]].
    destruct (H (Nat.max x1 x2)) as [k H1or2].
    destruct H1or2 as [H1|H2].
    { apply (Hnot1 (k + Nat.max x1 x2 - x1)).
      assert (k + Nat.max x1 x2 - x1 + x1 = k + Nat.max x1 x2) by lia.
      congruence. }
    { apply (Hnot2 (k + Nat.max x1 x2 - x2)).
      assert (k + Nat.max x1 x2 - x2 + x2 = k + Nat.max x1 x2) by lia.
      congruence. }
  - intros [H|H]; intros k.
    + destruct (H k) as [k' ?]; eauto.
    + destruct (H k) as [k' ?]; eauto.
Qed.

Lemma always_eventually_reverse p :
  □◇ p == ! ◇□ !p.
Proof.
  rewrite (eventually_to_always p).
  rewrite (always_to_eventually (! □ (! p))%L).
  rewrite not_not //.
Qed.

Lemma eventually_always_reverse p :
  ◇□ p == ! □◇ !p.
Proof.
  dual always_eventually_reverse.
Qed.

Theorem eventually_always_distrib p1 p2 :
  ◇□ (p1 ∧ p2) == ((◇□ p1) ∧ (◇□ p2)).
Proof.
  dual always_eventually_distrib.
Qed.

Theorem always_expand p :
  ⊢ □ p → (p ∧ □ p).
Proof.
  rewrite /valid => e; rewrite /always /tla_implies /tla_and.
  intros H.
  split; [ | auto ].
  specialize (H 0); rewrite drop_0 // in H.
Qed.

Definition state_pred (f: Σ → Prop) : predicate :=
    λ ex, f (ex 0).

Definition action (R: Σ → Σ → Prop) : predicate :=
    λ ex, R (ex 0) (ex 1).

End TLA.
