From Coq.Logic Require Import
  PropExtensionality FunctionalExtensionality
  Classical_Prop Classical_Pred_Type.
From Coq.ssr Require Import ssreflect.
From Coq Require Import Lia.

From stdpp Require Import base.

Module classical_logic.

  Lemma not_forall {A: Type} (P: A → Prop) :
    ¬ (∀ x, P x) ↔ (∃ x, ¬ P x).
  Proof.
    split.
    - apply not_all_ex_not.
    - intros [x HP] H.
      eauto.
  Qed.

  Lemma not_exists {A: Type} (P: A → Prop) :
    ¬ (∃ x, P x) ↔ (∀ x, ¬ P x).
  Proof.
    split.
    - apply not_ex_all_not.
    - intros HnotP [x HP].
      eapply HnotP; eauto.
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

Definition pred_impl (p q: predicate) :=
  ∀ e, p e → q e.

Notation "p  ⊢  q" := (pred_impl p%L q%L) (at level 100).

#[global]
Instance pred_impl_reflexive : Reflexive pred_impl.
Proof. compute; intuition auto. Qed.

Instance pred_impl_trans : Transitive pred_impl.
Proof. compute; intuition auto. Qed.

Definition tla_not p : predicate := λ e, ¬ p e.
Notation "!  p" := (tla_not p%L) (at level 51, right associativity) : tla.

Definition tla_or p1 p2 : predicate := λ e, p1 e ∨ p2 e.
Notation "p  ∨  q" := (tla_or p%L q%L) : tla.

Definition tla_and p1 p2 : predicate := λ e, p1 e ∧ p2 e.
Notation "p  ∧  q" := (tla_and p%L q%L) : tla.

Definition tla_implies p1 p2 : predicate := λ e, p1 e → p2 e.
Notation "p  →  q" := (tla_implies p%L q%L) : tla.
Notation "p  ->  q" := (tla_implies p%L q%L) : tla.

Theorem pred_impl_as_valid p q :
  (p ⊢ q) ↔ (⊢ (p → q)).
Proof. reflexivity. Qed.


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
Notation "□  p" := (always p%L) (at level 51, right associativity) : tla.

Definition eventually p : predicate := λ e, ∃ k, p (drop k e).
Notation "◇  p" := (eventually p%L) (at level 51, right associativity) : tla.

(* this is just to force parsing in tla scope *)
Notation "p == q" := (@eq predicate p%L q%L) (at level 70, only parsing).

Hint Unfold tla_and tla_or tla_not tla_implies eventually always : tla.

Local Ltac instance_t :=
  rewrite /Proper /respectful /Basics.flip /Basics.impl /pred_impl;
  autounfold with tla;
  try solve [ intuition auto ].

Global Instance implies_impl_proper :
  Proper (Basics.flip pred_impl ==> pred_impl ==> pred_impl) tla_implies.
Proof.  instance_t.  Qed.

Instance and_impl_proper :
  Proper (pred_impl ==> pred_impl ==> pred_impl) tla_and.
Proof. instance_t. Qed.

Instance and_impl_proper' p :
  Proper (pred_impl ==> pred_impl) (tla_and p).
Proof. apply and_impl_proper. reflexivity. Qed.

Instance or_impl_proper :
  Proper (pred_impl ==> pred_impl ==> pred_impl) tla_or.
Proof. instance_t. Qed.

Instance pred_impl_proper :
  Proper (Basics.flip pred_impl ==> pred_impl ==> Basics.impl) pred_impl.
Proof. instance_t. Qed.

Instance pred_flip_impl_proper :
  Proper (pred_impl ==> Basics.flip pred_impl ==> Basics.flip impl) pred_impl.
Proof. instance_t. Qed.

Ltac unseal :=
  apply predicate_ext => e;
  autounfold with tla;
  try tauto.

Theorem not_eventually p :
  ! ◇p == □ !p.
Proof.
  unseal.
  rewrite not_exists //.
Qed.

Theorem not_always p :
  ! □p == ◇ !p.
Proof.
  unseal.
  rewrite not_forall //.
Qed.

Lemma not_not p :
  (! ! p) == p.
Proof.  unseal.  Qed.

Lemma not_inj p q :
  !p == !q →
  p = q.
Proof.
  intros H.
  rewrite  -(not_not p) -(not_not q).
  rewrite H //.
Qed.

Lemma not_or p1 p2 :
  !(p1 ∨ p2) == (!p1 ∧ !p2).
Proof.  unseal.  Qed.

Lemma not_and p1 p2 :
  !(p1 ∧ p2) == (!p1 ∨ !p2).
Proof.  unseal.  Qed.

Lemma implies_to_or p1 p2 :
  (p1 → p2) == (!p1 ∨ p2).
Proof.  unseal.  Qed.

Lemma not_implies p1 p2 :
  !(p1 → p2) == (p1 ∧ !p2).
Proof.  unseal.  Qed.

Hint Rewrite not_eventually not_always
  not_and not_or not_not not_implies : tla.

Ltac dual0 :=
  apply not_inj;
  autorewrite with tla.

Tactic Notation "dual" := dual0; try reflexivity.
Tactic Notation "dual" constr(lem) := dual0; rewrite lem; done.

Theorem eventually_to_always p :
  ◇ p == ! (□ (! p)).
Proof.
  autorewrite with tla; reflexivity.
Qed.

Theorem always_to_eventually p :
  □ p == ! (◇ (! p)).
Proof.
  autorewrite with tla; reflexivity.
Qed.

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

Theorem and_idem p :
  (p ∧ p) == p.
Proof.  unseal.  Qed.

Theorem or_idem p :
  (p ∨ p) == p.
Proof.  unseal.  Qed.

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
  unseal.
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
  unseal.
  setoid_rewrite drop_drop.
  split.
  - intros H.
    apply NNPP.
    rewrite prop_not_or !not_forall.
    setoid_rewrite not_exists.
    intros H1.
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

Theorem eventually_always_distrib p1 p2 :
  ◇□ (p1 ∧ p2) == ((◇□ p1) ∧ (◇□ p2)).
Proof.
  dual always_eventually_distrib.
Qed.

Lemma always_eventually_reverse p :
  □◇ p == ! ◇□ !p.
Proof.
  autorewrite with tla; done.
Qed.

Lemma eventually_always_reverse p :
  ◇□ p == ! □◇ !p.
Proof.
  autorewrite with tla; done.
Qed.

Theorem always_weaken p :
  □ p ⊢ p.
Proof.
  rewrite /valid => e; rewrite /always /tla_implies /=.
  intros H.
  specialize (H 0).
  rewrite drop_0 // in H.
Qed.

Theorem always_expand p :
  □ p ⊢ p ∧ □ p.
Proof.
  rewrite -{1}(and_idem p).
  rewrite always_and.
  rewrite -> always_weaken at 1.
  reflexivity.
Qed.

Definition state_pred (f: Σ → Prop) : predicate :=
    λ ex, f (ex 0).

Definition action (R: Σ → Σ → Prop) : predicate :=
    λ ex, R (ex 0) (ex 1).

End TLA.
