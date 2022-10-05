(*|
**TLA modalities**

This file has some basic results about the TLA modalities, especially relating
them to each other. For example one of the theorems with a slightly involved
proof is that `□◇ (p ∨ q) = □◇ p ∨ □◇ q`, despite the fact that □ on its own
does not distribute over ∨.

|*)
From TLA Require Import defs automation.
From TLA Require Import classical.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).
Implicit Types (n m k: nat).

Theorem eventually_to_always p :
  ◇ p == ! (□ (! p)).
Proof.
  tla_simp.
Qed.

Theorem always_to_eventually p :
  □ p == ! (◇ (! p)).
Proof.
  tla_simp.
Qed.

Theorem always_idem p :
  □ □ p == □ p.
Proof.
  unseal.
  split.
  - intros H k.
    specialize (H k 0).
    rewrite //= in H.
  - intuition auto.
Qed.

Theorem eventually_idem p :
  ◇ ◇ p == ◇ p.
Proof.
  dual always_idem.
Qed.

Hint Rewrite always_idem eventually_idem : tla.

Theorem always_intro p :
  (⊢ p) ↔ ⊢ □ p.
Proof.
  unseal.
  split; intros H e; [ by eauto | ].
  specialize (H e 0).
  rewrite drop_0 // in H.
Qed.

Theorem implies_generalize p1 p2 :
  (⊢ p1 → p2) → (⊢ □ p1 → □ p2).
Proof.
  unfold valid; autounfold with tla.
  eauto.
Qed.

Theorem impl_under_always p1 p2 :
  (p1 ⊢ p2) → (□ p1 ⊢ □ p2).
Proof.
  apply implies_generalize.
Qed.

Theorem always_intro_impl p q :
  (□p ⊢ q) → (□p ⊢ □ q).
Proof.
  intros H. apply impl_under_always in H.
  rewrite <- H.
  rewrite always_idem //.
Qed.

Theorem always_and p1 p2 :
  □(p1 ∧ p2) == (□p1 ∧ □ p2).
Proof.
  unseal.
  intuition eauto.
  - destruct (H k); auto.
  - destruct (H k); auto.
Qed.

Theorem later_and p1 p2 :
  later (p1 ∧ p2) == (later p1 ∧ later p2).
Proof.
  unseal.
Qed.

Theorem later_or p1 p2 :
  later (p1 ∨ p2) == (later p1 ∨ later p2).
Proof.
  unseal.
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
  split.
  - intros H.
    apply classical.double_negation.
    rewrite classical.not_or !classical.not_forall.
    setoid_rewrite classical.not_exists.
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

Theorem eventually_and p1 p2 :
  ◇ (p1 ∧ p2) ⊢ ◇ p1 ∧ ◇ p2.
Proof. unseal. Qed.

(* this is a weakening; the left side says they happen at the same time, while
the right allows them to happen only separately *)
Theorem always_eventually_and p1 p2 :
  □◇ (p1 ∧ p2) ⊢ □◇ p1 ∧ □◇ p2.
Proof.
  rewrite -> eventually_and.
  rewrite always_and //.
Qed.

Theorem eventually_always_distrib p1 p2 :
  ◇□ (p1 ∧ p2) == ((◇□ p1) ∧ (◇□ p2)).
Proof.
  dual always_eventually_distrib.
Qed.

Theorem always_or p1 p2 :
  □ p1 ∨ □ p2 ⊢ □ (p1 ∨ p2).
Proof.
  dual eventually_and.
Qed.

Theorem eventually_always_or p1 p2 :
  ◇□ p1 ∨ ◇□ p2 ⊢ ◇□ (p1 ∨ p2).
Proof.
  dual always_eventually_and.
Qed.

Lemma always_eventually_reverse p :
  □◇ p == ! ◇□ !p.
Proof.
  tla_simp.
Qed.

Lemma eventually_always_reverse p :
  ◇□ p == ! □◇ !p.
Proof.
  tla_simp.
Qed.

Theorem always_eventually_idem p :
  □ ◇ □ ◇ p == □ ◇ p.
Proof.
  unseal.
  repeat setoid_rewrite drop_drop.
  split.
  - intros H k.
    specialize (H k).
    destruct H as [k' H].
    specialize (H 0).
    destruct H as [k'' H].
    eauto.
  - intros H k.
    exists 0. intros k'.
    destruct (H (k + k')) as [k'' H'].
    exists k''.
    replace (k'' + k' + 0 + k) with (k'' + (k + k')) by lia.
    done.
Qed.

Theorem eventually_always_idem p :
  ◇ □ ◇ □ p == ◇ □ p.
Proof.
  dual always_eventually_idem.
Qed.

Hint Rewrite always_eventually_idem eventually_always_idem : tla.

Theorem always_weaken p :
  □ p ⊢ p.
Proof.
  unseal.
  specialize (H 0).
  rewrite drop_0 // in H.
Qed.

Theorem always_weaken_eventually p :
  □ p ⊢ ◇ p.
Proof.
  autounfold with tla.
  intros e H.
  exists 0; eauto.
Qed.

Theorem always_and_eventually p q :
  □ p ∧ ◇ q ⊢ ◇ (p ∧ q).
Proof. unseal. Qed.

Theorem always_to_later p :
  □ p ⊢ later p.
Proof.
  unseal.
Qed.

Theorem later_to_eventually p :
  later p ⊢ ◇ p.
Proof.
  unseal.
Qed.

Theorem always_expand p :
  □ p == (p ∧ □ p).
Proof.
  tla_split; [ | tla_prop ].
  - tla_split; [ | tla_prop ].
    apply always_weaken.
Qed.

Lemma add_1_succ (n: nat) : n + 1 = S n.
Proof. lia. Qed.

Theorem always_unroll p :
  □ p == (p ∧ later (□ p)).
Proof.
  apply equiv_to_impl; unseal.
  { intuition eauto.
    rewrite -(drop_0 e) //. }
  intuition eauto.
  setoid_rewrite add_1_succ in H1.
  destruct k.
  { rewrite drop_0 //. }
  { eauto. }
Qed.

Theorem always_induction p :
  □ p == (p ∧ □(p → later p)).
Proof.
  apply equiv_to_impl.
  - unseal.
    intuition eauto.
    rewrite -(drop_0 e) //.
  - unseal.
    destruct H as [Hp Hlater] .
    generalize dependent e.
    induction k; intros; eauto.
    rewrite drop_0 //.
Qed.

Theorem later_always p :
  □ p ⊢ later (□ p).
Proof.
  rewrite -> always_unroll at 1.
  unseal.
Qed.

Theorem later_eventually p :
  (p ∨ later (◇ p)) == ◇ p.
Proof.
  unseal.
  intuition (deex; eauto).
  { exists 0; rewrite drop_0 //. }
  setoid_rewrite add_1_succ.
  destruct k; eauto.
  rewrite drop_0 in H; auto.
Qed.

Theorem later_eventually_weaken p :
  later (◇ p) ⊢ ◇ p.
Proof.
  rewrite <- later_eventually at 2.
  unseal.
Qed.

Theorem always_eventually_always (p: predicate) :
  □◇□ p == ◇□ p.
Proof.
  tla_split.
  - apply always_weaken.
  - unseal.
    destruct H as [k' Hp].
    exists k'. intros k''.
    replace (k'' + k' + k) with ((k'' + k) + k') by lia.
    eauto.
Qed.

Theorem eventually_always_eventually (p: predicate) :
  ◇□◇ p == □◇ p.
Proof.
  dual always_eventually_always.
Qed.

Theorem leads_to_weaken (p1 p2 q1 q2: predicate) :
  (p2 ⊢ p1) →
  (q1 ⊢ q2) →
  p1 ~~> q1 ⊢ p2 ~~> q2.
Proof.
  intros H1 H2.
  rewrite /leads_to.
  rewrite -> H1. rewrite <- H2.
  reflexivity.
Qed.

Theorem leads_to_or_left (Γ p q1 q2: predicate) :
  (Γ ⊢ p ~~> q1) →
  (Γ ⊢ p ~~> (q1 ∨ q2)).
Proof.
  intros H.
  rewrite -> H.
  apply leads_to_weaken; [ done | tla_prop ].
Qed.

Theorem leads_to_or_right (Γ p q1 q2: predicate) :
  (Γ ⊢ p ~~> q2) →
  (Γ ⊢ p ~~> (q1 ∨ q2)).
Proof.
  intros H.
  rewrite -> H.
  apply leads_to_weaken; [ done | tla_prop ].
Qed.

(*|

---------------------------------
Characterization of modalities
---------------------------------

Modalities can be composed. Here we show that □ and ◇ only give rise to 4
distinct modalities.

|*)

(*|
For simplicity we represent a chain of modalities `□ (◇ (◇ (□ ...)) p)` by
interpreting a list of booleans, where true is □ and false is ◇. Yes, we could
do something cleaner.
|*)
Fixpoint modality_chain (l: list bool) (p: predicate) : predicate :=
  match l with
  | nil => p
  | true :: l => □ (modality_chain l p)
  | false :: l => ◇ (modality_chain l p)
  end.

Example modality_chain_ex (p: predicate) :
  modality_chain [true; false; false; true] p = (□ (◇ (◇ (□ p))))%L.
Proof. reflexivity. Qed.

Hint Rewrite always_idem eventually_idem : tla.
Hint Rewrite always_eventually_idem eventually_always_idem : tla.
Hint Rewrite always_eventually_always eventually_always_eventually : tla.

Theorem modality_chain_reduces (l: list bool) (p: predicate) :
  (modality_chain l p == p) ∨
  (modality_chain l p == ◇ p) ∨
  (modality_chain l p == □ p) ∨
  (modality_chain l p == ◇□ p) ∨
  (modality_chain l p == □◇ p).
Proof.
  induction l; simpl.
  - eauto.
  - destruct a; simpl.
    + destruct IHl as [-> | [-> | [-> | [-> | ->]]]]; tla_simp; eauto.
    + destruct IHl as [-> | [-> | [-> | [-> | ->]]]]; tla_simp; eauto.
Qed.

End TLA.

Hint Rewrite always_idem eventually_idem : tla.
Hint Rewrite always_eventually_idem eventually_always_idem : tla.
Hint Rewrite always_eventually_always eventually_always_eventually : tla.
