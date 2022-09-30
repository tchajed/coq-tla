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
Proof.
  unseal.
  deex; intuition eauto.
Qed.

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
Proof.
  unseal.
  intuition (repeat deex; eauto).
Qed.

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

(* the induction principle from the TLA paper *)
Theorem later_induction (n inv: predicate) :
  (inv ∧ n ⊢ later inv) →
  (inv ∧ □n ⊢ □inv).
Proof.
  unseal.
  destruct H0 as [Hinit Hn].
  induction k.
  - rewrite drop_0 //.
  - change (S k) with (1 + k).
    rewrite -drop_drop.
    apply H; eauto.
Qed.

(* This is a more general induction principle _internal_ to the logic. It's
different from `later_induction` because it requires the implication only for
the "current" execution. *)
Theorem later_induction_internal (n inv: predicate) :
  ⊢ □(inv ∧ n → later inv) → (inv ∧ □n → □inv).
Proof.
  unseal.
  destruct H0 as [Hinit Hn].
  induction k.
  - rewrite drop_0 //.
  - change (S k) with (1 + k).
    apply H; eauto.
Qed.

End TLA.

Hint Rewrite always_idem eventually_idem : tla.
Hint Rewrite always_eventually_idem eventually_always_idem : tla.