From TLA Require Import defs classical automation.

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

Theorem and_idem p :
  (p ∧ p) == p.
Proof.  unseal.  Qed.

Theorem or_idem p :
  (p ∨ p) == p.
Proof.  unseal.  Qed.

Theorem tla_and_assoc p1 p2 p3 :
  ((p1 ∧ p2) ∧ p3) == (p1 ∧ p2 ∧ p3).
Proof. unseal. Qed.

Theorem tla_or_assoc p1 p2 p3 :
  ((p1 ∨ p2) ∨ p3) == (p1 ∨ p2 ∨ p3).
Proof. unseal. Qed.

Hint Rewrite tla_and_assoc tla_or_assoc : tla.

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

Theorem next_and p1 p2 :
  next (p1 ∧ p2) == (next p1 ∧ next p2).
Proof.
  unseal.
Qed.

Theorem next_or p1 p2 :
  next (p1 ∨ p2) == (next p1 ∨ next p2).
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

Theorem entails_and_iff p q1 q2 :
  ((p ⊢ q1) ∧ (p ⊢ q2)) ↔ (p ⊢ q1 ∧ q2).
Proof.
  unseal.
  intuition eauto.
  - apply H; done.
  - apply H; done.
Qed.

Theorem entails_and p q1 q2 :
  (p ⊢ q1) →
  (p ⊢ q2) →
  (p ⊢ q1 ∧ q2).
Proof.
  rewrite -entails_and_iff //.
Qed.

Theorem always_weaken p :
  □ p ⊢ p.
Proof.
  unseal.
  specialize (H 0).
  rewrite drop_0 // in H.
Qed.

Theorem always_to_next p :
  □ p ⊢ next p.
Proof.
  unseal.
Qed.

Theorem next_to_eventually p :
  next p ⊢ ◇ p.
Proof.
  unseal.
Qed.

Theorem always_expand p :
  □ p == (p ∧ □ p).
Proof.
  rewrite -{1}(and_idem p).
  rewrite always_and.
  unseal.
  intuition eauto.
  specialize (H0 0).
  rewrite drop_0 in H0; eauto.
Qed.

Lemma add_1_succ (n: nat) : n + 1 = S n.
Proof. lia. Qed.

Theorem always_unroll p :
  □ p == (p ∧ next (□ p)).
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
  □ p == (p ∧ □(p → next p)).
Proof.
  apply equiv_to_impl.
  - unseal.
    intuition eauto.
    rewrite -(drop_0 e) //.
  - unseal.
    destruct H as [Hp Hnext] .
    generalize dependent e.
    induction k; intros; eauto.
    rewrite drop_0 //.
Qed.

Theorem next_always p :
  □ p ⊢ next (□ p).
Proof.
  rewrite -> always_unroll at 1.
  unseal.
Qed.

Theorem next_eventually p :
  (p ∨ next (◇ p)) == ◇ p.
Proof.
  unseal.
  intuition (deex; eauto).
  { exists 0; rewrite drop_0 //. }
  setoid_rewrite add_1_succ.
  destruct k; eauto.
  rewrite drop_0 in H; auto.
Qed.

Theorem next_eventually_weaken p :
  next (◇ p) ⊢ ◇ p.
Proof.
  rewrite <- next_eventually at 2.
  unseal.
Qed.

(* the induction principle from the TLA paper *)
Theorem next_induction (n inv: predicate) :
  (inv ∧ n ⊢ next inv) →
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

Theorem init_safety (init n inv safe : predicate) :
  (init ⊢ inv) →
  (inv ∧ n ⊢ next inv) →
  (inv ⊢ safe) →
  ⊢ init ∧ □ n → □ safe.
Proof.
  intros Hinit Hnext Hsafe.
  rewrite <- Hsafe.
  rewrite -> Hinit.
  apply next_induction.
  auto.
Qed.

(* This is a more general induction principle _internal_ to the logic. It's
different from `next_induction` because it requires the implication only for the
"current" execution. *)
Theorem next_induction_internal (n inv: predicate) :
  ⊢ □(inv ∧ n → next inv) → (inv ∧ □n → □inv).
Proof.
  unseal.
  destruct H0 as [Hinit Hn].
  induction k.
  - rewrite drop_0 //.
  - change (S k) with (1 + k).
    apply H; eauto.
Qed.

Theorem weak_fairness_alt1 a :
  weak_fairness a == □ ◇ (! (enabled a) ∨ □ ◇ ⟨a⟩).
Proof.
  unfold weak_fairness.
  rewrite implies_to_or.
  tla_simp.
  rewrite -!eventually_or.
  rewrite !always_eventually_distrib.
  tla_simp.
Qed.

Theorem weak_fairness_alt2 a :
  weak_fairness a == (◇ □ (enabled a) → □ ◇ ⟨a⟩).
Proof.
  rewrite weak_fairness_alt1.
  rewrite implies_to_or.
  tla_simp.
  rewrite always_eventually_distrib.
  tla_simp.
Qed.

End TLA.