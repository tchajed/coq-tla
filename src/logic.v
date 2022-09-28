From TLA Require Export defs automation.
From TLA Require Import classical.

Set Default Proof Using "Type".

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

Theorem tla_and_comm p1 p2 :
  (p1 ∧ p2) == (p2 ∧ p1).
Proof. unseal. Qed.

Theorem tla_or_comm p1 p2 :
  (p1 ∨ p2) == (p2 ∨ p1).
Proof. unseal. Qed.

Theorem tla_and_implies p1 p2 q :
  (p1 ∧ p2 → q) == (p1 → p2 → q).
Proof. unseal. Qed.

Theorem tla_and_assoc p1 p2 p3 :
  ((p1 ∧ p2) ∧ p3) == (p1 ∧ p2 ∧ p3).
Proof. unseal. Qed.

Theorem tla_or_assoc p1 p2 p3 :
  ((p1 ∨ p2) ∨ p3) == (p1 ∨ p2 ∨ p3).
Proof. unseal. Qed.

Hint Rewrite tla_and_assoc tla_or_assoc : tla.

Lemma modus_ponens (p q: predicate) :
  (p ∧ (p → q)) ⊢ q.
Proof.
  unseal.
Qed.

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

Theorem init_safety (init next inv safe : predicate) :
  (init ⊢ inv) →
  (inv ∧ next ⊢ later inv) →
  (inv ⊢ safe) →
  ⊢ init ∧ □ next → □ safe.
Proof.
  intros Hinit Hlater Hsafe.
  rewrite <- Hsafe.
  rewrite -> Hinit.
  apply later_induction.
  auto.
Qed.

Theorem init_invariant (init: Σ → Prop) (next: action Σ) (inv: Σ → Prop) :
  (∀ s, init s → inv s) →
  (∀ s s', inv s → next s s' → inv s') →
  state_pred init ∧ □ ⟨next⟩ ⊢ □ state_pred inv.
Proof.
  intros Hinit Hinv.
  eapply init_safety; [ | | reflexivity ].
  - unseal.
  - unseal.
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

Theorem weak_fairness_alt1 a :
  weak_fairness a == □ ◇ ((! (tla_enabled a)) ∨ □ ◇ ⟨a⟩).
Proof.
  unfold weak_fairness.
  rewrite implies_to_or.
  tla_simp.
  rewrite -!eventually_or.
  rewrite !always_eventually_distrib.
  tla_simp.
Qed.

Theorem weak_fairness_alt1' a :
  weak_fairness a == □ ◇ ((! (tla_enabled a)) ∨ ⟨a⟩).
Proof.
  rewrite weak_fairness_alt1.
  rewrite !always_eventually_distrib.
  tla_simp.
Qed.

Theorem weak_fairness_alt2 a :
  weak_fairness a == (◇ □ (tla_enabled a) → □ ◇ ⟨a⟩).
Proof.
  rewrite weak_fairness_alt1.
  rewrite implies_to_or.
  tla_simp.
  rewrite always_eventually_distrib.
  tla_simp.
Qed.

Lemma until_next (p q: predicate) (next: action Σ) (e: exec) :
  (∀ e, p e ∧ next (e 0) (e 1) → p (drop 1 e) ∨ q (drop 1 e)) →
  (∀ k, next (e k) (e (S k))) →
  (∀ k, p (drop k e) → (∀ k', p (drop (k' + k) e)) ∨ ∃ k', q (drop (k' + k) e)).
Proof.
  intros Hind Hnext k Hp.
  apply classical.double_negation.
  rewrite classical.not_or classical.not_forall classical.not_exists.
  intros [[k' Hnotp] Hnotq].
  apply Hnotp; clear Hnotp.
  generalize dependent e. generalize dependent k.
  induction k'.
  - intuition auto.
  - intros.
    destruct (Hind (drop k e)); eauto; swap 1 2.
    { rewrite drop_drop in H. exfalso; eapply Hnotq; apply H.  }
    rewrite drop_drop in H.
    replace (S k' + k) with (k' + S k) by lia.
    eapply IHk'; eauto.
    intros.
    replace (x + S k) with (S x + k) by lia; eauto.
Qed.

Lemma wf1 (p q: predicate) (next a: action Σ) :
  ∀ (Hpuntilq: ⊢ p ∧ ⟨next⟩ → later p ∨ later q)
    (Haq: ⊢ p ∧ ⟨next⟩ ∧ ⟨a⟩ → later q)
    (Henable: ⊢ p → tla_enabled a),
  (⊢ □ ⟨next⟩ ∧ weak_fairness a → p ~~> q).
Proof.
  rewrite weak_fairness_alt1'.
  unseal.
  destruct H as [Hnext Henabled_a].

  edestruct (until_next p q next e Hpuntilq Hnext); eauto.

  destruct (Henabled_a k) as [k' [Hnotenabled | Ha]].
  { (* impossible, we have p everywhere after k *)
    contradiction Hnotenabled.
    apply Henable; eauto. }

  exists (S k').
  change (S k' + k) with (1 + (k' + k)). rewrite -drop_drop.
  apply Haq; eauto.
Qed.

Lemma state_pred_impl (P Q: Σ -> Prop) :
  (∀ s, P s → Q s) →
  state_pred P ⊢ state_pred Q.
Proof.
  unseal.
Qed.

Lemma action_preserves_inv (P: Σ → Prop) (a: action Σ) :
    (∀ s s', P s → a s s' → P s') →
    state_pred P ∧ ⟨a⟩ ⊢ later (state_pred P).
Proof.
  unseal.
Qed.

Theorem leads_to_refl p :
  ⊢ p ~~> p.
Proof.
  unseal.
  exists 0; eauto.
Qed.

Theorem leads_to_trans (p q r: predicate) :
  p ~~> q ∧ q ~~> r ⊢ p ~~> r.
Proof.
  unseal.
  destruct H as [Hpq Hqr].
  edestruct Hpq as [k' Hq]; eauto.
  edestruct Hqr as [k'' Hr]; eauto.
  exists (k'' + k').
  replace (k'' + k' + k) with (k'' + (k' + k)) by lia; auto.
Qed.

Theorem leads_to_trans' (p q r: predicate) :
  ⊢ p ~~> q → q ~~> r → p ~~> r.
Proof.
  rewrite <- (leads_to_trans p q r).
  tla_prop.
Qed.

Theorem leads_to_apply p q :
  p ∧ p ~~> q ⊢ ◇ q.
Proof.
  rewrite /leads_to.
  rewrite -> always_weaken.
  apply modus_ponens.
Qed.

End TLA.
