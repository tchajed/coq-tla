From TLA Require Export defs automation.
From TLA Require Export propositional_ltl modalities.
From TLA Require Import classical.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).
Implicit Types (n m k: nat).

Theorem tla_init_safety (inv init next safe : predicate) :
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

Theorem invariant_internal (inv next : predicate) :
   □ next ⊢ (inv → next → later inv) → inv → □ inv.
Proof.
Admitted.

Theorem init_safety (inv init: Σ → Prop) (next: action Σ) (safe : Σ → Prop) :
  (∀ s, init s → inv s) →
  (∀ s s', inv s → next s s' → inv s') →
  (∀ s, inv s → safe s) →
  ⊢ state_pred init ∧ □ ⟨next⟩ → □ (state_pred safe).
Proof.
  intros Hinit Hinv Hsafe.
  apply (tla_init_safety (state_pred inv)); unseal.
Qed.

Theorem init_invariant (init: Σ → Prop) (next: action Σ) (inv: Σ → Prop) :
  (∀ s, init s → inv s) →
  (∀ s s', inv s → next s s' → inv s') →
  state_pred init ∧ □ ⟨next⟩ ⊢ □ state_pred inv.
Proof.
  intros Hinit Hinv.
  apply (init_safety inv); auto.
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

(** This lemma is used to prove rule WF1. Loosely speaking it takes an
  assumption of the form [p ∧ ⟨next⟩ → later p ∨ later q] and turns it into a
  proof that either [p] always holds or eventually [q] holds. *)
Lemma until_next (p q: predicate) (next: action Σ) (e: exec) :
  (* induction-like hypothesis: p is preserved until q *)
  (∀ e, p e ∧ next (e 0) (e 1) →
        p (drop 1 e) ∨ q (drop 1 e)) →
  (* this is □⟨next⟩ e *)
  (∀ k, next (e k) (e (S k))) →
  (* we can prove always p or eventually q, but only after some shifted
  execution satisfying [p] as a base case for the induction *)
  ∀ k, p (drop k e) →
       (∀ k', p (drop (k' + k) e)) ∨
       (∃ k', q (drop (k' + k) e)).
Proof.
  intros Hind Hnext k Hp.

(*|
This proof is highly classical - we immediately appeal to a double negation
to deal with this disjunction.
|*)

  apply classical.double_negation.
  rewrite classical.not_or classical.not_forall classical.not_exists.
  intros [[k' Hnotp] Hnotq].

(*|
Classical reasoning gives a *specific* k' with `¬p` and `□ ¬q`. It turns out
we'll always derive a contradiction from the `¬p`, by induction on the k'. This
is what makes the proof so classical, this k' sort of comes out of nowhere.
|*)

  apply Hnotp; clear Hnotp. (* .unfold *)
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

(** WF1 exploits a weak fairness assumption to show a leads_to. This is the
general rule as presented in the paper. [wf1] below specializes it to the
situation where p and q are simple state predicates. *)
Lemma tla_wf1 (p q: predicate) (next a: action Σ) :
  ∀ (Hpuntilq: ⊢ p ∧ ⟨next⟩ → later p ∨ later q)
    (Haq: ⊢ p ∧ ⟨next⟩ ∧ ⟨a⟩ → later q)
    (Henable: ⊢ p → tla_enabled a),
  (⊢ □ ⟨next⟩ ∧ weak_fairness a → p ~~> q).
Proof.
  rewrite weak_fairness_alt1'.
  unseal.
  destruct H as [Hnext Hwf_alt].

  (* [until_next] produces three goals. The first is simply the proof of [p
  (drop k e)] which is needed as a starting point. Then it leaves two
  possibilities: either [p] always holds, or [◇ q] (loosely speaking). The
  latter case is exactly the goal so it goes through immediately. *)
  edestruct (until_next p q next e Hpuntilq Hnext); [ eassumption | | by auto ].

  (* in the former case we'll show that weak fairness gives us either that [a]
  is never enabled (false, because p implies it is enabled), or that [a]
  executes at some point, at which point [Haq] easily gives us [q].  *)

  destruct (Hwf_alt k) as [k' [Hnotenabled | Ha]].
  { (* impossible, we have p everywhere after k *)
    contradiction Hnotenabled.
    apply Henable; eauto. }

  exists (S k').
  change (S k' + k) with (1 + (k' + k)). rewrite -drop_drop.
  apply Haq; eauto.
Qed.

(*|
**WF1**. This is an important rule that uses a weak fairness assumption to show
that [p ~~> q].

This has the advantage of stating all assumptions
as simple quantified statements, without temporal logic.

Intuitively [wf1] is used to prove [p ~~> q] from the weak fairness of some
action [a]. The second premise establishes the intuition that [a] which has
"precondition" [p] and "postcondition" [q]: if [a] runs in a state satisfying
[p], then [q] holds. The first premise says that [p] is preserved by [⟨next⟩],
or [q] just magically becomes true, in which case [a] need not run and [p ~~> q]
can still be true. (This is important because [q] might actually disable the
action from running again.) The third premise says that [p] enables [a], so
preserving it also preserves that the action is enabled.

[p] is separate from [enabled a] in order to accomplish two things. First, it
allows to strengthen the inductive hypothesis to show [Hpuntilq]. Second, it
gives a stronger premise for [Haq], allowing to use some state-specific fact to
establish a more specific postcondition [q] than [a] might have in general.
|*)

Lemma wf1 (p q: Σ → Prop) (next a: action Σ) :
  ∀ (Hpuntilq: ∀ s s', p s → next s s' → p s' ∨ q s')
    (Haq: ∀ s s', p s → next s s' → a s s' → q s')
    (Henable: ∀ s, p s → enabled a s),
  (⊢ □ ⟨next⟩ ∧ weak_fairness a → state_pred p ~~> state_pred q).
Proof.
  intros.
  apply tla_wf1; unseal.
  rewrite /tla_enabled; tla_simp.
  eauto.
Qed.

Theorem enabled_or a1 a2 :
  ∀ s, enabled (λ s s', a1 s s' ∨ a2 s s') s ↔ (enabled a1 s ∨ enabled a2 s).
Proof.
  unfold enabled.
  intuition (repeat deex; eauto).
  intuition eauto.
Qed.

Theorem tla_enabled_or a1 a2 :
  tla_enabled (λ s s', a1 s s' ∨ a2 s s')%type ==
  (tla_enabled a1 ∨ tla_enabled a2).
Proof.
  apply predicate_ext => e.
  rewrite /tla_enabled; tla_simp.
  rewrite enabled_or; tla_simp.
Qed.

(* there doesn't seem to be any characterization of weak_fairness of a composite
action - it's just different to be able to run a1 ∨ a2 compared with fairness of
each individually (intuitively the latter seems stronger, but it doesn't seem to
be an implication, either) *)
Theorem wf_or a1 a2 :
  weak_fairness (λ s s', a1 s s' ∨ a2 s s')%type ==
  (weak_fairness a1 ∧ weak_fairness a2).
Proof.
  rewrite !weak_fairness_alt1'.
  rewrite tla_enabled_or.
  rewrite !always_eventually_distrib.
  fold (⟨ a1 ⟩)%L (⟨ a2 ⟩)%L.
  tla_simp.
Abort.

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

Theorem and_leads_to_elim p q :
  p ∧ p ~~> q ⊢ ◇ q.
Proof.
  rewrite /leads_to.
  rewrite -> always_weaken.
  apply modus_ponens.
Qed.

Theorem leads_to_apply q p φ :
  (p ⊢ q) →
  (p ⊢ q ~~> φ) →
  (p ⊢ ◇ φ).
Proof.
  intros Hq Hleads.
  tla_pose Hq.
  tla_pose Hleads.
  rewrite -> and_leads_to_elim.
  tla_prop.
Qed.

Theorem impl_to_leads_to p q :
  (p ⊢ q) →
  ⊢ p ~~> q.
Proof.
  unseal.
  exists 0; auto.
Qed.

Instance impl_leads_to_subrelation : subrelation pred_impl (λ p q, ⊢ p ~~> q).
Proof.
  unfold subrelation.
  apply impl_to_leads_to.
Qed.

Theorem pred_leads_to (P Q: Σ → Prop) :
  (∀ s, P s → Q s) →
  ⊢ ⌜P⌝ ~~> ⌜Q⌝.
Proof.
  intros.
  apply impl_to_leads_to.
  unseal.
Qed.

Lemma enabled_eq (P: Σ → Prop) (f: Σ → Σ) s :
  enabled (λ s s', P s ∧ s' = f s) s ↔ P s.
Proof.
  rewrite /enabled.
  intuition (try deex; eauto).
  intuition.
Qed.

Theorem impl_drop_hyp p q :
  (⊢ q) →
  p ⊢ q.
Proof. unseal. Qed.

(* a very crude way to drop a hypothesis *)
Theorem impl_drop_one p q r :
  (p ⊢ q) →
  p ∧ r ⊢ q.
Proof. unseal. Qed.

Lemma leads_to_or_split p q r :
  (p ∨ q) ~~> r == ((p ~~> r) ∧ (q ~~> r)).
Proof.
  rewrite /leads_to.
  rewrite -always_and.
  f_equal.
  rewrite !implies_to_or; tla_simp.
  rewrite !tla_or_distr_r.
  reflexivity.
Qed.

Lemma leads_to_assume (q p r φ: predicate) :
  (* side condition *)
  (r ⊢ □ q) →
  (* continue proof with q in the leads_to premise *)
  (r ⊢ (p ∧ q) ~~> φ) →
  (r ⊢ p ~~> φ).
Proof.
  rewrite /leads_to.
  intros H Hleads_to.
  tla_pose H.
  rewrite -> Hleads_to.
  unseal.
Qed.

(* when proving a leads_to, it's safe to assume the postcondition isn't already
achieved (because the proof is trivial in that case) *)
Lemma leads_to_assume_not p q :
  p ~~> q == (p ∧ !q) ~~> q.
Proof.
  tla_split; [ unseal | ].
  rewrite {2}(tla_and_em q p).
  rewrite tla_and_distr_l.
  rewrite leads_to_or_split; tla_split.
  - apply impl_drop_hyp.
    apply impl_to_leads_to.
    tla_prop.
  - reflexivity.
Qed.

(* combining predicates and actions *)

Lemma combine_preds (next: Σ → Σ → Prop) (P: Σ → Prop) :
  (□ ⟨ next ⟩ ∧ □ ⌜ P ⌝) == □ ⟨ λ s s', next s s' ∧ P s ∧ P s' ⟩.
Proof.
  unseal.
  intuition eauto.
  - specialize (H k). intuition auto.
  - specialize (H k). intuition auto.
Qed.

Lemma combine_state_preds (P Q: Σ → Prop) :
  (⌜P⌝ ∧ ⌜Q⌝) == ⌜λ s, P s ∧ Q s⌝.
Proof.
  unseal.
Qed.

Lemma combine_or_preds (P Q: Σ → Prop) :
  (⌜P⌝ ∨ ⌜Q⌝) == ⌜λ s, P s ∨ Q s⌝.
Proof.
  unseal.
Qed.

Lemma combine_always_preds (P Q: Σ → Prop) :
  (□⌜P⌝ ∧ □⌜Q⌝) == □⌜λ s, P s ∧ Q s⌝.
Proof.
  rewrite -always_and.
  rewrite combine_state_preds.
  reflexivity.
Qed.

Lemma not_state_pred (P: Σ → Prop) :
  !⌜λ s, P s⌝ == ⌜λ s, ¬ P s⌝.
Proof.
  unseal.
Qed.

End TLA.

Ltac leads_to_trans q :=
  rewrite <- (leads_to_trans _ q _);
  tla_split.

Ltac leads_to_etrans :=
  erewrite <- leads_to_trans;
  tla_split.

Ltac tla_clear p :=
  rewrite -> (any_impl_true p); tla_simp.
