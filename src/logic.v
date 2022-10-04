From TLA Require Export defs automation.
From TLA Require Export propositional_ltl modalities.
From TLA Require Import classical.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).
Implicit Types (n m k: nat).

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

Lemma combine_or_actions (a1 a2: action Σ) :
  (⟨a1⟩ ∨ ⟨a2⟩) == ⟨λ s s', a1 s s' ∨ a2 s s'⟩.
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

Lemma not_wf (a: action Σ) :
  ! weak_fairness a == (◇ (□ tla_enabled a ∧ ! ◇ ⟨a⟩)).
Proof.
  rewrite /weak_fairness; tla_simp.
Qed.

Lemma not_wf' (a: action Σ) :
  ! weak_fairness a == (◇ (□ (tla_enabled a ∧ !⟨a⟩))).
Proof.
  rewrite /weak_fairness; tla_simp.
  rewrite always_and //.
Qed.

Lemma always_eventually_impl p q :
  (p ⊢ q) →
  (□◇ p ⊢ □◇ q).
Proof.
  intros H.
  apply always_impl_proper.
  apply eventually_impl_proper.
  auto.
Qed.

Lemma eventually_always_impl p q :
  (p ⊢ q) →
  (◇□ p ⊢ ◇□ q).
Proof.
  intros H.
  apply eventually_impl_proper.
  apply always_impl_proper.
  auto.
Qed.

Lemma action_to_enabled a :
  ⟨a⟩ ⊢ tla_enabled a.
Proof.
  rewrite /tla_enabled /enabled.
  unseal.
Qed.

Lemma not_enabled_to_action a :
  !tla_enabled a ⊢ !⟨a⟩.
Proof.
  apply not_impl. tla_simp.
  apply action_to_enabled.
Qed.

Lemma or_apply_not r q p :
  (p ⊢ □ r ∨ ◇q) →
  p ∧ □ !q ⊢ □ r.
Proof.
  intros Hdr.
  rewrite -> Hdr; clear Hdr.
  intros e H.
  unseal.
  destruct H as [Hp Hnota].
  destruct Hp as [Hp | Ha].
  - pose proof (Hp 0) as Hp0; rewrite drop_0 in Hp0; auto.
  - destruct Ha as [k' Ha].
    exfalso; eapply Hnota; eauto.
Qed.

Lemma or_apply_not' r q p :
  (p ⊢ □ r ∨ ◇q) →
  □ p ∧ □ !q ⊢ □ r.
Proof.
  intros Hdr.
  rewrite -> (always_weaken p).
  apply or_apply_not; auto.
Qed.

Lemma or_implies_split p q r :
  (p ⊢ r) →
  (q ⊢ r) →
  (p ∨ q ⊢ r).
Proof.
  unseal.
Qed.

Lemma wf_combine_impl (a b: action Σ) :
  (tla_enabled a ⊢ □ !tla_enabled b ∨ ◇ ⟨a⟩) →
  (tla_enabled b ⊢ □ !tla_enabled a ∨ ◇ ⟨b⟩) →
  ◇ □ (tla_enabled a ∧ ! ⟨a⟩) ∨ ◇ □ (tla_enabled b ∧ ! ⟨b⟩) ⊢
  ◇ □ ((tla_enabled a ∨ tla_enabled b) ∧ ! ⟨a⟩ ∧ ! ⟨b⟩).
Proof.
  intros Hdr1 Hdr2.
  apply or_implies_split; apply eventually_impl_proper; rewrite always_and.
  + tla_pose (or_apply_not' _ _ _ Hdr1).
    rewrite -> not_enabled_to_action.

    (* TODO: why does tla_prop not work here? *)
    unseal.
  + tla_pose (or_apply_not' _ _ _ Hdr2).
    rewrite -> not_enabled_to_action.

    unseal.
Qed.

(* for some reason this direction of [wf_combine] seems more difficult and
unstructured *)
Lemma wf_split_impl (a b: action Σ) :
  (tla_enabled a ⊢ □ !tla_enabled b ∨ ◇ ⟨a⟩) →
  (tla_enabled b ⊢ □ !tla_enabled a ∨ ◇ ⟨b⟩) →
  ◇ □ ((tla_enabled a ∨ tla_enabled b) ∧ ! ⟨a⟩ ∧ ! ⟨b⟩) ⊢
  ◇ □ (tla_enabled a ∧ ! ⟨a⟩) ∨ ◇ □ (tla_enabled b ∧ ! ⟨b⟩).
Proof.
  intros Hdr1 Hdr2.
  intros e H.
  destruct H as [k H'].
  rewrite !always_and in H'. destruct H' as (Hab & Hnota & Hnotb).
  pose proof (Hab 0) as Hab0;
    rewrite drop_0 in Hab0;
    destruct Hab0 as [Ha | Hb].
  + pose proof (or_apply_not _ _ _ Hdr1 (drop k e) ltac:(unseal)).
    left.
    exists k.
    rewrite always_and.
    split; eauto.
    intros k'; setoid_rewrite drop_drop.
    destruct (Hab k') as [Ha'|Hb']; eauto.
    { exfalso; eapply H; eauto. }
  + pose proof (or_apply_not _ _ _ Hdr2 (drop k e) ltac:(unseal)).
    right.
    exists k.
    rewrite always_and.
    split; eauto.
    intros k'; setoid_rewrite drop_drop.
    destruct (Hab k') as [Ha'|Hb']; eauto.
    { exfalso; eapply H; eauto. }
Qed.

(** This theorem comes from the book "Specifying Systems", theorem 8.20. It has
a surprisingly complicated proof! *)
Theorem wf_combine (a b: action Σ) :
  (tla_enabled a ⊢ □ !tla_enabled b ∨ ◇ ⟨a⟩) →
  (tla_enabled b ⊢ □ !tla_enabled a ∨ ◇ ⟨b⟩) →
  (weak_fairness a ∧ weak_fairness b) ==
  weak_fairness (λ s s', a s s' ∨ b s s')%type.
Proof.
  intros Hdr1 Hdr2.
  apply not_inj.

  rewrite not_and.
  rewrite !not_wf'.
  rewrite -!combine_or_actions.
  rewrite tla_enabled_or.
  rewrite not_or.
  tla_split.
  - apply wf_combine_impl; auto.
  - apply wf_split_impl; auto.
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

Theorem leads_to_impl_internal p q :
  (□ (p → q)) ⊢ p ~~> q.
Proof.
  unseal.
  exists 0; simpl; eauto.
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

Lemma enabled_eq (P: Σ → Prop) (f: Σ → Σ) :
  enabled (λ s s', P s ∧ s' = f s) = P.
Proof.
  apply pred_ext => s.
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

Theorem eventually_stable (P: Σ → Prop) (next: action Σ) :
  (∀ s s', P s → next s s' → P s') →
  □⟨next⟩ ∧ ◇⌜P⌝ ⊢ ◇□ ⌜P⌝.
Proof.
  intros Hind.
  assert (□⟨next⟩ ⊢ □(⌜P⌝ → □⌜P⌝)).
  { apply always_intro_impl.
    apply impl_intro2.
    rewrite tla_and_comm. apply later_induction.
    unseal. }
  rewrite tla_and_curry.
  rewrite -> H.
  clear.
  intros e Halways.
  intros [k HP].
  exists k.
  apply Halways; eauto.
Qed.

Theorem leads_to_stable p (Q: Σ → Prop) (next: action Σ) :
  (∀ s s', Q s → next s s' → Q s') →
  □⟨next⟩ ∧ (p ~~> ⌜Q⌝) ⊢ (p ~~> □⌜Q⌝).
Proof.
  intros H.
  apply eventually_stable in H.
  apply tla_and_curry in H. rewrite tla_and_curry.
  apply always_intro_impl in H.
  rewrite -> H.
  rewrite /leads_to.
  clear.
  intros e Halways.
  intros HpQ.
  intros k Hp.
  apply Halways. apply HpQ. auto.
Qed.

Section lattice.

Context {S: Type} {R: S → S → Prop} (wf: well_founded R).

Local Infix "≺" := R (at level 50).

Theorem tla_lattice_leads_to (h: S → predicate) (c: S) (f hc g: predicate) :
  h c = hc →
  (∀ c, f ⊢ h c ~~> (g ∨ ∃ (d: S) (le: d ≺ c), h d)) →
  f ⊢ hc ~~> g.
Proof using wf.
  intros <- Hto_le.

  pose proof (wf c) as Hacc.
  induction Hacc.

  erewrite <- leads_to_trans;
  tla_split.
  { apply Hto_le. }
  rewrite leads_to_or_split.
  tla_split.
  { apply impl_drop_hyp. apply impl_to_leads_to. reflexivity. }

  rewrite /tla_exist => e Hf k.
  intros (c & Hle & Hc).
  eapply H0; eauto.
Qed.

(* TODO: try to make the goal a lattice element *)
Theorem lattice_leads_to (h: S → Σ → Prop) (c0: S) (f: predicate) (hc0 g: Σ → Prop) :
  h c0 = hc0 →
  (∀ c, f ⊢ ⌜h c⌝ ~~> ⌜λ s, g s ∨ ∃ (d: S), d ≺ c ∧ h d s⌝) →
  f ⊢ ⌜hc0⌝ ~~> ⌜g⌝.
Proof using wf.
  intros <- H.
  apply (tla_lattice_leads_to (λ l, ⌜h l⌝) c0); [ done | ].
  intros l.
  rewrite -> (H l).
  apply leads_to_weaken; [ done | ].
  unseal.
Qed.

End lattice.

(*|

We give a simple illustration of the lattice rule to prove the following
theorem:


::

  (f ⊢ p ~~> (q ∨ r)) →
  (f ⊢ q ~~> s) →
  (f ⊢ r ~~> s) →
  (f ⊢ p ~~> s)

The proof uses the simple lattice below:

::

      A
     / \
    B   C

The lattice points A, B, and C are interpreted (via the `h` argument to `lattice_leads_to`) as predicates p, q, and r, and the goal is to prove s. The relation on this lattice says B ≺ A and C ≺ A, which is why the leads_to out of p does not have to prove s but proves the intermediate goal q ∨ r. (Notice that the choice of which outgoing edge to use can be non-deterministic; this is an important freedom to give the user.)

Now notice that first of all this ≺ is well-founded: there are no
loops (which would represent circular reasoning). Second, notice that the
assumption `p ~~> (q ∨ r)` respects the ordering: it goes from `h A` to either
`h B` or `h C`, both of which are "smaller" in the lattice.

|*)

Inductive abc := A | B | C.

Definition abc_lt (x y: abc) :=
  (* notice the reverse order in the match: we want [abc_lt x y] when [y] is
  allowed to be used in the proof of [x] *)
  match y, x with
  | A, B | A, C => True
  | _, _ => False
  end.

Ltac prove_acc :=
  try assumption;
  apply Acc_intro; intros []; simpl; inversion 1; auto.

Theorem abc_lt_wf : well_founded abc_lt.
Proof.
  (* we carefully prove these bottom up *)
  assert (Acc abc_lt B) by prove_acc.
  assert (Acc abc_lt C) by prove_acc.
  assert (Acc abc_lt A) by prove_acc.
  by intros [].
Qed.

Lemma leads_to_fork (f p q r s: predicate) :
  (f ⊢ p ~~> (q ∨ r)) →
  (f ⊢ q ~~> s) →
  (f ⊢ r ~~> s) →
  (f ⊢ p ~~> s).
Proof.
  intros.
  apply (tla_lattice_leads_to abc_lt_wf
           (λ x, match x with
                 | A => p | B => q | C => r
                 end) A); [ done | ].
  intros []; simpl.
  - rewrite -> H.
    apply leads_to_or_right.
    apply leads_to_weaken; [ done | ].
    apply impl_or_split.
    * apply exist_impl_intro. exists B.
      apply exist_impl_intro. unshelve eexists _; eauto. done.
    * apply exist_impl_intro. exists C.
      apply exist_impl_intro. unshelve eexists _; eauto. done.
  - apply leads_to_or_left; done.
  - apply leads_to_or_left; done.
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

Ltac tla_intro :=
  first [ apply impl_intro | apply impl_intro2 ].

Ltac tla_left :=
  first [ tla_apply tla_or_introl |  apply leads_to_or_left ].
Ltac tla_right :=
  first [ tla_apply tla_or_intror |  apply leads_to_or_right ].

Ltac tla_intros := repeat tla_intro.

Ltac prove_acc_goal :=
  try assumption;
  apply Acc_intro; intros []; simpl; inversion 1; auto.

Ltac prove_wf xs :=
  lazymatch goal with
  | |- well_founded ?lt =>
    let rec go xs :=
      match xs with
      | nil => idtac
      | cons ?x ?xs =>
          assert (Acc lt x) by prove_acc_goal;
          go xs
      end in
    go xs;
    try solve [ intros []; assumption ]
  end.
