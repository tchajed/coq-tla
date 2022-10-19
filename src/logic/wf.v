(*|

========================
Weak fairness
========================

This file proves two big results about weak fairness. First, a key rule called "wf1" allows to prove that `p ~~> q` using the weak fairness of some action. Second, `wf_combine` gives a condition under which two weak fairness assumptions are equivalent to weak fairness of the composite action; that is, `WF(a1) ∧ WF(a2) == WF(a1 ∨ a2)` (with a slight abuse of notation in `a1 ∨ a2`, which needs to be `λ s s', a1 s s' ∨ a2 s s'`).

These both require non-trivial proofs.

|*)
From TLA Require Import defs automation.
From TLA Require Import propositional_ltl modalities.
From TLA Require Import classical.
From TLA.logic Require Import preds.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).

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

Theorem weak_fairness_alt3 a :
  weak_fairness a == (□◇ ⟨a⟩ ∨ □◇ !(tla_enabled a)).
Proof.
  rewrite weak_fairness_alt2.
  rewrite implies_to_or.
  tla_simp.
  rewrite tla_or_comm //.
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
  edestruct (until_next p q next e Hpuntilq Hnext);
    [ eassumption | | by auto ].

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

Lemma wf1 (a: action Σ) (next: action Σ) (p q: Σ → Prop)  :
  ∀ (Hpuntilq: ∀ s s', p s → next s s' → p s' ∨ q s')
    (Haq: ∀ s s', p s → next s s' → a s s' → q s')
    (Henable: ∀ s, p s → enabled a s),
  (⊢ □ ⟨next⟩ ∧ weak_fairness a → ⌜p⌝ ~~> ⌜q⌝).
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

Lemma eventually_always_weaken p :
  (◇□ p ⊢ □◇ p).
Proof.
  unseal.
  repeat deex.
  exists k0; eauto.
  replace (k0 + k) with (k + k0) by lia.
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

Lemma impl_intro' p q r :
  (p ∧ q ⊢ r) →
  (p ⊢ q → r).
Proof. unseal. Qed.

Theorem tla_wf2 (n m a b: action Σ) (p f: predicate) :
  (⟨n⟩ ∧ ⟨b⟩ ⊢ ⟨m⟩) →
  (p ∧ later p ∧ ⟨n⟩ ∧ ⟨a⟩ ∧ tla_enabled m ⊢ ⟨b⟩) →
  (p ∧ tla_enabled m ⊢ tla_enabled a) →
  (□⟨λ s s', n s s' ∧ ¬b s s'⟩ ∧
     weak_fairness a ∧ □f ∧
     ◇□ (tla_enabled m) ⊢ ◇□p) →
  (□⟨n⟩ ∧ weak_fairness a ∧ □f ⊢ weak_fairness m).
Proof.
  intros Hn_to_m Ha_to_b Hm_to_a_enabled Hp_while_not_b.
  rewrite (weak_fairness_alt2 m).
  apply impl_intro'; tla_simp.
  apply tla_contra.
  tla_simp.
  intros e (Hn & Hwf & Hf & Hmenabled & Heventually_notm).
  rewrite /tla_false /=.
Abort.

Theorem strong_fairness_alt2 a :
  strong_fairness a == (□◇ (tla_enabled a) → □ ◇ ⟨a⟩).
Proof.
  rewrite /strong_fairness.
  rewrite !implies_to_or.
  tla_simp.
  rewrite -!eventually_or.
  rewrite always_eventually_distrib.
  tla_simp.
Qed.

Lemma strong_fairness_alt3 a :
  strong_fairness a == (□◇⟨a⟩ ∨ ◇□(! tla_enabled a)).
Proof.
  rewrite strong_fairness_alt2.
  rewrite !implies_to_or.
  tla_simp.
  rewrite tla_or_comm //.
Qed.

Lemma strong_to_weak_fairness a :
  strong_fairness a ⊢ weak_fairness a.
Proof.
  rewrite weak_fairness_alt3 strong_fairness_alt3.
  rewrite eventually_always_weaken //.
Qed.

Lemma tla_sf1 (p q F: predicate) (next a: action Σ) :
  ∀ (Hpuntilq: ⊢ p ∧ ⟨next⟩ → later p ∨ later q)
    (Haq: ⊢ p ∧ ⟨next⟩ ∧ ⟨a⟩ → later q)
    (Henable: ⊢ □p ∧ □⟨next⟩ ∧ □F → tla_enabled a),
  (⊢ □ ⟨next⟩ ∧ strong_fairness a ∧ □F → p ~~> q).
Proof.
  rewrite strong_fairness_alt3.
  unseal.
  destruct H as (Hnext & Hsf_alt & HF).

  edestruct (until_next p q next e Hpuntilq Hnext);
    [ eassumption | | by auto ].

  destruct Hsf_alt as [Ha | [k' Hnotenabled]].
  - destruct (Ha k) as [k' Ha'].
    exists (S k').
    change (S k' + k) with (1 + (k' + k)). rewrite -drop_drop.
    apply Haq; eauto.
  - contradiction (Hnotenabled k).
    eapply Henable; intuition eauto.
    + rewrite ?drop_drop.
      replace (k0 + (k + k')) with ((k0 + k') + k) by lia.
      eauto.
    + rewrite ?drop_drop; eauto.
Qed.

End TLA.
