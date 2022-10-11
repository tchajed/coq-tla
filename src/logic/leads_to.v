(*|

=========================
Reasoning about leads-to
=========================

The connective `p ~~> q`, defined to be `□(p → ◇q)`, is pervasive in liveness
reasoning. This file proves a few basic results about leads to (for example,
that it is transitive), as well as a more sophisticated result that shows how to
combine a well-founded "lattice" of leads-to facts, which is crucial for
reasoning about diverging facts that eventually converge to guarantee some
result.

Some of these rules are specialized to state predicates, because we believe that
it will often be sufficient to only use the form `⌜P⌝ ~~> ⌜Q⌝` and not use the
full generality of temporal predicates.

|*)
From TLA Require Import defs automation.
From TLA Require Import propositional_ltl modalities.
From TLA Require Import classical.
From TLA.logic Require Import safety.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).

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

Theorem leads_to_weaken (p1 p2 q1 q2: predicate) :
  (p2 ⊢ p1) →
  (q1 ⊢ q2) →
  p1 ~~> q1 ⊢ p2 ~~> q2.
Proof.
  intros H1 H2.
  rewrite /leads_to.
  rewrite H1 -H2 //.
Qed.

#[global]
Instance leads_to_impl_proper :
  Proper (flip pred_impl ==> pred_impl ==> pred_impl) (leads_to (Σ := Σ)).
Proof.
  intros p1 q1 Himpl p2 q2 Himpl2.
  apply leads_to_weaken; auto.
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

Theorem pred_leads_to (P Q: Σ → Prop) Γ :
  (∀ s, P s → Q s) →
  Γ ⊢ ⌜P⌝ ~~> ⌜Q⌝.
Proof.
  intros.
  apply impl_drop_hyp.
  apply impl_to_leads_to.
  unseal.
Qed.

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

Lemma leads_to_assume (q: predicate) {p r φ: predicate} :
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

(* the rule as it appears in the paper *)
Theorem tla_paper_lattice_leads_to (h: S → predicate) (f g: predicate) :
  (∀ c, f ⊢ h c ~~> (g ∨ ∃ (d: S) (le: d ≺ c), h d)) →
  f ⊢ (∃ c0, h c0) ~~> g.
Proof using wf.
  intros Hto_le.

  cut (∀ c0, f ⊢ h c0 ~~> g).
  { intros Hfc0.
    rewrite /leads_to /tla_exist.
    intros e Hf k [c0 Hh].
    eapply Hfc0; eauto. }

  intros c0.
  pose proof (wf c0) as Hacc.
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

(* a variant of the rule where the goal is also part of the lattice *)
Theorem tla_lattice_leads_to (h: S → predicate) (c0 g: S)
  (f hc0 hg: predicate) :
  h c0 = hc0 → h g = hg →
  (∀ c, c ≠ g → f ⊢ h c ~~> (∃ (d: S) (le: d = g ∨ d ≺ c), h d)) →
  f ⊢ hc0 ~~> hg.
Proof using wf.
  intros <- <- Hto_le.
  rewrite <- (leads_to_trans _ (∃ c0, h c0)); tla_split.
  { apply impl_drop_hyp. apply impl_to_leads_to. unseal. }

  apply tla_paper_lattice_leads_to.
  intros l.

  destruct (classical.excluded_middle (l = g)); subst.
  { apply impl_drop_hyp.
    apply impl_to_leads_to.
    tla_prop. }

  rewrite -> (Hto_le l) by auto.
  apply leads_to_weaken; [ done | ].

  unseal.
  naive_solver.
Qed.

Theorem lattice_leads_to (h: S → Σ → Prop) (c0 g: S)
  (f: predicate) (hc0 hg: Σ → Prop) :
  h c0 = hc0 → h g = hg →
  (∀ c, c ≠ g → f ⊢ ⌜h c⌝ ~~> ⌜λ s, ∃ (d: S), (d = g ∨ d ≺ c) ∧ h d s⌝) →
  f ⊢ ⌜hc0⌝ ~~> ⌜hg⌝.
Proof using wf.
  intros <- <- H.
  apply (tla_lattice_leads_to (λ l, ⌜h l⌝) c0 g); [ done | done | ].
  intros l Hnotg.
  rewrite -> (H l) by auto.
  apply leads_to_weaken; [ done | ].
  unseal.
Qed.

Theorem lattice_leads_to_ex (h: S → Σ → Prop) (g: S)
  (f: predicate) (hg: Σ → Prop) :
  h g = hg →
  (∀ c, c ≠ g → f ⊢ ⌜h c⌝ ~~> ⌜λ s, ∃ (d: S), (d = g ∨ d ≺ c) ∧ h d s⌝) →
  f ⊢ (∃ c0, ⌜h c0⌝) ~~> ⌜hg⌝.
Proof using wf.
  intros <- H.

  cut (∀ c0, f ⊢ ⌜h c0⌝ ~~> ⌜h g⌝).
  { intros Hfc0.
    rewrite /leads_to /tla_exist.
    intros e Hf k [c0 Hh].
    eapply Hfc0; eauto. }

  intros c0.
  apply (tla_lattice_leads_to (λ l, ⌜h l⌝) c0 g); [ done | done | ].
  intros l Hnotg.
  rewrite -> (H l) by auto.
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
    \   /
      G

The lattice points A, B, C, and G are interpreted (via the `h` argument to `lattice_leads_to`) as predicates p, q, r, and s, where s is the special goal that has nothing after it. The relation on this lattice says B ≺ A, C ≺ A, G ≺ B, and G ≺ C (one for each edge). Notice that A has two "outgoing edges" - this means we prove p ~~> (q ∨ r), and it is this non-deterministic choice that makes the rule powerful.

First, notice that this ≺ is well-founded: there are no loops (which would represent circular reasoning). Second, notice that the assumption `p ~~> (q ∨ r)` respects the ordering: it goes from `h A` to either `h B` or `h C`, both of which are "smaller" in the lattice.

|*)

Inductive abc := A | B | C | G.

Definition abc_lt (x y: abc) :=
  (* notice the reverse order in the match: we want [abc_lt x y] when [y] is
  allowed to be used in the proof of [x] *)
  match y, x with
  | A, B | A, C => True
  | B, G | C, G => True
  | _, _ => False
  end.

Ltac prove_acc :=
  try assumption;
  apply Acc_intro; intros []; simpl; inversion 1; auto.

Theorem abc_lt_wf : well_founded abc_lt.
Proof.
  (* we carefully prove these bottom up *)
  assert (Acc abc_lt G) by prove_acc.
  assert (Acc abc_lt B) by prove_acc.
  assert (Acc abc_lt C) by prove_acc.
  assert (Acc abc_lt A) by prove_acc.
  by intros [].
Qed.

Lemma leads_to_fork2 (q r f p s: predicate) :
  (f ⊢ p ~~> (q ∨ r)) →
  (f ⊢ q ~~> s) →
  (f ⊢ r ~~> s) →
  (f ⊢ p ~~> s).
Proof.
  intros.
  apply (tla_lattice_leads_to abc_lt_wf
           (λ x, match x with
                 | A => p | B => q | C => r | G => s
                 end) A G); [ done | done | ].
  intros [] Hne; simpl; try congruence.
  - rewrite -> H.
    apply leads_to_weaken; [ done | ].
    apply impl_or_split.
    * apply exist_impl_intro. exists B.
      apply exist_impl_intro. unshelve eexists _; eauto. done.
    * apply exist_impl_intro. exists C.
      apply exist_impl_intro. unshelve eexists _; eauto. done.
  - rewrite -> H0.
    apply leads_to_weaken; [ done | ].
    apply exist_impl_intro. exists G. unseal.
  - rewrite -> H1.
    apply leads_to_weaken; [ done | ].
    apply exist_impl_intro. exists G. unseal.
Qed.

Lemma leads_to_detour (q p s Γ : predicate) :
  (Γ ⊢ p ~~> (q ∨ s)) →
  (Γ ⊢ q ~~> s) →
  (Γ ⊢ p ~~> s).
Proof.
  intros.
  apply (leads_to_fork2 q s); auto.
  apply impl_drop_hyp.
  apply leads_to_refl.
Qed.

Lemma leads_to_exist_intro {A} (Γ: predicate) (φ: A → predicate) q :
  (∀ x, Γ ⊢ φ x ~~> q) →
  (Γ ⊢ (∃ x, φ x) ~~> q).
Proof. unseal. Qed.

(* leads_to_fork is really just transitivity but it captures the idea of a
simple diverge-reconverge pattern *)
Lemma leads_to_fork {A: Type} (h: A → Σ → Prop)
  (f: predicate) (p q: Σ → Prop) :
  (f ⊢ ⌜p⌝ ~~> ⌜λ s, ∃ x, h x s⌝) →
  (∀ (x: A), f ⊢ ⌜h x⌝ ~~> ⌜q⌝) →
  (f ⊢ ⌜p⌝ ~~> ⌜q⌝).
Proof.
  intros Hph Hhq.
  erewrite <- leads_to_trans; tla_split; [ apply Hph | ].
  apply leads_to_exist_intro.
  intros x. fold (⌜h x⌝). eauto.
Qed.

End TLA.

Ltac leads_to_trans q :=
  rewrite <- (leads_to_trans _ q _);
  tla_split.

Ltac leads_to_etrans :=
  erewrite <- leads_to_trans;
  tla_split.

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
