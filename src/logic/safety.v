From TLA Require Import defs automation.
From TLA Require Import propositional_ltl modalities.
From TLA Require Import classical.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).

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


End TLA.
