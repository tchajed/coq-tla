(*|

========================
Proving safety in TLA
========================

Safety is actually extremely simple in TLA: there's basically one rule, and this file has a few convenient variants.

|*)

From TLA Require Import defs automation.
From TLA Require Import modalities.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation action := (action Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action).

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

Theorem tla_init_safety (inv init next safe : predicate) :
  (init ⊢ inv) →
  (inv ∧ next ⊢ later inv) →
  (inv ⊢ safe) →
  ⊢ init ∧ □ next → □ safe.
Proof.
  intros Hinit Hlater Hsafe.
  rewrite Hinit -Hsafe.
  by apply later_induction.
Qed.

Theorem init_safety (inv init: Σ → Prop) (next: action) (safe : Σ → Prop) :
  (∀ s, init s → inv s) →
  (∀ s s', inv s → next s s' → inv s') →
  (∀ s, inv s → safe s) →
  ⊢ state_pred init ∧ □ ⟨next⟩ → □ (state_pred safe).
Proof.
  intros Hinit Hinv Hsafe.
  apply (tla_init_safety (state_pred inv)); unseal.
Qed.

Theorem init_invariant (init: Σ → Prop) (next: action) (inv: Σ → Prop) :
  (∀ s, init s → inv s) →
  (∀ s s', inv s → next s s' → inv s') →
  state_pred init ∧ □ ⟨next⟩ ⊢ □ state_pred inv.
Proof.
  intros Hinit Hinv.
  apply (init_safety inv); auto.
Qed.

End TLA.
