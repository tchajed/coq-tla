(*|
**Propositional theorems for TLA**

These theorems are straightforward analogues of propositional logic theorems for
temporal predicates.

|*)
From TLA Require Export defs automation.
From TLA Require Import classical.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).
Implicit Types (n m k: nat).

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

Theorem tla_and_true_r p :
  (p ∧ tla_true) == p.
Proof. unseal. Qed.

Theorem tla_and_true_l p :
  (tla_true ∧ p) == p.
Proof. unseal. Qed.

Theorem tla_or_false_r p :
  (p ∨ tla_false) == p.
Proof. unseal. Qed.

Theorem tla_or_false_l p :
  (tla_false ∨ p) == p.
Proof. unseal. Qed.

Theorem any_impl_true p :
  p ⊢ tla_true.
Proof. unseal. Qed.

Theorem false_impl_any p :
  tla_false ⊢ p.
Proof. unseal. Qed.

Theorem tla_or_introl p q :
  p ⊢ p ∨ q.
Proof. unseal. Qed.

Theorem tla_or_intror p q :
  q ⊢ p ∨ q.
Proof. unseal. Qed.

Theorem forall_intro {A} (φ: A → predicate) :
  (∀ x, ⊢ φ x) →
  ⊢ ∀ x, φ x.
Proof. unseal. Qed.

Theorem forall_impl_intro {A} (φ: A → predicate) Γ :
  (∀ x, Γ ⊢ φ x) →
  Γ ⊢ ∀ x, φ x.
Proof. unseal. Qed.

Theorem forall_apply {A} (φ: A → predicate) (x0: A) :
  (∀ x, φ x) ⊢ φ x0.
Proof. unseal. Qed.

Theorem exist_intro {A} (φ: A → predicate) :
  (∃ x, ⊢ φ x) →
  ⊢ ∃ x, φ x.
Proof. unseal. Qed.

Theorem exist_impl {A} (φ: A → predicate) (x0: A) :
  φ x0 ⊢ ∃ x, φ x.
Proof. unseal. Qed.

Theorem exist_impl_intro {A} (φ: A → predicate) Γ :
  (∃ x, Γ ⊢ φ x) →
  Γ ⊢ ∃ x, φ x.
Proof. unseal. Qed.

Theorem exist_and {A} (φ: A → predicate) p :
  ((∃ x, φ x) ∧ p) == (∃ x, φ x ∧ p).
Proof. unseal. Qed.

Theorem exist_or {A} `{Inhabited A} (φ: A → predicate) p :
  ((∃ x, φ x) ∨ p) == (∃ x, φ x ∨ p).
Proof.
  unseal; naive_solver.
  Unshelve.
  exact inhabitant.
Qed.

Theorem forall_and {A} `{Inhabited A} (φ: A → predicate) p :
  ((∀ x, φ x) ∧ p) == (∀ x, φ x ∧ p).
Proof.
  dual.
  rewrite exist_or.
  setoid_rewrite not_and; auto.
Qed.

Theorem forall_or {A} (φ: A → predicate) p :
  ((∀ x, φ x) ∨ p) == (∀ x, φ x ∨ p).
Proof.
  dual.
  rewrite exist_and.
  setoid_rewrite not_or; auto.
Qed.

Lemma modus_ponens (p q: predicate) :
  (p ∧ (p → q)) ⊢ q.
Proof.
  unseal.
Qed.

(** more general excluded middle that allows inserting an [r ∨ !r] anywhere in a
TLA goal *)
Lemma tla_and_em r p :
  p == (p ∧ (r ∨ !r)).
Proof.
  unseal.
Qed.

Lemma tla_excluded_middle r p q :
  (p ∧ r ⊢ q) →
  (p ∧ !r ⊢ q) →
  (p ⊢ q).
Proof.
  rewrite {3}(tla_and_em r p).
  unseal.
Qed.

Lemma tla_and_distr_l p q r :
  (p ∧ (q ∨ r)) == (p ∧ q ∨ p ∧ r).
Proof.
  unseal.
Qed.

Lemma tla_and_distr_r p q r :
  ((q ∨ r) ∧ p) == (q ∧ p ∨ r ∧ p).
Proof.
  unseal.
Qed.

Lemma tla_or_distr_l p q r :
  (p ∨ (q ∧ r)) == ((p ∨ q) ∧ (p ∨ r)).
Proof.
  unseal.
Qed.

Lemma tla_or_distr_r p q r :
  ((q ∧ r) ∨ p) == ((q ∨ p) ∧ (r ∨ p)).
Proof.
  unseal.
Qed.

Lemma impl_intro p q :
  (p ⊢ q) →
  (⊢ p → q).
Proof. unseal. Qed.

Lemma tla_and_curry p q r :
  (p ∧ q ⊢ r) ↔ (p ⊢ q → r).
Proof. unseal. Qed.

Lemma impl_intro2 p q r :
  (p ∧ q ⊢ r) →
  (p ⊢ q → r).
Proof. rewrite tla_and_curry //. Qed.

Lemma impl_or_split p q φ :
  (p ⊢ φ) →
  (q ⊢ φ) →
  (p ∨ q ⊢ φ).
Proof. unseal. Qed.

Theorem impl_drop_hyp p q :
  (⊢ q) →
  p ⊢ q.
Proof. unseal. Qed.

(* a very crude way to drop a hypothesis *)
Theorem impl_drop_one p q r :
  (p ⊢ q) →
  p ∧ r ⊢ q.
Proof. unseal. Qed.

End TLA.

Hint Rewrite
  tla_and_true_r tla_and_true_l
  tla_or_false_l tla_or_false_r : tla.

Hint Rewrite tla_and_assoc tla_or_assoc : tla.
