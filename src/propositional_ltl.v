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

End TLA.

Hint Rewrite
  tla_and_true_r tla_and_true_l
  tla_or_false_l tla_or_false_r : tla.

Hint Rewrite tla_and_assoc tla_or_assoc : tla.
