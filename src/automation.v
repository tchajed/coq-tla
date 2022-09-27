From Coq.Logic Require Import
  FunctionalExtensionality.

From Coq Require Export Lia.

From TLA Require Import defs.
From TLA Require Import classical.

(** This file develops the core automation for proving TLA properties. *)

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate).
Implicit Types (n m k: nat).

Local Ltac unseal :=
  apply predicate_ext => e;
  autounfold with tla;
  try tauto.

Lemma not_not (p: predicate) :
  (! ! p) == p.
Proof.  unseal.  Qed.

Lemma not_inj p q :
  !p == !q →
  p = q.
Proof.
  intros H.
  rewrite  -(not_not p) -(not_not q).
  rewrite H //.
Qed.

Theorem not_eventually p :
  ! ◇p == □ !p.
Proof.
  unseal.
  rewrite classical.not_exists //.
Qed.

Theorem not_always p :
  ! □p == ◇ !p.
Proof.
  unseal.
  rewrite classical.not_forall //.
Qed.

Lemma not_or p1 p2 :
  !(p1 ∨ p2) == (!p1 ∧ !p2).
Proof.  unseal.  Qed.

Lemma not_and p1 p2 :
  !(p1 ∧ p2) == (!p1 ∨ !p2).
Proof.  unseal.  Qed.

Lemma implies_to_or p1 p2 :
  (p1 → p2) == (!p1 ∨ p2).
Proof.  unseal.  Qed.

Lemma not_implies p1 p2 :
  !(p1 → p2) == (p1 ∧ !p2).
Proof.  unseal.  Qed.

End TLA.

Hint Rewrite not_eventually not_always
  not_and not_or not_not not_implies : tla.

Ltac tla_simp := autorewrite with tla; try reflexivity.

Ltac dual0 :=
  apply not_inj; tla_simp.

Tactic Notation "dual" := dual0.
Tactic Notation "dual" constr(lem) := dual0; rewrite lem; done.

Lemma drop_drop {Σ} k1 k2 (e: exec Σ) : drop k1 (drop k2 e) = drop (k1 + k2) e.
Proof.
  extensionality n.  rewrite /drop.
  f_equal; lia.
Qed.

Lemma drop_0 {Σ} (e: exec Σ) : drop 0 e = e.
Proof.
  extensionality n. rewrite /drop.
  f_equal; lia.
Qed.

Ltac unseal :=
  lazymatch goal with
  | |- @eq (predicate _) _ _ =>
    apply predicate_ext => e
  | _ => idtac
  end;
  autounfold with tla;
  try tauto;
  repeat setoid_rewrite drop_drop;
  repeat lazymatch goal with
  | |- (∀ (e: exec _), _) => intro e
  | |- (∀ (n: ?T), _) =>
    let kind := type of T in
    lazymatch kind with
    | Prop => let H := fresh "H" in intro H
    | _ => let n := fresh n in intro n
    end
  | |- _ → _ => let H := fresh "H" in intro H
  end;
  eauto.
