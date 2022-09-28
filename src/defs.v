From Coq.Logic Require Import
  PropExtensionality FunctionalExtensionality.

From Coq.ssr Require Export ssreflect.
From stdpp Require Export base.

(*|
================================
Embedding the TLA logic in Coq.
================================

A TLA formula is defined using `predicate`, which is defined in Coq as a predicate over executions (also known as "behaviors" in TLA). Executions are in turn defined to be an infinite sequence of states, which come from some arbitrary type Σ. Note that throughout the entire theory Σ does not change and remains abstract - TLA never talks about how to relate predicates defined for different states.
|*)

Definition exec (Σ: Type) := nat → Σ.
Definition predicate (Σ: Type) := exec Σ → Prop.

(*|
There are a few primitive ways to construct TLA predicates, by lifting state predicates or actions.
|*)
Definition state_pred {Σ: Type} (f: Σ → Prop) : predicate Σ :=
    λ ex, f (ex 0).

Definition action (Σ: Type) := Σ → Σ → Prop.
Definition action_pred {Σ: Type} (a: action Σ) : predicate Σ :=
    λ ex, a (ex 0) (ex 1).

Notation "⟨ a ⟩" := (action_pred a).

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section TLA.

Context {Σ: Type}.

(* This trick avoids needing to repeat the parameters to [exec] and [predicate]
throughout. *)
Local Notation exec := (exec Σ).
Local Notation predicate := (predicate Σ).

(* This directive tells Coq that if a variable uses this name (or the name
followed by numbers or prime symbols), it should automatically get the
appropriate type. This follows common mathematical presentations, and can make
things easier to read since types reliably follow naming conventions. *)
Implicit Types (e: exec) (p q: predicate).
Implicit Types (n m k: nat).

(*|
TLA lifts the basic propositional logic connectives to predicates over executions, in a straightforward way.
|*)

Definition tla_not p : predicate := λ e, ¬ p e.
Definition tla_or p1 p2 : predicate := λ e, p1 e ∨ p2 e.
Definition tla_and p1 p2 : predicate := λ e, p1 e ∧ p2 e.
Definition tla_implies p1 p2 : predicate := λ e, p1 e → p2 e.

(*|
The heart of TLA's assertions are the `always` and `eventually` modalities. A modality is in general a transformation on formulas. `always p` (which will be written □ p) says that `p` holds "from now on". This is expressed using the `drop` function, which shifts a behavior by k steps.

The other important modality is `eventually p` (which will be written ◇ p).
|*)

Definition drop k e : exec := λ n, e (n + k).
Definition always p : predicate := λ e, ∀ k, p (drop k e).
Definition eventually p : predicate := λ e, ∃ k, p (drop k e).

(* This serves the rule of the "prime" in TLA, but with a more general and
formal definition than TLA, which seems to only use them in actions and does not
treat it as a full-fledged modality. *)
Definition later p : predicate := λ e, p (drop 1 e).

(*|
`valid` asserts that a TLA formula "holds" or "is true", which is defined as holding for all executions. This is sometimes phrased as saying that `p` is a tautology, but that can be confusing if you're not used to it. We'll use the standard logic notation `⊢ p` to state that `p` is valid. Note that validity is a "meta language assertion" (Prop, since Coq is our meta language), not a TLA formula.

`pred_impl` is equivalent to `valid (tla_implies p q)`, but it's convenient for Coq to have a definition for it (maybe, I haven't actually tried getting rid of it).
|*)

Definition valid p := ∀ e, p e.

Definition pred_impl (p q: predicate) :=
  ∀ e, p e → q e.

(*|
We assume some axioms so that predicates can be proven equal in the `=` sense if they are logically equivalent, which simplifies working with equivalent predicates a bit.
|*)
Lemma predicate_ext p1 p2 : (∀ e, p1 e ↔ p2 e) → p1 = p2.
Proof.
  intros H.  extensionality e.  apply propositional_extensionality.
  auto.
Qed.

Lemma pred_impl_as_valid p q :
  (pred_impl p q) ↔ (valid (tla_implies p q)).
Proof. reflexivity. Qed.

Lemma equiv_to_impl p q :
  (pred_impl p q) → (pred_impl q p) → (p = q).
Proof.
  intros H1 H2.
  apply predicate_ext => e.
  intuition eauto.
Qed.

End TLA.

#[export]
Hint Unfold tla_and tla_or tla_not tla_implies eventually always later : tla.
#[export]
Hint Unfold valid pred_impl : tla.

#[global] Hint Unfold state_pred action_pred : tla.

Declare Scope tla.
Delimit Scope tla with L.
Bind Scope tla with predicate.

Notation "⊢  p" := (valid p%L) (at level 99, p at level 200).
(* this is just to force parsing in tla scope *)
Notation "p == q" := (@eq (predicate _) p%L q%L) (at level 70, only parsing).
Notation "p  ⊢  q" := (pred_impl p%L q%L) (at level 100).

Notation "!  p" := (tla_not p%L) (at level 51, right associativity) : tla.
Notation "p  ∨  q" := (tla_or p%L q%L) : tla.
Notation "p  ∧  q" := (tla_and p%L q%L) : tla.
Notation "p  ->  q" := (tla_implies p%L q%L) : tla.
Notation "p  →  q" := (tla_implies p%L q%L) : tla.

Notation "□  p" := (always p%L) (at level 51, right associativity) : tla.
Notation "◇  p" := (eventually p%L) (at level 51, right associativity) : tla.

(*|
`weak_fairness` is a useful notion for liveness. When `weak_fairness a` holds of a behavior, if at any point the action is always enabled, then it must eventually run.
|*)

(* these two definitions are here so they can use the notation *)

Definition enabled {Σ} (a: action Σ) : predicate Σ :=
  state_pred (λ s, ∃ s', a s s').

Definition weak_fairness {Σ} (a: action Σ) : predicate Σ :=
    □ (□ (enabled a) → (◇ ⟨a⟩)).

#[global] Hint Unfold weak_fairness : tla.

Definition leads_to {Σ} (p q: predicate Σ) : predicate Σ :=
  □ (p → ◇ q).

#[global] Hint Unfold leads_to : tla.

Notation "p ~~> q" := (leads_to p q) (at level 51, right associativity).

Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]
  | [ H: _ ∧ _ |- _ ] => destruct H
  | _ => subst
  end.

(*|
The instances blow enable rewriting by predicate implications, even inside
formulae. For example we can use H: p ⊢ q (pred_impl p q) as [rewrite H] to
change [p ∧ r ⊢ q] to [q ∧ r ⊢ q].
|*)
Section rewriting.

Context [Σ: Type].
Notation pred_impl := (@pred_impl Σ).

Local Ltac instance_t :=
  rewrite /Proper /respectful /Basics.flip /Basics.impl /pred_impl;
  autounfold with tla;
  try solve [ intuition (deex; eauto) ].

Global Instance pred_impl_reflexive : Reflexive pred_impl.
Proof. compute; intuition auto. Qed.

Global Instance pred_impl_trans : Transitive pred_impl.
Proof. compute; intuition auto. Qed.

Global Instance implies_impl_proper :
  Proper (Basics.flip pred_impl ==> pred_impl ==> pred_impl) tla_implies.
Proof.  instance_t.  Qed.

Global Instance implies_impl_flip_proper :
  Proper (pred_impl ==> flip pred_impl ==> flip pred_impl) tla_implies.
Proof.  instance_t.  Qed.

Global Instance and_impl_proper :
  Proper (pred_impl ==> pred_impl ==> pred_impl) tla_and.
Proof. instance_t. Qed.

Global Instance and_impl_flip_proper :
  Proper (flip pred_impl ==> flip pred_impl ==> flip pred_impl) tla_and.
Proof. instance_t. Qed.

Global Instance and_impl_proper' p :
  Proper (pred_impl ==> pred_impl) (tla_and p).
Proof. apply and_impl_proper. reflexivity. Qed.

Global Instance or_impl_proper :
  Proper (pred_impl ==> pred_impl ==> pred_impl) tla_or.
Proof. instance_t. Qed.

Global Instance eventually_impl_proper :
  Proper (pred_impl ==> pred_impl) eventually.
Proof.  instance_t. Qed.

Global Instance always_impl_proper :
  Proper (pred_impl ==> pred_impl) always.
Proof.  instance_t. Qed.

Global Instance later_impl_proper :
  Proper (pred_impl ==> pred_impl) later.
Proof.  instance_t. Qed.

Global Instance pred_impl_proper :
  Proper (Basics.flip pred_impl ==> pred_impl ==> Basics.impl) pred_impl.
Proof. instance_t. Qed.

Global Instance pred_flip_impl_proper :
  Proper (pred_impl ==> Basics.flip pred_impl ==> Basics.flip impl) pred_impl.
Proof. instance_t. Qed.

Global Instance impl_valid :
  Proper (pred_impl ==> impl) valid.
Proof. instance_t. Qed.

Global Instance impl_flip_valid :
  Proper (flip pred_impl ==> flip impl) valid.
Proof. instance_t. Qed.

End rewriting.
