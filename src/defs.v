(*|
================================
Embedding the TLA logic in Coq
================================

This development defines a version of TLA (the Temporal Logic of Actions) in
Coq. This file just sets out the basic definitions of TLA, in particular the notion of a (temporal) predicate, lifting the basic propositional operators like "not" and "and" to predicates, and the always and eventually *modalities* of TLA.
|*)

From Coq.Logic Require Import
  PropExtensionality FunctionalExtensionality.

From Coq.ssr Require Export ssreflect.
From stdpp Require Export base.

#[export] Set Default Proof Using "Type".
#[export] Set Default Goal Selector "!".


(*|
A TLA formula is defined using `predicate`, which is defined in Coq as a predicate over executions (also known as "behaviors" in TLA). Executions are in turn defined to be an infinite sequence of states, which come from some arbitrary type Σ. Note that throughout the entire theory Σ does not change and remains abstract. In TLA, Σ corresponds to the state of all the variables, which are implicitly all available. |*)

Definition exec (Σ: Type) := nat → Σ.
Definition predicate (Σ: Type) := exec Σ → Prop.

(*|
There are a few primitive ways to construct TLA predicates, by lifting state predicates or actions; the particular use of actions is what distinguishes TLA from LTL (linear temporal logic), although the two will look very similar in this development.
|*)
Definition state_pred {Σ: Type} (f: Σ → Prop) : predicate Σ :=
    λ ex, f (ex 0).

Notation "⌜  P  ⌝" := (state_pred P%type).

Definition action (Σ: Type) := Σ → Σ → Prop.
Definition action_pred {Σ: Type} (a: action Σ) : predicate Σ :=
    λ ex, a (ex 0) (ex 1).

Notation "⟨ a ⟩" := (action_pred a%type) (format "⟨ a ⟩").

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

Definition tla_forall {A: Type} (p: A → predicate) : predicate :=
  λ e, ∀ x, (p x) e.
Definition tla_exist {A: Type} (p: A → predicate) : predicate :=
  λ e, ∃ x, (p x) e.

(*|
The heart of TLA's assertions are the `always` and `eventually` modalities. A modality is in general a transformation on formulas. `always p` (which will be written □ p) says that `p` holds "from now on". This is expressed using the `drop` function, which shifts a behavior by k steps.

The other important modality is `eventually p` (which will be written ◇ p).
|*)

Definition drop k e : exec := λ n, e (n + k).
Definition always p : predicate := λ e, ∀ k, p (drop k e).
Definition eventually p : predicate := λ e, ∃ k, p (drop k e).

(*| This serves the rule of the "prime" in TLA, but with a more general and
formal definition than TLA, which seems to only use them in actions and does not
treat it as a full-fledged modality. |*)
Definition later p : predicate := λ e, p (drop 1 e).

(*|
`valid` asserts that a TLA formula "holds" or "is true", which is defined as holding for all executions. This is sometimes phrased as saying that `p` is a tautology, but that can be confusing if you're not used to it. We'll use the standard logic notation `⊢ p` to state that `p` is valid. Note that validity is a "meta language assertion" (Prop, since Coq is our meta language), not a TLA formula.

`pred_impl` is equivalent to `valid (tla_implies p q)`, but it's convenient for Coq to have a definition for it (maybe, I haven't actually tried getting rid of it).
|*)

Definition valid p := ∀ e, p e.

Definition pred_impl (p q: predicate) :=
  ∀ e, p e → q e.

(*|
We assume some Coq axioms so that predicates can be proven equal in the `=` sense if they are logically equivalent, which simplifies working with equivalent predicates a bit.
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

Definition tla_true : predicate := λ _, True.
Definition tla_false : predicate := λ _, False.

End TLA.

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
Notation "∀ x .. y , p" :=
  (tla_forall (λ x, .. (tla_forall (λ y, p%L) ) ..)): tla.
Notation "∃ x .. y , p" :=
  (tla_exist (λ x, .. (tla_exist (λ y, p%L) ) ..)): tla.

Notation "□  p" := (always p%L) (at level 51, right associativity) : tla.
Notation "◇  p" := (eventually p%L) (at level 51, right associativity) : tla.

(*|
`enabled a` is a state predicate that defines what it means for an action to be
enabled.
|*)
Definition enabled {Σ} (a: action Σ) (s:Σ) := ∃ s', a s s'.

(*|
`tla_enabled` is just a convenience for lifting `enabled a` to a temporal
predicate.
|*)
Definition tla_enabled {Σ} (a: action Σ) : predicate Σ :=
  state_pred (enabled a).

(*|
Weak fairness is an important definition for stating liveness properties. Typically liveness properties hold only under some assumptions that the behavior in question treats an action _fairly_, intuitively meaning that it gets a chance to run "often enough". This is defined in weak fairness as the following: in a behavior, `a` is treated weakly fairly if whenever it is always enabled, it eventually runs. Alternately, we can rewrite the implication as a disjunction and say that `a` is treated weakly fairly if at every step it is either not enabled at some point, or it executes.

The logic will eventually have a rule `wf1` that allows to use a `weak_fairness a` assumption and prove `◇ q` from it.
|*)
Definition weak_fairness {Σ} (a: action Σ) : predicate Σ :=
  □ (□ (tla_enabled a) → (◇ ⟨a⟩)).

(*|
Leads to, written `p ~~> q`, is a useful definition for expressing something that is eventually true under some assumption. The □ in front is important to make this definition transitive (proven later), in the sense that `⊢ (p ~~> q) → (q ~~> r) → (p ~~> r)`. (Without it, the second leads_to couldn't be used at the time when the first leads_to says q holds).
|*)
Definition leads_to {Σ} (p q: predicate Σ) : predicate Σ :=
  □ (p → ◇ q).

Notation "p ~~> q" := (leads_to p q) (at level 51, right associativity).

Arguments enabled {Σ}%type_scope a%type_scope.
Arguments tla_enabled {Σ}%type_scope a%type_scope.
Arguments weak_fairness {Σ}%type_scope a%type_scope.
