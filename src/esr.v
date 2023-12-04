From TLA Require Import logic.
From TLA Require Import until.

Section controller.

Context {Σ: Type}.
Context {StateSpec: Type}.
Context (desire: Σ → StateSpec).
Context (matches: StateSpec → Σ → Prop).

Definition desired (d: StateSpec) : predicate Σ :=
  ⌜λ s, desire s = d⌝.

Lemma desired_changed (d: StateSpec) :
  !(desired d) == ⌜λ s, desire s ≠ d⌝.
Proof. clear matches. unseal. Qed.

Definition ESR : predicate Σ :=
  ∀ d, □ (□ desired d →
          ◇□ ⌜matches d⌝
         ).

Definition ESR' : predicate Σ :=
  ∀ d, □ (desired d →
          ◇ (weak_until
               ⌜matches d⌝
               (!(desired d))
         )).

Lemma esr_bodies_eq (d: StateSpec) :
  (□ desired d → ◇□ ⌜matches d⌝) ==
    (desired d →
     ◇ (weak_until
          ⌜matches d⌝
          (!(desired d))
    )).
Proof.
  rewrite eventually_weak_until.
  rewrite !tla_impl_to_or.
  rewrite not_always.
  rewrite !eventually_or.
  (* just propositional reasoning left *)
  unseal.
Qed.

End controller.
