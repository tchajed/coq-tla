From TLA Require Import logic.

Section example.

(*|
We define a simple state machine with a field `x` that goes from `A` to `B` to `C`, and separately a field `happy` that remains constant.

The state machine has a safety property that says `happy` is true, and a liveness property that eventually `x = C`.
|*)

Inductive abc := A | B | C.
Record state :=
  { x: abc; happy: bool; }.

Implicit Types (s: state).

Definition ab : action state :=
  λ s s', (s.(x) = A ∧ s'.(x) = B ∧ s'.(happy) = s.(happy)).

Definition bc : action state :=
  λ s s', (s.(x) = B ∧ s'.(x) = C ∧ s'.(happy) = s.(happy)).

Definition init (s: state) :=
    s.(x) = A ∧ s.(happy) = true.

(*|
It is important to allow stuttering (`s = s'`) in this predicate! Otherwise there would be no infinite sequences satisfying `□ ⟨next⟩`, since after two transitions no steps would be possible.
|*)
Definition next s s' :=
  ab s s' ∨ bc s s' ∨ s = s'.


(*|
A little automation will prove all the state-machine specific reasoning required for this example, essentially by brute force.
|*)
Hint Unfold init happy next ab bc : stm.

Hint Unfold enabled : stm.

Ltac stm :=
  autounfold with stm in *;
  intros;
  repeat match goal with
        | s: state |- _ =>
          let x := fresh "x" in
          let happy := fresh "happy" in
          destruct s as [x happy]
        | H: (@eq state _ _) |- _ => inversion H; subst; clear H
        end;
  intuition idtac;
  try solve [
      try match goal with
      | |- ∃ (s: state), _ => eexists {| x := _; happy := _; |}
      end;
    intuition (subst; eauto; try congruence) ].

(*|
--------
Safety
--------

The safety property is pretty easy, using `init_invariant`. In fact it's so simple it's already inductive and we don't need to go through a separate invariant.
|*)

Theorem always_happy :
  ⌜ init ⌝ ∧ □ ⟨next⟩ ⊢ □ ⌜λ s, s.(happy)⌝.
Proof.
  apply init_invariant. (* .unfold *)
  - stm.
  - stm.
Qed.

(*|
-----------
Liveness
-----------

Liveness is more interesting. The high-level strategy is to use the rule `wf1` to prove `A ~~> B` and that `B ~~> C`; then we can chain them together and finally apply them by showing that `init` implies `A`.
|*)

(*|
Notice that the state-machine reasoning all happens here, and in the analogous `b_leads_to_c` proof below. We only need to prove one- and two-state properties and the wf1 rules lifts them to a temporal property that uses the weak fairness assumption.
|*)
Theorem a_leads_to_b :
  □ ⟨ next ⟩ ∧ weak_fairness ab ⊢
  ⌜λ s, s.(x) = A⌝ ~~> ⌜λ s, s.(x) = B⌝.
Proof.
  apply wf1. (* .unfold *)
  - stm.
  - stm.
  - stm.
Qed.

Lemma init_a :
  ⌜init⌝ ⊢ ⌜λ s, s.(x) = A⌝.
Proof.
  apply state_pred_impl => s.  stm.
Qed.

(*|
This theorem isn't directly needed; we carry out the same reasoning to derive ◇ C from the leads_to proofs.
|*)
Theorem eventually_b :
  ⌜init⌝ ∧ □ ⟨next⟩ ∧ weak_fairness ab ⊢
  ◇ ⌜λ s, s.(x) = B⌝.
Proof.
  apply (leads_to_apply ⌜ λ s, s.(x) = A ⌝).
  { rewrite -> init_a; tla_prop. }
  tla_apply a_leads_to_b.
Qed.

Theorem b_leads_to_c :
  □ ⟨ next ⟩ ∧ weak_fairness bc ⊢
   ⌜λ s, s.(x) = B⌝ ~~> ⌜λ s, s.(x) = C⌝.
Proof.
  apply wf1.
  - stm.
  - stm.
  - stm.
Qed.

Theorem a_leads_to_c :
  □ ⟨ next ⟩ ∧ weak_fairness ab ∧ weak_fairness bc ⊢
  ⌜ λ s, s.(x) = A ⌝ ~~> ⌜ λ s, s.(x) = C ⌝.
Proof.
  leads_to_trans (⌜λ s, s.(x) = B⌝)%L.
  { tla_apply a_leads_to_b. }
  tla_apply b_leads_to_c.
Qed.

Theorem eventually_c :
  state_pred init ∧ □ ⟨next⟩ ∧ weak_fairness ab ∧ weak_fairness bc ⊢
  ◇ ⌜ λ s, s.(x) = C ⌝.
Proof.
(*|
`leads_to_apply p` will switch from proving `◇ q` to `p` and `p ~~> q`.
|*)
  apply (leads_to_apply ⌜λ s, s.(x) = A⌝%L).
  { rewrite -> init_a; tla_prop. }
  tla_apply a_leads_to_c.
Qed.

End example.
