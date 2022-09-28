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
  state_pred init ∧ □ ⟨next⟩ ⊢ □ (state_pred (λ s, s.(happy))).
Proof.
  apply init_invariant.
  - stm.
  - stm.
Qed.

(*|
-----------
Liveness
-----------

Liveness is more interesting. The high-level strategy is to use the rule `wf1` to prove A ~~> B and that B ~~> C; then we can chain them together and finally apply them by showing that `init` implies A.
|*)

(*|
Notice that the state-machine reasoning all happens here, and in the analogous `b_leads_to_c` proof below. We only need to prove one- and two-state properties and the wf1 rules lifts them to a temporal property that uses the weak fairness assumption.
|*)
Theorem a_leads_to_b :
  □ ⟨ next ⟩ ∧ weak_fairness ab ⊢
  state_pred (λ s, s.(x) = A) ~~> state_pred (λ s, s.(x) = B).
Proof.
  apply wf1.
  - unseal.  stm.
  - unseal.  stm.
  - apply state_pred_impl => s.  stm.
Qed.

Lemma init_a :
  state_pred init ⊢ state_pred (λ s, s.(x) = A).
Proof.
  apply state_pred_impl => s.  stm.
Qed.

(*|
This theorem isn't directly needed; we carry out the same reasoning to derive ◇ C from the leads_to proofs.
|*)
Theorem eventually_b :
  state_pred init ∧ □ ⟨next⟩ ∧ weak_fairness ab ⊢
  ◇ (state_pred (λ s, s.(x) = B)).
Proof.
  rewrite -> a_leads_to_b.
  rewrite -> init_a.
  rewrite -> leads_to_apply.
  reflexivity.
Qed.

Theorem b_leads_to_c :
  □ ⟨ next ⟩ ∧ weak_fairness bc ⊢
  leads_to (state_pred (λ s, s.(x) = B)) (state_pred (λ s, s.(x) = C)).
Proof.
  apply wf1.
  - unseal.  stm.
  - unseal.  stm.
  - apply state_pred_impl => s.  stm.
Qed.

Theorem a_leads_to_c :
  □ ⟨ next ⟩ ∧ weak_fairness ab ∧ weak_fairness bc ⊢
  state_pred (λ s, s.(x) = A) ~~> state_pred (λ s, s.(x) = C).
Proof.
  rewrite <- (leads_to_trans _ (state_pred (λ s, s.(x) = B))).
  rewrite <- a_leads_to_b.
  rewrite <- b_leads_to_c.
  tla_prop.
Qed.

Theorem eventually_c :
  state_pred init ∧ □ ⟨next⟩ ∧ weak_fairness ab ∧ weak_fairness bc ⊢
  ◇ (state_pred (λ s, s.(x) = C)).
Proof.
  rewrite -> a_leads_to_c.
  rewrite -> init_a.
  rewrite -> leads_to_apply.
  reflexivity.
Qed.

End example.
