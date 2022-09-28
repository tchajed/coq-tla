From TLA Require Import defs classical automation logic.

Section example.

Inductive abc := A | B | C.
Record state :=
  { x: abc; happy: bool; }.

Implicit Types (s: state).

Definition ab : action state :=
  λ s s', (s.(x) = A ∧ s'.(x) = B ∧ s'.(happy) = s.(happy)).

Definition bc : action state :=
  λ s s', (s.(x) = B ∧ s'.(x) = C ∧ s'.(happy) = s.(happy)).

Definition next s s' :=
  ab s s' ∨ bc s s' ∨ s = s'.

Definition init (s: state) : Prop := s.(x) = A ∧ s.(happy).

Hint Unfold init happy next ab bc : stm.

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

Theorem always_happy :
  state_pred init ∧ □ ⟨next⟩ ⊢ □ (state_pred (λ s, s.(happy))).
Proof.
  apply (init_safety _ _ (state_pred (λ s, s.(happy))) _).
  - apply state_pred_impl => s.  stm.
  - apply action_preserves_inv => s s'.  stm.
  - reflexivity.
Qed.

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
