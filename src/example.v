From TLA Require Import defs automation logic.

Section lib.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).
Implicit Types (n m k: nat).

Lemma wf1 (p q: predicate) (next a: Σ → Σ → Prop) :
  ∀ (Hpuntilq: ⊢ p ∧ ⟨next⟩ → later p ∨ later q)
    (Haq: ⊢ p ∧ ⟨next⟩ ∧ ⟨a⟩ → later q)
    (Henable: ⊢ p → enabled a),
  (⊢ □ ⟨next⟩ ∧ weak_fairness a → p ~~> q).
Proof.
  rewrite weak_fairness_alt1'.
  unseal.
Admitted.

End lib.

(* ---------------------------------------  *)

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
  - apply state_pred_impl.

    (* SM reasoning *)
    stm.
  - apply action_preserves_inv => s s'.

    (* SM reasoning *)
    stm.
  - reflexivity.
Qed.

Theorem a_leads_to_b :
  □ ⟨ next ⟩ ∧ weak_fairness ab ⊢
  state_pred (λ s, s.(x) = A) ~~> state_pred (λ s, s.(x) = B).
Proof.
  apply wf1.
  - unseal.
    stm.
  - unseal.
    stm.
  - apply state_pred_impl.
    stm.
Qed.

Lemma init_a :
  state_pred init ⊢ state_pred (λ s, s.(x) = A).
Proof.
  apply state_pred_impl.
  stm.
Qed.

Theorem eventually_b :
  state_pred init ∧ □ ⟨next⟩ ∧ weak_fairness ab ⊢
  ◇ (state_pred (λ s, s.(x) = B)).
Proof.
  rewrite -> a_leads_to_b.
  rewrite -> init_a.
  rewrite /leads_to.
  rewrite -> always_weaken.
  rewrite -> modus_ponens.
  reflexivity.
Qed.

Theorem b_leads_to_c :
  □ ⟨ next ⟩ ∧ weak_fairness bc ⊢
  leads_to (state_pred (λ s, s.(x) = B)) (state_pred (λ s, s.(x) = C)).
Proof.
Admitted.

Theorem a_leads_to_c :
  □ ⟨ next ⟩ ∧ weak_fairness ab ∧ weak_fairness bc ⊢
  state_pred (λ s, s.(x) = A) ~~> state_pred (λ s, s.(x) = C).
Proof.
Admitted.

Theorem eventually_c :
  state_pred init ∧ □ ⟨next⟩ ∧ weak_fairness ab ∧ weak_fairness bc ⊢
  ◇ (state_pred (λ s, s.(x) = C)).
Proof.
Admitted.

End example.
