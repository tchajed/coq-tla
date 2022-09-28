From TLA Require Import defs automation logic.

Section lib.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).
Implicit Types (n m k: nat).

Lemma wf1 (p q: predicate) (next a: Σ → Σ → Prop) :
  (⊢ p ∧ ⟨next⟩ → later p ∨ later q) →
  (⊢ p ∧ ⟨next⟩ ∧ ⟨a⟩ → later q) →
  (⊢ p → enabled a) →
  (⊢ □ ⟨next⟩ ∧ weak_fairness a → p ~~> q).
Proof.
  intros H1 H2 H3.
  rewrite weak_fairness_alt1'.
  autounfold with tla in *.
  setoid_rewrite drop_n.
  simpl.
  intros e [Hlater Hwf].
  intros k Hp.
  setoid_rewrite drop_drop.
  rewrite /weak_fairness in Hwf; autounfold with tla in Hwf.
  repeat setoid_rewrite drop_drop in Hwf.
  setoid_rewrite drop_n in Hwf; simpl in Hwf.
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

Theorem always_happy :
  state_pred init ∧ □ ⟨next⟩ ⊢ □ (state_pred (λ s, s.(happy))).
Proof.
  apply (init_safety _ _ (state_pred (λ s, s.(happy))) _).
  - apply state_pred_impl.

    (* SM reasoning *)
    rewrite /init /happy; intuition eauto.
  - apply action_preserves_inv => s s'.

    (* SM reasoning *)
    rewrite /happy /next /ab /bc.
    destruct s, s'; simpl.
    intuition (subst; auto).
    congruence.
  - reflexivity.
Qed.

Theorem a_leads_to_b :
  □ ⟨ next ⟩ ∧ weak_fairness ab ⊢
  state_pred (λ s, s.(x) = A) ~~> state_pred (λ s, s.(x) = B).
Proof.
  apply wf1.
  - unseal.
    intuition auto.
    rewrite /next in H1.
    rewrite /ab /bc in H1.
    intuition (eauto; try congruence).
  - unseal.
    rewrite /ab; intuition eauto.
  - apply state_pred_impl.
    rewrite /ab.
    intuition eauto.
    exists {| x := B; happy := happy s |}; simpl.
    auto.
Qed.

Lemma init_a :
  state_pred init ⊢ state_pred (λ s, s.(x) = A).
Proof.
  apply state_pred_impl.
  rewrite /init; tauto.
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
