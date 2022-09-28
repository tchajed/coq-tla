From TLA Require Import defs automation logic.

(* TODO: move to library *)
#[global] Hint Unfold state_pred action_pred : tla.

(* TODO: rename `next` to something else (maybe prime) *)

Section lib.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).
Implicit Types (n m k: nat).

Lemma state_pred_impl (p q: Σ -> Prop) :
  (∀ s, p s → q s) →
  state_pred p ⊢ state_pred q.
Proof.
  unseal.
Qed.

Lemma action_preserves_inv (p: Σ → Prop) (a: action Σ) :
    (∀ s s', p s → a s s' → p s') →
    state_pred p ∧ ⟨a⟩ ⊢ next (state_pred p).
Proof.
  intros H.
  unseal.
Admitted.

Definition leads_to (p q: predicate) : predicate :=
  □ (p → ◇ q).

Lemma drop_n (e: exec) (k n: nat) :
  drop k e n = e (n + k).
Proof.  reflexivity. Qed.

Hint Rewrite drop_n : tla.

Hint Unfold leads_to : tla.

Lemma wf1 (p q: predicate) (Next a: Σ → Σ → Prop) :
  (⊢ p ∧ ⟨Next⟩ → next p ∨ next q) →
  (⊢ p ∧ ⟨Next⟩ ∧ ⟨a⟩ → next q) →
  (⊢ p → enabled a) →
  (⊢ □ ⟨Next⟩ ∧ weak_fairness a → leads_to p q).
Proof.
  intros H1 H2 H3.
  rewrite weak_fairness_alt1'.
  autounfold with tla in *.
  setoid_rewrite drop_n.
  simpl.
  intros e [Hnext Hwf].
  intros k Hp.
  setoid_rewrite drop_drop.
  rewrite /weak_fairness in Hwf; autounfold with tla in Hwf.
  repeat setoid_rewrite drop_drop in Hwf.
  setoid_rewrite drop_n in Hwf; simpl in Hwf.
Admitted.

Lemma modus_ponens (p q: predicate) :
  (p ∧ (p → q)) ⊢ q.
Proof.
  unseal.
Qed.

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

Definition Next s s' :=
  ab s s' ∨ bc s s' ∨ s = s'.

Definition init (s: state) : Prop := s.(x) = A ∧ s.(happy).

Theorem always_happy :
  state_pred init ∧ □ ⟨Next⟩ ⊢ □ (state_pred (λ s, s.(happy))).
Proof.
  apply (init_safety _ _ (state_pred (λ s, s.(happy))) _).
  - apply state_pred_impl.

    (* SM reasoning *)
    rewrite /init /happy; intuition eauto.
  - apply action_preserves_inv => s s'.

    (* SM reasoning *)
    rewrite /happy /Next /ab /bc.
    destruct s, s'; simpl.
    intuition (subst; auto).
    congruence.
  - reflexivity.
Qed.

Theorem a_leads_to_b :
  □ ⟨ Next ⟩ ∧ weak_fairness ab ⊢
  leads_to (state_pred (λ s, s.(x) = A)) (state_pred (λ s, s.(x) = B)).
Proof.
  apply wf1.
  - unseal; rewrite /drop /=.
    generalize dependent (e 0); intros s.
    generalize dependent (e 1); intros s'.
    clear e.
    intuition auto.
    rewrite /Next in H1.
    rewrite /ab /bc in H1.
    intuition (eauto; try congruence).
  - unseal; rewrite /drop /=.
    generalize dependent (e 0); intros s.
    generalize dependent (e 1); intros s'.
    clear e.
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
  state_pred init ∧ □ ⟨Next⟩ ∧ weak_fairness ab ⊢
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
  □ ⟨ Next ⟩ ∧ weak_fairness bc ⊢
  leads_to (state_pred (λ s, s.(x) = B)) (state_pred (λ s, s.(x) = C)).
Proof.
Admitted.

Theorem a_leads_to_c :
  □ ⟨ Next ⟩ ∧ weak_fairness ab ∧ weak_fairness bc ⊢
  leads_to (state_pred (λ s, s.(x) = A)) (state_pred (λ s, s.(x) = C)).
Proof.
Admitted.

Theorem eventually_c :
  state_pred init ∧ □ ⟨Next⟩ ∧ weak_fairness ab ∧ weak_fairness bc ⊢
  ◇ (state_pred (λ s, s.(x) = C)).
Proof.
Admitted.

End example.
