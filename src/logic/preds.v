From TLA Require Import defs automation.
From TLA Require Import propositional_ltl modalities.
From TLA Require Import classical.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation action := (action Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action).

(* combining predicates and actions *)

Lemma combine_preds (next: action) (P: Σ → Prop) :
  (□ ⟨ next ⟩ ∧ □ ⌜ P ⌝) == □ ⟨ λ s s', next s s' ∧ P s ∧ P s' ⟩.
Proof.
  unseal.
  intuition eauto.
  - specialize (H k). intuition auto.
  - specialize (H k). intuition auto.
Qed.

Theorem add_safety {init: predicate} {next: action} {fair: predicate}
  {inv: Σ → Prop} {φ: predicate} :
  (init ∧ □⟨next⟩ ∧ fair ⊢ □⌜inv⌝) →
  (init ∧ □⟨λ s s', next s s' ∧ inv s ∧ inv s'⟩ ∧ fair ⊢ φ) →
  (init ∧ □⟨next⟩ ∧ fair ⊢ φ).
Proof.
  intros Hinv Hφ.
  tla_pose Hinv.
  (* this is the nasty associative-commutative rewriting this theorem avoids *)
  rewrite (tla_and_comm fair).
  rewrite -(tla_and_assoc (□⟨next⟩)).
  rewrite combine_preds.
  auto.
Qed.

Lemma combine_state_preds (P Q: Σ → Prop) :
  (⌜P⌝ ∧ ⌜Q⌝) == ⌜λ s, P s ∧ Q s⌝.
Proof.
  unseal.
Qed.

Lemma combine_or_preds (P Q: Σ → Prop) :
  (⌜P⌝ ∨ ⌜Q⌝) == ⌜λ s, P s ∨ Q s⌝.
Proof.
  unseal.
Qed.

Lemma combine_or_actions a1 a2 :
  (⟨a1⟩ ∨ ⟨a2⟩) == ⟨λ s s', a1 s s' ∨ a2 s s'⟩.
Proof.
  unseal.
Qed.

Lemma combine_always_preds (P Q: Σ → Prop) :
  (□⌜P⌝ ∧ □⌜Q⌝) == □⌜λ s, P s ∧ Q s⌝.
Proof.
  rewrite -always_and.
  rewrite combine_state_preds.
  reflexivity.
Qed.

Lemma not_state_pred (P: Σ → Prop) :
  !⌜λ s, P s⌝ == ⌜λ s, ¬ P s⌝.
Proof.
  unseal.
Qed.

Theorem enabled_or a1 a2 :
  ∀ s, enabled (λ s s', a1 s s' ∨ a2 s s') s ↔ (enabled a1 s ∨ enabled a2 s).
Proof.
  unfold enabled.
  intuition (repeat deex; eauto).
  intuition eauto.
Qed.

Theorem tla_enabled_or a1 a2 :
  tla_enabled (λ s s', a1 s s' ∨ a2 s s')%type ==
  (tla_enabled a1 ∨ tla_enabled a2).
Proof.
  apply predicate_ext => e.
  rewrite /tla_enabled; tla_simp.
  rewrite enabled_or; tla_simp.
Qed.

Lemma action_to_enabled a :
  ⟨a⟩ ⊢ tla_enabled a.
Proof.
  rewrite /tla_enabled /enabled.
  unseal.
Qed.

Lemma not_enabled_to_action a :
  !tla_enabled a ⊢ !⟨a⟩.
Proof.
  apply not_impl. tla_simp.
  apply action_to_enabled.
Qed.

Lemma state_pred_impl (P Q: Σ -> Prop) :
  (∀ s, P s → Q s) →
  state_pred P ⊢ state_pred Q.
Proof.
  unseal.
Qed.

Lemma enabled_eq (P: Σ → Prop) (f: Σ → Σ) :
  enabled (λ s s', P s ∧ s' = f s) = P.
Proof.
  apply pred_ext => s.
  rewrite /enabled.
  intuition (try deex; eauto).
  intuition.
Qed.

Lemma action_preserves_inv (P: Σ → Prop) a :
    (∀ s s', P s → a s s' → P s') →
    state_pred P ∧ ⟨a⟩ ⊢ later (state_pred P).
Proof.
  unseal.
Qed.

Lemma exist_state_pred {A} (P: A → Σ → Prop) :
  (∃ x, ⌜P x⌝) == ⌜λ s, ∃ x, P x s⌝.
Proof. unseal. Qed.

Lemma forall_state_pred {A} (P: A → Σ → Prop) :
  (∀ x, ⌜P x⌝) == ⌜λ s, ∀ x, P x s⌝.
Proof. unseal. Qed.

End TLA.

Hint Rewrite not_state_pred combine_or_preds combine_state_preds : tla.
