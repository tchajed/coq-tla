From Coq.Logic Require Import
  Classical_Prop Classical_Pred_Type.

From stdpp Require Import base.

Module classical.

  Lemma not_forall {A: Type} (P: A → Prop) :
    ¬ (∀ x, P x) ↔ (∃ x, ¬ P x).
  Proof.
    split.
    - apply not_all_ex_not.
    - intros [x HP] H.
      eauto.
  Qed.

  Lemma not_exists {A: Type} (P: A → Prop) :
    ¬ (∃ x, P x) ↔ (∀ x, ¬ P x).
  Proof.
    split.
    - apply not_ex_all_not.
    - intros HnotP [x HP].
      eapply HnotP; eauto.
  Qed.

  Lemma double_negation (P: Prop) : (~~P) ↔ P.
  Proof.
    tauto.
  Qed.

  Lemma not_or (P Q: Prop) : ~(P ∨ Q) ↔ (~P) ∧ (~Q).
  Proof.
    tauto.
  Qed.

  Lemma not_and (P Q: Prop) : ~(P ∧ Q) ↔ (~P) ∨ (~Q).
  Proof.
    tauto.
  Qed.

  Lemma excluded_middle (P: Prop) : P ∨ ~P.
    tauto.
  Qed.

End classical.
