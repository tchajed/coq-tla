From Coq.Logic Require Import
  PropExtensionality FunctionalExtensionality
  Classical_Prop Classical_Pred_Type.
From Coq.ssr Require Import ssreflect.
From Coq Require Import Lia.

From stdpp Require Import base.

Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]
  | [ H: _ ∧ _ |- _ ] => destruct H
  | _ => subst
  end.

Module classical_logic.

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

  Lemma prop_not_or (P Q: Prop) : ~(P ∨ Q) ↔ (~P) ∧ (~Q).
  Proof.
    tauto.
  Qed.

  Lemma prop_not_and (P Q: Prop) : ~(P ∧ Q) ↔ (~P) ∨ (~Q).
  Proof.
    tauto.
  Qed.

End classical_logic.

Import classical_logic.

Section TLA.

Context {Σ: Type}.

Definition exec := nat → Σ.
Definition predicate := exec → Prop.

Implicit Types (e: exec) (p q: predicate).
Implicit Types (n m k: nat).

Lemma predicate_ext p1 p2 : (∀ e, p1 e ↔ p2 e) → p1 = p2.
Proof.
  intros H.  extensionality e.  apply propositional_extensionality.
  auto.
Qed.

Declare Scope tla.
Delimit Scope tla with L.
Bind Scope tla with predicate.

Definition valid p := ∀ e, p e.
Notation "⊢  p" := (valid p%L) (at level 99, p at level 200).

Definition pred_impl (p q: predicate) :=
  ∀ e, p e → q e.

Notation "p  ⊢  q" := (pred_impl p%L q%L) (at level 100).

#[global]
Instance pred_impl_reflexive : Reflexive pred_impl.
Proof. compute; intuition auto. Qed.

Instance pred_impl_trans : Transitive pred_impl.
Proof. compute; intuition auto. Qed.

Definition tla_not p : predicate := λ e, ¬ p e.
Notation "!  p" := (tla_not p%L) (at level 51, right associativity) : tla.

Definition tla_or p1 p2 : predicate := λ e, p1 e ∨ p2 e.
Notation "p  ∨  q" := (tla_or p%L q%L) : tla.

Definition tla_and p1 p2 : predicate := λ e, p1 e ∧ p2 e.
Notation "p  ∧  q" := (tla_and p%L q%L) : tla.

Definition tla_implies p1 p2 : predicate := λ e, p1 e → p2 e.
Notation "p  →  q" := (tla_implies p%L q%L) : tla.
Notation "p  ->  q" := (tla_implies p%L q%L) : tla.

Theorem pred_impl_as_valid p q :
  (p ⊢ q) ↔ (⊢ (p → q)).
Proof. reflexivity. Qed.


Definition drop k e : exec := λ n, e (n + k).

Lemma drop_drop k1 k2 e : drop k1 (drop k2 e) = drop (k1 + k2) e.
Proof.
  extensionality n.  rewrite /drop.
  f_equal; lia.
Qed.

Lemma drop_0 e : drop 0 e = e.
Proof.
  extensionality n. rewrite /drop.
  f_equal; lia.
Qed.

Definition always p : predicate := λ e, ∀ k, p (drop k e).
Notation "□  p" := (always p%L) (at level 51, right associativity) : tla.

Definition eventually p : predicate := λ e, ∃ k, p (drop k e).
Notation "◇  p" := (eventually p%L) (at level 51, right associativity) : tla.

(* This serves the rule of the "prime" in TLA, but with a more general and
formal definition than TLA, which seems to only use them in actions and does not
treat it as a full-fledged modality. *)
Definition next p : predicate := λ e, p (drop 1 e).

(* this is just to force parsing in tla scope *)
Notation "p == q" := (@eq predicate p%L q%L) (at level 70, only parsing).

Lemma equiv_to_impl p q :
  (p ⊢ q) → (q ⊢ p) → (p == q).
Proof.
  intros H1 H2.
  apply predicate_ext => e.
  intuition eauto.
Qed.

Hint Unfold tla_and tla_or tla_not tla_implies eventually always next : tla.
Hint Unfold valid pred_impl : tla.

Local Ltac instance_t :=
  rewrite /Proper /respectful /Basics.flip /Basics.impl /pred_impl;
  autounfold with tla;
  try solve [ intuition (deex; eauto) ].

Global Instance implies_impl_proper :
  Proper (Basics.flip pred_impl ==> pred_impl ==> pred_impl) tla_implies.
Proof.  instance_t.  Qed.

Global Instance implies_impl_flip_proper :
  Proper (pred_impl ==> flip pred_impl ==> flip pred_impl) tla_implies.
Proof.  instance_t.  Qed.

Global Instance and_impl_proper :
  Proper (pred_impl ==> pred_impl ==> pred_impl) tla_and.
Proof. instance_t. Qed.

Global Instance and_impl_flip_proper :
  Proper (flip pred_impl ==> flip pred_impl ==> flip pred_impl) tla_and.
Proof. instance_t. Qed.

Global Instance and_impl_proper' p :
  Proper (pred_impl ==> pred_impl) (tla_and p).
Proof. apply and_impl_proper. reflexivity. Qed.

Global Instance or_impl_proper :
  Proper (pred_impl ==> pred_impl ==> pred_impl) tla_or.
Proof. instance_t. Qed.

Global Instance eventually_impl_proper :
  Proper (pred_impl ==> pred_impl) eventually.
Proof.  instance_t. Qed.

Global Instance always_impl_proper :
  Proper (pred_impl ==> pred_impl) always.
Proof.  instance_t. Qed.

Global Instance next_impl_proper :
  Proper (pred_impl ==> pred_impl) next.
Proof.  instance_t. Qed.

Global Instance pred_impl_proper :
  Proper (Basics.flip pred_impl ==> pred_impl ==> Basics.impl) pred_impl.
Proof. instance_t. Qed.

Global Instance pred_flip_impl_proper :
  Proper (pred_impl ==> Basics.flip pred_impl ==> Basics.flip impl) pred_impl.
Proof. instance_t. Qed.

Global Instance impl_valid :
  Proper (pred_impl ==> impl) valid.
Proof. instance_t. Qed.

Global Instance impl_flip_valid :
  Proper (flip pred_impl ==> flip impl) valid.
Proof. instance_t. Qed.

Ltac unseal :=
  lazymatch goal with
  | |- @eq predicate _ _ =>
    apply predicate_ext => e
  | _ => idtac
  end;
  autounfold with tla;
  try tauto;
  repeat setoid_rewrite drop_drop;
  repeat lazymatch goal with
  | |- (∀ (e: exec), _) => intro e
  | |- (∀ (n: _), _) => let n := fresh n in intro n
  | |- _ → _ => let H := fresh "H" in intro H
  end;
  eauto.

Theorem not_eventually p :
  ! ◇p == □ !p.
Proof.
  unseal.
  rewrite not_exists //.
Qed.

Theorem not_always p :
  ! □p == ◇ !p.
Proof.
  unseal.
  rewrite not_forall //.
Qed.

Lemma not_not p :
  (! ! p) == p.
Proof.  unseal.  Qed.

Lemma not_inj p q :
  !p == !q →
  p = q.
Proof.
  intros H.
  rewrite  -(not_not p) -(not_not q).
  rewrite H //.
Qed.

Lemma not_or p1 p2 :
  !(p1 ∨ p2) == (!p1 ∧ !p2).
Proof.  unseal.  Qed.

Lemma not_and p1 p2 :
  !(p1 ∧ p2) == (!p1 ∨ !p2).
Proof.  unseal.  Qed.

Lemma implies_to_or p1 p2 :
  (p1 → p2) == (!p1 ∨ p2).
Proof.  unseal.  Qed.

Lemma not_implies p1 p2 :
  !(p1 → p2) == (p1 ∧ !p2).
Proof.  unseal.  Qed.

Hint Rewrite not_eventually not_always
  not_and not_or not_not not_implies : tla.

Ltac tla_simp := autorewrite with tla; try reflexivity.

Ltac dual0 :=
  apply not_inj; tla_simp.

Tactic Notation "dual" := dual0.
Tactic Notation "dual" constr(lem) := dual0; rewrite lem; done.

Theorem eventually_to_always p :
  ◇ p == ! (□ (! p)).
Proof.
  tla_simp.
Qed.

Theorem always_to_eventually p :
  □ p == ! (◇ (! p)).
Proof.
  tla_simp.
Qed.

Theorem always_idem p :
  □ □ p == □ p.
Proof.
  unseal.
  split.
  - intros H k.
    specialize (H k 0).
    rewrite //= in H.
  - intuition auto.
Qed.

Theorem eventually_idem p :
  ◇ ◇ p == ◇ p.
Proof.
  dual always_idem.
Qed.

Hint Rewrite always_idem eventually_idem : tla.

Theorem and_idem p :
  (p ∧ p) == p.
Proof.  unseal.  Qed.

Theorem or_idem p :
  (p ∨ p) == p.
Proof.  unseal.  Qed.

Theorem tla_and_assoc p1 p2 p3 :
  ((p1 ∧ p2) ∧ p3) == (p1 ∧ p2 ∧ p3).
Proof. unseal. Qed.

Theorem tla_or_assoc p1 p2 p3 :
  ((p1 ∨ p2) ∨ p3) == (p1 ∨ p2 ∨ p3).
Proof. unseal. Qed.

Hint Rewrite tla_and_assoc : tla.
Hint Rewrite tla_or_assoc : tla.

Theorem always_intro p :
  (⊢ p) ↔ ⊢ □ p.
Proof.
  unseal.
  split; intros H e; [ by eauto | ].
  specialize (H e 0).
  rewrite drop_0 // in H.
Qed.

Theorem implies_generalize p1 p2 :
  (⊢ p1 → p2) → (⊢ □ p1 → □ p2).
Proof.
  unfold valid; autounfold with tla.
  eauto.
Qed.

Theorem always_and p1 p2 :
  □(p1 ∧ p2) == (□p1 ∧ □ p2).
Proof.
  unseal.
  intuition eauto.
  - destruct (H k); auto.
  - destruct (H k); auto.
Qed.

Theorem next_and p1 p2 :
  next (p1 ∧ p2) == (next p1 ∧ next p2).
Proof.
  unseal.
Qed.

Theorem next_or p1 p2 :
  next (p1 ∨ p2) == (next p1 ∨ next p2).
Proof.
  unseal.
Qed.

Theorem eventually_or p1 p2 :
  ◇(p1 ∨ p2) == (◇p1 ∨ ◇ p2).
Proof.
  dual always_and.
Qed.

Theorem always_eventually_distrib p1 p2 :
  □◇ (p1 ∨ p2) == ((□◇ p1) ∨ (□◇ p2)).
Proof.
  unseal.
  split.
  - intros H.
    apply NNPP.
    rewrite prop_not_or !not_forall.
    setoid_rewrite not_exists.
    intros H1.
    destruct H1 as [[x1 Hnot1] [x2 Hnot2]].
    destruct (H (Nat.max x1 x2)) as [k H1or2].
    destruct H1or2 as [H1|H2].
    { apply (Hnot1 (k + Nat.max x1 x2 - x1)).
      assert (k + Nat.max x1 x2 - x1 + x1 = k + Nat.max x1 x2) by lia.
      congruence. }
    { apply (Hnot2 (k + Nat.max x1 x2 - x2)).
      assert (k + Nat.max x1 x2 - x2 + x2 = k + Nat.max x1 x2) by lia.
      congruence. }
  - intros [H|H]; intros k.
    + destruct (H k) as [k' ?]; eauto.
    + destruct (H k) as [k' ?]; eauto.
Qed.

Theorem eventually_always_distrib p1 p2 :
  ◇□ (p1 ∧ p2) == ((◇□ p1) ∧ (◇□ p2)).
Proof.
  dual always_eventually_distrib.
Qed.

Lemma always_eventually_reverse p :
  □◇ p == ! ◇□ !p.
Proof.
  autorewrite with tla; done.
Qed.

Lemma eventually_always_reverse p :
  ◇□ p == ! □◇ !p.
Proof.
  autorewrite with tla; done.
Qed.

Theorem always_eventually_idem p :
  □ ◇ □ ◇ p == □ ◇ p.
Proof.
  unseal.
  repeat setoid_rewrite drop_drop.
  split.
  - intros H k.
    specialize (H k).
    destruct H as [k' H].
    specialize (H 0).
    destruct H as [k'' H].
    eauto.
  - intros H k.
    exists 0. intros k'.
    destruct (H (k + k')) as [k'' H'].
    exists k''.
    replace (k'' + k' + 0 + k) with (k'' + (k + k')) by lia.
    done.
Qed.

Theorem eventually_always_idem p :
  ◇ □ ◇ □ p == ◇ □ p.
Proof.
  dual always_eventually_idem.
Qed.

Hint Rewrite always_eventually_idem eventually_always_idem : tla.

Theorem entails_and_iff p q1 q2 :
  ((p ⊢ q1) ∧ (p ⊢ q2)) ↔ (p ⊢ q1 ∧ q2).
Proof.
  unseal.
  intuition eauto.
  - apply H; done.
  - apply H; done.
Qed.

Theorem entails_and p q1 q2 :
  (p ⊢ q1) →
  (p ⊢ q2) →
  (p ⊢ q1 ∧ q2).
Proof.
  rewrite -entails_and_iff //.
Qed.

Theorem always_weaken p :
  □ p ⊢ p.
Proof.
  unseal.
  specialize (H 0).
  rewrite drop_0 // in H.
Qed.

Theorem always_to_next p :
  □ p ⊢ next p.
Proof.
  unseal.
Qed.

Theorem next_to_eventually p :
  next p ⊢ ◇ p.
Proof.
  unseal.
Qed.

Theorem always_expand p :
  □ p == (p ∧ □ p).
Proof.
  rewrite -{1}(and_idem p).
  rewrite always_and.
  unseal.
  intuition eauto.
  specialize (H0 0).
  rewrite drop_0 in H0; eauto.
Qed.

Lemma add_1_succ (n: nat) : n + 1 = S n.
Proof. lia. Qed.

Theorem always_unroll p :
  □ p == (p ∧ next (□ p)).
Proof.
  apply equiv_to_impl; unseal.
  { intuition eauto.
    rewrite -(drop_0 e) //. }
  intuition eauto.
  setoid_rewrite add_1_succ in H1.
  destruct k.
  { rewrite drop_0 //. }
  { eauto. }
Qed.

Theorem next_always p :
  □ p ⊢ next (□ p).
Proof.
  rewrite -> always_unroll at 1.
  unseal.
Qed.

Theorem next_eventually p :
  (p ∨ next (◇ p)) == ◇ p.
Proof.
  unseal.
  intuition (deex; eauto).
  { exists 0; rewrite drop_0 //. }
  setoid_rewrite add_1_succ.
  destruct k; eauto.
  rewrite drop_0 in H; auto.
Qed.

Theorem next_eventually_weaken p :
  next (◇ p) ⊢ ◇ p.
Proof.
  rewrite <- next_eventually at 2.
  unseal.
Qed.

(* the induction principle from the TLA paper *)
Theorem next_induction (n inv: predicate) :
  (inv ∧ n ⊢ next inv) →
  (inv ∧ □n ⊢ □inv).
Proof.
  unseal.
  destruct H0 as [Hinit Hn].
  induction k.
  - rewrite drop_0 //.
  - change (S k) with (1 + k).
    rewrite -drop_drop.
    apply H; eauto.
Qed.

Theorem init_safety (init n inv safe : predicate) :
  (init ⊢ inv) →
  (inv ∧ n ⊢ next inv) →
  (inv ⊢ safe) →
  ⊢ init ∧ □ n → □ safe.
Proof.
  intros Hinit Hnext Hsafe.
  rewrite <- Hsafe.
  rewrite -> Hinit.
  apply next_induction.
  auto.
Qed.

(* This is a more general induction principle _internal_ to the logic. It's
different from `next_induction` because it requires the implication only for the
"current" execution. *)
Theorem next_induction_internal (n inv: predicate) :
  ⊢ □(inv ∧ n → next inv) → (inv ∧ □n → □inv).
Proof.
  unseal.
  destruct H0 as [Hinit Hn].
  induction k.
  - rewrite drop_0 //.
  - change (S k) with (1 + k).
    apply H; eauto.
Qed.

Definition state_pred (f: Σ → Prop) : predicate :=
    λ ex, f (ex 0).

Definition action := Σ → Σ → Prop.

Implicit Types (a: action).

Definition action_pred a : predicate :=
    λ ex, a (ex 0) (ex 1).

Notation "⟨ a ⟩" := (action_pred a).

Definition enabled a : predicate :=
  state_pred (λ s, ∃ s', a s s').

Definition weak_fairness a : predicate :=
    □ (□ (enabled a) → (◇ ⟨a⟩)).

Theorem weak_fairness_alt1 a :
  weak_fairness a == □ ◇ (! (enabled a) ∨ □ ◇ ⟨a⟩).
Proof.
  unfold weak_fairness.
  rewrite implies_to_or.
  tla_simp.
  rewrite -!eventually_or.
  rewrite !always_eventually_distrib.
  tla_simp.
Qed.

Theorem weak_fairness_alt2 a :
  weak_fairness a == (◇ □ (enabled a) → □ ◇ ⟨a⟩).
Proof.
  rewrite weak_fairness_alt1.
  rewrite implies_to_or.
  tla_simp.
  rewrite always_eventually_distrib.
  tla_simp.
Qed.

End TLA.
