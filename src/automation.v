From Coq.Logic Require Import
  FunctionalExtensionality.

From Coq Require Export Lia.

From TLA Require Import defs.
From TLA Require Import classical.

(** This file develops the core automation for proving TLA properties. *)

Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]
  | [ H: _ ∧ _ |- _ ] => destruct H
  | _ => subst
  end.

#[export]
Hint Unfold tla_and tla_or tla_not tla_implies eventually always later : tla.
#[export]
Hint Unfold valid pred_impl : tla.

(*|
The instances below enable rewriting by predicate implications, even inside
formulae. For example we can use H: p ⊢ q (pred_impl p q) as [rewrite H] to
change [p ∧ r ⊢ q] to [q ∧ r ⊢ q].
|*)
Section rewriting.

Context [Σ: Type].
Notation pred_impl := (@pred_impl Σ).

Local Ltac instance_t :=
  rewrite /Proper /respectful /Basics.flip /Basics.impl /pred_impl;
  autounfold with tla;
  try solve [ intuition (deex; eauto) ].

Global Instance pred_impl_reflexive : Reflexive pred_impl.
Proof. compute; intuition auto. Qed.

Global Instance pred_impl_trans : Transitive pred_impl.
Proof. compute; intuition auto. Qed.

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

Global Instance later_impl_proper :
  Proper (pred_impl ==> pred_impl) later.
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

End rewriting.


Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate).
Implicit Types (n m k: nat).

Local Ltac unseal :=
  apply predicate_ext => e;
  autounfold with tla;
  try tauto.

Lemma not_not (p: predicate) :
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

Lemma not_impl p q :
  (!p ⊢ !q) →
  q ⊢ p.
Proof.
  autounfold with tla; intuition eauto.
  apply classical.double_negation.
  eauto.
Qed.

Theorem not_eventually p :
  ! ◇p == □ !p.
Proof.
  unseal.
  rewrite classical.not_exists //.
Qed.

Theorem not_always p :
  ! □p == ◇ !p.
Proof.
  unseal.
  rewrite classical.not_forall //.
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

Lemma or_to_implies p1 p2 :
  (p1 ∨ p2) == (!p1 → p2).
Proof. unseal. Qed.

Lemma not_implies p1 p2 :
  !(p1 → p2) == (p1 ∧ !p2).
Proof.  unseal.  Qed.

Lemma state_pred_e (P: Σ → Prop) e :
  state_pred P e ↔ P (e 0).
Proof.
  reflexivity.
Qed.

Lemma action_pred_e (a: action Σ) e :
  ⟨ a ⟩ e ↔ a (e 0) (e 1).
Proof.
  reflexivity.
Qed.

Theorem tla_and_assoc p1 p2 p3 :
  ((p1 ∧ p2) ∧ p3) == (p1 ∧ p2 ∧ p3).
Proof. unseal. Qed.

Theorem entails_to_iff p q :
  (p ⊢ q) →
  (q ⊢ p) →
  p == q.
Proof.
  autounfold with tla; intros.
  apply predicate_ext => e.
  split; eauto.
Qed.

Theorem entails_and_iff p q1 q2 :
  ((p ⊢ q1) ∧ (p ⊢ q2)) ↔ (p ⊢ q1 ∧ q2).
Proof.
  autounfold with tla.
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

Theorem entails_trans p q r :
  (p ⊢ q) →
  (q ⊢ r) →
  (p ⊢ r).
Proof.
  autounfold with tla; intuition auto.
Qed.

Theorem entails_cut p q r :
  (p ⊢ q) →
  (p ∧ q ⊢ r) →
  (p ⊢ r).
Proof.
  autounfold with tla; intuition auto.
Qed.

End TLA.

Hint Rewrite not_eventually not_always
  not_and not_or not_not not_implies : tla.

Hint Rewrite state_pred_e action_pred_e : tla.

#[export]
Hint Unfold state_pred action_pred : tla.

#[export]
Hint Unfold tla_true tla_false : tla.

#[export]
Hint Unfold enabled weak_fairness : tla.

#[export]
Hint Unfold leads_to : tla.

Ltac tla_simp := autorewrite with tla; try reflexivity.

Ltac dual0 :=
  match goal with
  | |- _ = _ => apply not_inj; tla_simp
  | |- pred_impl _ _ => apply not_impl; tla_simp
  end.

Tactic Notation "dual" := dual0.
Tactic Notation "dual" constr(lem) := dual0; rewrite -> lem; done.

Lemma drop_drop {Σ} k1 k2 (e: exec Σ) : drop k1 (drop k2 e) = drop (k1 + k2) e.
Proof.
  extensionality n.  rewrite /drop.
  f_equal; lia.
Qed.

Lemma drop_0 {Σ} (e: exec Σ) : drop 0 e = e.
Proof.
  extensionality n. rewrite /drop.
  f_equal; lia.
Qed.

Lemma drop_n {Σ} (e: exec Σ) (k n: nat) :
  drop k e n = e (n + k).
Proof.  reflexivity. Qed.

Local Ltac specific_states_exec e :=
  repeat match goal with
         | H: context[drop _ _ _] |- _ => setoid_rewrite drop_n in H
         | |- _ => setoid_rewrite drop_n
         end;
  generalize dependent (e 0); intros s;
  generalize dependent (e 1); intros s';
  try clear s';
  clear e.

(* Try to prove a theorem about an execution e for just the first two states, in
order to simplify proving theorems about state_pred and action_pred. *)
Ltac specific_states :=
  lazymatch goal with
  | e: exec _, e': exec _ |- _ => fail "multiple execs to choose from"
  | e: exec _ |- _ => specific_states_exec e
  | _ => fail "no exec variables"
  end.

Ltac unseal :=
  (* cleanup *)
  lazymatch goal with
  | |- @eq (predicate _) _ _ =>
    apply predicate_ext => e
  | _ => idtac
  end;
  autounfold with tla;
  repeat setoid_rewrite drop_drop;
  repeat setoid_rewrite drop_n; simpl;
  repeat lazymatch goal with
  | |- (∀ (e: exec _), _) => intro e
  | |- (∀ (n: ?T), _) =>
    let kind := type of T in
    lazymatch kind with
    | Prop => intro
    | _ => let n := fresh n in intro n
    end
  | |- _ → _ => let H := fresh "H" in intro H
  end;
  try specific_states;
  (* finishing tactics*)
  try tauto;
  try solve [ intuition eauto ].

(* unfold very little, to only use propositional logic *)
Ltac tla_prop :=
  unfold tla_and, tla_or, tla_implies, tla_not, pred_impl, valid;
  intros;
  tauto.

Lemma tla_pose_lemma {Σ} (p1 q1: predicate Σ) :
  (* the lemma to introduce *)
  (p1 ⊢ q1) →
  ∀ (p2 q2: predicate Σ),
  (* side condition to show precondition (to be proved by [tla_prop]) *)
  (p2 ⊢ p1) →
  (* the new goal *)
  (p2 ∧ q1 ⊢ q2) →
  (p2 ⊢ q2).
Proof. unseal. Qed.

Ltac tla_pose lem :=
  let H := fresh "Htemp" in
  epose proof lem as H;
  apply (tla_pose_lemma _ _ H); clear H;
  [ tla_prop | try rewrite tla_and_assoc ].

Ltac tla_split :=
  match goal with
  | |- @eq (predicate _) _ _ => apply entails_to_iff
  | |- pred_impl _ (tla_and _ _) => apply entails_and
  end.

Ltac tla_apply lem :=
  eapply entails_trans; [ | apply lem ]; try solve [ tla_prop ].
