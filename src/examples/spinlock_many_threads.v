(*|

====================================================
Example: Spinlock with arbitrary number of threads
====================================================

This example is analogous to the spinlock_, but with an arbitrary number of threads rather than just two.

.. _spinlock: https://tchajed.github.io/coq-tla/examples/spinlock.html

|*)

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import gmap.

From TLA Require Import logic.

Module spec.

  (* program counter *)
  Inductive Pc := pc0 | pc1 | pc2.
  Definition Tid := nat.

  Implicit Types (pc: Pc) (tid: Tid).

  #[global]
  Instance pc_dec : EqDecision Pc.
  Proof. solve_decision. Defined.

  #[global]
  Instance tid_dec : EqDecision Tid.
  Proof. solve_decision. Defined.

  #[global]
  Instance tid_countable : Countable Tid := _.

  (* The state consists of the state of the mutex, and a program counter for
  each thread. The initial domain of the pcs map determines the number of
  threads.  *)
  Record state :=
    mkState { lock: bool; pcs: gmap Tid Pc; }.

  #[global]
  Instance _eta : Settable _ := settable! mkState <lock; pcs>.

  Definition cas_fail (t0: Tid): action state :=
    λ s s', (s.(pcs) !! t0 = Some pc0 ∧ s.(lock) = true)
            ∧ s' = s.

  Definition cas_succ (t0: Tid): action state :=
    λ s s', s.(pcs) !! t0 = Some pc0 ∧ s.(lock) = false
            ∧ s' = s <|lock := true|>
                     <|pcs ::= <[ t0 := pc1 ]> |>.

  Definition unlock (t0: Tid): action state :=
    λ s s', s.(pcs) !! t0 = Some pc1
            ∧ s' = s <|lock := false|>
                     <|pcs ::= <[ t0 := pc2 ]> |>.

  Definition step (t0: Tid): action state :=
      λ s s', cas_fail t0 s s' ∨ cas_succ t0 s s' ∨ unlock t0 s s'.

  Definition init: state → Prop :=
    λ s, s.(lock) = false ∧ ∀ tid pc, s.(pcs) !! tid = Some pc → pc = pc0.

  Definition next : action state :=
    λ s s', (∃ tid, step tid s s') ∨ s' = s.

  (* safety is mutual exclusion *)
  Definition safe: state → Prop :=
    λ s, ∀ tid tid',
    s.(pcs) !! tid = Some pc1 →
    s.(pcs) !! tid' = Some pc1 →
    tid = tid'.

  Definition fair: predicate state :=
    ∀ tid, weak_fairness (step tid).

  (* liveness means all threads have terminated *)
  Definition terminated: state → Prop :=
    λ s, ∀ tid pc, s.(pcs) !! tid = Some pc → pc = pc2.

End spec.

Import spec.

Section example.

Implicit Types (s: state) (t: Tid).

Hint Unfold init next step safe fair terminated : stm.
Hint Unfold cas_fail cas_succ unlock : stm.

Lemma enabled_thread t :
  enabled (step t) = λ s, ∃ pc, s.(pcs) !! t = Some pc ∧ pc ≠ pc2.
Proof.
  apply pred_ext => s.
  unfold enabled; split.
  - autounfold with stm. intros [s' Hstep];
      intuition (subst; eauto; congruence).
  - intros [pc [Hlookup Hne]].
    autounfold with stm.
    destruct s as [l pcs0]; simpl in *.
    destruct pc; [ | | congruence ].
    * destruct l; simpl; eexists (mkState _ _); eauto.
    * eexists (mkState _ _); eauto.
Qed.

Ltac lookup_simp :=
  subst;
  repeat
    match goal with
    | H: _ |- _ => rewrite lookup_insert in H
    | H: _ |- _ => rewrite -> lookup_insert_ne in H by congruence
    | _ => rewrite lookup_insert
    | _ => rewrite -> lookup_insert_ne by congruence
    end;
  try congruence.

Ltac stm_simp :=
  autounfold with stm;
  intros; (intuition (repeat deex; subst; trivial));
  rewrite ?enabled_eq ?enabled_thread;
  repeat deex;
  repeat (match goal with
        | s: state |- _ => (destruct s; cbn in * )
        | H: ?x = ?x |- _ => clear H
        | H: @eq Pc _ _ |- _ => solve [ inversion H ]
        | H: @eq state (mkState _ _) (mkState _ _) |- _ =>
            inversion H; subst; clear H; cbn in *
        | H: context[@set state _ _ _ _ _] |- _ =>
            progress (unfold set in H; simpl in H)
        | H: @eq bool _ _ |- _ => solve [ inversion H ]
        | _ => progress (unfold set; simpl)
        | _ => progress lookup_simp
        | _ => progress cbn in *
        end).

Ltac stm :=
  stm_simp;
  try solve [ intuition (repeat deex; eauto) ];
  try congruence.

Definition exclusion_inv: state → Prop :=
  λ s, (∀ tid, s.(pcs) !! tid = Some pc1 → s.(lock)) ∧
       safe s.

Hint Unfold exclusion_inv : stm.

Lemma exclusion_inv_ok :
  ⌜init⌝ ∧ □⟨next⟩ ⊢ □⌜exclusion_inv⌝.
Proof.
  apply init_invariant.
  - stm.
    { pose proof (H1 _ _ H); congruence. }
    { pose proof (H1 _ _ H); congruence. }
  - intros [lock pcs] [lock' pcs'].
    stm.
    { intuition stm.
      destruct (decide (tid0 = tid)); lookup_simp.
      eauto. }
    intuition stm.
    * destruct (decide (tid0 = tid)); lookup_simp; eauto.
      destruct (decide (tid = tid')); lookup_simp; eauto.
    * destruct (decide (tid0 = tid)); lookup_simp; eauto.
      destruct (decide (tid = tid')); lookup_simp; eauto.
      exfalso; eauto.
Qed.

Theorem safety :
  ⌜init⌝ ∧ □⟨next⟩ ⊢ □ ⌜safe⌝.
Proof.
  rewrite -> exclusion_inv_ok.
  apply always_impl_proper.
  unseal; stm.
Qed.

(** wrapper for [exclusion_inv_ok] to "upgrade" from a semantics with [next] to
one that incorporates the invariant *)
Lemma add_safety :
  ⌜init⌝ ∧ □⟨next⟩ ⊢
  ⌜init⌝ ∧ □⟨λ s s', next s s' ∧ exclusion_inv s ∧ exclusion_inv s'⟩.
Proof.
  tla_pose (exclusion_inv_ok).
  rewrite combine_preds //.
Qed.

(*|

---------------------
Proving termination
---------------------

Why does this program terminate?

|*)

Theorem gset_wf :
  well_founded  ((⊂) : gset Tid → gset Tid → Prop).
Proof. apply set_wf. Qed.

Definition waiting_set (pcs: gmap Tid Pc) : gset Tid :=
  dom (filter (λ '(tid, pc), pc = pc0) pcs).

Definition not_locked : state → Prop :=
  λ s,
    (∀ tid pc, s.(pcs) !! tid = Some pc → pc ≠ pc1) ∧
    s.(lock) = false.

Definition h (done_tids: gset Tid) : state → Prop :=
  λ s, waiting_set s.(pcs) = done_tids ∧ not_locked s.

Hint Unfold h waiting_set not_locked : stm.

Theorem init_to_h :
  ⌜init⌝ ⊢ ∃ waiting, ⌜h waiting⌝.
Proof.
  unseal. stm. eexists; intuition eauto.
  subst; eauto.
  apply H1 in H; congruence.
Qed.

Theorem h_0_to_terminated :
  ⌜h ∅⌝ ⊢ ⌜terminated⌝.
Proof.
  (* actually waiting_set s.(pcs) = ∅ is sufficient *)
  unseal. stm.
  apply dom_empty_iff_L in H1.

  destruct pc; auto; exfalso; eauto.

  (* contradicts waiting_set empty *)
  pose proof
    (map_filter_empty_not_lookup _ _ tid pc0 H1) as Hnotsome.
  simpl in Hnotsome.
  intuition auto.
Qed.

Lemma fair_step (tid: nat) :
  fair ⊢ weak_fairness (step tid).
Proof.
  unfold fair.
  (* apply doesn't work due to the wrong unification heuristics *)
  refine (forall_apply _ _).
Qed.

Lemma h_decrease (waiting: gset Tid) (t: Tid) :
  t ∈ waiting →
  ⌜init⌝ ∧ □⟨next⟩ ∧ fair ⊢
  ⌜h waiting⌝ ~~>
    ⌜λ s, ∃ waiting' (_: waiting' ⊂ waiting), h waiting' s⌝.
Proof.
  intros Hel.
  (* rewrite <- tla_and_assoc. rewrite -> add_safety. tla_simp. *)

  (* need to go through an intermediate state where lock is held by someone *)
  leads_to_trans (∃ t' (_: t' ∈ waiting), ⌜λ s,
      waiting_set s.(pcs) = waiting ∖ {[t']} ∧
      s.(pcs) !! t' = Some pc1 ∧
      s.(lock) = true⌝)%L.

  - setoid_rewrite -> exist_state_pred. rewrite -> exist_state_pred.
    tla_apply (wf1 (step t)).
    { tla_split; [ tla_assumption | tla_apply fair_step ]. }

Abort.

Lemma eventually_terminate :
  ⌜init⌝ ∧ □⟨next⟩ ∧ fair ⊢ ◇ ⌜terminated⌝.
Proof.
  apply (leads_to_apply ⌜init⌝); [ tla_assumption | ].

  rewrite <- tla_and_assoc. rewrite -> add_safety. tla_simp.

  assert (∀ tid, (fair ⊢ weak_fairness (step tid))%L) as Hfair.
  { intros tid. unfold fair.
    (* apply's unification heuristics don't work here *)
    refine (forall_apply _ _). }

  leads_to_etrans;
    [ apply impl_drop_hyp; apply impl_to_leads_to;
      apply init_to_h
    | ].
  leads_to_etrans;
    [| apply impl_drop_hyp; apply impl_to_leads_to;
       apply h_0_to_terminated
     ].

Abort.

End example.
