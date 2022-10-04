(*|

=============================
Example: (spinlock) Mutex
=============================

This example is a liveness proof for the following simple C program. It encodes the program as a hand-written state machine, with states referring to labeled points.

::

  type Mutex = bool;
  const UNLOCKED = false;
  const LOCKED = true;

  void lock(Mutex *m) {
    // pc0
    for cas(m, UNLOCKED, LOCKED) {}
    // control goes directly to pc1 (see `thread`)
  }

  void unlock(Mutex *m) {
    // pc1
    *m = UNLOCKED;
    // pc2
  }

  void thread(Mutex *m) {
    lock(m);
    unlock(m);
  }

  void main() {
    Mutex *m = malloc(sizeof(Mutex));
    // these two threads are what is modeled
    spawn(thread, m);
    spawn(thread, m);
  }

What we reason about is two threads running `lock(m); unlock(m)` (assuming m starts out allocated).

|*)

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import functions.

From TLA Require Import logic.


Module spec.

  Inductive pc := pc0 | pc1 | pc2.
  Inductive Tid := tid0 | tid1.

  #[global]
  Instance tid_eqdecision : EqDecision Tid.
  Proof.
    solve_decision.
  Defined.

  (* the state consists of the state of the mutex, and program counters for two
  threads, tid0 and tid1 *)
  Record state :=
    mkState { lock: bool; pcs: Tid → pc; }.

  #[global]
  Instance _eta : Settable _ := settable! mkState <lock; pcs>.

  Definition cas_fail (t0: Tid): action state :=
    λ s s', (s.(pcs) t0 = pc0 ∧ s.(lock) = true)
            ∧ s' = s.

  Definition cas_succ (t0: Tid): action state :=
    λ s s', s.(pcs) t0 = pc0 ∧ s.(lock) = false
            ∧ s' = s <|lock := true|>
                     <|pcs ::= <[ t0 := pc1 ]> |>.

  Definition unlock (t0: Tid): action state :=
    λ s s', s.(pcs) t0 = pc1
            ∧ s' = s <|lock := false|>
                     <|pcs ::= <[ t0 := pc2 ]> |>.

  Definition step (t0: Tid): action state :=
      λ s s', cas_fail t0 s s' ∨ cas_succ t0 s s' ∨ unlock t0 s s'.

  Definition init: state → Prop :=
    λ s, s = {| lock := false; pcs := λ _, pc0; |}.

  Definition next : action state :=
    λ s s', step tid0 s s' ∨ step tid1 s s' ∨ s' = s.

  (* safety is mutual exclusion *)
  Definition safe: state → Prop :=
    λ s, ¬ (s.(pcs) tid0 = pc1 ∧ s.(pcs) tid1 = pc1).

  Definition fair: predicate state :=
    weak_fairness (step tid0) ∧ weak_fairness (step tid1).

  (* liveness means both threads terminate *)
  Definition terminated: state → Prop :=
    λ s, s.(pcs) tid0 = pc2 ∧ s.(pcs) tid1 = pc2.

End spec.

Import spec.

Section example.

Implicit Types (s: state) (t: Tid).

Hint Unfold init next step safe fair terminated : stm.

Ltac stm_simp :=
  autounfold with stm;
  intros; (intuition (repeat deex; subst; trivial));
  rewrite ?enabled_eq;
  repeat deex;
  (* TODO: why does this infinite loop? *)
  do 10 (try match goal with
        | s: state |- _ => destruct s; cbn in *
        | H: @eq pc _ _ |- _ => inversion H; subst; clear H
        | H: @eq state (mkState _ _) (mkState _ _) |- _ =>
            inversion H; subst; clear H
        end);
  cbn in *.

Ltac stm :=
  stm_simp;
  try solve [ intuition (repeat deex; eauto) ].

Definition exclusion_inv: state → Prop :=
  λ s, (s.(pcs) tid0 = pc1 → s.(lock) ∧ s.(pcs) tid1 ≠ pc1) ∧
       (s.(pcs) tid1 = pc1 → s.(lock) ∧ s.(pcs) tid0 ≠ pc1).

Hint Unfold exclusion_inv : stm.

Hint Unfold cas_fail cas_succ unlock : stm.

Lemma exclusion_inv_ok :
  ⌜init⌝ ∧ □⟨next⟩ ⊢ □⌜exclusion_inv⌝.
Proof.
  apply init_invariant.
  - stm.
  - stm.
Qed.

Theorem safety :
  ⌜init⌝ ∧ □⟨next⟩ ⊢ □ ⌜safe⌝.
Proof.
  rewrite -> exclusion_inv_ok.
  apply always_impl_proper.
  unseal; stm.
Qed.

Lemma enabled_thread t :
  enabled (step t) = λ s, s.(pcs) t ≠ pc2.
Proof.
  apply pred_ext => s.
  unfold enabled; split.
  - autounfold with stm. intros [s' Hstep];
      (intuition subst);
      try congruence.
  - intros.
    autounfold with stm.
    destruct s as [l pcs0]; simpl in *.
    destruct (pcs0 t) eqn:?; [ | | congruence ].
    * destruct l; simpl; eexists (mkState _ _); eauto.
    * eexists (mkState _ _); eauto.
Qed.

Theorem wf_threads_combine :
  (weak_fairness (step tid0) ∧ weak_fairness (step tid1)) ==
  weak_fairness (λ s s', step tid0 s s' ∨ step tid1 s s')%type.
Proof.
  apply wf_combine.
  - rewrite /tla_enabled.
    (* rewrite ?enabled_thread. *)
    (* first, to have any hope here we'd need to make [wf_combine] internal and
    carry out this proof under the assumption of `□⟨next⟩`, but also this
    doesn't seem true at all: it's equivalent to [enabled (step tid0) → ◇
    enabled (step tid1) → ◇ (step tid0)], but this is obvious false in an
    execution which is just the initial state and then infinite stuttering *)
Abort.

Lemma eventually_terminate :
  ⌜init⌝ ∧ □⟨next⟩ ∧ fair ⊢ ◇ ⌜terminated⌝.
Proof.
Abort.

End example.
