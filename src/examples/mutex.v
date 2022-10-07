(*|
============================
Example: futex-based mutex
============================

See this `futex tutorial`__ for an explanation of what futexes are and how they
are used to implement a mutex. This example verifies safety and liveness for a
futex-based mutex. Liveness is trickier than in a spinlock, since it depends on
correct wakeups coming from unlock, otherwise the system can get stuck waiting
in the kernel.

__ https://github.com/tchajed/futex-tutorial

::

  void lock(m) {
    while (!atomic_cas(m, UNLOCKED, LOCKED)) {
      futex_wait(m, LOCKED)
      // goes into kernel_wait state if *m = LOCKED
    }
  }

  void unlock(m) {
    atomic_store(m, UNLOCKED)
    futex_wake(m)
  }

  // assume m is allocated as atomic bool
  lock(m)
  unlock(m)

The inductive `pc.t` below encodes the control flow of the program. We also need an additional boolean `σ.(lock)` to track the mutex itself and a queue `σ.(queue)` to track the list of threads waiting on the futex, which is needed to accurately give the semantics of which thread is woken up by `futex_wake`.

|*)

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import gmap.

From TLA Require Import logic.

Module spec.

  Module pc.
    Inductive t :=
      lock_cas | futex_wait | kernel_wait |
      unlock_store | unlock_wake | finished.
  End pc.

  Definition Tid := nat.

  Record State :=
    mkState {
        (* true if lock is held *)
        lock: bool;
        (* threads waiting for the futex *)
        queue: list Tid;
      }.

  #[global]
  Instance _eta_state : Settable _ := settable! mkState <lock; queue>.

  Definition pop {A} (l: list A) : list A :=
    match l with
    | [] => []
    | _::xs => xs
    end.

  Definition thread_step (t: Tid) : action (State * pc.t) :=
    λ '(σ, pc) '(σ', pc'),
    match pc with
    | pc.lock_cas =>
        (* cas success *)
        (σ.(lock) = false ∧
        σ' = σ<|lock := true|> ∧
        pc' = pc.unlock_store) ∨
        (* cas fail *)
        (σ.(lock) = true ∧
        σ' = σ ∧
        pc' = pc.futex_wait)
    | pc.futex_wait =>
        (* futex fail *)
        (σ.(lock) = false ∧
        σ' = σ ∧
        pc' = pc.lock_cas) ∨
        (* futex goes into waiting *)
        (σ.(lock) = true ∧
        σ' = σ<|queue ::= cons t|> ∧
        pc' = pc.kernel_wait)
    | pc.kernel_wait =>
        (* without this enabling condition the thread cannot step while waiting
        in the kernel *)
        t ∉ σ.(queue) ∧
        σ' = σ ∧
        pc' = pc.unlock_store
    | pc.unlock_store =>
        σ' = σ<|lock := false|> ∧
        pc' = pc.unlock_wake
    | pc.unlock_wake =>
        σ' = σ<|queue ::= pop|> ∧
        pc' = pc.finished
    | pc.finished => False
    end.

  Record Config :=
    mkConfig { state: State;
                (* program counter for each thread (or None if thread never
                existed) *)
                pcs: gmap Tid pc.t; }.

  #[global]
  Instance _eta_config : Settable _ := settable! mkConfig <state; pcs>.

  Definition step (t: Tid) : action Config :=
    λ s s', ∃ pc, s.(pcs) !! t = Some pc ∧
            ∃ ρ', thread_step t (s.(state), pc) ρ' ∧
                      s' = mkConfig ρ'.1 (<[t := ρ'.2]> s.(pcs)).

  Definition init : Config → Prop :=
    λ s, s.(state) = {| lock := false; queue := [] |} ∧
         ∀ tid pc, s.(pcs) !! tid = Some pc → pc = pc.lock_cas.

  Definition next : action Config :=
    λ s s', (∃ tid, step tid s s') ∨ s' = s.

  Definition fair: predicate Config :=
    ∀ tid, weak_fairness (step tid).

  Definition spec : predicate Config :=
    ⌜init⌝ ∧ □⟨next⟩ ∧ fair.

End spec.

Import spec.

Lemma state_inv l1 q1 l2 q2 :
  mkState l1 q1 = mkState l2 q2 ↔ l1 = l2 ∧ q1 = q2.
Proof.
  split.
  - inversion 1; subst; auto.
  - intuition congruence.
Qed.

(* sanity check on semantics *)
Lemma thread_step_deterministic t ρ :
  ∀ ρ' ρ'' ,
  thread_step t ρ ρ' →
  thread_step t ρ ρ'' →
  ρ' = ρ''.
Proof.
  destruct ρ as [[l q] pc].
  destruct pc; intros [[l' q'] pc] [[l'' q''] pc'']; simpl;
    rewrite ?state_inv;
    try intuition congruence.
Qed.

Lemma exist_prod {A B} (P: A * B → Prop) :
  (exists x y, P (x, y)) →
  exists xy, P xy.
Proof. naive_solver. Qed.

Lemma thread_step_enabled t :
  enabled (thread_step t) =
    (λ σ, (σ.2 = pc.kernel_wait → t ∉ σ.1.(queue)) ∧
          (σ.2 = pc.finished → False)).
Proof.
  apply pred_ext; intros [σ pc]; simpl.
  unfold enabled.
  split.
  - intros [[σ' pc'] Hstep].
    destruct pc; simpl in *; try (intuition congruence).
  - intros [? ?].
    apply exist_prod.
    destruct pc; simpl; intuition eauto.
    * destruct (lock σ); eauto 8.
    * destruct (lock σ); eauto 8.
Qed.

Lemma thread_step_enabled_s t σ :
  enabled (thread_step t) σ ↔
    (σ.2 = pc.kernel_wait → t ∉ σ.1.(queue)) ∧
    (σ.2 = pc.finished → False).
Proof.
  rewrite thread_step_enabled //.
Qed.

Lemma step_enabled t :
  enabled (step t) =
    (λ s, ∃ pc, s.(pcs) !! t = Some pc ∧
                (pc = pc.kernel_wait → t ∉ s.(state).(queue)) ∧
                (pc ≠ pc.finished)).
Proof.
  apply pred_ext; intros [σ pcs]; simpl.
  unfold enabled, step; cbn [spec.pcs set state].
  split.
  - intros; repeat deex.
    rewrite H. eexists; split; [ by auto | ].
    destruct ρ' as [σ' pc'].
    pose proof (thread_step_enabled_s t (σ, pc)) as [Htenable _];
      cbn [fst snd] in *.
    apply Htenable.
    eexists; eauto.
  - intros; repeat deex.
    rewrite H.
    pose proof (thread_step_enabled_s t (σ, pc)) as [_ Htenable];
      cbn [fst snd] in *.
    intuition auto.
    destruct H2 as [ρ' Hstep].
    eauto 8.
Qed.
