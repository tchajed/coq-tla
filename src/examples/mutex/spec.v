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

From TLA Require Import prelude.

From RecordUpdate Require Export RecordUpdate.
From stdpp Require Export gmap.

From TLA Require Import defs.

Module pc.
  Inductive t :=
    lock_cas | futex_wait | kernel_wait |
    unlock_store | unlock_wake | finished.

  #[global]
  Instance eq_dec : EqDecision t.
  Proof. solve_decision. Qed.

  Notation start := lock_cas (only parsing).

  Notation critical_sec := unlock_store (only parsing).

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

Definition thread_step_def (t: Tid) σ pc σ' pc' :=
  match pc with
  | pc.lock_cas =>
      if σ.(lock) then
        (* cas fail *)
        σ' = σ ∧
        pc' = pc.futex_wait
      else
        (* cas success *)
        σ' = σ<|lock := true|> ∧
        pc' = pc.unlock_store
  | pc.futex_wait =>
      if σ.(lock) then
        (* futex goes into waiting *)
        σ' = σ<|queue ::= λ q, q ++ [t]|> ∧
        pc' = pc.kernel_wait
      else
        (* futex_wait fails *)
        σ' = σ ∧
        pc' = pc.lock_cas
  | pc.kernel_wait =>
      (* without this enabling condition the thread cannot step while waiting
      in the kernel *)
      t ∉ σ.(queue) ∧
      σ' = σ ∧
      pc' = pc.lock_cas
  | pc.unlock_store =>
      σ' = σ<|lock := false|> ∧
      pc' = pc.unlock_wake
  | pc.unlock_wake =>
      σ' = σ<|queue ::= pop|> ∧
      pc' = pc.finished
  | pc.finished => False
  end.

Definition thread_step (t: Tid) : action (State * pc.t) :=
  λ '(σ, pc) '(σ', pc'), thread_step_def t σ pc σ' pc'.

Record Config :=
  mkConfig { state: State;
              (* "thread pool": represented by a program counter for each
              thread id (or None if this tid never existed) *)
              tp: gmap Tid pc.t; }.

#[global]
Instance _eta_config : Settable _ := settable! mkConfig <state; tp>.

Definition step (t: Tid) : action Config :=
  λ s s', ∃ pc, s.(tp) !! t = Some pc ∧
          ∃ ρ', thread_step t (s.(state), pc) ρ' ∧
                    s' = mkConfig ρ'.1 (<[t := ρ'.2]> s.(tp)).

Definition init : Config → Prop :=
  λ s, s.(state) = {| lock := false; queue := [] |} ∧
        ∀ tid pc, s.(tp) !! tid = Some pc → pc = pc.start.

Definition next : action Config :=
  λ s s', (∃ tid, step tid s s') ∨ s' = s.

Definition fair: predicate Config :=
  ∀ tid, weak_fairness (step tid).

Definition spec : predicate Config :=
  ⌜init⌝ ∧ □⟨next⟩ ∧ fair.

(*|
**Safety** means mutual exclusion in the critical section, which is a single program counter (the beginning of the unlock function.)
|*)
Definition safe: Config → Prop :=
  λ s, ∀ tid tid',
  s.(tp) !! tid = Some pc.critical_sec →
  s.(tp) !! tid' = Some pc.critical_sec →
  tid = tid'.

(*|
**Liveness** means all threads have terminated.
|*)
Definition terminated: Config → Prop :=
  λ s, ∀ tid pc, s.(tp) !! tid = Some pc → pc = pc.finished.
