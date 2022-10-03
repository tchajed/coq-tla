From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import functions.

From TLA Require Import logic.


(*|

=============================
Example: (spinlock) Mutex
=============================

This example is a liveness proof for the following simple C program. It encodes the program as a hand-written state machine, with states referring to labeled points.

type Mutex = bool;
const UNLOCKED = false;
const LOCKED = true;

void lock(Mutex *m) {
  // s0
  for cas(m, UNLOCKED, LOCKED) {}
}

void unlock(Mutex *m) {
  // s1
  *m = UNLOCKED;
  // s2
}

What we reason about is two threads running lock(m); unlock(m) (assuming m starts out allocated).

|*)

Module spec.

  Inductive pc := s0 | s1 | s2.
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
    λ s s', (s.(pcs) t0 = s0 ∧ s.(lock) = true)
            ∧ s' = s.

  Definition cas_succ (t0: Tid): action state :=
    λ s s', s.(pcs) t0 = s0 ∧ s.(lock) = false
            ∧ s' = s <|lock := true|>
                     <|pcs ::= <[ t0 := s1 ]> |>.

  Definition unlock (t0: Tid): action state :=
    λ s s', s.(pcs) t0 = s1
            ∧ s' = s <|lock := false|>
                     <|pcs ::= <[ t0 := s2 ]> |>.

  Definition step (t0: Tid): action state :=
      λ s s', cas_fail t0 s s' ∨ cas_succ t0 s s' ∨ unlock t0 s s'.

  Definition next : action state :=
    λ s s', step tid0 s s' ∨ step tid1 s s' ∨ s' = s.

End spec.
