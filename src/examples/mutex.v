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
          σ' = σ<|queue ::= cons t|> ∧
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

End spec.

Import spec.

Section example.

Implicit Types (σ: State) (s: Config) (tid t: Tid).
Implicit Types (ρ: State * pc.t).
Implicit Types (l: bool) (q: list Tid).

Lemma state_inv l1 q1 l2 q2 :
  mkState l1 q1 = mkState l2 q2 ↔ l1 = l2 ∧ q1 = q2.
Proof.
  split.
  - inversion 1; subst; auto.
  - intuition congruence.
Qed.

Lemma thread_step_eq t σ pc σ' pc' :
  thread_step t (σ, pc) (σ', pc') ↔ thread_step_def t σ pc σ' pc'.
Proof. reflexivity. Qed.

Opaque thread_step.

Ltac destruct_step :=
  lazymatch goal with
  | H: thread_step _ (?σ, ?pc) (?σ', ?pc') |- _ =>
      rewrite thread_step_eq /thread_step_def in H;
      destruct pc; simpl in H;
      [ let Heql := fresh "Heql" in
        destruct σ.(lock) eqn:Heql; simpl in H, Heql; subst
      | let Heql := fresh "Heql" in
        destruct σ.(lock) eqn:Heql; simpl in H, Heql; subst
      | (* kernel_wait *)
      | (* unlock_store *)
      | (* unlock_wake *)
      | exfalso; eauto (* finished *)
      ]
  end.

(* sanity check on semantics *)
Lemma thread_step_deterministic t ρ :
  ∀ ρ' ρ'' ,
  thread_step t ρ ρ' →
  thread_step t ρ ρ'' →
  ρ' = ρ''.
Proof.
  destruct ρ as [[l q] pc].
  intros [[l' q'] pc'] [[l'' q''] pc''].
  rewrite ?thread_step_eq.
  destruct pc; [ destruct l | destruct l | ..]; simpl;
    rewrite ?state_inv;
    try intuition congruence.
Qed.

Lemma exist_prod {A B} (P: A * B → Prop) :
  (exists x y, P (x, y)) →
  exists xy, P xy.
Proof. naive_solver. Qed.

Lemma thread_step_enabled t :
  enabled (thread_step t) =
    (λ ρ, (ρ.2 = pc.kernel_wait → t ∉ ρ.1.(queue)) ∧
          (ρ.2 = pc.finished → False)).
Proof.
  apply pred_ext; intros [σ pc]; simpl.
  unfold enabled.
  split.
  - intros [[σ' pc'] Hstep].
    destruct_step; try intuition congruence.
  - intros [? ?].
    apply exist_prod.
    setoid_rewrite thread_step_eq.
    destruct σ as [l q]; simpl in *.
    destruct pc; [ destruct l | destruct l | .. ];
      simpl; intuition eauto.
Qed.

Lemma thread_step_enabled_s t ρ :
  enabled (thread_step t) ρ ↔
    (ρ.2 = pc.kernel_wait → t ∉ ρ.1.(queue)) ∧
    (ρ.2 = pc.finished → False).
Proof.
  rewrite thread_step_enabled //.
Qed.

Lemma step_enabled t :
  enabled (step t) =
    (λ s, ∃ pc, s.(tp) !! t = Some pc ∧
                (pc = pc.kernel_wait → t ∉ s.(state).(queue)) ∧
                (pc ≠ pc.finished)).
Proof.
  apply pred_ext; intros [σ tp]; simpl.
  unfold enabled, step; simpl.
  split.
  - intros; repeat deex.
    rewrite H. eexists; split; [ by auto | ].
    destruct ρ' as [σ' pc'].
    pose proof (thread_step_enabled_s t (σ, pc)) as [Htenable _];
      simpl in *.
    apply Htenable.
    eexists; eauto.
  - intros; repeat deex.
    rewrite H.
    pose proof (thread_step_enabled_s t (σ, pc)) as [_ Htenable];
      simpl in *.
    intuition auto.
    destruct H2 as [ρ' Hstep].
    eauto 8.
Qed.

Definition exclusion_inv: Config → Prop :=
  λ s, (∀ tid, s.(tp) !! tid = Some pc.critical_sec →
               s.(state).(lock) = true) ∧
       safe s.

#[local]
Hint Unfold init next step safe fair terminated : stm.

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

Ltac invc H := inversion H; subst; clear H.

Ltac stm_simp :=
  autounfold with stm in *;
  intros; destruct_and?;
  repeat (match goal with
        | _ => progress deex
        | _ => progress subst
        | _ => destruct_and!
        | _ => destruct_or!
        | s: Config |- _ =>
            let σ := fresh "σ" in
            let tp := fresh "tp" in
            destruct s as [σ tp]; cbn in *
        | σ: State |- _ =>
            let l := fresh "l" in
            let q := fresh "q" in
            destruct σ as [l q]; cbn in *
        | ρ: State * pc.t |- _ =>
            let σ := fresh "σ" in
            let pc := fresh "pc" in
            destruct ρ as [σ pc]; cbn in *
        | H: ?x = ?x |- _ => clear H
        | H: @eq pc.t _ _ |- _ => solve [ inversion H ]
        | H: @eq _ (mkState _ _) (mkState _ _) |- _ =>
            invc H; cbn in *
        | H: @eq _ (mkConfig _ _) (mkConfig _ _) |- _ =>
            invc H; cbn in *
        | H: Some _ = Some _ |- _ => invc H
        | H: ?x = ?x → _ |- _ => specialize (H eq_refl)
        | H: ?P → _, H': ?P |- _ => lazymatch type of P with
                                    | Prop => specialize (H H')
                                    end
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
  try congruence;
  repeat first [
      (split; [ solve [ intuition eauto ] | ])
    | (split; [ | solve [ intuition eauto ] ])
    ].

Hint Unfold exclusion_inv : stm.

Lemma insert_lookup_dec {tp: gmap Tid pc.t} :
  ∀ t t' pc',
  <[t' := pc']> tp !! t = if decide (t = t') then Some pc' else tp !! t.
Proof.
  intros.
  destruct (decide _); lookup_simp.
Qed.

Theorem exclusion_inv' s :
  exclusion_inv s ↔
    (∀ t t', s.(tp) !! t = Some pc.critical_sec →
             s.(tp) !! t' = Some pc.critical_sec →
             t = t' ∧ s.(state).(lock) = true).
Proof.
  unfold exclusion_inv, safe.
  split; intros; destruct_and?; eauto.
  split; intros.
  - pose proof (H tid tid); intuition eauto.
  - pose proof (H tid tid'); intuition eauto.
Qed.

Opaque thread_step.

Lemma exclusion_inv_ok :
  spec ⊢ □⌜exclusion_inv⌝.
Proof.
  unfold spec.
  tla_clear fair.
  apply init_invariant.
  - stm; intuition auto.
    { pose proof (H1 _ _ H); congruence. }
    { pose proof (H1 _ _ H); congruence. }
  - intros [σ tp] [σ' tp']; simpl.
    intros Hinv Hnext.
    destruct Hnext as [ [t Hstep] | Heq]; [ | stm_simp; by eauto ].
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]].
    simpl in *.
    invc Heq.
    destruct ρ' as [σ' pc']; simpl.

    apply exclusion_inv' => t' t'' /= Ht' Ht''.
    destruct Hinv as [Hlocked Hsafe]; unfold safe in *; simpl in *.
    destruct (decide (t' = t'')); subst.
    { split; first done.
      destruct (decide (t = t'')); destruct_step; stm. }

    destruct (decide (t = t''));
      destruct (decide (t = t'));
      subst; lookup_simp; eauto;
      assert (σ.(lock) = true) by eauto.
    { destruct_step; stm. }
    { destruct_step; stm. }
    { split; eauto. }
Qed.

Theorem safety :
  spec ⊢ □ ⌜safe⌝.
Proof.
  rewrite -> exclusion_inv_ok.
  apply always_impl_proper.
  unseal; stm.
Qed.

Definition lock_held (s: Config) (t: Tid) :=
  s.(tp) !! t = Some pc.unlock_store.

Definition locked_inv : Config → Prop :=
  λ s, s.(state).(lock) = true →
       ∃ t, lock_held s t.

Lemma locked_inv_ok :
  spec ⊢ □⌜locked_inv⌝.
Proof.
  unfold spec.
  tla_clear fair.
  apply init_invariant.
  - unfold locked_inv; stm.
  - unfold locked_inv; intros [σ tp] [σ' tp'] Hinv Hnext.
    destruct Hnext as [ [t Hstep] | Heq]; [ | stm_simp; by eauto ].
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    unfold lock_held in *; simpl in *.
    destruct_step;
      repeat (stm_simp
              || lazymatch goal with
                  | H: context[set] |- _ => rewrite /set /= in H
                end
              ||  match goal with
                  | t: Tid |- _ => exists t; lookup_simp; by eauto
                  end).
Qed.

End example.
