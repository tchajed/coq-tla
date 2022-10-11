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

From Coq.Relations Require Import Relation_Operators.
From Coq.Wellfounded Require Import Lexicographic_Product.

From TLA Require Import logic.

Module spec.

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
        | H: context[set _ _] |- _ =>
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
  - unfold exclusion_inv.
    stm; intuition auto.
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
  rewrite exclusion_inv_ok /exclusion_inv.
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
              ||  match goal with
                  | t: Tid |- _ => exists t; lookup_simp; by eauto
                  end).
Qed.

Lemma fair_step (tid: nat) :
  fair ⊢ weak_fairness (step tid).
Proof.
  unfold fair.
  (* apply doesn't work due to the wrong unification heuristics *)
  refine (forall_apply _ _).
Qed.

Definition nodup_inv s :=
  NoDup s.(state).(queue).

Definition nodup_helper_inv s :=
  nodup_inv s ∧
  (∀ t, t ∈ s.(state).(queue) →
        s.(tp) !! t = Some pc.kernel_wait).

Lemma NoDup_singleton {A} (x: A) :
  NoDup [x].
Proof.
  constructor.
  - set_solver.
  - constructor.
Qed.

Lemma NoDup_app1 {A} (l: list A) (x: A) :
  NoDup (l ++ [x]) ↔ NoDup l ∧ x ∉ l.
Proof.
  rewrite NoDup_app.
  pose proof (NoDup_singleton x).
  (intuition auto); set_solver.
Qed.

Lemma NoDup_app1_fwd {A} (l: list A) (x: A) :
  NoDup l → x ∉ l →
  NoDup (l ++ [x]).
Proof.
  rewrite NoDup_app1 //.
Qed.

Lemma NoDup_pop (l: list Tid) :
  NoDup l → NoDup (pop l).
Proof.
  destruct l; simpl; auto.
  inversion 1; subst; auto.
Qed.

Lemma elem_of_pop t (l: list Tid) :
  t ∈ pop l →
  t ∈ l.
Proof.
  unfold pop.
  destruct l; set_solver.
Qed.

Lemma NoDup_cons_inv t ts :
  NoDup (t :: ts) ↔
  t ∉ ts ∧ NoDup ts.
Proof.
  split.
  - inversion 1; subst; auto.
  - intros.
    constructor; intuition auto.
Qed.

Lemma NoDup_head_not_in t ts :
  NoDup (t :: ts) →
  t ∉ ts.
Proof.
  rewrite NoDup_cons_inv; intuition auto.
Qed.

(* limit these hints to just this NoDup theorem *)
Section nodup.

#[local]
Hint Resolve NoDup_nil_2 NoDup_pop NoDup_app1_fwd elem_of_pop : core.

#[local]
Hint Extern 2 (_ ∉ _) => set_solver : core.
#[local]
Hint Extern 2 (_ ∈ _) => set_solver : core.

Lemma nodup_helper_inv_ok :
  spec ⊢ □⌜nodup_helper_inv⌝.
Proof.
  unfold spec.
  tla_clear fair.
  apply init_invariant.
  - unfold nodup_helper_inv, nodup_inv; stm.
    set_solver+.
  - unfold nodup_helper_inv, nodup_inv.
    intros [σ tp] [σ' tp'] [Hnodup Hwait] Hnext.
    destruct Hnext as [ [t Hstep] | Heq]; [ | stm_simp; by eauto ].
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    destruct_step; stm; intros;
      try (destruct (decide (t0 = t)); lookup_simp; eauto;
          let n := numgoals in guard n <= 1);
      try match goal with
          | H: ?t ∈ q0 |- _ => apply Hwait in H; congruence
          end.
    + assert (t ∈ q0) as Hel by auto.
      apply Hwait in Hel; congruence.
Qed.
End nodup.

Lemma nodup_inv_ok :
  spec ⊢ □⌜nodup_inv⌝.
Proof.
  tla_pose nodup_helper_inv_ok.
  tla_clear spec.
  apply always_impl_proper.
  apply state_pred_impl; unfold nodup_helper_inv; naive_solver.
Qed.

Lemma queue_invs :
  spec ⊢ □⌜λ s, exclusion_inv s ∧ nodup_inv s⌝.
Proof.
  tla_pose exclusion_inv_ok.
  tla_pose nodup_inv_ok.
  tla_clear spec.
  rewrite -always_and; tla_simp.
Qed.

Lemma queue_gets_popped t ts :
  spec ⊢
  ⌜λ s, s.(state).(queue) = t :: ts ∧
        s.(state).(lock) = true⌝ ~~>
  ⌜λ s, (∃ ts', s.(state).(queue) = ts ++ ts') ∧
        t ∉ s.(state).(queue)⌝.
Proof.
  leads_to_trans (∃ t', ⌜λ s,
        (∃ ts', s.(state).(queue) = t :: ts ++ ts' ∧ t ∉ ts ++ ts') ∧
        s.(state).(lock) = true ∧
        lock_held s t'⌝)%L.
  - rewrite exist_state_pred.
    apply (leads_to_assume _ locked_inv_ok).
    apply (leads_to_assume _ nodup_inv_ok).
    tla_simp.
    apply pred_leads_to => s [[[Hq Hl] Hinv] Hnodup].
    destruct s as [[l q] ?]; simpl in *; subst.
    destruct Hinv as [t' ?]; eauto.
    exists t'; intuition eauto.
    exists nil; rewrite app_nil_r. split; first by eauto.
    rewrite /nodup_inv /= in Hnodup.
    apply NoDup_cons_inv in Hnodup; intuition auto.
  - apply leads_to_exist_intro => t'.
    apply (add_safety queue_invs).
    unfold lock_held.

(*|
This "detour" is actually really interesting: you might think that simple transitivity is enough, because if t' has the lock, it will release the lock, then signal to t (transitivity is needed because this is two steps from thread t'). However, this is _not_ the case. It is possible for t' to release the lock, and then for some other thread to happen to do a CAS, acquire the lock, unlock it, and then send the signal to t; the original t' will now signal some other thread. This is unusual because t' is trying to signal something to t but some unrelated thread swoops in and does it instead, many steps later.
|*)
    apply (leads_to_detour ⌜λ s,
      ((∃ ts' : list Tid, s.(state).(queue) = t :: ts ++ ts')
       ∧ s.(tp) !! t' = Some pc.unlock_wake)⌝).

    { rewrite combine_or_preds.
      tla_apply (wf1 (step t')).
      { tla_split; [ tla_assumption | tla_apply fair_step ]. }
      - intros [σ tp] [σ' tp'] => /= [Hinv Hnext].
        destruct Hnext  as (Hnext & [Hexclusion Hnodup] & [_ Hnodup']).
        destruct Hnext as [ [t'' Hstep] | Heq]; [ | stm_simp; by eauto 8 ].
        destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]].
        stm_simp.

        destruct_step; stm_simp;
          try (assert (t' ≠ t'') as Hneq by congruence);
          try solve [ eauto 6 ].
        + left; intuition eauto.
          eexists (_ ++ [t'']).
          rewrite !app_assoc; split; first by eauto.
          rewrite /nodup_inv /= NoDup_cons_inv in Hnodup Hnodup'.
          rewrite elem_of_app elem_of_list_singleton; intuition subst.
          rewrite NoDup_cons_inv NoDup_app1 in Hnodup'.
          set_solver+ Hnodup'.
        + assert (t' = t''); subst.
          { apply Hexclusion; eauto. }
          right; stm.
      - intros [[q l] tp] [σ' tp'] => /= Hp.
        destruct_and!; subst; repeat deex.
        (* drop next *)
        intros _ Hstep.
        rewrite /step /= in Hstep.
        repeat deex.
        assert (pc = pc.unlock_store) by congruence; subst.
        stm_simp.
        rewrite thread_step_eq /= in H1.
        stm.
      - intros [[q l] tp] ?. rewrite step_enabled.
        stm.
        eexists; split; first by eauto.
        intuition congruence. }

    { tla_apply (wf1 (step t')).
      { tla_split; [ tla_assumption | tla_apply fair_step ]. }
      - intros [σ tp] [σ' tp'] => /= [Hinv Hnext].
        destruct Hnext  as (Hnext & [Hexclusion Hnodup] & [_ Hnodup']).
        destruct Hnext as [ [t'' Hstep] | Heq]; [ | stm_simp; by eauto ].
        destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]].
        stm_simp.

        destruct_step; stm_simp;
          try (assert (t' ≠ t'') as Hneq by congruence);
          try solve [ eauto 6 ].
        + left; intuition eauto.
          eexists (_ ++ [t'']).
          rewrite !app_assoc; split; eauto.
        + right. eexists; intuition eauto.
          rewrite /nodup_inv /= in Hnodup.
          apply NoDup_head_not_in in Hnodup; auto.
      - intros [[q l] tp] [σ' tp'] => /= Hp.
        destruct_and!; subst; repeat deex.
        (* drop next *)
        intros (_ & [_ Hnodup] & _) Hstep.
        rewrite /step /= in Hstep; stm_simp.
        assert (pc = pc.unlock_wake) by congruence; subst.
        rewrite thread_step_eq /= in H1.
        stm.
        rewrite /nodup_inv /= in Hnodup.
        apply NoDup_head_not_in in Hnodup; auto.
      - intros [[q l] tp] ?. rewrite step_enabled.
        stm.
        eexists; split; first by eauto.
        intuition congruence. }
Qed.

Definition pc_set pc0 (tp: gmap Tid pc.t) : gset _ :=
  dom (filter (λ '(tid, pc), pc = pc0) tp).

Definition lattice_lt : relation (gset Tid * gset Tid * gset Tid) :=
  slexprod _ (gset Tid) (slexprod (gset Tid) (gset Tid) (⊂) (⊂)) (⊂).

Infix "≺" := lattice_lt (at level 50).

Lemma lattice_lt_wf : well_founded lattice_lt.
Proof. repeat apply wf_slexprod; apply set_wf. Qed.

Definition thread_sets (a: gset Tid * gset Tid * gset Tid) : Config → Prop :=
  λ s, let '(FW, KW, CAS) := a in
       FW = pc_set pc.futex_wait s.(tp) ∧
       KW = pc_set pc.kernel_wait s.(tp) ∧
       CAS = pc_set pc.lock_cas s.(tp).

Definition h (a: gset Tid * gset Tid * gset Tid) : Config → Prop :=
  λ s, thread_sets a s ∧
       s.(state).(lock) = false.

(* TODO: remove duplicate from spinlock_many_threads *)
Lemma gset_ext {A: Type} `{Countable A} (s1 s2: gset A) :
  (∀ x, x ∈ s1 ↔ x ∈ s2) →
  s1 = s2.
Proof.
  intros.
  apply leibniz_equiv.
  apply set_equiv.
  auto.
Qed.

(* TODO: remove duplicate from spinlock_many_threads *)
Lemma filter_is_Some {K: Type} `{Countable K} {V: Type}
  (P: (K * V) → Prop) `{∀ x, Decision (P x)} (m: gmap K V) k :
  is_Some (filter P m !! k) ↔ (∃ v, m !! k = Some v ∧ P (k,v)).
Proof.
  split; (intuition auto); repeat deex.
  - destruct H1 as [v Hlookup].
    rewrite map_filter_lookup_Some in Hlookup.
    eauto.
  - rewrite map_filter_lookup. rewrite /is_Some.
    exists v.
    rewrite H1 /=.
    rewrite option_guard_True //.
Qed.

(* TODO: almost identical theorem in spinlock_many_threads *)
Lemma pc_set_insert_other t pc0 tp pc' :
  pc' ≠ pc0 →
  pc_set pc0 (<[t := pc']> tp) = pc_set pc0 tp ∖ {[t]}.
Proof.
  intros.
  unfold pc_set.
  apply gset_ext => t'.
  rewrite elem_of_dom elem_of_difference elem_of_dom.
  rewrite elem_of_singleton.
  rewrite !filter_is_Some.
  destruct (decide (t = t')); subst.
  - rewrite lookup_insert; naive_solver.
  - rewrite -> lookup_insert_ne by congruence.
    naive_solver.
Qed.

Lemma pc_set_insert_same t pc0 tp :
  pc_set pc0 (<[t := pc0]> tp) = pc_set pc0 tp ∪ {[t]}.
Proof.
  unfold pc_set.
  apply gset_ext => t'.
  rewrite elem_of_dom elem_of_union elem_of_dom.
  rewrite elem_of_singleton.
  rewrite !filter_is_Some.
  split.
  - intros; repeat deex.
    destruct (decide (t = t')); lookup_simp; eauto.
  - intros; intuition (subst; eauto; repeat deex); lookup_simp; eauto.
    destruct (decide (t = t')); lookup_simp; eauto.
Qed.

Lemma pc_set_remove_not_present t pc0 pc tp :
  tp !! t = Some pc →
  pc ≠ pc0 →
  pc_set pc0 tp ∖ {[t]} = pc_set pc0 tp.
Proof.
  intros.
  assert (t ∉ pc_set pc0 tp).
  { unfold pc_set.
    rewrite elem_of_dom.
    rewrite filter_is_Some.
    intros [v [Hlookup ?]]; subst.
    congruence.
  }
  set_solver.
Qed.

Hint Rewrite pc_set_insert_same : pc.
Hint Rewrite pc_set_insert_other using congruence : pc.
Hint Rewrite pc_set_remove_not_present using (auto; congruence) : pc.

Lemma decreases_FW FW KW CAS t :
  t ∈ FW →
  spec ⊢
  ⌜thread_sets (FW, KW, CAS)⌝ ~~>
  ⌜λ s, ∃ FW' KW' CAS', (FW', KW', CAS') ≺ (FW, KW, CAS) ∧
                        thread_sets (FW', KW', CAS') s⌝.
Proof.
  intros Hel.
  tla_apply (wf1 (step t)).
  - unfold spec. tla_split; [ tla_assumption | tla_apply fair_step ].
  - rewrite /h /thread_sets.
    move => [σ tp] [σ' tp'] /= [? Hunlocked] Hnext. destruct_and!; subst.
    destruct Hnext as [ [t' Hstep] | Heq]; [ | stm_simp; by eauto ].
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    destruct_step; stm_simp;
      autorewrite with pc;
      repeat erewrite pc_set_remove_not_present by eauto;
      eauto.
    + right.
      do 3 eexists; intuition eauto.
Abort.


End example.
