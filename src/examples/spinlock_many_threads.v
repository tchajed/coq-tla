(*|

====================================================
Example: Spinlock with n threads
====================================================

This example is analogous to the spinlock_, but with an arbitrary number of threads rather than just two.

.. _spinlock: https://tchajed.github.io/coq-tla/examples/spinlock.html

|*)

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import gmap.

From TLA Require Import logic.

(*|
====================
System description
====================

This example models n threads acquiring then releasing a spinlock. See spinlock_
for a description of what each thread does; in brief, they go from `pc0` to
`pc1` when they acquire the lock (and remain in `pc0` otherwise), and then from
`pc1` to `pc2` when they unlock.

|*)

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

(*|
The state consists of the state of the mutex, and a program counter for
each thread. The initial domain of the pcs map determines the number of
threads.
|*)
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
    λ s, s.(lock) = false ∧
        (* all of the allocated threads are at the beginning of the spin loop *)
         ∀ tid pc, s.(pcs) !! tid = Some pc → pc = pc0.

  Definition next : action state :=
    λ s s', (∃ tid, step tid s s') ∨ s' = s.

(*|
**Safety** is mutual exclusion.
|*)
  Definition safe: state → Prop :=
    λ s, ∀ tid tid',
    s.(pcs) !! tid = Some pc1 →
    s.(pcs) !! tid' = Some pc1 →
    tid = tid'.

(*|
We assume fairness for each thread independently. (The unallocated threads are
never enabled so weak fairness is trivial.) Notice that this is a whole set of assumptions made simultaneously under a [∀] which is in TLA, not a Coq forall.
|*)
  Definition fair: predicate state :=
    ∀ tid, weak_fairness (step tid).

(*|
**Liveness** means all threads have terminated.
|*)
  Definition terminated: state → Prop :=
    λ s, ∀ tid pc, s.(pcs) !! tid = Some pc → pc = pc2.

End spec.

Import spec.

Section example.

Implicit Types (s: state) (t: Tid).

Hint Unfold init next step safe fair terminated : stm.
Hint Unfold cas_fail cas_succ unlock : stm.

Lemma enabled_thread t :
  enabled (step t) =
  λ s, ∃ pc, s.(pcs) !! t = Some pc ∧ pc ≠ pc2.
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
  autounfold with stm in *;
  intros; (intuition (repeat deex; subst; trivial));
  rewrite ?enabled_eq ?enabled_thread;
  repeat deex;
  repeat (match goal with
        | s: state |- _ => (destruct s; cbn in * )
        | H: ?x = ?x |- _ => clear H
        | H: @eq Pc _ _ |- _ => solve [ inversion H ]
        | H: @eq state (mkState _ _) (mkState _ _) |- _ =>
            invc H; cbn in *
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
  rewrite exclusion_inv_ok.
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

Why does this program terminate? We make an argument using the lattice rule. The lattice will have a node for each set of threads currently waiting, and it will be ordered by strict subset. We further restrict the interpretation of each node to require that no thread holds the lock; the locked states don't need to be considered in the lattice, since if a node holds the lock it will immediately release it with no intervening steps. Thus we will have to argue that if some set `waiting` thread IDs are at the beginning of the loop and the lock is free, eventually a (strictly) smaller set `waiting'` will be waiting with the lock again free.

|*)

(** The fact that this strict subset on finite sets is well-founded is proven in
std++ (in a highly generic way). *)
Theorem gset_subset_wf :
  well_founded  ((⊂) : gset Tid → gset Tid → Prop).
Proof. apply set_wf. Qed.

Definition waiting_set (pcs: gmap Tid Pc) : gset Tid :=
  dom (filter (λ '(tid, pc), pc = pc0) pcs).

Definition not_locked : state → Prop :=
  λ s,
    (∀ tid pc, s.(pcs) !! tid = Some pc → pc ≠ pc1) ∧
    s.(lock) = false.

(*|
This is the interpretation of each lattice element.
|*)
Definition h (waiting: gset Tid) : state → Prop :=
  λ s, waiting_set s.(pcs) = waiting ∧ not_locked s.

Hint Unfold h : stm.

Theorem init_to_h :
  ⌜init⌝ ⊢ ∃ waiting, ⌜h waiting⌝.
Proof.
  unseal. stm. eexists; intuition eauto.
  unfold not_locked; intuition.
  subst; eauto.
  apply H1 in H; congruence.
Qed.

Theorem h_0_to_terminated :
  ⌜h ∅⌝ ⊢ ⌜terminated⌝.
Proof.
  (* actually waiting_set s.(pcs) = ∅ is sufficient *)
  unseal. unfold h, waiting_set, not_locked; stm.
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

Lemma gset_ext {A: Type} `{Countable A} (s1 s2: gset A) :
  (∀ x, x ∈ s1 ↔ x ∈ s2) →
  s1 = s2.
Proof.
  intros.
  apply leibniz_equiv.
  apply set_equiv.
  auto.
Qed.

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

Lemma waiting_set_remove pcs tid pc' :
  pc' ≠ pc0 →
  waiting_set (<[tid:=pc']> pcs) = waiting_set pcs ∖ {[tid]}.
Proof.
  intros Hnot0.
  unfold waiting_set.
  rename tid into tid0.
  apply gset_ext => tid.
  rewrite elem_of_dom elem_of_difference elem_of_dom.
  rewrite elem_of_singleton.
  rewrite !filter_is_Some.
  destruct (decide (tid = tid0)); subst.
  - rewrite lookup_insert; naive_solver.
  - rewrite -> lookup_insert_ne by congruence.
    naive_solver.
Qed.

Lemma step_not_locked {t s s'} :
  step t s s' →
  not_locked s →
  cas_succ t s s'.
Proof.
  unfold not_locked; stm.
  - exfalso; eauto.
  - exfalso; eauto.
Qed.

(*|
This is the first key lemma: whenever `h` holds, some thread acquire the lock and decreases the set of waiting threads.
|*)
Lemma h_leads_to_locked waiting t :
  t ∈ waiting →
  ⌜ init ⌝ ∧ □ ⟨next⟩ ∧ fair
  ⊢ ⌜ h waiting ⌝ ~~>
    ⌜λ s, ∃ (x : Tid) (_ : x ∈ waiting),
      waiting_set (pcs s) = waiting ∖ {[x]} ∧
      pcs s !! x = Some pc1 ∧
      lock s = true ⌝.
Proof.
  intros Hel.
  tla_apply (wf1 (step t)).
  { tla_split; [ tla_assumption | tla_apply fair_step ]. }
  - unfold h.
    intros s s' [Hwaitset Hno_lock] Hnext.
    destruct Hnext as [[tid Hstep] | ->]; [ | eauto ].
    pose proof (step_not_locked Hstep Hno_lock) as Hcas.

    stm.
    right.
    exists tid. split.
    { unfold waiting_set.
      rewrite elem_of_dom.
      exists pc0.
      rewrite map_filter_lookup_Some //. }
    rewrite waiting_set_remove //.
    rewrite lookup_insert //.
  - unfold h.
    (* drop next assumptions, it's implied by [step t] *)
    intros s s' [Hwait Hno_lock] _ Hstep.
    pose proof (step_not_locked Hstep Hno_lock) as Hcas.
    stm.
    unshelve eexists t, _; auto.
    rewrite waiting_set_remove //.
    rewrite lookup_insert //.
  - unfold h, waiting_set, not_locked; stm.
    rewrite elem_of_dom in Hel.
    rewrite filter_is_Some in Hel.
    naive_solver.
Qed.

Lemma unlock_to_h waiting t s s' :
  unlock t s s' →
  t ∈ waiting →
  waiting_set s.(pcs) = waiting ∖ {[t]} →
  s.(pcs) !! t = Some pc1 →
  s.(lock) = true →
  exclusion_inv s →
  ∃ (waiting' : gset Tid) (_ : waiting' ⊂ waiting), h waiting' s'.
Proof.
  unfold unlock.
  intros [_ Hs'] Hwaiting Hwait Ht Hlock Hinv.
  destruct s as [l pcs]; destruct s' as [l' pcs']; simpl in *.
  invc Hs'.

  exists (waiting ∖ {[t]}). unshelve eexists.
  { set_solver+ Hwaiting. }
  unfold h.
  split.
  { rewrite /= waiting_set_remove //.
    set_solver+ Hwait. }
  unfold not_locked; simpl.
  split; [ | done ].
  intros.
  destruct (decide (t = tid)); stm.
Qed.

Lemma locked_step {tid s s' t} :
  step tid s s' →
  exclusion_inv s →
  s.(pcs) !! t = Some pc1 →
  s.(lock) = true →
  (s' = s ∧ tid ≠ t) ∨ (tid = t ∧ unlock t s s').
Proof.
  stm.
  - destruct (decide (t = tid)); subst; eauto.
    congruence.
  - destruct (decide (t = tid)); subst; eauto.
    left.
    exfalso; eauto.
Qed.

(*|
This is the second key lemma: if some thread holds the lock, it will eventually free it and restore the `h` predicate that forms the lattice.
|*)
Lemma locked_to_smaller_h waiting :
  ⌜ init ⌝ ∧ □ ⟨next⟩ ∧ fair
  ⊢ (∃ t (_ : t ∈ waiting),
        ⌜λ s,
          waiting_set (pcs s) = waiting ∖ {[t]} ∧
          pcs s !! t = Some pc1 ∧
          lock s = true ⌝) ~~>
     ⌜ λ s, ∃ (waiting' : gset Tid),
              waiting' ⊂ waiting ∧ h waiting' s ⌝.
Proof.
  rewrite <- tla_and_assoc. rewrite add_safety. tla_simp.
  lt_intro. lt_intro Hwaiting.
  tla_apply (wf1 (step t)).
  { tla_split; [ tla_assumption | tla_apply fair_step ]. }
  - intros s s' (Hwait & Ht & Hlock) (Hnext & Hinv & Hinv').
    destruct Hnext as [[tid Hstep] | ->]; [ | by eauto ].
    eapply locked_step in Hstep; eauto.
    destruct Hstep as [ ? | [-> Hunlock] ]; [ naive_solver | ].
    right.

    eapply unlock_to_h in Hunlock; naive_solver.
  - intros s s' (Hwait & Ht & Hlock) (Hnext & Hinv & Hinv') Hstep.
    eapply locked_step in Hstep; eauto.
    destruct Hstep as [ ? | [_ Hunlock] ]; [ naive_solver | ].
    eapply unlock_to_h in Hunlock; naive_solver.
  - stm.
    eexists; eauto.
Qed.

(*|
Next, we simply group these two lemmas via simple transitivity into the statement that is the core of the lattice argument.
|*)
Lemma h_decrease (waiting: gset Tid) (t: Tid) :
  t ∈ waiting →
  ⌜init⌝ ∧ □⟨next⟩ ∧ fair ⊢
  ⌜h waiting⌝ ~~>
    ⌜λ s, ∃ waiting', waiting' ⊂ waiting ∧ h waiting' s⌝.
Proof.
  intros Hel.

  (* need to go through an intermediate state where lock is held by someone *)
  leads_to_trans (∃ t' (_: t' ∈ waiting), ⌜λ s,
      waiting_set s.(pcs) = waiting ∖ {[t']} ∧
      s.(pcs) !! t' = Some pc1 ∧
      s.(lock) = true⌝)%L.

  -
(*|
In this branch we need to go from the wait set `waiting` to a set with one thread `t ∈ waiting` removed and the lock held; this is exactly what `cas_succ` does. Removing one thread results in a strictly smaller waiting set.
|*)
    lt_eapply h_leads_to_locked; eauto.
    lt_auto.
  -
(*|
Over in the other branch we need to show that from the smaller wait set, we can get back to `h`, which additionally requires that the lock be free. This will happen easily due to an `unlock t` action, which is the only thing enabled.
|*)
    apply locked_to_smaller_h.
Qed.

(*|
Putting everything together, `eventually_terminate` first shows that in the initial state there exists some waiting set to start the lattice proof off, then shows that if waiting goes to `∅` indeed all threads have terminated, and then uses `h_decrease` to show that each non-goal node leads to a strictly smaller node.
|*)

Lemma eventually_terminate :
  ⌜init⌝ ∧ □⟨next⟩ ∧ fair ⊢ ◇ ⌜terminated⌝.
Proof.
  apply (leads_to_apply ⌜init⌝); [ tla_assumption | ].

  assert (∀ tid, (fair ⊢ weak_fairness (step tid))%L) as Hfair.
  { intros tid. unfold fair.
    (* apply's unification heuristics don't work here *)
    refine (forall_apply _ _). }

  leads_to_etrans;
    [ tla_clear; apply impl_to_leads_to;
      apply init_to_h
    | ].
  leads_to_etrans;
    [| tla_clear; apply impl_to_leads_to;
       apply h_0_to_terminated
     ].

  apply (lattice_leads_to_ex gset_subset_wf h ∅); [ done | ].
  intros waiting Hnotempty.

  assert (exists t, t ∈ waiting) as [t Hwaiting].
  { apply set_choose_L in Hnotempty; naive_solver. }

  lt_eapply h_decrease; eauto.
  lt_auto naive_solver.
Qed.

End example.
