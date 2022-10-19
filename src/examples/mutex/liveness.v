From Coq.Relations Require Import Relation_Operators.
From Coq.Wellfounded Require Import Lexicographic_Product.

From TLA.examples.mutex Require Import nodup automation safety.

Section example.

Implicit Types (σ: State) (s: Config) (t: Tid) (tp: gmap Tid pc.t).
Implicit Types (l: bool) (q: list Tid).

Lemma fair_step (tid: nat) :
  fair ⊢ weak_fairness (step tid).
Proof.
  unfold fair.
  (* apply doesn't work due to the wrong unification heuristics *)
  refine (forall_apply _ _).
Qed.

(* specialized wf1 rule that handles some common manipulation for this state
machine *)
Lemma mutex_wf1 (t: Tid) (P Q: Config → Prop) :
  (∀ t' σ tp pc σ' pc',
     let s := {| state := σ; tp := tp|} in
     let s' := {| state := σ'; tp := <[t' := pc']> tp |} in
     ∀ (Hpre: P s)
       (Hinv: all_invs s)
       (Hinv': all_invs s')
       (Hneq: t ≠ t')
       (Hlookup: tp !! t' = Some pc)
       (Hstep: thread_step t' (σ, pc) (σ', pc')),
       P s' ∨ Q s'
  ) →
  (∀ σ tp pc σ' pc',
     let s := {| state := σ; tp := tp|} in
     let s' := {| state := σ'; tp := <[t := pc']> tp |} in
     ∀ (Hpre: P s)
       (Hinv: all_invs s)
       (Hlookup: tp !! t = Some pc)
       (Hstep: thread_step t (σ, pc) (σ', pc')),
     Q s'
  ) →
  (∀ l q tp,
     let s := {| state := {| lock := l; queue := q |}; tp := tp |} in
     P s →
     ∃ pc, tp !! t = Some pc ∧
           (pc = pc.kernel_wait → t ∉ q) ∧
           pc ≠ pc.finished
  ) →
  spec ⊢ ⌜P⌝ ~~> ⌜Q⌝.
Proof.
  simpl.
  intros H1 H2 H3.
  apply (add_safety all_invs_ok).
  tla_apply (wf1 (step t)).
  { rewrite /spec.
    tla_split; [ tla_assumption | tla_apply fair_step ]. }
  - intros [σ tp] [σ' tp'].
    intros Hp Hnext.
    destruct Hnext as [Hnext [Hinvs Hinvs']].
    destruct Hnext as [ [t' Hstep] | Heq].
    + destruct Hstep as [pc [Hlookup [ρ' [Hstep Heq]]]].
      invc Heq.
      destruct ρ' as [σ' pc']; simpl in *.
      (* in one branch we use the proof that P ∨ Q is preserved, in the other we
      use the proof that [step t] leads to Q *)
      destruct (decide (t = t')); subst; eauto.
    + invc Heq; eauto.
  - intros [σ tp] [σ' tp'].
    intros Hp [Hnext [Hinvs Hinvs']] Hstep.
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]].
    invc Heq.
    destruct ρ' as [σ' tp']; simpl in *.
    eauto.
  - intros [[l q] tp] HP.
    rewrite step_enabled /=.
    eauto.
Qed.

Lemma leads_to_if_lock Γ (P: Config → Prop) φ :
  (Γ ⊢ ⌜λ s, P s ∧ s.(state).(lock) = false⌝ ~~> φ) →
  (Γ ⊢ ⌜λ s, P s ∧ s.(state).(lock) = true⌝ ~~> φ) →
  Γ ⊢ ⌜P⌝ ~~> φ.
Proof.
  intros Hfalse Htrue.
  apply (leads_to_if ⌜λ s, s.(state).(lock) = true⌝); tla_simp; auto.
  leads_to_etrans; [ | apply Hfalse ].
  lt_unfold. rewrite not_true_iff_false //.
Qed.

Lemma list_elem_of_head {A} (l: list A) (x: A) :
  x ∈ x::l.
Proof. set_solver. Qed.

Hint Resolve list_elem_of_head : core.

Lemma eventually_unlock W :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W⌝ ~~>
  ⌜λ s, wait_set s.(tp) = W ∧ s.(state).(lock) = false⌝.
Proof.
  apply leads_to_if_lock; first by lt_auto.

  (* somebody must hold the lock *)
  eapply leads_to_assume; [ apply locked_inv_ok | ].
  tla_simp.
  leads_to_trans (∃ t, ⌜λ s, wait_set s.(tp) = W ∧
                             s.(state).(lock) = true ∧
                             lock_held s t⌝)%L.
  { rewrite /locked_inv.
    lt_auto naive_solver. }
  lt_intro t0.

  apply (mutex_wf1 t0); simpl; intros.
  - rewrite /lock_held /= in Hpre |- *.
    destruct Hpre as (Hwait & Hlock & Ht0); subst.
    destruct_step; stm.
  - rewrite /lock_held /= in Hpre |- *.
    destruct Hpre as (Hwait & Hlock & Ht0); subst.
    stm.
  - naive_solver.
Qed.

Lemma lock_cas_unlocked_progress t W :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        s.(state).(lock) = false ∧
        s.(tp) !! t = Some pc.lock_cas⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W⌝.
Proof.
  apply (mutex_wf1 t); simpl; intros.
  - destruct_step; stm.
  - stm.
  - naive_solver.
Qed.

(* if there is a thread t in pc.kernel_wait, then either the queue is empty, in
which case weak_fairness (step t) easily gets t to pc.lock_cas, or it has a head element t', in which case that thread will get to cas *)

Lemma queue_gets_popped_unlocked W t ts :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        s.(state).(queue) = t :: ts ∧
        s.(state).(lock) = false⌝ ~~>
  ⌜λ s,
  (* this case covers when the lock goes from false to true *)
    wait_set s.(tp) ⊂ W ∨
      wait_set s.(tp) = W ∧
      s.(state).(queue) = ts ∧
      t ∉ s.(state).(queue) ∧
      s.(tp) !! t = Some pc.kernel_wait ∧
      s.(state).(lock) = false⌝.
Proof.
  apply (leads_to_assume _ all_invs_ok); tla_simp.
  leads_to_trans (∃ t', ⌜ λ s,
                    wait_set s.(tp) = W ∧
                    s.(state).(queue) = t :: ts ∧
                    s.(state).(lock) = false ∧
                    thread_can_lock t' s
                   ⌝)%L.
  { lt_unfold.
    destruct s as [[l q] tp].
    move => /= [[Hwaiters [? ?]] Hinv]; simpl; subst.
    destruct Hinv as [_ _ _ _ Hcan_lock];
      autounfold with inv in *.
    specialize (Hcan_lock _ _ ltac:(eauto)); stm. }

  lt_intro.
  apply (leads_to_detour
    ⌜λ s, wait_set s.(tp) = W ∧
         s.(state).(lock) = false ∧
         s.(tp) !! t' = Some pc.lock_cas⌝); tla_simp.

  { apply (mutex_wf1 t'); simpl.
    - intros t'' **.
      destruct Hinv as [_ _ Hnodup Hwaiting Hcan_lock];
        autounfold with inv in *.
      rewrite /thread_can_lock.
      destruct_step; stm_simp; simp_props; auto.
      + right; right; left. eauto.
      + assert (t ∉ ts) by (inversion Hnodup; auto).
        rewrite /waiting_inv in Hwaiting.
        assert (t'' ≠ t) by set_solver.
        right; right; right. stm.
    - intros.
      destruct Hinv as [_ _ Hnodup Hwaiting Hcan_lock];
        autounfold with inv in *; simpl in *.
      stm_simp.
      assert (t ∉ ts) by (eauto using NoDup_head_not_in).
      assert (tp !! t = Some pc.kernel_wait) by (eapply Hwaiting; eauto).
      rewrite thread_step_eq /thread_step_def in Hstep.
      unfold thread_can_lock in *; stm.
    - intros. rewrite /thread_can_lock /= in H.
      naive_solver. }

  lt_apply lock_cas_unlocked_progress.
Qed.

Hint Resolve elem_of_pop : core.

Lemma kernel_wait_not_queued_unlocked_progress W t :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        t ∉ s.(state).(queue) ∧
        s.(state).(lock) = false⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        wait_set s.(tp) = W ∧
          s.(tp) !! t = Some pc.lock_cas ∧
          s.(state).(lock) = false⌝.
Proof.
  apply (mutex_wf1 t); simpl; intros.
  - destruct Hpre as (Hwait & Ht & Hnotin); subst.
    destruct_step; stm; simp_props.
  - stm.
  - naive_solver.
Qed.

Lemma kernel_wait_unlocked_progress1 W t :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        s.(state).(lock) = false⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (∃ t', wait_set s.(tp) = W ∧
               s.(tp) !! t' = Some pc.lock_cas ∧
               s.(state).(lock) = false
         )⌝.
Proof.
  apply (leads_to_if ⌜λ s, t ∈ s.(state).(queue)⌝).
  - tla_simp.
    leads_to_trans (∃ t0 ts0,
                       ⌜λ s, wait_set s.(tp) = W ∧
                             s.(tp) !! t = Some pc.kernel_wait ∧
                             s.(state).(queue) = t0::ts0 ∧
                             s.(state).(lock) = false⌝)%L.
    + lt_auto intuition idtac.
      destruct s.(state).(queue) eqn:Hq; [ exfalso; set_solver | ].
      naive_solver.
    + lt_intro t0. lt_intro ts0.
      lt_apply queue_gets_popped_unlocked.
      lt_split; first by lt_auto.
      lt_apply kernel_wait_not_queued_unlocked_progress.
  - tla_simp.
    lt_apply kernel_wait_not_queued_unlocked_progress.
Qed.

Lemma kernel_wait_unlocked_progress W t :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        s.(state).(lock) = false⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W⌝.
Proof.
  leads_to_etrans.
  { apply kernel_wait_unlocked_progress1. }
  lt_split; first by lt_auto.
  lt_intro t'.
  lt_apply lock_cas_unlocked_progress.
Qed.

Lemma gset_subset_wf :
  well_founded  ((⊂) : gset Tid → gset Tid → Prop).
Proof. apply set_wf. Qed.

Lemma wake_threads_decrease_unlocked U :
  U ≠ ∅ →
  spec ⊢
  ⌜λ s, wait_set s.(tp) = ∅ ∧
        wake_set s.(tp) = U ∧
        s.(state).(lock) = false⌝ ~~>
  ⌜λ s, wait_set s.(tp) = ∅ ∧
        wake_set s.(tp) ⊂ U ∧
        s.(state).(lock) = false⌝.
Proof.
  intros Hnotempty.
  assert (∃ t, t ∈ U) as [t Hel].
  { apply set_choose_L in Hnotempty; naive_solver. }
  apply (mutex_wf1 t); simpl; intros.
  - stm_simp.
    assert (¬wait_pc pc) as Hnotwait%not_wait_pc.
    { intros Hwait.
      assert (t' ∈ wait_set tp) by eauto.
      set_solver. }
    (intuition idtac); stm.
    + destruct Hinv as [[Hexcl _] _ _ _ _]; simpl in Hexcl.
      apply Hexcl in Hlookup; congruence.
  - stm_simp.
    apply elem_wake_set in Hel.
    stm_simp.
    intuition eauto.
  - stm_simp.
    apply elem_wake_set in Hel.
    naive_solver.
Qed.

Lemma wake_threads_empty :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = ∅⌝ ~~>
  ⌜λ s, wait_set s.(tp) = ∅ ∧
        wake_set s.(tp) = ∅ ∧
        s.(state).(lock) = false⌝.
Proof.
  leads_to_trans ⌜λ s, wait_set s.(tp) = ∅ ∧
                       s.(state).(lock) = false⌝.
  { apply eventually_unlock. }
  set (h U s := wait_set s.(tp) = ∅ ∧
                s.(state).(lock) = false ∧
                wake_set s.(tp) = U).
  lt_apply (lattice_leads_to_ex gset_subset_wf h ∅);
    rewrite /h.
  - lt_auto naive_solver.
  - intros U Hnonempty.
    lt_apply wake_threads_decrease_unlocked; auto.
    lt_auto intuition eauto 10.
  - lt_auto naive_solver.
Qed.

Lemma futex_wait_unlocked_progress t W :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        s.(tp) !! t = Some pc.futex_wait ∧
        s.(state).(lock) = false⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W⌝.
Proof.
  apply (leads_to_detour
           ⌜λ s, wait_set s.(tp) = W ∧
                 s.(state).(lock) = false ∧
                 s.(tp) !! t = Some pc.lock_cas⌝).
  { tla_simp.
    apply (mutex_wf1 t); simpl; intros.
    - destruct_step; stm.
    - stm.
    - naive_solver. }
  lt_apply lock_cas_unlocked_progress.
Qed.

Lemma append_non_empty {A} (l: list A) (x: A) :
  l ++ [x] ≠ [].
Proof.
  destruct l; simpl; congruence.
Qed.

Hint Resolve append_non_empty : core.

Lemma futex_wait_progress1 t W U :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        wake_set s.(tp) = U ∧
        s.(tp) !! t = Some pc.futex_wait⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (wait_set s.(tp) = W ∧
         wake_set s.(tp) ⊂ U) ∨
        (wait_set s.(tp) = W ∧
         wake_set s.(tp) = U ∧
         s.(tp) !! t = Some pc.kernel_wait ∧
         s.(state).(lock) = true ∧
         s.(state).(queue) ≠ [])⌝.
Proof.
  apply (leads_to_detour
           (⌜λ s, wait_set s.(tp) = W ∧
                 s.(state).(lock) = false ∧
                 s.(tp) !! t = Some pc.lock_cas⌝ ∨
           ⌜λ s, wait_set s.(tp) = W ∧
                  s.(state).(lock) = false ∧
                  s.(tp) !! t = Some pc.futex_wait⌝)%L).
  { tla_simp.
    apply (mutex_wf1 t); simpl; intros.
    - destruct_step; stm.
    - stm.
      destruct l0; stm.
      eauto 10.
    - naive_solver. }
  lt_split.
  - lt_apply lock_cas_unlocked_progress.
  - lt_apply futex_wait_unlocked_progress.
Qed.

Lemma queue_gets_popped_locked W U t :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        wake_set s.(tp) = U ∧
        (∃ ts, s.(state).(queue) = t :: ts) ∧
        s.(state).(lock) = true⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
       (wait_set s.(tp) = W ∧
        wake_set s.(tp) ⊂ U) ∨
      (wait_set s.(tp) = W ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        t ∉ s.(state).(queue) ∧
       s.(state).(lock) = false) ⌝.
Proof.
  leads_to_trans (∃ t', ⌜λ s,
        wait_set s.(tp) = W ∧
        wake_set s.(tp) = U ∧
        (∃ ts, s.(state).(queue) = t :: ts ∧
                t ∉ ts) ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        s.(state).(lock) = true ∧
        lock_held s t'⌝)%L.
  - apply (leads_to_assume _ all_invs_ok).
    lt_unfold.
    intros [(?&?&?&?) Hinv].
    destruct Hinv as [_ Hlocked Hnodup Hwaiting _];
      autounfold with inv in *.
    stm.
    exists t0; intuition eauto.
    eexists; intuition eauto.
    apply NoDup_head_not_in in Hnodup; auto.
  - lt_intros.
    unfold lock_held.

(*|
This "detour" is actually really interesting: you might think that simple transitivity is enough, because if t' has the lock, it will release the lock, then signal to t (transitivity is needed because this is two steps from thread t'). However, this is _not_ the case. It is possible for t' to release the lock, and then for some other thread to happen to do a CAS, acquire the lock, unlock it, and then send the signal to t; the original t' will now signal some other thread. This is unusual because t' is trying to signal something to t but some unrelated thread swoops in and does it instead, many steps later.
|*)
    apply (leads_to_detour ⌜λ s,
      wait_set s.(tp) = W ∧
      (∃ ts' : list Tid, s.(state).(queue) = t :: ts') ∧
      s.(tp) !! t = Some pc.kernel_wait ∧
       s.(tp) !! t' = Some pc.unlock_wake ∧
      s.(state).(lock) = false⌝).

    { tla_simp.
      apply (mutex_wf1 t'); cbn.
      - intro t''; intros.
        (* extract the invariants we want to use *)
        destruct Hinv as [Hexclusion _ Hnodup _ _];
          destruct Hinv' as [_ _ Hnodup' _ _];
          autounfold with inv in *; simpl in *.
        destruct Hexclusion as [_ Hsafe].
        stm_simp.

        destruct_step; stm_simp; eauto 8.
        + left; intuition eauto.
        + left; intuition eauto.
          eexists (_ ++ [t'']).
          intuition eauto.
          apply NoDup_head_not_in in Hnodup'; auto.
        + assert (t'' ≠ t) by set_solver.
          stm.
        + assert (t' = t'').
          { apply Hsafe; eauto. }
          exfalso; congruence.
      - stm.
      - stm.
        eexists; split; first by eauto.
        intuition congruence. }

    { apply (mutex_wf1 t'); cbn.
      - intro t''; intros.
        destruct Hinv as [_ _  Hnodup _ _];
          autounfold with inv in *; simpl in *.
        stm_simp.

        destruct_step; stm.
        + assert (t'' ≠ t) by set_solver.
          stm.
        + simp_props.
          right; right; right.
          apply NoDup_head_not_in in Hnodup; eauto.
      - intros.
        stm.
        destruct Hinv as [_ _ Hnodup _ _];
          autounfold with inv in *; simpl in *.
        apply NoDup_head_not_in in Hnodup; eauto 10.
      - intros.
        stm.
        eexists; split; first by eauto.
        intuition congruence. }
Qed.

Lemma kernel_wait_locked_progress W U :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        wake_set s.(tp) = U ∧
        (* the fact that the queue is non-empty implies some thread is waiting
        (in fact the one that matters is only the head of the queue) *)
        s.(state).(lock) = true ∧
        s.(state).(queue) ≠ []⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (wait_set s.(tp) = W ∧ wake_set s.(tp) ⊂ U) ⌝.
Proof.
  leads_to_trans (∃ t,
                      ⌜λ s, wait_set s.(tp) = W ∧
                            wake_set s.(tp) = U ∧
                            s.(tp) !! t = Some pc.kernel_wait ∧
                            (∃ ts, s.(state).(queue) = t::ts) ∧
                            s.(state).(lock) = true⌝)%L.
  { apply (leads_to_assume _ all_invs_ok); tla_simp.
    lt_unfold. intros [(?&?&?&?) [_ _ _ Hwait _]].
    autounfold with inv in *.
    stm_simp.
    destruct q as [|t ts]; [ congruence | ].
    eauto 10.
  }
  lt_intros.
  apply (leads_to_detour ⌜λ s, wait_set s.(tp) = W ∧
                                s.(tp) !! t = Some pc.kernel_wait ∧
                                s.(state).(lock) = false⌝);
    lt_simp.
  2: { by lt_apply kernel_wait_unlocked_progress. }

  lt_apply queue_gets_popped_locked.
Qed.

Lemma futex_wait_progress t W U :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        wake_set s.(tp) = U ∧
        s.(tp) !! t = Some pc.futex_wait⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (wait_set s.(tp) = W ∧ wake_set s.(tp) ⊂ U)⌝.
Proof.
  lt_apply futex_wait_progress1.
  lt_split; first by lt_auto.
  lt_split; first by lt_auto.
  lt_apply kernel_wait_locked_progress.
Qed.

Lemma lock_cas_locked_progress t W U :
  spec
  ⊢ ⌜
      λ s,
      wait_set s.(tp) = W ∧
      wake_set s.(tp) = U ∧
      s.(state).(lock) = true ∧
      s.(tp) !! t = Some pc.lock_cas ⌝ ~~>
    ⌜ λ s, wait_set s.(tp) ⊂ W ∨
          (wait_set s.(tp) = W ∧ wake_set s.(tp) ⊂ U) ⌝.
Proof.
  apply (leads_to_detour ⌜λ s, wait_set s.(tp) = W ∧
                               (wake_set s.(tp) ⊂ U ∨
                               s.(tp) !! t = Some pc.lock_cas ∧
                                 s.(state).(lock) = false ∨
                               wake_set s.(tp) = U ∧
                                 s.(tp) !! t = Some pc.futex_wait)⌝);
    lt_simp.
  - apply (mutex_wf1 t); simpl; intros.
    + destruct_step; stm.
    + stm.
    + naive_solver.
  - rewrite -combine_state_preds.
    lt_split; first by lt_auto.
    lt_split.
    { lt_apply lock_cas_unlocked_progress. }
    lt_apply (futex_wait_progress t W U).
Qed.

Lemma lock_cas_progress t W U :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        wake_set s.(tp) = U ∧
        s.(tp) !! t = Some pc.lock_cas⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (wait_set s.(tp) = W ∧ wake_set s.(tp) ⊂ U)⌝.
Proof.
  apply leads_to_if_lock.
  - lt_apply lock_cas_unlocked_progress.
  - lt_apply lock_cas_locked_progress.
Qed.

Lemma kernel_wait_locked_queue_empty_progress W U t :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        wake_set s.(tp) = U ∧
        s.(state).(lock) = true ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        s.(state).(queue) = []⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (wait_set s.(tp) = W ∧ wake_set s.(tp) ⊂ U) ∨
        wait_set s.(tp) = W ∧
        wake_set s.(tp) = U ∧
        ∃ t', s.(tp) !! t' = Some pc.lock_cas⌝.
Proof.
  apply (leads_to_detour ⌜λ s,
             wait_set s.(tp) = W ∧
              s.(state).(lock) = false ∧
              s.(tp) !! t = Some pc.kernel_wait ∨
              (wait_set s.(tp) = W ∧
               wake_set s.(tp) = U ∧
                s.(state).(queue) ≠ [] ∧
                s.(state).(lock) = true)
              ⌝);
    lt_simp.
  - apply (mutex_wf1 t); simpl; intros.
    + destruct_step; stm.
      eauto 10.
    + stm.
      simp_props.
      right; right; right.
      exists t; lookup_simp.
    + stm_simp.
      eauto with set_solver.
  - lt_split.
    + lt_apply kernel_wait_unlocked_progress.
    + lt_apply kernel_wait_locked_progress.
Qed.

Lemma kernel_wait_progress W U t :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        wake_set s.(tp) = U ∧
        s.(tp) !! t = Some pc.kernel_wait⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (wait_set s.(tp) = W ∧ wake_set s.(tp) ⊂ U)⌝.
Proof.
  apply leads_to_if_lock.
  { lt_apply kernel_wait_unlocked_progress. }
  apply (leads_to_if ⌜λ s, s.(state).(queue) = []⌝); lt_simp.
  - lt_apply kernel_wait_locked_queue_empty_progress.
    lt_split; first by lt_auto.
    lt_split; first by lt_auto.
    lt_simp.
    leads_to_trans (∃ t',
                       ⌜λ s, wait_set s.(tp) = W ∧
                             wake_set s.(tp) = U ∧
                             s.(tp) !! t' = Some pc.lock_cas⌝)%L.
    { lt_auto naive_solver. }
    lt_intros.
    lt_apply lock_cas_progress.
  - lt_apply kernel_wait_locked_progress.
Qed.

Lemma empty_wait_wake_to_unlock :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = ∅ ∧
        wake_set s.(tp) = ∅⌝ ~~>
  ⌜λ s, wait_set s.(tp) = ∅ ∧
        wake_set s.(tp) = ∅ ∧
        s.(state).(lock) = false⌝.
Proof.
  lt_apply wake_threads_empty.
Qed.

Lemma empty_wait_wake_to_terminated :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = ∅ ∧
        wake_set s.(tp) = ∅ ∧
        s.(state).(lock) = false⌝ ~~>
  ⌜terminated⌝.
Proof.
  rewrite /terminated.
  apply (leads_to_assume _ all_invs_ok).
  lt_unfold.
  intros [[Hempty Hunlocked] Hinv] t pc.
  intuition eauto.
  destruct (decide (wait_pc pc)) as [|Hnot_wait].
  + assert (t ∈ wait_set s.(tp)) by eauto.
    exfalso; set_solver.
  + apply not_wait_pc in Hnot_wait; intuition (subst; auto).
    * destruct Hinv as [[Hexcl _] _ _ _ _].
      apply Hexcl in H.
      exfalso; congruence.
    * assert (t ∈ wake_set s.(tp)) by eauto.
      exfalso; set_solver.
Qed.

Lemma any_wait_progress W U t :
  spec ⊢
  (⌜ λ s, wait_set s.(tp) = W ∧ wake_set s.(tp) = U ⌝ ∧
   (⌜ λ s, s.(tp) !! t = Some pc.lock_cas ⌝ ∨
    ⌜ λ s, s.(tp) !! t = Some pc.futex_wait ⌝ ∨
    ⌜ λ s, s.(tp) !! t = Some pc.kernel_wait ⌝)) ~~>
  ⌜ λ s, wait_set s.(tp) ⊂ W ∨ wait_set s.(tp) = W ∧ wake_set s.(tp) ⊂ U ⌝.
Proof.
  lt_split; [ | lt_split ]; tla_simp.
  - lt_apply lock_cas_progress.
  - lt_apply futex_wait_progress.
  - lt_apply kernel_wait_progress.
Qed.

Hint Constructors slexprod : core.

Theorem eventually_terminated :
  spec ⊢ ◇⌜terminated⌝.
Proof.
  apply (leads_to_apply ⌜λ s, True⌝).
  { unseal. }

  set (h := λ '(W, U) s, wait_set s.(tp) = W ∧
                         wake_set s.(tp) = U).
  lt_apply (lattice_leads_to_ex
              (wf_slexprod _ _ _ _ gset_subset_wf gset_subset_wf)
              h (∅, ∅)).

  - rewrite /h. lt_unfold.
    intros.
    eexists (_, _); intuition eauto.

  - intros [W U] Hnot_bothempty.

(*|
Handle the case where W = ∅ separately.
  |*)
    assert ((W = ∅ ∧ U ≠ ∅) ∨ W ≠ ∅) as [[-> Hnonempty]|Hnonempty].
    { destruct (decide (W = ∅)); destruct (decide (U = ∅)); subst; eauto. }
    { rewrite /h. lt_apply wake_threads_empty.
      lt_auto naive_solver. }

    assert (∃ t, t ∈ W) as [t Hel].
    { apply set_choose_L in Hnonempty; naive_solver. }

    leads_to_trans (⌜h (W, U)⌝ ∧
                    (⌜λ s, s.(tp) !! t = Some pc.lock_cas⌝ ∨
                    ⌜λ s, s.(tp) !! t = Some pc.futex_wait⌝ ∨
                    ⌜λ s, s.(tp) !! t = Some pc.kernel_wait⌝))%L.
    { rewrite /h. lt_auto intuition auto. subst.
      apply elem_of_wait_set in Hel as (pc & Hlookup & Hwait).
      rewrite /wait_pc in Hwait; naive_solver. }
    rewrite /h.
    lt_apply any_wait_progress.
    lt_auto naive_solver.

  - rewrite /h.
    lt_apply empty_wait_wake_to_unlock.
    lt_apply empty_wait_wake_to_terminated.

Qed.

End example.
