From TLA Require Import prelude.
From TLA.examples.mutex Require Import nodup automation safety liveness.

Section example.

Implicit Types (σ: State) (s: Config) (t: Tid) (tp: gmap Tid pc.t).
Implicit Types (l: bool) (q: list Tid).

Lemma waiters_monotonic_next s s' :
  next s s' →
  wait_set s'.(tp) ⊆ wait_set s.(tp).
Proof.
  destruct s as [σ tp]. destruct s' as [σ' tp'].
  simpl.
  intros Hnext.
  destruct Hnext as [ [t'' Hstep] | Heq ]; [ | by stm ].
  destruct Hstep as [pc [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
  destruct_step; stm.
Qed.

Lemma waiters_monotonic W :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W⌝ ~~>
  □⌜λ s, wait_set s.(tp) ⊆ W⌝.
Proof.
  rewrite -leads_to_impl_internal.
  rewrite /spec. tla_clear ⌜init⌝. tla_clear fair.
  apply always_induction_impl_pred.
  - eauto.
  - intros s s' Hwait_set.
    intros Hsubset%waiters_monotonic_next.
    set_solver.
Qed.

Hint Resolve list_elem_of_head : core.

Lemma __queue_gets_popped_locked W t ts :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        s.(state).(queue) = t :: ts ∧
        s.(state).(lock) = true⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊆ W ∧
       (∃ ts', s.(state).(queue) = ts ++ ts') ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        t ∉ s.(state).(queue)⌝.
Proof.
  leads_to_trans (∃ t', ⌜λ s,
        wait_set s.(tp) = W ∧
        (∃ ts', s.(state).(queue) = t :: ts ++ ts' ∧
                t ∉ ts ++ ts') ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        s.(state).(lock) = true ∧
        lock_held s t'⌝)%L.
  - apply (leads_to_assume _ all_invs_ok).
    lt_unfold.
    intros [[HW [Hq Hl]] Hinv].
    destruct Hinv as [_ Hlocked Hnodup Hwaiting _];
      autounfold with inv in *.
    destruct s as [[l q] ?]; simpl in *; subst.
    destruct Hlocked as [t' ?]; eauto.
    exists t'; intuition eauto.
    { exists nil; rewrite app_nil_r. split; first by eauto.
      apply NoDup_cons_inv in Hnodup; intuition auto. }
  - apply leads_to_exist_intro => t'.
    unfold lock_held.

(*|
This "detour" is actually really interesting: you might think that simple transitivity is enough, because if t' has the lock, it will release the lock, then signal to t (transitivity is needed because this is two steps from thread t'). However, this is _not_ the case. It is possible for t' to release the lock, and then for some other thread to happen to do a CAS, acquire the lock, unlock it, and then send the signal to t; the original t' will now signal some other thread. This is unusual because t' is trying to signal something to t but some unrelated thread swoops in and does it instead, many steps later.
|*)
    apply (leads_to_detour ⌜λ s,
      wait_set s.(tp) ⊆ W ∧
      ((∃ ts' : list Tid, s.(state).(queue) = t :: ts ++ ts') ∧
      s.(tp) !! t = Some pc.kernel_wait ∧
       s.(tp) !! t' = Some pc.unlock_wake)⌝).

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
          eexists (_ ++ [t'']).
          rewrite !app_assoc; split; first by eauto.
          rewrite NoDup_cons_inv in Hnodup Hnodup'.
          rewrite elem_of_app elem_of_list_singleton; intuition subst.
          rewrite NoDup_cons_inv NoDup_app1 in Hnodup'.
          set_solver+ Hnodup'.
        + assert (t'' ≠ t) by set_solver.
          stm.
        + assert (t' = t''); subst.
          { apply Hsafe; eauto. }
          right; stm.
      - stm.
      - stm.
        eexists; split; first by eauto.
        intuition congruence. }

    { apply (mutex_wf1 t'); cbn.
      - intro t''; intros.
        destruct Hinv as [_ _  Hnodup _ _];
          autounfold with inv in *; simpl in *.
        stm_simp.

        destruct_step; stm_simp;
          try solve [ eauto 6 ].
        + left; intuition eauto.
          eexists (_ ++ [t'']).
          rewrite !app_assoc; split; eauto.
        + assert (t'' ≠ t) by set_solver.
          stm.
        + right. eexists; intuition eauto.
          apply NoDup_head_not_in in Hnodup; auto.
      - intros.
        stm.
        destruct Hinv as [_ _ Hnodup _ _];
          autounfold with inv in *; simpl in *.
        apply NoDup_head_not_in in Hnodup; auto.
      - intros.
        stm.
        eexists; split; first by eauto.
        intuition congruence. }
Qed.

Lemma __futex_wait_progress t W :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        s.(tp) !! t = Some pc.futex_wait⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        wait_set s.(tp) = W ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        s.(state).(lock) = true⌝.
Proof.
  apply (leads_to_detour
           ⌜λ s, wait_set s.(tp) = W ∧
                 s.(state).(lock) = false ∧
                 s.(tp) !! t = Some pc.lock_cas⌝).
  { tla_simp.
    apply (mutex_wf1 t); simpl; intros.
    - destruct_step; stm.
    - stm.
      destruct l0; stm.
    - naive_solver. }
  lt_apply lock_cas_unlocked_progress.
Qed.

Lemma __queue_gets_popped W t ts :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W ∧
        s.(state).(queue) = t :: ts⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (wait_set s.(tp) ⊆ W ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        t ∉ s.(state).(queue))⌝.
Proof.
  apply leads_to_if_lock.
  - lt_apply queue_gets_popped_unlocked.
  - lt_apply __queue_gets_popped_locked.
Qed.

Definition no_wake_threads tp :=
  ∀ t pc, tp !! t = Some pc → pc ≠ pc.unlock_wake.

(** This is never used, but it's an interesting observation. I was hoping to use
it to avoid decreasing a lexicographic tuple, but this strategy doesn't really
work: after waiting for the wake threads to go away, threads may have
re-arranged and the original kernel_wait threads may now be in lock_cas, for
example. *)
Lemma __eventually_no_wake_threads W :
  spec ⊢
  ⌜λ s, wait_set s.(tp) = W⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        s.(state).(lock) = false ∨
        wait_set s.(tp) = W ∧
        s.(state).(lock) = true ∧
        no_wake_threads s.(tp)⌝.
Proof.
  set (h S s := wait_set s.(tp) ⊂ W ∨
                s.(state).(lock) = false ∨
                wait_set s.(tp) = W ∧
                signal_set s.(tp) = S ∧
                s.(state).(lock) = true
      ).
  lt_apply (lattice_leads_to_ex gset_subset_wf h ∅).
  - lt_auto.
    rewrite /h. destruct s.(state).(lock); eauto. naive_solver.
  - intros S Hnotempty.
    rewrite /h.
    assert (∃ t, t ∈ S) as [t Hel].
    { apply set_choose_L in Hnotempty; naive_solver. }
    leads_to_trans (⌜λ s, wait_set s.(tp) ⊂ W ∨
                     s.(state).(lock) = false ∨
                    ∃ U', U' ⊂ S ∧
                            wait_set s.(tp) = W ∧
                            signal_set s.(tp) = U' ∧
                            s.(state).(lock) = true⌝).
    2: { lt_auto naive_solver. }
    leads_to_trans (⌜λ s, wait_set s.(tp) ⊂ W⌝ ∨
                    ⌜λ s, s.(state).(lock) = false⌝ ∨
                    ⌜λ s, wait_set s.(tp) = W ∧
                          signal_set s.(tp) = S ∧
                          s.(state).(lock) = true⌝
                   )%L.
    { lt_auto naive_solver. }
    lt_split; first by lt_auto.
    lt_split; first by lt_auto.
    apply (mutex_wf1 t); simpl; intros.
    + destruct_step; stm.
      * assert (t' ∈ signal_set tp) by eauto.
        assert (t' ∉ wait_set tp) by eauto.
        right; right; right.
        eexists; intuition eauto.
    + stm_simp.
      apply elem_signal_set in Hel.
      stm_simp.
      right; right.
      eexists; intuition eauto.
    + stm_simp.
      apply elem_signal_set in Hel.
      naive_solver.
  - rewrite /h /no_wake_threads.
    lt_auto.
    intros [| [|]]; eauto.
    right; right.
    intuition eauto.
    subst.
    assert (t ∈ signal_set s.(tp)) by eauto.
    set_solver.

    Unshelve.
    all: exact inhabitant.
Qed.

End example.
