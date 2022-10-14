From Coq.Relations Require Import Relation_Operators.
From Coq.Wellfounded Require Import Lexicographic_Product.

From TLA Require Import logic.
From TLA.examples.mutex Require Import spec wait_set nodup automation safety.

Section example.

Implicit Types (σ: State) (s: Config) (t: Tid).
Implicit Types (l: bool) (q: list Tid).

Lemma fair_step (tid: nat) :
  fair ⊢ weak_fairness (step tid).
Proof.
  unfold fair.
  (* apply doesn't work due to the wrong unification heuristics *)
  refine (forall_apply _ _).
Qed.

(* NOTE: this monotonicity proof isn't actually used (although its relative
simplicity does demonstrate that the automation is working) *)

Hint Extern 2 (_ ⊆ _) => set_solver : core.

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

Lemma subseteq_to_subset (W W': gset Tid) :
  W' ⊆ W → W' = W ∨ W' ⊂ W.
Proof.
  intros.
  destruct (decide (W = W')); eauto.
  set_solver.
Qed.

(* this is an implication but leads_tos are more convenient *)
Lemma waiters_are_monotonic W :
  spec ⊢
  ⌜waiters_are W⌝ ~~>
  □⌜λ s, waiters_are W s ∨ ∃ W', W' ⊂ W ∧ waiters_are W' s⌝.
Proof.
  rewrite -leads_to_impl_internal.
  rewrite /spec. tla_clear ⌜init⌝. tla_clear fair.
  apply always_induction_impl_pred.
  - eauto.
  - rewrite /waiters_are.
    intros s s' Hwait_set.
    intros Hsubset%waiters_monotonic_next.
    apply subseteq_to_subset in Hsubset.
    (intuition idtac); subst; repeat deex; eauto.
    right. eexists; split; [ | done ].
    set_solver.
Qed.

(* specialized wf1 rule that handles some common manipulation for this state
machine *)
Lemma mutex_wf1 (t: Tid) (P Q: Config → Prop) :
  (∀ t' σ tp pc σ' pc',
     let s := {| state := σ; tp := tp|} in
     let s' := {| state := σ'; tp := <[t' := pc']> tp |} in
     P s →
     t ≠ t' →
     tp !! t' = Some pc →
     thread_step t' (σ, pc) (σ', pc') →
     P s' ∨ Q s'
  ) →
  (∀ σ tp pc σ' pc',
     let s := {| state := σ; tp := tp|} in
     let s' := {| state := σ'; tp := <[t := pc']> tp |} in
     P s →
     tp !! t = Some pc →
     thread_step t (σ, pc) (σ', pc') →
     Q s'
  ) →
  (∀ l q tp,
     P {| state := {| lock := l; queue := q |}; tp := tp |} →
     ∃ pc, tp !! t = Some pc ∧
           (pc = pc.kernel_wait → t ∉ q) ∧
           pc ≠ pc.finished
  ) →
  spec ⊢ ⌜P⌝ ~~> ⌜Q⌝.
Proof.
  simpl.
  intros H1 H2 H3.
  tla_apply (wf1 (step t)).
  { rewrite /spec.
    tla_split; [ tla_assumption | tla_apply fair_step ]. }
  - intros [σ tp] [σ' tp'].
    intros Hp Hnext.
    destruct Hnext as [ [t' Hstep] | Heq].
    + destruct Hstep as [pc [Hlookup [ρ' [Hstep Heq]]]].
      invc Heq.
      destruct ρ' as [σ' pc']; simpl in *.
      (* in one branch we use the proof that P ∨ Q is preserved, in the other we
      use the proof that [step t] leads to Q *)
      destruct (decide (t = t')); subst; eauto.
    + invc Heq; eauto.
  - intros [σ tp] [σ' tp'].
    intros Hp Hnext Hstep.
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]].
    invc Heq.
    destruct ρ' as [σ' tp']; simpl in *.
    eauto.
  - intros [[l q] tp] HP.
    rewrite step_enabled /=.
    eauto.
Qed.

Lemma list_elem_of_head {A} (l: list A) (x: A) :
  x ∈ x::l.
Proof. set_solver. Qed.

Lemma list_not_elem_of_head {A} (l: list A) (x y: A) :
  x ∉ y::l → x ≠ y.
Proof. set_solver. Qed.

Hint Resolve list_elem_of_head list_not_elem_of_head : core.

Lemma queue_gets_popped_locked W t ts :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(state).(queue) = t :: ts ∧
        s.(state).(lock) = true⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊆ W ∧
       (∃ ts', s.(state).(queue) = ts ++ ts') ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        t ∉ s.(state).(queue)⌝.
Proof.
  rewrite /waiters_are.
  leads_to_trans (∃ t', ⌜λ s,
        wait_set s.(tp) = W ∧
        (∃ ts', s.(state).(queue) = t :: ts ++ ts' ∧
                t ∉ ts ++ ts') ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        s.(state).(lock) = true ∧
        lock_held s t'⌝)%L.
  - rewrite exist_state_pred.
    apply (leads_to_assume _ locked_inv_ok).
    apply (leads_to_assume _ nodup_helper_inv_ok).
    tla_simp.
    apply pred_leads_to => s [[[HW [Hq Hl]] Hinv] Hnodup].
    destruct Hnodup as [Hnodup Hwaiting].
    rewrite /waiting_inv in Hwaiting.
    destruct s as [[l q] ?]; simpl in *; subst.
    destruct Hinv as [t' ?]; eauto.
    exists t'; intuition eauto.
    { exists nil; rewrite app_nil_r. split; first by eauto.
      rewrite /nodup_inv /= in Hnodup.
      apply NoDup_cons_inv in Hnodup; intuition auto. }
  - apply leads_to_exist_intro => t'.
    apply (add_safety queue_invs).
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
      tla_apply (wf1 (step t')).
      { tla_split; [ tla_assumption | tla_apply fair_step ]. }
      - intros [σ tp] [σ' tp'] => /= [[Hwaiters Hinv] Hnext].
        destruct Hnext  as (Hnext & [Hexclusion Hnodup] & [_ Hnodup']).
        destruct Hnext as [ [t'' Hstep] | Heq]; [ | stm_simp; by eauto 8 ].
        destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]].
        stm_simp.

        destruct_step; stm_simp;
          try (assert (t' ≠ t'') as Hneq by congruence);
          try solve [ eauto 8 ].
        + left; intuition eauto.
          eexists (_ ++ [t'']).
          rewrite !app_assoc; split; first by eauto.
          rewrite /nodup_inv /= NoDup_cons_inv in Hnodup Hnodup'.
          rewrite elem_of_app elem_of_list_singleton; intuition subst.
          rewrite NoDup_cons_inv NoDup_app1 in Hnodup'.
          set_solver+ Hnodup'.
        + assert (t'' ≠ t) by set_solver.
          stm.
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
        rewrite thread_step_eq /= in H2.
        stm.
      - intros [[q l] tp] ?. rewrite step_enabled.
        stm.
        eexists; split; first by eauto.
        intuition congruence. }

    { tla_apply (wf1 (step t')).
      { tla_split; [ tla_assumption | tla_apply fair_step ]. }
      - intros [σ tp] [σ' tp'] => /= [Hinv Hnext].
        destruct Hnext  as (Hnext & [Hexclusion Hnodup] & [_ Hnodup']).
        destruct Hnext as [ [t'' Hstep] | Heq]; [ | by  stm ].
        destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]].
        stm_simp.

        destruct_step; stm_simp;
          try (assert (t' ≠ t'') as Hneq by congruence);
          try solve [ eauto 6 ].
        + left; intuition eauto.
          eexists (_ ++ [t'']).
          rewrite !app_assoc; split; eauto.
        + assert (t'' ≠ t) by set_solver.
          stm.
        + right. eexists; intuition eauto.
          rewrite /nodup_inv /= in Hnodup.
          apply NoDup_head_not_in in Hnodup; auto.
      - intros [[q l] tp] [σ' tp'] => /= Hp.
        destruct_and!; subst; repeat deex.
        (* drop next *)
        intros (_ & [_ Hnodup] & _) Hstep.
        rewrite /step /= in Hstep; stm_simp.
        assert (pc = pc.unlock_wake) by congruence; subst.
        rewrite thread_step_eq /= in H2.
        stm.
        rewrite /nodup_inv /= in Hnodup.
        apply NoDup_head_not_in in Hnodup; auto.
      - intros [[q l] tp] ?. rewrite step_enabled.
        stm.
        eexists; split; first by eauto.
        intuition congruence. }
Qed.

Lemma eventually_unlock W :
  spec ⊢
  ⌜waiters_are W⌝ ~~>
  ⌜λ s, waiters_are W s ∧ s.(state).(lock) = false⌝.
Proof.
  apply (leads_to_if ⌜λ s, s.(state).(lock) = true⌝); tla_simp.
  2: {
    apply pred_leads_to => s.
    destruct (s.(state).(lock)); intuition auto.
  }

  (* somebody must hold the lock *)
  eapply leads_to_assume; [ apply locked_inv_ok | ].
  tla_simp.
  leads_to_trans (∃ t, ⌜λ s, waiters_are W s ∧
                             s.(state).(lock) = true ∧
                             lock_held s t⌝)%L.
  { rewrite exist_state_pred.
    apply pred_leads_to => s.
    rewrite /locked_inv.
    naive_solver. }
  apply leads_to_exist_intro => t0.

  tla_apply (wf1 (step t0)).
  { rewrite /spec.
    tla_split; [ tla_assumption | tla_apply fair_step ]. }
  - move => [σ tp] [σ' tp'] /=.
    rewrite /waiters_are /lock_held /=.
    intros (Hwait & Hlock & Ht0) Hnext; subst.
    destruct Hnext as [ [t Hstep] | Heq]; [ | stm_simp; by eauto ].
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    destruct_step; stm_simp; simp_props; auto.
    + right.
      assert (t ∉ wait_set tp) by eauto.
      set_solver.
    + left.
      assert (t ∉ wait_set tp) by eauto.
      set_solver.
  - move => [σ tp] [σ' tp'] /=.
    rewrite /waiters_are /lock_held /=.
    intros (Hwait & Hlock & Ht0) _ Hstep; subst.
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    assert (pc'' = pc.unlock_store) by congruence; subst.
    rewrite thread_step_eq /thread_step_def in Hstep; stm.
  - move => [[l q] tp] /=.
    rewrite /waiters_are /lock_held /=.
    intros (? & ? & Hlookup); subst.
    rewrite step_enabled /=.
    naive_solver.
Qed.

Lemma lock_cas_progress t W :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(state).(lock) = false ∧
        s.(tp) !! t = Some pc.lock_cas⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W⌝.
Proof.
  rewrite /waiters_are /=.
  tla_apply (wf1 (step t)).
  { rewrite /spec. tla_split; [ tla_assumption | tla_apply fair_step ]. }
  - move => [σ tp] [σ' tp'] /=.
    intros (Hwait & Hpc) Hnext; subst.
    destruct Hnext as [ [t' Hstep] | Heq]; [ | stm_simp; by eauto ].
    destruct Hstep as [pc [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    destruct_step; stm; simp_props; eauto 8.
  - move => [σ tp] [σ' tp'] /=.
    intros (Hwait & Hpc) _ Hstep; subst.
    destruct Hstep as [pc [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    assert (pc = pc.lock_cas) by congruence; subst.
    rewrite thread_step_eq /thread_step_def in Hstep; stm.
  - move => [[l q] tp] /=.
    intros (? & Hpc); subst.
    rewrite step_enabled /=.
    naive_solver.
Qed.

Lemma futex_wait_progress t W :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(tp) !! t = Some pc.futex_wait⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        wait_set s.(tp) = W ∧
        s.(tp) !! t = Some pc.kernel_wait⌝.
Proof.
  rewrite /waiters_are /=.
  apply (leads_to_detour
           ⌜λ s, wait_set s.(tp) = W ∧
                 s.(state).(lock) = false ∧
                 s.(tp) !! t = Some pc.lock_cas⌝).
  { tla_simp.
    tla_apply (wf1 (step t)).
    { rewrite /spec. tla_split; [ tla_assumption | tla_apply fair_step ]. }
    - move => [σ tp] [σ' tp'] /=.
      intros (Hwait & Hpc) Hnext; subst.
      destruct Hnext as [ [t' Hstep] | Heq]; [ | stm_simp; by eauto ].
      destruct Hstep as [pc [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
      destruct_step; stm; simp_props; eauto 8.
      + destruct (decide (t = t')); subst; lookup_simp; eauto.
      + destruct (decide (t = t')); subst; lookup_simp; eauto.
    - move => [σ tp] [σ' tp'] /=.
      intros (Hwait & Hpc) _ Hstep; subst.
      destruct Hstep as [pc [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
      assert (pc = pc.futex_wait) by congruence; subst.
      rewrite thread_step_eq /thread_step_def in Hstep; stm.
      destruct l0; stm.
    - move => [[l q] tp] /=.
      intros (? & Hpc); subst.
      rewrite step_enabled /=.
      naive_solver. }
  leads_to_etrans; [ apply lock_cas_progress | ].
  apply pred_leads_to => s; naive_solver.
Qed.

(* if there is a thread t in pc.kernel_wait, then either the queue is empty, in
which case weak_fairness (step t) easily gets t to pc.lock_cas, or it has a head element t', in which case that thread will get to cas *)

(* this is actually an implication but everything is setup to use leads_to *)
Lemma kernel_wait_head_queue t W :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(tp) !! t = Some pc.kernel_wait⌝ ~~>
  ⌜λ s, waiters_are W s ∧
        (s.(state).(queue) = [] ∧
          s.(tp) !! t = Some pc.kernel_wait) ∨
          (∃ t', ∃ ts, s.(state).(queue) = t' :: ts ∧
                s.(tp) !! t' = Some pc.kernel_wait)⌝.
Proof.
  eapply leads_to_assume.
  { apply nodup_helper_inv_ok. }
  tla_simp. apply pred_leads_to.
  intros [[q l] tp].
  rewrite /waiters_are /nodup_helper_inv /waiting_inv /=.
  intros ([? Hlookup] & _ & Hq_wait); subst.
  destruct l; [ left; by eauto | right ].
  eexists _, _; intuition eauto.
Qed.

Lemma kernel_wait_head_progress t W :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
       ∃ ts, s.(state).(queue) = t::ts ∧
             s.(tp) !! t = Some pc.kernel_wait⌝ ~~>
  ⌜λ s, (∃ W', W' ⊂ W ∧ waiters_are W' s) ∨
        waiters_are W s ∧
        s.(tp) !! t = Some pc.lock_cas⌝.
Proof.
Abort.

Lemma queue_gets_popped_unlocked W t ts :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(state).(queue) = t :: ts ∧
        s.(state).(lock) = false⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊆ W ∧
        (s.(state).(queue) = ts ∧
           t ∉ s.(state).(queue) ∧
           s.(tp) !! t = Some pc.kernel_wait ∨
         s.(state).(queue) = t :: ts ∧
           s.(state).(lock) = true)⌝.
Proof.
  apply (leads_to_assume _ lock_free_queue_inv_ok); tla_simp.
  rewrite /lock_free_queue_inv.

  leads_to_trans (∃ t', ⌜ λ s,
                    wait_set s.(tp) ⊆ W ∧
                    s.(state).(queue) = t :: ts ∧
                    s.(state).(lock) = false ∧
                    thread_can_lock t' s
                   ⌝)%L.
  { rewrite exist_state_pred.
    apply pred_leads_to.
    rewrite /waiters_are.
    move => [[l q] tp] /= [[Hwaiters [? ?]] Hcan_lock]; simpl; subst.
    specialize (Hcan_lock _ _ ltac:(eauto)); stm. }

  apply leads_to_exist_intro => t'.

  apply (add_safety nodup_helper_inv_ok).

  apply (leads_to_detour
    ⌜λ s, wait_set s.(tp) ⊆ W ∧
         s.(state).(queue) = t::ts ∧
         s.(tp) !! t = Some pc.kernel_wait ∧
         s.(state).(lock) = false ∧
         s.(tp) !! t' = Some pc.lock_cas⌝).

  { tla_simp.
    tla_apply (wf1 (step t')).
    { rewrite /spec. tla_split; [ tla_assumption | tla_apply fair_step ]. }

    - move => [σ tp] [σ' tp'] /=.
      rewrite /nodup_helper_inv /nodup_inv /=.
      intros (Hwaiters & Hq & Hlock & Hcan_lock).
      intros (Hnext & [Hnodup Hwaiting] & _); simpl; subst.
      destruct Hnext as [ [t'' Hstep] | Heq]; [ | stm_simp; by eauto ].
      destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
      destruct_step; stm_simp; simp_props; eauto.
      + left.
        rewrite /thread_can_lock /= in Hcan_lock |- *.
        assert (t' ≠ t'') by intuition congruence.
        lookup_simp; eauto.
      + left; intuition auto.
        rewrite /thread_can_lock /= in Hcan_lock |- *.
        destruct (decide (t' = t'')); lookup_simp; eauto.
      + left.
        rewrite /thread_can_lock /= in Hcan_lock |- *.
        destruct (decide (t' = t'')); lookup_simp; eauto.
      + assert (t ∉ ts) by (inversion Hnodup; auto).
        rewrite /waiting_inv in Hwaiting.
        assert (t'' ≠ t) by set_solver.
        right; right; left. stm.
    - move => [σ tp] [σ' tp'] /=.
      intros (Hwaiters & Hq & Hlock & Hcan_lock) (_ & Hnodup & _) Hstep; subst.
      destruct Hnodup as [Hnodup Hwaiting].
      rewrite /nodup_inv /= in Hnodup.
      rewrite /waiting_inv /= in Hwaiting.
      destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
      assert (t ∉ ts) by (inversion Hnodup; auto).
      rewrite thread_step_eq /thread_step_def in Hstep.
      assert (tp !! t = Some pc.kernel_wait) by eauto.
      rewrite /thread_can_lock /= in Hcan_lock;
        (intuition idtac).
      + assert (pc'' = pc.unlock_wake) by congruence; stm.
      + assert (pc'' = pc.kernel_wait) by congruence; stm.
        assert (t ≠ t') by set_solver. stm.
      + assert (pc'' = pc.lock_cas) by congruence; stm.
    - move => [[l q] tp] /=.
      intros (? & ? & Hlookup); subst.
      rewrite step_enabled /=.
      rewrite /thread_can_lock /= in Hlookup.
      naive_solver. }

    tla_apply (wf1 (step t')).
    { rewrite /spec. tla_split; [ tla_assumption | tla_apply fair_step ]. }

    - move => [σ tp] [σ' tp'] /=.
      intros (Hq & Hlock & Hcan_lock) (Hnext & Hnodup & _); subst.
      destruct Hnodup as [Hnodup Hwaiting].
      rewrite /nodup_inv /= in Hnodup.
      destruct Hnext as [ [t'' Hstep] | Heq]; [ | by stm ].
      destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
      assert (t ∉ ts) by (inversion Hnodup; auto).
      destruct_step; stm.
      assert (t'' ≠ t) by set_solver.
      stm.
    - move => [σ tp] [σ' tp'] /=.
      intros (Hq & Hlock & Hcan_lock) _ Hstep; subst.
      destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
      rewrite thread_step_eq /thread_step_def in Hstep.
      assert (pc'' = pc.lock_cas) by congruence; stm.
    - move => [[l q] tp] /=.
      intros (? & ? & Hlookup); subst.
      rewrite step_enabled /=.
      naive_solver.
Qed.

Lemma queue_gets_popped W t ts :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(state).(queue) = t :: ts⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊆ W ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        t ∉ s.(state).(queue)⌝.
Proof.
  apply (leads_to_if ⌜λ s, s.(state).(lock) = true⌝);
    tla_simp.
  - lt_apply queue_gets_popped_locked.
  - lt_apply queue_gets_popped_unlocked.
    { lt_unfold. rewrite not_true_iff_false. naive_solver. }
    leads_to_trans
      (⌜λ s, wait_set s.(tp) ⊆ W ∧
               s.(tp) !! t = Some pc.kernel_wait ∧
               t ∉ s.(state).(queue)⌝ ∨
       ⌜λ s, wait_set s.(tp) ⊆ W ∧
               s.(state).(queue) = t::ts ∧
               s.(state).(lock) = true⌝
      )%L.
    { lt_auto tauto. }
    rewrite leads_to_or_split; tla_split; [ lt_auto | ].
    leads_to_trans (∃ W' (_: W' ⊆ W), ⌜λ s, wait_set s.(tp) = W' ∧
                                s.(state).(queue) = t::ts ∧
                                s.(state).(lock) = true⌝)%L.
    { lt_auto naive_solver. }
    apply leads_to_exist_intro => W'.
    apply leads_to_exist_intro => Hsub.
    lt_apply queue_gets_popped_locked.
Qed.

Lemma kernel_wait_not_queued_progress W t :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        t ∉ s.(state).(queue)⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        wait_set s.(tp) = W ∧
          s.(tp) !! t = Some pc.lock_cas⌝.
Proof.
  rewrite /waiters_are.
  tla_apply (wf1 (step t)).
  { rewrite /spec. tla_split; [ tla_assumption | tla_apply fair_step ]. }

  - move => [σ tp] [σ' tp'] /=.
    intros (Hwait & Ht & Hnotin) Hnext; subst.
    destruct Hnext as [ [t' Hstep] | Heq]; [ | by stm ].
    destruct Hstep as [pc [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    destruct_step; stm; simp_props.
    + assert (t ≠ t') by congruence.
      left. set_solver.
    + destruct (decide (t = t')); lookup_simp; eauto.
    + assert (t ∉ pop q0) by (intros ?%elem_of_pop; auto).
      assert (t' ∉ wait_set tp) by eauto.
      eauto.
  - move => [σ tp] [σ' tp'] /=.
    intros (Hwait & Ht & Hnotin) _ Hstep; subst.
    destruct Hstep as [pc [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    rewrite thread_step_eq /thread_step_def in Hstep.
    assert (pc = pc.kernel_wait) by congruence; stm.
  - move => [[l q] tp] /=.
    intros (? & ? & Hlookup); subst.
    rewrite step_enabled /=.
    naive_solver.
Qed.

Lemma kernel_wait_progress W t :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(tp) !! t = Some pc.kernel_wait⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (∃ t', wait_set s.(tp) ⊆ W ∧
               s.(tp) !! t' = Some pc.lock_cas)⌝.
Proof.
  rewrite /waiters_are.
  apply (leads_to_if ⌜λ s, t ∈ s.(state).(queue)⌝).
  - tla_simp.
    leads_to_trans (∃ t0 ts0,
                       ⌜λ s, wait_set s.(tp) = W ∧
                             s.(tp) !! t = Some pc.kernel_wait ∧
                             s.(state).(queue) = t0::ts0⌝)%L.
    + lt_auto intuition idtac.
      destruct s.(state).(queue) eqn:Hq; [ exfalso; set_solver | ].
      naive_solver.
    + apply leads_to_exist_intro => t0.
      apply leads_to_exist_intro => ts0.
      lt_apply queue_gets_popped.

      leads_to_trans (∃ W' (_: W' ⊆ W),
                         ⌜λ s, wait_set s.(tp) = W' ∧
                                 s.(tp) !! t0 = Some pc.kernel_wait ∧
                                 t0 ∉ s.(state).(queue)⌝)%L.
      { lt_auto intuition eauto. }

      apply leads_to_exist_intro => W'.
      apply leads_to_exist_intro => Hle.
      lt_apply kernel_wait_not_queued_progress.
      lt_auto intuition eauto.
      left; set_solver.
  - tla_simp.
    lt_apply kernel_wait_not_queued_progress.
Qed.

End example.
