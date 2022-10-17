From Coq.Relations Require Import Relation_Operators.
From Coq.Wellfounded Require Import Lexicographic_Product.

From TLA Require Import logic.
From TLA.examples.mutex Require Import spec wait_set nodup automation safety.

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
  { rewrite /locked_inv.
    lt_auto naive_solver. }
  lt_intro t0.

  apply (mutex_wf1 t0); simpl; intros.
  - rewrite /waiters_are /lock_held /= in Hpre |- *.
    destruct Hpre as (Hwait & Hlock & Ht0); subst.
    destruct_step; stm_simp; simp_props; auto.
    + right.
      assert (t' ∉ wait_set tp) by eauto.
      set_solver.
    + left.
      assert (t' ∉ wait_set tp) by eauto.
      set_solver.
  - rewrite /waiters_are /lock_held /= in Hpre |- *.
    destruct Hpre as (Hwait & Hlock & Ht0); subst.
    stm.
  - naive_solver.
Qed.

Lemma lock_cas_progress t W :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(state).(lock) = false ∧
        s.(tp) !! t = Some pc.lock_cas⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W⌝.
Proof.
  rewrite /waiters_are /=.
  apply (mutex_wf1 t); simpl; intros.
  - destruct_step; stm.
    eauto 10.
  - stm.
  - naive_solver.
Qed.

Lemma futex_wait_progress t W :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(tp) !! t = Some pc.futex_wait⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        wait_set s.(tp) = W ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        s.(state).(lock) = true⌝.
Proof.
  rewrite /waiters_are /=.
  apply (leads_to_detour
           ⌜λ s, wait_set s.(tp) = W ∧
                 s.(state).(lock) = false ∧
                 s.(tp) !! t = Some pc.lock_cas⌝).
  { tla_simp.
    apply (mutex_wf1 t); simpl; intros.
    - destruct_step; stm.
      eauto 10.
    - stm.
      destruct l0; stm.
    - naive_solver. }
  leads_to_etrans; [ apply lock_cas_progress | ].
  lt_auto.
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

Lemma queue_gets_popped_unlocked W t ts :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
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
  apply (leads_to_assume _ lock_free_queue_inv_ok); tla_simp.
  rewrite /lock_free_queue_inv.

  leads_to_trans (∃ t', ⌜ λ s,
                    wait_set s.(tp) = W ∧
                    s.(state).(queue) = t :: ts ∧
                    s.(state).(lock) = false ∧
                    thread_can_lock t' s
                   ⌝)%L.
  { rewrite exist_state_pred.
    apply pred_leads_to.
    rewrite /waiters_are.
    move => [[l q] tp] /= [[Hwaiters [? ?]] Hcan_lock]; simpl; subst.
    specialize (Hcan_lock _ _ ltac:(eauto)); stm. }

  lt_intro.

  apply (leads_to_detour
    ⌜λ s, wait_set s.(tp) = W ∧
         s.(state).(queue) = t::ts ∧
         s.(tp) !! t = Some pc.kernel_wait ∧
         s.(state).(lock) = false ∧
         s.(tp) !! t' = Some pc.lock_cas⌝); tla_simp.

  { apply (mutex_wf1 t'); simpl.
    - intros t'' **.
      destruct Hinv as [_ _ Hnodup Hwaiting Hcan_lock];
        autounfold with inv in *.
      destruct_step; stm_simp; simp_props; eauto.
      + right; right; left. eauto 10.
      + left.
        rewrite /thread_can_lock /= in Hcan_lock |- *.
        lookup_simp; eauto.
      + left; intuition auto.
        rewrite /thread_can_lock /= in Hcan_lock |- *.
        lookup_simp; eauto.
      + left.
        rewrite /thread_can_lock /= in Hcan_lock |- *.
        lookup_simp; eauto 8.
      + assert (t ∉ ts) by (inversion Hnodup; auto).
        rewrite /waiting_inv in Hwaiting.
        assert (t'' ≠ t) by set_solver.
        right; right; right. stm.
        assert (t'' ∉ wait_set tp) by eauto.
        set_solver.
    - intros.
      destruct Hinv as [_ _ Hnodup Hwaiting Hcan_lock];
        autounfold with inv in *; simpl in *.
      stm_simp.
      assert (t ∉ ts) by (inversion Hnodup; auto).
      stm_simp.
      assert (tp !! t = Some pc.kernel_wait) by (eapply Hwaiting; eauto).
      rewrite thread_step_eq /thread_step_def in Hstep.
      unfold thread_can_lock in *; stm.
      + assert (t ≠ t') by set_solver.
        assert (t' ∉ wait_set tp) by eauto.
        stm.
      + assert (t' ∈ wait_set tp) by eauto.
        assert (t ≠ t') by set_solver.
        lookup_simp; eauto 10.
    - intros. rewrite /thread_can_lock /= in H.
      naive_solver. }

    apply (mutex_wf1 t'); simpl.
    - intros t'' **.
      destruct Hpre as (Hq & Hlock & Hcan_lock).
      destruct Hinv as [_ _ Hnodup Hwaiting _];
        autounfold with inv in *; simpl in *.
      stm_simp.
      assert (t ∉ ts) by (inversion Hnodup; auto).
      destruct_step; stm.
      + assert (t'' ≠ t) by set_solver.
        stm.
      + assert (t'' ∉ wait_set tp) by eauto.
        stm.
    - intros *.
      intros (Hq & Hlock & Hcan_lock) _ Hstep; subst.
      stm.
    - naive_solver.
Qed.

Lemma queue_gets_popped W t ts :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(state).(queue) = t :: ts⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        (wait_set s.(tp) ⊆ W ∧
        s.(tp) !! t = Some pc.kernel_wait ∧
        t ∉ s.(state).(queue)
        (* ∧ s.(state).(lock) = false *))⌝.
Proof.
  apply (leads_to_if ⌜λ s, s.(state).(lock) = true⌝);
    tla_simp.
  - lt_apply queue_gets_popped_locked.
  - lt_apply queue_gets_popped_unlocked.
    { lt_unfold. rewrite not_true_iff_false. naive_solver. }
Qed.

Hint Resolve elem_of_pop : core.

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
  apply (mutex_wf1 t); simpl; intros.
  - destruct Hpre as (Hwait & Ht & Hnotin); subst.
    destruct_step; stm; simp_props.
    + left. set_solver.
    + assert (t ∉ pop q) by auto.
      assert (t' ∉ wait_set tp) by eauto.
      left; set_solver.
  - stm.
  - naive_solver.
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
    + lt_intro t0. lt_intro ts0.
      lt_apply queue_gets_popped.

      leads_to_trans
        (⌜λ s, wait_set s.(tp) ⊂ W⌝ ∨
        ⌜λ s, wait_set s.(tp) ⊆ W ∧
                s.(tp) !! t0 = Some pc.kernel_wait ∧
                t0 ∉ s.(state).(queue)⌝
        )%L.
      { lt_auto naive_solver. }
      rewrite leads_to_or_split; tla_split; [ by lt_auto | ].

      leads_to_trans (∃ W' (_: W' ⊆ W),
                         ⌜λ s, wait_set s.(tp) = W' ∧
                                 s.(tp) !! t0 = Some pc.kernel_wait ∧
                                 t0 ∉ s.(state).(queue)⌝)%L.
      { lt_auto intuition eauto. }

      lt_intros.
      lt_apply kernel_wait_not_queued_progress.
      lt_auto intuition eauto.
      left; set_solver.
  - tla_simp.
    lt_apply kernel_wait_not_queued_progress.
Qed.

Definition no_wake_threads tp :=
  ∀ t pc, tp !! t = Some pc → pc ≠ pc.unlock_wake.

Definition wake_set tp : gset Tid :=
  dom (filter (λ '(_, pc), pc = pc.unlock_wake) tp).

Theorem gset_subset_wf :
  well_founded  ((⊂) : gset Tid → gset Tid → Prop).
Proof. apply set_wf. Qed.

Lemma elem_wake_set tp t :
  t ∈ wake_set tp ↔ tp !! t = Some pc.unlock_wake.
Proof.
  rewrite /wake_set.
  rewrite elem_of_dom filter_is_Some. naive_solver.
Qed.

Lemma elem_wake_set_2 tp t :
  tp !! t = Some pc.unlock_wake →
  t ∈ wake_set tp.
Proof.
  apply elem_wake_set.
Qed.

Lemma not_elem_wake_set tp t pc :
  tp !! t = Some pc →
  pc ≠ pc.unlock_wake →
  t ∉ wake_set tp.
Proof.
  rewrite elem_wake_set.
  naive_solver.
Qed.

Hint Resolve elem_wake_set_2 not_elem_wake_set : core.

Lemma wake_set_insert_same tp t pc pc' :
  tp !! t = Some pc →
  pc ≠ pc.unlock_wake → pc' ≠ pc.unlock_wake →
  wake_set (<[t := pc']> tp) = wake_set tp.
Proof.
  intros.
  apply gset_ext => t'.
  rewrite /wake_set.
  rewrite !elem_of_dom !filter_is_Some.
  destruct (decide (t = t')); lookup_simp; naive_solver.
Qed.

Lemma wake_set_remove tp t pc' :
  pc' ≠ pc.unlock_wake →
  wake_set (<[t := pc']> tp) = wake_set tp ∖ {[t]}.
Proof.
  intros.
  apply gset_ext => t'.
  rewrite /wake_set. rewrite elem_of_difference !elem_of_dom !filter_is_Some.
  rewrite elem_of_singleton.
  destruct (decide (t = t')); lookup_simp; naive_solver.
Qed.

Hint Rewrite wake_set_remove using (by auto) : pc.

Lemma wake_set_subset tp t pc' :
  tp !! t = Some pc.unlock_wake →
  pc' ≠ pc.unlock_wake →
  wake_set (<[t := pc']> tp) ⊂ wake_set tp.
Proof.
  intros.
  rewrite -> wake_set_remove by auto.
  assert (t ∈ wake_set tp) by auto.
  set_solver.
Qed.

Hint Resolve wake_set_insert_same wake_set_subset : core.

Lemma eventually_no_wake_threads W :
  spec ⊢
  ⌜λ s, waiters_are W s ∧
        s.(state).(lock) = true⌝ ~~>
  ⌜λ s, wait_set s.(tp) ⊂ W ∨
        s.(state).(lock) = false ∨
        wait_set s.(tp) = W ∧
        s.(state).(lock) = true ∧
        no_wake_threads s.(tp)⌝.
Proof.
  set (h := λ U, λ s, wait_set s.(tp) ⊂ W ∨
                      s.(state).(lock) = false ∨
                      wait_set s.(tp) = W ∧
                      wake_set s.(tp) = U ∧
                      s.(state).(lock) = true
      ).
  lt_apply (lattice_leads_to_ex gset_subset_wf h ∅).
  - lt_auto.
    rewrite /h. naive_solver.
  - intros U Hnotempty.
    rewrite /h.
    assert (∃ t, t ∈ U) as [t Hel].
    { apply set_choose_L in Hnotempty; naive_solver. }
    leads_to_trans (⌜λ s, wait_set s.(tp) ⊂ W ∨
                     s.(state).(lock) = false ∨
                    ∃ U', U' ⊂ U ∧
                            wait_set s.(tp) = W ∧
                            wake_set s.(tp) = U' ∧
                            s.(state).(lock) = true⌝).
    2: { lt_auto naive_solver. }
    leads_to_trans (⌜λ s, wait_set s.(tp) ⊂ W⌝ ∨
                    ⌜λ s, s.(state).(lock) = false⌝ ∨
                    ⌜λ s, wait_set s.(tp) = W ∧
                          wake_set s.(tp) = U ∧
                          s.(state).(lock) = true⌝
                   )%L.
    { lt_auto naive_solver. }
    rewrite leads_to_or_split; tla_split; [ by lt_auto | ].
    rewrite leads_to_or_split; tla_split; [ by lt_auto | ].
    apply (mutex_wf1 t); simpl; intros.
    + destruct_step; stm.
      * assert (t' ∈ wake_set tp) by eauto.
        assert (t' ∉ wait_set tp) by eauto.
        right; right; right.
        eexists; intuition eauto.
    + stm_simp.
      apply elem_wake_set in Hel.
      stm_simp.
      right; right.
      eexists; intuition eauto.
      assert (t ∉ wait_set tp) by eauto.
      set_solver.
    + stm_simp.
      apply elem_wake_set in Hel.
      naive_solver.
  - rewrite /h /no_wake_threads.
    lt_auto.
    intros [| [|]]; eauto.
    right; right.
    intuition eauto.
    subst.
    assert (t ∈ wake_set s.(tp)) by eauto.
    set_solver.
Qed.

End example.
