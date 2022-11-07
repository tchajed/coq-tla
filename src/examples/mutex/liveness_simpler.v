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
    apply next_inv in Hnext as
        [[[=] ?] |
          (t' & pc & pc' & Hlookup & Hstep & ?)]; subst; eauto.
    (* in one branch we use the proof that P ∨ Q is preserved, in the other we
    use the proof that [step t] leads to Q *)
    destruct (decide (t = t')); subst; eauto.
  - intros [σ tp] [σ' tp'].
    intros Hp [_ [Hinvs Hinvs']] Hstep.
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]].
    invc Heq.
    destruct ρ' as [σ' tp']; simpl in *.
    eauto.
  - intros [[l q] tp] HP.
    rewrite step_enabled /=.
    eauto.
Qed.

Definition measure (s: Config) : gset Tid * gset Tid * gset Tid :=
  (wait_set s.(tp), pc_set pc.unlock_store s.(tp), pc_set pc.unlock_wake s.(tp)).

Definition h_lt : relation (gset Tid * gset Tid * gset Tid) :=
  slexprod _ _ (slexprod _ _ (⊂) (⊂)) (⊂).

Infix "≺" := h_lt (at level 70).

Definition h_le : relation (gset Tid * gset Tid * gset Tid) :=
  λ ss ss', ss = ss' ∨ ss ≺ ss'.

Infix "⪯" := h_le (at level 70).

Lemma unlock_set_lock_inv s :
  all_invs s →
  s.(state).(lock) = true →
  ∃ t, pc_set pc.unlock_store s.(tp) = {[t]} ∧
       s.(tp) !! t = Some pc.unlock_store.
Proof.
  destruct 1; intros Hlock.
  apply Hlocked in Hlock as [t Hlock].
  rewrite /lock_held in Hlock.
  exists t; intuition idtac.
  cut ({[t]} ⊆ pc_set pc.unlock_store s.(tp) ⊆ {[t]}); [ set_solver | ].
  split.
  - apply singleton_subseteq_l.
    auto.
  - apply elem_of_subseteq => t'.
    rewrite elem_pc_set => Hlock'.
    assert (t = t') by (apply Hexcl; eauto); set_solver.
Qed.

Lemma unlock_set_unlocked_inv s :
  all_invs s →
  pc_set pc.unlock_store s.(tp) = ∅ →
  s.(state).(lock) = false.
Proof.
  intros Hinv Hempty.
  destruct s.(state).(lock) eqn:Hlock; [ exfalso | done ].
  apply unlock_set_lock_inv in Hlock as [t Hlock]; intuition idtac.
  set_solver.
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

Hint Constructors slexprod : core.

Lemma measure_lt_unfold Sₗ Sᵤ S__w Sₗ' Sᵤ' S__w' :
  (Sₗ', Sᵤ', S__w') ≺ (Sₗ, Sᵤ, S__w) ↔
  Sₗ' ⊂ Sₗ ∨
  (Sₗ' = Sₗ ∧ Sᵤ' ⊂ Sᵤ) ∨
  (Sₗ' = Sₗ ∧ Sᵤ' = Sᵤ ∧ S__w' ⊂ S__w).
Proof.
  split.
  - intros H; invc H; eauto.
    invc H1; eauto.
  - rewrite /h_lt. intuition (subst; eauto).
Qed.

Lemma tuple_eq_unfold (S1 S2 S3 S1' S2' S3': gset Tid) :
  (S1, S2, S3) = (S1', S2', S3') ↔
  S1 = S1' ∧ S2 = S2' ∧ S3 = S3'.
Proof. naive_solver. Qed.

Hint Rewrite tuple_eq_unfold measure_lt_unfold : pc.

Lemma eventually_wake_progress Sₗ Sᵤ S__w :
  S__w ≠ ∅ →
  spec ⊢ ⌜λ s, measure s = (Sₗ, Sᵤ, S__w)⌝ ~~>
         ⌜λ s, measure s ≺ (Sₗ, Sᵤ, S__w)⌝.
Proof.
  intros [t Hel]%set_choose_L.
  rewrite /measure.
  apply (mutex_wf1 t); simpl; intros.
  - destruct_step; stm.
  - assert (pc = pc.unlock_wake); [ | by stm ].
    { stm.
      apply elem_pc_set in Hel; congruence. }
  - assert (tp !! t = Some pc.unlock_wake); [ | naive_solver ].
    stm.
    apply elem_pc_set in Hel; congruence.
Qed.

Lemma eventually_unlock_progress Sₗ Sᵤ S__w :
  Sᵤ ≠ ∅ →
  spec ⊢ ⌜λ s, measure s = (Sₗ, Sᵤ, S__w)⌝ ~~>
         ⌜λ s, measure s ≺ (Sₗ, Sᵤ, S__w)⌝.
Proof.
  intros [t Hel]%set_choose_L.
  rewrite /measure.
  apply (mutex_wf1 t); simpl; intros.
  - destruct_step; stm.
  - assert (pc = pc.unlock_store); [ | by stm ].
    { stm.
      apply elem_pc_set in Hel; congruence. }
  - assert (tp !! t = Some pc.unlock_store); [ | naive_solver ].
    stm.
    apply elem_pc_set in Hel; congruence.
Qed.

Lemma eventually_atomic_cas_progress Sₗ t :
  spec ⊢ ⌜λ s, measure s = (Sₗ, ∅, ∅) ∧
               s.(tp) !! t = Some pc.lock_cas ⌝ ~~>
         ⌜λ s, measure s ≺ (Sₗ, ∅, ∅)⌝.
Proof.
  rewrite /measure.
  apply (mutex_wf1 t); simpl; intros.
  - destruct_step; stm.
  - stm.
    destruct l0; stm.
    exfalso.
    apply unlock_set_lock_inv in Hinv as [t' ?]; intuition.
    simpl in *.
    set_solver.
  - naive_solver.
Qed.

Lemma eventually_futex_wait_progress Sₗ t :
  spec ⊢ ⌜λ s, measure s = (Sₗ, ∅, ∅) ∧
               s.(tp) !! t = Some pc.futex_wait ⌝ ~~>
         ⌜λ s, measure s ≺ (Sₗ, ∅, ∅)⌝.
Proof.
  eapply leads_to_detour; [ | apply (eventually_atomic_cas_progress _ t); eauto ].
  lt_simp.
  rewrite /measure.
  apply (mutex_wf1 t); simpl; intros.
  - destruct_step; stm.
  - stm.
    destruct l0; stm.
    exfalso.
    apply unlock_set_lock_inv in Hinv as [t' ?]; intuition.
    simpl in *.
    set_solver.
  - naive_solver.
Qed.

Lemma eventually_kernel_wait_progress Sₗ t :
  spec ⊢ ⌜λ s, measure s = (Sₗ, ∅, ∅) ∧
               s.(tp) !! t = Some pc.kernel_wait ⌝ ~~>
         ⌜λ s, measure s ≺ (Sₗ, ∅, ∅)⌝.
Proof.
  lt_simp.
  leads_to_trans (∃ t', ⌜λ s, measure s = (Sₗ, ∅, ∅) ∧
                              (s.(tp) !! t' = Some pc.kernel_wait ∧ t' ∉ s.(state).(queue) ∨
                                s.(tp) !! t' = Some pc.lock_cas)⌝)%L.
  { apply (leads_to_assume _ all_invs_ok).
    lt_unfold.
    intros [ [Hmeasure Hlookup] Hinv ].
    destruct s.(state).(queue) eqn:Hq.
    - exists t; intuition.
      rewrite /thread_can_signal.
      left. intuition.
      set_solver.
    - rewrite /measure in Hmeasure |- *; stm.
      pose proof Hinv as Hinv'.
      apply unlock_set_unlocked_inv in Hinv'; eauto. stm_simp.
      destruct Hinv.
      rewrite /lock_free_queue_inv /= in Hcan_lock.
      edestruct Hcan_lock; eauto.
      destruct H; stm.
  }

  lt_intro t'.
  rewrite -combine_state_preds -combine_or_preds. rewrite ?tla_and_distr_l.
  lt_split_or; lt_simp.
  - eapply leads_to_detour; [ | apply (eventually_atomic_cas_progress _ t'); eauto ].
    rewrite /measure /thread_can_signal.
    lt_simp.
    apply (mutex_wf1 t'); simpl; intros.
    + destruct_step; stm.
      simp_props.
      left; set_solver.
    + stm.
    + naive_solver.
  - lt_apply eventually_atomic_cas_progress.
Qed.

Lemma eventually_lock_progress Sₗ t :
  t ∈ Sₗ →
  spec ⊢ ⌜λ s, measure s = (Sₗ, ∅, ∅) ⌝ ~~>
         ⌜λ s, measure s ≺ (Sₗ, ∅, ∅)⌝.
Proof.
  intros Hel.
  leads_to_trans
    (⌜λ s, measure s = (Sₗ, ∅, ∅)⌝ ∧
    (⌜λ s, s.(tp) !! t = Some pc.lock_cas⌝ ∨
     ⌜λ s, s.(tp) !! t = Some pc.futex_wait⌝ ∨
     ⌜λ s, s.(tp) !! t = Some pc.kernel_wait⌝))%L.
  { lt_unfold.
    intros Hmeasure.
    split; auto.
    rewrite /measure in Hmeasure; stm_simp.
    apply elem_of_wait_set in Hel as [pc [Hlookup H]].
    rewrite /wait_pc in H; naive_solver. }
  lt_split_or; [ | lt_split_or ]; lt_simp.
  - apply eventually_atomic_cas_progress.
  - apply eventually_futex_wait_progress.
  - apply eventually_kernel_wait_progress.
Qed.

Lemma eventually_progress Sₗ Sᵤ S__w :
  (Sₗ, Sᵤ, S__w) ≠ (∅, ∅, ∅) →
  spec ⊢ ⌜λ s, measure s = (Sₗ, Sᵤ, S__w) ⌝ ~~>
         ⌜λ s, measure s ≺ (Sₗ, Sᵤ, S__w)⌝.
Proof.
  intros.
  assert (S__w ≠ ∅ ∨ Sᵤ ≠ ∅ ∨ (S__w = ∅ ∧ Sᵤ = ∅ ∧ Sₗ ≠ ∅)).
  { destruct (decide (S__w = ∅)); subst; auto.
    destruct (decide (Sᵤ = ∅)); subst; auto.
    destruct (decide (Sₗ = ∅)); subst; auto.
  }
  intuition subst.
  - apply eventually_wake_progress; auto.
  - apply eventually_unlock_progress; auto.
  - apply set_choose_L in H3 as [t Hel].
    eapply eventually_lock_progress; eauto.
Qed.

Lemma h_lt_wf :
  well_founded (h_lt).
Proof.
  apply wf_slexprod; [ apply wf_slexprod | ]; apply set_wf.
Qed.

Theorem eventually_terminated :
  spec ⊢ ◇⌜terminated⌝.
Proof.
  apply (leads_to_apply ⌜λ s, True⌝).
  { unseal. }

  set (h := λ ss s, measure s = ss).
  lt_apply (lattice_leads_to_ex h_lt_wf h (∅, ∅, ∅)).

  - lt_unfold; intros _.
    rewrite /h. eauto.
  - intros [[Sₗ Sᵤ] S__w] Hnotempty.
    rewrite /h.
    lt_apply eventually_progress; auto.
    lt_auto.
  - rewrite /h /terminated /measure.
    lt_unfold; stm.
    destruct pc; trivial; exfalso; eauto.
    + assert (tid ∈ wait_set tp) by eauto; set_solver.
    + assert (tid ∈ wait_set tp) by eauto; set_solver.
    + assert (tid ∈ wait_set tp) by eauto; set_solver.
Qed.

End example.
