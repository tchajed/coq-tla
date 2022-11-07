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

Lemma unlock_set_unlocked_inv' s :
  all_invs s →
  s.(state).(lock) = false →
  pc_set pc.unlock_store s.(tp) = ∅.
Proof.
  destruct 1; intros Hlock.
  apply elem_of_equiv_empty_L => t.
  rewrite elem_pc_set => Hlock'.
  apply Hexcl in Hlock'.
  congruence.
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

Lemma measure_lt1 Sₗ Sᵤ S__w Sₗ' Sᵤ' S__w' :
  Sₗ' ⊂ Sₗ →
  (Sₗ', Sᵤ', S__w') ≺ (Sₗ, Sᵤ, S__w).
Proof.
  rewrite /h_lt. auto.
Qed.

Lemma measure_lt2 Sₗ Sᵤ S__w Sᵤ' S__w' :
  Sᵤ' ⊂ Sᵤ →
  (Sₗ, Sᵤ', S__w') ≺ (Sₗ, Sᵤ, S__w).
Proof.
  rewrite /h_lt. auto.
Qed.

Lemma measure_lt3 Sₗ Sᵤ S__w S__w' :
  S__w' ⊂ S__w →
  (Sₗ, Sᵤ, S__w') ≺ (Sₗ, Sᵤ, S__w).
Proof.
  rewrite /h_lt. auto.
Qed.

Hint Resolve measure_lt1 measure_lt2 measure_lt3 : core.

Lemma measure_lt_unfold Sₗ Sᵤ S__w Sₗ' Sᵤ' S__w' :
  (Sₗ', Sᵤ', S__w') ≺ (Sₗ, Sᵤ, S__w) ↔
  Sₗ' ⊂ Sₗ ∨
  (Sₗ' = Sₗ ∧ Sᵤ' ⊂ Sᵤ) ∨
  (Sₗ' = Sₗ ∧ Sᵤ' = Sᵤ ∧ S__w' ⊂ S__w).
Proof.
  split.
  - intros H; invc H; eauto.
    invc H1; eauto.
  - intuition (subst; eauto).
Qed.

Lemma tuple_eq_unfold (S1 S2 S3 S1' S2' S3': gset Tid) :
  (S1, S2, S3) = (S1', S2', S3') ↔
  S1 = S1' ∧ S2 = S2' ∧ S3 = S3'.
Proof. naive_solver. Qed.

Hint Rewrite tuple_eq_unfold measure_lt_unfold : pc.

Lemma eventually_unlocked ss :
  spec ⊢ ⌜λ s, measure s = ss⌝ ~~>
         ⌜λ s, measure s ≺ ss ∨
               measure s = ss ∧
               let '(_, Sᵤ', _) := measure s in
               Sᵤ' = ∅ ∧ s.(state).(lock) = false⌝.
Proof.
  apply (leads_to_assume _ all_invs_ok). lt_simp.
  apply leads_to_if_lock.
  - lt_unfold.
    intuition subst.
    simpl.
    right; intuition auto.
    apply unlock_set_unlocked_inv' in H1; auto.
  - leads_to_trans (∃ t, ⌜λ s, measure s = ss ∧
                   pc_set pc.unlock_store s.(tp) = {[t]} ∧
                   s.(tp) !! t = Some pc.unlock_store⌝)%L.
    { lt_unfold. intuition subst.
      apply unlock_set_lock_inv in H1 as [t ?]; eauto. }
    lt_intros.
    rewrite /measure.
    apply (mutex_wf1 t); simpl; intros.
    + destruct ss as [[Sₗ Sᵤ] S__w].
      destruct_step; stm.
    + destruct ss as [[Sₗ Sᵤ] S__w].
      stm.
    + naive_solver.
Qed.

Lemma eventually_unlocked2 ss :
  spec ⊢ ⌜λ s, measure s = ss ⌝ ~~>
         ⌜λ s, measure s ≺ ss ∨
               measure s = ss ∧
               let '(_, Sᵤ', S__w') := measure s in
               Sᵤ' = ∅ ∧ S__w' = ∅ ∧ s.(state).(lock) = false⌝.
Proof.
  leads_to_etrans.
  { apply eventually_unlocked. }
  lt_split; [ by lt_auto | ].
  simpl.
  destruct ss as [[Sₗ Sᵤ] S__w].
  destruct (decide (S__w = ∅)); subst.
  { lt_unfold.
    rewrite /measure; stm.
    rewrite H H4; auto. }
  apply set_choose_L in n as [t Hwake].
  rewrite /measure.
  lt_simp.
  apply (mutex_wf1 t); simpl; intros.
  - destruct_step; stm.
  - intuition subst.
    assert (tp !! t = Some pc.unlock_wake).
    { stm. apply elem_pc_set in Hwake; auto. }
    stm.
  - stm.
    assert (tp !! t = Some pc.unlock_wake).
    { stm. apply elem_pc_set in Hwake; auto. }
    naive_solver.
Qed.

Lemma eventually_progress_atomic_cas Sₗ t :
  t ∈ Sₗ →
  spec ⊢ ⌜λ s, measure s = (Sₗ, ∅, ∅) ∧
               s.(tp) !! t = Some pc.lock_cas ⌝ ~~>
         ⌜λ s, measure s ≺ (Sₗ, ∅, ∅)⌝.
Proof.
  intros Hel.
  rewrite /measure.
  apply (mutex_wf1 t); simpl; intros.
  - destruct_step; stm.
    rewrite H4 H3. simp_props.
    apply elem_pc_set in Hlookup.
    set_solver.
  - stm.
    destruct l0; stm.
    exfalso.
    apply unlock_set_lock_inv in Hinv as [t' ?]; intuition.
    simpl in *.
    set_solver.
  - naive_solver.
Qed.

Lemma eventually_progress_futex_wait Sₗ t :
  t ∈ Sₗ →
  spec ⊢ ⌜λ s, measure s = (Sₗ, ∅, ∅) ∧
               s.(tp) !! t = Some pc.futex_wait ⌝ ~~>
         ⌜λ s, measure s ≺ (Sₗ, ∅, ∅)⌝.
Proof.
  intros Hel.
  eapply leads_to_detour; [ | apply eventually_progress_atomic_cas; eauto ].
  lt_simp.
  rewrite /measure.
  apply (mutex_wf1 t); simpl; intros.
  - destruct_step; stm.
    rewrite H4 H3. simp_props.
    apply elem_pc_set in Hlookup.
    set_solver.
  - stm.
    destruct l0; stm.
    exfalso.
    apply unlock_set_lock_inv in Hinv as [t' ?]; intuition.
    simpl in *.
    set_solver.
  - naive_solver.
Qed.

End example.
