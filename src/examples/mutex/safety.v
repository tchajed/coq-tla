From TLA Require Import logic.
From TLA.examples.mutex Require Import
  spec wait_set nodup automation.

Implicit Types (σ: State) (s: Config) (t: Tid).
Implicit Types (l: bool) (q: list Tid).

Definition exclusion_inv: Config → Prop :=
  λ s, (∀ tid, s.(tp) !! tid = Some pc.critical_sec →
               s.(state).(lock) = true) ∧
       safe s.

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

Definition nodup_inv s :=
  NoDup s.(state).(queue).

Definition waiting_inv s :=
  ∀ t, t ∈ s.(state).(queue) →
        s.(tp) !! t = Some pc.kernel_wait.

(* these need to be proven together *)
Definition nodup_helper_inv s :=
  nodup_inv s ∧ waiting_inv s.

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

(* this hints are just for proving these invariants *)
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
  rewrite /nodup_helper_inv /nodup_inv /waiting_inv.
  apply init_invariant.
  - stm.
    set_solver+.
  - intros [σ tp] [σ' tp'] [Hnodup Hwait] Hnext.
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

Lemma nodup_inv_ok :
  spec ⊢ □⌜nodup_inv⌝.
Proof.
  tla_pose nodup_helper_inv_ok.
  tla_clear spec.
  apply always_impl_proper.
  apply state_pred_impl; rewrite /nodup_helper_inv; naive_solver.
Qed.

Lemma queue_invs :
  spec ⊢ □⌜λ s, exclusion_inv s ∧ nodup_inv s⌝.
Proof.
  tla_pose exclusion_inv_ok.
  tla_pose nodup_inv_ok.
  tla_clear spec.
  rewrite -always_and; tla_simp.
Qed.

Definition thread_can_lock t' s :=
  s.(tp) !! t' = Some pc.unlock_wake ∨
  (s.(tp) !! t' = Some pc.kernel_wait ∧
  t' ∉ s.(state).(queue)) ∨
  s.(tp) !! t' = Some pc.lock_cas.

(* if the queue has a head element [t] but the lock is free, there's some thread
that can acquire the lock and send a signal to [t] *)
Definition lock_free_queue_inv s :=
  ∀ t ts,
    s.(state).(queue) = t::ts →
    s.(state).(lock) = false →
    ∃ t', thread_can_lock t' s.

Lemma lock_free_queue_inv_ok :
  spec ⊢ □⌜lock_free_queue_inv⌝.
Proof.
  tla_pose nodup_helper_inv_ok.
  rewrite /lock_free_queue_inv /thread_can_lock.
  unfold spec. tla_clear fair.
  rewrite combine_preds.
  apply init_invariant.
  - intros s. stm.
  - move => [[q l] tp] [[q' l'] tp'] /=.
    intros Hinv [Hnext [[Hnodup Hwait] _]] t0 ts0 -> ->; simpl in *.
    rewrite /nodup_inv /= in Hnodup.
    destruct Hnext as [ [t Hstep] | Heq]; [ | stm_simp; by eauto ].
    destruct Hstep as [pc'' [Hlookup [ρ' [Hstep Heq]]]]; stm_simp.
    destruct_step;
      repeat (stm_simp
              || solve [
                     specialize (Hinv _ _ ltac:(eauto));
                     stm_simp;
                     match goal with
                     | t: Tid |- _ =>
                         exists t; lookup_simp; eauto
                     end
        ]).
    + destruct l.
      { (* pop [] can't produce a non-nil queue *)
        simpl in *; congruence. }
      simpl in *; subst.
      assert (tp !! t1 = Some pc.kernel_wait).
      { apply Hwait; set_solver. }
      exists t1. right; left.
      lookup_simp.
      split; [ done | ].
      inversion Hnodup; auto.
Qed.

Record all_invs s :=
  { Hexcl: exclusion_inv s;
    Hlocked: locked_inv s;
    Hnodup: nodup_inv s;
    Hwaiting: waiting_inv s;
    Hcan_lock: lock_free_queue_inv s;
  }.

Theorem all_invs_ok :
  spec ⊢ □⌜all_invs⌝.
Proof.
  tla_pose exclusion_inv_ok.
  tla_pose locked_inv_ok.
  tla_pose nodup_helper_inv_ok.
  tla_pose lock_free_queue_inv_ok.
  tla_clear spec.
  rewrite -!always_and.
  tla_simp.
  apply always_impl_proper.
  apply state_pred_impl.
  rewrite /nodup_helper_inv.
  intuition idtac.
  constructor; auto.
Qed.

#[export]
Hint Unfold exclusion_inv locked_inv
  nodup_inv waiting_inv
  lock_free_queue_inv : inv.