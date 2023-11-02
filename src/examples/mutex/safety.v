From TLA Require Import logic.
From TLA.examples.mutex Require Import
  spec wait_set nodup automation.

Implicit Types (σ: State) (s: Config) (t: Tid).
Implicit Types (l: bool) (q: list Tid).

Definition exclusion_inv: Config → Prop :=
  λ s, (∀ tid, s.(tp) !! tid = Some pc.critical_sec →
               s.(state).(lock) = true) ∧
       safe s.

Lemma exclusion_inv' s :
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
    apply next_inv in Hnext as
        [[[=] ?] |
          (t & pc & pc' & Hlookup & Hstep & ?)]; subst; eauto.

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
    apply next_inv in Hnext as
        [[[=] ?] |
          (t & pc & pc' & Hlookup & Hstep & ?)]; subst; eauto.
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
Hint Extern 2 (_ ∉ _) => set_solver : stm.
#[local]
Hint Extern 2 (_ ∈ _) => set_solver : stm.

Ltac learn H :=
  let P := type of H in
  lazymatch goal with
  | H': P |- _ => fail
  | _ => let name := fresh "_Hlearned" in
         pose proof H as name
  end.

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
    apply next_inv in Hnext as
        [[[=] ?] |
          (t & pc & pc' & Hlookup & Hstep & ?)]; subst; eauto.
    destruct_step; stm; intros;
      repeat match goal with
        | t: Tid |- _ =>
            match goal with
            | Hin: t ∈ _ |- _ => learn (Hwait t Hin)
            end
        end;
      lookup_simp.
    + destruct (decide (t = t0)); lookup_simp.
      apply elem_of_app in H. set_solver.
    + apply elem_of_pop in H; lookup_simp.
      apply Hwait in H.
      destruct (decide (t = t0)); lookup_simp.
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

(*|
We'll now prove an invariant `lock_free_queue_inv` to cover the situation where the queue has some head thread `t` (which must be in `kernel_wait`, a simple inductive invariant) but the lock is free. It'll show the existence of some other thread `t'` that will help make progress. We don't need to worry about the case where the lock is held, because then the lock holder will release the lock and signal, so progress is relatively easy in that case.

If the queue has a head element `t` but the lock is free, then some thread `t'` must have acquired the lock, then released it (because the code only starts waiting if the lock is still held, according to the semantics of `futex_wait()`). To make this an inductive invariant, we need to also consider that `t'` next signalled to some thread `t''`, in which case `t''` is in `kernel_wait` and enabled. Finally, `t''` in turn may have already run and is now back in `lock_cas`, so this third case is also needed to make the invariant inductive. These three cover all the cases because the lock is free, so `t''` couldn't have acquired the lock yet.
|*)

(* NOTE: this is incorrectly named, it's just a thread that can help make
progress in general *)
Definition thread_can_signal t' s :=
  s.(tp) !! t' = Some pc.unlock_wake ∨
  (s.(tp) !! t' = Some pc.kernel_wait ∧
  t' ∉ s.(state).(queue)) ∨
  s.(tp) !! t' = Some pc.lock_cas.

Definition lock_free_queue_inv s :=
  ∀ t ts,
    s.(state).(queue) = t::ts →
    s.(state).(lock) = false →
    ∃ t', thread_can_signal t' s.

Lemma lock_free_queue_inv_ok :
  spec ⊢ □⌜lock_free_queue_inv⌝.
Proof.
  tla_pose nodup_helper_inv_ok.
  tla_pose exclusion_inv_ok.
  rewrite /lock_free_queue_inv /thread_can_signal.
  unfold spec. tla_clear fair.
  rewrite -always_and combine_state_preds.
  rewrite combine_preds.
  apply init_invariant.
  - intros s. stm.
  - move => [[l q] tp] [[l' q'] tp'] /=.
    intros Hinv [Hnext [Hinvs _]] t0 ts0 -> ->; simpl in *.
    destruct Hinvs as ([Hnodup Hwait] & [Hexcl _]); simpl in *.
    rewrite /nodup_inv /= in Hnodup.
    apply next_inv in Hnext as
        [[[=] ?] |
          (t & pc & pc' & Hlookup & Hstep & ?)]; subst; eauto.

(*|
This proof is done carefully to illustrate all the cases above.
|*)
    destruct_step; stm_simp.
    + (* futex_wait -> lock_cas *)
      destruct (Hinv _ _ ltac:(eauto) ltac:(auto)) as [t' Ht'];
        destruct_or!; destruct_and?;
          try solve [ exists t'; lookup_simp; eauto ].
      (* doesn't affect t', all cases are proven automatically *)
    + (* kernel_wait -> lock_cas *)
      destruct (Hinv _ _ ltac:(eauto) ltac:(auto)) as [t' Ht'];
        destruct_or!; destruct_and?;
          try solve [ exists t'; lookup_simp; eauto ].
      (* t' was in kernel_wait but now it's in lock_cas *)
      assert (tp !! t' = Some pc.kernel_wait) as _ by assumption.
      exists t; lookup_simp; eauto.
    + (* unlock_store -> unlock_wake *)
      assert (l = true) by eauto; subst.
      (* this is the easy case where we got here because a thread just released
      the lock *)
      exists t; lookup_simp; eauto.
    + (* unlock_wake -> finished *)
(*|
There may no longer be thread still in `unlock_wake`, so we'll instead show
there's now a `kernel_wait` thread that's enabled.
|*)
      (* this invariant only concerns the queue being non-empty, so signalling
      must have signalled some other thread [t1] just in front of t0 *)
      destruct q as [|t'' q']; [ by inversion H2 | simpl in H2; subst ].
      assert (t'' ∉ t0 :: ts0) by (inversion Hnodup; eauto).
      rewrite /waiting_inv /= in Hwait.
      (* follows from [t''] being in the queue *)
      assert (tp !! t'' = Some pc.kernel_wait) by set_solver.
      exists t''; lookup_simp; eauto.
Qed.

Record all_invs s :=
  { Hexcl: exclusion_inv s;
    Hlocked: locked_inv s;
    Hnodup: nodup_inv s;
    Hwaiting: waiting_inv s;
    Hcan_lock: lock_free_queue_inv s;
  }.

Lemma all_invs_ok :
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
