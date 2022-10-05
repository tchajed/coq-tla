(*|

=============================
Example: (spinlock) Mutex
=============================

This example is a liveness proof for the following simple C program. It encodes the program as a hand-written state machine, with states referring to labeled points.

::

  type Mutex = bool;
  const UNLOCKED = false;
  const LOCKED = true;

  void lock(Mutex *m) {
    // pc0
    for cas(m, UNLOCKED, LOCKED) {}
    // control goes directly to pc1 (see `thread`)
  }

  void unlock(Mutex *m) {
    // pc1
    *m = UNLOCKED;
    // pc2
  }

  void thread(Mutex *m) {
    lock(m);
    unlock(m);
  }

  void main() {
    Mutex *m = malloc(sizeof(Mutex));
    // these two threads are what is modeled
    spawn(thread, m);
    spawn(thread, m);
  }

What we reason about is two threads running `lock(m); unlock(m)` (assuming m starts out allocated).

|*)

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import functions.

From TLA Require Import logic.


Module spec.

  Inductive pc := pc0 | pc1 | pc2.
  Inductive Tid := tidA | tidB.

  #[global]
  Instance tid_eqdecision : EqDecision Tid.
  Proof.
    solve_decision.
  Defined.

  (* the state consists of the state of the mutex, and program counters for two
  threads, tidA and tidB *)
  Record state :=
    mkState { lock: bool; pcs: Tid → pc; }.

  #[global]
  Instance _eta : Settable _ := settable! mkState <lock; pcs>.

  Definition cas_fail (t0: Tid): action state :=
    λ s s', (s.(pcs) t0 = pc0 ∧ s.(lock) = true)
            ∧ s' = s.

  Definition cas_succ (t0: Tid): action state :=
    λ s s', s.(pcs) t0 = pc0 ∧ s.(lock) = false
            ∧ s' = s <|lock := true|>
                     <|pcs ::= <[ t0 := pc1 ]> |>.

  Definition unlock (t0: Tid): action state :=
    λ s s', s.(pcs) t0 = pc1
            ∧ s' = s <|lock := false|>
                     <|pcs ::= <[ t0 := pc2 ]> |>.

  Definition step (t0: Tid): action state :=
      λ s s', cas_fail t0 s s' ∨ cas_succ t0 s s' ∨ unlock t0 s s'.

  Definition init: state → Prop :=
    λ s, s = {| lock := false; pcs := λ _, pc0; |}.

  Definition next : action state :=
    λ s s', step tidA s s' ∨ step tidB s s' ∨ s' = s.

  (* safety is mutual exclusion *)
  Definition safe: state → Prop :=
    λ s, ¬ (s.(pcs) tidA = pc1 ∧ s.(pcs) tidB = pc1).

  Definition fair: predicate state :=
    weak_fairness (step tidA) ∧ weak_fairness (step tidB).

  (* liveness means both threads terminate *)
  Definition terminated: state → Prop :=
    λ s, s.(pcs) tidA = pc2 ∧ s.(pcs) tidB = pc2.

End spec.

Import spec.

Section example.

Implicit Types (s: state) (t: Tid).

Hint Unfold init next step safe fair terminated : stm.
Hint Unfold cas_fail cas_succ unlock : stm.

Lemma enabled_thread t :
  enabled (step t) = λ s, s.(pcs) t ≠ pc2.
Proof.
  apply pred_ext => s.
  unfold enabled; split.
  - autounfold with stm. intros [s' Hstep];
      (intuition subst);
      try congruence.
  - intros.
    autounfold with stm.
    destruct s as [l pcs0]; simpl in *.
    destruct (pcs0 t) eqn:?; [ | | congruence ].
    * destruct l; simpl; eexists (mkState _ _); eauto.
    * eexists (mkState _ _); eauto.
Qed.

Ltac stm_simp :=
  autounfold with stm;
  intros; (intuition (repeat deex; subst; trivial));
  rewrite ?enabled_eq ?enabled_thread;
  repeat deex;
  (* TODO: why does this infinite loop? *)
  repeat (match goal with
        | s: state |- _ => (destruct s; cbn in * )
        | H: ?x = ?x |- _ => clear H
        | H: @eq pc _ _ |- _ => solve [ inversion H ]
        | H: @eq state (mkState _ _) (mkState _ _) |- _ =>
            inversion H; subst; clear H; cbn in *
        | H: context[@set state _ _ _ _ _] |- _ =>
            progress (unfold set in H; simpl in H)
        | H: @eq bool _ _ |- _ => solve [ inversion H ]
        | _ => progress (unfold set; simpl)
        | _ => rewrite fn_lookup_insert
        | _ => rewrite -> fn_lookup_insert_ne by congruence
        | _ => progress cbn in *
        end).

Ltac stm :=
  stm_simp;
  try solve [ intuition (repeat deex; eauto) ];
  try congruence.

Definition exclusion_inv: state → Prop :=
  λ s, (s.(pcs) tidA = pc1 → s.(lock) ∧ s.(pcs) tidB ≠ pc1) ∧
       (s.(pcs) tidB = pc1 → s.(lock) ∧ s.(pcs) tidA ≠ pc1).

Hint Unfold exclusion_inv : stm.

Lemma exclusion_inv_ok :
  ⌜init⌝ ∧ □⟨next⟩ ⊢ □⌜exclusion_inv⌝.
Proof.
  apply init_invariant.
  - stm.
  - stm.
Qed.

Theorem safety :
  ⌜init⌝ ∧ □⟨next⟩ ⊢ □ ⌜safe⌝.
Proof.
  rewrite -> exclusion_inv_ok.
  apply always_impl_proper.
  unseal; stm.
Qed.

Theorem wf_threads_combine :
  (weak_fairness (step tidA) ∧ weak_fairness (step tidB)) ==
  weak_fairness (λ s s', step tidA s s' ∨ step tidB s s')%type.
Proof.
  apply wf_combine.
  - rewrite /tla_enabled.
    (* rewrite ?enabled_thread. *)
    (* first, to have any hope here we'd need to make [wf_combine] internal and
    carry out this proof under the assumption of `□⟨next⟩`, but also this
    doesn't seem true at all: it's equivalent to [enabled (step tidA) → ◇
    enabled (step tidB) → ◇ (step tidA)], but this is obvious false in an
    execution which is just the initial state and then infinite stuttering *)
Abort.

Inductive L := start | A1 | Afin | AfinB1 | B1 | Bfin | BfinA1 | goal.

Definition Llt (l1 l2: L) : Prop :=
  match l2, l1 with
  | start, A1 | A1, Afin | Afin, AfinB1 => True
  | start, B1 | B1, Bfin | Bfin, BfinA1 => True
  | AfinB1, goal | BfinA1, goal => True
  | _, _ => False
  end.

Theorem Llt_wf : well_founded Llt.
Proof.
  prove_wf [goal; AfinB1; Afin; A1; BfinA1; Bfin; B1; start].
Qed.

Definition h (label: L) : state → Prop :=
  match label with
  | start => init

  | A1 => λ s, s.(pcs) tidA = pc1 ∧ s.(pcs) tidB = pc0
  | Afin => λ s, s.(pcs) tidA = pc2 ∧ s.(pcs) tidB = pc0 ∧ s.(lock) = false
  | AfinB1 => λ s, s.(pcs) tidA = pc2 ∧ s.(pcs) tidB = pc1

  | B1 => λ s, s.(pcs) tidB = pc1 ∧ s.(pcs) tidA = pc0
  | Bfin => λ s, s.(pcs) tidB = pc2 ∧ s.(pcs) tidA = pc0 ∧ s.(lock) = false
  | BfinA1 => λ s, s.(pcs) tidB = pc2 ∧ s.(pcs) tidA = pc1

  | goal => terminated
  end.

Lemma leads_to_helper (Γ: predicate state) (p q: state → Prop) :
  (∀ s, p s → q s) →
  (Γ ⊢ ⌜p⌝ ~~> ⌜λ s, q s⌝).
Proof.
  intros Hpr.
  apply impl_drop_hyp.
  apply pred_leads_to.
  eauto.
Qed.

Hint Extern 1 (Llt _ _) => exact I : core.

Lemma add_safety :
  ⌜init⌝ ∧ □⟨next⟩ ⊢
  ⌜init⌝ ∧ □⟨λ s s', next s s' ∧ exclusion_inv s ∧ exclusion_inv s'⟩.
Proof.
  tla_pose (exclusion_inv_ok).
  rewrite combine_preds //.
Qed.

Lemma init_to_terminate :
  ⌜init⌝ ∧ □⟨next⟩ ∧ fair ⊢ ⌜init⌝ ~~> ⌜terminated⌝.
Proof.
  unfold fair.
  apply (lattice_leads_to Llt_wf h start goal); [ done | done | ].
  intros l Hne.

  rewrite <- tla_and_assoc. rewrite -> add_safety. tla_simp.

  (* split the proof into one case per label *)
  destruct l; cbn [h]; try congruence.

  - (* start *)
    leads_to_trans ⌜λ s, h A1 s ∨ h B1 s⌝; swap 1 2.
    { apply leads_to_helper => s.
      intros [|]; [ exists A1 | exists B1 ]; eauto. }
    tla_apply (wf1 (step tidA)); stm.
  - (* A1 *)
    leads_to_trans ⌜h Afin⌝; swap 1 2.
    { apply leads_to_helper => s. exists Afin; eauto. }

    tla_apply (wf1 (step tidA)); stm.
  - (* Afin *)
    leads_to_trans ⌜h AfinB1⌝; swap 1 2.
    { apply leads_to_helper => s. exists AfinB1; eauto. }

    tla_apply (wf1 (step tidB)); stm.
  - (* AfinB1 *)
    leads_to_trans ⌜terminated⌝; swap 1 2.
    { apply leads_to_helper => s. exists goal; eauto. }
    tla_apply (wf1 (step tidB)); stm.

  - (* B1 *)
    leads_to_trans ⌜h Bfin⌝; swap 1 2.
    { apply leads_to_helper => s. exists Bfin; eauto. }

    tla_apply (wf1 (step tidB)); stm.
  - (* Bfin *)
    leads_to_trans ⌜h BfinA1⌝; swap 1 2.
    { apply leads_to_helper. exists BfinA1; eauto. }

    tla_apply (wf1 (step tidA)); stm.
  - (* BfinA1 *)
    leads_to_trans ⌜terminated⌝; swap 1 2.
    { apply leads_to_helper => s. exists goal; eauto. }
    tla_apply (wf1 (step tidA)); stm.
Qed.

Lemma eventually_terminate :
  ⌜init⌝ ∧ □⟨next⟩ ∧ fair ⊢ ◇ ⌜terminated⌝.
Proof.
  eapply leads_to_apply; [ | apply init_to_terminate ].
  tla_prop.
Qed.

End example.
