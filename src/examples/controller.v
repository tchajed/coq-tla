(*|

=============================================
Example: a controller-like state machine
=============================================

This example is intended to model something like a distributed system like
Kubernetes. It models a controller that on startup sends a message to create
"object 1" then "object 2". These messages are processed by the network (a
different set of transitions), which actually transitions to a state where the
objects exist. The goal is to create object 1, wait for it to exist, and then
create object 2.

The specification for this controller has two parts. First is a safety property:
if object 2 exists, object 1 should exist (enforcing the ordering). Second is a
liveness property that under some fairness assumptions both objects eventually
exist.

|*)

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import sets.
From TLA Require Import logic.

Section example.

(* For now, we send a create message and that's it. No replies, we just directly
check if the objects exist. *)
Inductive message :=
| CreateReq (id: nat)
.

#[global]
Instance message_eqdec : EqDecision message.
Proof. solve_decision. Defined.

Record state := mkState {
  (* local controller state *)
  sent1Create: bool;
  sent2Create: bool;

  (* remote cluster state (not directly readable) *)
  obj1Exists: bool;
  obj2Exists: bool;

  (* messages *)
  messages: list message;
}.

Instance _eta_state : Settable _ :=
  settable! mkState<sent1Create; sent2Create;
                   obj1Exists; obj2Exists; messages>.

Local Notation action := (action state).
Local Notation exec := (exec state).

Implicit Types (s: state) (e: exec) (a: action).

Definition send1_a : action :=
  λ s s',
  (¬s.(obj1Exists) ∧ ¬s.(sent1Create)) ∧
  s' = s <| sent1Create := true |> <| messages ::= cons (CreateReq 1) |>.

Definition send2_a : action :=
  λ s s',
  (* reconcile would also check that send1_a is disabled but we can ignore that
  because of the check on obj1Exists *)
  (s.(obj1Exists) ∧
  (* now make sure we should be trying*)
  ¬s.(obj2Exists) ∧ ¬s.(sent2Create)) ∧
  s' = s <| sent2Create := true |> <| messages ::= cons (CreateReq 2) |>.

Definition reconcile: action :=
    λ s s', send1_a s s' ∨ send2_a s s'.

Definition create1 : action :=
  λ s s', CreateReq 1 ∈ s.(messages) ∧
          s' = s <| obj1Exists := true |>.

Definition create2 : action :=
  λ s s', CreateReq 2 ∈ s.(messages) ∧
          s' = s <| obj2Exists := true |>.

Definition cluster: action := λ s s', create1 s s' ∨ create2 s s'.

Definition next : action :=
  λ s s', s = s' ∨ reconcile s s' ∨ cluster s s'.

Definition init s :=
  s = {| sent1Create := false; sent2Create := false;
         obj1Exists := false; obj2Exists := false;
         messages := [] |}.

Hint Unfold init next : stm.
Hint Unfold reconcile cluster send1_a send2_a create1 create2 : stm.

Ltac stm_simp :=
  autounfold with stm;
  intros; (intuition idtac);
  rewrite ?enabled_eq;
  repeat deex;
  repeat match goal with
        | s: state |- _ => destruct s
        | H: @eq state _ _ |- _ => inversion H; subst; clear H
        end;
  simpl in *;
  intuition idtac.

Ltac stm :=
  stm_simp;
  try solve [ intuition auto ];
  try set_solver.

(*|
------------
Safety
------------

We do some safety reasoning. The safety property proven is that of object 2
exists, then object 1 also exists. This property is not inductive; the exact
inductive invariant wasn't immediately obvious, so I just started randomly
proving reasonable-looking invariants until the proof went through.
|*)

Definition msg_inv s :=
  (CreateReq 1 ∈ s.(messages) ↔ s.(sent1Create)) ∧
  (CreateReq 2 ∈ s.(messages) ↔ s.(sent2Create)).

Hint Unfold msg_inv : stm.

Theorem messages_sent :
  ⌜init⌝ ∧ □ ⟨next⟩ ⊢ □ ⌜msg_inv⌝.
Proof.
  apply init_invariant.
  - stm.
  - stm.
Qed.

(*|
The proof starts out with `tla_pose messages_sent`. This will place the
conclusion of `messages_sent` in this theorem's premises, after proving that the
current premises imply the premises of `message_sent`. The result is a use of
modus ponens where we derive the invariant in `messages_sent` without losing `□
⟨next⟩` for example.
|*)

Theorem obj1_invariant :
  ⌜init⌝ ∧ □ ⟨next⟩ ⊢
  □ ⌜λ s, (s.(sent2Create) → s.(obj1Exists)) ∧
          (s.(obj1Exists) → s.(sent1Create))⌝.
Proof.
  tla_pose messages_sent.
  rewrite !combine_preds.
  (* The state here looks like a regular invariant proof from an initial
  predicate, except that the transition system semantics is assumed to satisfy
  the invariant. Of course this reasoning is sound because it _already implied_
  this invariant, so logically nothing changes, but practically speaking we can
  build on previously proven invariants and thus can break down the proof of
  complex inductive invariants. *)
  apply init_invariant.
  - stm.
  - stm.
Qed.

(*|
`messages_sent` and `obj1_invariant` are just enough help to prove this larger
invariant, which nicely characterizes when obj2Exists is possible. Note that two
of these conjuncts follow easily from obj1_invariant, but we assume that first.
|*)

Theorem create_invariant :
  ⌜init⌝ ∧ □ ⟨next⟩ ⊢
  □ ⌜λ s, s.(obj2Exists) →
    s.(sent2Create) ∧ s.(sent1Create) ∧ s.(obj1Exists)⌝.
Proof.
  tla_pose messages_sent.
  tla_pose obj1_invariant.
  rewrite !combine_preds.
  apply init_invariant.
  - stm.
  - stm.
Qed.

(*|
What we've proven above implies safety.
|*)

Definition safe (s: state) := s.(obj2Exists) → s.(obj1Exists).

Theorem is_safe :
  ⌜init⌝ ∧ □ ⟨next⟩ ⊢ □ ⌜safe⌝.
Proof.
  rewrite -> create_invariant.
  apply always_impl_proper.
  unseal.
  stm.
Qed.

(*|
------------
Liveness
------------

Now we get to the interesting part: a liveness proof showing that both objects
are eventually created. First, this requires making fairness assumptions like
[weak_fairness reconcile]. These assumptions ensure we only consider executions
where actions get to run, as long as they're enabled. Next, we exploit
[weak_fairness] to prove a number of [~~>] ("leads to") theorems that go through
the steps of the protocol. Finally, we tie everything together to show liveness.
|*)

Lemma reconcile_enabled s :
  enabled reconcile s ↔
    ((¬ s.(obj1Exists) ∧ ¬ s.(sent1Create)) ∨
    (s.(obj1Exists) ∧ ¬ s.(obj2Exists) ∧ ¬ s.(sent2Create))).
Proof.
  rewrite /reconcile.
  rewrite enabled_or.
  autounfold with stm; rewrite !enabled_eq.
  intuition idtac.
Qed.

Lemma eventually_send1 :
  □ ⟨next⟩ ∧ weak_fairness reconcile ⊢
  ⌜ λ s, ¬ s.(sent1Create) ∧ ¬ s.(obj1Exists) ⌝ ~~>
  ⌜ λ s, CreateReq 1 ∈ s.(messages) ⌝.
Proof.
  apply wf1.
  - stm.
  - stm.
  - intros s. rewrite reconcile_enabled.
    intuition auto.
Qed.

Lemma eventually_create1 :
  □ ⟨next⟩ ∧ weak_fairness create1 ⊢
  ⌜ λ s, CreateReq 1 ∈ s.(messages) ⌝ ~~>
  ⌜ λ s, s.(obj1Exists) ⌝.
Proof.
  apply wf1; stm.
Qed.

Lemma init_send_create1 :
  □ ⟨next⟩ ∧ weak_fairness create1 ∧ weak_fairness reconcile ⊢
  ⌜init⌝ ~~>
  ⌜ λ s, s.(obj1Exists) ⌝.
Proof.
  leads_to_trans ⌜λ s, CreateReq 1 ∈ s.(messages)⌝.
  - leads_to_trans ⌜λ s, ¬ s.(sent1Create) ∧ ¬ s.(obj1Exists)⌝.
    { apply impl_drop_hyp.
      apply pred_leads_to.
      stm. }
    tla_pose eventually_send1.
    tla_prop.
  - tla_pose eventually_create1.
    tla_prop.
Qed.

Lemma eventually_send2 :
  □ ⟨ next ⟩ ∧ weak_fairness reconcile ⊢
  ⌜ λ s, s.(obj1Exists) ∧ ¬ s.(obj2Exists) ∧ ¬ s.(sent2Create) ⌝ ~~>
  ⌜ λ s, CreateReq 2 ∈ s.(messages) ⌝.
Proof.
  apply wf1.
  - stm.
  - stm.
  - intros s. rewrite reconcile_enabled.
    intuition auto.
Qed.

Lemma eventually_create2 :
  □ ⟨next⟩ ∧ weak_fairness create2 ⊢
  ⌜ λ s, CreateReq 2 ∈ s.(messages) ⌝ ~~>
  ⌜ λ s, s.(obj2Exists) ⌝.
Proof.
  apply wf1; stm.
Qed.

(*|
This next proof is actually not that simple. You might think we want to chain
[eventually_send1] and [eventually_send2] (like we did above for object 1), but
we can only apply [eventually_send1] under some additional preconditions. The
issue is that [reconcile] only tries to create object 2 if it doesn't exist;
there's a similar issue in principle for object 1, but the required conditions
are immediately met at initialization.

The proof handles this issue by using a different strategy when the
preconditions for [eventually_send2] fail; basically in one case we're already
done because [s.(obj2Exists)] is true, and in the other we've already sent a
request for object 2 and it will eventually be created.
|*)

Lemma eventually_send_create2 :
  ⌜init⌝ ∧ □ ⟨next⟩ ∧ weak_fairness reconcile ∧ weak_fairness create2 ⊢
  ⌜ λ s, s.(obj1Exists) ⌝ ~~>
  ⌜ λ s, s.(obj2Exists) ⌝.
Proof.
  (* This proof is actually interesting.  *)
  rewrite leads_to_assume_not.
  rewrite not_state_pred combine_state_preds.
  rewrite (tla_and_em (⌜λ s, s.(sent2Create)⌝)
             (⌜λ s, s.(obj1Exists) ∧ ¬ s.(obj2Exists)⌝)).
  rewrite tla_and_distr_l.
  rewrite leads_to_or_split.
  rewrite !not_state_pred !combine_state_preds.
  tla_split.
  {

  (*
  This next step is a key idea: we prove that the current premises imply
  [□ msg_inv] (a previously proven safety proof), and then we can safely assume
  them in the premise of the [~~>].
  *)

    apply (leads_to_assume ⌜msg_inv⌝).
    { tla_apply messages_sent. }
    leads_to_etrans; [ | tla_apply eventually_create2 ].
    apply impl_drop_hyp.
    rewrite combine_state_preds.
    apply pred_leads_to; stm. }

  leads_to_trans ⌜λ s, CreateReq 2 ∈ s.(messages)⌝.
  {
    leads_to_etrans; [ | tla_apply eventually_send2 ].
    apply impl_drop_hyp.
    apply pred_leads_to; stm. }
  tla_apply eventually_create2.
Qed.

Lemma init_create2 :
  ⌜init⌝ ∧ □ ⟨next⟩ ∧
    weak_fairness reconcile ∧
    weak_fairness create1 ∧ weak_fairness create2 ⊢
  ◇ ⌜ λ s, s.(obj2Exists) ⌝.
Proof.
  apply (leads_to_apply ⌜init⌝); [ tla_prop | ].
  leads_to_trans ⌜λ s, s.(obj1Exists)⌝.
  - tla_apply init_send_create1.
  - tla_apply eventually_send_create2.
Qed.

(** This is the final liveness theorem. We need [reconcile] to be weakly fair
(that is, the controller gets a chance to run if it's enabled), and network
actions to be _each_ be treated fairly. *)
Theorem eventually_create_both :
  ⌜init⌝ ∧ □ ⟨next⟩ ∧
    weak_fairness reconcile ∧
     weak_fairness create1 ∧ weak_fairness create2 ⊢
   ◇ ⌜λ s, s.(obj1Exists) ∧ s.(obj2Exists)⌝.
Proof.
  eapply entails_cut.
  { apply init_create2. }

  tla_clear (weak_fairness reconcile ∧
                 weak_fairness create1 ∧ weak_fairness create2)%L.

  tla_pose is_safe.

  (* At this point the reasoning is pretty mundane, we're just trying to combine
     ◇obj2Exists with □safe but there's a bunch of re-arranging to do (including
     modalities, so it isn't easily automated, either).
   *)
  tla_clear ⌜init⌝. tla_clear (□⟨next⟩)%L.
  rewrite tla_and_comm.
  rewrite -> always_and_eventually.
  rewrite combine_state_preds.
  apply eventually_impl_proper.
  apply state_pred_impl.
  stm.
Qed.

End example.
