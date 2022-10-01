(*|

=============================================
Example: a controller-like state machine
=============================================

This example is intended to model something like a controller running in Kubernetes. It models a controller that on startup sends a message to create "object 1" then "object 2" (these are simply modeled as booleans as to whether or not they exist). These messages are processed by the network/rest of the cluster (a different set of transitions), which actually transitions to a state where the objects exist. The goal is to create object 1, wait for it to exist, and then create object 2.

The specification for this controller has two parts. First is a safety property: if object 2 exists, object 1 should exist (enforcing the ordering). Second is a liveness property that under some fairness assumptions both objects eventually exist.

|*)

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import sets.
From TLA Require Import logic.

Section example.

(*|

------
State
------

The state will combine local state on the controller, the cluster state, and the
network.

|*)

(* For now, the controller sends a create message out and that's it. No replies,
we just directly check if the objects exist. *)
Inductive message :=
| CreateReq (id: nat)
.

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

(* a little boilerplate for coq-record-update *)
Instance _eta_state : Settable _ :=
  settable! mkState<sent1Create; sent2Create;
                    obj1Exists; obj2Exists; messages>.

Local Notation action := (action state).
Local Notation exec := (exec state).

Implicit Types (s: state) (e: exec) (a: action).

(*|

----------------------------
State machine transitions
----------------------------

The two transitions `send1_a` and `send2_a` correspond to lines of code in the (hypothetical) `reconcile` function. This imagined function first checks if it should send a message to create object 1 (the enabling condition of `send1_a`), then if `obj1Exists` is true, it can run the `send2_a` action which when enabled sends a message to create object 2.

The syntax `s <|sent1Create := true|>` comes from coq-record-update: it changes
the field `sent1Create1` to `true` and leaves other fields unchanged.
`<|messages ::= cons (CreateReq 1)|>` is similar but applies a function based on
the current value of the `messages` field (so this prepends a new message to the
field that models the network).

|*)

Definition send1_a : action :=
  λ s s',
  (¬s.(obj1Exists) ∧ ¬s.(sent1Create)) ∧
  s' = s <|sent1Create := true|> <|messages ::= cons (CreateReq 1)|>.

Definition send2_a : action :=
  λ s s',
  (* reconcile would also check that send1_a is disabled but we can ignore that
  because of the check on obj1Exists *)
  (s.(obj1Exists) ∧
  (* now make sure we should be trying*)
  ¬s.(obj2Exists) ∧ ¬s.(sent2Create)) ∧
  s' = s <|sent2Create := true|> <|messages ::= cons (CreateReq 2)|>.

Definition reconcile: action :=
    λ s s', send1_a s s' ∨ send2_a s s'.

(*|

The cluster transitions are not intended to model the controller but the rest of the Kubernetes cluster. We assume that some other part of the system can pick up on the creation messages and respond by creating the corresponding object. Again for simplicity there are no reply messages, we just give the reconcile code the ability to directly detect if the objects have been created.

|*)

Definition create1 : action :=
  λ s s', CreateReq 1 ∈ s.(messages) ∧
          s' = s <|obj1Exists := true|>.

Definition create2 : action :=
  λ s s', CreateReq 2 ∈ s.(messages) ∧
          s' = s <|obj2Exists := true|>.

Definition cluster: action := λ s s', create1 s s' ∨ create2 s s'.

(*|
`next` ties everything together into a single transition action, including a
"stutter step" (this is needed for the specification to make sense for infinite
executions).
|*)

Definition next : action :=
  λ s s', s = s' ∨ reconcile s s' ∨ cluster s s'.

(*|
Finally we need `init` to define the initial state. We just say nothing is
created and no messages have been sent.
|*)
Definition init s :=
  s = {| sent1Create := false; sent2Create := false;
         obj1Exists := false; obj2Exists := false;
         messages := [] |}.

(*|
As in the "hello" example, a little state machine-specific automation will be
enough for the goals that come up in these proofs.
|*)

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

Theorem obj1_invariant :
  ⌜init⌝ ∧ □ ⟨next⟩ ⊢
  □ ⌜λ s, (s.(sent2Create) → s.(obj1Exists)) ∧
          (s.(obj1Exists) → s.(sent1Create))⌝.
Proof.
(*|
The proof starts out with `tla_pose messages_sent`. This will place the
conclusion of `messages_sent` in this theorem's premises, after proving that the
current premises imply the premises of `message_sent`. The result is a use of
modus ponens where we derive the invariant in `messages_sent` without losing `□
⟨next⟩` for example.
|*)
  tla_pose messages_sent.
  rewrite !combine_preds. (* .unfold *)
(*|
The state here looks like a regular invariant proof from an initial
predicate, except that the transition system semantics is assumed to satisfy
the invariant. Of course this reasoning is sound because it *already implied*
this invariant, so logically nothing changes, but practically speaking we can
build on previously proven invariants and thus can break down the proof of
complex inductive invariants.
|*)
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

Hint Unfold safe : stm.

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
`weak_fairness reconcile`. These assumptions ensure we only consider executions
where actions get to run, as long as they're enabled. Next, we exploit
`weak_fairness` to prove a number of `~~>` ("leads to") theorems that go through
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

(* this says the message was sent on the network (which is related to the local
fields s.(sent1Create) and s.(sent2Create) via an invariant) *)
Definition create_sent (id:nat) : state → Prop :=
  λ s, CreateReq id ∈ s.(messages).

Hint Unfold create_sent : stm.

Lemma eventually_send1 :
  □ ⟨next⟩ ∧ weak_fairness reconcile ⊢
  ⌜ λ s, ¬ s.(sent1Create) ∧ ¬ s.(obj1Exists) ⌝ ~~>
  ⌜ create_sent 1 ⌝.
Proof.
  apply wf1.
  - stm.
  - stm.
  - intros s. rewrite reconcile_enabled.
    intuition auto.
Qed.

Lemma eventually_create1 :
  □ ⟨next⟩ ∧ weak_fairness create1 ⊢
  ⌜ create_sent 1 ⌝ ~~>
  ⌜ obj1Exists ⌝.
Proof.
  apply wf1; stm.
Qed.

Lemma init_send_create1 :
  □ ⟨next⟩ ∧ weak_fairness create1 ∧ weak_fairness reconcile ⊢
  ⌜init⌝ ~~>
  ⌜ obj1Exists ⌝.
Proof.
  leads_to_trans ⌜create_sent 1⌝.
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
  ⌜ create_sent 2 ⌝.
Proof.
  apply wf1.
  - stm.
  - stm.
  - intros s. rewrite reconcile_enabled.
    intuition auto.
Qed.

Lemma eventually_create2 :
  □ ⟨next⟩ ∧ weak_fairness create2 ⊢
  ⌜ create_sent 2 ⌝ ~~>
  ⌜ obj2Exists ⌝.
Proof.
  apply wf1; stm.
Qed.

(*|
This next proof is actually not that simple. You might think we want to chain
`eventually_send1` and `eventually_send2` (like we did above for object 1), but
we can only apply `eventually_send1` under some additional preconditions. The
issue is that `reconcile` only tries to create object 2 if it doesn't exist;
there's a similar issue in principle for object 1, but the required conditions
are immediately met at initialization.

The proof handles this issue by using a different strategy when the
preconditions for `eventually_send2` fail; basically in one case we're already
done because `s.(obj2Exists)` is true, and in the other we've already sent a
request for object 2 and it will eventually be created.
|*)

Lemma eventually_send_create2 :
  ⌜init⌝ ∧ □ ⟨next⟩ ∧ weak_fairness reconcile ∧ weak_fairness create2 ⊢
  ⌜ obj1Exists ⌝ ~~>
  ⌜ obj2Exists ⌝.
Proof.
(*|
This proof is actually interesting.
|*)

  rewrite leads_to_assume_not.
  rewrite not_state_pred combine_state_preds.

(*|
Now we've switched to the case where the conclusion isn't already true. The next
step is more "inspired": we do the TLA equivalent of a case split on whether or
not `s.(sent2Create)` is true, *within the `~~>` premise*.
|*)

  rewrite (tla_and_em (⌜sent2Create⌝)
             (⌜λ s, s.(obj1Exists) ∧ ¬ s.(obj2Exists)⌝)).
  rewrite tla_and_distr_l.
  rewrite leads_to_or_split.
  rewrite !not_state_pred !combine_state_preds.
(*|
After a little cleanup, we have two goals.
|*)
  tla_split. (* .unfold *)
  -

(*|
In this first goal, you can see that we already have `s.(sent2Create)`. This is
almost enough to guarantee it'll be created, but it's an invariant that this
implies that we actually sent a message on the network! The key idea encoded in
the `leads_to_assume` rule is that if we can prove that the current premises
imply `□ msg_inv` (which is `messages_sent`, a safety proof above), then we can
safely assume them in the premise of the `~~>`.
|*)

    apply (leads_to_assume ⌜msg_inv⌝).
    { tla_apply messages_sent. }
    (* .unfold *)

(*|
`eventually_create2` will prove this goal with just a little low-level
manipulation.
|*)
    leads_to_etrans; [ | tla_apply eventually_create2 ].
    apply impl_drop_hyp.
    rewrite combine_state_preds.
    apply pred_leads_to; stm.

  -

(*|
In the second case of the split, we don't have `s.(sent2Create)`, so we'll use
`eventually_send2` chained with `eventually_create2`.
|*)

  leads_to_trans ⌜create_sent 2⌝.
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
  leads_to_trans ⌜obj1Exists⌝.
  - tla_apply init_send_create1.
  - tla_apply eventually_send_create2.
Qed.

(*|
This is the final liveness theorem. We need `reconcile` to be weakly fair
(that is, the controller gets a chance to run if it's enabled), and network
actions to *each* be treated fairly.
|*)
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

(*|
At this point the reasoning is pretty mundane, we're just trying to combine
`◇obj2Exists` with `□safe` but there's a bunch of re-arranging to do (including
modalities, so it isn't easily automated, either).
|*)
  tla_clear ⌜init⌝. tla_clear (□⟨next⟩)%L.
  rewrite tla_and_comm.
  rewrite -> always_and_eventually.
  rewrite combine_state_preds.
  apply eventually_impl_proper.
  apply state_pred_impl.
  stm.
Qed.

End example.
