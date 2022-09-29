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
  rewrite <- (leads_to_trans _ ⌜λ s, CreateReq 1 ∈ s.(messages)⌝).
  tla_split.
  - rewrite <- (leads_to_trans _ ⌜λ s, ¬ s.(sent1Create) ∧ ¬ s.(obj1Exists)⌝).
    tla_split.
    { apply impl_drop_hyp.
      apply leads_to_impl.
      stm. }
    tla_pose eventually_send1.
    tla_prop.
  - tla_pose eventually_create1.
    tla_prop.
Qed.

(* TODO: the preconditions here are actually a bit tricky; they are carried
through due to invariants, but don't follow in a straightforward [~~>] chain. *)
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

Lemma eventually_send_create2 :
  ⌜init⌝ ∧ □ ⟨next⟩ ∧ weak_fairness reconcile ∧ weak_fairness create2 ⊢
  ⌜ λ s, s.(obj1Exists) ⌝ ~~>
  ⌜ λ s, s.(obj2Exists) ⌝.
Proof.
  rewrite leads_to_assume_not.
  rewrite not_state_pred combine_state_preds.
  rewrite (tla_and_em (⌜λ s, s.(sent2Create)⌝)
             (⌜λ s, s.(obj1Exists) ∧ ¬ s.(obj2Exists)⌝)).
  rewrite tla_and_distr_l.
  rewrite leads_to_or_split.
  rewrite !not_state_pred !combine_state_preds.
  tla_split.
  {
    apply (leads_to_assume ⌜msg_inv⌝).
    { tla_apply messages_sent. }
    leads_to_etrans; [ | tla_apply eventually_create2 ].
    apply impl_drop_hyp.
    rewrite combine_state_preds.
    apply leads_to_impl; stm. }

  leads_to_trans ⌜λ s, CreateReq 2 ∈ s.(messages)⌝.
  {
    leads_to_etrans; [ | tla_apply eventually_send2 ].
    apply impl_drop_hyp.
    apply leads_to_impl; intuition idtac. }
  tla_apply eventually_create2.
Qed.

Lemma init_create2 :
  ⌜init⌝ ∧ □ ⟨next⟩ ∧
    weak_fairness reconcile ∧
    weak_fairness create1 ∧ weak_fairness create2 ⊢
  ◇ ⌜ λ s, s.(obj2Exists) ⌝.
Proof.
  apply (eventually_from_leads_to ⌜init⌝); [ tla_prop | ].
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
  tla_clear ⌜init⌝. tla_clear (□⟨next⟩)%L.

  rewrite tla_and_comm.
  rewrite -> always_and_eventually.
  rewrite combine_state_preds.
  apply eventually_impl_proper.
  apply state_pred_impl.
  stm.
Qed.

End example.
