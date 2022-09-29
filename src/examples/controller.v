From RecordUpdate Require Import RecordUpdate.

From stdpp Require Import sets gmap.

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

#[global]
Instance message_countable : Countable message.
Proof.
  refine (inj_countable' (λ m, match m with
  | CreateReq id => id
  end)
  (λ id, CreateReq id) _); intros []; done.
Qed.

Record state := mkState {
  (* local controller state *)
  sent1Create: bool;
  sent2Create: bool;

  (* remote cluster state (not directly readable) *)
  obj1Exists: bool;
  obj2Exists: bool;

  (* messages *)
  messages: gset message;
}.

Instance _eta_state : Settable _ :=
  settable! mkState<sent1Create; sent2Create;
                   obj1Exists; obj2Exists; messages>.

Local Notation action := (action state).
Local Notation exec := (exec state).

Implicit Types (s: state) (e: exec) (a: action).

Definition send1_a : action :=
  λ s s', negb s.(obj1Exists) ∧ negb s.(sent1Create) ∧
          s' = s <| sent1Create := true |> <| messages ::= (∪) {[CreateReq 1]} |>.

Definition send2_a : action :=
  λ s s', s.(obj1Exists) ∧ s.(sent1Create) ∧ negb s.(obj2Exists) ∧ negb s.(sent2Create) ∧
          s' = s <| sent2Create := true |> <| messages ::= (∪) {[CreateReq 2]} |>.

Definition reconcile: action := λ s s', send1_a s s' ∨ send2_a s s'.

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
         messages := ∅; |}.

Definition safe (s: state) := s.(obj2Exists) → s.(obj1Exists).

Hint Unfold init next : stm.
Hint Unfold reconcile cluster send1_a send2_a create1 create2 : stm.

Ltac stm_simp :=
  autounfold with stm;
  intros; intuition idtac;
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

Theorem messages_sent :
  ⌜init⌝ ∧ □ ⟨next⟩ ⊢ □ ⌜λ s, (CreateReq 1 ∈ s.(messages) ↔ s.(sent1Create)) ∧
                             (CreateReq 2 ∈ s.(messages) ↔ s.(sent2Create))⌝.
Proof.
  apply init_invariant.
  - stm.
  - stm.
Qed.

Lemma tla_pose_lemma {Σ} (p1 q1: predicate Σ) :
  (* the lemma to introduce *)
  (p1 ⊢ q1) →
  ∀ (p2 q2: predicate Σ),
  (* side condition to show precondition (to be proved by [tla_prop]) *)
  (p2 ⊢ p1) →
  (* the new goal *)
  (p2 ∧ q1 ⊢ q2) →
  (p2 ⊢ q2).
Proof. unseal. Qed.

Ltac tla_pose lem :=
  let H := fresh "Htemp" in
  epose proof lem as H;
  apply (tla_pose_lemma _ _ H); clear H;
  [ tla_prop | rewrite tla_and_assoc ].

Lemma combine_preds {Σ} (next: Σ → Σ → Prop) (P: Σ → Prop) :
  (□ ⟨ next ⟩ ∧ □ ⌜ P ⌝) == □ ⟨ λ (s s': Σ), next s s' ∧ P s ∧ P s' ⟩.
Proof.
  unseal.
  intuition eauto.
  - specialize (H k). intuition auto.
  - specialize (H k). intuition auto.
Qed.

Theorem obj1_invariant :
  ⌜init⌝ ∧ □ ⟨next⟩ ⊢ □ ⌜λ s, (s.(sent2Create) → s.(obj1Exists)) ∧ (s.(obj1Exists) → s.(sent1Create))⌝.
Proof.
  tla_pose messages_sent.
  rewrite !combine_preds.
  apply init_invariant.
  - stm.
  - stm.
Qed.

Theorem create_invariant :
  ⌜init⌝ ∧ □ ⟨next⟩ ⊢ □ ⌜λ s, s.(obj2Exists) → s.(sent2Create) ∧ s.(sent1Create) ∧ s.(obj1Exists)⌝.
Proof.
  tla_pose messages_sent.
  tla_pose obj1_invariant.
  rewrite !combine_preds.
  apply init_invariant.
  - stm.
  - stm.
Qed.

Theorem is_safe :
  ⌜init⌝ ∧ □ ⟨next⟩ ⊢ □ ⌜safe⌝.
Proof.
  rewrite -> create_invariant.
  apply always_impl_proper.
  unseal.
  stm.
Qed.

End example.
