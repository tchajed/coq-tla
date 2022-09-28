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
  sentCreate1: bool;
  sentCreate2: bool;

  (* remote cluster state (not directly readable) *)
  obj1Exists: bool;
  obj2Exists: bool;

  (* messages *)
  messages: gset message;
}.

Instance _eta_state : Settable _ :=
  settable! mkState<sentCreate1; sentCreate2;
                   obj1Exists; obj2Exists; messages>.

Local Notation action := (action state).
Local Notation predicate := (predicate state).
Local Notation exec := (exec state).

Implicit Types (s: state) (e: exec) (a: action).

Definition send1_a : action :=
  λ s s', negb s.(obj1Exists) ∧ negb s.(sentCreate1) ∧
          s' = s <| sentCreate1 := true |> <| messages ::= (∪) {[CreateReq 1]} |>.

Definition send2_a : action :=
  λ s s', s.(obj1Exists) ∧ s.(sentCreate1) ∧ negb s.(obj2Exists) ∧ negb s.(sentCreate2) ∧
          s' = s <| sentCreate2 := true |> <| messages ::= (∪) {[CreateReq 2]} |>.

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
  s = {| sentCreate1 := false; sentCreate2 := false;
         obj1Exists := false; obj2Exists := false;
         messages := ∅; |}.

End example.
