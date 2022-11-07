From Coq.Relations Require Import Relation_Operators.

From TLA Require Export logic.
From TLA.examples.mutex Require Export spec wait_set.

Lemma state_inv l1 q1 l2 q2 :
  mkState l1 q1 = mkState l2 q2 ↔ l1 = l2 ∧ q1 = q2.
Proof.
  split.
  - inversion 1; subst; auto.
  - intuition congruence.
Qed.

Lemma thread_step_eq t σ pc σ' pc' :
  thread_step t (σ, pc) (σ', pc') ↔ thread_step_def t σ pc σ' pc'.
Proof. reflexivity. Qed.

#[global]
Opaque thread_step.

(* sanity check on semantics *)
Lemma thread_step_deterministic t ρ :
  ∀ ρ' ρ'' ,
  thread_step t ρ ρ' →
  thread_step t ρ ρ'' →
  ρ' = ρ''.
Proof.
  destruct ρ as [[l q] pc].
  intros [[l' q'] pc'] [[l'' q''] pc''].
  rewrite ?thread_step_eq.
  destruct pc; [ destruct l | destruct l | ..]; simpl;
    rewrite ?state_inv;
    try intuition congruence.
Qed.

Lemma next_inv σ tp σ' tp' :
  next {| state := σ; tp := tp; |} {| state := σ'; tp := tp'; |} →
  (σ' = σ ∧ tp' = tp) ∨
    (∃ t pc pc', tp !! t = Some pc ∧
                thread_step t (σ, pc) (σ', pc') ∧
                tp' = <[t := pc']> tp).
Proof.
  rewrite /next /step /=.
  destruct 1; repeat deex.
  - invc H1.
    destruct ρ' as [σ' pc']; simpl.
    right; eauto 8.
  - invc H. eauto.
Qed.

Ltac destruct_step :=
  lazymatch goal with
  | H: thread_step _ (?σ, ?pc) (?σ', ?pc') |- _ =>
      rewrite thread_step_eq /thread_step_def in H;
      destruct pc; simpl in H;
      [ let Heql := fresh "Heql" in
        destruct σ.(lock) eqn:Heql; simpl in H, Heql; subst
      | let Heql := fresh "Heql" in
        destruct σ.(lock) eqn:Heql; simpl in H, Heql; subst
      | (* kernel_wait *)
      | (* unlock_store *)
      | (* unlock_wake *)
      | exfalso; eauto (* finished *)
      ]
  end.

Lemma exist_prod {A B} (P: A * B → Prop) :
  (exists x y, P (x, y)) →
  exists xy, P xy.
Proof. naive_solver. Qed.

Lemma thread_step_enabled t :
  enabled (thread_step t) =
    (λ ρ, (ρ.2 = pc.kernel_wait → t ∉ ρ.1.(queue)) ∧
          (ρ.2 = pc.finished → False)).
Proof.
  apply pred_ext; intros [σ pc]; simpl.
  unfold enabled.
  split.
  - intros [[σ' pc'] Hstep].
    destruct_step; try intuition congruence.
  - intros [? ?].
    apply exist_prod.
    setoid_rewrite thread_step_eq.
    destruct σ as [l q]; simpl in *.
    destruct pc; [ destruct l | destruct l | .. ];
      simpl; intuition eauto.
Qed.

Lemma thread_step_enabled_s t ρ :
  enabled (thread_step t) ρ ↔
    (ρ.2 = pc.kernel_wait → t ∉ ρ.1.(queue)) ∧
    (ρ.2 = pc.finished → False).
Proof.
  rewrite thread_step_enabled //.
Qed.

Lemma step_enabled t :
  enabled (step t) =
    (λ s, ∃ pc, s.(tp) !! t = Some pc ∧
                (pc = pc.kernel_wait → t ∉ s.(state).(queue)) ∧
                (pc ≠ pc.finished)).
Proof.
  apply pred_ext; intros [σ tp]; simpl.
  unfold enabled, step; simpl.
  split.
  - intros; repeat deex.
    rewrite H. eexists; split; [ by auto | ].
    destruct ρ' as [σ' pc'].
    pose proof (thread_step_enabled_s t (σ, pc)) as [Htenable _];
      simpl in *.
    apply Htenable.
    eexists; eauto.
  - intros; repeat deex.
    rewrite H.
    pose proof (thread_step_enabled_s t (σ, pc)) as [_ Htenable];
      simpl in *.
    intuition auto.
    destruct H2 as [ρ' Hstep].
    eauto 8.
Qed.

#[export]
Hint Unfold init next step safe fair terminated : stm.

Ltac stm_simp :=
  autounfold with stm in *;
  intros; destruct_and?;
  repeat (match goal with
        | _ => progress deex
        | _ => progress subst
        | _ => destruct_and!
        | _ => destruct_or!
        | s: Config |- _ =>
            let σ := fresh "σ" in
            let tp := fresh "tp" in
            destruct s as [σ tp]; cbn in *
        | σ: State |- _ =>
            let l := fresh "l" in
            let q := fresh "q" in
            destruct σ as [l q]; cbn in *
        | ρ: State * pc.t |- _ =>
            let σ := fresh "σ" in
            let pc := fresh "pc" in
            destruct ρ as [σ pc]; cbn in *
        | H: ?x = ?x |- _ => clear H
        | H: @eq pc.t _ _ |- _ => solve [ inversion H ]
        | H: @eq _ (mkState _ _) (mkState _ _) |- _ =>
            invc H; cbn in *
        | H: @eq _ (mkConfig _ _) (mkConfig _ _) |- _ =>
            invc H; cbn in *
        | H: (_, _) = (_, _) |- _ => invc H
        | H: Some _ = Some _ |- _ => invc H
        | pc: pc.t, H: ?x = Some ?pc, H': ?x = Some ?pc' |- _ =>
            assert (pc = pc') by congruence; subst; clear H
        | H: thread_step ?t (_, ?pc) (_, _) |- _ =>
            first [ is_var pc (* make sure pc is not a variable *)
                  | rewrite thread_step_eq /= in H ]
        | H: ?x = ?x → _ |- _ => specialize (H eq_refl)
        | H: ?P → _, H': ?P |- _ => lazymatch type of P with
                                    | Prop => specialize (H H')
                                    end
        | H: context[set _ _] |- _ =>
            progress (unfold set in H; simpl in H)
        | H: @eq bool _ _ |- _ => solve [ inversion H ]
        | _ => progress (unfold set; simpl)
        | _ => progress lookup_simp
        | _ => progress cbn in *
        | _ => progress autorewrite with pc
        | _ => erewrite wait_set_unchanged by eauto
        | _ => erewrite wait_set_unchanged_not_present by eauto
        end).

Ltac stm :=
  stm_simp;
  try solve [ intuition (repeat deex; eauto) ];
  try congruence;
  repeat first [
      (split; [ solve [ intuition eauto ] | ])
    | (split; [ | solve [ intuition eauto ] ])
    ].

#[export]
Hint Extern 2 (_ ⊆ _) => set_solver : core.
