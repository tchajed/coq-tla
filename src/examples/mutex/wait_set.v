From TLA Require Import prelude.
From stdpp Require Import gmap.

From TLA Require Import automation.
From TLA.examples.mutex Require Import spec.

Ltac lookup_simp :=
  subst;
  repeat
    match goal with
    | H: _ |- _ => rewrite lookup_insert in H
    | H: _ |- _ => rewrite -> lookup_insert_ne in H by congruence
    | _ => rewrite lookup_insert
    | _ => rewrite -> lookup_insert_ne by congruence
    end;
  try congruence.

(*|
===========
Wake set
===========
|*)

Definition wait_pc pc :=
  pc = pc.lock_cas ∨
  pc = pc.futex_wait ∨
  pc = pc.kernel_wait.

#[global]
Instance wait_pc_dec pc : Decision (wait_pc pc).
Proof. apply _. Defined.

Definition wait_set (tp: gmap Tid pc.t) : gset _ :=
  dom (filter (λ '(tid, pc), wait_pc pc) tp).

(* TODO: remove duplicate from spinlock_many_threads *)
Lemma gset_ext {A: Type} `{Countable A} (s1 s2: gset A) :
  (∀ x, x ∈ s1 ↔ x ∈ s2) →
  s1 = s2.
Proof.
  intros.
  apply leibniz_equiv.
  apply set_equiv.
  auto.
Qed.

(* TODO: remove duplicate from spinlock_many_threads *)
Lemma filter_is_Some {K: Type} `{Countable K} {V: Type}
  (P: (K * V) → Prop) `{∀ x, Decision (P x)} (m: gmap K V) k :
  is_Some (filter P m !! k) ↔ (∃ v, m !! k = Some v ∧ P (k,v)).
Proof.
  split; (intuition auto); repeat deex.
  - destruct H1 as [v Hlookup].
    rewrite map_filter_lookup_Some in Hlookup.
    eauto.
  - rewrite map_filter_lookup. rewrite /is_Some.
    exists v.
    rewrite H1 /=.
    rewrite option_guard_True //.
Qed.

Lemma elem_of_wait_set t tp :
  t ∈ wait_set tp ↔ (∃ pc, tp !! t = Some pc ∧ wait_pc pc).
Proof.
  rewrite /wait_set.
  rewrite elem_of_dom filter_is_Some //.
Qed.

(* TODO: almost identical theorem in spinlock_many_threads *)
Lemma wait_set_insert_other t tp pc' :
  (pc' = pc.unlock_store ∨ pc' = pc.unlock_wake ∨ pc' = pc.finished) →
  wait_set (<[t := pc']> tp) = wait_set tp ∖ {[t]}.
Proof.
  intros.
  apply gset_ext => t'.
  rewrite elem_of_wait_set
    elem_of_difference elem_of_singleton elem_of_wait_set.
  rewrite /wait_pc.
  destruct (decide (t = t')); lookup_simp.
  - naive_solver.
  - naive_solver.
Qed.

Lemma not_wait_pc pc :
  ¬wait_pc pc ↔ (pc = pc.unlock_store ∨ pc = pc.unlock_wake ∨ pc = pc.finished).
Proof.
  unfold wait_pc.
  intuition (try congruence).
  destruct pc; eauto; try congruence.
Qed.

Lemma wait_set_insert_same t pc' tp :
  wait_pc pc' →
  wait_set (<[t := pc']> tp) = wait_set tp ∪ {[t]}.
Proof.
  intros Hpc'.
  apply gset_ext => t'.
  rewrite elem_of_wait_set elem_of_union elem_of_singleton elem_of_wait_set.
  split.
  - intros; repeat deex.
    destruct (decide (t = t')); lookup_simp; eauto.
  - intros [H|H]; lookup_simp; eauto.
    repeat deex; destruct_and?.
    destruct (decide (t = t')); lookup_simp; eauto.
Qed.

#[export]
Hint Extern 1 (wait_pc _) => rewrite /wait_pc : core.

Lemma wait_set_unchanged t pc pc' tp :
  tp !! t = Some pc →
  wait_pc pc →
  wait_pc pc' →
  wait_set (<[t := pc']> tp) = wait_set tp.
Proof.
  intros.
  apply gset_ext => t'.
  rewrite wait_set_insert_same //.
  assert (t ∈ wait_set tp).
  { rewrite elem_of_wait_set; eauto. }
  set_solver.
Qed.

Lemma in_wait_set tp t pc :
  tp !! t = Some pc →
  wait_pc pc →
  t ∈ wait_set tp.
Proof.
  intros.
  rewrite elem_of_wait_set.
  naive_solver.
Qed.

Lemma not_in_wait_set tp t pc :
  tp !! t = Some pc →
  ¬wait_pc pc →
  t ∉ wait_set tp.
Proof.
  intros.
  rewrite elem_of_wait_set.
  intros [pc' [Hlookup Hwait_pc]].
  assert (Some pc = Some pc').
  { rewrite -H -Hlookup //. }
  congruence.
Qed.

#[export]
Hint Extern 1 (¬wait_pc ?pc) => apply not_wait_pc : core.

#[export]
Hint Resolve in_wait_set not_in_wait_set : core.

Lemma wait_set_unchanged_not_present t pc pc' tp :
  tp !! t = Some pc →
  ¬wait_pc pc →
  ¬wait_pc pc' →
  wait_set (<[t := pc']> tp) = wait_set tp.
Proof.
  intros.
  apply gset_ext => t'.
  rewrite wait_set_insert_other //.
  { rewrite not_wait_pc in H1; auto. }
  assert (t ∉ wait_set tp) by eauto.
  set_solver.
Qed.

#[export]
Hint Rewrite wait_set_unchanged using (by auto) : pc.
#[export]
Hint Rewrite wait_set_insert_other using (by auto) : pc.

Lemma wait_set_remove_subset (W: gset Tid) (t: Tid) :
  t ∈ W → W ∖ {[t]} ⊂ W.
Proof. set_solver. Qed.

Lemma wait_set_remove_eq (W: gset Tid) (t: Tid) :
  t ∉ W → W ∖ {[t]} = W.
Proof. set_solver. Qed.

#[export]
Hint Resolve wait_set_remove_subset wait_set_remove_eq : core.
Hint Rewrite wait_set_remove_eq using (by eauto) : pc.

(*|
===========
Wake set
===========
|*)

Definition signal_set (tp: gmap Tid pc.t) : gset Tid :=
  dom (filter (λ '(_, pc), pc = pc.unlock_wake) tp).

Lemma elem_signal_set tp t :
  t ∈ signal_set tp ↔ tp !! t = Some pc.unlock_wake.
Proof.
  rewrite /signal_set.
  rewrite elem_of_dom filter_is_Some. naive_solver.
Qed.

Lemma elem_signal_set_2 tp t :
  tp !! t = Some pc.unlock_wake →
  t ∈ signal_set tp.
Proof.
  apply elem_signal_set.
Qed.

Lemma not_elem_signal_set tp t pc :
  tp !! t = Some pc →
  pc ≠ pc.unlock_wake →
  t ∉ signal_set tp.
Proof.
  rewrite elem_signal_set.
  naive_solver.
Qed.

#[export]
Hint Resolve elem_signal_set_2 not_elem_signal_set : core.

Lemma signal_set_remove tp t pc' :
  pc' ≠ pc.unlock_wake →
  signal_set (<[t := pc']> tp) = signal_set tp ∖ {[t]}.
Proof.
  intros.
  apply gset_ext => t'.
  rewrite /signal_set. rewrite elem_of_difference !elem_of_dom !filter_is_Some.
  rewrite elem_of_singleton.
  destruct (decide (t = t')); lookup_simp; naive_solver.
Qed.

#[export]
Hint Rewrite signal_set_remove using (by auto) : pc.

Lemma signal_set_add tp t :
  signal_set (<[t := pc.unlock_wake]> tp) = signal_set tp ∪ {[t]}.
Proof.
  intros.
  apply gset_ext => t'.
  rewrite /signal_set. rewrite elem_of_union !elem_of_dom !filter_is_Some.
  rewrite elem_of_singleton.
  destruct (decide (t = t')); lookup_simp; naive_solver.
Qed.

#[export]
Hint Rewrite signal_set_add : pc.
