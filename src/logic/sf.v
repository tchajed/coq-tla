(*|

========================
Strong fairness
========================

The theory around strong fairness is largely analogous to weak fairness, but it's less well-developed here because we haven't found a case where we want it. What we do prove here is SF1, the rule analogous to WF1 that allows to use a strong fairness assumption to prove a leads-to fact.

Also we prove that strong fairness implies weak fairness, justifying the naming.
|*)
From TLA Require Import defs automation.
From TLA Require Import propositional_ltl modalities.
From TLA Require Import classical.
From TLA.logic Require Import preds wf.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate) (a: action Σ).

Theorem strong_fairness_alt2 a :
  strong_fairness a == (□◇ (tla_enabled a) → □ ◇ ⟨a⟩).
Proof.
  rewrite /strong_fairness.
  rewrite !implies_to_or.
  tla_simp.
  rewrite -!eventually_or.
  rewrite always_eventually_distrib.
  tla_simp.
Qed.

Lemma strong_fairness_alt3 a :
  strong_fairness a == (□◇⟨a⟩ ∨ ◇□(! tla_enabled a)).
Proof.
  rewrite strong_fairness_alt2.
  rewrite !implies_to_or.
  tla_simp.
  rewrite tla_or_comm //.
Qed.

Lemma strong_to_weak_fairness a :
  strong_fairness a ⊢ weak_fairness a.
Proof.
  rewrite weak_fairness_alt3 strong_fairness_alt3.
  rewrite eventually_always_weaken //.
Qed.

Lemma tla_sf1 (p q F: predicate) (next a: action Σ) :
  ∀ (Hpuntilq: ⊢ p ∧ ⟨next⟩ → later p ∨ later q)
    (Haq: ⊢ p ∧ ⟨next⟩ ∧ ⟨a⟩ → later q)
    (Henable: ⊢ □p ∧ □⟨next⟩ ∧ □F → tla_enabled a),
  (⊢ □ ⟨next⟩ ∧ strong_fairness a ∧ □F → p ~~> q).
Proof.
  rewrite strong_fairness_alt3.
  unseal.
  destruct H as (Hnext & Hsf_alt & HF).

  edestruct (until_next p q next e Hpuntilq Hnext);
    [ eassumption | | by auto ].

  destruct Hsf_alt as [Ha | [k' Hnotenabled]].
  - destruct (Ha k) as [k' Ha'].
    exists (S k').
    change (S k' + k) with (1 + (k' + k)). rewrite -drop_drop.
    apply Haq; eauto.
  - contradiction (Hnotenabled k).
    eapply Henable; intuition eauto.
    + rewrite ?drop_drop.
      replace (k0 + (k + k')) with ((k0 + k') + k) by lia.
      eauto.
    + rewrite ?drop_drop; eauto.
Qed.

End TLA.
