From TLA Require Import prelude.
From stdpp Require Import list gmap.

Lemma NoDup_singleton {A} (x: A) :
  NoDup [x].
Proof.
  constructor.
  - set_solver.
  - constructor.
Qed.

Lemma NoDup_app1 {A} (l: list A) (x: A) :
  NoDup (l ++ [x]) ↔ NoDup l ∧ x ∉ l.
Proof.
  rewrite NoDup_app.
  pose proof (NoDup_singleton x).
  (intuition auto); set_solver.
Qed.

Lemma NoDup_app1_fwd {A} (l: list A) (x: A) :
  NoDup l → x ∉ l →
  NoDup (l ++ [x]).
Proof.
  rewrite NoDup_app1 //.
Qed.

Lemma NoDup_cons_inv {A} (t: A) (ts: list A) :
  NoDup (t :: ts) ↔
  t ∉ ts ∧ NoDup ts.
Proof.
  split.
  - inversion 1; subst; auto.
  - intros.
    constructor; intuition auto.
Qed.

Lemma NoDup_head_not_in {A} (t: A) (ts: list A) :
  NoDup (t :: ts) →
  t ∉ ts.
Proof.
  rewrite NoDup_cons_inv; intuition auto.
Qed.
