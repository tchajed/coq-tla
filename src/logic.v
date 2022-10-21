(*|

================
The TLA logic
================

This file just re-exports files that make up the entire theory.

The most interesting ones are safety_, wf_ (for theory around weak fairness), and
leads_to_.

.. _safety: https://tchajed.github.io/coq-tla/logic/safety.html
.. _wf: https://tchajed.github.io/coq-tla/logic/wf.html
.. _leads_to: https://tchajed.github.io/coq-tla/logic/leads_to.html

|*)

From TLA Require Export defs automation.
From TLA Require Export propositional_ltl modalities.
From TLA.logic Require Export preds safety wf sf leads_to.

Tactic Notation "tla_clear" :=
  apply impl_drop_hyp.

Tactic Notation "tla_clear" constr(p) :=
  rewrite -> (any_impl_true p); tla_simp.

Ltac tla_intro :=
  first [ apply impl_intro | apply impl_intro2 ].

Ltac tla_left :=
  first [ tla_apply tla_or_introl |  apply leads_to_or_left ].
Ltac tla_right :=
  first [ tla_apply tla_or_intror |  apply leads_to_or_right ].

Ltac tla_intros := repeat tla_intro.
