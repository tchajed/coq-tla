From TLA Require Export defs automation.
From TLA Require Export propositional_ltl modalities.
From TLA.logic Require Export preds safety wf leads_to.

Ltac tla_clear p :=
  rewrite -> (any_impl_true p); tla_simp.

Ltac tla_intro :=
  first [ apply impl_intro | apply impl_intro2 ].

Ltac tla_left :=
  first [ tla_apply tla_or_introl |  apply leads_to_or_left ].
Ltac tla_right :=
  first [ tla_apply tla_or_intror |  apply leads_to_or_right ].

Ltac tla_intros := repeat tla_intro.
