From Coq.ssr Require Export ssreflect.
From stdpp Require Export base.

#[global] Set Default Proof Using "Type".
#[global] Set Default Goal Selector "!".
#[global] Set Printing Projections.
(* re-enable [if] on non-booleans *)
#[global] Open Scope general_if_scope.

From Coq.Logic Require Export
  PropExtensionality FunctionalExtensionality.
