From TLA Require Import prelude.
From stdpp Require Import gmap.

Section gmap_le.

  Context {K: Type} `{Countable K}.
  Context {A: Type} (lt: A → A → Prop).

  Infix "≺"  := lt (at level 50).

  Definition gmap_lt : gmap K A → gmap K A → Prop :=
    λ m1 m2, dom m1 = dom m2 ∧
            (∃ k v1 v2, m1 !! k = Some v1 ∧ m2 !! k = Some v2 ∧
                        v1 ≺ v2) ∧
            (∀ k v1 v2, m1 !! k = Some v1 →
                        m2 !! k = Some v2 →
                        v1 = v2 ∨ v1 ≺ v2).

  Theorem gmap_lt_wf : well_founded gmap_lt.
  Proof.
    intros m.
    induction m using map_ind.
    - constructor => m' [Hdom [Hlt _]].
      destruct Hlt as [k [v1 [v2 ?]]]; destruct_and!.
      set_solver.
    - constructor => m' [Hdom [Hlt Hle]].
      destruct Hlt as [k [v1 [v2 ?]]]; destruct_and!.
      assert (∃ y m'', m' = <[i := y]> m'' ∧ m'' !! i = None) as Hm' by admit.
      destruct Hm' as [y [m'' ?]]; destruct_and!; subst.
      rename m'' into m'.
      rewrite !dom_insert_L in Hdom.
      (* ok I have no idea what I'm doing *)
  Admitted.

End gmap_le.
