From TLA Require Import defs automation.
From TLA Require Import propositional_ltl modalities.
From TLA Require Import classical.

Section TLA.

Context [Σ: Type].

Notation exec := (exec Σ).
Notation predicate := (predicate Σ).

Implicit Types (e: exec) (p q: predicate).

Lemma weak_until_alt p q :
  weak_until p q == strong_until p (q ∨ □ p).
Proof.
  unseal.
  split.
  - unseal.
  - intros [i [Hi Hpre]].

    (* some classical logic nonsense: learn where p stops holding *)
    apply classical.classical_or_intror.
    setoid_rewrite classical.not_forall;
      intros [j Hnotp].

    exists i; unseal.
    intuition eauto.
    destruct (Compare_dec.lt_dec j i).
    * contradict Hnotp; eauto.
    * contradiction Hnotp.
      replace j with ((j - i) + i) by lia.
      apply H.

      Unshelve.
      exact 0.
Qed.

End TLA.
