import Dcare.Semantics

/-!
# Parametricity: care is a relational invariant

MAJOR FINDING (affirmed in review, 2026-11-08): a free theorem over the
policy ALONE is impossible. A policy that protects under one generator
may fail under another — different coalgebras emit different content and
reach different histories. Universality cannot ignore the substrate.

The free theorem therefore relates the POLICY and the GENERATOR together
(`GenRel` below): protection transfers across coupled substrates. This is
"terminal dependency on knowers," formalized — you cannot declare care;
care is a relational invariant between the reducer and the coalgebra it
protects. The paper carries this as its own subsection.

Superseded draft: the earlier `ParametricCoupling` (uniform trace for all
knowers under one generator) was sound but stronger than a free theorem;
it is subsumed by `GenRel` at the identity relation.
-/

namespace Dcare

/-- Substrate coupling: a coalgebra-morphism relation between two
generators — related knowers emit the SAME content and remain related. -/
def GenRel {K₁ K₂ : Type} (R : K₁ → K₂ → Prop)
    (g₁ : Generator K₁) (g₂ : Generator K₂) : Prop :=
  ∀ k₁ k₂, R k₁ k₂ →
    (g₁.step k₁).1 = (g₂.step k₂).1 ∧ R (g₁.step k₁).2 (g₂.step k₂).2

/-- The free theorem's engine: coupled generators produce IDENTICAL runs —
same emissions, same histories, same decisions. -/
theorem run_eq_of_genrel {K₁ K₂ : Type} {R : K₁ → K₂ → Prop}
    {g₁ : Generator K₁} {g₂ : Generator K₂} (hcouple : GenRel R g₁ g₂)
    (p : Policy) :
    ∀ (hist : List Content) (k₁ : K₁) (k₂ : K₂), R k₁ k₂ → ∀ n,
    runAux g₁ p hist k₁ n = runAux g₂ p hist k₂ n := by
  intro hist k₁ k₂ hR n
  induction n generalizing hist k₁ k₂ with
  | zero =>
      rw [runAux, runAux]
      by_cases hstop : p hist = Decision.stop
      · rw [if_pos hstop, if_pos hstop]
      · rw [if_neg hstop, if_neg hstop]
        rw [(hcouple k₁ k₂ hR).1]
  | succ m ih =>
      rw [runAux, runAux]
      by_cases hstop : p hist = Decision.stop
      · rw [if_pos hstop, if_pos hstop]
      · rw [if_neg hstop, if_neg hstop, (hcouple k₁ k₂ hR).1]
        exact ih (hist ++ [(g₂.step k₂).1]) (g₁.step k₁).2 (g₂.step k₂).2
          (hcouple k₁ k₂ hR).2

end Dcare
