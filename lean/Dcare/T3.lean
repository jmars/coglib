import Dcare.Parametricity

/-!
# T3 — Parametric universality

The relational form: under substrate coupling, protection transfers —
the same policy protects related knowers of coupled generators.
Universality is a property of the (policy, generator) pair, never of the
policy alone.

S7 proof route: `GenRel` + `R k₁ k₂` implies the two runs produce EQUAL
traces (induction over intervals: same emissions ⇒ same histories ⇒ same
decisions), so `IsInfinite` transfers. The substrate-blindness adversary
(`Dcare.Adversaries.adversary_blind_transfer`) shows the coupling
hypothesis is not removable.
-/

namespace Dcare

theorem T3_main {K₁ K₂ : Type} {R : K₁ → K₂ → Prop}
    {g₁ : Generator K₁} {g₂ : Generator K₂}
    (hcouple : GenRel R g₁ g₂) (p : Policy) (k₁ : K₁) (k₂ : K₂)
    (hR : R k₁ k₂) :
    Protected g₁ p k₁ ↔ Protected g₂ p k₂ := by
  have hrun : run g₁ p k₁ = run g₂ p k₂ :=
    funext fun n => run_eq_of_genrel hcouple p [] k₁ k₂ hR n
  unfold Protected
  rw [hrun]

end Dcare
