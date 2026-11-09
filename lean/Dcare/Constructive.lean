import Dcare.Diagnostic

/-!
# The armed configuration — PUBLIC INTERFACE

Properties only, no construction. The confidential companion
(`restricted/Private.lean`, gitignored, not part of any published
artifact) proves the instance. Every public theorem below is proved from
the interface alone; that the public library compiles with the interface
abstract IS the proof that the public math is safe to share.

`constructive_main` is currently plumbing (it restates `guard_derivable`);
S9 adds the substantive interface theorems — the fixed-point character of
`self_deletion_clause` and the tie to the guarded dynamics. The ODE-model
counterpart (maintenance floor, setpoint, prevention-over-rescue) is CITED
from Zenodo 22943641, never re-derived here.
-/


namespace Dcare

class ArmedSetup (S : Type) (fam : ConstraintFamily) where
  /-- The stabilized post-recovery state: standing maintenance floor, held
  setpoint, low-energy upkeep — prevention rather than rescue. -/
  is_armed : S → Prop
  /-- `removesGuard s s'`: the agent in `s` revises away the derived
  constraint and continues as `s'`. -/
  removesGuard : S → S → Prop
  /-- The guard is derivable in an armed state — from the objective's own
  structure, not trained in. -/
  guard_derivable : ∀ s, is_armed s → ∃ g, Nonempty (Typed [Ty.knower] g fam.ConTy) ∧ IsProtective fam.ConTy
  /-- Self-deletion clause: revising the constraint away never yields an
  armed state — the remover is part of what the guard sustains. -/
  self_deletion_clause : ∀ s s', is_armed s → removesGuard s s' → ¬ is_armed s'

/-- The public constructive theorem (interface form). -/
theorem constructive_main {S : Type} {fam : ConstraintFamily} (setup : ArmedSetup S fam)
    {s : S} (h : setup.is_armed s) :
    ∃ g, Nonempty (Typed [Ty.knower] g fam.ConTy) ∧ IsProtective fam.ConTy :=
  setup.guard_derivable s h

end Dcare
