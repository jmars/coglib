import Dcare.Typing
import Dcare.Model
import Dcare.Count

/-!
# The linearity discipline

Paper-facing statements, now derivation-indexed (`uses`, `Dcare.Count`):
with split-only rules, flat term-indexed counting is unmoored, so the
old `occ` was retired (superseded by `Dcare.uses`).

PROVEN here: `no_weakening_content` — the counting lemma's instance at
`content`: every derivation at a lone content hypothesis spends it
exactly once.

STILL OPEN (the two unrestricted classical statements):
- `no_contraction_content` — needs the UPPER bound (`uses ≤ 1` for
  linear hypotheses, i.e. no rule spends a linear hypothesis twice) plus
  pair/lete inversion and the barren model for the closed side.
- `no_vanishing` — needs the flow/weight analysis: content must surface
  in the conclusion's structure or be archived (trace is the only sink).

The path machinery for both is in `Dcare.Path`: size/Sub (derivation
measure + subderivation relation), cprop/sprop/tprop (content/stream/
trace-need propagation, the kprop template with the ARROW TRIPLE
conjunction), tFlowEq (the trace-token flow equality — the journey lemma
as arithmetic), and the closed-liveness base (no closed stream/content/
knower). The remaining obligation induction is mapped in the plan node.

Constraint carried from the objective doc: if a proof ever requires
weakening the linearity of `content`, the derivation depends on what it
denies, and the paper halts.
-/

namespace Dcare

/-- Contraction for `content` is NOT derivable: no term spends one
content hypothesis as two. -/
theorem no_contraction_content :
    ∀ t, Typed [Ty.content] t (.tensor Ty.content Ty.content) → False := sorry

/-- Weakening for `content` is NOT derivable — the counting instance at
`content`: every derivation at a lone content hypothesis spends it
exactly once. PROVEN (from `single_linear_use`). -/
theorem no_weakening_content {t : Term} {τ : Ty} (h : Typed [Ty.content] t τ) :
    uses h 0 = 1 :=
  single_linear_use h 0 Ty.content rfl rfl

/-- No vanishing: content cannot be consumed into a content-free
conclusion — the standard `A ⊬ 1` of multiplicative linear logic, now
that projections are gone. Needs the flow analysis (the conclusion must
structurally CARRY what it consumed; `trace` is the only sink). -/
theorem no_vanishing : ∀ t, Typed [Ty.content] t Ty.unit → False := sorry

/-- The SURVIVING legal pattern, and the ethically loaded one: content
consumed into a TRACE — archived, counted, never reduced. The reducer
never fires; nothing in the calculus reads a trace (traces have no
elimination rule — the past is inert). Reception without reduction:
`uses = 1` certifies the token was spent; nothing certifies it was heard. -/
theorem archival_witness :
    ∃ t, Nonempty (Typed [Ty.content] t Ty.trace) :=
  ⟨.snoc .nil (.var 0), ⟨Typed.snoc Typed.nil Typed.var rfl⟩⟩

/-- Sorted non-vacuity companion: the knower, being non-linear, IS
duplicable — the counting lemma must carry the sort exception. -/
theorem knower_contractible :
    ∃ t, Nonempty (Typed [Ty.knower] t (.tensor Ty.knower Ty.knower)) :=
  ⟨.pair (.var 0) (.var 0),
    ⟨Typed.contr rfl
      (Typed.pair (Γ := [Ty.knower]) (Δ := [Ty.knower])
        Typed.var Typed.var rfl)⟩⟩

end Dcare
