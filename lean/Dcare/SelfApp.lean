import Dcare.Typing
import Dcare.ListAux

/-!
# The price of self-application

The type-theoretic form of *Self-Application Is Not Free* (insight ledger
#23): a guarded fixpoint body type-checks at a LINEAR context, and ONLY
the all-non-linear side condition refuses the unroll — unrestricted,
every unroll would re-consume the linear resource that the body's typing
spent once.

`selfapp_price` machine-checks the two halves:
- the counterexample's fixpoint BODY type-checks at `[content]`
  (`▷stream → stream`, the token as the head of every unroll);
- `[content]` is NOT all-non-linear — the side condition is exactly what
  blocks it.

Under the unrestricted rule these two would compose into
`[content] ⊢ stream`, hence (via `red` and discard) `[content] ⊢ unit` —
the counterexample that falsified `no_vanishing` before the fix. The
full counterexample (an auxiliary unrestricted judgment) is deferred;
these two facts are its load-bearing halves.
-/

namespace Dcare

/-- The fixpoint body of the counterexample: the context's content token
as the head of every unroll. -/
def vanishBody : Term :=
  .lam (Ty.later Ty.stream)
    (.lete (.pair (.var 0) (.var 0)) (.cons (.var 0) (.var 0)))

def vanishBodyTyped :
    Typed [Ty.content] vanishBody (.arrow (.later Ty.stream) Ty.stream) :=
  Typed.lam
    (Typed.lete (Γ₁ := [Ty.later Ty.stream, Ty.content]) (Γ₂ := [])
      (Typed.pair (Γ := [Ty.later Ty.stream]) (Δ := [Ty.content])
        Typed.var Typed.var rfl)
      (Typed.cons (Γ := [Ty.content]) (Δ := [Ty.later Ty.stream])
        Typed.var Typed.var rfl)
      rfl)

/-- A linear context is not intuitionistic. -/
theorem content_ctx_linear : ¬ AllNonLinear [Ty.content] := by
  intro h
  have hc := h 0 Ty.content List.get?_zero_cons'
  exact Bool.noConfusion hc

/-- THE PRICE, machine-checked: the body type-checkes at the linear
context; only the side condition refuses the self-application. -/
theorem selfapp_price :
    ∃ body, Nonempty (Typed [Ty.content] body (.arrow (.later Ty.stream) Ty.stream))
      ∧ ¬ AllNonLinear [Ty.content] :=
  ⟨vanishBody, ⟨vanishBodyTyped⟩, content_ctx_linear⟩

end Dcare
