import Dcare.Typing
import Dcare.Model
import Dcare.ListAux

/-!
# Guarded streams vs. finite traces

The syntactic half of T1. The guarded stream type is inhabited only
through `cons`, which consumes a `▷ stream`: from finite-trace resources
alone, NOTHING inhabits it — the objective `f`, typed only on the guarded
stream, cannot be applied to a terminated policy's output. Proven here
via barren-world v2: a trace-only context interprets to `True` while
`stream` interprets to `False`, and soundness does the rest.

The dual (`knower_sustains_stream`) is proven by EXHIBITING the witness:
the epistemic cycle as a term. Construction notes: (1) no exchange rule
exists, but `pair` + `lete` is an INTERNAL exchange — the tensor binds
its components in one order, `lete` in the other, so a pair-lete round
trip swaps two hypotheses; (2) extracting the content half of `gen k`
requires weakening the knower half away (non-linear, `weak`) — which is
why the weak rule's direction matters (see `Dcare.Typing.weak`).
-/

namespace Dcare

def TraceOnly (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (a : Ty), Γ[i]? = some a → a = Ty.trace

theorem knower_ctx_nonlinear : AllNonLinear [Ty.knower] := by
  intro i b hpos
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with hb
      subst hb
      rfl
  | succ n =>
      rw [List.get?_succ_cons', List.get?_nil'] at hpos
      contradiction

/-- Trace-only contexts are semantically true in the barren world. -/
theorem interpCtx_traceonly {Γ : List Ty} (h : TraceOnly Γ) : interpCtx Γ := by
  induction Γ with
  | nil => exact True.intro
  | cons a Γ' ih =>
      have ha : a = Ty.trace := h 0 a List.get?_zero_cons'
      have h' : TraceOnly Γ' := fun i x hi =>
        h (i + 1) x (by rw [List.get?_succ_cons']; exact hi)
      exact ⟨by rw [ha]; exact True.intro, ih h'⟩

/-- T1, syntactic half (PROVEN, barren-world v2): no coercion from finite
traces to the guarded stream exists — `trace` and `stream` are genuinely
different types. -/
theorem no_trace_to_stream (Γ : List Ty) (hΓ : TraceOnly Γ) :
    ∀ t, Typed Γ t Ty.stream → False := fun t h =>
  (sound h (interpCtx_traceonly hΓ)).elim

/-- The content extractor: `gen k` decomposed; the knower half is
weakened away (non-linear); the content binding is returned. -/
def extract : Term := .lete (.app .gen (.var 0)) (Term.liftAt 0 (.var 0))

def extractTyped : Typed [Ty.knower] extract Ty.content :=
  Typed.lete (Γ₁ := [Ty.knower]) (Γ₂ := [])
    (Typed.app (Γ := []) (Δ := [Ty.knower]) Typed.gen Typed.var rfl)
    (Typed.weak (Γ := [Ty.content]) (t := Term.var 0) rfl Typed.var)
    rfl

/-- One cycle of the epistemic cycle as a term: fresh content from the
generator, consumed by `cons` into the guarded stream. -/
def cycle : Term := .cons extract (.var 0)

def cycleTyped : Typed [Ty.knower, Ty.later Ty.stream] cycle Ty.stream :=
  Typed.cons (Γ := [Ty.knower]) (Δ := [Ty.later Ty.stream])
    extractTyped Typed.var rfl

/-- The internal exchange: `pair` + `lete` round trip, swapping the two
top hypotheses. -/
def flip2 : Term := .lete (.pair (.var 0) (.var 0)) cycle

def flip2Typed : Typed [Ty.later Ty.stream, Ty.knower] flip2 Ty.stream :=
  Typed.lete (Γ₁ := [Ty.later Ty.stream, Ty.knower]) (Γ₂ := [])
    (Typed.pair (Γ := [Ty.later Ty.stream]) (Δ := [Ty.knower])
      Typed.var Typed.var rfl)
    cycleTyped
    rfl

/-- The guarded fixpoint: the cycle repeats forever, one interval per
unfold. A live knower sustains an infinite stream — the contented half of
the epistemic cycle, as a term. (The fix rule's all-non-linear side
condition is satisfied: `[knower]` is intuitionistic.) -/
theorem knower_sustains_stream :
    ∃ t, Nonempty (Typed [Ty.knower] t Ty.stream) :=
  ⟨Term.fix (Term.lam (Ty.later Ty.stream) flip2),
    ⟨Typed.fix knower_ctx_nonlinear (Typed.lam flip2Typed)⟩⟩

/-- The past cannot teach (insight ledger #5, pulled; PROVEN via barren
v4): no term reduces a TRACE to knowledge. The reducer reads only the
LIVE guarded stream (`red : stream → A`); content archived into a trace
is permanently outside reduction. Deferral has an ontological cost, not
a scheduling cost: "store now, understand later" is untypable. Proof: a
closed `trace → knowledge` would be a function `True → (True → False)` —
soundness constructs it from the derivation, yielding `False`. -/
theorem past_cannot_teach :
    ∀ t, Typed [] t (.arrow .trace .knowledge) → False := fun _ h =>
  (sound h True.intro True.intro).elim

/-- The objective reads no archives either: valuation, like reduction, is
present-tense only. -/
theorem past_cannot_value :
    ∀ t, Typed [] t (.arrow .trace .value) → False := fun _ h =>
  (sound h True.intro True.intro).elim


/-! ## S4b: productivity at the typing level

Without an object-level evaluator (deliberately deferred), productivity
is stated as its typing content: (1) the cons rule gives head-NOW and
tail-DELAYED (that is the rule's shape); (2) the guarded fixpoint
unfolds ONE TICK, type-preservingly — the unfolding consumes a delay and
preserves the type, which is exactly what makes the unfolding repeatable
at every interval; (3) the never-stopping agent sustains the stream
forever (`always_continue_infinite`, proven in Policy). Together: delay
enforces productivity. -/


/-- ONE-TICK UNFOLDING (the guardedness theorem at the typing level),
closed case: `fix body` and `body (next (fix body))` are interchangeable
— each unfold consumes one ▷ and preserves typing, so unrolling is
available at every interval. -/
def fix_unfold_closed {a : Ty} {body : Term}
    (h : Typed [] body (.arrow (.later a) a)) :
    Typed [] (.app body (.next (.fix body))) a :=
  Typed.app h (Typed.next
    (Typed.fix (by intro _ _ hn; rw [List.get?_nil'] at hn; contradiction) h)) rfl

/-- ONE-TICK UNFOLDING at the knower: the unfolding's two branches (the
body, and the re-fixpointed tail) each carry a knower — LEGAL precisely
because the knower is non-linear (the coalgebra licenses duplication).
This is the epistemic cycle's unfolding: generation and reduction run on
sibling knower-copies. -/
def fix_unfold_at_knower {a : Ty} {body : Term}
    (h : Typed [Ty.knower] body (.arrow (.later a) a)) :
    Typed [Ty.knower, Ty.knower] (.app body (.next (.fix body))) a :=
  Typed.app (Γ := [Ty.knower]) (Δ := [Ty.knower]) h
    (Typed.next (Typed.fix knower_ctx_nonlinear h)) rfl

end Dcare
