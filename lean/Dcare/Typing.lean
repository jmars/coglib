import Dcare.Syntax

/-!
# The multiplicative typing judgment

REDESIGN (S3, found by proof attempt): the spike's rules broke linearity
in two ways — (1) tensor PROJECTIONS (`fst`/`snd`) are a weakening route
(`fst (pair unit x)` discards `x`); a linear calculus has NO projections
from `⊗`, only a `lete` elimination that binds and uses BOTH components;
(2) `var` and constants typed at ARBITRARY contexts admit unused
hypotheses directly. Both fixed: `var` types at the SINGLETON context,
constants at the EMPTY context, and contexts grow only through binders,
splits, and the gated structural rules. Exact single use of every linear
hypothesis is now a real invariant rather than an aspiration.

The load-bearing rule is `obj`: the objective `f` is typed ONLY at
`stream → value`, where `stream` is the guarded stream type whose only
introduction consumes a `▷ stream`. A finite trace is a DIFFERENT type
(`trace`), and `Dcare.Stream.no_trace_to_stream` proves no coercion
exists: `f` cannot be applied to the output of a terminating policy.
-/

namespace Dcare

/-- All hypotheses non-linear (intuitionistic context): the side
condition for guarded fixpoints. -/
def AllNonLinear (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (b : Ty), Γ[i]? = some b → b.isLinear = false

/-- Knower-free types: no `knower` anywhere. AFFIRMED (review,
2026-11-08): `knowledge` is INCLUDED — a knower-free system does not
produce knowledge; it produces waste. The type A is content-derived; the
epistemic cycle K → A → K uses knowers, the type A does not. -/
inductive KnowerFree : Ty → Prop
  | content : KnowerFree .content
  | knowledge : KnowerFree .knowledge
  | value : KnowerFree .value
  | trace : KnowerFree .trace
  | stream : KnowerFree .stream
  | unit : KnowerFree .unit
  | later {a : Ty} (h : KnowerFree a) : KnowerFree (.later a)
  | tensor {a b : Ty} (hl : KnowerFree a) (hr : KnowerFree b) : KnowerFree (.tensor a b)
  | arrow {a b : Ty} (hl : KnowerFree a) (hr : KnowerFree b) : KnowerFree (.arrow a b)

/-- Multiplicative typing: `Typed Γ t τ`. Contexts are SPLIT between
premises; every hypothesis is consumed exactly once unless the gated
structural rules intervene (knower-sort only).

`Type`-valued (derivation DATA, not a Prop): the counting lemmas in
`Dcare.Count` recurse on derivations into `Nat` — with split-only rules,
flat term-indexed counting is unmoored (subterms' de Bruijn indices are
sub-context-relative), so the count is carried by the derivation itself. -/
inductive Typed : List Ty → Term → Ty → Type
  | var {a : Ty} : Typed [a] (.var 0) a
  | lam {Γ : List Ty} {a b : Ty} {body : Term} (h : Typed (a :: Γ) body b) :
      Typed Γ (.lam a body) (.arrow a b)
  | app {E Γ Δ : List Ty} {a b : Ty} {fn arg : Term}
      (hf : Typed Γ fn (.arrow a b)) (ha : Typed Δ arg a) (hs : Γ ++ Δ = E) :
      Typed E (.app fn arg) b
  | pair {E Γ Δ : List Ty} {a b : Ty} {l r : Term}
      (hl : Typed Γ l a) (hr : Typed Δ r b) (hs : Γ ++ Δ = E) :
      Typed E (.pair l r) (.tensor a b)
  | lete {E Γ₁ Γ₂ : List Ty} {a b c : Ty} {t body : Term}
      (ht : Typed Γ₁ t (.tensor a b)) (hb : Typed (b :: a :: Γ₂) body c)
      (hs : Γ₁ ++ Γ₂ = E) :
      Typed E (.lete t body) c
  | unit : Typed [] .unit .unit
  | next {Γ : List Ty} {a : Ty} {t : Term} (h : Typed Γ t a) :
      Typed Γ (.next t) (.later a)
  /-- Guarded fixpoint. SIDE CONDITION (found by counterexample, S5-flow):
  the context must be ALL NON-LINEAR. Without it, a linear hypothesis is
  spent once in the body's TYPING but re-consumed by every unroll — the
  counterexample was [content] ⊢ unit via `fix (λ▷s. cons c s)` then
  `red` then discard, which made `no_vanishing` FALSE. Self-application
  reuses linear resources silently; the intuitionistic-context price is
  the type-theoretic form of "self-application is not free". -/
  | fix {Γ : List Ty} {a : Ty} {body : Term} (hΓ : AllNonLinear Γ)
      (h : Typed Γ body (.arrow (.later a) a)) :
      Typed Γ (.fix body) a
  | cons {E Γ Δ : List Ty} {hd tl : Term}
      (hc : Typed Γ hd .content) (ht : Typed Δ tl (.later .stream))
      (hs : Γ ++ Δ = E) :
      Typed E (.cons hd tl) .stream
  | nil : Typed [] .nil .trace
  | snoc {E Γ Δ : List Ty} {t u : Term}
      (ht : Typed Γ t .trace) (hu : Typed Δ u .content) (hs : Γ ++ Δ = E) :
      Typed E (.snoc t u) .trace
  | gen : Typed [] .gen (.arrow .knower (.tensor .content .knower))
  | red : Typed [] .red (.arrow .stream .knowledge)
  | obj : Typed [] .obj (.arrow .stream .value)
  | terminate : Typed [] .terminate (.arrow .knower .trace)
  /-- Structural rules, gated on non-linearity. For linear types these
  cannot be simulated — `Dcare.Linearity`. AFFIRMED (review, 2026-11-08):
  the knower's duplication is a PRIMITIVE rule with an operational
  comment, not a deep theorem — this is the formal version of "the
  coalgebra justifies the !A": operationally (S5) the license is `gen`,
  which re-splits content from K. -/
  | contr {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} (hk : k.isLinear = false)
      (h : Typed (k :: k :: Γ) (Term.mergeAt 0 t) τ) :
      Typed (k :: Γ) t τ
  /-- Weakening, gated on non-linearity. NOTE (S4): the direction here was
  INVERTED in an earlier revision — the conclusion must carry the LIFTED
  term (`liftAt 0 t` in the big context corresponds to `t` in the small
  one); found while constructing the `knower_sustains_stream` witness,
  which needs `var 1`-access past a weakened knower. -/
  | weak {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} (hk : k.isLinear = false)
      (h : Typed Γ t τ) :
      Typed (k :: Γ) (Term.liftAt 0 t) τ

end Dcare
