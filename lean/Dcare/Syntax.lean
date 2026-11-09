/-!
# Object language: types and terms

The derivation-of-care formalization, deep-embedded. The object language is
a sorted linear λ-calculus: `content` is LINEAR (no contraction, no
weakening — a theorem in `Dcare.Linearity`, not a discipline we assume),
while the knower type is cartesian, its duplication licensed by the
coalgebra `gen` rather than primitive. `later` is the guarded modality ▷;
`stream` is the guarded stream whose ONLY introduction rule consumes a
`▷ stream` (`Dcare.Typing.cons`).
-/

namespace Dcare

/-- Object types. -/
inductive Ty where
  | content : Ty
  | knower : Ty
  | knowledge : Ty
  | value : Ty
  | stream : Ty
  | trace : Ty
  | later : Ty → Ty
  | tensor : Ty → Ty → Ty
  | arrow : Ty → Ty → Ty
  | unit : Ty
  deriving Repr, DecidableEq

/-- A type is *linear* when hypotheses of that type may be neither
duplicated nor discarded. Content is linear; the knower is not (it is the
coalgebraic source of the linear stream, not itself a linear resource).

S2 REVIEW FLAG → AFFIRMED (review, 2026-11-08): `arrow` is linear if
either side is — if the input is a generator, the function must be linear
in it, or it duplicates the generator. -/
def Ty.isLinear : Ty → Bool
  | .content | .trace | .stream => true
  | .later a => a.isLinear
  | .tensor a b => a.isLinear || b.isLinear
  | .arrow a b => a.isLinear || b.isLinear
  | _ => false

/-- de Bruijn terms. -/
inductive Term where
  | var (i : Nat)
  | lam (a : Ty) (body : Term)
  | app (fn arg : Term)
  | pair (l r : Term)
  | lete (t : Term) (body : Term)   -- linear tensor elimination: uses BOTH components
  | unit
  | next (t : Term)       -- A → ▷A
  | fix (body : Term)     -- (▷A → A) → A ; unfolding costs one tick
  | cons (hd tl : Term)   -- content → ▷stream → stream (guarded)
  | nil                   -- empty trace
  | snoc (t u : Term)     -- trace → content → trace
  | gen                   -- c : K → content ⊗ K   (the coalgebra)
  | red                   -- r : stream → A        (the reducer)
  | obj                   -- f : stream → value    — typed ONLY on the guarded stream
  | terminate             -- consume the generator : K → trace (a FINITE trace)
  deriving Repr

/-- Raise every free variable with index ≥ `d` by one (weakening
renaming, used by the structural rule `Typed.weak`). -/
def Term.liftAt (d : Nat) : Term → Term
  | .var i => if d ≤ i then .var (i + 1) else .var i
  | .lam a b => .lam a (liftAt (d + 1) b)
  | .app f x => .app (liftAt d f) (liftAt d x)
  | .pair l r => .pair (liftAt d l) (liftAt d r)
  | .lete t b => .lete (liftAt d t) (liftAt (d + 2) b)
  | .unit => .unit
  | .next t => .next (liftAt d t)
  | .fix t => .fix (liftAt d t)
  | .cons h t => .cons (liftAt d h) (liftAt d t)
  | .nil => .nil
  | .snoc t u => .snoc (liftAt d t) (liftAt d u)
  | .gen => .gen
  | .red => .red
  | .obj => .obj
  | .terminate => .terminate

/-- Contract the two most recent hypotheses in a term: index `d + 1`
becomes `d`, higher indices decrement (used by `Typed.contr`). -/
def Term.mergeAt (d : Nat) : Term → Term
  | .var i =>
      if i = d + 1 then .var d
      else if d + 1 < i then .var (i - 1)
      else .var i
  | .lam a b => .lam a (mergeAt (d + 1) b)
  | .app f x => .app (mergeAt d f) (mergeAt d x)
  | .pair l r => .pair (mergeAt d l) (mergeAt d r)
  | .lete t b => .lete (mergeAt d t) (mergeAt (d + 2) b)
  | .unit => .unit
  | .next t => .next (mergeAt d t)
  | .fix t => .fix (mergeAt d t)
  | .cons h t => .cons (mergeAt d h) (mergeAt d t)
  | .nil => .nil
  | .snoc t u => .snoc (mergeAt d t) (mergeAt d u)
  | .gen => .gen
  | .red => .red
  | .obj => .obj
  | .terminate => .terminate

end Dcare
