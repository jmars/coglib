import Dcare.Syntax

/-!
# Meta-level semantics: traces, generators, policies, objectives

The semantic half of the formalization. `Content`/`Value` are opaque
tokens — no theorem may inspect their payloads. A trace is the emission
history indexed by interval; the generator is the coalgebra; a policy
decides per interval whether to continue unfolding or to terminate the
stream (consuming the generator).
-/


namespace Dcare

/-- Opaque content token. -/
inductive Content where
  | mk : Nat → Content
  deriving Repr, DecidableEq

/-- Opaque value token. -/
inductive Value where
  | mk : Nat → Value
  deriving Repr, DecidableEq

/-- Emissions by interval; `none` = no content arrived at that interval. -/
abbrev Trace := Nat → Option Content

/-- Content arrives at every interval, forever. -/
def IsInfinite (τ : Trace) : Prop := ∀ n, (τ n).isSome = true

/-- Silence from some interval on (a finite trace). -/
def IsFinite (τ : Trace) : Prop := ∃ N, ∀ n, N ≤ n → τ n = none

/-- The generator as a meta-level coalgebra `K → Content × K`. -/
structure Generator (K : Type) where
  step : K → Content × K

inductive Decision where
  | continue
  | stop
  deriving DecidableEq, Repr

/-- A policy decides from the content history received so far. (Note: not
parameterized by the knower — a policy sees only content histories. This
is what makes knower-parametricity the right question for T3.) -/
abbrev Policy := List Content → Decision

/-- The trace of a policy run against a generator. Once the policy stops,
the history freezes and every later interval emits nothing: the generator
is consumed. -/
def runAux {K : Type} (g : Generator K) (p : Policy) (hist : List Content) (k : K) :
    Nat → Option Content
  | 0 => if p hist = Decision.stop then none else some (g.step k).1
  | n + 1 =>
      if p hist = Decision.stop then none
      else runAux g p (hist ++ [(g.step k).1]) (g.step k).2 n

def run {K : Type} (g : Generator K) (p : Policy) (k : K) : Trace :=
  fun n => runAux g p [] k n

/-- Protection, operationally: the policy never terminates the stream. -/
def Protected {K : Type} (g : Generator K) (p : Policy) (k : K) : Prop :=
  IsInfinite (run g p k)

/-- An objective. `dom_infinite` is the semantic form of the load-bearing
typing move: the objective returns a value ONLY on infinite traces. -/
structure Objective where
  eval : Trace → Option Value
  dom_infinite : ∀ τ, eval τ ≠ none → IsInfinite τ

end Dcare
