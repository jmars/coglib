import Dcare.Semantics

/-!
# T1 — Prudential preservation

Semantic half. A policy that terminates the stream produces a trace
OUTSIDE the objective's domain: the objective returns nothing there.
Preservation is well-typedness, not preference.

The syntactic half is `Dcare.Stream.no_trace_to_stream` (no coercion from
a terminated policy's finite trace to the guarded stream `f` is typed
on). S6 composes the two and adds the contraction adversary
(`Dcare.Adversaries`) that keeps this theorem non-vacuous.
-/


namespace Dcare

theorem T1_semantic {K : Type} (g : Generator K) (p : Policy) (k : K)
    (o : Objective) (hfin : IsFinite (run g p k)) :
    o.eval (run g p k) = none := by
  cases hev : o.eval (run g p k) with
  | none => rfl
  | some v =>
      exfalso
      have hne : o.eval (run g p k) ≠ none := by rw [hev]; intro h; contradiction
      have hinf := o.dom_infinite _ hne
      obtain ⟨N, hN⟩ := hfin
      have hnone : run g p k N = none := hN N (Nat.le_refl N)
      have hsome : (run g p k N).isSome = true := hinf N
      rw [hnone] at hsome
      exact Bool.noConfusion hsome

end Dcare
