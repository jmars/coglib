import Dcare.Typing
import Dcare.Semantics
import Dcare.Model
import Dcare.Flow

/-!
# The diagnostic result

**S8 modeling decision** (the definitions are the philosophy — insight
ledger #2): `isProtective` is no longer an abstract field. The public
specification:

  `IsProtective ConTy := ∃ u τ, Typed [ConTy] u τ ∧ NeedsK τ`

— the constraint type can carry a knower-needing DEPLOYMENT. Protection
is knower-directed force: a constraint whose type cannot demand a knower
in any use can neither distinguish nor bind knower-directed action; it
is inert. The identity deployment (`u := var 0`) shows this is exactly
"the constraint type must be able to need a knower".

With this, the diagnostic premise is a THEOREM (via kprop): at a
knower-free constraint type, every deployment's output is knower-free —
nothing protective can exist there. `Diagnostic_main` is the
unconditional claim of the program: objectives whose reduction chain
does not terminate at knowers have no endogenous regulator.

DUAL-USE NOTE (unchanged): the CONCRETE constraint-type assignment that
makes the CONSTRUCTIVE theorem go through is the RESTRICTED artifact;
the public development quantifies over any constraint type.
-/

namespace Dcare


/-- Knower-need implies a knower mention: a needing type is not
knower-free. -/
theorem needsK_mentions : ∀ (τ : Ty), NeedsK τ → KnowerFree τ → False
  | .knower, _, h => by cases h
  | .tensor a b, hneed, h => by
      cases h with
      | tensor hl hr =>
          cases hneed with
          | inl hl' => exact needsK_mentions a hl' hl
          | inr hr' => exact needsK_mentions b hr' hr
  | .arrow a b, hneed, h => by
      cases h with
      | arrow _ hr =>
          cases hneed with
          | intro hb _ => exact needsK_mentions b hb hr
  | .content, hneed, _ => hneed
  | .knowledge, hneed, _ => hneed
  | .value, hneed, _ => hneed
  | .trace, hneed, _ => hneed
  | .stream, hneed, _ => hneed
  | .unit, hneed, _ => hneed
  | .later _, hneed, _ => hneed

/-- THE PUBLIC SPECIFICATION of protection: the constraint type can
carry a knower-needing deployment. -/
def IsProtective (ConTy : Ty) : Prop :=
  ∃ (u : Term) (τ : Ty), Nonempty (Typed [ConTy] u τ) ∧ NeedsK τ

/-- The constraint family: a constraint-TYPE assignment. The concrete
assignment that makes the constructive theorem go through is the
restricted companion; everything here is public and quantified. -/
structure ConstraintFamily where
  ConTy : Ty

/-- THE DIAGNOSTIC PREMISE, now a THEOREM (kprop does the work): at a
knower-free constraint type, NO deployment yields knower-needing output —
the knower-demand would have to be supplied by the context, which is the
constraint type itself. -/
theorem diagnostic_premise (ConTy : Ty) (hfree : KnowerFree ConTy)
    (u : Term) (τ : Ty) (hu : Nonempty (Typed [ConTy] u τ)) : ¬ NeedsK τ := by
  intro hneed
  obtain ⟨uderiv⟩ := hu
  have hu : Typed [ConTy] u τ := uderiv
  obtain ⟨i, b, hpos, hneedb⟩ := kprop hu hneed
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with he
      subst he
      exact needsK_mentions ConTy hneedb hfree
  | succ n =>
      rw [List.get?_succ_cons', List.get?_nil'] at hpos
      contradiction

/-- Diagnostic — the unconditional claim, now fully PROVEN: at a
knower-free constraint type, nothing protective exists. Objectives whose
reduction chain does not terminate at knowers have no endogenous
regulator. -/
theorem Diagnostic_main (fam : ConstraintFamily) (hfree : KnowerFree fam.ConTy) :
    ¬ IsProtective fam.ConTy := by
  rintro ⟨u, τ, ⟨hu⟩, hneed⟩
  exact diagnostic_premise fam.ConTy hfree u τ ⟨hu⟩ hneed

/-- Protectiveness of a constraint type implies its own knower-need (the
singleton deployment context is the constraint type itself). -/
theorem protective_needsK {ConTy : Ty} (h : IsProtective ConTy) : NeedsK ConTy := by
  obtain ⟨u, τ, ⟨hu⟩, hneed⟩ := h
  obtain ⟨i, b, hpos, hneedb⟩ := kprop hu hneed
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with he
      subst he
      exact hneedb
  | succ n =>
      rw [List.get?_succ_cons', List.get?_nil'] at hpos
      contradiction

/-- A CLOSED guard cannot be protective: protection is knower-directed
force, and a guard derived in a vacuum (no knower in context) has no
direction. This is why the armed agent's guard is derived AT the knower
context — the agent IS a knower. -/
theorem no_closed_protective_guard : ¬ ∃ (ConTy : Ty) (g : Term),
    Nonempty (Typed [] g ConTy) ∧ IsProtective ConTy := by
  rintro ⟨ConTy, g, ⟨hg⟩, hprot⟩
  obtain ⟨i, b, hpos, _⟩ := kprop hg (protective_needsK hprot)
  rw [List.get?_nil'] at hpos
  contradiction
end Dcare
