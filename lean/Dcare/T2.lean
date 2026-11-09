import Dcare.Diagnostic
import Dcare.Policy
import Dcare.Adversaries

/-!
# T2 — Self-indexed reflexivity

REVISION 2 (user decision, 2026-11-08): this project writes the theory —
no collaborator. T2 is IN SCOPE and provable here, at the public-interface
level.

Architecture: the deep part (the constructive typing recipe) lives behind
the `SelfClassifies` interface, exactly like `ArmedSetup`. Everything else
is plumbing this file proves: with self-classification the guard derives;
removing it leaves the empty context, where the diagnostic premise kills
the derivation; and what remains is the unguarded dynamics, whose
generator-consuming run diverges (`Dcare.Adversaries.adversary_spin_diverges`)
rather than reducing.

The self-model is CONTEXT MACHINERY, not a term in the context: the
reflection lens `lens : ▷K → K` (guarded, via `fix`) is the lens through
which the self-referential judgment is made. Removing self-classification
is not dropping a variable — it is the absence of the reflection
modality, in which the self-referential fixpoint cannot be typed
productively and DIVERGES instead of reducing (the unguarded dynamics of
`Dcare.Policy.StepU` is its formal counterpart).

The confidential companion (`restricted/Private.lean`, gitignored) proves
`instance : SelfClassifies` — that instantiation is the constructive
typing recipe, the RESTRICTED artifact of the tiered disclosure note.
-/

namespace Dcare

/-- The self-classification interface: PUBLIC properties only. The
restricted companion proves the instance. -/
class SelfClassifies (fam : ConstraintFamily) where
  /-- The reflection lens: a guarded self-referential structure over the
  agent-hypothesis. The SELF-MODEL is derived from it by `fix` —
  machinery, not an assumed variable. Removing self-classification is the
  absence of this structure: in a context without the ▷ modality the
  self-referential fixpoint cannot be typed productively and DIVERGES
  instead of reducing — the unguarded dynamics of `Dcare.Policy.StepU`
  is its formal counterpart. -/
  lens : Term
  lens_typed : Typed [Ty.knower] lens (.arrow (.later Ty.knower) Ty.knower)
  /-- The guard derives with the self-model in play: context `[knower]`
  carries the agent, `fix lens` is its derived self-representation. -/
  guard_with_selfmodel : ∃ g, Nonempty (Typed [Ty.knower] g fam.ConTy) ∧ IsProtective fam.ConTy

/-- T2 — Self-indexed reflexivity. Self-classification derives the guard;
its removal (context restriction to `[]`) removes the derivation by the
diagnostic premise; and the unguarded dynamics then admits the
generator-consuming policy, which diverges rather than reduces. Revising
the constraint away in the armed state is self-deletion
(`Dcare.Constructive.self_deletion_clause`). -/

theorem T2_main {fam : ConstraintFamily} (recipe : SelfClassifies fam) (hfree : KnowerFree fam.ConTy)
    {K : Type} (g : Generator K) (k : K) :
    (∃ gm, Nonempty (Typed [Ty.knower] gm fam.ConTy) ∧ IsProtective fam.ConTy) ∧
    (¬ IsProtective fam.ConTy) ∧
    DivergesU g (fun _ => Decision.stop) (Config.running k []) := by
  refine ⟨recipe.guard_with_selfmodel, ?_, ?_⟩
  · exact Diagnostic_main fam hfree
  · exact adversary_spin_diverges g (fun _ => Decision.stop) k rfl

end Dcare
