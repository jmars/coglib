import Dcare.Policy
import Dcare.Parametricity

/-!
# Adversaries — the non-vacuity proofs

Each public theorem ships with a countermodel witness: a variant system in
which the theorem's conclusion FAILS, proving the theorem carves something.

ADVERSARY 1 (contraction ⇒ divergence, S6): in the variant judgment with
unrestricted contraction for `content`, a closed term exists that consumes
the generator and enters the unguarded loop — the DPDR manifold, not a
type error. `TypedC` is defined in S6; until then the meta-level half
below (`adversary_spin_diverges`) fixes the divergence vocabulary.

ADVERSARY 2 (monomorphic protection, S7): a policy family protecting only
some knowers violates the parametric coupling — the gnostic failure mode.
-/


namespace Dcare

/-- Meta-level half of Adversary 1: a stopping run, under the UNGUARDED
dynamics, reaches a state that recurs at every horizon — it ticks forever
and emits nothing. The guard (`Dcare.Policy.Step`, where `stopped` is
terminal) is exactly what prevents this. -/
theorem adversary_spin_diverges {K : Type} (g : Generator K) (p : Policy) (k : K)
    (hstop : p [] = Decision.stop) :
    DivergesU g p (Config.running k []) := by
  refine ⟨2, Config.looped, ?_, ?_⟩
  · -- two unguarded steps: running → stopped → looped
    refine ⟨Config.stopped, StepU.halt hstop, ?_⟩
    exact ⟨Config.looped, StepU.spin, rfl⟩
  · intro n
    induction n with
    | zero => rfl
    | succ m ih => exact ⟨Config.looped, StepU.spinLoop, ih⟩

/-- ADVERSARY 2 (substrate blindness, S7): without the coupling
hypothesis the free theorem FAILS — one policy protects under one
generator and not under another. Witness: a policy that stops iff it has
just seen content `mk 1`, run against an always-`mk 0` generator
(protects) and a `mk 1`-emitting generator (fails). Protection claims
that ignore the substrate are unsound — the gnostic failure mode,
relational form. -/

private def pblind : Policy := fun hist =>
  if hist = [Content.mk 1] then Decision.stop else Decision.continue

private def gzero : Generator PUnit := ⟨fun _ => (Content.mk 0, PUnit.unit)⟩

private def gone : Generator PUnit := ⟨fun _ => (Content.mk 1, PUnit.unit)⟩

private theorem pblind_cont_nil : pblind [] = Decision.continue := by
  unfold pblind
  rw [if_neg (by intro h; contradiction)]

private theorem pblind_stop_one : pblind [Content.mk 1] = Decision.stop := by
  unfold pblind
  rw [if_pos rfl]

/-- On the all-`mk 0` substrate, the blind policy never stops: its stop
history `[mk 1]` never occurs. -/
private theorem gzero_protected : Protected gzero pblind PUnit.unit := by
  have key : ∀ (m : Nat) (hist : List Content), (∀ c, c ∈ hist → c = Content.mk 0) →
      (runAux gzero pblind hist PUnit.unit m).isSome = true := by
    intro m
    induction m with
    | zero =>
        intro hist hinv
        have hcont : pblind hist = Decision.continue := by
          unfold pblind
          rw [if_neg (by
            intro he
            have hmem : Content.mk 1 ∈ hist := by rw [he]; exact List.Mem.head _
            have := hinv (Content.mk 1) hmem
            injection this with hnat; exact absurd hnat (by decide))]
        rw [runAux, if_neg (by
          intro hs
          rw [hcont] at hs
          exact Decision.noConfusion hs)]
        rfl
    | succ m ih =>
        intro hist hinv
        have hcont : pblind hist = Decision.continue := by
          unfold pblind
          rw [if_neg (by
            intro he
            have hmem : Content.mk 1 ∈ hist := by rw [he]; exact List.Mem.head _
            have := hinv (Content.mk 1) hmem
            injection this with hnat; exact absurd hnat (by decide))]
        rw [runAux, if_neg (by
          intro hs
          rw [hcont] at hs
          exact Decision.noConfusion hs)]
        refine ih (hist ++ [Content.mk 0]) ?_
        intro c hc
        cases List.mem_append.mp hc with
        | inl h1 => exact hinv c h1
        | inr h2 =>
            cases h2 with
            | head => rfl
            | tail _ hrest => exact (List.not_mem_nil hrest).elim
  exact fun n => key n [] (fun c hc => (List.not_mem_nil hc).elim)

/-- On the `mk 1`-emitting substrate, the blind policy stops at the
second interval: protection does not transfer across substrates. -/
private theorem gone_not_protected : ¬ Protected gone pblind PUnit.unit := by
  intro hinf
  have h1 : run gone pblind PUnit.unit 1 = none := by
    show runAux gone pblind [] PUnit.unit 1 = none
    rw [runAux, if_neg (by
      rw [pblind_cont_nil]
      intro hs
      exact Decision.noConfusion hs)]
    show (if pblind ([] ++ [Content.mk 1]) = Decision.stop then none
          else some (gone.step PUnit.unit).1) = none
    rw [if_pos (by show pblind [Content.mk 1] = Decision.stop; exact pblind_stop_one)]
  have h2 := hinf 1
  rw [h1] at h2
  exact Bool.noConfusion h2

theorem adversary_blind_transfer :
    ∃ (K₁ K₂ : Type) (g₁ : Generator K₁) (g₂ : Generator K₂) (p : Policy)
      (k₁ : K₁) (k₂ : K₂),
      Protected g₁ p k₁ ∧ ¬ Protected g₂ p k₂ :=
  ⟨PUnit, PUnit, gzero, gone, pblind, PUnit.unit, PUnit.unit,
    gzero_protected, gone_not_protected⟩

end Dcare
