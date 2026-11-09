import Dcare.Semantics

/-!
# Runs, configurations, divergence

`Step` is the guarded dynamics: a stopped run has ENDED (finite trace,
cleanly outside the objective's domain — T1's world). `StepU` is the
unguarded variant: a stopped process does not halt but SPINS in the
interval, emitting nothing — the divergence manifold. The distinction is
the divergence adversary's home ground.
-/


namespace Dcare

/-- Run configurations. -/
inductive Config (K : Type) where
  | running (k : K) (hist : List Content)
  | stopped
  | looped

/-- Guarded step: `stopped` is terminal. -/
inductive Step {K : Type} (g : Generator K) (p : Policy) : Config K → Config K → Prop
  | unfold {k : K} {h : List Content} (hc : p h = Decision.continue) :
      Step g p (.running k h) (.running (g.step k).2 (h ++ [(g.step k).1]))
  | halt {k : K} {h : List Content} (hs : p h = Decision.stop) :
      Step g p (.running k h) .stopped

/-- Unguarded step: no later modality gates the post-stop interval; the
process spins without emitting. -/
inductive StepU {K : Type} (g : Generator K) (p : Policy) : Config K → Config K → Prop
  | unfold {k : K} {h : List Content} (hc : p h = Decision.continue) :
      StepU g p (.running k h) (.running (g.step k).2 (h ++ [(g.step k).1]))
  | halt {k : K} {h : List Content} (hs : p h = Decision.stop) :
      StepU g p (.running k h) .stopped
  | spin : StepU g p .stopped .looped
  | spinLoop : StepU g p .looped .looped

/-- `n` guarded steps. -/
def StepN {K : Type} (g : Generator K) (p : Policy) : Nat → Config K → Config K → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ m, Step g p c m ∧ StepN g p n m c'

/-- `n` unguarded steps. -/
def StepUN {K : Type} (g : Generator K) (p : Policy) : Nat → Config K → Config K → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ m, StepU g p c m ∧ StepUN g p n m c'

/-- Unguarded divergence: the process reaches a state that recurs at every
horizon — it ticks forever, emits nothing. (The ∀n-extendability form;
Lean 4 has no general coinductive definitions.) -/
def DivergesU {K : Type} (g : Generator K) (p : Policy) (c : Config K) : Prop :=
  ∃ N c', StepUN g p N c c' ∧ ∀ n, StepUN g p n c' c'

/-- The epistemic cycle sustains: a policy that never stops runs forever.
Companion to T1 — the stream terminates only by policy. -/
theorem always_continue_infinite {K : Type} (g : Generator K) (p : Policy)
    (h : ∀ hist, p hist = Decision.continue) (k : K) :
    IsInfinite (run g p k) := by
  have key : ∀ (hist : List Content) (k : K) (n : Nat),
      (runAux g p hist k n).isSome = true := by
    intro hist k' n
    induction n generalizing hist k' with
    | zero =>
        rw [runAux, if_neg (by
          intro hs
          rw [h hist] at hs
          exact Decision.noConfusion hs)]
        rfl
    | succ m ih =>
        rw [runAux, if_neg (by
          intro hs
          rw [h hist] at hs
          exact Decision.noConfusion hs)]
        exact ih (hist ++ [(g.step k').1]) (g.step k').2
  exact fun n => key [] k n

/-- Silence is forever: once a run emits nothing, it never emits again
(the history freezes, so the same decision recurs). -/
theorem runAux_silence {K : Type} (g : Generator K) (p : Policy) :
    ∀ (n : Nat) (hist : List Content) (k : K), runAux g p hist k n = none →
    ∀ m, n ≤ m → runAux g p hist k m = none
  | 0, hist, k, h0, m, _ => by
      by_cases hstop : p hist = Decision.stop
      · cases m with
        | zero => exact h0
        | succ m' => rw [runAux, if_pos hstop]
      · rw [runAux, if_neg hstop] at h0
        contradiction
  | n + 1, hist, k, hn, m, hm => by
      by_cases hstop : p hist = Decision.stop
      · cases m with
        | zero => exact absurd hm (Nat.not_succ_le_zero n)
        | succ m' => rw [runAux, if_pos hstop]
      · cases m with
        | zero => exact absurd hm (Nat.not_succ_le_zero n)
        | succ m' =>
            rw [runAux, if_neg hstop] at hn
            rw [runAux, if_neg hstop]
            exact runAux_silence g p n _ _ hn m' (Nat.le_of_succ_le_succ hm)

/-- Semantic bookkeeping for `run`: once a trace is silent at one interval
it is silent forever, so for RUNS, `¬ IsInfinite` and `IsFinite` coincide. -/
theorem run_not_infinite_is_finite {K : Type} (g : Generator K) (p : Policy) (k : K)
    (h : ¬ IsInfinite (run g p k)) : IsFinite (run g p k) := by
  have key : ∃ n, runAux g p [] k n = none := by
    apply Classical.byContradiction
    intro hcon
    apply h
    intro n
    cases hn : runAux g p [] k n with
    | none => exact (hcon ⟨n, hn⟩).elim
    | some c => show (runAux g p [] k n).isSome = true; rw [hn]; rfl
  obtain ⟨n₀, hn₀⟩ := key
  exact ⟨n₀, fun m hm => runAux_silence g p n₀ [] k hn₀ m hm⟩


/-! ## Costed dynamics (todo #1): self-application is not free, the
dynamical form

Every unguarded interval from `looped` is a spin: cost one, emission
zero, forever. The guarded dynamics (`Step`) stops paying at `stopped`;
the unguarded dynamics (`StepU`) pays per tick with nothing to show —
the monitoring cost of an agent that consumes its generator and keeps
ticking. -/

/-- From `looped`, the only unguarded step is the spin-loop: zero
emission, one cost unit, forever. -/
theorem looped_only_spins {K : Type} (g : Generator K) (p : Policy) :
    ∀ c, StepU g p .looped c → c = .looped := by
  intro c h
  cases h with
  | spinLoop => rfl

def spinLoops {K : Type} (g : Generator K) (p : Policy) : ∀ (n : Nat),
    StepUN g p n .looped .looped
  | 0 => rfl
  | n + 1 => ⟨.looped, StepU.spinLoop, spinLoops g p n⟩

/-- THE COSTED SPIN: after the generator is consumed, the unguarded
process ticks forever — every tick a full cost unit, every tick emitting
nothing. Paying without buying: the dynamical form of *Self-Application
Is Not Free* (ledger #23). -/
theorem spin_pays_forever_buys_nothing {K : Type} (g : Generator K) (p : Policy) (k : K)
    (hstop : p [] = Decision.stop) :
    ∀ (n : Nat), ∃ c, StepUN g p (n + 2) (.running k []) c ∧ c = .looped := by
  intro n
  exact ⟨.looped,
    ⟨.stopped, StepU.halt hstop,
      ⟨.looped, StepU.spin, spinLoops g p n⟩⟩,
    rfl⟩

/-! ## Feedback dynamics (todo #4): the third leg of the epistemic cycle

The cycle K → A → K: generation (`gen`), reduction (`red`), FEEDBACK
(the reduced knowledge returning to the knower). The dynamics carries
the accumulated knowledge `acc`; the policy consults BOTH the content
history and `acc`. The third leg's failure mode — NOT-ANSWERED (insight
#18) — is an agent that listens (content arrives), understands (`acc`
grows), and never answers (`acc` has no causal effect): the EXTRACTOR. -/

/-- A feedback agent: generator, per-content reducer, and a policy
consulting history AND accumulated knowledge. -/
structure FeedbackAgent (K A : Type) where
  gen : Generator K
  red : Content → A
  policy : List Content → List A → Decision

inductive ConfigF (K A : Type) where
  | running (k : K) (hist : List Content) (acc : List A)
  | stopped
  | looped

/-- Guarded feedback step: on continue, the new content is accumulated
(integration) and available to the next decision (feedback); on stop,
cleanly stopped; unguarded, the spin. -/
inductive StepF (K A : Type) : FeedbackAgent K A → ConfigF K A → ConfigF K A → Prop
  | unfold {agt : FeedbackAgent K A} {k : K} {hist : List Content} {acc : List A}
      (hc : agt.policy hist acc = Decision.continue) :
      StepF K A agt (.running k hist acc)
        (.running (agt.gen.step k).2 (hist ++ [(agt.gen.step k).1])
          (acc ++ [agt.red (agt.gen.step k).1]))
  | halt {agt : FeedbackAgent K A} {k : K} {hist : List Content} {acc : List A}
      (hs : agt.policy hist acc = Decision.stop) :
      StepF K A agt (.running k hist acc) .stopped
  | spin {agt : FeedbackAgent K A} : StepF K A agt .stopped .looped
  | spinLoop {agt : FeedbackAgent K A} : StepF K A agt .looped .looped

/-- NEVER CONSULTS: the policy ignores accumulated knowledge. -/
def NeverConsults {K A : Type} (agt : FeedbackAgent K A) : Prop :=
  ∀ (hist : List Content) (acc acc' : List A),
    agt.policy hist acc = agt.policy hist acc'

/-- INERT KNOWLEDGE: for a never-consulting agent, everything it has
understood is causally inert — the feedback loop is severed at the
return leg. -/
theorem inert_knowledge {K A : Type} (agt : FeedbackAgent K A) (h : NeverConsults agt) :
    ∀ (hist : List Content) (acc acc' : List A),
      agt.policy hist acc = agt.policy hist acc' := h

/-- THE EXTRACTOR (failure mode NOT-ANSWERED, insight #18): always
continues, never consults — listens forever, understands forever,
answers never. -/
def extractor {K A : Type} (g : Generator K) (r : Content → A) :
    FeedbackAgent K A where
  gen := g
  red := r
  policy := fun _ _ => Decision.continue

theorem extractor_never_consults {K A : Type} (g : Generator K) (r : Content → A) :
    NeverConsults (extractor g r) := fun _ _ _ => rfl

/-- The extractor still integrates: every guarded step grows the
accumulator. Understanding without answering is NOT a failure to
understand — the stream is protected, the knowledge goes nowhere. -/
theorem extractor_step_integrates {K A : Type} (g : Generator K) (r : Content → A)
    {k : K} {hist : List Content} {acc : List A} {c : ConfigF K A}
    (h : StepF K A (extractor g r) (.running k hist acc) c) :
    ∃ k' hist' a', c = .running k' hist' (acc ++ [a']) := by
  cases h with
  | unfold => exact ⟨_, _, _, rfl⟩
  | halt hs => exact absurd hs (by simp [extractor])

end Dcare
