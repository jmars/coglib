import Dcare.SC

/-!
# The Guarded Kernel — the restricted calculus (the ArmedSetup)

THE SAFE KERNEL. The official specification of the restricted calculus:
the unrestricted calculus minus the discard, plus the knower-synthesis
ban. The two classical laws are ABSOLUTE theorems here:

  no_vanishing_restricted   : Typed [content] t unit          → NoWeak h → False
  no_contraction_restricted : Typed [content] t (content⊗content) → NoWeak h → False

THE ENGINE is the in-tree counting-model soundness (`sound_of_zeroWeak`,
SC.lean): sound for 16 of 17 constructors with no hypothesis, and for
`weak` under exactly `ZeroW k`. A `NoWeak` tree has NO weak nodes, so its
weak-head obligation is vacuous — the kernel's theorems are the model's
verdict at the no-weak grain, with `fix` INCLUDED (the guard `▷` reads as
`⊤` in the model, so the crossed arrow carries no side condition) and
`gen`/`contr`/`cons`/`snoc`/all constants INSIDE the theorem. This is
strictly the deepest unconditional form of both laws in the tree.

THE ARMEDSETUP, as specified:

- NO WEAK (the discard ban): a derivation cannot drop a resource. This
  alone carries both laws (the theorems below), and it alone excludes the
  counterexample — whose LAST step is a `weak` (`counterexample_not_noweak`).
- NO FAKE KNOWERS (`NoKnowerSynthesis`): no `lam`/`lete` binder may
  demand knower supply — the compiler rejects `λ(k : knower). …` pockets,
  which is the shape the lete/pair swap feeds. At the no-weak grain this
  ban is NOT needed for the two laws (a stronger statement than the
  specification asked for); it is carried because it excludes the
  counterexample's conduit by a SECOND, independent route
  (`counterexample_conduit_no_synthesis`).
- THE GUARD (▷): already in the rule set — `fix` fires only at
  all-non-linear contexts (`AllNonLinear`), which `content`'s linearity
  enforces (`no_fix_at_content`: no fix at any content-bearing frame).
  The kernel changes nothing here; it inherits the guard.

NON-VACUITY: the kernel still admits real derivations — the archive
(`[content] ⊢ trace` — reception without reduction is LEGAL; the spent
token is recorded, not discarded), the closed `unit`, the constants.
What it forbids is exactly the discard.

Axioms: everything here is within `[propext, Quot.sound]` (inherited
from `sound_of_zeroWeak`); no `sorryAx` anywhere in the restricted path.
-/

namespace Dcare.Kernel.Guarded

open SCExtractor SCProvenance SCProvenance2 SCProvenance3

/-! ## The discard ban, and the vacuous-head bridge -/

/-- A `NoWeak` tree lists no weak heads: the model's weak-arm obligation
is vacuous. (17 arms; the `weak` arm is `False` by the definition.) -/
theorem weakHeads_nil_of_noweak : ∀ {Γ : List Ty} {t : Term} {τ : Ty}
    (h : Typed Γ t τ), NoWeakFrag.NoWeak h → weakHeads h = []
  | _, _, _, Typed.var, _ => rfl
  | _, _, _, @Typed.lam _ _ _ _ h, hN => weakHeads_nil_of_noweak h hN
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha hs, hN => by
      obtain ⟨h1, h2⟩ := hN
      show weakHeads hf ++ weakHeads ha = []
      rw [weakHeads_nil_of_noweak hf h1, weakHeads_nil_of_noweak ha h2]
      rfl
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr hs, hN => by
      obtain ⟨h1, h2⟩ := hN
      show weakHeads hl ++ weakHeads hr = []
      rw [weakHeads_nil_of_noweak hl h1, weakHeads_nil_of_noweak hr h2]
      rfl
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb hs, hN => by
      obtain ⟨h1, h2⟩ := hN
      show weakHeads ht ++ weakHeads hb = []
      rw [weakHeads_nil_of_noweak ht h1, weakHeads_nil_of_noweak hb h2]
      rfl
  | _, _, _, Typed.unit, _ => rfl
  | _, _, _, @Typed.next _ _ _ h, hN => weakHeads_nil_of_noweak h hN
  | _, _, _, @Typed.fix _ _ _ _ h, hN => weakHeads_nil_of_noweak h hN
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht hs, hN => by
      obtain ⟨h1, h2⟩ := hN
      show weakHeads hc ++ weakHeads ht = []
      rw [weakHeads_nil_of_noweak hc h1, weakHeads_nil_of_noweak ht h2]
      rfl
  | _, _, _, Typed.nil, _ => rfl
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu hs, hN => by
      obtain ⟨h1, h2⟩ := hN
      show weakHeads ht ++ weakHeads hu = []
      rw [weakHeads_nil_of_noweak ht h1, weakHeads_nil_of_noweak hu h2]
      rfl
  | _, _, _, Typed.gen, _ => rfl
  | _, _, _, Typed.red, _ => rfl
  | _, _, _, Typed.obj, _ => rfl
  | _, _, _, Typed.terminate, _ => rfl
  | _, _, _, @Typed.contr _ _ _ _ _ h, hN => weakHeads_nil_of_noweak h hN
  | _, _, _, @Typed.weak _ _ _ _ _ _, hN => by
      exact absurd hN (fun h => h)

/-! ## THE TWO LAWS -/

/-- UNITARITY (no vanishing), restricted: in the Guarded kernel, content
cannot reach `unit`. Fix included, gen/contr/cons/snoc/constants inside;
only the discard is banned. -/
theorem no_vanishing_restricted {t : Term} (h : Typed [Ty.content] t Ty.unit)
    (hN : NoWeakFrag.NoWeak h) : False :=
  no_vanishing_of_zeroWeak h (by
    intro k hk
    rw [weakHeads_nil_of_noweak h hN] at hk
    exact absurd hk (by simp))

/-- NO-CLONING, restricted: in the Guarded kernel, one content cannot become
two. The arithmetic: the frame costs `1`, but `content ⊗ content` needs
`m + n` with both `≥ 1`. -/
theorem no_contraction_restricted {t : Term}
    (h : Typed [Ty.content] t (Ty.tensor Ty.content Ty.content))
    (hN : NoWeakFrag.NoWeak h) : False := by
  have hW : ∀ k, k ∈ weakHeads h → ZeroW k := by
    intro k hk
    rw [weakHeads_nil_of_noweak h hN] at hk
    exact absurd hk (by simp)
  have hw : wCtx [Ty.content] 1 := ⟨1, 0, Nat.le_refl 1, rfl, by omega⟩
  have hI := sound_of_zeroWeak h hW 1 hw
  obtain ⟨m, n, hm, hn, he⟩ := hI
  have h1 : 1 ≤ m := hm
  have h2 : 1 ≤ n := hn
  omega

/-! ## The ArmedSetup -/

/-- NO FAKE KNOWERS: no `lam`/`lete` binder may demand knower supply.
This is the compiler-side ban on `λ(k : knower). …` pockets — the shape
the lete/pair swap feeds (`binderTys` is the round-2 position-origin
traversal: every weak head is a context position or one of these). -/
def NoKnowerSynthesis {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ) : Prop :=
  ∀ k, k ∈ binderTys h → ¬ NeedsK k

/-- THE ARMEDSETUP: the discard ban plus the knower-synthesis ban. -/
def ArmedSetup {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ) : Prop :=
  NoWeakFrag.NoWeak h ∧ NoKnowerSynthesis h

/-- UNITARITY under the full ArmedSetup. (The synthesis ban is not needed
at the no-weak grain — a STRONGER statement than the specification asked
for — but it rides as the kernel's second, independent line of defence.) -/
theorem no_vanishing_armed {t : Term} (h : Typed [Ty.content] t Ty.unit)
    (hA : ArmedSetup h) : False :=
  no_vanishing_restricted h hA.1

/-- NO-CLONING under the full ArmedSetup. -/
theorem no_contraction_armed {t : Term}
    (h : Typed [Ty.content] t (Ty.tensor Ty.content Ty.content))
    (hA : ArmedSetup h) : False :=
  no_contraction_restricted h hA.1

/-- The knower-synthesis ban EXCLUDES the counterexample's conduit: the
witness binds a knower (`λ(k : knower). …`), and `knower` demands knower
supply. -/
theorem counterexample_conduit_no_synthesis :
    ¬ NoKnowerSynthesis arrowKnowerKnowledge := by
  intro hB
  unfold NoKnowerSynthesis at hB
  exact hB Ty.knower (List.mem_cons.mpr (Or.inl rfl)) True.intro

/-- THE KERNEL FORBIDS THE COUNTEREXAMPLE, twice over: the witness carries a
`weak` node (its LAST step — the discard), so it is not a `NoWeak`
derivation. -/
theorem counterexample_not_noweak :
    ¬ NoWeakFrag.NoWeak (carrierAKK arrowKnowerKnowledge) := by
  intro hN
  have h := hN
  unfold NoWeakFrag.NoWeak carrierAKK arrowKnowerKnowledge at h
  exact h.1

/-- … and the full ArmedSetup rejects it by both routes at once. -/
theorem counterexample_not_armed :
    ¬ ArmedSetup (carrierAKK arrowKnowerKnowledge) :=
  fun hA => counterexample_not_noweak hA.1

/-! ## The guard, inherited -/

/-- The ▷ guard is IN the rule set: `fix` fires only at all-non-linear
contexts, so no fix node can sit at a content-bearing frame. The kernel
inherits this unchanged. -/
theorem guard_inherited (Γ Δ : List Ty) : ¬ AllNonLinear (Γ ++ Ty.content :: Δ) :=
  not_allNonLinear_frame Γ Δ

/-! ## Non-vacuity: what the kernel still admits -/

/-- The ARCHIVE is legal: `[content] ⊢ trace` (reception without
reduction; the spent token is recorded, not discarded). -/
def archive : Typed [Ty.content] (Term.snoc Term.nil (Term.var 0)) Ty.trace :=
  Typed.snoc (Γ := []) (Δ := [Ty.content]) Typed.nil Typed.var rfl

theorem archive_noweak : NoWeakFrag.NoWeak archive := ⟨trivial, trivial⟩

/-- The closed `unit` is legal (there is no content to discard). -/
theorem unit_at_nil_noweak :
    NoWeakFrag.NoWeak (Typed.unit : Typed [] Term.unit Ty.unit) := trivial

end Dcare.Kernel.Guarded
