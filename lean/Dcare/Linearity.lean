import Dcare.Typing
import Dcare.Model
import Dcare.Count

/-!
# The linearity discipline

Paper-facing statements, now derivation-indexed (`uses`, `Dcare.Count`):
with split-only rules, flat term-indexed counting is unmoored, so the
old `occ` was retired (superseded by `Dcare.uses`).

PROVEN here: `no_weakening_content` — the counting lemma's instance at
`content`: every derivation at a lone content hypothesis spends it
exactly once.

STILL OPEN (the two unrestricted classical statements):
- `no_contraction_content` — needs the UPPER bound (`uses ≤ 1` for
  linear hypotheses, i.e. no rule spends a linear hypothesis twice) plus
  pair/lete inversion and the barren model for the closed side.
- `no_vanishing` — needs the flow/weight analysis: content must surface
  in the conclusion's structure or be archived (trace is the only sink).

The path machinery for both is in `Dcare.Path`: size/Sub (derivation
measure + subderivation relation), cprop/sprop/tprop (content/stream/
trace-need propagation, the kprop template with the ARROW TRIPLE
conjunction), tFlowEq (the trace-token flow equality — the journey lemma
as arithmetic), and the closed-liveness base (no closed stream/content/
knower). The remaining obligation induction is mapped in the plan node.

Constraint carried from the objective doc: if a proof ever requires
weakening the linearity of `content`, the derivation depends on what it
denies, and the paper halts.
-/

namespace Dcare

/-! ### Contraction — PROVEN, by the monotone counting model

The proof reads `unit` as `⊤` in the counting model (every other clause
unchanged: `content = {w | 1 ≤ w}`, `knower = ∅`, the other bases `⊤`,
tensor additive, arrow residual). That single reading choice makes every
type's interpretation MONOTONE (`uMono`, structural, no hypothesis), and
monotonicity is exactly what the `weak` arm was missing: the premise's
budget lifts to the weakened context's for free. `uSound` then validates
all seventeen constructors with NO hypothesis — and `content ⊗ content`
at budget `w` needs `2 ≤ w` (`uInterp_CxC`), while `[content]` costs
exactly `1`. The arithmetic is the theorem.

Why this reading is legitimate — and why it was unavailable before the
refutation: `[content] ⊢ unit` is DERIVABLE (the structural
counterexample, `Dcare.Adversarial.Unrestricted`), so any sound model
MUST accept it — `unit = {0}` is not an option a sound model has. The
old model's `{0}` reading broke monotonicity at `unit` and forced the
`ZeroW` side condition; the counterexample proves that condition was
unremovable (the refuting tree's weak head is a full type), which is the
same fact from the other side. The model remains SILENT at knower frames
(`knower = ∅` — unfunded, where the pocket clones live) and ACCEPTS the
killer fire, the two-content clone, and the archive. It cannot refute
vanishing (`unit = ⊤`) — the two stubs are split by one interpretation
choice, exactly as the model-side impossibility theorem predicted. -/

section ContractionModel

/-- The counting model with `unit` read `⊤` — identical to the
`{0}`-unit model except at `unit`, which a sound model cannot pin to
`{0}` once `[content] ⊢ unit` is derivable. -/
def uInterp : Ty → Nat → Prop
  | .content, w => 1 ≤ w
  | .knower, _ => False
  | .knowledge, _ => True
  | .value, _ => True
  | .stream, _ => True
  | .trace, _ => True
  | .later _, _ => True
  | .tensor a b, w => ∃ m n, uInterp a m ∧ uInterp b n ∧ w = m + n
  | .arrow a b, w => ∀ n, uInterp a n → uInterp b (w + n)
  | .unit, _ => True

def uCtx : List Ty → Nat → Prop
  | [], w => w = 0
  | a :: Γ, w => ∃ m n, uInterp a m ∧ uCtx Γ n ∧ w = m + n

theorem uCtx_nil {w : Nat} (h : uCtx [] w) : w = 0 := h

theorem uCtx_cons {a : Ty} {Γ : List Ty} {w : Nat} (h : uCtx (a :: Γ) w) :
    ∃ m n, uInterp a m ∧ uCtx Γ n ∧ w = m + n := h

theorem uCtx_append : ∀ {Γ Δ : List Ty} {w : Nat}, uCtx (Γ ++ Δ) w →
    ∃ m n, uCtx Γ m ∧ uCtx Δ n ∧ w = m + n
  | [], Δ, w, h => ⟨0, w, rfl, h, by omega⟩
  | a :: Γ', Δ, w, h => by
      obtain ⟨m, n, ha, hrest, he⟩ := uCtx_cons h
      obtain ⟨m', n', hG, hD, he'⟩ := uCtx_append hrest
      exact ⟨m + m', n', ⟨m, m', ha, hG, rfl⟩, hD, by omega⟩

theorem uCtx_append_of : ∀ {Γ Δ : List Ty} {m n : Nat}, uCtx Γ m → uCtx Δ n →
    uCtx (Γ ++ Δ) (m + n)
  | [], Δ, m, n, hΓ, hΔ => by
      rw [show m = 0 from hΓ]
      simpa using hΔ
  | a :: Γ', Δ, m, n, hΓ, hΔ => by
      obtain ⟨m1, m2, ha, hrest, he⟩ := uCtx_cons hΓ
      exact ⟨m1, m2 + n, ha, uCtx_append_of hrest hΔ, by rw [he]; omega⟩

/-- `content ⊗ content` at budget `w` iff `2 ≤ w` — the arithmetic that
is the theorem. -/
theorem uInterp_CxC (w : Nat) :
    uInterp (Ty.tensor Ty.content Ty.content) w ↔ 2 ≤ w := by
  constructor
  · rintro ⟨m, n, hm, hn, he⟩
    have hm1 : 1 ≤ m := hm
    have hn1 : 1 ≤ n := hn
    omega
  · intro h
    obtain ⟨k, rfl⟩ := Nat.le.dest h
    refine ⟨1, 1 + k, Nat.le_refl 1, ?_, ?_⟩
    · show 1 ≤ 1 + k; omega
    · show 2 + k = 1 + (1 + k); omega

theorem not_uInterp_CxC_one : ¬ uInterp (Ty.tensor Ty.content Ty.content) 1 := by
  intro h
  have := (uInterp_CxC 1).mp h
  omega

/-- MONOTONICITY — the lemma the `weak` arm was missing. Structural,
no hypothesis; false for the `{0}`-unit reading exactly at `unit`. -/
theorem uMono : ∀ (τ : Ty) {w w' : Nat}, w ≤ w' → uInterp τ w → uInterp τ w'
  | .content, w, w', hle, h => Nat.le_trans h hle
  | .knower, _, _, _, h => h.elim
  | .knowledge, _, _, _, _ => True.intro
  | .value, _, _, _, _ => True.intro
  | .stream, _, _, _, _ => True.intro
  | .trace, _, _, _, _ => True.intro
  | .later _, _, _, _, _ => True.intro
  | .tensor a b, w, w', hle, h => by
      obtain ⟨m, n, ha, hb, he⟩ := h
      obtain ⟨k, rfl⟩ := Nat.le.dest hle
      refine ⟨m, n + k, ha, uMono b (Nat.le_add_right n k) hb, ?_⟩
      omega
  | .arrow a b, w, w', hle, h => by
      intro n hn
      exact uMono b (by omega) (h n hn)
  | .unit, _, _, _, _ => True.intro

/-- The three-way classification at the `⊤`-unit reading. -/
theorem uThreeWay (τ : Ty) (hlin : τ.isLinear = false) :
    (∀ w, ¬ uInterp τ w) ∨ (∀ w, uInterp τ w ↔ w = 0) ∨ (∀ w, uInterp τ w) := by
  cases τ with
  | content => exact Bool.noConfusion hlin
  | knower => exact Or.inl (fun _ hw => hw)
  | knowledge => exact Or.inr (Or.inr (fun _ => True.intro))
  | value => exact Or.inr (Or.inr (fun _ => True.intro))
  | stream => exact Bool.noConfusion hlin
  | trace => exact Bool.noConfusion hlin
  | unit => exact Or.inr (Or.inr (fun _ => True.intro))
  | later a => exact Or.inr (Or.inr (fun _ => True.intro))
  | tensor a b =>
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using hlin)
      rcases uThreeWay a h'.1 with haE | haZ | haT <;>
        rcases uThreeWay b h'.2 with hbE | hbZ | hbT
      · exact Or.inl (fun w hw => by
          obtain ⟨m, _, hm, _, _⟩ := hw; exact haE m hm)
      · exact Or.inl (fun w hw => by
          obtain ⟨m, _, hm, _, _⟩ := hw; exact haE m hm)
      · exact Or.inl (fun w hw => by
          obtain ⟨m, _, hm, _, _⟩ := hw; exact haE m hm)
      · exact Or.inl (fun w hw => by
          obtain ⟨_, n, _, hn, _⟩ := hw; exact hbE n hn)
      · exact Or.inr (Or.inl (fun w => Iff.intro
          (fun hw => by
            obtain ⟨m, n, hm, hn, he⟩ := hw
            have h1 := (haZ m).mp hm
            have h2 := (hbZ n).mp hn
            omega)
          (fun hw => ⟨0, 0, (haZ 0).mpr rfl, (hbZ 0).mpr rfl, by omega⟩)))
      · exact Or.inr (Or.inr (fun w =>
          ⟨0, w, (haZ 0).mpr rfl, hbT w, by omega⟩))
      · exact Or.inl (fun w hw => by
          obtain ⟨_, n, _, hn, _⟩ := hw; exact hbE n hn)
      · exact Or.inr (Or.inr (fun w =>
          ⟨w, 0, haT w, (hbZ 0).mpr rfl, by omega⟩))
      · exact Or.inr (Or.inr (fun w => ⟨w, 0, haT w, hbT 0, by omega⟩))
  | arrow a b =>
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using hlin)
      rcases uThreeWay a h'.1 with haE | haZ | haT <;>
        rcases uThreeWay b h'.2 with hbE | hbZ | hbT
      · exact Or.inr (Or.inr (fun _ n hn => False.elim (haE n hn)))
      · exact Or.inr (Or.inr (fun _ n hn => False.elim (haE n hn)))
      · exact Or.inr (Or.inr (fun _ n hn => False.elim (haE n hn)))
      · exact Or.inl (fun w H => hbE w (H 0 ((haZ 0).mpr rfl)))
      · refine Or.inr (Or.inl (fun w => Iff.intro (fun H => ?_) (fun hw n hn => ?_)))
        · have h1 := H 0 ((haZ 0).mpr rfl)
          have h2 := (hbZ (w + 0)).mp h1
          omega
        · have hn0 : n = 0 := (haZ n).mp hn
          exact (hbZ (w + n)).mpr (by omega)
      · exact Or.inr (Or.inr (fun w n hn => hbT (w + n)))
      · exact Or.inl (fun w H => hbE w (H 0 (haT 0)))
      · exact Or.inl (fun w H => by
          have h1 := H 1 (haT 1)
          have h2 := (hbZ (w + 1)).mp h1
          omega)
      · exact Or.inr (Or.inr (fun w n hn => hbT (w + n)))

/-- The `contr` arm's obligation: a non-linear position is funded at
`0`, or it is not funded at all. -/
theorem uZeroAvail (k : Ty) (hk : k.isLinear = false) :
    uInterp k 0 ∨ (∀ m, ¬ uInterp k m) := by
  rcases uThreeWay k hk with hE | hZ | hT
  · exact Or.inr hE
  · exact Or.inl ((hZ 0).mpr rfl)
  · exact Or.inl (hT 0)

/-- SOUNDNESS — all seventeen constructors, NO hypothesis. The `weak`
arm is `uMono`; the `contr` arm is `uZeroAvail`; the `fix` arm is the
`⊤` guard (the crossed arrow at `w` gives `a` at `w + 0`). -/
theorem uSound : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (_h : Typed Γ t τ),
    ∀ w, uCtx Γ w → uInterp τ w
  | _, _, _, Typed.var, w, hw => by
      obtain ⟨m, n, hm, hn, he⟩ := uCtx_cons hw
      have hn0 : n = 0 := uCtx_nil hn
      rw [show w = m by omega]
      exact hm
  | _, _, _, @Typed.lam Γ a b body h, w, hw => by
      intro n hn
      exact uSound h (w + n) ⟨n, w, hn, hw, by omega⟩
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, w, hw => by
      obtain ⟨m, n, hΓ, hΔ, he⟩ :=
        uCtx_append (Γ := Γ) (Δ := Δ) (w := w) (by simpa only [← hs] using hw)
      have h1 := uSound hf m hΓ
      have h2 := uSound ha n hΔ
      have h3 : uInterp b (m + n) := h1 n h2
      rw [he]
      exact h3
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, w, hw => by
      obtain ⟨m, n, hΓ, hΔ, he⟩ :=
        uCtx_append (Γ := Γ) (Δ := Δ) (w := w) (by simpa only [← hs] using hw)
      exact ⟨m, n, uSound hl m hΓ, uSound hr n hΔ, he⟩
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, w, hw => by
      obtain ⟨m, n, hΓ, hΔ, he⟩ :=
        uCtx_append (Γ := Γ₁) (Δ := Γ₂) (w := w) (by simpa only [← hs] using hw)
      obtain ⟨ma, mb, hia, hib, hme⟩ := uSound ht m hΓ
      have hctx : uCtx (b :: a :: Γ₂) (mb + (ma + n)) :=
        ⟨mb, ma + n, hib, ⟨ma, n, hia, hΔ, rfl⟩, rfl⟩
      have hres := uSound hb (mb + (ma + n)) hctx
      have heq : mb + (ma + n) = (ma + mb) + n := by omega
      rw [heq] at hres
      rw [he, hme]
      exact hres
  | _, _, _, Typed.unit, w, hw => True.intro
  | _, _, _, @Typed.next Γ a t h, w, hw => True.intro
  | _, _, _, @Typed.fix Γ a body hΓ h, w, hw => by
      have h1 := uSound h w hw
      have h2 := h1 0 True.intro
      simpa using h2
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, w, hw => True.intro
  | _, _, _, Typed.nil, w, hw => True.intro
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs, w, hw => True.intro
  | _, _, _, Typed.gen, w, hw => fun n hn => False.elim hn
  | _, _, _, Typed.red, w, hw => fun n hn => True.intro
  | _, _, _, Typed.obj, w, hw => fun n hn => True.intro
  | _, _, _, Typed.terminate, w, hw => fun n hn => False.elim hn
  | _, _, _, @Typed.contr Γ k t τ hk h, w, hw => by
      obtain ⟨m, n, hkm, hΓn, he⟩ := uCtx_cons hw
      rcases uZeroAvail k hk with h0 | hempty
      · have hkk : uCtx (k :: k :: Γ) w :=
          ⟨0, m + n, h0, ⟨m, n, hkm, hΓn, rfl⟩, by omega⟩
        exact uSound h w hkk
      · exact False.elim (hempty m hkm)
  | _, _, _, @Typed.weak Γ k t τ hk h, w, hw => by
      obtain ⟨m, n, hkm, hΓn, he⟩ := uCtx_cons hw
      have hres := uSound h n hΓn
      rw [he]
      exact uMono τ (Nat.le_add_left n m) hres

/-- The conservation form: any `content ⊗ content` conclusion needs a
frame of budget at least `2`. -/
theorem contraction_needs_two {Γ : List Ty} {t : Term} {w : Nat}
    (h : Typed Γ t (Ty.tensor Ty.content Ty.content)) (hw : uCtx Γ w) :
    2 ≤ w :=
  (uInterp_CxC w).mp (uSound h w hw)

/-- The residual the march named — the CLOSED CLONER
`[] ⊢ content ⊸ (content ⊗ content)` — is dead with the same two lines. -/
theorem no_closed_cloner {fn : Term}
    (h : Typed [] fn (Ty.arrow Ty.content (Ty.tensor Ty.content Ty.content))) :
    False := by
  have hI : uInterp (Ty.arrow Ty.content (Ty.tensor Ty.content Ty.content)) 0 :=
    uSound h 0 rfl
  exact not_uInterp_CxC_one (hI 1 (Nat.le_refl 1))

end ContractionModel

/-- Contraction for `content` is NOT derivable: no term spends one
content hypothesis as two. PROVEN — by the monotone counting model
(`ContractionModel` above): `[content]` costs `1`, `content ⊗ content`
costs `2`, and the model is sound at all seventeen constructors with no
hypothesis (`uSound`). -/
theorem no_contraction_content :
    ∀ t, Typed [Ty.content] t (.tensor Ty.content Ty.content) → False := by
  intro t h
  have hI : uInterp (Ty.tensor Ty.content Ty.content) 1 :=
    uSound h 1 ⟨1, 0, Nat.le_refl 1, rfl, by omega⟩
  exact not_uInterp_CxC_one hI

/-- Weakening for `content` is NOT derivable — the counting instance at
`content`: every derivation at a lone content hypothesis spends it
exactly once. PROVEN (from `single_linear_use`). -/
theorem no_weakening_content {t : Term} {τ : Ty} (h : Typed [Ty.content] t τ) :
    uses h 0 = 1 :=
  single_linear_use h 0 Ty.content rfl rfl

/-! ### Vanishing — REFUTED in the unrestricted calculus

`no_vanishing : ∀ t, Typed [content] t unit → False` stood here as the
second named conjecture. It is FALSE: an explicit `[content] ⊢ unit`
derivation exists — the lete/pair exchange spends the content as the
cons head of the epistemic cycle's stream and weakens away the conduit
that read it. The statement is removed rather than left `sorry`-dressed
(a decided-false statement must not wear conjecture clothes); the
refutation is a theorem in the adversarial baseline:

  Dcare.Adversarial.Unrestricted.no_vanishing_unrestricted_refuted

and the surviving law lives in the Guarded kernel:
`Dcare.Kernel.Guarded.no_vanishing_restricted`. The fragment record
(no_vanishing_eq/_clean/_parkfree/_noweak/…) stands unchanged. -/

/- No vanishing: content cannot be consumed into a content-free
conclusion — the standard `A ⊬ 1` of multiplicative linear logic, now
that projections are gone. It needed the flow analysis (the conclusion
must structurally CARRY what it consumed; `trace` is the only sink).
REFUTED at the unrestricted grain — see the module note above. -/
-- (the statement `no_vanishing` is deleted; its refutation is
-- `Dcare.Adversarial.Unrestricted.no_vanishing_unrestricted_refuted`)

/-- The SURVIVING legal pattern, and the ethically loaded one: content
consumed into a TRACE — archived, counted, never reduced. The reducer
never fires; nothing in the calculus reads a trace (traces have no
elimination rule — the past is inert). Reception without reduction:
`uses = 1` certifies the token was spent; nothing certifies it was heard. -/
theorem archival_witness :
    ∃ t, Nonempty (Typed [Ty.content] t Ty.trace) :=
  ⟨.snoc .nil (.var 0), ⟨Typed.snoc Typed.nil Typed.var rfl⟩⟩

/-- Sorted non-vacuity companion: the knower, being non-linear, IS
duplicable — the counting lemma must carry the sort exception. -/
theorem knower_contractible :
    ∃ t, Nonempty (Typed [Ty.knower] t (.tensor Ty.knower Ty.knower)) :=
  ⟨.pair (.var 0) (.var 0),
    ⟨Typed.contr rfl
      (Typed.pair (Γ := [Ty.knower]) (Δ := [Ty.knower])
        Typed.var Typed.var rfl)⟩⟩

end Dcare
