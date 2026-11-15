/-
# Minimal reproducer: both conservation laws, decided in one file

Run with `lean minimal-reproducer.lean` — no imports, no Mathlib, no
build. One file, ~430 lines.

## Reading guide: this is intuitionistic linear ND, plus two deltas

If you know ILL's natural deduction, you know the shape of every rule
here — six are literally standard, and the only non-standard content in
the whole calculus is the two discipline deltas at the end of this
guide. The map:

  var / lam / app      — identity, ⇒I, ⇒E            (standard)
  pair / lete         — ⊗I / ⊗E                      (standard, with
                         ONE twist: lete binds the components in
                         REVERSED order, b :: a :: Γ₂ — this localized
                         exchange is load-bearing, see below)
  unit                — 1I (at the empty context)    (standard)
  next / fix          — the guard ▷: next is the co-unit-shaped
                         A → ▷A, fix is the guarded recursor with a
                         context gate (delta 2)
  contr / weak        — contraction and weakening, GATED on the head
                         type being non-linear (delta 2)
  gen / red / cons    — three closed constants (axioms):
                         gen : knower → content ⊗ knower   (MINTS content)
                         red : stream → knowledge
                         cons : content → ▷stream → stream

DELTA 1 — ORDERED SPLITS. app/pair/lete/cons split the context in
order (Γ ++ Δ = E): no exchange. The only definable reorder is the
pair/lete round trip above — a swap of the two components of a tensor
the calculus just introduced. That localized exchange is the engine of
the counterexample below.

DELTA 2 — SORT-KEYED LINEARITY (no modality). Linearity is a predicate
on base types (content/stream linear; knower/knowledge/unit not), not a
`!`. contr/weak fire only at non-linear heads, and fix fires only at
all-non-linear contexts. There is no exponential to introduce or
eliminate — the permission travels with the type.

Everything else is standard. The two deltas are the object of study.

## What is here (all kernel-checked)

  1. VANISHING IS REFUTED — an explicit `[content] ⊢ unit` derivation:
     content spent as the `cons` head of the guarded cycle's stream,
     the REVERSED lete binding swaps the knower pocket in front, `red`
     reads the stream, and `weak` discards the resulting NON-LINEAR
     conduit for `unit`. The discard needs the conduit to be non-linear
     — a linear conduit would fail weak's gate.
  2. CONTRACTION IS PROVED — the monotone counting model: worlds = ℕ,
     content = {w ≥ 1}, knower = ∅, unit = ⊤ (the reading the
     counterexample forces — a sound model must accept what is
     derivable), tensor adds, arrow residuals. Monotonicity makes the
     weak arm free; soundness holds for all 13 rules with NO
     hypothesis; content ⊗ content needs budget 2 where [content]
     costs 1.
  3. THE MODEL ACCEPTS THE COUNTEREXAMPLE — required, and the whole
     story: one interpretation choice, one law each way.

The full development (962 theorems, 17 rules, traces/values, zero
sorries, gate-enforced) is the dcare tree; this file is the core of
both decisions.
-/

namespace Repro

/-! ## 1. The calculus -/

inductive Ty where
  | content | knower | knowledge | stream
  | later : Ty → Ty
  | tensor : Ty → Ty → Ty
  | arrow : Ty → Ty → Ty
  | unit

/-- Linearity is keyed to the base types: content/stream are linear;
knower/knowledge/unit are not; later preserves; tensor/arrow take the or. -/
def Ty.isLinear : Ty → Bool
  | .content | .stream => true
  | .later a => a.isLinear
  | .tensor a b => a.isLinear || b.isLinear
  | .arrow a b => a.isLinear || b.isLinear
  | _ => false

/-- `fix` fires only at all-non-linear contexts — the ▷ guard's price. -/
def AllNonLinear : List Ty → Prop :=
  fun Γ => ∀ b ∈ Γ, b.isLinear = false

inductive Term where
  | var (i : Nat)
  | lam (a : Ty) (body : Term)
  | app (fn arg : Term)
  | pair (l r : Term)
  | lete (t : Term) (body : Term)   -- tensor elimination; body at REVERSED components
  | unit
  | next (t : Term)                 -- A → ▷A
  | fix (body : Term)               -- (▷A → A) → A
  | cons (hd tl : Term)             -- content → ▷stream → stream
  | gen                             -- knower → content ⊗ knower (MINTS content)
  | red                             -- stream → knowledge

/-- Weakening renaming for the structural rule. -/
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
  | .gen => .gen
  | .red => .red

/-- Contraction renaming. -/
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
  | .gen => .gen
  | .red => .red

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
  | fix {Γ : List Ty} {a : Ty} {body : Term} (hΓ : AllNonLinear Γ)
      (h : Typed Γ body (.arrow (.later a) a)) :
      Typed Γ (.fix body) a
  | cons {E Γ Δ : List Ty} {hd tl : Term}
      (hc : Typed Γ hd .content) (ht : Typed Δ tl (.later .stream))
      (hs : Γ ++ Δ = E) :
      Typed E (.cons hd tl) .stream
  | gen : Typed [] .gen (.arrow .knower (.tensor .content .knower))
  | red : Typed [] .red (.arrow .stream .knowledge)
  | contr {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} (hk : k.isLinear = false)
      (h : Typed (k :: k :: Γ) (Term.mergeAt 0 t) τ) :
      Typed (k :: Γ) t τ
  | weak {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} (hk : k.isLinear = false)
      (h : Typed Γ t τ) :
      Typed (k :: Γ) (Term.liftAt 0 t) τ

/-! ## 2. Vanishing is REFUTED — the counterexample, piece by piece -/

/-- Fresh content from the generator; the knower half weakened away. -/
def extract : Term := .lete (.app .gen (.var 0)) (Term.liftAt 0 (.var 0))

def extractTyped : Typed [Ty.knower] extract Ty.content :=
  Typed.lete (Γ₁ := [Ty.knower]) (Γ₂ := [])
    (Typed.app (Γ := []) (Δ := [Ty.knower]) Typed.gen Typed.var rfl)
    (Typed.weak (Γ := [Ty.content]) (t := Term.var 0) rfl Typed.var)
    rfl

/-- One lap of the cycle: fresh content consumed into the guarded stream. -/
def cycle : Term := .cons extract (.var 0)

def cycleTyped : Typed [Ty.knower, Ty.later Ty.stream] cycle Ty.stream :=
  Typed.cons (Γ := [Ty.knower]) (Δ := [Ty.later Ty.stream])
    extractTyped Typed.var rfl

/-- THE INTERNAL EXCHANGE: `pair` + `lete` round trip swaps the two top
hypotheses — `lete`'s body context is `b :: a :: Γ₂`, the tensor's
components REVERSED. -/
def flip2 : Term := .lete (.pair (.var 0) (.var 0)) cycle

def flip2Typed : Typed [Ty.later Ty.stream, Ty.knower] flip2 Ty.stream :=
  Typed.lete (Γ₁ := [Ty.later Ty.stream, Ty.knower]) (Γ₂ := [])
    (Typed.pair (Γ := [Ty.later Ty.stream]) (Δ := [Ty.knower])
      Typed.var Typed.var rfl)
    cycleTyped
    rfl

/-- The guarded fixpoint: a knower sustains an infinite stream. -/
theorem knower_ctx_nonlinear : AllNonLinear [Ty.knower] := by
  intro b hb
  have : b = Ty.knower := by simpa using hb
  subst this
  rfl

def fixCycle : Term := .fix (.lam (Ty.later Ty.stream) flip2)

def fixCycleTyped : Typed [Ty.knower] fixCycle Ty.stream :=
  Typed.fix knower_ctx_nonlinear (Typed.lam flip2Typed)

/-- The content token spent as the cycle's stream head. -/
def streamCK : Term := .cons (.var 0) (.next fixCycle)

def streamCKTyped : Typed [Ty.content, Ty.knower] streamCK Ty.stream :=
  Typed.cons (Γ := [Ty.content]) (Δ := [Ty.knower])
    Typed.var (Typed.next fixCycleTyped) rfl

/-- The swap moves the knower pocket in front of the content. -/
def streamKC : Term := .lete (.pair (.var 0) (.var 0)) streamCK

def streamKCTyped : Typed [Ty.knower, Ty.content] streamKC Ty.stream :=
  Typed.lete (Γ₁ := [Ty.knower, Ty.content]) (Γ₂ := [])
    (Typed.pair (Γ := [Ty.knower]) (Δ := [Ty.content])
      Typed.var Typed.var rfl)
    streamCKTyped
    rfl

/-- `red` reads the pocket's stream. -/
def knowledgeKC : Term := .app .red streamKC

def knowledgeKCTyped : Typed [Ty.knower, Ty.content] knowledgeKC Ty.knowledge :=
  Typed.app (Γ := []) (Δ := [Ty.knower, Ty.content]) Typed.red streamKCTyped rfl

/-- THE CONDUIT — this non-linear type at `[content]` is the load-bearing
inhabitant: it cannot fire here (a knower argument is unreachable), but it
CAN be discarded by `weak`, because it is non-linear. -/
def conduit : Term := .lam Ty.knower knowledgeKC

def conduitTyped : Typed [Ty.content] conduit (Ty.arrow Ty.knower Ty.knowledge) :=
  Typed.lam knowledgeKCTyped

theorem conduit_nonlinear :
    (Ty.arrow Ty.knower Ty.knowledge).isLinear = false := by decide

/-- **THE COUNTEREXAMPLE**: `[content] ⊢ unit`. The outer `weak` discards
the conduit — the discard is the last step, and it needs the conduit to be
NON-LINEAR (a linear type would fail `weak`'s gate). -/
def counterexample : Term :=
  .app (.lam (Ty.arrow Ty.knower Ty.knowledge) (Term.liftAt 0 Term.unit))
    conduit

def counterexampleTyped : Typed [Ty.content] counterexample Ty.unit :=
  Typed.app (Γ := []) (Δ := [Ty.content])
    (Typed.lam (Typed.weak (k := Ty.arrow Ty.knower Ty.knowledge)
      (t := Term.unit) (τ := Ty.unit) conduit_nonlinear Typed.unit))
    conduitTyped rfl

theorem vanishing_refuted :
    ¬ (∀ (t : Term), Typed [Ty.content] t Ty.unit → False) := by
  intro H
  exact H counterexample counterexampleTyped

/-! ## 3. Contraction is PROVED — the monotone counting model

Worlds are ℕ; `content = {w | 1 ≤ w}`; `knower = ∅`; the other bases ⊤
(INCLUDING `unit` — the reading the counterexample forces); tensor adds;
arrow is the residual. Monotonicity is what makes the `weak` arm free. -/

def uInterp : Ty → Nat → Prop
  | .content, w => 1 ≤ w
  | .knower, _ => False
  | .knowledge, _ => True
  | .stream, _ => True
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
      obtain ⟨m', n', hG, hD, _⟩ := uCtx_append hrest
      exact ⟨m + m', n', ⟨m, m', ha, hG, rfl⟩, hD, by omega⟩

/-- The arithmetic that IS the theorem: `content ⊗ content` needs budget 2. -/
theorem uInterp_CxC (w : Nat) :
    uInterp (Ty.tensor Ty.content Ty.content) w ↔ 2 ≤ w := by
  constructor
  · rintro ⟨m, n, hm, hn, _⟩
    have : 1 ≤ m := hm
    have : 1 ≤ n := hn
    omega
  · intro h
    obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact ⟨1, 1 + k, Nat.le_refl 1, Nat.le_add_right 1 k, by omega⟩

/-- MONOTONICITY — structural, no hypothesis. False for the `{0}`-unit
reading exactly at `unit`; that failure is the only reason a soundness
proof would need a side condition on `weak` heads. -/
theorem uMono : ∀ (τ : Ty) {w w' : Nat}, w ≤ w' → uInterp τ w → uInterp τ w'
  | .content, w, w', hle, h => Nat.le_trans h hle
  | .knower, _, _, _, h => h.elim
  | .knowledge, _, _, _, _ => True.intro
  | .stream, _, _, _, _ => True.intro
  | .later _, _, _, _, _ => True.intro
  | .tensor a b, w, w', hle, h => by
      obtain ⟨m, n, ha, hb, he⟩ := h
      obtain ⟨k, rfl⟩ := Nat.le.dest hle
      exact ⟨m, n + k, ha, uMono b (Nat.le_add_right n k) hb, by omega⟩
  | .arrow a b, w, w', hle, h => by
      intro n hn
      exact uMono b (by omega) (h n hn)
  | .unit, _, _, _, _ => True.intro

/-- At a NON-LINEAR type the interpretation is empty or everything (the
`⊤`-unit reading collapses the middle case). This is LOAD-BEARING for
the `contr` arm: duplication needs the head funded at `0` (or nowhere). -/
theorem uTwoWay (τ : Ty) (hlin : τ.isLinear = false) :
    (∀ w, ¬ uInterp τ w) ∨ (∀ w, uInterp τ w) := by
  cases τ with
  | content | stream => exact Bool.noConfusion hlin
  | knower => exact Or.inl (fun _ hw => hw)
  | knowledge | unit => exact Or.inr (fun _ => True.intro)
  | later _ => exact Or.inr (fun _ => True.intro)
  | tensor a b =>
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using hlin)
      rcases uTwoWay a h'.1 with haE | haT <;>
        rcases uTwoWay b h'.2 with hbE | hbT
      · exact Or.inl (fun w hw => by
          obtain ⟨m, _, hm, _, _⟩ := hw; exact haE m hm)
      · exact Or.inl (fun w hw => by
          obtain ⟨m, _, hm, _, _⟩ := hw; exact haE m hm)
      · exact Or.inl (fun w hw => by
          obtain ⟨_, n, _, hn, _⟩ := hw; exact hbE n hn)
      · exact Or.inr (fun w => ⟨w, 0, haT w, hbT 0, by omega⟩)
  | arrow a b =>
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using hlin)
      rcases uTwoWay a h'.1 with haE | haT <;>
        rcases uTwoWay b h'.2 with hbE | hbT
      · exact Or.inr (fun _ _ hn => False.elim (haE _ hn))
      · exact Or.inr (fun _ _ hn => False.elim (haE _ hn))
      · exact Or.inl (fun w H => hbE w (H 0 (haT 0)))
      · exact Or.inr (fun _ n _ => hbT _)

/-- SOUNDNESS — all thirteen rules, NO hypothesis. The `weak` arm is one
monotonicity lift; the `contr` arm is `uTwoWay` (duplication needs the
head funded at `0` — one budget cannot fund two copies, so this is
load-bearing, not a leftover); the `fix` arm is the ⊤ guard (`later` is
⊤, so the crossed arrow at `w` gives the payload at `w + 0`). -/
theorem uSound : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (_h : Typed Γ t τ),
    ∀ w, uCtx Γ w → uInterp τ w
  | _, _, _, Typed.var, w, hw => by
      obtain ⟨m, n, hm, hn, he⟩ := uCtx_cons hw
      have : n = 0 := uCtx_nil hn
      rw [show w = m by omega]
      exact hm
  | _, _, _, @Typed.lam Γ a b body h, w, hw => by
      intro n hn
      exact uSound h (w + n) ⟨n, w, hn, hw, by omega⟩
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, w, hw => by
      obtain ⟨m, n, hΓ, hΔ, he⟩ :=
        uCtx_append (Γ := Γ) (Δ := Δ) (w := w) (by simpa only [← hs] using hw)
      have h3 : uInterp b (m + n) := uSound hf m hΓ n (uSound ha n hΔ)
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
      rw [show mb + (ma + n) = (ma + mb) + n from by omega] at hres
      rw [he, hme]
      exact hres
  | _, _, _, Typed.unit, _, _ => True.intro
  | _, _, _, @Typed.next _ _ _ h, _, _ => True.intro
  | _, _, _, @Typed.fix Γ a body hΓ h, w, hw => by
      have h1 := uSound h w hw
      have h2 := h1 0 True.intro
      simpa using h2
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, _, _ => True.intro
  | _, _, _, Typed.gen, _, _ => fun _ hn => False.elim hn
  | _, _, _, Typed.red, _, _ => fun _ _ => True.intro
  | _, _, _, @Typed.contr Γ k t τ hk h, w, hw => by
      -- The head must be funded at 0 (uTwoWay): one budget cannot fund
      -- the duplicated copy.
      obtain ⟨m, n, hkm, hΓn, he⟩ := uCtx_cons hw
      rcases uTwoWay k hk with hE | hT
      · exact False.elim (hE m hkm)
      · exact uSound h w ⟨0, w, hT 0, ⟨m, n, hkm, hΓn, he⟩, (Nat.zero_add w).symm⟩
  | _, _, _, @Typed.weak Γ k t τ hk h, w, hw => by
      obtain ⟨m, n, _, hΓn, he⟩ := uCtx_cons hw
      rw [he]
      exact uMono τ (Nat.le_add_left n m) (uSound h n hΓn)

/-- **CONTRACTION, PROVED**: `[content] ⊬ content ⊗ content`. -/
theorem no_contraction (t : Term)
    (h : Typed [Ty.content] t (Ty.tensor Ty.content Ty.content)) : False := by
  have hI : uInterp (Ty.tensor Ty.content Ty.content) 1 :=
    uSound h 1 ⟨1, 0, Nat.le_refl 1, rfl, by omega⟩
  have := (uInterp_CxC 1).mp hI
  omega

/-! ## 4. The model accepts the counterexample (it must) -/

/-- The same model, run on the counterexample: `unit = ⊤`, so the
derivation is validated — this model can never refute vanishing, which is
the impossibility shape: one interpretation choice buys exactly one law. -/
theorem model_accepts_counterexample : uInterp Ty.unit 1 :=
  uSound counterexampleTyped 1 ⟨1, 0, Nat.le_refl 1, rfl, by omega⟩

end Repro

#print axioms Repro.vanishing_refuted
#print axioms Repro.no_contraction
#print axioms Repro.uSound
#print axioms Repro.uMono
#print axioms Repro.model_accepts_counterexample
