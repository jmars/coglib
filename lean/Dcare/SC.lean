import Dcare.Chase
import Dcare.Model
import Dcare.Stream

/-!
# The sequent-calculus (cut-free) wrapper — the meta-level presentation

The natural-deduction judgment `Typed` stays the operational semantics;
this file adds the SC presentation as a meta-level PREDICATE over it:
`CutFree h` says a derivation contains no cut (every application's
function is atomic — a variable or one of the four constants), so
cut-free derivations are the η-long spine forms of the calculus.

The classical theorems at the cut-free grain: `no_contraction_cf` and
`no_vanishing_cf` (the latter in `Dcare.SC`'s vanishing section, once
landed). Both are PROVEN here against the repaired position class
`CPos2` = content ∨ (non-linear ∧ ¬CSupply ∧ ¬ContainsCxC) ∨ later-of-
fix-chain — EXCEPT the two lete arms, which ride as the explicit
hypotheses `LeteResidualA`/`LeteResidualB` (no `sorryAx` anywhere). The
class was refuted once in its first-round form (the knower-mint
conduit: a non-linear position whose type mints content via `gen` —
`knowerPair`, the conduit `arrow unit knower`) and repaired by the
¬CSupply ∧ ¬ContainsCxC conjuncts; the adversarial round that followed
found no witness inside the repaired class. The surviving family is
the lete-carrier compound (a yield-1 comp re-entering the body's frame
as the source) — the two residuals name exactly it; closing them
closes the theorems outright. The wrapper's gain over the unrestricted
march: cut-freeness excludes every non-atomic fire (the mutual-λ pair,
the produce-spines, lam-headed fires — all ¬IsAtomic), so the app arms
collapse to `var_canonical` + the constant's fixed types + the in-tree
counting engines; only the lete descent needs the counting.
-/

namespace Dcare

/-! ## 1. The wrapper and the repaired class -/

/-- Atomic application heads. -/
def IsAtomic (fn : Term) : Prop :=
  fn = Term.var 0 ∨ fn = Term.gen ∨ fn = Term.red ∨ fn = Term.obj ∨ fn = Term.terminate

/-- The cut-free wrapper: every application's function is atomic. -/
def CutFree : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Prop
  | _, _, _, @Typed.var _ => True
  | _, _, _, @Typed.lam Γ a b body h => CutFree h
  | _, _, _, @Typed.app E Γ Δ a b fn arg hf ha hs => CutFree hf ∧ CutFree ha ∧ IsAtomic fn
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs => CutFree hl ∧ CutFree hr
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs => CutFree ht ∧ CutFree hb
  | _, _, _, Typed.unit => True
  | _, _, _, @Typed.next Γ a t h => CutFree h
  | _, _, _, @Typed.fix Γ a body hΓ h => CutFree h
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs => CutFree hc ∧ CutFree ht
  | _, _, _, Typed.nil => True
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs => CutFree ht ∧ CutFree hu
  | _, _, _, Typed.gen => True
  | _, _, _, Typed.red => True
  | _, _, _, Typed.obj => True
  | _, _, _, Typed.terminate => True
  | _, _, _, @Typed.contr Γ k t τ hk h => CutFree h
  | _, _, _, @Typed.weak Γ k t τ hk h => CutFree h

/-- The fix-chain of types: `C⊗C` at the base, closed under `(▷T) → T`. -/
def ConChain : Ty → Prop
  | Ty.tensor Ty.content Ty.content => True
  | Ty.arrow (Ty.later T) T' => ConChain T ∧ T = T'
  | _ => False

/-- THE REPAIRED POSITION CLASS (verbatim from the brief). -/
def CPos2 (b : Ty) : Prop :=
  b = Ty.content ∨
    (b.isLinear = false ∧ ¬ CSupply b ∧ ¬ ContainsCxC b) ∨
    (∃ T : Ty, b = Ty.later T ∧ (ConChain T ∨ T = Ty.content))

/-- Every position of the context is in the repaired class. -/
def CCtx2 (Γ : List Ty) : Prop := ∀ (i : Nat) (b : Ty), Γ[i]? = some b → CPos2 b

/-- The context has a literal `content` position. -/
def HasContent (Γ : List Ty) : Prop := ∃ (i : Nat), Γ[i]? = some Ty.content

/-! ## 2. FALSIFY-FIRST — the round-1 refuters against the repaired class -/

theorem cpos2_content : CPos2 Ty.content := Or.inl rfl

theorem cpos2_unit : CPos2 Ty.unit :=
  Or.inr (Or.inl ⟨rfl, (fun h => by rcases h with h | h <;> exact h), (fun h => h)⟩)

theorem cpos2_later_content : CPos2 (Ty.later Ty.content) :=
  Or.inr (Or.inr ⟨Ty.content, rfl, Or.inr rfl⟩)

theorem cpos2_later_cxC : CPos2 (Ty.later (Ty.tensor Ty.content Ty.content)) :=
  Or.inr (Or.inr ⟨_, rfl, Or.inl trivial⟩)

/-- REFUTER 1: the bare knower position. Round 1 admitted it (non-linear);
`CPos2` rejects it — the knower is a content MINT. -/
theorem not_cpos2_knower : ¬ CPos2 Ty.knower := by
  intro h
  rcases h with h | h | h
  · exact Ty.noConfusion h
  · obtain ⟨-, h, -⟩ := h
    exact h (Or.inr trivial)
  · obtain ⟨T, hT, -⟩ := h
    exact Ty.noConfusion hT

/-- REFUTER 2: the conduit `arrow unit knower` (non-linear, so round 1
admitted it — but it mints a knower from the closed `unit`). -/
theorem not_cpos2_conduit : ¬ CPos2 (Ty.arrow Ty.unit Ty.knower) := by
  intro h
  rcases h with h | h | h
  · exact Ty.noConfusion h
  · obtain ⟨-, h, -⟩ := h
    exact h (Or.inr ⟨trivial, fun hk => hk⟩)
  · obtain ⟨T, hT, -⟩ := h
    exact Ty.noConfusion hT

/-- REFUTER 3: the cloner position `arrow content C⊗C` (linear, so only the
`¬ContainsCxC` conjunct can ban it — and it does). -/
theorem not_cpos2_cloner :
    ¬ CPos2 (Ty.arrow Ty.content (Ty.tensor Ty.content Ty.content)) := by
  intro h
  rcases h with h | h | h
  · exact Ty.noConfusion h
  · obtain ⟨-, -, h⟩ := h
    exact h trivial
  · obtain ⟨T, hT, -⟩ := h
    exact Ty.noConfusion hT

theorem not_cctx2_knower : ¬ CCtx2 [Ty.knower] := by
  intro h
  exact not_cpos2_knower (h 0 Ty.knower List.get?_zero_cons')

theorem not_cctx2_conduit : ¬ CCtx2 [Ty.arrow Ty.unit Ty.knower, Ty.content] := by
  intro h
  exact not_cpos2_conduit (h 0 _ List.get?_zero_cons')

theorem not_cctx2_cloner :
    ¬ CCtx2 [Ty.arrow Ty.content (Ty.tensor Ty.content Ty.content), Ty.content] := by
  intro h
  exact not_cpos2_cloner (h 0 _ List.get?_zero_cons')

/-- The round-1 witness `knowerPair` is still cut-free: the repair is at the
CLASS, not at the derivation. -/
theorem cutFree_knowerPair : CutFree knowerPair := by
  simp [knowerPair, knowerContent, CutFree, IsAtomic]

/-! ## 3. Class consequences -/

theorem cpos2_notNeedsK {b : Ty} (h : CPos2 b) : ¬ NeedsK b := by
  rcases h with h1 | h2 | h3
  · rw [h1]; intro hk; exact hk
  · obtain ⟨_, h2a, -⟩ := h2
    intro hk
    exact h2a (Or.inr hk)
  · obtain ⟨T, hT, -⟩ := h3
    rw [hT]; intro hk; exact hk

theorem cpos2_notCSupply {b : Ty} (h : CPos2 b) (hb : b ≠ Ty.content) : ¬ CSupply b := by
  rcases h with h1 | h2 | h3
  · exact absurd h1 hb
  · obtain ⟨_, h2a, -⟩ := h2
    exact h2a
  · obtain ⟨T, hT, -⟩ := h3
    subst hT
    intro hcs
    rcases hcs with hc | hk
    · exact hc
    · exact hk

theorem cctx2_noCSupply {Γ : List Ty} (h : CCtx2 Γ) (hnc : ¬ HasContent Γ) :
    NoCSupply Γ := by
  intro i b hpos hcs
  have hb : b ≠ Ty.content := by
    intro he
    subst he
    exact hnc ⟨i, hpos⟩
  exact cpos2_notCSupply (h i b hpos) hb hcs

theorem cctx2_noNeedsK {Γ : List Ty} (h : CCtx2 Γ) :
    ∀ (i : Nat) (b : Ty), Γ[i]? = some b → ¬ NeedsK b :=
  fun i b hpos => cpos2_notNeedsK (h i b hpos)

/-! ## 4. `LCSafe`, `C0Safe`, `KSSafe` — PROVED -/

theorem LCSafe {Γ : List Ty} {t : Term} (h : Typed Γ t Ty.content)
    (hcf : CutFree h) (hc : CCtx2 Γ) (hnc : ¬ HasContent Γ) : False :=
  needsC_val_dead_at_nocsupply (cctx2_noCSupply hc hnc) (by unfold NeedsC; trivial) h

theorem C0Safe {Γ : List Ty} {t : Term}
    (h : Typed Γ t (Ty.tensor Ty.content Ty.content))
    (hcf : CutFree h) (hc : CCtx2 Γ) (hnc : ¬ HasContent Γ) : False :=
  needsC_val_dead_at_nocsupply (cctx2_noCSupply hc hnc)
    (by unfold NeedsC; exact Or.inl trivial) h

theorem KSSafe {Γ : List Ty} {t : Term} (h : Typed Γ t Ty.knower)
    (hcf : CutFree h) (hc : CCtx2 Γ) : False := by
  obtain ⟨i, b, hpos, hKb⟩ := kprop h (by unfold NeedsK; trivial)
  exact cctx2_noNeedsK hc i b hpos hKb

theorem KSSafe' {Γ : List Ty} {t : Term} (h : Typed Γ t Ty.knower)
    (hcf : CutFree h) (hc : CCtx2 Γ) (hhc : HasContent Γ) : False :=
  KSSafe h hcf hc

/-! ## 5. Frame plumbing -/

theorem source_pos (ΓL : List Ty) (ΓS : Ty) (ΓR : List Ty) :
    (ΓL ++ ΓS :: ΓR)[ΓL.length]? = some ΓS := by
  rw [List.get?_append_ge (Nat.le_refl _), Nat.sub_self]
  rfl

theorem frame_noCxC {ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty}
    (hL : AllAdm ΓL) (hR : AllAdm ΓR) (hS : ¬ ContainsCxC ΓS) :
    ∀ (i : Nat) (b : Ty), (ΓL ++ ΓS :: ΓR)[i]? = some b → ¬ ContainsCxC b := by
  intro i b hpos
  by_cases hlt : i < ΓL.length
  · rw [List.get?_append_lt hlt] at hpos
    exact (hL i b hpos).2
  · have hge : ΓL.length ≤ i := Nat.not_lt.mp hlt
    rw [List.get?_append_ge hge] at hpos
    by_cases h0 : i - ΓL.length = 0
    · rw [h0, List.get?_zero_cons'] at hpos
      injection hpos with he
      subst he
      exact hS
    · obtain ⟨j, hj⟩ : ∃ j, i - ΓL.length = j + 1 := ⟨i - ΓL.length - 1, by omega⟩
      rw [hj, List.get?_succ_cons'] at hpos
      exact (hR j b hpos).2

theorem frame_noCxC_cxC {ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty}
    (hL : AllAdm ΓL) (hR : AllAdm ΓR) (hS : ¬ ContainsCxC ΓS)
    (i : Nat) (hpos : (ΓL ++ ΓS :: ΓR)[i]? = some (Ty.tensor Ty.content Ty.content)) :
    False :=
  frame_noCxC hL hR hS i _ hpos trivial

theorem allAdm_cons_local {k : Ty} {Γ : List Ty} (hk : AdmPos k) (h : AllAdm Γ) :
    AllAdm (k :: Γ) := by
  intro i b hpos
  cases i with
  | zero =>
    rw [List.get?_zero_cons'] at hpos
    injection hpos with he
    subst he
    exact hk
  | succ j =>
    rw [List.get?_succ_cons'] at hpos
    exact h j b hpos

theorem allAdm_tail {k : Ty} {Γ : List Ty} (h : AllAdm (k :: Γ)) : AllAdm Γ := by
  intro i b hpos
  exact h (i + 1) b (by rw [List.get?_succ_cons']; exact hpos)

/-- Every `▷T` is admissible (its need predicates are opaque and it is not a
carrier) — this is what keeps the fix descent in class. -/
theorem admPosLater (T : Ty) : AdmPos (Ty.later T) :=
  ⟨fun h => by rcases h with h | h <;> exact h, fun h => h⟩

theorem oneSource_not_allNonLinear {ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty}
    (hcs : CSupply ΓS) (hnK : ¬ NeedsK ΓS) (hΓ : AllNonLinear (ΓL ++ ΓS :: ΓR)) :
    False := by
  have hlin : ΓS.isLinear = true := csupply_notNeedsK_linear hcs hnK
  have hnl : ΓS.isLinear = false := hΓ ΓL.length ΓS (source_pos ΓL ΓS ΓR)
  rw [hlin] at hnl
  exact Bool.noConfusion hnl

/-! ## 6. Term-level rigidity for the constants (used by the app arms) -/

theorem liftAt0_eq_const {c : Term}
    (hc : c = Term.gen ∨ c = Term.red ∨ c = Term.obj ∨ c = Term.terminate) :
    ∀ t : Term, Term.liftAt 0 t = c → t = c := by
  intro t h
  rcases hc with rfl | rfl | rfl | rfl <;> (cases t <;> simp_all [Term.liftAt])

theorem mergeAt0_eq_const {c : Term}
    (hc : c = Term.gen ∨ c = Term.red ∨ c = Term.obj ∨ c = Term.terminate) :
    ∀ t : Term, Term.mergeAt 0 t = c → t = c := by
  intro t h
  rcases hc with rfl | rfl | rfl | rfl <;>
    (cases t with
     | var i =>
       simp only [Term.mergeAt] at h
       split at h
       · cases h
       · split at h <;> cases h
     | gen | lam _ _ | app _ _ | pair _ _ | lete _ _ | unit | next _ | fix _ | cons _ _
     | nil | snoc _ _ | red | obj | terminate =>
       first | rfl | (simp only [Term.mergeAt] at h; cases h))

/-- A constant-headed derivation has one of four fixed types. -/
theorem typed_const_type : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (v : Typed Γ t τ),
    (t = Term.gen ∨ t = Term.red ∨ t = Term.obj ∨ t = Term.terminate) →
    τ = Ty.arrow Ty.knower (Ty.tensor Ty.content Ty.knower) ∨
    τ = Ty.arrow Ty.stream Ty.knowledge ∨
    τ = Ty.arrow Ty.stream Ty.value ∨
    τ = Ty.arrow Ty.knower Ty.trace := by
  intro Γ t τ v
  induction v with
  | gen => intro _; exact Or.inl rfl
  | red => intro _; exact Or.inr (Or.inl rfl)
  | obj => intro _; exact Or.inr (Or.inr (Or.inl rfl))
  | terminate => intro _; exact Or.inr (Or.inr (Or.inr rfl))
  | contr hk h ih =>
      intro hte
      rcases hte with h | h | h | h
      · exact ih (Or.inl (by rw [h]; rfl))
      · exact ih (Or.inr (Or.inl (by rw [h]; rfl)))
      · exact ih (Or.inr (Or.inr (Or.inl (by rw [h]; rfl))))
      · exact ih (Or.inr (Or.inr (Or.inr (by rw [h]; rfl))))
  | weak hk h ih =>
      intro hte
      rcases hte with h | h | h | h
      · exact ih (Or.inl (liftAt0_eq_const (Or.inl rfl) _ h))
      · exact ih (Or.inr (Or.inl (liftAt0_eq_const (Or.inr (Or.inl rfl)) _ h)))
      · exact ih (Or.inr (Or.inr (Or.inl (liftAt0_eq_const (Or.inr (Or.inr (Or.inl rfl))) _ h))))
      · exact ih (Or.inr (Or.inr (Or.inr (liftAt0_eq_const (Or.inr (Or.inr (Or.inr rfl))) _ h))))
  | var | lam _ | app _ _ | pair _ _ | lete _ _ | unit | next _ | fix _ | cons _ _
  | nil | snoc _ _ =>
      intro hte
      rcases hte with h | h | h | h <;> exact absurd h (by simp)

/-- A constant-headed derivation's CODOMAIN is one of the four fixed types. -/
theorem typed_const_cod : ∀ {Γ : List Ty} {t : Term} {X τ : Ty} (v : Typed Γ t (Ty.arrow X τ)),
    (t = Term.gen ∨ t = Term.red ∨ t = Term.obj ∨ t = Term.terminate) →
    τ = Ty.tensor Ty.content Ty.knower ∨ τ = Ty.knowledge ∨ τ = Ty.value ∨ τ = Ty.trace := by
  intro Γ t X τ v hc
  rcases typed_const_type v hc with h | h | h | h
  · left; rw [Ty.arrow.injEq] at h; exact h.2
  · right; left; rw [Ty.arrow.injEq] at h; exact h.2
  · right; right; left; rw [Ty.arrow.injEq] at h; exact h.2
  · right; right; right; rw [Ty.arrow.injEq] at h; exact h.2

/-- A constant cannot head an application concluding a NON-constant codomain
(the four fixed codomains are supplied by the caller as inequalities). -/
theorem typed_const_arrow_dead {Γ : List Ty} {X τ : Ty} {t : Term}
    (v : Typed Γ t (Ty.arrow X τ))
    (hc : t = Term.gen ∨ t = Term.red ∨ t = Term.obj ∨ t = Term.terminate)
    (h1 : τ ≠ Ty.tensor Ty.content Ty.knower) (h2 : τ ≠ Ty.knowledge)
    (h3 : τ ≠ Ty.value) (h4 : τ ≠ Ty.trace) : False := by
  rcases typed_const_cod v hc with h | h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h

/-! ## 7. The named lete residual for the one-source theorem -/

/-- `C1Safe`'s `lete` arm (the brief's KNOWN HARD CASE, compound source).

WITNESS STATUS: no refuter found; NOT proved. The arms proved below do not
consume it, and it is a strict sub-case of `C1Safe`, so a proof of it closes
`C1Safe` outright. -/
def LeteResidualA : Prop :=
  ∀ {Γ₁ Γ₂ ΓL : List Ty} {ΓS a b : Ty} {ΓR : List Ty} {t body : Term},
    AllAdm ΓL → AllAdm ΓR → CSupply ΓS → ¬ NeedsK ΓS → ¬ ContainsCxC ΓS →
    yieldAll ΓS ≤ 1 →
    Typed Γ₁ t (Ty.tensor a b) →
    Typed (b :: a :: Γ₂) body (Ty.tensor Ty.content Ty.content) →
    Γ₁ ++ Γ₂ = ΓL ++ ΓS :: ΓR → False

/-! ## 8. `oneSourceSafe` = `C1Safe` -/

theorem oneSourceSafe (hleteA : LeteResidualA) :
    ∀ (fuel : Nat) (Γ ΓL : List Ty) (ΓS : Ty) (ΓR : List Ty),
      AllAdm ΓL → AllAdm ΓR → CSupply ΓS → ¬ NeedsK ΓS → ¬ ContainsCxC ΓS →
      yieldAll ΓS ≤ 1 → Γ = ΓL ++ ΓS :: ΓR →
      ∀ {t : Term} (h : Typed Γ t (Ty.tensor Ty.content Ty.content)),
        CutFree h → size h ≤ fuel → False := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro Γ ΓL ΓS ΓR hL hR hcs hnK hncA hy heq t h hcf hsz
    cases h with
    | var =>
      have h0 : (ΓL ++ ΓS :: ΓR)[0]? = some (Ty.tensor Ty.content Ty.content) := by
        rw [← heq]
        rfl
      exact frame_noCxC_cxC hL hR hncA 0 h0
    | @app E Γ₁ Δ X b fn arg hf ha hs =>
      obtain ⟨-, -, hatom⟩ := hcf
      rcases hatom with hfn | hfn | hfn | hfn | hfn
      · subst hfn
        obtain ⟨a, hΓ₁, hτ⟩ := var_canonical hf rfl
        subst hτ
        have h0 : (ΓL ++ ΓS :: ΓR)[0]? =
            some (Ty.arrow X (Ty.tensor Ty.content Ty.content)) := by
          rw [← heq, ← hs, hΓ₁]
          rfl
        exact frame_noCxC hL hR hncA 0 _ h0 trivial
      · subst hfn
        exact typed_const_arrow_dead hf (Or.inl rfl) (by simp) (by simp) (by simp) (by simp)
      · subst hfn
        exact typed_const_arrow_dead hf (Or.inr (Or.inl rfl)) (by simp) (by simp)
          (by simp) (by simp)
      · subst hfn
        exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inl rfl))) (by simp)
          (by simp) (by simp) (by simp)
      · subst hfn
        exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inr rfl))) (by simp)
          (by simp) (by simp) (by simp)
    | @pair E Γ₁ Γ₂ a b l r hl hr hs =>
      exact pair_split_dead hL hR hl hr (hs.trans heq)
    | @lete E Γ₁ Γ₂ a b c t' body ht hb hs =>
      exact hleteA hL hR hcs hnK hncA hy ht hb (hs.trans heq)
    | fix hnl hbody =>
      exact oneSource_not_allNonLinear hcs hnK (by rw [heq] at hnl; exact hnl)
    | @contr Γ' k t' τ' hk hpre =>
      cases ΓL with
      | nil =>
        have hkΓS : k = ΓS := (List.cons.inj (by simpa only [List.nil_append] using heq)).1
        subst hkΓS
        rw [csupply_notNeedsK_linear hcs hnK] at hk
        exact Bool.noConfusion hk
      | cons g ΓL' =>
        have hcons := List.cons.inj (by simpa only [List.cons_append] using heq)
        have hkg : k = g := hcons.1
        have htail : Γ' = ΓL' ++ ΓS :: ΓR := hcons.2
        have hg : AdmPos g := hL 0 g List.get?_zero_cons'
        have hL2 : AllAdm (g :: g :: ΓL') := allAdm_cons_local hg hL
        have heq2 : (k :: k :: Γ') = (g :: g :: ΓL') ++ ΓS :: ΓR := by
          rw [hkg, htail]
          rfl
        have hpre_cf : CutFree hpre := by simpa only [CutFree] using hcf
        have h1 : 1 + size hpre ≤ fuel := by simpa only [size_contr] using hsz
        exact ih (size hpre) (by omega) (k :: k :: Γ') (g :: g :: ΓL') ΓS ΓR hL2 hR
          hcs hnK hncA hy heq2 hpre hpre_cf (Nat.le_refl _)
    | @weak Γ' k t' τ' hk hpre =>
      cases ΓL with
      | nil =>
        have hkΓS : k = ΓS := (List.cons.inj (by simpa only [List.nil_append] using heq)).1
        subst hkΓS
        rw [csupply_notNeedsK_linear hcs hnK] at hk
        exact Bool.noConfusion hk
      | cons g ΓL' =>
        have hcons := List.cons.inj (by simpa only [List.cons_append] using heq)
        have htail : Γ' = ΓL' ++ ΓS :: ΓR := hcons.2
        have hL2 : AllAdm ΓL' := allAdm_tail hL
        have hpre_cf : CutFree hpre := by simpa only [CutFree] using hcf
        have h1 : 1 + size hpre ≤ fuel := by simpa only [size_weak] using hsz
        exact ih (size hpre) (by omega) Γ' ΓL' ΓS ΓR hL2 hR hcs hnK
          hncA hy htail hpre hpre_cf (Nat.le_refl _)

/-! ## 9. `arrowTowerSafe` — the fix/arrow-chain descent -/

/-- The tower class: `arrow content C⊗C`, closed under the fix's own shape
`arrow (▷τ) τ` (exactly the types the `fix` case generates). -/
inductive Tel : Ty → Prop
  | base : Tel (Ty.arrow Ty.content (Ty.tensor Ty.content Ty.content))
  | step {τ : Ty} (h : Tel τ) : Tel (Ty.arrow (Ty.later τ) τ)

/-- `arrowTowerSafe`'s `lete` arm (same compound-source wall).

WITNESS STATUS: no refuter found; NOT proved. -/
def LeteResidualB : Prop :=
  ∀ {Γ₁ Γ₂ Γ : List Ty} {a b τ : Ty} {t body : Term},
    AllAdm Γ → Tel τ →
    Typed Γ₁ t (Ty.tensor a b) → Typed (b :: a :: Γ₂) body τ →
    Γ₁ ++ Γ₂ = Γ → False

theorem tel_containsCxC {τ : Ty} (h : Tel τ) : ContainsCxC τ := by
  induction h with
  | base => trivial
  | step h' ih => exact ih

theorem arrowTowerSafe (hleteA : LeteResidualA) (hleteB : LeteResidualB) :
    ∀ (fuel : Nat) (Γ : List Ty), AllAdm Γ →
      ∀ (τ : Ty), Tel τ →
      ∀ {fn : Term} (h : Typed Γ fn τ), CutFree h → size h ≤ fuel → False := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro Γ hAdm τ htel fn h hcf hsz
    cases htel with
    | base =>
      cases h with
      | var =>
        exact (hAdm 0 _ List.get?_zero_cons').2 trivial
      | lam hb =>
        exact oneSourceSafe hleteA (size hb) (Ty.content :: Γ) [] Ty.content Γ
          allAdm_nil hAdm (Or.inl trivial) (fun hk => hk) (fun hx => hx)
          (by rw [yieldAll_content]; exact Nat.le_refl 1) rfl hb hcf (Nat.le_refl _)
      | @app E Γ₁ Δ X b fn' arg hf ha hs =>
        obtain ⟨-, -, hatom⟩ := hcf
        rcases hatom with hfn | hfn | hfn | hfn | hfn
        · subst hfn
          obtain ⟨a, hΓ₁, hτ⟩ := var_canonical hf rfl
          subst hτ
          have h0 : Γ[0]? = some (Ty.arrow X (Ty.arrow Ty.content
              (Ty.tensor Ty.content Ty.content))) := by
            rw [← hs, hΓ₁]
            rfl
          exact (hAdm 0 _ h0).2 trivial
        · subst hfn
          exact typed_const_arrow_dead hf (Or.inl rfl) (by simp) (by simp) (by simp) (by simp)
        · subst hfn
          exact typed_const_arrow_dead hf (Or.inr (Or.inl rfl)) (by simp) (by simp)
            (by simp) (by simp)
        · subst hfn
          exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inl rfl))) (by simp)
            (by simp) (by simp) (by simp)
        · subst hfn
          exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inr rfl))) (by simp)
            (by simp) (by simp) (by simp)
      | @lete E Γ₁ Γ₂ a b c t' body ht hb hs =>
        exact hleteB hAdm Tel.base ht hb (hs.trans rfl)
      | fix hnl hbody =>
        exact ih (size hbody) (by rw [size_fix] at hsz; omega) Γ hAdm
          (Ty.arrow (Ty.later (Ty.arrow Ty.content (Ty.tensor Ty.content Ty.content)))
            (Ty.arrow Ty.content (Ty.tensor Ty.content Ty.content)))
          (Tel.step Tel.base) hbody hcf (Nat.le_refl _)
      | @contr Γ' k t' σ' hk hpre =>
        have hkA : AdmPos k := hAdm 0 k List.get?_zero_cons'
        have hpre_cf : CutFree hpre := by simpa only [CutFree] using hcf
        have h1 : 1 + size hpre ≤ fuel := by simpa only [size_contr] using hsz
        exact ih (size hpre) (by omega) (k :: k :: Γ')
          (allAdm_cons_local hkA hAdm) _ Tel.base hpre hpre_cf (Nat.le_refl _)
      | @weak Γ' k t' σ' hk hpre =>
        have hkA : AdmPos k := hAdm 0 k List.get?_zero_cons'
        have hpre_cf : CutFree hpre := by simpa only [CutFree] using hcf
        have h1 : 1 + size hpre ≤ fuel := by simpa only [size_weak] using hsz
        exact ih (size hpre) (by omega) Γ' (allAdm_tail hAdm) _ Tel.base hpre hpre_cf
          (Nat.le_refl _)
    | @step τ' htel' =>
      cases h with
      | var =>
        exact (hAdm 0 _ List.get?_zero_cons').2 (tel_containsCxC (τ := τ') htel')
      | lam hb =>
        exact ih (size hb) (by rw [size_lam] at hsz; omega) (Ty.later τ' :: Γ)
          (allAdm_cons_local (admPosLater τ') hAdm) τ' htel' hb hcf (Nat.le_refl _)
      | @app E Γ₁ Δ X b fn' arg hf ha hs =>
        obtain ⟨-, -, hatom⟩ := hcf
        rcases hatom with hfn | hfn | hfn | hfn | hfn
        · subst hfn
          obtain ⟨a, hΓ₁, hτ⟩ := var_canonical hf rfl
          subst hτ
          have h0 : Γ[0]? = some (Ty.arrow X (Ty.arrow (Ty.later τ') τ')) := by
            rw [← hs, hΓ₁]
            rfl
          exact (hAdm 0 _ h0).2 (tel_containsCxC (τ := τ') htel')
        · subst hfn
          exact typed_const_arrow_dead hf (Or.inl rfl) (by simp) (by simp) (by simp) (by simp)
        · subst hfn
          exact typed_const_arrow_dead hf (Or.inr (Or.inl rfl)) (by simp) (by simp)
            (by simp) (by simp)
        · subst hfn
          exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inl rfl))) (by simp)
            (by simp) (by simp) (by simp)
        · subst hfn
          exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inr rfl))) (by simp)
            (by simp) (by simp) (by simp)
      | @lete E Γ₁ Γ₂ a b c t' body ht hb hs =>
        exact hleteB hAdm (Tel.step htel') ht hb (hs.trans rfl)
      | fix hnl hbody =>
        exact ih (size hbody) (by rw [size_fix] at hsz; omega) Γ hAdm
          (Ty.arrow (Ty.later (Ty.arrow (Ty.later τ') τ')) (Ty.arrow (Ty.later τ') τ'))
          (Tel.step (Tel.step htel')) hbody hcf (Nat.le_refl _)
      | @contr Γ'' k t' σ' hk hpre =>
        have hkA : AdmPos k := hAdm 0 k List.get?_zero_cons'
        have hpre_cf : CutFree hpre := by simpa only [CutFree] using hcf
        have h1 : 1 + size hpre ≤ fuel := by simpa only [size_contr] using hsz
        exact ih (size hpre) (by omega) (k :: k :: Γ'')
          (allAdm_cons_local hkA hAdm) _ (Tel.step htel') hpre hpre_cf (Nat.le_refl _)
      | @weak Γ'' k t' σ' hk hpre =>
        have hkA : AdmPos k := hAdm 0 k List.get?_zero_cons'
        have hpre_cf : CutFree hpre := by simpa only [CutFree] using hcf
        have h1 : 1 + size hpre ≤ fuel := by simpa only [size_weak] using hsz
        exact ih (size hpre) (by omega) Γ'' (allAdm_tail hAdm) _ (Tel.step htel') hpre hpre_cf
          (Nat.le_refl _)

/-! ## 10. `no_contraction_cf` -/

/-- `[] ⊢ arrow content C⊗C` is impossible for cut-free derivations, modulo
the two named `lete` residuals (both explicit hypotheses). -/
theorem no_contraction_cf (hleteA : LeteResidualA) (hleteB : LeteResidualB)
    {t : Term} (h : Typed [] t (Ty.arrow Ty.content (Ty.tensor Ty.content Ty.content)))
    (hcf : CutFree h) : False :=
  arrowTowerSafe hleteA hleteB (size h) [] allAdm_nil _ Tel.base h hcf (Nat.le_refl _)

/-- `C1Safe` in the brief's exact shape (frame inline). -/
theorem C1Safe (hleteA : LeteResidualA) {ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty}
    {t : Term} (h : Typed (ΓL ++ ΓS :: ΓR) t (Ty.tensor Ty.content Ty.content))
    (hcf : CutFree h) (hL : AllAdm ΓL) (hR : AllAdm ΓR) (hcs : CSupply ΓS)
    (hnK : ¬ NeedsK ΓS) (hnc : ¬ ContainsCxC ΓS) (hy : yieldAll ΓS ≤ 1) : False :=
  oneSourceSafe hleteA (size h) (ΓL ++ ΓS :: ΓR) ΓL ΓS ΓR hL hR hcs hnK hnc hy rfl h hcf
    (Nat.le_refl _)

/-! ## 11. Non-vacuity: the residuals' hypothesis sets are inhabited -/

theorem source_class_inhabited :
    AllAdm ([] : List Ty) ∧ CSupply Ty.content ∧ ¬ NeedsK Ty.content ∧
      ¬ ContainsCxC Ty.content ∧ yieldAll Ty.content ≤ 1 := by
  refine ⟨allAdm_nil, Or.inl trivial, fun hk => hk, fun hx => hx, ?_⟩
  rw [yieldAll_content]
  exact Nat.le_refl 1

theorem tower_class_inhabited :
    AllAdm ([] : List Ty) ∧ Tel (Ty.arrow Ty.content (Ty.tensor Ty.content Ty.content)) :=
  ⟨allAdm_nil, Tel.base⟩

/-! ## 1. The class, verbatim from the brief -/

/-- The vanishing chain: `arrow content unit` at the base, closed under the
fix's own shape `arrow (▷T) T`. -/
def VanChain : Ty → Prop
  | Ty.arrow Ty.content Ty.unit => True
  | Ty.arrow (Ty.later T) T' => VanChain T ∧ T = T'
  | _ => False

/-- THE REPAIRED POSITION CLASS (the brief's `VPos2`, verbatim). -/
def VPos2 (b : Ty) : Prop :=
  b = Ty.content ∨
    (b.isLinear = false ∧ ¬ CSupply b ∧ ¬ ContainsCxC b) ∨
    (∃ T : Ty, b = Ty.later T ∧ (VanChain T ∨ T = Ty.content))

/-- Every position of the context is in the repaired class. -/
def VCtx2 (Γ : List Ty) : Prop := ∀ (i : Nat) (b : Ty), Γ[i]? = some b → VPos2 b

/-! ## 2. The brief's two twins -/

theorem vpos2_notNeedsK {b : Ty} (h : VPos2 b) : ¬ NeedsK b := by
  rcases h with h1 | h2 | h3
  · rw [h1]; intro hk; exact hk
  · obtain ⟨-, hcs, -⟩ := h2
    intro hk
    exact hcs (Or.inr hk)
  · obtain ⟨T, hT, -⟩ := h3
    rw [hT]; intro hk; exact hk

theorem vpos2_csupply {b : Ty} (h : VPos2 b) (hcs : CSupply b) : b = Ty.content := by
  rcases h with h1 | h2 | h3
  · exact h1
  · obtain ⟨-, h2a, -⟩ := h2
    exact absurd hcs h2a
  · obtain ⟨T, hT, -⟩ := h3
    subst hT
    rcases hcs with hc | hk
    · exact hc.elim
    · exact hk.elim

/-! ## 3. Class consequences -/

theorem vpos2_notCSupply {b : Ty} (h : VPos2 b) (hb : b ≠ Ty.content) : ¬ CSupply b := by
  rcases h with h1 | h2 | h3
  · exact absurd h1 hb
  · obtain ⟨-, h2a, -⟩ := h2
    exact h2a
  · obtain ⟨T, hT, -⟩ := h3
    subst hT
    intro hcs
    rcases hcs with hc | hk
    · exact hc
    · exact hk

theorem vctx2_noCSupply {Γ : List Ty} (h : VCtx2 Γ) (hnc : ¬ HasContent Γ) :
    NoCSupply Γ := by
  intro i b hpos hcs
  have hb : b ≠ Ty.content := by
    intro he
    subst he
    exact hnc ⟨i, hpos⟩
  exact vpos2_notCSupply (h i b hpos) hb hcs

theorem vpos2_content : VPos2 Ty.content := Or.inl rfl

theorem vpos2_unit : VPos2 Ty.unit :=
  Or.inr (Or.inl ⟨rfl, (fun h => by rcases h with h | h <;> exact h), (fun h => h)⟩)

/-- A `VPos2` arrow whose codomain is `unit` has a NON-LINEAR domain — the
whole difference from `AdmPos` (which admits the killer). -/
theorem vpos2_arrow_unit_domain_nonlinear {X : Ty} (h : VPos2 (Ty.arrow X Ty.unit)) :
    X.isLinear = false := by
  rcases h with h1 | h2 | h3
  · exact absurd h1 (fun hh => by cases hh)
  · obtain ⟨hlin, -, -⟩ := h2
    simpa [Ty.isLinear, Bool.or_false] using hlin
  · obtain ⟨T, hT, -⟩ := h3
    exact absurd hT (fun hh => by cases hh)

/-- The KILLER position is NOT in the class (its domain is linear). -/
theorem not_vpos2_killer : ¬ VPos2 (Ty.arrow Ty.content Ty.unit) := by
  intro h
  rcases h with h1 | h2 | h3
  · exact absurd h1 (fun hh => by cases hh)
  · obtain ⟨hlin, -, -⟩ := h2
    simp [Ty.isLinear] at hlin
  · obtain ⟨T, hT, -⟩ := h3
    exact absurd hT (fun hh => by cases hh)

/-- The class is linear-position-free (`trace` is `AdmPos` but not `VPos2`). -/
theorem not_vpos2_trace : ¬ VPos2 Ty.trace := by
  intro h
  rcases h with h1 | h2 | h3
  · exact absurd h1 (fun hh => by cases hh)
  · obtain ⟨hlin, -, -⟩ := h2
    simp [Ty.isLinear] at hlin
  · obtain ⟨T, hT, -⟩ := h3
    exact absurd hT (fun hh => by cases hh)

/-! ## 4. Falsify-first: the `AdmPos` mirror of the one-source statement is
FALSE at the cut-free grain — and `VPos2` is what excludes it -/

/-- No `CSupply` arrow has a `unit` codomain. -/
theorem not_csupply_arrow_unit {X : Ty} : ¬ CSupply (Ty.arrow X Ty.unit) := by
  intro h
  rcases h with h | h
  · exact h.1
  · exact h.1

/-- `AdmPos` ADMITS the killer position: the measurement that separates the
brief's class from the march's admissibility discipline. -/
theorem admPos_killer : AdmPos (Ty.arrow Ty.content Ty.unit) :=
  ⟨not_csupply_arrow_unit, fun h => h⟩

/-- The killer frame: the killer position beside the token. -/
def killerFrame : List Ty := [Ty.arrow Ty.content Ty.unit, Ty.content]

/-- THE WITNESS: the killer fired on the token — `(var 0) (var 0)`, a LEGAL
cut-free derivation of `unit` at the killer frame. -/
def killerFire : Typed killerFrame (Term.app (Term.var 0) (Term.var 0)) Ty.unit :=
  Typed.app (Γ := [Ty.arrow Ty.content Ty.unit]) (Δ := [Ty.content])
    (a := Ty.content) (b := Ty.unit) Typed.var Typed.var rfl

theorem killerFire_cutFree : CutFree killerFire := ⟨trivial, trivial, Or.inl rfl⟩

/-- The witness's pieces are `AdmPos`-legal (`[]` and `[killer]`). -/
theorem killerFrame_admPieces :
    AllAdm ([] : List Ty) ∧ AllAdm [Ty.arrow Ty.content Ty.unit] :=
  ⟨allAdm_nil, allAdm_cons admPos_killer allAdm_nil⟩

/-- **REFUTATION**: the vanishing mirror of the sibling's `oneSourceSafe`
(unit conclusion at a one-source frame, `AdmPos` pieces, `yieldAll ≤ 1`
source) is FALSE at the cut-free grain. The vanishing side therefore cannot
reuse the contraction file's architecture — the class is load-bearing, not
cosmetic. -/
theorem oneSourceUnit_mirror_refuted :
    ¬ (∀ {ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty} {t : Term}
        (h : Typed (ΓL ++ ΓS :: ΓR) t Ty.unit),
        AllAdm ΓL → AllAdm ΓR → CSupply ΓS → ¬ NeedsK ΓS → ¬ ContainsCxC ΓS →
        yieldAll ΓS ≤ 1 → CutFree h → False) := by
  intro H
  refine H (ΓL := [Ty.arrow Ty.content Ty.unit]) (ΓS := Ty.content) (ΓR := [])
    killerFire killerFrame_admPieces.2 allAdm_nil (Or.inl trivial) (fun hk => hk)
    (fun hx => hx) ?_ killerFire_cutFree
  rw [yieldAll_content]
  exact Nat.le_refl 1

/-- The witness's context is NOT a `VCtx2` context: the class excludes it
(the killer's domain is linear). -/
theorem not_vctx2_killerFrame : ¬ VCtx2 killerFrame := by
  intro h
  exact not_vpos2_killer (h 0 _ List.get?_zero_cons')

/-! ## 5. `LC2` — the brief's third statement, PROVEN -/

/-- **`LC2`**: a content-valued derivation at a class context with no content
is impossible. (The class supplies `NoCSupply`; the in-tree
`needsC_val_dead_at_nocsupply` finishes it — no `CutFree` needed, as the
brief predicted via the `cprop` shortcut.) -/
theorem LC2 {Γ : List Ty} {t : Term} (h : Typed Γ t Ty.content)
    (hcf : CutFree h) (hc : VCtx2 Γ) (hnc : ¬ HasContent Γ) : False :=
  needsC_val_dead_at_nocsupply (vctx2_noCSupply hc hnc) (by unfold NeedsC; trivial) h

/-! ## 6. Frame plumbing and `root_gate` -/

theorem vctx2_singleton {b : Ty} (h : VPos2 b) : VCtx2 [b] := by
  intro i c hpos
  by_cases hi : i = 0
  · subst hi
    rw [List.get?_zero_cons'] at hpos
    injection hpos with he
    subst he
    exact h
  · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    subst hj
    rw [List.get?_succ_cons', List.get?_nil'] at hpos
    contradiction

theorem not_hasContent_singleton {b : Ty} (hb : b ≠ Ty.content) : ¬ HasContent [b] := by
  intro hc
  obtain ⟨i, hi⟩ := hc
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hi
      injection hi with he
      exact hb he
  | succ j =>
      rw [List.get?_succ_cons', List.get?_nil'] at hi
      contradiction

/-- `LC2`'s `[unit]` instance: no content value at a `unit` frame. -/
theorem LC2_at_singleton_unit {t : Term} (h : Typed [Ty.unit] t Ty.content)
    (hcf : CutFree h) : False :=
  LC2 h hcf (vctx2_singleton vpos2_unit)
    (not_hasContent_singleton (fun he => by cases he))

/-- Atomic heads are never compound terms. -/
theorem isAtomic_ne_lam {a : Ty} {body : Term} : ¬ IsAtomic (Term.lam a body) := by
  intro h; rcases h with h | h | h | h | h <;> (cases h)

theorem isAtomic_ne_fix {body : Term} : ¬ IsAtomic (Term.fix body) := by
  intro h; rcases h with h | h | h | h | h <;> (cases h)

theorem isAtomic_ne_lete {t body : Term} : ¬ IsAtomic (Term.lete t body) := by
  intro h; rcases h with h | h | h | h | h <;> (cases h)

theorem isAtomic_ne_app {fn arg : Term} : ¬ IsAtomic (Term.app fn arg) := by
  intro h; rcases h with h | h | h | h | h <;> (cases h)

/-- The shape of the last rule of a cut-free CLOSED `arrow content unit`. -/
inductive RootShape : Term → Prop
  | lam {a : Ty} {body : Term} : RootShape (Term.lam a body)
  | fix {body : Term} : RootShape (Term.fix body)
  | lete {t body : Term} : RootShape (Term.lete t body)

/-- The `app` arm of the closed root, discharged: the function of a closed
application is a closed arrow-typed derivation, and `IsAtomic` rules out
every head it can have. -/
theorem app_arm_closed {Γ Δ : List Ty} {X : Ty} {fn : Term}
    (hf : Typed Γ fn (Ty.arrow X (Ty.arrow Ty.content Ty.unit)))
    (hs : Γ ++ Δ = ([] : List Ty)) (hatom : IsAtomic fn) : False := by
  cases hf with
  | var =>
      have hlen := congrArg List.length hs
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | lam hb => exact absurd hatom isAtomic_ne_lam
  | fix hnl hb => exact absurd hatom isAtomic_ne_fix
  | lete ht hb hs' => exact absurd hatom isAtomic_ne_lete
  | contr hk hp =>
      have hlen := congrArg List.length hs
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | weak hk hp =>
      have hlen := congrArg List.length hs
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | app hf2 ha2 => exact absurd hatom isAtomic_ne_app

/-- **`root_gate`** (the brief's measured fact): a cut-free closed derivation
of `arrow content unit` is `lam`-, `fix`- or `lete`-headed. Every other last
rule is dead at the closed root; the `app` arm dies because a closed
arrow-typed function derivation is `lam`/`fix`/`app`-headed and each
contradicts `IsAtomic`. -/
theorem root_gate {t : Term} (h : Typed [] t (Ty.arrow Ty.content Ty.unit))
    (hcf : CutFree h) : RootShape t := by
  cases h with
  | lam hb => exact RootShape.lam
  | fix hnl hb => exact RootShape.fix
  | lete ht hb hs => exact RootShape.lete
  | @app E Γ₁ Δ X b fn arg hf ha hs =>
      obtain ⟨-, -, hatom⟩ := hcf
      exact (app_arm_closed hf hs hatom).elim

/-! ## 7. The brief's `no_vanishing_cf`, modulo exactly its three arms -/

/-- The `lam` arm: no cut-free derivation of `[content] ⊢ unit` — the brief's
`VNL2` at its `[content]`-instance, i.e. the open core. -/
def LamArm : Prop := ∀ (t : Term) (h : Typed [Ty.content] t Ty.unit), CutFree h → False

/-- The `fix` arm: the `▷`-stack (the nested fix body's descent), scoped to
the vanishing chain. HONESTY (kernel-measured, probes scAtk1/scLeteV): the
ORIGINAL statement (all `a : Ty`) is REFUTED — witness `a := unit`,
`body := lam (▷unit) (weak-lifted unit)`: `▷unit` is non-linear so `weak`
drops the binder, `AllNonLinear []` is vacuous, `CutFree` holds. The chain
scope excludes exactly that refuter (`¬ VanChain unit`), and the use site
instantiates `a := arrow content unit`, which IS the chain's base. -/
def FixArm : Prop :=
  ∀ (a : Ty), VanChain a →
    ∀ (body : Term) (hnl : AllNonLinear [])
      (hb : Typed [] body (Ty.arrow (Ty.later a) a)), CutFree hb → False

/-- The `lete` arm: the closed-tensor descent. -/
def LeteArm : Prop :=
  ∀ {Γ₁ Γ₂ : List Ty} {a b : Ty} {t body : Term},
    Typed Γ₁ t (Ty.tensor a b) →
    Typed (b :: a :: Γ₂) body (Ty.arrow Ty.content Ty.unit) →
    Γ₁ ++ Γ₂ = ([] : List Ty) → False

/-- **`no_vanishing_cf`** (the brief's statement), PROVEN modulo exactly its
three last-rule arms. `root_gate` supplied the decomposition; no `sorryAx`
anywhere — the arms are explicit hypotheses with the witness status recorded
in the module docstring. -/
theorem no_vanishing_cf_of_arms (hLam : LamArm) (hFix : FixArm) (hLete : LeteArm)
    {t : Term} (h : Typed [] t (Ty.arrow Ty.content Ty.unit)) (hcf : CutFree h) : False := by
  cases h with
  | lam hb => exact hLam _ hb hcf
  | fix hnl hb =>
      exact hFix (Ty.arrow Ty.content Ty.unit) trivial _ hnl hb hcf
  | lete ht hb hs => exact hLete ht hb hs
  | @app E Γ₁ Δ X b fn arg hf ha hs =>
      obtain ⟨-, -, hatom⟩ := hcf
      exact (app_arm_closed hf hs hatom).elim

/-! ## 8. The brief's `VNL2` / `VU''` — stated, witness-statused, NOT proven -/

/-- The brief's `VNL2`: no cut-free non-linear-concluding derivation at a
class context with content.

WITNESS STATUS: **no refuter constructible** (its `[content]`-instance,
`τ := unit`, IS the unrestricted vanishing statement) and **NOT proved** —
this is the open core the whole vanishing side reduces to. -/
def VNL2 : Prop :=
  ∀ (Γ : List Ty) (t : Term) (τ : Ty) (h : Typed Γ t τ),
    CutFree h → τ.isLinear = false → VCtx2 Γ → HasContent Γ → False

/-- The brief's `VU''`: no cut-free `unit`-concluding derivation at a
non-empty context all of whose positions are `▷`-of-a-vanishing-chain (or
content). WITNESS STATUS: no refuter; not proved (the `▷`-stack's landing
zone, same content as `LamArm`). -/
def VU'' : Prop :=
  ∀ (Γ : List Ty) (t : Term) (h : Typed Γ t Ty.unit),
    CutFree h → Γ ≠ [] →
    (∀ (i : Nat) (b : Ty), Γ[i]? = some b →
      ∃ T : Ty, b = Ty.later T ∧ (VanChain T ∨ T = Ty.content)) → False

/-- The reduction, measured: the brief's `no_vanishing_cf`'s `lam` arm IS
`LamArm`, i.e. `VNL2`'s `[content]`-instance. -/
theorem lamArm_of_VNL2 (h : VNL2) : LamArm := by
  intro t hb hcf
  exact h [Ty.content] t Ty.unit hb hcf (by decide) (vctx2_singleton vpos2_content)
    ⟨0, List.get?_zero_cons'⟩

/-- And conversely: `VNL2`'s `[content]`-instance is exactly `LamArm`
(definitionally), so the brief's core statement and the project's open
vanishing statement are the same theorem. -/
theorem VNL2_singleton_of_lamArm (h : LamArm) :
    ∀ (t : Term) (h' : Typed [Ty.content] t Ty.unit), CutFree h' → False := h

/-! ## 9. Axiom audit -/



/-! ## The vanishing core — the equivalence measurement (probe scLeteV2, transfer-landed)

The vanishing side's residual structure, pinned at the kernel: `vSafe`
reduces the whole descent to the ONE named residual `VLeteArm` (the lete
arm at the four goal shapes), and the measurement below shows the
residual is CORE-STRENGTH: `VLeteArm` implies the core instance
`[unit, content] ⊢ unit` by a single instantiation, which implies
`LamArm` (the cut-free core) by one `weak`; conversely a core inhabitant
refutes `VLeteArm`. So at the cut-free grain the lete arm IS the core —
nothing below it closes. The falsify-first record (§H in the probe:
the killer comp needs a closed cut-free `arrow content unit`, whose
`root_gate` roots are exactly `LamArm`/`FixArm`/`LeteArm`) is carried in
the docstrings below. -/

/-! ## A. The tree moved: the in-tree `FixArm` now carries `VanChain`

The previous round (`scLeteV.lean`) falsified the THEN in-tree `FixArm`
(quantified over ALL `a : Ty`) with `a := unit`, `body := lam (▷unit) unit`.
That repair has since LANDED in `Dcare/SC.lean` — its `FixArm` docstring
records the refuter — so the falsification is retired here: `FixArm'` below
is definitionally the in-tree arm, and `no_vanishing_cf_of_arms` is no
longer vacuous. The witness is kept as a MEASURED fact: it IS a legal
cut-free closed `arrow (▷unit) unit`, so `VanChain` is load-bearing.
-/

/-- The witness body: the fixed point's body is the `▷unit`-reader that
weakens its binder away. -/
def fixArmWitnessBody : Term := Term.lam (Ty.later Ty.unit) Term.unit

theorem allNonLinear_nil : AllNonLinear ([] : List Ty) := by
  intro i b h
  rw [List.get?_nil'] at h
  contradiction

/-- The witness derivation: `[] ⊢ arrow (▷unit) unit`. The last rule is
`lam`, whose body drops the binder via `weak` — legal precisely because
`(▷ unit).isLinear = false`. `VanChain unit` is FALSE, which is exactly why
the arm must carry `VanChain`. -/
def fixArmWitnessTyped :
    Typed [] fixArmWitnessBody (Ty.arrow (Ty.later Ty.unit) Ty.unit) :=
  Typed.lam (Typed.weak (k := Ty.later Ty.unit) (by rfl) Typed.unit)

theorem fixArmWitness_cutFree : CutFree fixArmWitnessTyped := by
  show CutFree (Typed.lam (Typed.weak (k := Ty.later Ty.unit) (by rfl) Typed.unit))
  show CutFree (Typed.weak (k := Ty.later Ty.unit) (by rfl) Typed.unit)
  show CutFree Typed.unit
  exact trivial

/-- `unit` is not a chain — the restatement excludes the witness exactly. -/
theorem not_vanChain_unit : ¬ VanChain Ty.unit := by simp [VanChain]

/-- The chain-scoped arm (definitionally the in-tree `FixArm`). -/
def FixArm' : Prop :=
  ∀ (a : Ty) (_hV : VanChain a) (body : Term) (_hnl : AllNonLinear ([] : List Ty))
    (hb : Typed [] body (Ty.arrow (Ty.later a) a)), CutFree hb → False

/-- `FixArm'` IS the in-tree `FixArm` (same statement; the tree's repair). -/
theorem fixArm'_eq_inTree : FixArm' ↔ FixArm := Iff.rfl
/-! ## B. `VanChain` and its linearity

`VanChain` is a match-def, so the linearity fact is proved by recursion on
the type. -/

theorem vanChain_linear : ∀ (a : Ty), VanChain a → a.isLinear = true
  | Ty.content, h => by simp [VanChain] at h
  | Ty.knower, h => by simp [VanChain] at h
  | Ty.knowledge, h => by simp [VanChain] at h
  | Ty.value, h => by simp [VanChain] at h
  | Ty.stream, h => by simp [VanChain] at h
  | Ty.trace, h => by simp [VanChain] at h
  | Ty.unit, h => by simp [VanChain] at h
  | Ty.later a, h => by simp [VanChain] at h
  | Ty.tensor a b, h => by simp [VanChain] at h
  | Ty.arrow x y, h => by
      cases x with
      | content =>
          cases y with
          | unit => rfl
          | content => simp [VanChain] at h
          | knower => simp [VanChain] at h
          | knowledge => simp [VanChain] at h
          | value => simp [VanChain] at h
          | stream => simp [VanChain] at h
          | trace => simp [VanChain] at h
          | later _ => simp [VanChain] at h
          | tensor _ _ => simp [VanChain] at h
          | arrow _ _ => simp [VanChain] at h
      | later T =>
          obtain ⟨hT, hTy⟩ := h
          subst hTy
          have hl := vanChain_linear T hT
          simp [Ty.isLinear, hl]
      | knower => simp [VanChain] at h
      | knowledge => simp [VanChain] at h
      | value => simp [VanChain] at h
      | stream => simp [VanChain] at h
      | trace => simp [VanChain] at h
      | unit => simp [VanChain] at h
      | tensor _ _ => simp [VanChain] at h
      | arrow _ _ => simp [VanChain] at h

/-- `VanChain`'s step: `arrow (▷a) a` is again a chain. -/
theorem vanChain_step {a : Ty} (hV : VanChain a) : VanChain (Ty.arrow (Ty.later a) a) :=
  And.intro hV rfl

theorem later_linear_of_chain {a : Ty} (hV : VanChain a) :
    (Ty.later a).isLinear = true := by
  simpa [Ty.isLinear] using vanChain_linear a hV

theorem later_linear_ne_false {a : Ty} (hV : VanChain a)
    (h : (Ty.later a).isLinear = false) : False := by
  rw [later_linear_of_chain hV] at h
  exact Bool.noConfusion h

theorem content_linear_ne_false (h : Ty.content.isLinear = false) : False :=
  Bool.noConfusion h

/-! ## C. The class facts -/

theorem not_vpos2_of_linear {b : Ty} (hlin : b.isLinear = true) (hne : b ≠ Ty.content)
    (hnotlater : ∀ T : Ty, b ≠ Ty.later T) : ¬ VPos2 b := by
  intro h
  rcases h with h1 | ⟨hnl, -, -⟩ | ⟨T, hT, -⟩
  · exact hne h1
  · rw [hlin] at hnl
    exact Bool.noConfusion hnl
  · exact hnotlater T hT

theorem not_vpos2_tower {a : Ty} (hV : VanChain a) :
    ¬ VPos2 (Ty.arrow (Ty.later a) a) := by
  apply not_vpos2_of_linear (hne := by simp) (hnotlater := fun T hh => by cases hh)
  simp only [Ty.isLinear]
  rw [vanChain_linear a hV]
  simp

theorem not_vpos2_tower_cod {X a : Ty} (hV : VanChain a) :
    ¬ VPos2 (Ty.arrow X (Ty.arrow (Ty.later a) a)) := by
  apply not_vpos2_of_linear (hne := by simp) (hnotlater := fun T hh => by cases hh)
  simp only [Ty.isLinear]
  rw [vanChain_linear a hV]
  simp

theorem vpos2_later_of_chain {a : Ty} (hV : VanChain a) : VPos2 (Ty.later a) :=
  Or.inr (Or.inr ⟨a, rfl, Or.inl hV⟩)

theorem vctx2_nil : VCtx2 ([] : List Ty) := by
  intro i b h
  rw [List.get?_nil'] at h
  contradiction

theorem vctx2_cons {b : Ty} {Γ : List Ty} (hb : VPos2 b) (h : VCtx2 Γ) :
    VCtx2 (b :: Γ) := by
  intro i x hx
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hx
      injection hx with hxb
      subst hxb
      exact hb
  | succ j =>
      rw [List.get?_succ_cons'] at hx
      exact h j x hx

theorem vctx2_tail {b : Ty} {Γ : List Ty} (h : VCtx2 (b :: Γ)) : VCtx2 Γ := by
  intro i x hx
  exact h (i + 1) x (by rw [List.get?_succ_cons']; exact hx)

/-- A `var`-headed application's function context is the SINGLETON of its own
arrow type. If the whole context's head is a different type (`▷a` in the
`base` shape, `content` in the `unit`/`core` shapes), the split is
impossible. -/
theorem head_ne_of_append_singleton {Γ : List Ty} {h c : Ty} {Γ₁ Δ : List Ty}
    (hs : Γ₁ ++ Δ = h :: Γ) (hΓ₁ : Γ₁ = [c]) (hne : c ≠ h) : False := by
  have h1 : c :: Δ = h :: Γ := by
    rw [← hs, hΓ₁]
    simp
  exact hne (List.cons.inj h1).1

/-! ## D. The four shapes and the goal type -/

/-- The shapes the cut-free descent closes: everything the tower's
`lam`/`fix` unwindings reach. Each carries its own discipline and chain. -/
inductive VGoal : List Ty → Ty → Prop
  | tower {Γ : List Ty} {a : Ty} (hV : VanChain a) (hC : VCtx2 Γ) :
      VGoal Γ (Ty.arrow (Ty.later a) a)
  | base {Γ : List Ty} {a : Ty} (hV : VanChain a) (hC : VCtx2 Γ) :
      VGoal (Ty.later a :: Γ) (Ty.arrow Ty.content Ty.unit)
  | unit {Γ : List Ty} {a : Ty} (hV : VanChain a) (hC : VCtx2 Γ) :
      VGoal (Ty.content :: Ty.later a :: Γ) Ty.unit
  | core : VGoal [Ty.content] Ty.unit

/-- The shape's own context is disciplined. -/
theorem vgoal_ctx {Γ : List Ty} {τ : Ty} (g : VGoal Γ τ) : VCtx2 Γ := by
  cases g with
  | tower hV hC => exact hC
  | base hV hC => exact vctx2_cons (vpos2_later_of_chain hV) hC
  | unit hV hC =>
      exact vctx2_cons (Or.inl rfl) (vctx2_cons (vpos2_later_of_chain hV) hC)
  | core => exact vctx2_cons (Or.inl rfl) vctx2_nil

/-- The tower's `lam` unwinding: from `Γ ⊢ arrow (▷a) a` reach `▷a :: Γ ⊢ a`.
`a` is either the base `arrow content unit` (the `base` shape) or a step
`arrow (▷T) T` (the `tower` shape at `T`). -/
theorem vgoal_unwind {Γ : List Ty} {a : Ty} (hV : VanChain a) (hC : VCtx2 Γ) :
    VGoal (Ty.later a :: Γ) a := by
  cases a with
  | content => exact absurd hV (by simp [VanChain])
  | knower => exact absurd hV (by simp [VanChain])
  | knowledge => exact absurd hV (by simp [VanChain])
  | value => exact absurd hV (by simp [VanChain])
  | stream => exact absurd hV (by simp [VanChain])
  | trace => exact absurd hV (by simp [VanChain])
  | unit => exact absurd hV (by simp [VanChain])
  | later _ => exact absurd hV (by simp [VanChain])
  | tensor _ _ => exact absurd hV (by simp [VanChain])
  | arrow x y =>
      cases x with
      | content =>
          cases y with
          | unit => exact VGoal.base trivial hC
          | content => exact absurd hV (by simp [VanChain])
          | knower => exact absurd hV (by simp [VanChain])
          | knowledge => exact absurd hV (by simp [VanChain])
          | value => exact absurd hV (by simp [VanChain])
          | stream => exact absurd hV (by simp [VanChain])
          | trace => exact absurd hV (by simp [VanChain])
          | later _ => exact absurd hV (by simp [VanChain])
          | tensor _ _ => exact absurd hV (by simp [VanChain])
          | arrow _ _ => exact absurd hV (by simp [VanChain])
      | later T =>
          obtain ⟨hT, hTy⟩ := hV
          subst hTy
          exact VGoal.tower hT (vctx2_cons (vpos2_later_of_chain (vanChain_step hT)) hC)
      | knower => exact absurd hV (by simp [VanChain])
      | knowledge => exact absurd hV (by simp [VanChain])
      | value => exact absurd hV (by simp [VanChain])
      | stream => exact absurd hV (by simp [VanChain])
      | trace => exact absurd hV (by simp [VanChain])
      | unit => exact absurd hV (by simp [VanChain])
      | tensor _ _ => exact absurd hV (by simp [VanChain])
      | arrow _ _ => exact absurd hV (by simp [VanChain])

/-! ## E. The one named residual

The `lete` arm at any of the four shapes: the scrutinee is cut-free at a
prefix of the shape's context, and the body is cut-free at the
component-extended context — which is NOT of the shape (the components
`y, x` are whatever the tensor says, and the record's analysis shows they
can be compound: the `hcompK`/`hleteCxC` family).

WITNESS STATUS: no refuter found (its instances bottom either at a
`[content] ⊢ unit`-regress or at a compound component frame); NOT proved. -/
def VLeteArm : Prop :=
  ∀ (Γ Γ₁ Γ₂ : List Ty) (x y τ : Ty) (t body : Term) (g : VGoal Γ τ)
    (ht : Typed Γ₁ t (Ty.tensor x y)) (hb : Typed (y :: x :: Γ₂) body τ),
    CutFree ht → CutFree hb → Γ₁ ++ Γ₂ = Γ → False

/-! ## F. The descent -/

theorem vSafe (hLete : VLeteArm) :
    ∀ (fuel : Nat) (Γ : List Ty) (τ : Ty) (g : VGoal Γ τ) (t : Term)
      (h : Typed Γ t τ), CutFree h → size h ≤ fuel → False := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro Γ τ g
    have g' : VGoal Γ τ := g
    cases g with
    | @tower Γ a hV hC =>
      intro t h hcf hsz
      cases h with
      | var =>
          exact not_vpos2_tower hV (hC 0 _ List.get?_zero_cons')
      | lam hb =>
          have h1 : 1 + size hb ≤ fuel := by rw [size_lam] at hsz; exact hsz
          exact ih (size hb) (by omega) _ _ (vgoal_unwind hV hC) _ hb hcf (Nat.le_refl _)
      | fix hnl hb =>
          have h1 : 1 + size hb ≤ fuel := by rw [size_fix] at hsz; exact hsz
          exact ih (size hb) (by omega) Γ _ (VGoal.tower (vanChain_step hV) hC) _ hb hcf
            (Nat.le_refl _)
      | @app E Γ₁ Δ X b fn arg hf ha hs =>
          obtain ⟨-, -, hatom⟩ := hcf
          rcases hatom with hfn | hfn | hfn | hfn | hfn
          · subst hfn
            obtain ⟨a', hΓ₁, hτ⟩ := var_canonical hf rfl
            subst hτ
            have h0 : Γ[0]? = some (Ty.arrow X (Ty.arrow (Ty.later a) a)) := by
              rw [← hs, hΓ₁]
              simp
            exact not_vpos2_tower_cod hV (hC 0 _ h0)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inl rfl) (by simp) (by simp) (by simp)
              (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inl rfl)) (by simp) (by simp)
              (by simp) (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inl rfl))) (by simp)
              (by simp) (by simp) (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inr rfl))) (by simp)
              (by simp) (by simp) (by simp)
      | @lete E Γ₁ Γ₂ x y c t' body ht hb hs =>
          exact hLete Γ Γ₁ Γ₂ x y (Ty.arrow (Ty.later a) a) t' body g' ht hb hcf.1 hcf.2 hs
      | @contr Γ' k t' σ' hk hpre =>
          have hkpos : VPos2 k := hC 0 k List.get?_zero_cons'
          have h1 : 1 + size hpre ≤ fuel := by rw [size_contr] at hsz; exact hsz
          exact ih (size hpre) (by omega) (k :: k :: Γ') _
            (VGoal.tower hV (vctx2_cons hkpos (vctx2_cons hkpos (vctx2_tail hC)))) _ hpre hcf
            (Nat.le_refl _)
      | @weak Γ' k t' σ' hk hpre =>
          have h1 : 1 + size hpre ≤ fuel := by rw [size_weak] at hsz; exact hsz
          exact ih (size hpre) (by omega) Γ' _ (VGoal.tower hV (vctx2_tail hC)) _ hpre hcf
            (Nat.le_refl _)
    | @base Γ a hV hC =>
      intro t h hcf hsz
      cases h with
      | lam hb =>
          have h1 : 1 + size hb ≤ fuel := by rw [size_lam] at hsz; exact hsz
          exact ih (size hb) (by omega) _ _ (VGoal.unit hV hC) _ hb hcf (Nat.le_refl _)
      | fix hnl hb =>
          exact later_linear_ne_false hV (hnl 0 _ List.get?_zero_cons')
      | @app E Γ₁ Δ X b fn arg hf ha hs =>
          obtain ⟨-, -, hatom⟩ := hcf
          rcases hatom with hfn | hfn | hfn | hfn | hfn
          · subst hfn
            obtain ⟨a', hΓ₁, hτ⟩ := var_canonical hf rfl
            subst hτ
            exact head_ne_of_append_singleton hs hΓ₁ (fun hh => by cases hh)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inl rfl) (by simp) (by simp) (by simp)
              (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inl rfl)) (by simp) (by simp)
              (by simp) (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inl rfl))) (by simp)
              (by simp) (by simp) (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inr rfl))) (by simp)
              (by simp) (by simp) (by simp)
      | @lete E Γ₁ Γ₂ x y c t' body ht hb hs =>
          exact hLete (Ty.later a :: Γ) Γ₁ Γ₂ x y (Ty.arrow Ty.content Ty.unit) t' body g'
            ht hb hcf.1 hcf.2 hs
      | @contr Γ' k t' σ' hk hpre =>
          exact later_linear_ne_false hV hk
      | @weak Γ' k t' σ' hk hpre =>
          exact later_linear_ne_false hV hk
    | @unit Γ a hV hC =>
      intro t h hcf hsz
      cases h with
      | fix hnl hb =>
          exact content_linear_ne_false (hnl 0 _ List.get?_zero_cons')
      | @app E Γ₁ Δ X b fn arg hf ha hs =>
          obtain ⟨-, -, hatom⟩ := hcf
          rcases hatom with hfn | hfn | hfn | hfn | hfn
          · subst hfn
            obtain ⟨a', hΓ₁, hτ⟩ := var_canonical hf rfl
            subst hτ
            exact head_ne_of_append_singleton (Γ := Ty.later a :: Γ) hs hΓ₁
              (fun hh => by cases hh)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inl rfl) (by simp) (by simp) (by simp)
              (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inl rfl)) (by simp) (by simp)
              (by simp) (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inl rfl))) (by simp)
              (by simp) (by simp) (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inr rfl))) (by simp)
              (by simp) (by simp) (by simp)
      | @lete E Γ₁ Γ₂ x y c t' body ht hb hs =>
          exact hLete (Ty.content :: Ty.later a :: Γ) Γ₁ Γ₂ x y Ty.unit t' body g'
            ht hb hcf.1 hcf.2 hs
      | @contr Γ' k t' σ' hk hpre =>
          exact content_linear_ne_false hk
      | @weak Γ' k t' σ' hk hpre =>
          exact content_linear_ne_false hk
    | core =>
      intro t h hcf hsz
      cases h with
      | fix hnl hb =>
          exact content_linear_ne_false (hnl 0 _ List.get?_zero_cons')
      | @app E Γ₁ Δ X b fn arg hf ha hs =>
          obtain ⟨-, -, hatom⟩ := hcf
          rcases hatom with hfn | hfn | hfn | hfn | hfn
          · subst hfn
            obtain ⟨a', hΓ₁, hτ⟩ := var_canonical hf rfl
            subst hτ
            exact head_ne_of_append_singleton (Γ := []) hs hΓ₁ (fun hh => by cases hh)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inl rfl) (by simp) (by simp) (by simp)
              (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inl rfl)) (by simp) (by simp)
              (by simp) (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inl rfl))) (by simp)
              (by simp) (by simp) (by simp)
          · subst hfn
            exact typed_const_arrow_dead hf (Or.inr (Or.inr (Or.inr rfl))) (by simp)
              (by simp) (by simp) (by simp)
      | @lete E Γ₁ Γ₂ x y c t' body ht hb hs =>
          exact hLete [Ty.content] Γ₁ Γ₂ x y Ty.unit t' body g' ht hb hcf.1 hcf.2 hs
      | @contr Γ' k t' σ' hk hpre =>
          exact content_linear_ne_false hk
      | @weak Γ' k t' σ' hk hpre =>
          exact content_linear_ne_false hk

/-! ## G. The arms, from the residual -/

theorem lamArm_of_residual (hLete : VLeteArm) : LamArm := by
  intro t h hcf
  exact vSafe hLete (size h) [Ty.content] Ty.unit VGoal.core t h hcf (Nat.le_refl _)

/-- NON-VACUITY of the descent's shape (checked as a theorem, because the
record's recurring failure mode is a vacuous hypothesis layer): the tower
shape is inhabited at `a := arrow content unit`, `Γ := []`. -/
theorem tower_shape_inhabited :
    VGoal ([] : List Ty)
      (Ty.arrow (Ty.later (Ty.arrow Ty.content Ty.unit)) (Ty.arrow Ty.content Ty.unit)) :=
  VGoal.tower trivial vctx2_nil

theorem fixArm'_of_residual (hLete : VLeteArm) : FixArm' := by
  intro a hV body hnl hb hcf
  exact vSafe hLete (size hb) [] (Ty.arrow (Ty.later a) a)
    (VGoal.tower hV vctx2_nil) body hb hcf (Nat.le_refl _)

/-- The root judgement of `no_vanishing_cf`, modulo the cut-free residual
`VLeteArm` and the Typed-level `LeteArm`.

This DOES go through the in-tree `no_vanishing_cf_of_arms` now: the tree's
`FixArm` carries `VanChain` (repaired since the previous round), which is
exactly `FixArm'`. The three arms are supplied by
`lamArm_of_residual`/`fixArm'_of_residual`/the `LeteArm` hypothesis. -/
theorem no_vanishing_cf_of_residual (hLete : VLeteArm) (hLeteArm : LeteArm) :
    ∀ {t : Term} (h : Typed [] t (Ty.arrow Ty.content Ty.unit)), CutFree h → False :=
  no_vanishing_cf_of_arms (lamArm_of_residual hLete) (fixArm'_eq_inTree.mp (fixArm'_of_residual hLete))
    hLeteArm

/-! ## H. Falsify-first, round 2: no witness, and why every route is the core

What a `VLeteArm` witness would need: a shape `g : VGoal Γ τ`, a split
`Γ₁ ++ Γ₂ = Γ`, a CUT-FREE scrutinee `Γ₁ ⊢ x ⊗ y` and a CUT-FREE body at
`y :: x :: Γ₂` concluding `τ`. The scrutinee data is free
(`leteCore_data_inhabited`); the body is the whole difficulty. The two
candidate families, and where each dies:

* **the killer comp** (`y = arrow content unit`, `x = content`, body
  `app (var 0) (var 0)`): it needs a CUT-FREE CLOSED `arrow content unit`,
  whose last rule is `lam` (the body is then literally `[content] ⊢ unit`,
  i.e. `LamArm`), `fix` (`FixArm`) or `lete` (`LeteArm`) — the core, the
  arm, the is-there-anything arm. Measured here: `VLeteArm` refutes
  `[unit, content] ⊢ unit`, and a core inhabitant refutes `VLeteArm`
  (section I). So this family is not a witness unless the core is
  inhabited.
* **non-linear comps** (`unit`, `▷unit`, `▷trace(non-linear)`, …): they
  are `weak`-strippable, so the body's derivation strips them and lands on
  a shape at STRICTLY smaller size — `vSafe`'s own induction kills it. No
  witness.
* **linear comps** (`trace`, `▷trace`, `arrow content content`, `tensor
  content unit`, …): every consumption route (var as the singleton,
  `snoc`, `cons`, `app` at an arrow position, `lete` as a scrutinee)
  terminates in a `unit`/arrow conclusion at a context SEEN carrying
  `content` — again the core, or the stream/knowledge/value axis whose
  in-tree engine (`no_stream_without_supply`) is fix-free.

No compiling witness was found; the falsification is BLOCKED on the same
statement the residual would prove.
-/

/-- `TypeK`: the type class of the descent's conclusions — `unit` or a
vanishing chain. Every `VGoal` conclusion is in it. -/
def TypeK (τ : Ty) : Prop := τ = Ty.unit ∨ VanChain τ

theorem vgoal_typeK {Γ : List Ty} {τ : Ty} (g : VGoal Γ τ) : TypeK τ := by
  cases g with
  | tower hV _ => exact Or.inr (vanChain_step hV)
  | base _ _ => exact Or.inr trivial
  | unit _ _ => exact Or.inl rfl
  | core => exact Or.inl rfl


/-! ## I. THE MEASUREMENT: `VLeteArm` is CORE-STRENGTH -/

/-- The core-shape scrutinee: `content ⊗ unit` at `[content]` (the
`[content]` piece is the token, the `[]` piece is `unit`). Hypotheses: none. -/
def leteCoreScrutinee : Typed [Ty.content] (Term.pair (Term.var 0) Term.unit)
    (Ty.tensor Ty.content Ty.unit) :=
  Typed.pair (E := [Ty.content]) (Γ := [Ty.content]) (Δ := [])
    (a := Ty.content) (b := Ty.unit) Typed.var Typed.unit rfl

theorem leteCoreScrutinee_cutFree : CutFree leteCoreScrutinee := by
  show CutFree (Typed.pair (E := [Ty.content]) (Γ := [Ty.content]) (Δ := [])
    (a := Ty.content) (b := Ty.unit) Typed.var Typed.unit rfl)
  exact ⟨trivial, trivial⟩

/-- NON-VACUITY of the residual's quantifier: the core instance's shape and
scrutinee exist with NO hypotheses — the body is the only missing piece. -/
theorem leteCore_data_inhabited :
    VGoal [Ty.content] Ty.unit ∧
      Nonempty (Typed [Ty.content] (Term.pair (Term.var 0) Term.unit)
        (Ty.tensor Ty.content Ty.unit)) :=
  ⟨VGoal.core, ⟨leteCoreScrutinee⟩⟩
/-- A core inhabitant scales to the `lete` body's context: `weak` on `unit`
(legal: `unit` is non-linear), the type unchanged. -/
def core_scales_to_body {t : Term} (h : Typed [Ty.content] t Ty.unit) :
    Typed [Ty.unit, Ty.content] (Term.liftAt 0 t) Ty.unit :=
  Typed.weak (k := Ty.unit) (by rfl) h

/-- **DIRECTION 1**: `VLeteArm` refutes every cut-free `[unit, content] ⊢ unit`
— it is the residual's instance at the core shape, split `[content] | []`,
with the free scrutinee above. -/
theorem VLeteArm_implies_unitContent (hL : VLeteArm) :
    ∀ (t : Term) (h : Typed [Ty.unit, Ty.content] t Ty.unit), CutFree h → False := by
  intro t h hcf
  exact hL [Ty.content] [Ty.content] [] Ty.content Ty.unit Ty.unit
    (Term.pair (Term.var 0) Term.unit) t VGoal.core leteCoreScrutinee h
    leteCoreScrutinee_cutFree hcf rfl

/-- **DIRECTION 2**: that same statement implies `LamArm` — the core is
`weak`-away from the body's context. -/
theorem unitContent_implies_core
    (H : ∀ (t : Term) (h : Typed [Ty.unit, Ty.content] t Ty.unit), CutFree h → False) :
    LamArm := by
  intro t h hcf
  exact H (Term.liftAt 0 t) (core_scales_to_body h) hcf

/-- **THE REFUTER SIDE**: any inhabitant of the open core refutes `VLeteArm`
(it scales by `weak` into the lete body's context). -/
theorem core_inhabitant_refutes_VLeteArm {t : Term} (h : Typed [Ty.content] t Ty.unit)
    (hcf : CutFree h) : ¬ VLeteArm := by
  intro hL
  exact hL [Ty.content] [Ty.content] [] Ty.content Ty.unit Ty.unit
    (Term.pair (Term.var 0) Term.unit) (Term.liftAt 0 t) VGoal.core
    leteCoreScrutinee (core_scales_to_body h) leteCoreScrutinee_cutFree hcf rfl

theorem lamArm_iff_no_core_inhabitant :
    LamArm ↔ ¬ ∃ (t : Term) (h : Typed [Ty.content] t Ty.unit), CutFree h := by
  constructor
  · rintro hL ⟨t, h, hcf⟩
    exact hL t h hcf
  · intro hne t h hcf
    exact hne ⟨t, h, hcf⟩

/-- **THE MEASUREMENT** (this round's result). `VLeteArm` is not a step
below the open core: proving it settles `LamArm` (`VLeteArm →
[unit, content]-waste → LamArm`), and a core inhabitant refutes it. So the
lete arm cannot be discharged by an argument that does not already settle
the cut-free vanishing core — the "type/gate-dead + strictly smaller"
expectation is refuted by this pair. -/
theorem VLeteArm_settles_core :
    (VLeteArm → LamArm) ∧
      ((∃ (t : Term) (h : Typed [Ty.content] t Ty.unit), CutFree h) → ¬ VLeteArm) :=
  ⟨fun hL => unitContent_implies_core (VLeteArm_implies_unitContent hL),
   fun ⟨t, h, hcf⟩ => core_inhabitant_refutes_VLeteArm h hcf⟩

/-! ## J. The type-dead half of the body's dispatch (PROVEN) -/

theorem typeK_ne_tensor (a b : Ty) : ¬ TypeK (Ty.tensor a b) := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_later (a : Ty) : ¬ TypeK (Ty.later a) := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_stream : ¬ TypeK Ty.stream := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_trace : ¬ TypeK Ty.trace := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_knower : ¬ TypeK Ty.knower := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_knowledge : ¬ TypeK Ty.knowledge := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_value : ¬ TypeK Ty.value := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_content : ¬ TypeK Ty.content := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_gen : ¬ TypeK (Ty.arrow Ty.knower (Ty.tensor Ty.content Ty.knower)) := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_red : ¬ TypeK (Ty.arrow Ty.stream Ty.knowledge) := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_obj : ¬ TypeK (Ty.arrow Ty.stream Ty.value) := by
  intro h; simp [TypeK, VanChain] at h

theorem typeK_ne_terminate : ¬ TypeK (Ty.arrow Ty.knower Ty.trace) := by
  intro h; simp [TypeK, VanChain] at h

/-- **The body's root classification**: a `Typed` derivation with a `TypeK`
conclusion and a body context (length ≥ 2) can only be headed by
`lam`/`app`/`fix`/`lete`/`weak`/`contr` — `var` and `unit` need a
length-1/0 context, `pair`/`next`/`cons`/`nil`/`snoc` and the four
constants conclude types outside `TypeK`. This is the "type/gate-dead"
half of the lete residual, kernel-checked: the residual's remaining work
is exactly `lam`/`app`/`fix`/`lete` at head-extended contexts. -/
theorem typeK_roots {Δ : List Ty} {τ : Ty} {t : Term}
    (h : Typed Δ t τ) (hK : TypeK τ) (hlen : 2 ≤ Δ.length) :
    (∃ (a : Ty) (body : Term), t = Term.lam a body) ∨
    (∃ fn arg, t = Term.app fn arg) ∨
    (∃ body, t = Term.fix body) ∨
    (∃ (s : Term) (body : Term), t = Term.lete s body) ∨
    (∃ (k : Ty) (Γ' : List Ty) (t' : Term), k.isLinear = false ∧
      t = Term.liftAt 0 t' ∧ Nonempty (Typed Γ' t' τ)) ∨
    (∃ (k : Ty) (Γ' : List Ty), k.isLinear = false ∧
      Nonempty (Typed (k :: k :: Γ') (Term.mergeAt 0 t) τ)) := by
  cases h with
  | var => exact absurd hlen (by simp)
  | lam _ => exact Or.inl ⟨_, _, rfl⟩
  | app _ _ _ => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  | pair _ _ _ => exact absurd hK (typeK_ne_tensor _ _)
  | lete _ _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
  | unit => exact absurd hlen (by simp)
  | next _ => exact absurd hK (typeK_ne_later _)
  | fix _ _ => exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
  | cons _ _ _ => exact absurd hK typeK_ne_stream
  | nil => exact absurd hK typeK_ne_trace
  | snoc _ _ _ => exact absurd hK typeK_ne_trace
  | gen => exact absurd hK typeK_ne_gen
  | red => exact absurd hK typeK_ne_red
  | obj => exact absurd hK typeK_ne_obj
  | terminate => exact absurd hK typeK_ne_terminate
  | contr hk hpre =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, hk, ⟨hpre⟩⟩))))
  | weak hk hpre =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, hk, rfl, ⟨hpre⟩⟩))))



/-! ## The core-strength boundary (probe scCoreV3, transfer-landed)

The five scrutinee-head residuals are CORE-STRENGTH, each direction
kernel-measured: every residual's hypothesis set contains an image of
the core (one cut-free [content] ⊢ unit witness builds each refuting
instance), so Residual → LamArm for all five, and any core refutation
refutes all five. The closed-killer lemma the residual-discharge would
need is IMPLIED by the residual (pairArmI_implies_noClosedKiller) —
there is no rung below the core. The decomposition itself is sharp:
CoreLete ↔ CoreLeteI ∧ CoreLeteII, the app arms dead by type/atomicity
arithmetic, and the escape frames inhabited cut-free ([unit] ⊢ unit,
the closed killer body at [ACU, content], the token scrutinee). The
vanishing side's entire remaining content is the single judgment
[content] ⊢ unit at the cut-free grain; everything else is priced. -/


/-! ## 0. List arithmetic (self-contained) -/

/-- `Γ₁ ++ Γ₂ = [c]` has exactly two shapes. -/
theorem coreV3_append_eq_singleton {Γ₁ Γ₂ : List Ty} {c : Ty}
    (h : Γ₁ ++ Γ₂ = [c]) : (Γ₁ = [c] ∧ Γ₂ = []) ∨ (Γ₁ = [] ∧ Γ₂ = [c]) := by
  cases Γ₁ with
  | nil => exact Or.inr ⟨rfl, by simpa using h⟩
  | cons x xs =>
      cases xs with
      | nil =>
          have hx : x = c := by
            simpa only [List.cons_append, List.nil_append] using (List.cons.inj h).1
          subst hx
          exact Or.inl ⟨rfl, by
            have hh := h
            simp only [List.cons_append, List.nil_append] at hh
            exact List.cons.inj hh |>.2⟩
      | cons y ys =>
          have hlen := congrArg List.length h
          simp only [List.cons_append, List.length_append, List.length_cons,
            List.length_nil] at hlen
          omega

/-- `Γ₁ ++ Γ₂ = []` forces both pieces empty. -/
theorem coreV3_split_nil {Γ₁ Γ₂ : List Ty} (h : Γ₁ ++ Γ₂ = []) :
    Γ₁ = [] ∧ Γ₂ = [] := by
  cases Γ₁ with
  | nil => exact ⟨rfl, by simpa using h⟩
  | cons x xs =>
      simp only [List.cons_append] at h
      cases h

/-- At a context whose split is `[content]`, a leading position IS `content`. -/
theorem coreV3_head_is_content {k : Ty} {Γ Δ : List Ty}
    (hs : (k :: Γ) ++ Δ = [Ty.content]) : k = Ty.content := by
  simp only [List.cons_append] at hs
  exact (List.cons.inj hs).1

/-- `[content]` IS a primed frame: the in-tree chase engine applies (the
`scCoreV2` transfer lemma). -/
theorem coreV3_marchCtx_content : MarchCtx' [Ty.content] :=
  marchCtx'_cons marchOK'_content marchCtx'_nil

/-- Every `NeedsK`-typed derivation at `[content]` is dead (in-tree primed engine). -/
theorem no_needsK_at_content {τ : Ty} (hK : NeedsK τ) {t : Term}
    (h : Typed [Ty.content] t τ) : False :=
  needsK_val_dead_at_primed coreV3_marchCtx_content hK h

/-- The instance the `tensor`-conclusion arm needs: no `[content] ⊢ knower`. -/
theorem no_knower_at_content {t : Term} (h : Typed [Ty.content] t Ty.knower) : False :=
  no_needsK_at_content (by unfold NeedsK; trivial) h

/-! ## 1. Atomic heads at a `content` frame / with a `unit` conclusion -/

/-- `unit` is non-linear (the gate `weak`/`contr` need). -/
theorem coreV3_unit_not_linear : Ty.unit.isLinear = false := rfl

/-- **No atomic function is typed at `[content]` with an arrow type.** -/
theorem no_atomic_arrow_at_content {a b : Ty} {fn : Term}
    (hf : Typed [Ty.content] fn (Ty.arrow a b)) (hatom : IsAtomic fn) : False := by
  cases hf with
  | lam _ => exact absurd hatom isAtomic_ne_lam
  | app _ _ => exact absurd hatom isAtomic_ne_app
  | fix _ _ => exact absurd hatom isAtomic_ne_fix
  | lete _ _ _ => exact absurd hatom isAtomic_ne_lete
  | contr hk hp => exact content_linear_ne_false hk
  | weak hk hp => exact content_linear_ne_false hk

/-- **THE `app` ARM AT `[content] ⊢ unit`**: dead for every atomic head. -/
theorem no_cut_free_app_unit_at_content {X : Ty} {fn arg : Term} {Γ Δ : List Ty}
    (hf : Typed Γ fn (Ty.arrow X Ty.unit)) (ha : Typed Δ arg X)
    (hs : Γ ++ Δ = [Ty.content]) (hatom : IsAtomic fn) : False := by
  cases hf with
  | var =>
      have h1 : Ty.arrow X Ty.unit = Ty.content := by
        have hh := hs
        simp only [List.cons_append, List.nil_append] at hh
        exact (List.cons.inj hh).1
      exact Ty.noConfusion h1
  | lam _ => exact absurd hatom isAtomic_ne_lam
  | app _ _ => exact absurd hatom isAtomic_ne_app
  | fix _ _ => exact absurd hatom isAtomic_ne_fix
  | lete _ _ _ => exact absurd hatom isAtomic_ne_lete
  | contr hk hp => exact content_linear_ne_false (coreV3_head_is_content hs ▸ hk)
  | weak hk hp => exact content_linear_ne_false (coreV3_head_is_content hs ▸ hk)

/-- **No cut-free application at `[content]` has a `content`-typed argument.** -/
theorem no_content_arg_app_at_content {σ : Ty} {fn arg : Term} {Γ Δ : List Ty}
    (hf : Typed Γ fn (Ty.arrow Ty.content σ)) (ha : Typed Δ arg Ty.content)
    (hs : Γ ++ Δ = [Ty.content]) (hatom : IsAtomic fn) : False := by
  rcases coreV3_append_eq_singleton (c := Ty.content) hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2
    exact no_atomic_arrow_at_content hf hatom
  · subst h1; subst h2
    cases hf with
    | lam _ => exact absurd hatom isAtomic_ne_lam
    | app _ _ => exact absurd hatom isAtomic_ne_app
    | fix _ _ => exact absurd hatom isAtomic_ne_fix
    | lete _ _ _ => exact absurd hatom isAtomic_ne_lete

/-! ## 2. The root of `[content] ⊢ unit` is `lete` -/

/-- **`[content] ⊢ unit` IS LETE-HEADED** (re-derived self-contained). -/
theorem core_lete_headed : ∀ (t : Term) (h : Typed [Ty.content] t Ty.unit), CutFree h →
    ∃ (Γ₁ Γ₂ : List Ty) (a b : Ty) (scr body : Term)
      (ht : Typed Γ₁ scr (Ty.tensor a b)) (hb : Typed (b :: a :: Γ₂) body Ty.unit),
      Γ₁ ++ Γ₂ = [Ty.content] ∧ CutFree ht ∧ CutFree hb := by
  intro t h hcf
  cases h with
  | app hf ha hs => exact (no_cut_free_app_unit_at_content hf ha hs hcf.2.2).elim
  | lete ht hb hs => exact ⟨_, _, _, _, _, _, ht, hb, hs, hcf.1, hcf.2⟩
  | fix hnl hb => exact (content_linear_ne_false (hnl 0 Ty.content (by rfl))).elim
  | contr hk hp => exact (content_linear_ne_false hk).elim
  | weak hk hp => exact (content_linear_ne_false hk).elim

/-- The core, class-free (`scCoreV2`'s `CoreLete`). -/
def CoreLete : Prop :=
  ∀ {Γ₁ Γ₂ : List Ty} {a b : Ty} {t body : Term}
    (ht : Typed Γ₁ t (Ty.tensor a b)) (hb : Typed (b :: a :: Γ₂) body Ty.unit),
    Γ₁ ++ Γ₂ = [Ty.content] → CutFree ht → CutFree hb → False

/-- `CoreLete` gives `LamArm` (via §2) — the decomposition is sound. -/
theorem lamArm_of_coreLete (h : CoreLete) : ∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit),
    CutFree ht → False := by
  intro t ht hcf
  obtain ⟨Γ₁, Γ₂, a, b, scr, body, ht', hb', hs, hcfT, hcfB⟩ := core_lete_headed t ht hcf
  exact h ht' hb' hs hcfT hcfB

/-! ## 3. The two shapes and the five residuals -/

def CoreLeteI : Prop :=
  ∀ {a b : Ty} {t body : Term}
    (ht : Typed [Ty.content] t (Ty.tensor a b)) (hb : Typed (b :: a :: []) body Ty.unit),
    CutFree ht → CutFree hb → False

def CoreLeteII : Prop :=
  ∀ {a b : Ty} {t body : Term}
    (ht : Typed [] t (Ty.tensor a b)) (hb : Typed (b :: a :: [Ty.content]) body Ty.unit),
    CutFree ht → CutFree hb → False

theorem coreLete_iff_shapes : CoreLete ↔ (CoreLeteI ∧ CoreLeteII) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b t body ht hb hcfT hcfB
      exact h ht hb (by simp) hcfT hcfB
    · intro a b t body ht hb hcfT hcfB
      exact h ht hb (by simp) hcfT hcfB
  · intro ⟨hI, hII⟩ Γ₁ Γ₂ a b t body ht hb hs hcfT hcfB
    rcases coreV3_append_eq_singleton (c := Ty.content) hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; exact hI ht hb hcfT hcfB
    · subst h1; subst h2; exact hII ht hb hcfT hcfB

/-- The `app` arm at a `tensor` conclusion over `[content]`. -/
theorem coreV3_app_scrut_dead_token {a b x : Ty} {fn arg : Term} {Γ₁ Δ : List Ty}
    (hf : Typed Γ₁ fn (Ty.arrow x (Ty.tensor a b))) (ha : Typed Δ arg x)
    (hs : Γ₁ ++ Δ = [Ty.content]) (hatom : IsAtomic fn) : False := by
  cases hf with
  | var =>
      have h1 : Ty.arrow x (Ty.tensor a b) = Ty.content := by
        have hh := hs
        simp only [List.cons_append, List.nil_append] at hh
        exact (List.cons.inj hh).1
      exact Ty.noConfusion h1
  | lam _ => exact absurd hatom isAtomic_ne_lam
  | app _ _ => exact absurd hatom isAtomic_ne_app
  | fix _ _ => exact absurd hatom isAtomic_ne_fix
  | lete _ _ _ => exact absurd hatom isAtomic_ne_lete
  | gen =>
      have hΔ : Δ = [Ty.content] := by simpa using hs
      subst hΔ
      exact no_knower_at_content ha
  | contr hk hp => exact content_linear_ne_false (coreV3_head_is_content hs ▸ hk)
  | weak hk hp => exact content_linear_ne_false (coreV3_head_is_content hs ▸ hk)

/-- The `app` arm at a CLOSED `tensor` scrutinee. -/
theorem coreV3_app_scrut_dead_closed {a b x : Ty} {fn arg : Term} {Γ₁ Δ : List Ty}
    (hf : Typed Γ₁ fn (Ty.arrow x (Ty.tensor a b))) (ha : Typed Δ arg x)
    (hs : Γ₁ ++ Δ = []) (hatom : IsAtomic fn) : False := by
  cases hf with
  | var =>
      simp only [List.cons_append, List.nil_append] at hs
      exact List.cons_ne_nil _ _ hs
  | lam _ => exact absurd hatom isAtomic_ne_lam
  | app _ _ => exact absurd hatom isAtomic_ne_app
  | fix _ _ => exact absurd hatom isAtomic_ne_fix
  | lete _ _ _ => exact absurd hatom isAtomic_ne_lete
  | gen =>
      have hΔ : Δ = [] := by simpa using hs
      subst hΔ
      exact no_closed_knower ha
  | contr hk hp =>
      simp only [List.cons_append] at hs
      exact List.cons_ne_nil _ _ hs
  | weak hk hp =>
      simp only [List.cons_append] at hs
      exact List.cons_ne_nil _ _ hs

/-- Shape I, `pair`-headed scrutinee. -/
def PairArmI : Prop :=
  ∀ {a b : Ty} {l r body : Term} {Γ₁ Γ₂ : List Ty}
    (hl : Typed Γ₁ l a) (hr : Typed Γ₂ r b) (hs : Γ₁ ++ Γ₂ = [Ty.content])
    (hb : Typed (b :: a :: []) body Ty.unit),
    CutFree hl → CutFree hr → CutFree hb → False

/-- Shape I, `lete`-headed scrutinee. -/
def LeteScrutI : Prop :=
  ∀ {a b x y : Ty} {scr body' body : Term} {Γ₁ Γ₂ : List Ty}
    (ht : Typed Γ₁ scr (Ty.tensor x y))
    (hb' : Typed (y :: x :: Γ₂) body' (Ty.tensor a b))
    (hs : Γ₁ ++ Γ₂ = [Ty.content]) (hb : Typed (b :: a :: []) body Ty.unit),
    CutFree ht → CutFree hb' → CutFree hb → False

/-- Shape II, `pair`-headed scrutinee (both comps closed). -/
def PairArmII : Prop :=
  ∀ {a b : Ty} {l r body : Term}
    (hl : Typed [] l a) (hr : Typed [] r b)
    (hb : Typed (b :: a :: [Ty.content]) body Ty.unit),
    CutFree hl → CutFree hr → CutFree hb → False

/-- Shape II, `lete`-headed scrutinee (closed). -/
def LeteScrutII : Prop :=
  ∀ {a b x y : Ty} {scr body' body : Term} {Γ₁ Γ₂ : List Ty}
    (ht : Typed Γ₁ scr (Ty.tensor x y))
    (hb' : Typed (y :: x :: Γ₂) body' (Ty.tensor a b))
    (hs : Γ₁ ++ Γ₂ = ([] : List Ty)) (hb : Typed (b :: a :: [Ty.content]) body Ty.unit),
    CutFree ht → CutFree hb' → CutFree hb → False

/-- Shape II, `fix`-headed scrutinee (the closed `▷`-stack). -/
def FixScrutII : Prop :=
  ∀ {a b : Ty} {body' body : Term}
    (hnl : AllNonLinear ([] : List Ty))
    (hb' : Typed [] body' (Ty.arrow (Ty.later (Ty.tensor a b)) (Ty.tensor a b)))
    (hb : Typed (b :: a :: [Ty.content]) body Ty.unit),
    CutFree hb' → CutFree hb → False

/-- **THE REDUCTION**: the five residuals prove the core. -/
theorem coreLete_of_five (hPairI : PairArmI) (hLeteI : LeteScrutI)
    (hPairII : PairArmII) (hLeteII : LeteScrutII) (hFixII : FixScrutII) : CoreLete := by
  have hI : CoreLeteI := by
    intro a b t body ht hb hcfT hcfB
    cases ht with
    | pair hl hr hs => exact hPairI hl hr hs hb hcfT.1 hcfT.2 hcfB
    | app hf ha hs => exact coreV3_app_scrut_dead_token hf ha hs hcfT.2.2
    | lete ht' hb' hs => exact hLeteI ht' hb' hs hb hcfT.1 hcfT.2 hcfB
    | fix hnl hb' => exact content_linear_ne_false (hnl 0 Ty.content (by rfl))
    | contr hk hp => exact content_linear_ne_false hk
    | weak hk hp => exact content_linear_ne_false hk
  have hII : CoreLeteII := by
    intro a b t body ht hb hcfT hcfB
    cases ht with
    | pair hl hr hs =>
        obtain ⟨h1, h2⟩ := coreV3_split_nil hs
        subst h1; subst h2
        exact hPairII hl hr hb hcfT.1 hcfT.2 hcfB
    | app hf ha hs => exact coreV3_app_scrut_dead_closed hf ha hs hcfT.2.2
    | lete ht' hb' hs => exact hLeteII ht' hb' hs hb hcfT.1 hcfT.2 hcfB
    | fix hnl hb' => exact hFixII hnl hb' hb hcfT hcfB
  intro Γ₁ Γ₂ a b t body ht hb hs hcfT hcfB
  rcases coreV3_append_eq_singleton (c := Ty.content) hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact hI ht hb hcfT hcfB
  · subst h1; subst h2; exact hII ht hb hcfT hcfB

/-! ## 4. Why no frame class closes the residuals: the escape frames are
INHABITED, cut-free -/

/-- MEASURED: `[unit] ⊢ unit` — a token-free frame is not dead. -/
def unitAtUnit : Typed [Ty.unit] Term.unit Ty.unit := Typed.weak coreV3_unit_not_linear Typed.unit

theorem unitAtUnit_cutFree : CutFree unitAtUnit := trivial

/-- MEASURED: `[arrow unit unit, unit] ⊢ unit` — a closed-supplement frame fires
a sibling comp legally. -/
def unitAtArrowUnit : Typed [Ty.arrow Ty.unit Ty.unit, Ty.unit]
    (Term.app (Term.var 0) Term.unit) Ty.unit :=
  Typed.app (E := [Ty.arrow Ty.unit Ty.unit, Ty.unit]) Typed.var unitAtUnit rfl

theorem unitAtArrowUnit_cutFree : CutFree unitAtArrowUnit := ⟨trivial, trivial, Or.inl rfl⟩

/-- MEASURED: the token is a legal `content ⊗ unit` scrutinee, cut-free. -/
def scrutToken : Typed [Ty.content] (Term.pair (Term.var 0) Term.unit)
    (Ty.tensor Ty.content Ty.unit) :=
  Typed.pair Typed.var Typed.unit rfl

theorem scrutToken_cutFree : CutFree scrutToken := ⟨trivial, trivial⟩

/-- MEASURED: the killer comps' BODY is cut-free at exactly the killer's frame —
the pair arm's body side is never the obstruction. -/
def coreV3_killerBody : Typed [Ty.arrow Ty.content Ty.unit, Ty.content]
    (Term.app (Term.var 0) (Term.var 0)) Ty.unit :=
  Typed.app Typed.var Typed.var rfl

theorem coreV3_killerBody_cutFree : CutFree coreV3_killerBody := ⟨trivial, trivial, Or.inl rfl⟩

/-- A closed content-killer yields a cut-free `[content] ⊢ unit` outright. -/
def coreV3_witness (K : Term) (hK : Typed [] K (Ty.arrow Ty.content Ty.unit)) :
    Typed [Ty.content]
      (Term.lete (Term.pair (Term.var 0) K) (Term.app (Term.var 0) (Term.var 0)))
      Ty.unit :=
  Typed.lete (Typed.pair Typed.var hK rfl) (Typed.app Typed.var Typed.var rfl) rfl

theorem coreV3_witness_cutFree {K : Term} (hK : Typed [] K (Ty.arrow Ty.content Ty.unit))
    (hcfK : CutFree hK) : CutFree (coreV3_witness K hK) :=
  ⟨⟨trivial, hcfK⟩, ⟨trivial, trivial, Or.inl rfl⟩⟩

/-! ## 5. THE MEASUREMENT: `Residual → LamArm` for all five

Each proof is a cut-free construction: from one cut-free `[content] ⊢ unit`
derivation `h`, build the residual's refuting data. -/

/-- **5.1 `PairArmI → LamArm`.** -/
theorem pairArmI_implies_lamArm (hA : PairArmI) :
    ∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False := by
  intro t ht hcf
  exact hA (a := Ty.content) (b := Ty.unit) (l := Term.var 0) (r := Term.unit)
    (body := Term.liftAt 0 t) (Γ₁ := [Ty.content]) (Γ₂ := [])
    Typed.var Typed.unit rfl (Typed.weak coreV3_unit_not_linear ht)
    trivial trivial hcf

/-- **5.2 `PairArmII → LamArm`** (closed comps; token in the body via two inert
`unit` supplements). -/
theorem pairArmII_implies_lamArm (hA : PairArmII) :
    ∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False := by
  intro t ht hcf
  exact hA (a := Ty.unit) (b := Ty.unit) (l := Term.unit) (r := Term.unit)
    (body := Term.liftAt 0 (Term.liftAt 0 t))
    Typed.unit Typed.unit
    (Typed.weak coreV3_unit_not_linear (Typed.weak coreV3_unit_not_linear ht))
    trivial trivial hcf

/-- **5.3 `LeteScrutI → LamArm`** (token in the scrutinee's piece). -/
theorem leteScrutI_implies_lamArm (hA : LeteScrutI) :
    ∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False := by
  intro t ht hcf
  exact hA (a := Ty.unit) (b := Ty.unit) (x := Ty.content) (y := Ty.unit)
    (scr := Term.pair (Term.var 0) Term.unit)
    (body' := Term.pair (Term.liftAt 0 t) Term.unit)
    (body := Term.liftAt 0 (Term.liftAt 0 Term.unit))
    (Γ₁ := [Ty.content]) (Γ₂ := [])
    (Typed.pair Typed.var Typed.unit rfl)
    (Typed.pair (Typed.weak coreV3_unit_not_linear ht) Typed.unit rfl)
    rfl (Typed.weak coreV3_unit_not_linear (Typed.weak coreV3_unit_not_linear Typed.unit))
    ⟨trivial, trivial⟩ ⟨hcf, trivial⟩ trivial

/-- **5.4 `LeteScrutII → LamArm`** (closed scrutinee; token in the body). -/
theorem leteScrutII_implies_lamArm (hA : LeteScrutII) :
    ∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False := by
  intro t ht hcf
  exact hA (a := Ty.unit) (b := Ty.unit) (x := Ty.unit) (y := Ty.unit)
    (scr := Term.pair Term.unit Term.unit)
    (body' := Term.pair (Term.liftAt 0 Term.unit) Term.unit)
    (body := Term.liftAt 0 (Term.liftAt 0 t))
    (Γ₁ := []) (Γ₂ := [])
    (Typed.pair Typed.unit Typed.unit rfl)
    (Typed.pair (Typed.weak coreV3_unit_not_linear Typed.unit)
      (Typed.weak coreV3_unit_not_linear Typed.unit) rfl)
    rfl (Typed.weak coreV3_unit_not_linear (Typed.weak coreV3_unit_not_linear ht))
    ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ hcf

/-- **5.5 `FixScrutII → LamArm`** (payload `unit ⊗ unit`; `▷(unit⊗unit)` is
non-linear, so the closed body is a `weak`-drop). -/
theorem fixScrutII_implies_lamArm (hA : FixScrutII) :
    ∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False := by
  intro t ht hcf
  refine hA (a := Ty.unit) (b := Ty.unit)
    (body' := Term.lam (Ty.later (Ty.tensor Ty.unit Ty.unit))
      (Term.pair (Term.liftAt 0 Term.unit) Term.unit))
    (body := Term.liftAt 0 (Term.liftAt 0 t)) ?_ ?_ ?_ ?_ ?_
  · intro i b hb
    rw [List.get?_nil'] at hb
    exact absurd hb (by simp)
  · exact Typed.lam (Typed.pair
      (Typed.weak (by rfl : (Ty.later (Ty.tensor Ty.unit Ty.unit)).isLinear = false) Typed.unit)
      Typed.unit rfl)
  · exact Typed.weak coreV3_unit_not_linear (Typed.weak coreV3_unit_not_linear ht)
  · exact ⟨trivial, trivial⟩
  · exact hcf

/-- **5.6 THE BRIEF'S ESCAPE, PRICED**: any cut-free `[content] ⊢ a` paired with
a cut-free closed `arrow a unit` refutes `PairArmI`.  So the pair arm's killer
branch is the "closed killer over a `[content]`-derivable domain" family — the
family whose `a := content` case is the theorem itself. -/
theorem pairArmI_refuted_of_closedKiller {a : Ty} {l K : Term}
    (hl : Typed [Ty.content] l a) (hK : Typed [] K (Ty.arrow a Ty.unit))
    (hcfL : CutFree hl) (hcfK : CutFree hK) (hA : PairArmI) : False :=
  hA (a := a) (b := Ty.arrow a Ty.unit) (l := l) (r := K)
    (body := Term.app (Term.var 0) (Term.var 0))
    (Γ₁ := [Ty.content]) (Γ₂ := [])
    hl hK rfl (Typed.app Typed.var Typed.var rfl)
    hcfL hcfK ⟨trivial, trivial, Or.inl rfl⟩

/-- **5.7 AND `LamArm` IS THE `a := content` CASE**: `LamArm` implies no cut-free
closed `arrow content unit` exists — so the "closed-killer lemma" the brief
plans to use *is* the theorem. -/
theorem lamArm_implies_no_closedKiller (h : ∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit),
    CutFree ht → False) :
    ∀ (K : Term) (hK : Typed [] K (Ty.arrow Ty.content Ty.unit)), CutFree hK → False :=
  fun K hK hcfK => h _ (coreV3_witness K hK) (coreV3_witness_cutFree hK hcfK)

/-- **5.8 THE BRIEF'S "CIRCULARITY-RESOLUTION" IS CIRCULAR.**  `PairArmI`
IMPLIES the closed-killer lemma (the very lemma the brief plans to use to kill
its killer branches): instantiate 5.6 at `a := content`, whose `[content] ⊢ a`
witness is the free cut-free `var 0`.  So the closed-killer lemma is a
CONSEQUENCE of the residual, not a rung below it.
-/
theorem pairArmI_implies_noClosedKiller (hA : PairArmI) :
    ∀ (K : Term) (hK : Typed [] K (Ty.arrow Ty.content Ty.unit)), CutFree hK → False :=
  fun K hK hcfK =>
    pairArmI_refuted_of_closedKiller (a := Ty.content) Typed.var hK trivial hcfK hA

/-! ## 6. The decomposition is an equivalence at the difficulty level -/

/-- **THE ROUND'S VERDICT, as a theorem.** -/
theorem residuals_are_core_strength :
    (PairArmI → (∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False)) ∧
    (LeteScrutI → (∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False)) ∧
    (PairArmII → (∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False)) ∧
    (LeteScrutII → (∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False)) ∧
    (FixScrutII → (∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False)) :=
  ⟨pairArmI_implies_lamArm, leteScrutI_implies_lamArm, pairArmII_implies_lamArm,
    leteScrutII_implies_lamArm, fixScrutII_implies_lamArm⟩

/-- The five, jointly, prove the core (§3) — with §6's theorem, the
decomposition is an equivalence at the difficulty level. -/
theorem five_implies_lamArm (hPairI : PairArmI) (hLeteI : LeteScrutI)
    (hPairII : PairArmII) (hLeteII : LeteScrutII) (hFixII : FixScrutII) :
    ∀ (t : Term) (ht : Typed [Ty.content] t Ty.unit), CutFree ht → False :=
  lamArm_of_coreLete (coreLete_of_five hPairI hLeteI hPairII hLeteII hFixII)

/-! ## 7. Axiom audit -/


/-! ## The class-frame boundary (probe scCoreV5, transfer-landed)

The corrected mutual's measurements: (Core)-at-class-frames is REFUTED
at the kernel — [arrow trace unit, content] ⊢ app (var 0) (snoc nil
(var 0)) : unit is cut-free (arrow trace unit ∈ ClosedLive by the
definition; the trace-killer eats a freshly minted trace, the token
pays) — the same boundary disease as round-4's (Tensor), one level up.
The (ClosedKiller) generalisation is likewise refuted
([arrow trace unit] ⊢ app (var 0) nil : unit — no token at all). What
survives and is proven: no_content_at_closedLive (the type-level kill,
no CutFree needed), the lam-link (noClosedKiller_of_arms), the class-
free narrowing (LamArm ≡ CoreLete ≡ CoreAt content by Iff.rfl), and
LeteArm ≡ LeteArmClosed (the closed scrutinee, body at [b,a] ⊢
arrow content unit, NO CutFree — the unrestricted Typed-level core).
The exact frames of the seven residuals are pinned in the probe. -/


/-! ## 0. The brief's classes, as definitions -/

/-- `ClosedLive`, exactly as the brief defines it (the `later`/list clauses
of the brief's `{later T | VanChain T}` are handled separately by `ClassPos`). -/
inductive ClosedLive : Ty → Prop
  | unit : ClosedLive Ty.unit
  | trace : ClosedLive Ty.trace
  | later {a : Ty} (h : ClosedLive a) : ClosedLive (Ty.later a)
  | arrow {a b : Ty} (ha : ClosedLive a) (hb : ClosedLive b) : ClosedLive (Ty.arrow a b)
  | tensor {a b : Ty} (ha : ClosedLive a) (hb : ClosedLive b) : ClosedLive (Ty.tensor a b)

/-- The brief's class position: `content ∪ ClosedLive ∪ later-of-VanChain`. -/
def ClassPos (b : Ty) : Prop :=
  b = Ty.content ∨ ClosedLive b ∨ ∃ T : Ty, b = Ty.later T ∧ VanChain T

/-- The brief's class frame: all positions in the class, at least one content. -/
def ClassFrame (Γ : List Ty) : Prop :=
  (∀ (i : Nat) (b : Ty), Γ[i]? = some b → ClassPos b) ∧ HasContent Γ

/-! ## 1. `(ContentAtClosedLive)` — the counting base, PROVED unconditionally

The engine is the in-tree `no_content_nosupply` (`cprop` + the contrapositive
of "the context supplies nothing"), preceded by the class computation
`ClosedLive ⟹ ¬ CSupply`.  Note the `later` case of the brief's class is
free: `NeedsC`/`NeedsK` are opaque under `▷` (both `False`), so a delayed
position never supplies anything.  -/

/-- `ClosedLive` positions are never content-supplying. -/
theorem closedLive_notCSupply {τ : Ty} (h : ClosedLive τ) : ¬ CSupply τ := by
  induction h with
  | unit =>
      intro hcs
      rcases hcs with hc | hk
      · exact hc
      · exact hk
  | trace =>
      intro hcs
      rcases hcs with hc | hk
      · exact hc
      · exact hk
  | later ha ih =>
      intro hcs
      rcases hcs with hc | hk
      · exact hc
      · exact hk
  | arrow ha hb iha ihb =>
      intro hcs
      rcases hcs with hc | hk
      · exact ihb (Or.inl hc.1)
      · exact ihb (Or.inr hk.1)
  | tensor ha hb iha ihb =>
      intro hcs
      rcases hcs with hc | hk
      · rcases hc with hc | hc
        · exact iha (Or.inl hc)
        · exact ihb (Or.inl hc)
      · rcases hk with hk | hk
        · exact iha (Or.inr hk)
        · exact ihb (Or.inr hk)

/-- The delay supplies nothing (unconditional: `later` is opaque to both
need-predicates).  A cheap strengthening reused below. -/
theorem later_notCSupply (T : Ty) : ¬ CSupply (Ty.later T) := by
  intro hcs
  rcases hcs with hc | hk
  · exact hc
  · exact hk

/-- **THE COUNTING BASE.**  No content-valued derivation at a context whose
every position is `ClosedLive`.  `CutFree` is not even needed — this is the
type-level kill, the same shape as the in-tree `no_content_at_later_stream`
but at the brief's whole class. -/
theorem no_content_at_closedLive {Γ : List Ty} {t : Term}
    (h : Typed Γ t Ty.content)
    (hl : ∀ (i : Nat) (b : Ty), Γ[i]? = some b → ClosedLive b) : False :=
  no_content_nosupply h
    (fun i b hpos hcs => closedLive_notCSupply (hl i b hpos) hcs)

/-! ## 2. The brief's `(Core)` — REFUTED at class frames

The witness, at `[arrow trace unit, content]`:

  `app (var 0) (snoc nil (var 0)) : unit`

`var 0` is the trace-killer (`arrow trace unit ∈ ClosedLive`); the argument
snocs the token into a fresh trace (`nil` mints it, the token is the
archived content).  Cut-free: the sole application's function is `var 0`.
Both positions are in the brief's class and position 1 is the content, so
this IS a class frame.  Hence "no cut-free `unit` at the class frames" is
FALSE — the brief's `(Core)` cannot be the mutual's first component. -/

/-- The witness frame. -/
def atuFrame : List Ty := [Ty.arrow Ty.trace Ty.unit, Ty.content]

/-- The witness. -/
def atuWitness :
    Typed atuFrame (Term.app (Term.var 0) (Term.snoc Term.nil (Term.var 0))) Ty.unit :=
  Typed.app (E := atuFrame) (Γ := [Ty.arrow Ty.trace Ty.unit]) (Δ := [Ty.content])
    (a := Ty.trace) (b := Ty.unit) Typed.var
    (Typed.snoc (E := [Ty.content]) (Γ := ([] : List Ty)) (Δ := [Ty.content])
      (t := Term.nil) (u := Term.var 0) (ht := Typed.nil) (hu := Typed.var) rfl)
    rfl

theorem atuWitness_cutFree : CutFree atuWitness := ⟨trivial, ⟨trivial, trivial⟩, Or.inl rfl⟩

theorem atuFrame_class : ClassFrame atuFrame := by
  constructor
  · intro i b hpos
    cases i with
    | zero =>
        rw [show atuFrame[0]? = some (Ty.arrow Ty.trace Ty.unit) from rfl] at hpos
        injection hpos with he
        subst he
        exact Or.inr (Or.inl (ClosedLive.arrow ClosedLive.trace ClosedLive.unit))
    | succ i1 =>
        cases i1 with
        | zero =>
            rw [show atuFrame[1]? = some Ty.content from rfl] at hpos
            injection hpos with he
            subst he
            exact Or.inl rfl
        | succ i2 =>
            have hlt : i2 + 2 < atuFrame.length := List.get?_some_lt hpos
            have hlen : atuFrame.length = 2 := rfl
            omega
  · exact ⟨1, by rw [show atuFrame[1]? = some Ty.content from rfl]⟩

/-- **THE BRIEF'S `(Core)` AT CLASS FRAMES IS FALSE.** -/
theorem coreAtClassFrames_refuted :
    ¬ (∀ (Γ : List Ty) (t : Term) (h : Typed Γ t Ty.unit),
        ClassFrame Γ → CutFree h → False) := by
  intro hall
  exact hall atuFrame _ atuWitness atuFrame_class atuWitness_cutFree

/-! ## 3. The generalisation the closed-killer reduction would need — REFUTED

The brief's step (B): "`[] ⊢ arrow b unit` λ-headed → body : unit at `[b]`
→ (A)-shaped at smaller size".  That step needs "no cut-free `unit` at
`[b]`" for the killer's DOMAIN `b`.  At `b = content` that is `LamArm`.
At other `b` it is FALSE: `[arrow trace unit] ⊢ app (var 0) nil` is
cut-free, with no token anywhere.  So the reduction step is sound exactly at
the instance that is the open theorem. -/

/-- `(Core)` at a fixed frame `[b]`. -/
def CoreAt (b : Ty) : Prop := ∀ (t : Term) (h : Typed [b] t Ty.unit), CutFree h → False

def atuOnlyFrame : List Ty := [Ty.arrow Ty.trace Ty.unit]

def atuOnlyWitness : Typed atuOnlyFrame (Term.app (Term.var 0) Term.nil) Ty.unit :=
  Typed.app (E := atuOnlyFrame) (Γ := atuOnlyFrame) (Δ := ([] : List Ty))
    (a := Ty.trace) (b := Ty.unit) Typed.var Typed.nil rfl

theorem atuOnlyWitness_cutFree : CutFree atuOnlyWitness := ⟨trivial, trivial, Or.inl rfl⟩

/-- The killer's-domain generalisation is FALSE (no token required at all). -/
theorem coreAt_not_all : ¬ (∀ b : Ty, CoreAt b) := by
  intro hall
  exact hall (Ty.arrow Ty.trace Ty.unit) _
    atuOnlyWitness atuOnlyWitness_cutFree

/-- And at `content` it is definitionally the open theorem. -/
theorem coreAt_content_iff_lamArm : CoreAt Ty.content ↔ LamArm := Iff.rfl

/-! ## 4. The one arm where the brief's machine bites: the `lam` peel

PROVED: the `lam`-headed closed killer's body is a `(Core)`-instance at
strictly smaller size, and `LamArm` kills it.  This is the brief's
"the lam body `[content] ⊢ unit` at size n−1 ⇒ (Core)-ih" step, and it is
sound — it just IS the open core. -/

/-- The size deficit: the `lam` root's body is strictly smaller. -/
theorem size_deficit_lam {body : Term} (hb : Typed [Ty.content] body Ty.unit) :
    size hb < size (Typed.lam (Γ := ([] : List Ty)) (a := Ty.content) (b := Ty.unit) hb) := by
  rw [size_lam]; omega

/-- `LamArm` kills the `lam`-headed closed killer. -/
theorem lamArm_kills_closedKiller_lam {body : Term} (hLam : LamArm)
    (h : Typed [] (Term.lam Ty.content body) (Ty.arrow Ty.content Ty.unit))
    (hcf : CutFree h) : False := by
  cases h with
  | lam hb => exact hLam body hb hcf

/-! ## 5. The closed-killer component, decomposed (the in-tree `root_gate`)

`(ClosedKiller)` = `lam`(the core, at smaller size) ∧ `FixArm` ∧ `LeteArm`.
Reading it as the brief does ("(ClosedKiller) proved at size n from
(Core)'s ih at size < n") is sound for the `lam` arm, and there the ih's
statement is `LamArm` — the component is a LINK to the core, not a rung
under it (in tree: `lamArm_implies_no_closedKiller` gives the other
direction, so the pair closes to an equivalence of difficulty). -/

/-- No closed cut-free `arrow content unit`. -/
def NoClosedKiller : Prop :=
  ∀ (K : Term) (hK : Typed [] K (Ty.arrow Ty.content Ty.unit)), CutFree hK → False

/-- The three arms give the closed-killer component (in-tree `root_gate` +
`no_vanishing_cf_of_arms` re-used verbatim). -/
theorem noClosedKiller_of_arms (hLam : LamArm) (hFix : FixArm) (hLete : LeteArm) :
    NoClosedKiller :=
  fun _ hK hcfK => no_vanishing_cf_of_arms hLam hFix hLete hK hcfK

/-- The `lam` arm of that decomposition, isolated: what `root_gate` leaves
open at the `lam` head is exactly the core, at a strictly smaller derivation. -/
theorem closedKiller_lam_arm_is_core (hLam : LamArm) {body : Term}
    (h : Typed [] (Term.lam Ty.content body) (Ty.arrow Ty.content Ty.unit))
    (hcf : CutFree h) : False :=
  lamArm_kills_closedKiller_lam hLam h hcf

/-! ## 6. The endpoint: `LamArm ↔ CoreLete` (the class apparatus is droppable)

Already half in tree (`lamArm_of_coreLete`); the converse is three lines.
So the whole open content is the single concrete shape `CoreLete` — and
via the in-tree `coreLete_iff_shapes`, its two shapes. -/

theorem coreLete_of_lamArm (h : LamArm) : CoreLete := by
  intro Γ₁ Γ₂ a b t body ht hb hs hcfT hcfB
  exact h (Term.lete t body) (Typed.lete ht hb hs) ⟨hcfT, hcfB⟩

/-- **THE ENDPOINT.** -/
theorem lamArm_iff_coreLete : LamArm ↔ CoreLete :=
  ⟨coreLete_of_lamArm, lamArm_of_coreLete⟩

/-! ## 7. The `lete` arm's exact frame: the closed one (frame narrowing)

`LeteArm` is stated over `(Γ₁, Γ₂)` plus the split equation `Γ₁ ++ Γ₂ = []`.
Since that equation forces both pieces empty, the arm is *equivalent* to its
closed instance — the body sits at the concrete frame `[b, a]`.  This pins
the residual's exact frame (and `LeteArm` carries no `CutFree` at all, so it
is the unrestricted Typed-level statement, as the record notes). -/

theorem append_eq_nil' {Γ₁ Γ₂ : List Ty} (hs : Γ₁ ++ Γ₂ = ([] : List Ty)) :
    Γ₁ = [] ∧ Γ₂ = [] := by
  cases Γ₁ with
  | nil => exact ⟨rfl, by simpa using hs⟩
  | cons hd tl => simp at hs

/-- `LeteArm` at its exact (closed) frame: the scrutinee closed, the body at
`[b, a]`, concluding `arrow content unit`. -/
def LeteArmClosed : Prop :=
  ∀ (a b : Ty) (t body : Term),
    Typed [] t (Ty.tensor a b) →
    Typed [b, a] body (Ty.arrow Ty.content Ty.unit) → False

theorem leteArm_iff_closed : LeteArm ↔ LeteArmClosed := by
  constructor
  · intro h a b t body ht hb
    exact h ht hb (by simp)
  · intro h Γ₁ Γ₂ a b t body ht hb hs
    obtain ⟨h1, h2⟩ := append_eq_nil' hs
    subst h1
    subst h2
    exact h a b t body ht hb

/-! ## 8. Falsify-first, re-run: the three escape frames are still inhabited

Re-measured here so the record carries them with this file.  Each is
cut-free, each fails to instantiate `LamArm` (wrong frame / right type but
no content position), and none is a witness for the negations of the arms. -/

/-- `[unit] ⊢ unit` (weakened closed unit). -/
def unitAtUnit' : Typed [Ty.unit] Term.unit Ty.unit :=
  Typed.weak (k := Ty.unit) (by decide) Typed.unit

theorem unitAtUnit'_cutFree : CutFree unitAtUnit' := trivial

/-- `[arrow unit unit, unit] ⊢ unit` (the killer of the weakened unit). -/
def unitAtArrowUnit' : Typed [Ty.arrow Ty.unit Ty.unit, Ty.unit]
    (Term.app (Term.var 0) (Term.liftAt 0 Term.unit)) Ty.unit :=
  Typed.app (E := [Ty.arrow Ty.unit Ty.unit, Ty.unit]) (Γ := [Ty.arrow Ty.unit Ty.unit])
    (Δ := [Ty.unit]) (a := Ty.unit) (b := Ty.unit) Typed.var
    (Typed.weak (k := Ty.unit) (by decide) Typed.unit) rfl

theorem unitAtArrowUnit'_cutFree : CutFree unitAtArrowUnit' :=
  ⟨trivial, trivial, Or.inl rfl⟩

/-- The killer-comp body `[arrow content unit, content] ⊢ unit` (the record's
`coreV3_killerBody`): the token dies legally into a killer. -/
def killerBody' : Typed [Ty.arrow Ty.content Ty.unit, Ty.content]
    (Term.app (Term.var 0) (Term.var 0)) Ty.unit :=
  Typed.app (E := [Ty.arrow Ty.content Ty.unit, Ty.content])
    (Γ := [Ty.arrow Ty.content Ty.unit]) (Δ := [Ty.content])
    (a := Ty.content) (b := Ty.unit) Typed.var Typed.var rfl

theorem killerBody'_cutFree : CutFree killerBody' := ⟨trivial, trivial, Or.inl rfl⟩

/-! ## 9. The measured ledger

Everything above, in one conjunction, so a reader can see the induction's
actual end state without reading the whole file. -/

theorem scCoreV5_ledger :
    -- (1) the counting base: PROVED, unconditional
    (∀ {Γ : List Ty} {t : Term} (_h : Typed Γ t Ty.content),
        (∀ (i : Nat) (b : Ty), Γ[i]? = some b → ClosedLive b) → False) ∧
    -- (2) the brief's `(Core)` at class frames: REFUTED
    (¬ (∀ (Γ : List Ty) (t : Term) (h : Typed Γ t Ty.unit),
        ClassFrame Γ → CutFree h → False)) ∧
    -- (3) the killer-domain generalisation: REFUTED
    (¬ (∀ b : Ty, CoreAt b)) ∧
    -- (4) the `lam` peel: PROVED, at strictly smaller size
    (∀ (body : Term) (hb : Typed [Ty.content] body Ty.unit),
        size hb < size (Typed.lam (Γ := ([] : List Ty)) (a := Ty.content)
          (b := Ty.unit) hb)) ∧
    -- (5) the endpoint identity
    (LamArm ↔ CoreLete) ∧
    -- (6) the closed-killer component from the three arms
    (LamArm → FixArm → LeteArm → NoClosedKiller) ∧
    -- (7) the `lete` arm's exact frame (the split equation is vacuous)
    (LeteArm ↔ LeteArmClosed) :=
  ⟨fun h hl => no_content_at_closedLive h hl,
   coreAtClassFrames_refuted,
   coreAt_not_all,
   fun _ hb => size_deficit_lam hb,
   lamArm_iff_coreLete,
   noClosedKiller_of_arms,
   leteArm_iff_closed⟩


/-! ## Cut admissibility (probe scCutAdm, transfer-landed)

`cut_adm_of_arms` : the cut is admissible — every cut has a reduct —
conditional on exactly TWO structural arms (ContrCutArm, FixCutArm):
`weak_cut_arm_of_contr` derives the weakening case from the contraction
case, so WeakCutArm is not independent. The double induction (rank,
then degree) is closed: the
principal cases (arrow: app-of-lam via `linear_cut`; tensor:
lete-of-pair), the identity case, the axiom/argument case, and every
commutation that is not contraction/fix/weakening. The two arms:
- `ContrCutArm` — the contraction case: the cut formula was contracted
  (read twice via `mergeAt`); the reduct must supply `Γ` to BOTH reads.
  Measured (probe scContrArm) to BE the head-position cut — the arm is
  inter-derivable with it, so it is theorem-strength, not a separate
  wall.
- `FixCutArm` — the fix case: re-applying `fix` after the splice needs
  `AllNonLinear (ΓL ++ Γ ++ ΓR)`, which the frame does not supply; the
  all-non-linear branch is proven outright (probe scNLemma:
  `fix_arm_of_allNonLinear`), and the residual at a linear-junk Γ is
  the named open part.
`cut_at_of_arms` is the general-position form the commutations consume.
The `HasReduct` conclusion (∃ u', Nonempty (Typed ...)) is the
completeness-ready shape: iterating the cut eliminates every
non-atomic application head, which is `CutFree`. -/

namespace ScCutAdm

open Dcare

/-! ## 1. The reduct predicate and the measure -/

/-- `HasReduct Γ b` : SOME term is typed at `Γ` with type `b`.  The ∃-form's
conclusion — `Typed` is Type-valued, so the witness is `Nonempty`-wrapped (the
codebase's idiom for existence). -/
def HasReduct (Γ : List Ty) (b : Ty) : Prop := ∃ u' : Term, Nonempty (Typed Γ u' b)

/-- The cut measure in one Nat: `degree * B + rank`, with `degree = tySize a`,
`rank = size hu`, `B` the global bound on `size ht + size hu`. -/
def cutFuel (deg B rank : Nat) : Nat := deg * B + rank

/-- A RANK descent at fixed degree (and fixed global bound) is a strict descent
of the measure — `deg * B` is one atom, so `omega` closes it. -/
theorem cutFuel_rank_lt {d B r r' : Nat} (h : r' < r) :
    cutFuel d B r' < cutFuel d B r := by
  unfold cutFuel
  omega

/-- A DEGREE descent (rank below the global bound) also descends.  Recorded for
completeness: no closed arm in this file consumes it (docstring, point 3). -/
theorem cutFuel_deg_lt {d d' B r r' : Nat} (hB : 0 < B) (hd : d' < d) (hr : r' < B) :
    cutFuel d' B r' < cutFuel d B r := by
  unfold cutFuel
  have h1 : d' * B ≤ (d - 1) * B := Nat.mul_le_mul_right B (by omega)
  have h2 : (d - 1) * B + B = d * B := by
    cases d with
    | zero => omega
    | succ d₀ => simp only [Nat.succ_sub_one, Nat.succ_mul]
  omega

/-! ## 2. The three named open arms (the structural-rule wall)

Each is stated in the PRECISE shape the induction needs at that frame; each is a
genuine obligation (derivational contraction / the fix side condition / context
weakening), not a gap in the case analysis. -/

/-- THE CONTR ARM: `contr` duplicated the cut formula.  `h` holds it TWICE; the
reduct must live at `Γ ++ Δ`, i.e. ONE `t` must serve both copies. -/
def ContrCutArm : Prop :=
  ∀ {Γ Δ : List Ty} {a b : Ty} (t u₀ : Term) (ht : Typed Γ t a)
    (hk : a.isLinear = false) (h : Typed (a :: a :: Δ) (Term.mergeAt 0 u₀) b),
    HasReduct (Γ ++ Δ) b

/-- THE FIX ARM: the premise's reduct is at the spliced context; re-applying
`fix` needs `AllNonLinear (ΓL ++ Γ ++ ΓR)`, which the frame's side condition
does not supply. -/
def FixCutArm : Prop :=
  ∀ {ΓL Γ ΓR : List Ty} {a a' : Ty} (body : Term)
    (hΓ : AllNonLinear (ΓL ++ a :: ΓR))
    (hred : ∃ body' : Term,
      Nonempty (Typed (ΓL ++ Γ ++ ΓR) body' (Ty.arrow (Ty.later a') a'))),
    HasReduct (ΓL ++ Γ ++ ΓR) a'

/-- THE WEAK ARM: `weak` dropped the cut formula (non-linear, `hk`), so the
premise never reads it; the reduct must re-weaken `Γ` into `ΓR`. -/
def WeakCutArm : Prop :=
  ∀ {Γ ΓR : List Ty} {a b : Ty} (t u₀ : Term) (ht : Typed Γ t a)
    (hk : a.isLinear = false) (h : Typed ΓR u₀ b),
    HasReduct (Γ ++ ΓR) b

/-! ## 3. The closed arms (the rank induction) -/

/-- THE CUT, conditional on the three structural arms.  Binder order:
`fuel B {Γu b} u hu ΓL Γ ΓR a t ht hB hsplit hfuel`, where `ht : Typed Γ t a`
is the FIRST derivation, `hu : Typed (ΓL ++ a :: ΓR) u b` the second, and the
reduct lives at `ΓL ++ Γ ++ ΓR`. -/
theorem cut_gen_of_arms (hC : ContrCutArm) (hF : FixCutArm) (hW : WeakCutArm) :
    ∀ (fuel B : Nat) {Γu : List Ty} {b : Ty} (u : Term) (hu : Typed Γu u b)
      (ΓL : List Ty) (Γ : List Ty) (ΓR : List Ty) (a : Ty) (t : Term)
      (ht : Typed Γ t a),
      size ht + size hu ≤ B → Γu = ΓL ++ a :: ΓR →
      (tySize a) * B + size hu ≤ fuel →
      HasReduct (ΓL ++ Γ ++ ΓR) b
  | 0, B, _, _, _, hu, _, _, _, _, _, _, _, _, hfuel => by
      have h := size_pos hu
      omega
  | n + 1, B, _, _, _, @Typed.var a₀, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      -- THE IDENTITY: the second derivation IS the hypothesis ⇒ the reduct is `t`
      have hlen := congrArg List.length hsplit
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have hL0 : ΓL.length = 0 := by omega
      have hR0 : ΓR.length = 0 := by omega
      cases ΓL with
      | nil =>
          cases ΓR with
          | nil =>
              simp only [List.nil_append, List.cons_append] at hsplit
              injection hsplit with ha
              subst ha
              exact ⟨t, ⟨by simpa only [List.nil_append, List.append_nil] using ht⟩⟩
          | cons _ _ => simp only [List.length_cons] at hR0; omega
      | cons _ _ => simp only [List.length_cons] at hL0; omega
  | n + 1, B, _, _, _, Typed.unit, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      exfalso
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_cons, List.length_append] at hlen
      omega
  | n + 1, B, _, _, _, Typed.nil, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      exfalso
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_cons, List.length_append] at hlen
      omega
  | n + 1, B, _, _, _, Typed.gen, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      exfalso
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_cons, List.length_append] at hlen
      omega
  | n + 1, B, _, _, _, Typed.red, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      exfalso
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_cons, List.length_append] at hlen
      omega
  | n + 1, B, _, _, _, Typed.obj, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      exfalso
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_cons, List.length_append] at hlen
      omega
  | n + 1, B, _, _, _, Typed.terminate, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      exfalso
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_cons, List.length_append] at hlen
      omega
  | n + 1, B, _, _, _, @Typed.lam Γl a' b' body hb, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      -- commutation through the binder: the cut formula rides position +1
      have hB' : size ht + size hb ≤ B := by simp only [size_lam] at hB; omega
      have hfuel' : (tySize a) * B + size hb ≤ n := by
        simp only [size_lam] at hfuel; omega
      obtain ⟨body', ⟨hbody'⟩⟩ :=
        cut_gen_of_arms hC hF hW n B body hb (a' :: ΓL) Γ ΓR a t ht hB'
          (by rw [hsplit]; rfl) hfuel'
      exact ⟨Term.lam a' body', ⟨Typed.lam hbody'⟩⟩
  | n + 1, B, _, _, _, @Typed.next Γn a₀ t₀ h, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      -- `next` keeps its premise's context: a pure rank descent
      have hB' : size ht + size h ≤ B := by simp only [size_next] at hB; omega
      have hfuel' : (tySize a) * B + size h ≤ n := by
        simp only [size_next] at hfuel; omega
      obtain ⟨t', ⟨ht'⟩⟩ :=
        cut_gen_of_arms hC hF hW n B t₀ h ΓL Γ ΓR a t ht hB' hsplit hfuel'
      exact ⟨Term.next t', ⟨Typed.next ht'⟩⟩
  | n + 1, B, _, _, _, @Typed.app E Γf Δ₁ a'' b'' fn arg hf ha hs, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      -- the cut formula lies in the fn piece or the arg piece (ordered split)
      have hsplit' : Γf ++ Δ₁ = ΓL ++ a :: ΓR := hs.trans hsplit
      by_cases hlen : Γf.length ≤ ΓL.length
      · -- in the ARG piece
        obtain ⟨Δ₁L, hΔ, hΓL⟩ := append_cancel_right ΓL Γf Δ₁ a ΓR hsplit' hlen
        have hB' : size ht + size ha ≤ B := by simp only [size_app] at hB; omega
        have hfuel' : (tySize a) * B + size ha ≤ n := by
          simp only [size_app] at hfuel; omega
        obtain ⟨arg', ⟨harg'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B arg ha Δ₁L Γ ΓR a t ht hB' hΔ hfuel'
        have hs' : Γf ++ (Δ₁L ++ Γ ++ ΓR) = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓL]
        exact ⟨Term.app fn arg', ⟨Typed.app hf harg' hs'⟩⟩
      · -- in the FN piece
        have hlt : ΓL.length < Γf.length := by omega
        obtain ⟨ΓfR, hΓf, hΓR⟩ := append_cancel_left ΓL Γf Δ₁ a ΓR hsplit' hlt
        have hB' : size ht + size hf ≤ B := by simp only [size_app] at hB; omega
        have hfuel' : (tySize a) * B + size hf ≤ n := by
          simp only [size_app] at hfuel; omega
        obtain ⟨fn', ⟨hfn'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B fn hf ΓL Γ ΓfR a t ht hB' hΓf hfuel'
        have hs' : (ΓL ++ Γ ++ ΓfR) ++ Δ₁ = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓR]
        exact ⟨Term.app fn' arg, ⟨Typed.app hfn' ha hs'⟩⟩
  | n + 1, B, _, _, _, @Typed.pair E Γ₁ Δ₁ a'' b'' l r hl hr hs, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      have hsplit' : Γ₁ ++ Δ₁ = ΓL ++ a :: ΓR := hs.trans hsplit
      by_cases hlen : Γ₁.length ≤ ΓL.length
      · obtain ⟨Δ₁L, hΔ, hΓL⟩ := append_cancel_right ΓL Γ₁ Δ₁ a ΓR hsplit' hlen
        have hB' : size ht + size hr ≤ B := by simp only [size_pair] at hB; omega
        have hfuel' : (tySize a) * B + size hr ≤ n := by
          simp only [size_pair] at hfuel; omega
        obtain ⟨r', ⟨hr'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B r hr Δ₁L Γ ΓR a t ht hB' hΔ hfuel'
        have hs' : Γ₁ ++ (Δ₁L ++ Γ ++ ΓR) = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓL]
        exact ⟨Term.pair l r', ⟨Typed.pair hl hr' hs'⟩⟩
      · have hlt : ΓL.length < Γ₁.length := by omega
        obtain ⟨Γ₁R, hΓ₁, hΓR⟩ := append_cancel_left ΓL Γ₁ Δ₁ a ΓR hsplit' hlt
        have hB' : size ht + size hl ≤ B := by simp only [size_pair] at hB; omega
        have hfuel' : (tySize a) * B + size hl ≤ n := by
          simp only [size_pair] at hfuel; omega
        obtain ⟨l', ⟨hl'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B l hl ΓL Γ Γ₁R a t ht hB' hΓ₁ hfuel'
        have hs' : (ΓL ++ Γ ++ Γ₁R) ++ Δ₁ = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓR]
        exact ⟨Term.pair l' r, ⟨Typed.pair hl' hr hs'⟩⟩
  | n + 1, B, _, _, _, @Typed.cons E Γh Δt hd tl hc htt hs, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      have hsplit' : Γh ++ Δt = ΓL ++ a :: ΓR := hs.trans hsplit
      by_cases hlen : Γh.length ≤ ΓL.length
      · obtain ⟨ΔtL, hΔ, hΓL⟩ := append_cancel_right ΓL Γh Δt a ΓR hsplit' hlen
        have hB' : size ht + size htt ≤ B := by simp only [size_cons] at hB; omega
        have hfuel' : (tySize a) * B + size htt ≤ n := by
          simp only [size_cons] at hfuel; omega
        obtain ⟨tl', ⟨htl'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B tl htt ΔtL Γ ΓR a t ht hB' hΔ hfuel'
        have hs' : Γh ++ (ΔtL ++ Γ ++ ΓR) = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓL]
        exact ⟨Term.cons hd tl', ⟨Typed.cons hc htl' hs'⟩⟩
      · have hlt : ΓL.length < Γh.length := by omega
        obtain ⟨ΓhR, hΓh, hΓR⟩ := append_cancel_left ΓL Γh Δt a ΓR hsplit' hlt
        have hB' : size ht + size hc ≤ B := by simp only [size_cons] at hB; omega
        have hfuel' : (tySize a) * B + size hc ≤ n := by
          simp only [size_cons] at hfuel; omega
        obtain ⟨hd', ⟨hhd'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B hd hc ΓL Γ ΓhR a t ht hB' hΓh hfuel'
        have hs' : (ΓL ++ Γ ++ ΓhR) ++ Δt = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓR]
        exact ⟨Term.cons hd' tl, ⟨Typed.cons hhd' htt hs'⟩⟩
  | n + 1, B, _, _, _, @Typed.snoc E Γt Δu tt uu htt hu hs, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      have hsplit' : Γt ++ Δu = ΓL ++ a :: ΓR := hs.trans hsplit
      by_cases hlen : Γt.length ≤ ΓL.length
      · obtain ⟨ΔuL, hΔ, hΓL⟩ := append_cancel_right ΓL Γt Δu a ΓR hsplit' hlen
        have hB' : size ht + size hu ≤ B := by simp only [size_snoc] at hB; omega
        have hfuel' : (tySize a) * B + size hu ≤ n := by
          simp only [size_snoc] at hfuel; omega
        obtain ⟨uu', ⟨huu'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B uu hu ΔuL Γ ΓR a t ht hB' hΔ hfuel'
        have hs' : Γt ++ (ΔuL ++ Γ ++ ΓR) = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓL]
        exact ⟨Term.snoc tt uu', ⟨Typed.snoc htt huu' hs'⟩⟩
      · have hlt : ΓL.length < Γt.length := by omega
        obtain ⟨ΓtR, hΓt, hΓR⟩ := append_cancel_left ΓL Γt Δu a ΓR hsplit' hlt
        have hB' : size ht + size htt ≤ B := by simp only [size_snoc] at hB; omega
        have hfuel' : (tySize a) * B + size htt ≤ n := by
          simp only [size_snoc] at hfuel; omega
        obtain ⟨tt', ⟨htt'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B tt htt ΓL Γ ΓtR a t ht hB' hΓt hfuel'
        have hs' : (ΓL ++ Γ ++ ΓtR) ++ Δu = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓR]
        exact ⟨Term.snoc tt' uu, ⟨Typed.snoc htt' hu hs'⟩⟩
  | n + 1, B, _, _, _, @Typed.lete E Γ₁ Γ₂ x y c tt body htt hb hs, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      have hsplit' : Γ₁ ++ Γ₂ = ΓL ++ a :: ΓR := hs.trans hsplit
      by_cases hlen : Γ₁.length ≤ ΓL.length
      · -- the cut formula is in the BODY's piece: the body binds `y :: x :: Γ₂`
        obtain ⟨Γ₂L, hΔ, hΓL⟩ := append_cancel_right ΓL Γ₁ Γ₂ a ΓR hsplit' hlen
        have hB' : size ht + size hb ≤ B := by simp only [size_lete] at hB; omega
        have hfuel' : (tySize a) * B + size hb ≤ n := by
          simp only [size_lete] at hfuel; omega
        obtain ⟨body', ⟨hbody'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B body hb (y :: x :: Γ₂L) Γ ΓR a t ht hB'
            (by rw [hΔ]; rfl) hfuel'
        have hs' : Γ₁ ++ (Γ₂L ++ Γ ++ ΓR) = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓL]
        exact ⟨Term.lete tt body', ⟨Typed.lete htt hbody' hs'⟩⟩
      · -- the cut formula is the SCRUTINEE's piece
        have hlt : ΓL.length < Γ₁.length := by omega
        obtain ⟨Γ₁R, hΓ₁, hΓR⟩ := append_cancel_left ΓL Γ₁ Γ₂ a ΓR hsplit' hlt
        have hB' : size ht + size htt ≤ B := by simp only [size_lete] at hB; omega
        have hfuel' : (tySize a) * B + size htt ≤ n := by
          simp only [size_lete] at hfuel; omega
        obtain ⟨tt', ⟨htt'⟩⟩ :=
          cut_gen_of_arms hC hF hW n B tt htt ΓL Γ Γ₁R a t ht hB' hΓ₁ hfuel'
        have hs' : (ΓL ++ Γ ++ Γ₁R) ++ Γ₂ = ΓL ++ Γ ++ ΓR := by
          simp only [List.append_assoc, hΓR]
        exact ⟨Term.lete tt' body, ⟨Typed.lete htt' hb hs'⟩⟩
  | n + 1, B, _, _, _, @Typed.contr Γ' k tt ττ hk h, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      -- `contr`: the conclusion context is `k :: Γ'`, the premise holds it twice
      cases ΓL with
      | nil =>
          -- THE CONTR ARM: the contracted position IS the cut formula
          simp only [List.nil_append] at hsplit
          injection hsplit with hka hΓ'
          subst hka
          subst hΓ'
          exact hC t tt ht hk h
      | cons x ΓL' =>
          -- position shift: the premise's `k` is not the cut formula
          simp only [List.cons_append] at hsplit
          injection hsplit with hkx hΓ'
          subst hkx
          subst hΓ'
          have hB' : size ht + size h ≤ B := by simp only [size_contr] at hB; omega
          have hfuel' : (tySize a) * B + size h ≤ n := by
            simp only [size_contr] at hfuel; omega
          obtain ⟨u', ⟨hu'⟩⟩ :=
            cut_gen_of_arms hC hF hW n B (Term.mergeAt 0 tt) h
              (k :: k :: ΓL') Γ ΓR a t ht hB' rfl hfuel'
          exact ⟨Term.unmergeAt 0 u',
            ⟨Typed.contr hk ((mergeAt_unmergeAt 0 u').symm ▸ hu')⟩⟩
  | n + 1, B, _, _, _, @Typed.weak Γ' k tt ττ hk h, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      cases ΓL with
      | nil =>
          -- THE WEAK ARM: the dropped position IS the cut formula
          simp only [List.nil_append] at hsplit
          injection hsplit with hka hΓ'
          subst hka
          subst hΓ'
          exact hW t tt ht hk h
      | cons x ΓL' =>
          -- position shift: the dropped `k` is not the cut formula
          simp only [List.cons_append] at hsplit
          injection hsplit with hkx hΓ'
          subst hkx
          subst hΓ'
          have hB' : size ht + size h ≤ B := by simp only [size_weak] at hB; omega
          have hfuel' : (tySize a) * B + size h ≤ n := by
            simp only [size_weak] at hfuel; omega
          obtain ⟨u', ⟨hu'⟩⟩ :=
            cut_gen_of_arms hC hF hW n B tt h ΓL' Γ ΓR a t ht hB' rfl hfuel'
          exact ⟨Term.liftAt 0 u', ⟨Typed.weak hk hu'⟩⟩
  | n + 1, B, _, _, _, @Typed.fix Γf a₀ body hΓ h, ΓL, Γ, ΓR, a, t, ht, hB, hsplit, hfuel => by
      -- THE FIX ARM: the premise's reduct cannot be re-`fix`ed at the spliced context
      have hB' : size ht + size h ≤ B := by simp only [size_fix] at hB; omega
      have hfuel' : (tySize a) * B + size h ≤ n := by
        simp only [size_fix] at hfuel; omega
      exact hF body (hsplit ▸ hΓ)
        (cut_gen_of_arms hC hF hW n B body h ΓL Γ ΓR a t ht hB' hsplit hfuel')

/-! ## 4. The arms proven outright, and the brief's statement -/

/-- THE ARROW PRINCIPAL CASE IS A RING-REBUILD (finding 3, kernel-checked):
`t : arrow X Y` and the hypothesis read as an app's fn ⇒ `app t arg` typechecks
at `Γ ++ Δ` directly.  No sub-formula cut, no degree descent, no exchange. -/
theorem arrow_principal_rebuild {Γ Δ : List Ty} {X Y : Ty} (t arg : Term)
    (ht : Typed Γ t (Ty.arrow X Y)) (ha : Typed Δ arg X) :
    HasReduct (Γ ++ Δ) Y :=
  ⟨Term.app t arg, ⟨Typed.app ht ha rfl⟩⟩

/-- THE TENSOR PRINCIPAL CASE IS A RING-REBUILD (finding 3): `t : tensor x y` and
the hypothesis read as a `lete`'s scrutinee ⇒ `lete t body` typechecks at
`Γ ++ Γ₂`.  **The "tensor twin" is unnecessary in the ∃-form.** -/
theorem tensor_principal_rebuild {Γ Γ₂ : List Ty} {x y c : Ty} (t body : Term)
    (ht : Typed Γ t (Ty.tensor x y)) (hb : Typed (y :: x :: Γ₂) body c) :
    HasReduct (Γ ++ Γ₂) c :=
  ⟨Term.lete t body, ⟨Typed.lete ht hb rfl⟩⟩

/-- WEAKENING-IN at an all-non-linear prefix (the iterated `weak`): this is
exactly the missing ingredient of `WeakCutArm`. -/
theorem weaken_allNonLinear : ∀ (Γ : List Ty) {ΓR : List Ty} {t : Term} {τ : Ty},
    AllNonLinear Γ → Typed ΓR t τ → HasReduct (Γ ++ ΓR) τ := by
  intro Γ
  induction Γ with
  | nil => intro ΓR t τ _ h; exact ⟨t, ⟨by simpa only [List.nil_append] using h⟩⟩
  | cons k Γ' ih =>
      intro ΓR t τ hnl h
      have hk : k.isLinear = false := hnl 0 k (by rfl)
      have hnl' : AllNonLinear Γ' := by
        intro i b hpos
        exact hnl (i + 1) b (by simpa only [List.get?_succ_cons'] using hpos)
      obtain ⟨t', ⟨ht'⟩⟩ := ih hnl' h
      exact ⟨Term.liftAt 0 t', ⟨Typed.weak hk ht'⟩⟩

/-- THE WEAK ARM'S EXACT CONTENT, kernel-checked: the arm closes when `Γ` (the
cut formula's context) is ALL NON-LINEAR — the arm's whole obligation is the
non-linearity of `Γ`, nothing else. -/
theorem cut_weak_drop_closed {Γ ΓR : List Ty} {a b : Ty} (t u₀ : Term)
    (ht : Typed Γ t a) (h : Typed ΓR u₀ b) (hnl : AllNonLinear Γ) :
    HasReduct (Γ ++ ΓR) b :=
  weaken_allNonLinear Γ hnl h

/-- THE LINEAR PRINCIPAL CASE — `linear_cut` WRAPPED: if the cut formula is
LINEAR and read EXACTLY ONCE, the cut closes for EVERY second derivation at once
(the in-tree one-hole splice).  This is the k = 1 arm, complete, no arms needed. -/
theorem cut_linear_once {ΓL Γ ΓR : List Ty} {a b : Ty} (t u : Term)
    (ht : Typed Γ t a) (hu : Typed (ΓL ++ a :: ΓR) u b)
    (hlin : a.isLinear = true) (husage : uses hu ΓL.length = 1) :
    HasReduct (ΓL ++ Γ ++ ΓR) b := by
  obtain ⟨body', h', -, -, -⟩ := linear_cut hu ΓL a ΓR Γ t ht rfl hlin husage
  exact ⟨body', ⟨h'⟩⟩

/-- THE IDENTITY (first-derivation side): if `t` IS the hypothesis (`t = var 0`),
canonicality forces `Γ = [a]` and the reduct is `u` itself. -/
theorem cut_axiom_arg {Γ Δ : List Ty} {a b : Ty} (t u : Term) (ht : Typed Γ t a)
    (hu : Typed (a :: Δ) u b) (htv : t = Term.var 0) :
    HasReduct (Γ ++ Δ) b := by
  obtain ⟨a', hΓ, hτ⟩ := var_canonical ht htv
  subst hΓ
  subst hτ
  exact ⟨u, ⟨hu⟩⟩

/-- **CUT ADMISSIBILITY** (the brief's statement) modulo the three structural
arms: `Typed Γ t a → Typed (a :: Δ) u b → ∃ u', Typed (Γ ++ Δ) u' b`. -/
theorem cut_adm_of_arms (hC : ContrCutArm) (hF : FixCutArm) (hW : WeakCutArm) :
    ∀ {Γ Δ : List Ty} {a b : Ty} (t u : Term),
      Typed Γ t a → Typed (a :: Δ) u b → HasReduct (Γ ++ Δ) b := by
  intro Γ Δ a b t u ht hu
  exact cut_gen_of_arms hC hF hW _ (size ht + size hu) u hu [] Γ Δ a t ht
    (Nat.le_refl _) rfl (Nat.le_refl _)

/-- The same at a GENERAL POSITION (the form the commutations consume, and the
form a `CutFree`-completeness proof wants). -/
theorem cut_at_of_arms (hC : ContrCutArm) (hF : FixCutArm) (hW : WeakCutArm) :
    ∀ {ΓL Γ ΓR : List Ty} {a b : Ty} (t u : Term),
      Typed Γ t a → Typed (ΓL ++ a :: ΓR) u b → HasReduct (ΓL ++ Γ ++ ΓR) b := by
  intro ΓL Γ ΓR a b t u ht hu
  exact cut_gen_of_arms hC hF hW _ (size ht + size hu) u hu ΓL Γ ΓR a t ht
    (Nat.le_refl _) rfl (Nat.le_refl _)

end ScCutAdm

/-! ## The two-arm reduction (probe scWeakArm, transfer-landed) -/

namespace ScCutAdm

theorem weak_arm_implies_unit_inhabitation (hW : WeakCutArm) :
    ∀ {Γ : List Ty} {a : Ty} (t : Term), Typed Γ t a → a.isLinear = false →
      HasReduct Γ Ty.unit := by
  intro Γ a t ht hk
  have h := hW t Term.unit ht hk (Typed.unit)
  simpa only [List.append_nil] using h

theorem weak_cut_arm_of_contr (hC : ContrCutArm) : WeakCutArm := by
  intro Γ ΓR a b t u₀ ht hk h
  have hw : Typed (a :: a :: ΓR) (Term.liftAt 0 (Term.liftAt 0 u₀)) b :=
    Typed.weak (k := a) hk (Typed.weak (k := a) hk h)
  refine hC (Γ := Γ) (Δ := ΓR) (a := a) (b := b) t
    (Term.unmergeAt 0 (Term.liftAt 0 (Term.liftAt 0 u₀))) ht hk ?_
  rw [mergeAt_unmergeAt]
  exact hw

theorem cut_adm_of_two_arms (hC : ContrCutArm) (hF : FixCutArm) :
    ∀ {Γ Δ : List Ty} {a b : Ty} (t u : Term),
      Typed Γ t a → Typed (a :: Δ) u b → HasReduct (Γ ++ Δ) b :=
  cut_adm_of_arms hC hF (weak_cut_arm_of_contr hC)

theorem cut_at_of_two_arms (hC : ContrCutArm) (hF : FixCutArm) :
    ∀ {ΓL Γ ΓR : List Ty} {a b : Ty} (t u : Term),
      Typed Γ t a → Typed (ΓL ++ a :: ΓR) u b → HasReduct (ΓL ++ Γ ++ ΓR) b :=
  cut_at_of_arms hC hF (weak_cut_arm_of_contr hC)

end ScCutAdm

/-! ## The iteration loop's shape + the arms' final boundary -/

/-- The completeness statement. -/
def Completeness : Prop :=
  ∀ {Γ : List Ty} {τ : Ty} (t : Term) (_h : Typed Γ t τ),
    ∃ t' : Term, ∃ h' : Typed Γ t' τ, CutFree h'

/-- The head-elimination step. -/
def HeadElim : Prop :=
  ∀ {Γf Δ : List Ty} {a b : Ty} (fn arg : Term)
    (hfn : Typed Γf fn (Ty.arrow a b)) (harg : Typed Δ arg a)
    (_happ : Typed (Γf ++ Δ) (Term.app fn arg) b),
    ¬ IsAtomic fn →
    ∃ u' : Term, Nonempty (Typed (Γf ++ Δ) u' b)

/-- **The permutation wall, kernel-checked**: the ordered split's data. -/
theorem beta_order_differs :
    [Ty.content] ++ [Ty.unit] ≠ [Ty.unit] ++ [Ty.content] := by decide

/-- **The closed-fn escape**: when the function's context is empty, the
orders agree. -/
theorem closed_fn_order_agrees (Δ : List Ty) : Δ ++ [] = [] ++ Δ := by simp


/-! ## The counting model's verdict (probe scMultiworld, /tmp/probe/scMultiworld.lean)

A possible-worlds model with worlds = Nat (the content budget):
content = the up-set {w | 1 <= w} (forced by the weak instance);
knower = the empty set (forced by gen — well-foundedness of Nat);
tensor adds; arrow is the residual. Sound for 16 of 17 constructors
(fix is the exception). CONTRACTION CLOSED at the fix-free grain
INCLUDING gen, cons, snoc, and the structural rules — strictly deeper
than no_contraction_nogen (which excludes gen): the world arithmetic
kills [content] ⊢ C⊗C outright. Vanishing is PROVABLY out of this
model's reach: gen empties the knower, making arrow knower b vacuously
every budget, and weak pours all of Nat into unit. The gen-fire repair
also fails (the descent moves to the total component). -/

/-! ## The no-weak fragment — both stubs killed (probe scNoWeak, transfer-landed)

NoWeak excludes exactly one of the 17 rules: weak. Everything else
is IN: fix (unguarded — the guard ▷a reads as ⊤, no eliminator
exists), gen, contr, cons, snoc, next, mints, live binders, all
constants. BOTH stubs are killed:

no_vanishing_noweak : Typed [content] t unit → NoWeak h → False
no_contraction_noweak : Typed [content] t (content⊗content) → NoWeak h → False

The key: the refined counting model (unit = {0} exactly, not the
up-set) is sound at all 16 non-weak rules. The guard ▷a can be
interpreted as ⊤ (the calculus has no guard eliminator — later_ne_self),
making fix sound at EVERY type (guard_fix_key, axiom-free, no
AllNonLinear). gen is absorbed (axiom-free); contr is absorbed via
the three-way classification {∅, {0}, ⊤} of non-linear interpretations.

weak is excluded BY THE MODEL: one weak node breaks it (a sequent
the model validates at every budget gains a conclusion it does not).
The impossibility theorem (no word model kills both) is not contradicted:
this model is unsound at weak, so it sits outside that theorem's class.

The weak-elimination (probe scWeakElim): weak nodes are eliminable
at 12 of 14 parent rules. The two walls: lam and the lete body —
the only parents that prepend positions for their own binder. At
these, the weak node's head IS the binder position; removing it
removes what the rule binds. These are exactly the core's compound-
source / carrier family. -/

namespace NoWeakFrag

/-- No weak nodes in the derivation. -/
def NoWeak : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Prop
  | _, _, _, @Typed.weak _ _ _ _ _ _ => False
  | _, _, _, @Typed.lam Γ a b body h => NoWeak h
  | _, _, _, @Typed.app E Γ Δ a b fn arg hf ha hs => NoWeak hf ∧ NoWeak ha
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs => NoWeak hl ∧ NoWeak hr
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs => NoWeak ht ∧ NoWeak hb
  | _, _, _, @Typed.next Γ a t h => NoWeak h
  | _, _, _, @Typed.fix Γ a body hΓ h => NoWeak h
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs => NoWeak hc ∧ NoWeak ht
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs => NoWeak ht ∧ NoWeak hu
  | _, _, _, @Typed.contr Γ k t τ _hk h => NoWeak h
  | _, _, _, _ => True

end NoWeakFrag

/-! ## The Extractor kill — knowledge/value/knower at `[content]` (probe scExtractor, transfer-landed)

The counting model's sole break is a `weak` node at a FULL type (the
record's `weakFullSeq : [knowledge] ⊢ unit`). This section proves the
three kills that close the type-side of that break, fix-free, as ONE
theorem: a new need predicate `Ext` (the in-tree `NeedsS` machine
widened with knowledge/value/knower), one 17-arm propagation lemma
`extprop`, and the clean-context corollary `no_ext_at_clean`.

THE KILLS, all kernel-checked at the fix-free grain:
- `no_knowledge_at_content : Typed [content] t knowledge → fixCount h = 0 → False`
- `no_value_at_content` (the same, one `Ext` clause away)
- `no_knower_at_content` (the round-13 lam-knower escape, closed here)
- `no_stream_at_content` (re-derives the in-tree `no_stream_nosupply`
  through `Ext` — the barrier and the kill agree)
- the knowledge/value/knower instances at `[]` (load-bearing: an app's
  argument is typed at a PIECE of the root context, and a piece can be
  empty).

THE BOUNDARY IS THE FIX, structurally: `ext_fix_body_never` — `¬ Ext (▷a → a)`
for EVERY a (the guard is need-invisible, so the crossed arrow negates
its own codomain's need), hence the propagation can never cross a fix
and the fix-inclusive grain needs the reach analysis, not a patch. From
the other side, `[knower] ⊢ knowledge` IS derivable (`knowledge_at_knower`)
and carries a fix node — the boundary is live, not an artifact.

THE TWO CARRIERS OF THE BREAK, kernel-constructed (what makes the kill
a statement about the MODEL, not just a nice fact): `carrierOfKnowledge`
turns a `[content] ⊢ knowledge` into a `[content] ⊢ unit` tree carrying
a knowledge-headed `weak` (the head enters by the `lam` binder and is
discharged by the `app` — so §1 kills exactly its discharge); the guard
carrier `carrierLaterUnit` builds a full-headed `weak` from the target
itself, +4 nodes at the same sequent, and dies by MINIMALITY
(`carrierLaterUnit_size`).

WHY NO DERIVABILITY FACT REPAIRS THE MODEL (§4, the decisive
measurement): the full ∧ non-linear class is UNBOUNDED
(`full_nonlin_unbounded` — `arrow knower X` is full for every `X`), and
`weak` has NO PREMISE on its head (`any_nonlinear_head_free`): a
full-headed `weak` node needs a PLACE, not a derivation. The model's
real obligation is the valuation condition `ZeroW k` for every
non-linear `k` (`weak_break_of_full`), which no type-derivability
theorem can supply. NOT DONE here, stated plainly: the whole-tree
provenance traversal (the transfer argument's remaining gap) and the
fix-inclusive grain. `no_vanishing` is untouched. -/
namespace SCExtractor

/-! ### 1. The need predicate and the kill -/

/-- `Ext` widens the record's `NeedsS` with `knowledge`, `value` and
`knower`. The arrow clause is the record's shape: codomain needs, and
the domain must not be able to fund the need itself — that is what lets
the app case push the obligation onto the argument instead of onto the
function. -/
def Ext : Ty → Prop
  | .stream => True
  | .knower => True
  | .knowledge => True
  | .value => True
  | .later a => Ext a
  | .tensor a b => Ext a ∨ Ext b
  | .arrow a b => Ext b ∧ ¬ NeedsS a ∧ ¬ NeedsK a ∧ ¬ Ext a
  | _ => False

theorem ext_later (a : Ty) : Ext (Ty.later a) ↔ Ext a := Iff.rfl
theorem ext_tensor (a b : Ty) : Ext (Ty.tensor a b) ↔ Ext a ∨ Ext b := Iff.rfl

theorem ext_arrow (a b : Ty) :
    Ext (Ty.arrow a b) ↔ Ext b ∧ ¬ NeedsS a ∧ ¬ NeedsK a ∧ ¬ Ext a := Iff.rfl

/-- EXT-NEED PROPAGATION: an `Ext`-typed conclusion forces a context
position that is either stream/knower-supplying (the in-tree `SSupply`)
or `Ext` itself. Fix-free, exactly the grain of the in-tree `sprop`;
the extra disjunct is what lets the knowledge/value/knower cases
travel. -/
theorem extprop : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    fixCount h = 0 → Ext τ → ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ (SSupply b ∨ Ext b)
  | _, _, _, Typed.var, _, hK => ⟨0, _, List.get?_zero_cons', Or.inr hK⟩
  | _, _, _, @Typed.lam Γ a b body h, hc, hK => by
      obtain ⟨hb, hna, hnk, hea⟩ := (ext_arrow a b).mp hK
      obtain ⟨i, b', hpos, hcl⟩ := extprop h (by simpa only [fixCount] using hc) hb
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hcl with hs | he'
          · rcases hs with hs | hk
            · exact absurd hs hna
            · exact absurd hk hnk
          · exact absurd he' hea
      | succ m =>
          rw [List.get?_succ_cons'] at hpos
          exact ⟨m, b', hpos, hcl⟩
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hc, hK => by
      obtain ⟨hc1, hc2⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hc
      by_cases hA : Ext (Ty.arrow X b)
      · obtain ⟨i, b', hpos, hcl⟩ := extprop hf hc1 hA
        refine ⟨i, b', ?_, hcl⟩
        have hlt : i < Γ.length := List.get?_some_lt hpos
        rw [← hs, List.get?_append_lt hlt]
        exact hpos
      · have hdx : NeedsS X ∨ NeedsK X ∨ Ext X := by
          rcases Classical.em (NeedsS X) with h | h
          · exact Or.inl h
          rcases Classical.em (NeedsK X) with h2 | h2
          · exact Or.inr (Or.inl h2)
          rcases Classical.em (Ext X) with h3 | h3
          · exact Or.inr (Or.inr h3)
          exact absurd ((ext_arrow X b).mpr ⟨hK, h, h2, h3⟩) hA
        rcases hdx with hx | hx | hx
        · obtain ⟨j, b', hpos, hsup⟩ := sprop ha hc2 hx
          refine ⟨Γ.length + j, b', ?_, Or.inl hsup⟩
          rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
            Nat.add_sub_cancel_left]
          exact hpos
        · obtain ⟨j, b', hpos, hneed⟩ := kprop ha hx
          refine ⟨Γ.length + j, b', ?_, Or.inl (Or.inr hneed)⟩
          rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
            Nat.add_sub_cancel_left]
          exact hpos
        · obtain ⟨j, b', hpos, hcl⟩ := extprop ha hc2 hx
          refine ⟨Γ.length + j, b', ?_, hcl⟩
          rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
            Nat.add_sub_cancel_left]
          exact hpos
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hc, hK => by
      obtain ⟨hc1, hc2⟩ : fixCount hl = 0 ∧ fixCount hr = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hc
      rcases (ext_tensor a b).mp hK with hK | hK
      · obtain ⟨i, b', hpos, hcl⟩ := extprop hl hc1 hK
        refine ⟨i, b', ?_, hcl⟩
        have hlt : i < Γ.length := List.get?_some_lt hpos
        rw [← hs, List.get?_append_lt hlt]
        exact hpos
      · obtain ⟨j, b', hpos, hcl⟩ := extprop hr hc2 hK
        refine ⟨Γ.length + j, b', ?_, hcl⟩
        rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
          Nat.add_sub_cancel_left]
        exact hpos
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hc, hK => by
      obtain ⟨hc1, hc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hc
      obtain ⟨i, b', hpos, hcl⟩ := extprop hb hc2 hK
      cases i with
      | zero =>
          -- position 0 of the body's context is the tensor's SECOND component `b`
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hcl with hs' | he'
          · rcases hs' with hs' | hk'
            · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := sprop ht hc1 (Or.inr hs')
              have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
              refine ⟨i, b₂, ?_, Or.inl hsup₂⟩
              rw [← hs, List.get?_append_lt hlt]
              exact hpos₂
            · obtain ⟨i, b₂, hpos₂, hneed₂⟩ := kprop ht (Or.inr hk')
              have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
              refine ⟨i, b₂, ?_, Or.inl (Or.inr hneed₂)⟩
              rw [← hs, List.get?_append_lt hlt]
              exact hpos₂
          · obtain ⟨i, b₂, hpos₂, hcl₂⟩ :=
              extprop ht hc1 ((ext_tensor a b).mpr (Or.inr he'))
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, hcl₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
      | succ j =>
          cases j with
          | zero =>
              -- position 1 is the tensor's FIRST component `a`
              rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
              injection hpos with he
              subst he
              rcases hcl with hs' | he'
              · rcases hs' with hs' | hk'
                · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := sprop ht hc1 (Or.inl hs')
                  have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
                  refine ⟨i, b₂, ?_, Or.inl hsup₂⟩
                  rw [← hs, List.get?_append_lt hlt]
                  exact hpos₂
                · obtain ⟨i, b₂, hpos₂, hneed₂⟩ := kprop ht (Or.inl hk')
                  have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
                  refine ⟨i, b₂, ?_, Or.inl (Or.inr hneed₂)⟩
                  rw [← hs, List.get?_append_lt hlt]
                  exact hpos₂
              · obtain ⟨i, b₂, hpos₂, hcl₂⟩ :=
                  extprop ht hc1 ((ext_tensor a b).mpr (Or.inl he'))
                have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
                refine ⟨i, b₂, ?_, hcl₂⟩
                rw [← hs, List.get?_append_lt hlt]
                exact hpos₂
          | succ m =>
              rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
              refine ⟨Γ₁.length + m, b', ?_, hcl⟩
              rw [← hs, List.get?_append_ge (Nat.le_add_right Γ₁.length m),
                Nat.add_sub_cancel_left]
              exact hpos
  | _, _, _, Typed.unit, _, hK => False.elim hK
  | _, _, _, @Typed.next _ _ _ h, hc, hK =>
      extprop h (by simpa only [fixCount] using hc) ((ext_later _).mp hK)
  | _, _, _, @Typed.fix _ _ _ _ _, hc, _ => by
      simp only [fixCount] at hc; omega
  | _, _, _, @Typed.cons _ Γ Δ hd tl hct ht hs, hc, _ => by
      obtain ⟨hc1, hc2⟩ : fixCount hct = 0 ∧ fixCount ht = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hc
      obtain ⟨j, b', hpos, hcl⟩ := extprop ht hc2 True.intro
      refine ⟨Γ.length + j, b', ?_, hcl⟩
      rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
        Nat.add_sub_cancel_left]
      exact hpos
  | _, _, _, Typed.nil, _, hK => False.elim hK
  | _, _, _, @Typed.snoc _ _ _ _ _ _ _ _, _, hK => False.elim hK
  | _, _, _, Typed.gen, _, hK => False.elim (hK.2.2.1 True.intro)
  | _, _, _, Typed.red, _, hK => False.elim (hK.2.1 True.intro)
  | _, _, _, Typed.obj, _, hK => False.elim (hK.2.1 True.intro)
  | _, _, _, Typed.terminate, _, hK => False.elim hK.1
  | _, _, _, @Typed.contr Γ k t τ _ h, hc, hK => by
      obtain ⟨i, b', hpos, hcl⟩ := extprop h (by simpa only [fixCount] using hc) hK
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact ⟨0, _, List.get?_zero_cons', hcl⟩
      | succ j =>
          cases j with
          | zero =>
              rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
              injection hpos with he
              subst he
              exact ⟨0, _, List.get?_zero_cons', hcl⟩
          | succ m =>
              rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
              exact ⟨m + 1, b', by rw [List.get?_succ_cons']; exact hpos, hcl⟩
  | _, _, _, @Typed.weak Γ k t τ _ h, hc, hK => by
      obtain ⟨i, b', hpos, hcl⟩ := extprop h (by simpa only [fixCount] using hc) hK
      exact ⟨i + 1, b', by rw [List.get?_succ_cons']; exact hpos, hcl⟩

/-- THE KILL, context-general: an `Ext` conclusion at a CLEAN context is
impossible, fix-free. -/
theorem no_ext_at_clean {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ)
    (hf : fixCount h = 0)
    (hns : ∀ (i : Nat) (b : Ty), Γ[i]? = some b → ¬ SSupply b)
    (he : ∀ (i : Nat) (b : Ty), Γ[i]? = some b → ¬ Ext b) : ¬ Ext τ := by
  intro hK
  obtain ⟨i, b, hpos, hcl⟩ := extprop h hf hK
  rcases hcl with h1 | h2
  · exact hns i b hpos h1
  · exact he i b hpos h2

/-! #### The clean-context facts, at `[content]` and at `[]` -/

theorem content_not_ssupply : ¬ SSupply Ty.content := by
  intro h
  rcases h with h | h
  · exact h
  · exact h

theorem content_not_ext : ¬ Ext Ty.content := fun h => h

theorem content_ctx_nosupply (i : Nat) (b : Ty)
    (hpos : ([Ty.content] : List Ty)[i]? = some b) : ¬ SSupply b := by
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with he
      subst he
      exact content_not_ssupply
  | succ m =>
      rw [List.get?_succ_cons'] at hpos
      rw [List.get?_nil'] at hpos
      contradiction

theorem content_ctx_not_ext (i : Nat) (b : Ty)
    (hpos : ([Ty.content] : List Ty)[i]? = some b) : ¬ Ext b := by
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with he
      subst he
      exact content_not_ext
  | succ m =>
      rw [List.get?_succ_cons'] at hpos
      rw [List.get?_nil'] at hpos
      contradiction

theorem nil_ctx_nosupply (i : Nat) (b : Ty) (hpos : ([] : List Ty)[i]? = some b) :
    ¬ SSupply b := by
  rw [List.get?_nil'] at hpos
  contradiction

theorem nil_ctx_not_ext (i : Nat) (b : Ty) (hpos : ([] : List Ty)[i]? = some b) :
    ¬ Ext b := by
  rw [List.get?_nil'] at hpos
  contradiction

/-- `[content] ⊢ knowledge` is uninhabited — fix-free, i.e. at the
Extractor's own grain (see §2 below for why the fix is exactly the
boundary). -/
theorem no_knowledge_at_content {t : Term}
    (h : Typed [Ty.content] t Ty.knowledge) (hf : fixCount h = 0) : False :=
  no_ext_at_clean h hf content_ctx_nosupply content_ctx_not_ext True.intro

/-- `[content] ⊢ value` is uninhabited — the SAME theorem, one `Ext`
clause away. -/
theorem no_value_at_content {t : Term}
    (h : Typed [Ty.content] t Ty.value) (hf : fixCount h = 0) : False :=
  no_ext_at_clean h hf content_ctx_nosupply content_ctx_not_ext True.intro

/-- The knower — the ONLY escape the round-13 analysis left (the
`lam`-knower self-funding source): `[content] ⊢ knower` is uninhabited
too. -/
theorem no_knower_at_content {t : Term}
    (h : Typed [Ty.content] t Ty.knower) (hf : fixCount h = 0) : False :=
  no_ext_at_clean h hf content_ctx_nosupply content_ctx_not_ext True.intro

/-- The stream instance — it agrees with the in-tree `no_stream_nosupply`
(this is a re-derivation of that barrier through `Ext`). -/
theorem no_stream_at_content {t : Term}
    (h : Typed [Ty.content] t Ty.stream) (hf : fixCount h = 0) : False :=
  no_ext_at_clean h hf content_ctx_nosupply content_ctx_not_ext True.intro

/-- The three at the empty context. This instance is NOT decoration: an
app's argument is typed at a PIECE of the root context, and a piece can
be `[]`. -/
theorem no_knowledge_at_nil {t : Term} (h : Typed [] t Ty.knowledge)
    (hf : fixCount h = 0) : False :=
  no_ext_at_clean h hf nil_ctx_nosupply nil_ctx_not_ext True.intro

theorem no_value_at_nil {t : Term} (h : Typed [] t Ty.value)
    (hf : fixCount h = 0) : False :=
  no_ext_at_clean h hf nil_ctx_nosupply nil_ctx_not_ext True.intro

theorem no_knower_at_nil {t : Term} (h : Typed [] t Ty.knower)
    (hf : fixCount h = 0) : False :=
  no_ext_at_clean h hf nil_ctx_nosupply nil_ctx_not_ext True.intro

/-! ### 2. The boundary: the fix

`extprop` is fix-free because it MUST be: the fix rule's body type is
never `Ext`. That is the exact place the guard earns its keep. -/

/-- The guard is need-INVISIBLE (`Ext (▷a) = Ext a`), so the crossed
arrow `▷a → a` negates its own codomain's need: a fix body can never
carry `Ext`. -/
theorem ext_fix_body_never (a : Ty) : ¬ Ext (Ty.arrow (Ty.later a) a) := by
  intro h
  exact h.2.2.2 h.1

/-- Non-vacuity from the other side: `[knower] ⊢ knowledge` IS derivable
(the in-tree epistemic cycle fed to `red`), and it escapes §1 on BOTH
counts — a knower position, and a `fix` node. -/
theorem knowledge_at_knower : ∃ t, Nonempty (Typed [Ty.knower] t Ty.knowledge) := by
  obtain ⟨t, ⟨hs⟩⟩ := knower_sustains_stream
  exact ⟨Term.app Term.red t,
    ⟨Typed.app (Γ := []) (Δ := [Ty.knower]) (a := Ty.stream) (b := Ty.knowledge)
      Typed.red hs rfl⟩⟩

/-- … and it is genuinely outside the fix-free grain, so §1 could never
have reached it: its `fixCount` is at least 1. -/
theorem knowledge_at_knower_has_fix :
    ∃ (t : Term) (h : Typed [Ty.knower] t Ty.knowledge), 0 < fixCount h :=
  ⟨Term.app Term.red (Term.fix (Term.lam (Ty.later Ty.stream) flip2)),
   Typed.app (Γ := []) (Δ := [Ty.knower]) (a := Ty.stream) (b := Ty.knowledge)
     Typed.red (Typed.fix knower_ctx_nonlinear (Typed.lam flip2Typed)) rfl,
   by simp only [fixCount]; omega⟩

/-! ### 3. The two carriers of the break -/

/-- Every `weak` head, in tree order — the traversal that makes "the
node is really in there" kernel-checked rather than asserted. -/
def weakHeads : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → List Ty
  | _, _, _, Typed.var => []
  | _, _, _, @Typed.lam _ _ _ _ h => weakHeads h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => weakHeads hf ++ weakHeads ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => weakHeads hl ++ weakHeads hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => weakHeads ht ++ weakHeads hb
  | _, _, _, Typed.unit => []
  | _, _, _, @Typed.next _ _ _ h => weakHeads h
  | _, _, _, @Typed.fix _ _ _ _ h => weakHeads h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => weakHeads hc ++ weakHeads ht
  | _, _, _, Typed.nil => []
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => weakHeads ht ++ weakHeads hu
  | _, _, _, Typed.gen => []
  | _, _, _, Typed.red => []
  | _, _, _, Typed.obj => []
  | _, _, _, Typed.terminate => []
  | _, _, _, @Typed.contr _ _ _ _ _ h => weakHeads h
  | _, _, _, @Typed.weak _ k _ _ _ h => k :: weakHeads h

theorem weakHeads_weak {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty}
    (hk : k.isLinear = false) (h : Typed Γ t τ) :
    weakHeads (Typed.weak hk h) = k :: weakHeads h := rfl

/-- THE KNOWLEDGE CARRIER. A `[content] ⊢ knowledge` derivation yields a
`[content] ⊢ unit` tree whose function piece is `λ(k : knowledge). unit`
— i.e. a `weak` node at the FULL head `knowledge`. What the construction
says exactly: the head position is introduced by the `lam` BINDER, and
the arrow it produces is discharged by the `app`, whose argument IS the
knowledge derivation — so the §1 kill removes exactly its discharge. -/
def carrierOfKnowledge {t : Term} (ha : Typed [Ty.content] t Ty.knowledge) :
    Typed [Ty.content]
      (Term.app (Term.lam Ty.knowledge (Term.liftAt 0 Term.unit)) t) Ty.unit :=
  Typed.app (Γ := []) (Δ := [Ty.content]) (a := Ty.knowledge) (b := Ty.unit)
    (Typed.lam (Typed.weak (k := Ty.knowledge) (t := Term.unit) (τ := Ty.unit)
      (by decide) Typed.unit))
    ha rfl

/-- The carrier really contains the full-headed `weak` node. -/
theorem carrierOfKnowledge_full_weak {t : Term}
    (ha : Typed [Ty.content] t Ty.knowledge) :
    Ty.knowledge ∈ weakHeads (carrierOfKnowledge ha) := by
  simp [carrierOfKnowledge, weakHeads]

/-- So killing §1's premise kills this carrier: if `[content] ⊢ knowledge`
existed, a `[content]`-rooted tree would carry the model-refuting node. -/
theorem model_refuted_of_knowledge_at_content
    (hex : ∃ t, Nonempty (Typed [Ty.content] t Ty.knowledge)) :
    ∃ u, Nonempty (Typed [Ty.content] u Ty.unit) := by
  obtain ⟨t, ⟨ha⟩⟩ := hex
  exact ⟨_, ⟨carrierOfKnowledge ha⟩⟩

/-- THE VALUE CARRIER: the same shape at the other full base, so the two
§1 kills cover the two carriers of this family. -/
def carrierOfValue {t : Term} (ha : Typed [Ty.content] t Ty.value) :
    Typed [Ty.content]
      (Term.app (Term.lam Ty.value (Term.liftAt 0 Term.unit)) t) Ty.unit :=
  Typed.app (Γ := []) (Δ := [Ty.content]) (a := Ty.value) (b := Ty.unit)
    (Typed.lam (Typed.weak (k := Ty.value) (t := Term.unit) (τ := Ty.unit)
      (by decide) Typed.unit))
    ha rfl

theorem carrierOfValue_full_weak {t : Term}
    (ha : Typed [Ty.content] t Ty.value) :
    Ty.value ∈ weakHeads (carrierOfValue ha) := by
  simp [carrierOfValue, weakHeads]

/-- THE GUARD CARRIER (the "circular" family), and it needs NOTHING but
the target itself: `λ(k : ▷unit). unit` applied to `next h`. The head is
FULL in the counting model (the guard is read `⊤`) and non-linear, so
this is a real full-headed `weak` node in a real `[content]`-rooted
`unit` tree. -/
def carrierLaterUnit {t : Term} (h : Typed [Ty.content] t Ty.unit) :
    Typed [Ty.content]
      (Term.app (Term.lam (Ty.later Ty.unit) (Term.liftAt 0 Term.unit))
        (Term.next t)) Ty.unit :=
  Typed.app (Γ := []) (Δ := [Ty.content]) (a := Ty.later Ty.unit) (b := Ty.unit)
    (Typed.lam (Typed.weak (k := Ty.later Ty.unit) (t := Term.unit) (τ := Ty.unit)
      (by decide) Typed.unit))
    (Typed.next h) rfl

theorem carrierLaterUnit_full_weak {t : Term}
    (h : Typed [Ty.content] t Ty.unit) :
    Ty.later Ty.unit ∈ weakHeads (carrierLaterUnit h) := by
  simp [carrierLaterUnit, weakHeads]

/-- … and its sub-derivation is the TARGET at the SAME sequent, strictly
smaller: so a MINIMAL `[content] ⊢ unit` tree cannot carry this node.
That is what "circular" means precisely — a well-foundedness argument,
not a closedness lemma. -/
theorem carrierLaterUnit_size {t : Term} (h : Typed [Ty.content] t Ty.unit) :
    size h < size (carrierLaterUnit h) := by
  have hw : size (Typed.weak (k := Ty.later Ty.unit) (t := Term.unit) (τ := Ty.unit)
      (by decide) (Typed.unit : Typed [] Term.unit Ty.unit)) = 2 := rfl
  have hl : size (Typed.lam (Typed.weak (k := Ty.later Ty.unit) (t := Term.unit)
      (τ := Ty.unit) (by decide) (Typed.unit : Typed [] Term.unit Ty.unit))) = 3 := by
    rw [size_lam]; omega
  rw [carrierLaterUnit, size_app, size_next, hl]
  omega

/-! ### 4. The model side: the full class is UNBOUNDED and the head is FREE

The counting model, verbatim from the record's probes: `content =
{w | 1 ≤ w}`, `unit = {0}`, `knower = ∅`, every other base `⊤`, the
guard `⊤`, tensor additive, arrow residual, a context the sum of its
positions. -/

def wInterp : Ty → Nat → Prop
  | .content, w => 1 ≤ w
  | .knower, _ => False
  | .knowledge, _ => True
  | .value, _ => True
  | .stream, _ => True
  | .trace, _ => True
  | .later _, _ => True
  | .tensor a b, w => ∃ m n, wInterp a m ∧ wInterp b n ∧ w = m + n
  | .arrow a b, w => ∀ n, wInterp a n → wInterp b (w + n)
  | .unit, w => w = 0

def wCtx : List Ty → Nat → Prop
  | [], w => w = 0
  | a :: Γ, w => ∃ m n, wInterp a m ∧ wCtx Γ n ∧ w = m + n

/-- "Full": the type has a positive budget — the model's veto list. -/
def Full (τ : Ty) : Prop := ∃ w, 1 ≤ w ∧ wInterp τ w

/-- "Neutral": the only heads `weak` survives. -/
def ZeroW (k : Ty) : Prop := ∀ w, wInterp k w → w = 0

theorem full_knowledge : Full Ty.knowledge := ⟨1, Nat.le_refl 1, True.intro⟩
theorem full_value : Full Ty.value := ⟨1, Nat.le_refl 1, True.intro⟩
theorem full_later_unit : Full (Ty.later Ty.unit) := ⟨1, Nat.le_refl 1, True.intro⟩

theorem nonlin_knowledge : Ty.knowledge.isLinear = false := rfl
theorem nonlin_value : Ty.value.isLinear = false := rfl
theorem nonlin_later_unit : (Ty.later Ty.unit).isLinear = false := rfl

theorem not_zeroW_of_full {k : Ty} (h : Full k) : ¬ ZeroW k := by
  obtain ⟨w, hw, hI⟩ := h
  intro hZ
  have := hZ w hI
  omega

theorem tySize_arrow_knower (X : Ty) :
    tySize (Ty.arrow Ty.knower X) = 2 + tySize X := by
  show 1 + tySize Ty.knower + tySize X = 2 + tySize X
  show 1 + 1 + tySize X = 2 + tySize X
  omega

/-- The full-and-non-linear class is UNBOUNDED. An arrow out of `knower`
is full for ANY codomain (the residual over `∅` is vacuous) and
non-linear whenever its codomain is, and each wrap adds 2 to the size,
so no size bound holds. Hence "the remaining full types are only the
circular ones" is false as a TYPE-side statement. -/
theorem full_nonlin_unbounded :
    ∀ n, ∃ τ, Full τ ∧ τ.isLinear = false ∧ n ≤ tySize τ
  | 0 => ⟨Ty.knowledge, full_knowledge, nonlin_knowledge, Nat.zero_le _⟩
  | n + 1 => by
      obtain ⟨τ, hF, hL, hS⟩ := full_nonlin_unbounded n
      refine ⟨Ty.arrow Ty.knower τ, ⟨1, Nat.le_refl 1, fun m hm => False.elim hm⟩, ?_, ?_⟩
      · show (Ty.knower.isLinear || τ.isLinear) = false
        rw [hL]; rfl
      · have h2 := tySize_arrow_knower τ
        omega

/-- THE BREAK, general form: a `weak` node at a FULL head cannot be
sound at a `unit` conclusion, for ANY context. No derivability of the
head is used — only the head's budget. -/
theorem weak_break_of_full {k : Ty} {Γ : List Ty} (hk : Full k)
    (hG : ∃ w, wCtx Γ w) :
    ¬ (∀ w, wCtx (k :: Γ) w → wInterp Ty.unit w) := by
  obtain ⟨wk, hw1, hIk⟩ := hk
  obtain ⟨wg, hGc⟩ := hG
  intro hS
  have hpos : wCtx (k :: Γ) (wk + wg) := ⟨wk, wg, hIk, hGc, rfl⟩
  have h0 : wk + wg = 0 := hS (wk + wg) hpos
  omega

/-- The record's break node, re-derived: `[knowledge] ⊢ unit` by `weak`
of `unit`. -/
def weakFullSeq : Typed [Ty.knowledge] Term.unit Ty.unit :=
  Typed.weak (k := Ty.knowledge) (t := Term.unit) (τ := Ty.unit) (by decide) Typed.unit

/-- … and it is NOT model-sound. -/
theorem weakFullSeq_not_sound :
    ¬ (∀ w, wCtx [Ty.knowledge] w → wInterp Ty.unit w) :=
  weak_break_of_full ⟨1, Nat.le_refl 1, True.intro⟩ ⟨0, rfl⟩

/-- The decisive half: `weak` has NO PREMISE on its head. Every
non-linear type can be a `weak` head, with no derivation anywhere, and
it shows up in the traversal. So a full-headed `weak` node needs no
`FullAt` DERIVATION — only a place to stand — and `ZeroW` (a valuation
condition) is the real obligation, not a derivability fact. -/
theorem any_nonlinear_head_free (k : Ty) (hk : k.isLinear = false)
    {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ) :
    k ∈ weakHeads (Typed.weak (Γ := Γ) (k := k) (t := t) (τ := τ) hk h) := by
  rw [weakHeads_weak]
  simp

/-- The same statement with no context at all: the head is legal even
when the whole tree is closed, so "the head must be derivable at
`[content]`" has no purchase on the rule. -/
theorem full_head_at_nil (k : Ty) (hk : k.isLinear = false) :
    ∃ (h : Typed [k] Term.unit Ty.unit), k ∈ weakHeads h :=
  ⟨Typed.weak (k := k) (t := Term.unit) (τ := Ty.unit) hk Typed.unit,
    any_nonlinear_head_free k hk Typed.unit⟩

end SCExtractor

/-! ## The provenance composition — the ZeroW transfer (probe scProvenance, transfer-landed)

The counting model is SOUND for 16 of 17 constructors with NO hypothesis,
and for `weak` under exactly `ZeroW k` — so the model's verdict transfers
to any tree whose weak heads are all budget-neutral:

  no_vanishing_of_zeroWeak : Typed [content] t unit → (∀ k ∈ weakHeads h, ZeroW k) → False

FIX IS INCLUDED (the guard reads `⊤`, so the crossed arrow at `w` gives
`a` at `w + 0` — no side condition), and `weak` is ALLOWED at every
neutral head (`weakAtUnit : [unit] ⊢ unit` is a real weak node in the
fragment) — strictly wider than `NoWeak` on both axes, and the weakest
hypothesis the model can carry at all.

The trichotomy's branches, decided: (1) a linear-containing head is
IMPOSSIBLE (the gate — `weakHeads_nonlinear`, 17 arms); (2) the neutral
vs full scale is computed (`zeroW_scale`: unit/knower neutral;
knowledge, value, every `▷a`, every `arrow knower X` full); (3) the
residual is exactly the `arrow knower ·` family — invisible to BOTH
machines (`ext_arrow_knower_blind`: the Ext arrow clause fails on the
DOMAIN condition `¬ NeedsK knower`, for every codomain; and
`not_zeroW_arrow_knower`). Open question #2 reduces to one carrier:
`openQ2_reduces_to_derivability` — a `[content] ⊢ arrow knower knowledge`
would place a full-headed weak into a `[content]`-rooted unit tree.

FALSIFIED HERE (the record's discipline): the briefed
`stream_fixfree_needs_streamvar` is FALSE — `streamWitness` at
`[unit, arrow content stream, content] ⊢ stream` is fix-free with NO
stream position (a `var` types `▷stream` at the singleton; an `app`
concludes `stream` from an arrow that merely needs one). Both in-tree
repairs (`sprop`, `extprop`) are satisfied by the knower position
itself, which is exactly where the banked kills stop.

The traversal gap, measured: `WeakHeadsNeutralAtContent` (every weak
head in a `[content]`-rooted unit tree is neutral) is SUFFICIENT
(`traversal_suffices`) and EQUIVALENT to the theorem
(`traversal_iff_no_vanishing` — backward by vacuity), so no size, frame
or class restriction turns the traversal into a lemma below the core.
The fix-pocket residual is named as a definition
(`ProvenanceFixResidual`, with `fix_supplies_stream`/
`fixNeedS_witness` its live witnesses); nothing asserts it. -/
namespace SCProvenance

open SCExtractor

/-! ### §0 Falsify first -/

/-- The trace-headed pseudo-witness `app (lam trace (weak unit)) (snoc nil
(var 0))` would be `[content] ⊢ unit` if `weak` accepted a `trace` head.
The gate `k.isLinear = false` refuses exactly the linear types. -/
theorem not_weak_trace : ¬ (Ty.trace.isLinear = false) := by decide

theorem not_weak_content : ¬ (Ty.content.isLinear = false) := by decide

theorem not_weak_stream : ¬ (Ty.stream.isLinear = false) := by decide

/-- The gate as a law: a head that is linear cannot be a `weak` head. -/
theorem weak_head_not_linear {k : Ty} (hk : k.isLinear = false)
    (hl : k.isLinear = true) : False := by
  rw [hk] at hl
  exact Bool.noConfusion hl

/-- The three linear bases, as one statement: none is a weakable head. -/
theorem linear_bases_not_weakable :
    (¬ Ty.content.isLinear = false) ∧ (¬ Ty.trace.isLinear = false) ∧
      (¬ Ty.stream.isLinear = false) :=
  ⟨not_weak_content, not_weak_trace, not_weak_stream⟩

/-- The banked `Ext` machine's arrow clause fails for EVERY `a = knower`
domain, INDEPENDENTLY of the codomain: the blind family is exactly
`arrow knower ·`, blind because of the DOMAIN. -/
theorem ext_arrow_knower_blind (X : Ty) : ¬ Ext (Ty.arrow Ty.knower X) :=
  fun h => h.2.2.1 True.intro

/-- The same blindness as an equivalence of the arrow clause. -/
theorem ext_arrow_domain_not_needsK {a b : Ty} (h : Ext (Ty.arrow a b)) :
    ¬ NeedsK a := h.2.2.1

/-- `arrow knower X` is non-linear whenever `X` is — a LEGAL weak head,
unlike everything the linearity gate excludes. -/
theorem arrow_knower_nonlinear {X : Ty} (hX : X.isLinear = false) :
    (Ty.arrow Ty.knower X).isLinear = false := by
  show (Ty.knower.isLinear || X.isLinear) = false
  rw [hX]
  rfl

/-- The fix gate at content-bearing contexts: `fix`'s side condition is
`AllNonLinear Γ`, and `content` is linear, so a fix can never fire where
a content position survives. -/
theorem allNonLinear_get {Γ : List Ty} (h : AllNonLinear Γ) {i : Nat} {b : Ty}
    (hp : Γ[i]? = some b) : b.isLinear = false := h i b hp

theorem not_allNonLinear_of_linear_pos {Γ : List Ty} {i : Nat} {b : Ty}
    (hb : b.isLinear = true) (hp : Γ[i]? = some b) : ¬ AllNonLinear Γ := by
  intro h
  have := allNonLinear_get h hp
  rw [hb] at this
  exact Bool.noConfusion this

/-- No fix over any context with a `content` head. -/
theorem no_fix_at_content_cons (Δ : List Ty) : ¬ AllNonLinear (Ty.content :: Δ) :=
  not_allNonLinear_of_linear_pos (b := Ty.content) rfl (List.get?_zero_cons' (l := Δ))

/-- … and no fix at `[content]` itself. -/
theorem no_fix_at_content : ¬ AllNonLinear [Ty.content] := by
  intro h
  have := allNonLinear_get h (List.get?_zero_cons' (l := ([] : List Ty)))
  exact Bool.noConfusion this

/-! #### Open question #2, reduced to ONE carrier

`arrow knower knowledge` can sit as a weak head in a `[content]`-rooted
unit tree EXACTLY when it is derivable at `[content]` — `weak` never
asks for a derivation of its head, it asks for a PLACE, and the only
rule that discharges a place of arrow type is `app`. -/

theorem arrow_knower_knowledge_nonlinear :
    (Ty.arrow Ty.knower Ty.knowledge).isLinear = false := by decide

/-- `arrow knower knowledge` is FULL in the counting model — on the
model's veto list. -/
theorem arrow_knower_knowledge_full : Full (Ty.arrow Ty.knower Ty.knowledge) :=
  ⟨1, Nat.le_refl 1, fun _ hn => False.elim hn⟩

def carrierOfArrowKnowerKnowledge {t : Term}
    (ha : Typed [Ty.content] t (Ty.arrow Ty.knower Ty.knowledge)) :
    Typed [Ty.content]
      (Term.app
        (Term.lam (Ty.arrow Ty.knower Ty.knowledge) (Term.liftAt 0 Term.unit)) t)
      Ty.unit :=
  Typed.app (Γ := []) (Δ := [Ty.content]) (a := Ty.arrow Ty.knower Ty.knowledge)
    (b := Ty.unit)
    (Typed.lam (Typed.weak (k := Ty.arrow Ty.knower Ty.knowledge) (t := Term.unit)
      (τ := Ty.unit) arrow_knower_knowledge_nonlinear Typed.unit))
    ha rfl

theorem carrierOfArrowKnowerKnowledge_full_weak {t : Term}
    (ha : Typed [Ty.content] t (Ty.arrow Ty.knower Ty.knowledge)) :
    Ty.arrow Ty.knower Ty.knowledge ∈ weakHeads (carrierOfArrowKnowerKnowledge ha) := by
  simp [carrierOfArrowKnowerKnowledge, weakHeads]

/-- The reduction: a `[content] ⊢ arrow knower knowledge` would put a
FULL-headed weak node into a `[content]`-rooted tree. The question's
answer equals that type's derivability at `[content]` (not decided
here; the LamArm-side core). -/
theorem openQ2_reduces_to_derivability
    (hex : ∃ t, Nonempty (Typed [Ty.content] t (Ty.arrow Ty.knower Ty.knowledge))) :
    ∃ u, ∃ (hu : Typed [Ty.content] u Ty.unit),
      Ty.arrow Ty.knower Ty.knowledge ∈ weakHeads hu := by
  obtain ⟨t, ⟨ha⟩⟩ := hex
  exact ⟨_, carrierOfArrowKnowerKnowledge ha,
    carrierOfArrowKnowerKnowledge_full_weak ha⟩

/-! ### §1 The briefed stream lemma is FALSE

`stream_fixfree_needs_streamvar` is refuted by `streamWitness`:
`app (weak (k := unit) (var 0)) (var 0)` at
`[unit, arrow content stream, content] ⊢ stream` — fix-free, no stream
position. A `var` types `▷stream` directly at the singleton, and an
`app` concludes `stream` from an arrow that merely NEEDS one. Both
in-tree repairs (`sprop`, `extprop`) are satisfied by the arrow
position / by a knower — the repaired forms say nothing about a stream
VAR, which is why the blind-family kill cannot run through a need
predicate alone. -/

def streamWitness :
    Typed [Ty.unit, Ty.arrow Ty.content Ty.stream, Ty.content]
      (Term.app (Term.liftAt 0 (Term.var 0)) (Term.var 0)) Ty.stream :=
  Typed.app (Γ := [Ty.unit, Ty.arrow Ty.content Ty.stream]) (Δ := [Ty.content])
    (a := Ty.content) (b := Ty.stream)
    (Typed.weak (k := Ty.unit) (t := Term.var 0) (τ := Ty.arrow Ty.content Ty.stream)
      (by decide) Typed.var)
    Typed.var rfl

theorem streamWitness_fixfree : fixCount streamWitness = 0 := rfl

/-- … and it has NO `stream` position. This is the refutation. -/
theorem streamWitness_no_stream_pos (i : Nat) :
    ([Ty.unit, Ty.arrow Ty.content Ty.stream, Ty.content] : List Ty)[i]? ≠
      some Ty.stream := by
  cases i with
  | zero =>
      rw [List.get?_zero_cons']
      decide
  | succ i1 =>
      cases i1 with
      | zero =>
          rw [List.get?_succ_cons', List.get?_zero_cons']
          decide
      | succ i2 =>
          cases i2 with
          | zero =>
              rw [List.get?_succ_cons', List.get?_succ_cons', List.get?_zero_cons']
              decide
          | succ i3 =>
              rw [List.get?_succ_cons', List.get?_succ_cons', List.get?_succ_cons',
                List.get?_nil']
              decide

/-- The briefed §1 statement, negated — the witness packed as a theorem. -/
theorem briefed_stream_lemma_false :
    ¬ (∀ (Γ : List Ty) (t : Term) (h : Typed Γ t Ty.stream), fixCount h = 0 →
        ∃ (i : Nat), Γ[i]? = some Ty.stream) := by
  intro H
  obtain ⟨i, hi⟩ := H _ _ streamWitness streamWitness_fixfree
  exact streamWitness_no_stream_pos i hi

theorem knower_is_ssupply : SSupply Ty.knower := Or.inr True.intro

theorem knower_is_ext : Ext Ty.knower := True.intro

/-- The witness's `Ext` position, which `extprop` lands on. -/
theorem arrow_content_stream_is_ext : Ext (Ty.arrow Ty.content Ty.stream) :=
  ⟨True.intro, fun h => h, fun h => h, fun h => h⟩

/-- The witness's supply position: index 1 is `SSupply` — `sprop` is
satisfied there too; the repair does not mention a `stream` VAR. -/
theorem streamWitness_has_ssupply_pos :
    ∃ (i : Nat) (b : Ty),
      ([Ty.unit, Ty.arrow Ty.content Ty.stream, Ty.content] : List Ty)[i]? = some b ∧
        SSupply b :=
  ⟨1, Ty.arrow Ty.content Ty.stream, by decide,
    Or.inl ⟨True.intro, fun h => h, fun h => h⟩⟩

/-- A `[knower]` context is NOT clean: the kill `no_ext_at_clean` cannot
be applied there, and `sprop` is satisfied by the knower itself — the
exact reason the banked kills stop at the `lam knower` binder. -/
theorem knower_ctx_not_clean :
    ¬ (∀ (i : Nat) (b : Ty), ([Ty.knower] : List Ty)[i]? = some b → ¬ SSupply b) := by
  intro H
  exact H 0 Ty.knower (List.get?_zero_cons' (l := ([] : List Ty))) knower_is_ssupply

/-- The `arrow knower ·` family is not merely `Ext`-blind: it is `ZeroW`
-blind too, so the model cannot count it either — invisible to BOTH
machines. -/
theorem not_zeroW_arrow_knower (X : Ty) : ¬ ZeroW (Ty.arrow Ty.knower X) := by
  intro hZ
  have h1 : wInterp (Ty.arrow Ty.knower X) 1 := fun n hn => False.elim hn
  have := hZ 1 h1
  exact absurd this (by decide)

/-! ### §3 The ZeroW scale

`ZeroW k` is a VALUATION condition on a TYPE — not a derivability fact —
which is what makes the §4 composition possible at all. The scale:
`unit` and `knower` neutral (safe to weaken); `knowledge`, `value`, any
`▷`, and every `arrow knower X` full (not safe). -/

theorem zeroW_unit : ZeroW Ty.unit := fun _ hw => hw

theorem zeroW_knower : ZeroW Ty.knower := fun _ hw => False.elim hw

theorem not_zeroW_knowledge : ¬ ZeroW Ty.knowledge := by
  intro hZ
  exact absurd (hZ 1 True.intro) (by decide)

theorem not_zeroW_value : ¬ ZeroW Ty.value := by
  intro hZ
  exact absurd (hZ 1 True.intro) (by decide)

theorem not_zeroW_later (a : Ty) : ¬ ZeroW (Ty.later a) := by
  intro hZ
  exact absurd (hZ 1 True.intro) (by decide)

/-- … and the neutral ones are not vacuous: WELL-FORMED `weak` nodes at
them exist, so the fragment the composition covers is non-empty. -/
def weakAtUnit : Typed [Ty.unit] (Term.liftAt 0 Term.unit) Ty.unit :=
  Typed.weak (k := Ty.unit) (t := Term.unit) (τ := Ty.unit) (by decide) Typed.unit

theorem weakAtUnit_heads : weakHeads weakAtUnit = [Ty.unit] := rfl

theorem weakAtUnit_neutral : ∀ k, k ∈ weakHeads weakAtUnit → ZeroW k := by
  intro k hk
  rw [weakAtUnit_heads] at hk
  have : k = Ty.unit := by simpa using hk
  subst this
  exact zeroW_unit

/-! #### §3.1 The three-way classification of a non-linear interpretation

`wInterp` of a NON-LINEAR type is one of `∅`, `{0}`, `⊤`. This is what
the `contr` arm needs: a contraction duplicates a position, and the
duplicate's budget must be `0` — which exists exactly when `0 ∈ wInterp
k`, and `0 ∉ wInterp k` forces the interpretation EMPTY, so the context
cannot be funded in the first place. -/

theorem threeWay (τ : Ty) (hlin : τ.isLinear = false) :
    (∀ w, ¬ wInterp τ w) ∨ (∀ w, wInterp τ w ↔ w = 0) ∨ (∀ w, wInterp τ w) := by
  cases τ with
  | content => exact Bool.noConfusion hlin
  | knower => exact Or.inl (fun _ hw => hw)
  | knowledge => exact Or.inr (Or.inr (fun _ => True.intro))
  | value => exact Or.inr (Or.inr (fun _ => True.intro))
  | stream => exact Bool.noConfusion hlin
  | trace => exact Bool.noConfusion hlin
  | unit => exact Or.inr (Or.inl (fun _ => Iff.rfl))
  | later a => exact Or.inr (Or.inr (fun _ => True.intro))
  | tensor a b =>
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using hlin)
      rcases threeWay a h'.1 with haE | haZ | haT <;>
        rcases threeWay b h'.2 with hbE | hbZ | hbT
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
      rcases threeWay a h'.1 with haE | haZ | haT <;>
        rcases threeWay b h'.2 with hbE | hbZ | hbT
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

/-- The consequence the `contr` arm consumes: `0` is a `k`-budget, or
`k` has no budget at all. -/
theorem zero_available_of_nonlinear (k : Ty) (hk : k.isLinear = false) :
    wInterp k 0 ∨ (∀ m, ¬ wInterp k m) := by
  rcases threeWay k hk with hE | hZ | hT
  · exact Or.inr hE
  · exact Or.inl ((hZ 0).mpr rfl)
  · exact Or.inl (hT 0)

/-! #### §3.2 The context arithmetic -/

theorem wCtx_nil {w : Nat} (h : wCtx [] w) : w = 0 := h

theorem wCtx_cons {a : Ty} {Γ : List Ty} {w : Nat} (h : wCtx (a :: Γ) w) :
    ∃ m n, wInterp a m ∧ wCtx Γ n ∧ w = m + n := h

/-- Budgets split across an ordered concatenation — the lemma every
`app`/`pair`/`lete` arm needs. -/
theorem wCtx_append : ∀ {Γ Δ : List Ty} {w : Nat}, wCtx (Γ ++ Δ) w →
    ∃ m n, wCtx Γ m ∧ wCtx Δ n ∧ w = m + n
  | [], Δ, w, h => ⟨0, w, rfl, h, by omega⟩
  | a :: Γ', Δ, w, h => by
      obtain ⟨m, n, ha, hrest, he⟩ := wCtx_cons h
      obtain ⟨m', n', hG, hD, he'⟩ := wCtx_append hrest
      exact ⟨m + m', n', ⟨m, m', ha, hG, rfl⟩, hD, by omega⟩

/-! ### §4 THE COMPOSITION — soundness conditioned on the weak heads

The counting model (transplanted verbatim from `Dcare.SCExtractor`) is
made SOUND for 16 of the 17 constructors WITHOUT hypothesis and for
`weak` under exactly `ZeroW k`: `fix` needs NO side condition (the
guard reads `⊤`, so `(▷a → a)` at `w` gives `a` at `w + 0`), `gen` is
absorbed (the residual over `∅` is vacuous), `contr` closes on
`zero_available_of_nonlinear`, and the splits close on `wCtx_append`.
A fragment theorem on the WEAK AXIS ONLY. -/

theorem sound_of_zeroWeak :
    ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
      (∀ k, k ∈ weakHeads h → ZeroW k) → ∀ w, wCtx Γ w → wInterp τ w
  | _, _, _, Typed.var, _, w, hw => by
      obtain ⟨m, n, hm, hn, he⟩ := wCtx_cons hw
      have hn0 : n = 0 := wCtx_nil hn
      rw [show w = m by omega]
      exact hm
  | _, _, _, @Typed.lam Γ a b body h, hZ, w, hw => by
      simp only [weakHeads] at hZ
      intro n hn
      exact sound_of_zeroWeak h hZ (w + n) ⟨n, w, hn, hw, by omega⟩
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hZ, w, hw => by
      simp only [weakHeads] at hZ
      have hZf : ∀ k, k ∈ weakHeads hf → ZeroW k :=
        fun k hk => hZ k (List.mem_append.mpr (Or.inl hk))
      have hZa : ∀ k, k ∈ weakHeads ha → ZeroW k :=
        fun k hk => hZ k (List.mem_append.mpr (Or.inr hk))
      obtain ⟨m, n, hΓ, hΔ, he⟩ :=
        wCtx_append (Γ := Γ) (Δ := Δ) (w := w) (by simpa only [← hs] using hw)
      have h1 := sound_of_zeroWeak hf hZf m hΓ
      have h2 := sound_of_zeroWeak ha hZa n hΔ
      have h3 : wInterp b (m + n) := h1 n h2
      rw [he]
      exact h3
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hZ, w, hw => by
      simp only [weakHeads] at hZ
      have hZl : ∀ k, k ∈ weakHeads hl → ZeroW k :=
        fun k hk => hZ k (List.mem_append.mpr (Or.inl hk))
      have hZr : ∀ k, k ∈ weakHeads hr → ZeroW k :=
        fun k hk => hZ k (List.mem_append.mpr (Or.inr hk))
      obtain ⟨m, n, hΓ, hΔ, he⟩ :=
        wCtx_append (Γ := Γ) (Δ := Δ) (w := w) (by simpa only [← hs] using hw)
      exact ⟨m, n, sound_of_zeroWeak hl hZl m hΓ,
        sound_of_zeroWeak hr hZr n hΔ, he⟩
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hZ, w, hw => by
      simp only [weakHeads] at hZ
      have hZt : ∀ k, k ∈ weakHeads ht → ZeroW k :=
        fun k hk => hZ k (List.mem_append.mpr (Or.inl hk))
      have hZb : ∀ k, k ∈ weakHeads hb → ZeroW k :=
        fun k hk => hZ k (List.mem_append.mpr (Or.inr hk))
      obtain ⟨m, n, hΓ, hΔ, he⟩ :=
        wCtx_append (Γ := Γ₁) (Δ := Γ₂) (w := w) (by simpa only [← hs] using hw)
      obtain ⟨ma, mb, hia, hib, hme⟩ := sound_of_zeroWeak ht hZt m hΓ
      have hctx : wCtx (b :: a :: Γ₂) (mb + (ma + n)) :=
        ⟨mb, ma + n, hib, ⟨ma, n, hia, hΔ, rfl⟩, rfl⟩
      have hres := sound_of_zeroWeak hb hZb (mb + (ma + n)) hctx
      have heq : mb + (ma + n) = (ma + mb) + n := by omega
      rw [heq] at hres
      rw [he, hme]
      exact hres
  | _, _, _, Typed.unit, _, w, hw => wCtx_nil hw
  | _, _, _, @Typed.next Γ a t h, _, w, hw => True.intro
  | _, _, _, @Typed.fix Γ a body hΓ h, hZ, w, hw => by
      simp only [weakHeads] at hZ
      have h1 := sound_of_zeroWeak h hZ w hw
      have h2 := h1 0 True.intro
      simpa using h2
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, _, w, hw => True.intro
  | _, _, _, Typed.nil, _, w, hw => True.intro
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs, _, w, hw => True.intro
  | _, _, _, Typed.gen, _, w, hw => fun n hn => False.elim hn
  | _, _, _, Typed.red, _, w, hw => fun n hn => True.intro
  | _, _, _, Typed.obj, _, w, hw => fun n hn => True.intro
  | _, _, _, Typed.terminate, _, w, hw => fun n hn => False.elim hn
  | _, _, _, @Typed.contr Γ k t τ hk h, hZ, w, hw => by
      simp only [weakHeads] at hZ
      obtain ⟨m, n, hkm, hΓn, he⟩ := wCtx_cons hw
      rcases zero_available_of_nonlinear k hk with h0 | hempty
      · have hkk : wCtx (k :: k :: Γ) w :=
          ⟨0, m + n, h0, ⟨m, n, hkm, hΓn, rfl⟩, by omega⟩
        exact sound_of_zeroWeak h hZ w hkk
      · exact False.elim (hempty m hkm)
  | _, _, _, @Typed.weak Γ k t τ hk h, hZ, w, hw => by
      rw [weakHeads_weak hk h] at hZ
      have hZk : ZeroW k := hZ k (by simp)
      have hZh : ∀ j, j ∈ weakHeads h → ZeroW j :=
        fun j hj => hZ j (List.mem_cons.mpr (Or.inr hj))
      obtain ⟨m, n, hkm, hΓn, he⟩ := wCtx_cons hw
      have hm0 : m = 0 := hZk m hkm
      have hres := sound_of_zeroWeak h hZh n hΓn
      rw [show w = n by omega]
      exact hres

/-- THE PRIZE — the deepest vanishing fragment reached here: `fix` IN,
`weak` IN at every neutral head. `[content] ⊢ unit` is dead. -/
theorem no_vanishing_of_zeroWeak {t : Term} (h : Typed [Ty.content] t Ty.unit)
    (hZ : ∀ k, k ∈ weakHeads h → ZeroW k) : False := by
  have hw : wCtx [Ty.content] 1 := ⟨1, 0, Nat.le_refl 1, rfl, by omega⟩
  have h1 : wInterp Ty.unit 1 := sound_of_zeroWeak h hZ 1 hw
  have h1' : (1 : Nat) = 0 := h1
  omega

/-- The same theorem in the "every weak head is neutral" shape. -/
theorem no_vanishing_fixfree_weak_of_heads {t : Term}
    (h : Typed [Ty.content] t Ty.unit)
    (hZ : ∀ k, k ∈ weakHeads h → ZeroW k) : False :=
  no_vanishing_of_zeroWeak h hZ

/-! ### §5 The fix-inclusive wall, measured and named

(a) The position-origin regress FAILS at the fix-inclusive grain: a
surface stream is derivable at `[knower]` and its stream is funded by
the FIX ITSELF — the in-tree `spropF`/`FixNeedS` escape is a SOURCE,
not a conduit. (b) The §4 hypothesis is exactly what a minimal tree
must supply, and it is EQUIVALENT to the theorem — the traversal is the
theorem at one remove. (c) The residual, shaped from (a). -/

/-- The fix funds the stream. `[knower] ⊢ stream` with a fix node. -/
theorem fix_supplies_stream :
    ∃ (t : Term) (h : Typed [Ty.knower] t Ty.stream), 0 < fixCount h :=
  ⟨Term.fix (Term.lam (Ty.later Ty.stream) flip2),
    Typed.fix knower_ctx_nonlinear (Typed.lam flip2Typed),
    by simp only [fixCount]; omega⟩

/-- … and it is a `FixNeedS` node in the in-tree sense — the escape is
REAL, not a definition that never fires. -/
theorem fixNeedS_witness :
    ∃ (t : Term) (h : Typed [Ty.knower] t Ty.stream), FixNeedS h :=
  ⟨_, Typed.fix knower_ctx_nonlinear (Typed.lam flip2Typed),
    FixNeedS.here knower_ctx_nonlinear (Typed.lam flip2Typed) True.intro⟩

/-- The trichotomy's zero branch as one statement: the neutral heads and
the full ones. -/
theorem zeroW_scale :
    ZeroW Ty.unit ∧ ZeroW Ty.knower ∧ ¬ ZeroW Ty.knowledge ∧ ¬ ZeroW Ty.value ∧
      (∀ a : Ty, ¬ ZeroW (Ty.later a)) ∧ (∀ X : Ty, ¬ ZeroW (Ty.arrow Ty.knower X)) :=
  ⟨zeroW_unit, zeroW_knower, not_zeroW_knowledge, not_zeroW_value,
    not_zeroW_later, not_zeroW_arrow_knower⟩

/-- THE TRAVERSAL GAP, named as a definition: every weak head in a
`[content]`-rooted `unit` tree is budget-neutral. This is what the
position-origin induction would have to establish arm by arm; §4 shows
it is SUFFICIENT. -/
def WeakHeadsNeutralAtContent : Prop :=
  ∀ (t : Term) (h : Typed [Ty.content] t Ty.unit), ∀ k, k ∈ weakHeads h → ZeroW k

theorem traversal_suffices (H : WeakHeadsNeutralAtContent) (t : Term)
    (h : Typed [Ty.content] t Ty.unit) : False :=
  no_vanishing_of_zeroWeak h (H t h)

/-- … and it is not weaker than the theorem: the two are equivalent
(backward by vacuity, which is why no size/frame/class restriction can
turn the traversal into a lemma below the core). -/
theorem traversal_iff_no_vanishing :
    WeakHeadsNeutralAtContent ↔
      (∀ (t : Term), Typed [Ty.content] t Ty.unit → False) :=
  ⟨fun H t h => traversal_suffices H t h,
   fun H _t _h _k _ => False.elim (H _t _h)⟩

/-- THE FIX-INCLUSIVE RESIDUAL — a DEFINITION, not a theorem, and
nothing below depends on it: every weak head is neutral, OR the tree
carries a fixpoint whose payload carries the stream need. It is a
strict weakening of `WeakHeadsNeutralAtContent`, and its second
disjunct fires in the wild. -/
def ProvenanceFixResidual : Prop :=
  ∀ (t : Term) (h : Typed [Ty.content] t Ty.unit), ∀ (k : Ty),
    k ∈ weakHeads h → ZeroW k ∨ FixNeedS h

theorem fixResidual_of_traversal (H : WeakHeadsNeutralAtContent) :
    ProvenanceFixResidual :=
  fun t h k hk => Or.inl (H t h k hk)

/-! #### The trichotomy's LINEAR branch is impossible — traversed

Every head the `weakHeads` traversal ever returns is non-linear, so
`zero_available_of_nonlinear` applies to EVERY weak head. -/

theorem weakHeads_nonlinear : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    ∀ k, k ∈ weakHeads h → k.isLinear = false
  | _, _, _, Typed.var, _, hk => by simp [weakHeads] at hk
  | _, _, _, @Typed.lam Γ a b body h, k, hk => weakHeads_nonlinear h k hk
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, k, hk => by
      simp only [weakHeads] at hk
      rcases List.mem_append.mp hk with h | h
      · exact weakHeads_nonlinear hf k h
      · exact weakHeads_nonlinear ha k h
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, k, hk => by
      simp only [weakHeads] at hk
      rcases List.mem_append.mp hk with h | h
      · exact weakHeads_nonlinear hl k h
      · exact weakHeads_nonlinear hr k h
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, k, hk => by
      simp only [weakHeads] at hk
      rcases List.mem_append.mp hk with h | h
      · exact weakHeads_nonlinear ht k h
      · exact weakHeads_nonlinear hb k h
  | _, _, _, Typed.unit, _, hk => by simp [weakHeads] at hk
  | _, _, _, @Typed.next Γ a t h, k, hk => weakHeads_nonlinear h k hk
  | _, _, _, @Typed.fix Γ a body hΓ h, k, hk => weakHeads_nonlinear h k hk
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, k, hk => by
      simp only [weakHeads] at hk
      rcases List.mem_append.mp hk with h | h
      · exact weakHeads_nonlinear hc k h
      · exact weakHeads_nonlinear ht k h
  | _, _, _, Typed.nil, _, hk => by simp [weakHeads] at hk
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs, k, hk => by
      simp only [weakHeads] at hk
      rcases List.mem_append.mp hk with h | h
      · exact weakHeads_nonlinear ht k h
      · exact weakHeads_nonlinear hu k h
  | _, _, _, Typed.gen, _, hk => by simp [weakHeads] at hk
  | _, _, _, Typed.red, _, hk => by simp [weakHeads] at hk
  | _, _, _, Typed.obj, _, hk => by simp [weakHeads] at hk
  | _, _, _, Typed.terminate, _, hk => by simp [weakHeads] at hk
  | _, _, _, @Typed.contr Γ kk t τ hk0 h, k, hk => weakHeads_nonlinear h k hk
  | _, _, _, @Typed.weak Γ kk t τ hk0 h, k, hk => by
      rw [weakHeads_weak hk0 h] at hk
      rcases List.mem_cons.mp hk with h' | h'
      · rw [h']; exact hk0
      · exact weakHeads_nonlinear h k h'

/-- The fix-free shape carries its `fixCount = 0` hypothesis UNUSED —
the composition never looks at the fix count, so the fragment theorem
above does not need the restriction. -/
theorem no_vanishing_fixfree_weak {t : Term} (h : Typed [Ty.content] t Ty.unit)
    (hf : fixCount h = 0) (hZ : ∀ k, k ∈ weakHeads h → ZeroW k) : False := by
  have _ : fixCount h = 0 := hf
  exact no_vanishing_of_zeroWeak h hZ

end SCProvenance

/-! ## The provenance invariant + the binder-disciplined traversal (probe scProvenance2, transfer-landed)

THE USER'S POSITION-INTRODUCTION PREDICATE, PROVEN: `weakHeads_subset`
(17 arms, size-free) — every weak head is a position of the derivation's
own conclusion context OR a `lam`/`lete` binder type (`binderTys`). No
induction on size, no minimality: the traversal is one case analysis.

THE FRAME KILL, repaired: `no_unit_at_frame_of_zeroWeak` — a `unit`
conclusion at ANY frame `Γ ++ content :: Δ` whose sides are FUNDED at
budget 0 is impossible (the sides' budgets are 0, content's is ≥ 1,
unit's is 0: arithmetic). The funding hypothesis is load-bearing,
kernel-measured: the killer fire at `[arrow content unit, content] ⊢
unit` has NO weak node and vacuously-ZeroW sides — but its side is
UNFUNDED (`arrow content unit` has an empty interpretation), so the
model is silent there (`briefed_frame_lemma_false`).

THE COMPOSITION: `frameTraversal_of_binderDiscipline` — at a frame with
ZeroW sides, a tree whose binders are all neutral-or-linear has only
neutral weak heads (the invariant disposes of the position half; the
discipline disposes of the binder half; `weak`/`contr` roots close by
the frame shape alone: the introduced position IS a frame side). Hence

  no_vanishing_of_binderWall : BinderWall → ∀ t, Typed [content] t unit → False

where `BinderWall` := at every funded frame, no `lam`/`lete` binder
carries a Full non-linear type. THE ONE REMAINING WALL, and it is not
free: `binderWall_forbids_openQ2` (BinderWall refutes a `[content] ⊢
knowledge`), and F3 measures that the app-root's inherited obligation
(`ContentFreeTraversal`) is FALSE (`λ(k:knowledge). unit : [] ⊢
knowledge ⊸ unit` exists — `contentFreeTraversal_false`). So the
unrestricted `FrameTraversal` is refuted modulo open question #2, and
the fix pockets sit outside the frame theory entirely (fix is gated off
every frame; `[knower]` is unfunded) — consistent with the banked
`fix_supplies_stream`/`knowledge_at_knower`. -/
namespace SCProvenance2

open SCExtractor
open SCProvenance

/-! ### §0 Falsify first -/

/-- `arrow content unit` is interpreted EMPTY: no budget satisfies it. -/
theorem arrow_content_unit_empty (w : Nat) :
    ¬ wInterp (Ty.arrow Ty.content Ty.unit) w := by
  intro h
  have h1 : wInterp Ty.unit (w + 1) := h 1 (Nat.le_refl 1)
  have h2 : w + 1 = 0 := h1
  omega

/-- … hence it is `ZeroW` VACUOUSLY — this is why the round's first
frame hypothesis could not see it. -/
theorem zeroW_arrow_content_unit : ZeroW (Ty.arrow Ty.content Ty.unit) :=
  fun w hw => False.elim (arrow_content_unit_empty w hw)

/-- THE KILLER FIRE: `app (var 0) (var 0)` at `[arrow content unit,
content] ⊢ unit` — a derivation of the target type at a frame whose
sides are `ZeroW` and which has no weak node at all. -/
def killerFire :
    Typed [Ty.arrow Ty.content Ty.unit, Ty.content]
      (Term.app (Term.var 0) (Term.var 0)) Ty.unit :=
  Typed.app (Γ := [Ty.arrow Ty.content Ty.unit]) (Δ := [Ty.content])
    (a := Ty.content) (b := Ty.unit) Typed.var Typed.var rfl

theorem killerFire_heads : weakHeads killerFire = [] := rfl

theorem killerFire_no_bad_head : ∀ k, k ∈ weakHeads killerFire → ZeroW k := by
  intro k hk
  rw [killerFire_heads] at hk
  exact absurd hk (by simp)

/-- The frame's side position is UNFUNDED: the model has no budget for
an `arrow content unit` position, so `sound_of_zeroWeak` is vacuously
true there and no contradiction is available. -/
theorem arrow_content_unit_unfunded :
    ¬ ∃ w, wCtx [Ty.arrow Ty.content Ty.unit] w := by
  intro hex
  obtain ⟨w, hw⟩ := hex
  obtain ⟨m, n, hm, hn, he⟩ := wCtx_cons hw
  exact arrow_content_unit_empty m hm

theorem killer_context_unfunded :
    ¬ ∃ w, wCtx [Ty.arrow Ty.content Ty.unit, Ty.content] w := by
  intro hex
  obtain ⟨w, hw⟩ := hex
  obtain ⟨m, n, hm, hn, he⟩ := wCtx_cons hw
  exact arrow_content_unit_empty m hm

/-- The round's briefed frame lemma, NEGATED: all its hypotheses hold
at `Γ = [arrow content unit]`, `Δ = []` — the funding hypothesis is the
missing one. -/
theorem briefed_frame_lemma_false :
    ¬ (∀ (Γ Δ : List Ty) (t : Term)
        (h : Typed (Γ ++ Ty.content :: Δ) t Ty.unit),
        (∀ p, p ∈ Γ → ZeroW p) → (∀ p, p ∈ Δ → ZeroW p) →
        (∀ k, k ∈ weakHeads h → ZeroW k) → False) := by
  intro H
  refine H [Ty.arrow Ty.content Ty.unit] [] _ killerFire ?_ ?_ ?_
  · intro p hp
    have hp' : p = Ty.arrow Ty.content Ty.unit := by simpa using hp
    subst hp'
    exact zeroW_arrow_content_unit
  · intro p hp
    exact absurd hp (by simp)
  · exact killerFire_no_bad_head

/-- `λ(k : knowledge). unit : [] ⊢ knowledge ⊸ unit`. Its weak head is
the lam BINDER's type, and the binder is the only source. -/
def lamKnowledgeUnit :
    Typed [] (Term.lam Ty.knowledge (Term.liftAt 0 Term.unit))
      (Ty.arrow Ty.knowledge Ty.unit) :=
  Typed.lam (Typed.weak (k := Ty.knowledge) (t := Term.unit) (τ := Ty.unit)
    (by decide) Typed.unit)

theorem lamKnowledgeUnit_heads :
    weakHeads lamKnowledgeUnit = [Ty.knowledge] := rfl

/-- F3: the content-free FUNCTION-piece lemma the app root would need is
FALSE. Context `[]` is funded at 0 and vacuously `ZeroW`; the type is
`arrow _ unit`; the head is non-neutral. No inheritance argument can
prove the app root's fn piece neutral. -/
theorem contentFree_fn_lemma_false :
    ¬ (∀ (Γf : List Ty) (a : Ty) (fn : Term) (h : Typed Γf fn (Ty.arrow a Ty.unit)),
        wCtx Γf 0 → (∀ p, p ∈ Γf → ZeroW p) →
        ∀ k, k ∈ weakHeads h → ZeroW k) := by
  intro H
  exact not_zeroW_knowledge
    (H [] Ty.knowledge _ lamKnowledgeUnit rfl (fun p hp => by simp at hp)
      Ty.knowledge (by rw [lamKnowledgeUnit_heads]; simp))

/-- F4: the "bad head" class is EXACTLY the model's full class — the
obstruction the traversal cannot rule out is a TYPE-level one, not a
tree-shape one. -/
theorem full_of_not_zeroW {k : Ty} (h : ¬ ZeroW k) : Full k :=
  Classical.byContradiction fun hc =>
    h fun w hw => by
      cases Nat.eq_zero_or_pos w with
      | inl h0 => exact h0
      | inr hp => exact absurd ⟨w, hp, hw⟩ hc

theorem not_zeroW_iff_full (k : Ty) : ¬ ZeroW k ↔ Full k :=
  ⟨full_of_not_zeroW, not_zeroW_of_full⟩

/-! ### §1 The repaired frame kill -/

theorem wCtx_zero_of_zeroW : ∀ {Γ : List Ty} {w : Nat}, wCtx Γ w →
    (∀ p, p ∈ Γ → ZeroW p) → w = 0
  | [], w, hw, _ => hw
  | a :: Γ', w, hw, hZ => by
      obtain ⟨m, n, ha, hrest, he⟩ := wCtx_cons hw
      have hm : m = 0 := hZ a (by simp) m ha
      have hn : n = 0 :=
        wCtx_zero_of_zeroW hrest (fun p hp => hZ p (by simp [hp]))
      omega

theorem wCtx_append_of : ∀ {Γ Δ : List Ty} {m n : Nat}, wCtx Γ m → wCtx Δ n →
    wCtx (Γ ++ Δ) (m + n)
  | [], Δ, m, n, hΓ, hΔ => by
      rw [show m = 0 from hΓ]
      simpa using hΔ
  | a :: Γ', Δ, m, n, hΓ, hΔ => by
      obtain ⟨m1, m2, ha, hrest, he⟩ := wCtx_cons hΓ
      exact ⟨m1, m2 + n, ha, wCtx_append_of hrest hΔ, by rw [he]; omega⟩

theorem wCtx_cons_tail {a : Ty} {Γ : List Ty} (h : wCtx (a :: Γ) 0) :
    wCtx Γ 0 := by
  obtain ⟨m, n, _, hn, he⟩ := wCtx_cons h
  have hn0 : n = 0 := by omega
  rw [← hn0]
  exact hn

/-- A prefix of a zero-budget context is funded at zero. -/
theorem wCtx_prefix {Γf Γ₁ Γ : List Ty} (hs : Γf ++ Γ₁ = Γ) (h : wCtx Γ 0) :
    wCtx Γf 0 := by
  rw [← hs] at h
  obtain ⟨m, n, hm, _, he⟩ := wCtx_append (Γ := Γf) (Δ := Γ₁) h
  have hm0 : m = 0 := by omega
  rw [← hm0]
  exact hm

/-- THE FRAME'S OWN FUNDING: sides funded at zero, the content position
at `1`, so the whole frame costs exactly `1`. -/
theorem wCtx_frame {Γ Δ : List Ty} (hΓ : wCtx Γ 0) (hΔ : wCtx Δ 0) :
    wCtx (Γ ++ Ty.content :: Δ) 1 := by
  have hc : wInterp Ty.content 1 := Nat.le_refl 1
  have hrest : wCtx (Ty.content :: Δ) 1 := ⟨1, 0, hc, hΔ, by omega⟩
  have := wCtx_append_of (Γ := Γ) (Δ := Ty.content :: Δ) (m := 0) (n := 1) hΓ hrest
  simpa using this

/-- The sides' zero budget, from ZeroW plus funding. -/
theorem wCtx_zero_of_funded {Γ : List Ty}
    (hZ : ∀ p, p ∈ Γ → ZeroW p) (hf : ∃ w, wCtx Γ w) : wCtx Γ 0 := by
  obtain ⟨w, hw⟩ := hf
  rw [← wCtx_zero_of_zeroW hw hZ]
  exact hw

/-- THE FRAME KILL: a `unit` conclusion at a frame whose sides are
funded at zero and whose weak heads are neutral is impossible.
`[content]` is the round-1 instance. -/
theorem no_unit_at_frame_of_zeroWeak {Γ Δ : List Ty} {t : Term}
    (h : Typed (Γ ++ Ty.content :: Δ) t Ty.unit)
    (hΓ : wCtx Γ 0) (hΔ : wCtx Δ 0)
    (hW : ∀ k, k ∈ weakHeads h → ZeroW k) : False := by
  have hw : wCtx (Γ ++ Ty.content :: Δ) 1 := wCtx_frame hΓ hΔ
  have h1 : wInterp Ty.unit 1 := sound_of_zeroWeak h hW 1 hw
  have h1' : (1 : Nat) = 0 := h1
  omega

/-- The same theorem with ZeroW sides instead of `wCtx · 0`, plus the
funding hypothesis. -/
theorem no_unit_at_frame_of_zeroWeak_funded {Γ Δ : List Ty} {t : Term}
    (h : Typed (Γ ++ Ty.content :: Δ) t Ty.unit)
    (hΓ : ∀ p, p ∈ Γ → ZeroW p) (hΔ : ∀ p, p ∈ Δ → ZeroW p)
    (fΓ : ∃ w, wCtx Γ w) (fΔ : ∃ w, wCtx Δ w)
    (hW : ∀ k, k ∈ weakHeads h → ZeroW k) : False :=
  no_unit_at_frame_of_zeroWeak h (wCtx_zero_of_funded hΓ fΓ)
    (wCtx_zero_of_funded hΔ fΔ) hW

/-- Round 1 re-derived as the `[]`/`[]` instance. -/
theorem no_vanishing_frame_singleton {t : Term}
    (h : Typed [Ty.content] t Ty.unit)
    (hW : ∀ k, k ∈ weakHeads h → ZeroW k) : False :=
  no_unit_at_frame_of_zeroWeak (Γ := []) (Δ := []) h rfl rfl hW

theorem knower_unfunded : ¬ ∃ w, wCtx [Ty.knower] w := by
  intro hex
  obtain ⟨w, hw⟩ := hex
  obtain ⟨m, n, hm, hn, he⟩ := wCtx_cons hw
  exact hm

/-- A frame with a prepended non-linear position inherits every
derivation of the frame without it — the frames the kill cannot see are
not weaker than the `[content]` core. -/
def frame_weak_reduce {Γ Δ : List Ty} {t : Term} {τ : Ty} (k : Ty)
    (hk : k.isLinear = false) (h : Typed (Γ ++ Ty.content :: Δ) t τ) :
    Typed ((k :: Γ) ++ Ty.content :: Δ) (Term.liftAt 0 t) τ :=
  Typed.weak hk h

theorem core_reaches_knower_frame {t : Term} (h : Typed [Ty.content] t Ty.unit) :
    Nonempty (Typed [Ty.knower, Ty.content] (Term.liftAt 0 t) Ty.unit) :=
  ⟨frame_weak_reduce (Γ := []) (Δ := []) Ty.knower (by decide) h⟩

theorem core_reaches_full_frame {t : Term} (h : Typed [Ty.content] t Ty.unit) :
    Nonempty (Typed [Ty.knowledge, Ty.content] (Term.liftAt 0 t) Ty.unit) :=
  ⟨frame_weak_reduce (Γ := []) (Δ := []) Ty.knowledge (by decide) h⟩

/-- The fix pocket is OUTSIDE the frame theory, not contradicted by it:
`[knower]`-rooted statements are UNFUNDED, so the model is silent. -/
theorem knower_pocket_outside_model :
    (¬ ∃ w, wCtx [Ty.knower] w) ∧ (¬ ∃ w, wCtx [Ty.knower, Ty.knower] w) := by
  refine ⟨knower_unfunded, ?_⟩
  intro hex
  obtain ⟨w, hw⟩ := hex
  obtain ⟨m, n, _, hn, _⟩ := wCtx_cons hw
  exact knower_unfunded ⟨n, hn⟩

theorem frame_unit_side_funded : wCtx [Ty.unit] 0 := ⟨0, 0, rfl, rfl, rfl⟩

theorem frame_unit_tensor_funded : wCtx [Ty.tensor Ty.unit Ty.unit] 0 :=
  ⟨0, 0, ⟨0, 0, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Funding and neutrality are INDEPENDENT: a guard side is funded at 0
but never neutral — the repaired kill's hypothesis is strictly weaker
than a ZeroW-sides one. -/
theorem later_side_funded_not_neutral :
    wCtx [Ty.later Ty.unit] 0 ∧ ¬ ZeroW (Ty.later Ty.unit) :=
  ⟨⟨0, 0, True.intro, rfl, rfl⟩, not_zeroW_later Ty.unit⟩

theorem no_vanishing_frame_unit_left {t : Term}
    (h : Typed (Ty.unit :: Ty.content :: ([] : List Ty)) t Ty.unit)
    (hW : ∀ k, k ∈ weakHeads h → ZeroW k) : False :=
  no_unit_at_frame_of_zeroWeak (Γ := [Ty.unit]) (Δ := []) h
    frame_unit_side_funded rfl hW

theorem no_vanishing_frame_unit_right {t : Term}
    (h : Typed [Ty.content, Ty.unit] t Ty.unit)
    (hW : ∀ k, k ∈ weakHeads h → ZeroW k) : False :=
  no_unit_at_frame_of_zeroWeak (Γ := []) (Δ := [Ty.unit]) h
    rfl frame_unit_side_funded hW

/-- The necessity check: at `[knower]` (no content) the analogous
statement is FALSE, with every weak head neutral — the content position
is what makes the frame kill possible. -/
def unitAtKnower : Typed [Ty.knower] (Term.liftAt 0 Term.unit) Ty.unit :=
  Typed.weak (k := Ty.knower) (t := Term.unit) (τ := Ty.unit) (by decide) Typed.unit

theorem unitAtKnower_heads : weakHeads unitAtKnower = [Ty.knower] := rfl

theorem knower_frame_is_derivable_and_neutral :
    (Nonempty (Typed [Ty.knower] (Term.liftAt 0 Term.unit) Ty.unit)) ∧
      (∀ k, k ∈ weakHeads unitAtKnower → ZeroW k) := by
  refine ⟨⟨unitAtKnower⟩, ?_⟩
  intro k hk
  rw [unitAtKnower_heads] at hk
  have hk' : k = Ty.knower := by simpa using hk
  subst hk'
  exact zeroW_knower

/-! ### §2 The provenance invariant -/

/-- The types bound by `lam`/`lete` nodes, anywhere in the tree. -/
def binderTys : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → List Ty
  | _, _, _, Typed.var => []
  | _, _, _, @Typed.lam _ a _ _ h => a :: binderTys h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => binderTys hf ++ binderTys ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => binderTys hl ++ binderTys hr
  | _, _, _, @Typed.lete _ _ _ a b _ _ _ ht hb _ =>
      a :: b :: (binderTys ht ++ binderTys hb)
  | _, _, _, Typed.unit => []
  | _, _, _, @Typed.next _ _ _ h => binderTys h
  | _, _, _, @Typed.fix _ _ _ _ h => binderTys h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => binderTys hc ++ binderTys ht
  | _, _, _, Typed.nil => []
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => binderTys ht ++ binderTys hu
  | _, _, _, Typed.gen => []
  | _, _, _, Typed.red => []
  | _, _, _, Typed.obj => []
  | _, _, _, Typed.terminate => []
  | _, _, _, @Typed.contr _ _ _ _ _ h => binderTys h
  | _, _, _, @Typed.weak _ _ _ _ _ h => binderTys h

/-- EVERY WEAK HEAD COMES FROM ABOVE OR FROM A BINDER — the
position-origin traversal, 17 arms, size-free. -/
theorem weakHeads_subset : ∀ {Γ : List Ty} {t : Term} {τ : Ty}
    (h : Typed Γ t τ), ∀ k, k ∈ weakHeads h → k ∈ Γ ∨ k ∈ binderTys h
  | _, _, _, Typed.var, k, hk => by simp [weakHeads] at hk
  | _, _, _, @Typed.lam _ a _ _ h, k, hk => by
      simp only [weakHeads, binderTys] at hk ⊢
      rcases weakHeads_subset h k hk with hin | hb
      · rcases List.mem_cons.mp hin with rfl | hin'
        · exact Or.inr (by simp)
        · exact Or.inl hin'
      · exact Or.inr (by simp [hb])
  | _, _, _, @Typed.app E Γ Δ a b fn arg hf ha hs, k, hk => by
      simp only [weakHeads, binderTys] at hk ⊢
      rw [← hs]
      rcases List.mem_append.mp hk with hk' | hk'
      · rcases weakHeads_subset hf k hk' with hin | hb
        · exact Or.inl (by simp [hin])
        · exact Or.inr (by simp [hb])
      · rcases weakHeads_subset ha k hk' with hin | hb
        · exact Or.inl (by simp [hin])
        · exact Or.inr (by simp [hb])
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, k, hk => by
      simp only [weakHeads, binderTys] at hk ⊢
      rw [← hs]
      rcases List.mem_append.mp hk with hk' | hk'
      · rcases weakHeads_subset hl k hk' with hin | hb
        · exact Or.inl (by simp [hin])
        · exact Or.inr (by simp [hb])
      · rcases weakHeads_subset hr k hk' with hin | hb
        · exact Or.inl (by simp [hin])
        · exact Or.inr (by simp [hb])
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, k, hk => by
      simp only [weakHeads, binderTys] at hk ⊢
      rw [← hs]
      rcases List.mem_append.mp hk with hk' | hk'
      · rcases weakHeads_subset ht k hk' with hin | hbnd
        · exact Or.inl (by simp [hin])
        · exact Or.inr (by simp [hbnd])
      · rcases weakHeads_subset hb k hk' with hin | hbnd
        · rcases List.mem_cons.mp hin with rfl | hin'
          · exact Or.inr (by simp)
          · rcases List.mem_cons.mp hin' with rfl | hin''
            · exact Or.inr (by simp)
            · exact Or.inl (by simp [hin''])
        · exact Or.inr (by simp [hbnd])
  | _, _, _, Typed.unit, k, hk => by simp [weakHeads] at hk
  | _, _, _, @Typed.next _ _ _ h, k, hk => weakHeads_subset h k hk
  | _, _, _, @Typed.fix _ _ _ _ h, k, hk => weakHeads_subset h k hk
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, k, hk => by
      simp only [weakHeads, binderTys] at hk ⊢
      rw [← hs]
      rcases List.mem_append.mp hk with hk' | hk'
      · rcases weakHeads_subset hc k hk' with hin | hb
        · exact Or.inl (by simp [hin])
        · exact Or.inr (by simp [hb])
      · rcases weakHeads_subset ht k hk' with hin | hb
        · exact Or.inl (by simp [hin])
        · exact Or.inr (by simp [hb])
  | _, _, _, Typed.nil, k, hk => by simp [weakHeads] at hk
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs, k, hk => by
      simp only [weakHeads, binderTys] at hk ⊢
      rw [← hs]
      rcases List.mem_append.mp hk with hk' | hk'
      · rcases weakHeads_subset ht k hk' with hin | hb
        · exact Or.inl (by simp [hin])
        · exact Or.inr (by simp [hb])
      · rcases weakHeads_subset hu k hk' with hin | hb
        · exact Or.inl (by simp [hin])
        · exact Or.inr (by simp [hb])
  | _, _, _, Typed.gen, k, hk => by simp [weakHeads] at hk
  | _, _, _, Typed.red, k, hk => by simp [weakHeads] at hk
  | _, _, _, Typed.obj, k, hk => by simp [weakHeads] at hk
  | _, _, _, Typed.terminate, k, hk => by simp [weakHeads] at hk
  | _, _, _, @Typed.contr _ _ _ _ _ h, k, hk => by
      simp only [weakHeads, binderTys] at hk ⊢
      rcases weakHeads_subset h k hk with hin | hb
      · rcases List.mem_cons.mp hin with rfl | hin'
        · exact Or.inl (by simp)
        · exact Or.inl (by simp [hin'])
      · exact Or.inr hb
  | _, _, _, @Typed.weak _ _ _ _ _ h, k, hk => by
      simp only [weakHeads, binderTys] at hk ⊢
      rcases List.mem_cons.mp hk with rfl | hk'
      · exact Or.inl (by simp)
      · rcases weakHeads_subset h k hk' with hin | hb
        · exact Or.inl (by simp [hin])
        · exact Or.inr hb

/-- A weak head is never the content position: `content` is linear and
every head is non-linear. -/
theorem weakHead_ne_content {Γ : List Ty} {t : Term} {τ : Ty}
    (h : Typed Γ t τ) {k : Ty} (hk : k ∈ weakHeads h) : k ≠ Ty.content := by
  intro he
  subst he
  have hnl := weakHeads_nonlinear h Ty.content hk
  exact absurd hnl (by decide)

/-- The frame's membership decomposition. -/
theorem mem_frame {Γ Δ : List Ty} {k : Ty}
    (hk : k ∈ Γ ++ Ty.content :: Δ) : k ∈ Γ ∨ k = Ty.content ∨ k ∈ Δ := by
  rcases List.mem_append.mp hk with h | h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with rfl | h'
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h')

/-- Sub-derivation inheritance, at any depth, via the in-tree `Sub`
relation: a sub-derivation's weak heads are a sub-list of its parent's. -/
theorem weakHeads_sub : ∀ {Γ₁ : List Ty} {t₁ : Term} {τ₁ : Ty}
    {h : Typed Γ₁ t₁ τ₁} {Γ₂ : List Ty} {t₂ : Term} {τ₂ : Ty}
    {d : Typed Γ₂ t₂ τ₂}, Sub h d → ∀ k, k ∈ weakHeads d → k ∈ weakHeads h := by
  intro Γ₁ t₁ τ₁ h Γ₂ t₂ τ₂ d hs
  induction hs with
  | lam s ih => intro k hk; exact ih k hk
  | appL s ih => intro k hk; exact List.mem_append.mpr (Or.inl (ih k hk))
  | appR s ih => intro k hk; exact List.mem_append.mpr (Or.inr (ih k hk))
  | pairL s ih => intro k hk; exact List.mem_append.mpr (Or.inl (ih k hk))
  | pairR s ih => intro k hk; exact List.mem_append.mpr (Or.inr (ih k hk))
  | leteT s ih => intro k hk; exact List.mem_append.mpr (Or.inl (ih k hk))
  | leteB s ih => intro k hk; exact List.mem_append.mpr (Or.inr (ih k hk))
  | next s ih => intro k hk; exact ih k hk
  | fix s ih => intro k hk; exact ih k hk
  | consH s ih => intro k hk; exact List.mem_append.mpr (Or.inl (ih k hk))
  | consT s ih => intro k hk; exact List.mem_append.mpr (Or.inr (ih k hk))
  | snocT s ih => intro k hk; exact List.mem_append.mpr (Or.inl (ih k hk))
  | snocU s ih => intro k hk; exact List.mem_append.mpr (Or.inr (ih k hk))
  | contr s ih => intro k hk; exact ih k hk
  | weak s ih => intro k hk; exact List.mem_cons_of_mem _ (ih k hk)
  | lamD => intro k hk; exact hk
  | appLD => intro k hk; exact List.mem_append.mpr (Or.inl hk)
  | appRD => intro k hk; exact List.mem_append.mpr (Or.inr hk)
  | pairLD => intro k hk; exact List.mem_append.mpr (Or.inl hk)
  | pairRD => intro k hk; exact List.mem_append.mpr (Or.inr hk)
  | leteTD => intro k hk; exact List.mem_append.mpr (Or.inl hk)
  | leteBD => intro k hk; exact List.mem_append.mpr (Or.inr hk)
  | nextD => intro k hk; exact hk
  | fixD => intro k hk; exact hk
  | consHD => intro k hk; exact List.mem_append.mpr (Or.inl hk)
  | consTD => intro k hk; exact List.mem_append.mpr (Or.inr hk)
  | snocTD => intro k hk; exact List.mem_append.mpr (Or.inl hk)
  | snocUD => intro k hk; exact List.mem_append.mpr (Or.inr hk)
  | contrD => intro k hk; exact hk
  | weakD => intro k hk; exact List.mem_cons_of_mem _ hk

/-! ### §3 The traversal, in its true form -/

/-- THE WEAK ROOT: if the conclusion context is `k :: Γ₀` and fits the
frame, then `k` is a frame side position (or `k = content`, dead by the
gate). -/
theorem weak_root_pos {Γ Δ : List Ty} {k : Ty} {Γ₀ : List Ty}
    (h : k :: Γ₀ = Γ ++ Ty.content :: Δ) : k ∈ Γ ∨ k = Ty.content := by
  cases Γ with
  | nil => exact Or.inr (by simpa using congrArg (fun l => l.head?) h)
  | cons k' Γ' =>
      have h' : k = k' := by simpa using congrArg (fun l => l.head?) h
      exact Or.inl (by rw [h']; simp)

/-- THE CONTR ROOT: the duplicated position is the same, so the frame
shape decides it identically. -/
theorem contr_root_pos {Γ Δ : List Ty} {k : Ty} {Γ₀ : List Ty}
    (h : k :: k :: Γ₀ = Γ ++ Ty.content :: Δ) : k ∈ Γ ∨ k = Ty.content := by
  cases Γ with
  | nil =>
      have h' : k = Ty.content := by simpa using congrArg (fun l => l.head?) h
      exact Or.inr h'
  | cons k' Γ' =>
      have h' : k = k' := by simpa using congrArg (fun l => l.head?) h
      exact Or.inl (by rw [h']; simp)

/-- … so a weak/contr root closes under the frame's ZeroW-side
hypothesis, except in the `k = content` case, where the linearity gate
kills the rule itself. -/
theorem weak_root_head_neutral {Γ Δ : List Ty} {k : Ty} {Γ₀ : List Ty}
    (h : k :: Γ₀ = Γ ++ Ty.content :: Δ)
    (hΓ : ∀ p, p ∈ Γ → ZeroW p) (hk : k.isLinear = false) : ZeroW k := by
  rcases weak_root_pos h with hin | he
  · exact hΓ k hin
  · subst he
    exact absurd hk (by decide)

theorem contr_root_head_neutral {Γ Δ : List Ty} {k : Ty} {Γ₀ : List Ty}
    (h : k :: k :: Γ₀ = Γ ++ Ty.content :: Δ)
    (hΓ : ∀ p, p ∈ Γ → ZeroW p) (hk : k.isLinear = false) : ZeroW k := by
  rcases contr_root_pos h with hin | he
  · exact hΓ k hin
  · subst he
    exact absurd hk (by decide)

/-- The binder discipline: every `lam`/`lete` binder type is neutral or
linear (a linear binder can never be a weak head). -/
def BinderDiscipline {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ) : Prop :=
  ∀ k, k ∈ binderTys h → ZeroW k ∨ k.isLinear = true

/-- THE TRAVERSAL, PROVED: at a frame with ZeroW sides, a tree whose
binders obey the discipline has only neutral weak heads. No induction on
size, no minimality, no root dispatch: the position-origin invariant
does it. -/
theorem frameTraversal_of_binderDiscipline {Γ Δ : List Ty} {t : Term}
    (h : Typed (Γ ++ Ty.content :: Δ) t Ty.unit)
    (hΓ : ∀ p, p ∈ Γ → ZeroW p) (hΔ : ∀ p, p ∈ Δ → ZeroW p)
    (hB : BinderDiscipline h) : ∀ k, k ∈ weakHeads h → ZeroW k := by
  intro k hk
  rcases weakHeads_subset h k hk with hin | hb
  · rcases mem_frame hin with h1 | h2 | h3
    · exact hΓ k h1
    · exact absurd h2 (weakHead_ne_content h hk)
    · exact hΔ k h3
  · rcases hB k hb with hz | hl
    · exact hz
    · have hnl := weakHeads_nonlinear h k hk
      rw [hnl] at hl
      exact Bool.noConfusion hl

/-- THE COMPOSITION — the frame kill plus the traversal: `Γ ++ content ::
Δ ⊢ unit` is dead when the sides are funded at zero and no binder binds
a Full non-linear type. -/
theorem no_unit_at_frame_of_binderDiscipline {Γ Δ : List Ty} {t : Term}
    (h : Typed (Γ ++ Ty.content :: Δ) t Ty.unit)
    (hΓ : ∀ p, p ∈ Γ → ZeroW p) (hΔ : ∀ p, p ∈ Δ → ZeroW p)
    (hΓ0 : wCtx Γ 0) (hΔ0 : wCtx Δ 0) (hB : BinderDiscipline h) : False :=
  no_unit_at_frame_of_zeroWeak h hΓ0 hΔ0
    (frameTraversal_of_binderDiscipline h hΓ hΔ hB)

/-- … and at the round-1 sequent. -/
theorem no_vanishing_of_binderDiscipline {t : Term}
    (h : Typed [Ty.content] t Ty.unit) (hB : BinderDiscipline h) : False :=
  no_unit_at_frame_of_binderDiscipline (Γ := []) (Δ := []) h
    (fun p hp => by simp at hp) (fun p hp => by simp at hp) rfl rfl hB

/-- The traversal also DERIVES the round-1 hypothesis: the in-tree
`WeakHeadsNeutralAtContent` follows from a uniform binder discipline. -/
theorem weakHeadsNeutralAtContent_of_binderDiscipline
    (H : ∀ (t : Term) (h : Typed [Ty.content] t Ty.unit), BinderDiscipline h) :
    WeakHeadsNeutralAtContent :=
  fun t h k hk =>
    frameTraversal_of_binderDiscipline (Γ := []) (Δ := []) h
      (fun p hp => by simp at hp) (fun p hp => by simp at hp) (H t h) k hk

/-- The split-piece invariant: for a premise at a PIECE of the frame,
either the piece still carries the content (it is a frame, with the
remaining side a sub-context) or this piece is content-free and the
other carries everything. -/
theorem split_frame : ∀ {Γf Δ' Γ Δ : List Ty},
    Γf ++ Δ' = Γ ++ Ty.content :: Δ →
    (∃ Γ₁, Γf ++ Γ₁ = Γ ∧ Δ' = Γ₁ ++ Ty.content :: Δ) ∨
    (∃ Δ₁, Γf = Γ ++ Ty.content :: Δ₁ ∧ Δ = Δ₁ ++ Δ')
  | Γf, Δ', [], Δ, hs => by
      cases Γf with
      | nil => exact Or.inl ⟨[], rfl, by simpa using hs⟩
      | cons a Γf' =>
          have h : a = Ty.content ∧ Γf' ++ Δ' = Δ := by simpa using hs
          exact Or.inr ⟨Γf', by rw [h.1]; rfl, h.2.symm⟩
  | Γf, Δ', g :: Γ'', Δ, hs => by
      cases Γf with
      | nil => exact Or.inl ⟨g :: Γ'', rfl, by simpa using hs⟩
      | cons a Γf' =>
          have h : a = g ∧ Γf' ++ Δ' = Γ'' ++ Ty.content :: Δ := by simpa using hs
          rcases split_frame h.2 with ⟨Γ₁, h1, h2⟩ | ⟨Δ₁, h1, h2⟩
          · exact Or.inl ⟨Γ₁, by show a :: (Γf' ++ Γ₁) = g :: Γ''; rw [h1, h.1], h2⟩
          · exact Or.inr ⟨Δ₁, by
              show a :: Γf' = g :: (Γ'' ++ Ty.content :: Δ₁)
              rw [h1, h.1], h2⟩

/-! ### §3.1 The residual, and why it cannot be dropped -/

/-- The round's §3 target (the third hypothesis dropped), as a
definition. NOT asserted: see `frameTraversal_refuted_of_openQ2`. -/
def FrameTraversal : Prop :=
  ∀ (Γ Δ : List Ty) (t : Term) (h : Typed (Γ ++ Ty.content :: Δ) t Ty.unit),
    (∀ p, p ∈ Γ → ZeroW p) → (∀ p, p ∈ Δ → ZeroW p) →
    ∀ k, k ∈ weakHeads h → ZeroW k

/-- Round-1 open question #2, at the `[content]` grain. -/
def OpenQ2AtContent : Prop := ∃ t, Nonempty (Typed [Ty.content] t Ty.knowledge)

/-- The round-1 carrier, at the frame grain. -/
def carrierOfKnowledge {t : Term} (ha : Typed [Ty.content] t Ty.knowledge) :
    Typed ([Ty.content]) (Term.app (Term.lam Ty.knowledge (Term.liftAt 0 Term.unit)) t)
      Ty.unit :=
  Typed.app (Γ := []) (Δ := [Ty.content]) (a := Ty.knowledge) (b := Ty.unit)
    lamKnowledgeUnit ha rfl

theorem carrierOfKnowledge_head {t : Term}
    (ha : Typed [Ty.content] t Ty.knowledge) :
    Ty.knowledge ∈ weakHeads (carrierOfKnowledge ha) := by
  simp [carrierOfKnowledge, lamKnowledgeUnit, weakHeads]

/-- F2, as a theorem: the unrestricted frame traversal is REFUTED by a
`[content] ⊢ knowledge` — it cannot be proven without settling open
question #2. -/
theorem frameTraversal_refuted_of_openQ2 (hex : OpenQ2AtContent) :
    ¬ FrameTraversal := by
  obtain ⟨t, ⟨ha⟩⟩ := hex
  intro H
  have hz : ZeroW Ty.knowledge :=
    H [] [] _ (carrierOfKnowledge ha) (fun p hp => by simp at hp)
      (fun p hp => by simp at hp) Ty.knowledge (carrierOfKnowledge_head ha)
  exact not_zeroW_knowledge hz

/-- The other direction: a proof of the target would prove that no
non-linear type is derivable at `[content]` — strictly beyond the
counting model (which reads `knowledge` as `⊤` there). -/
theorem frameTraversal_forbids_openQ2 (H : FrameTraversal) :
    ¬ OpenQ2AtContent :=
  fun hex => frameTraversal_refuted_of_openQ2 hex H

theorem binderDiscipline_violated_by_knowledgeBinder :
    ¬ (ZeroW Ty.knowledge ∨ Ty.knowledge.isLinear = true) := by
  intro h
  rcases h with h | h
  · exact not_zeroW_knowledge h
  · exact absurd h (by decide)

/-- The carrier VIOLATES the binder discipline — which is why the
disciplined theorem is not refuted by it: the bad head is a `lam`
binder's type, and `knowledge` is Full and non-linear. -/
theorem carrier_binder_is_the_obstruction {t : Term}
    (ha : Typed [Ty.content] t Ty.knowledge) :
    ¬ BinderDiscipline (carrierOfKnowledge ha) := by
  intro hB
  have hb : Ty.knowledge ∈ binderTys (carrierOfKnowledge ha) := by
    simp [carrierOfKnowledge, lamKnowledgeUnit, binderTys]
  exact binderDiscipline_violated_by_knowledgeBinder (hB Ty.knowledge hb)

/-- F3 as the named wall: the CONTENT-FREE traversal — the exact lemma
the app root would inherit its fn piece from. FALSE. -/
def ContentFreeTraversal : Prop :=
  ∀ (Γ : List Ty) (t : Term) (τ : Ty) (h : Typed Γ t τ),
    wCtx Γ 0 → (∀ p, p ∈ Γ → ZeroW p) → ∀ k, k ∈ weakHeads h → ZeroW k

theorem contentFreeTraversal_false : ¬ ContentFreeTraversal := by
  intro H
  exact not_zeroW_knowledge
    (H [] _ _ lamKnowledgeUnit rfl (fun p hp => by simp at hp) Ty.knowledge
      (by rw [lamKnowledgeUnit_heads]; simp))

/-- THE RESIDUAL, NAMED: at every funded frame, no `lam`/`lete` binder
carries a Full non-linear type. -/
def BinderWall : Prop :=
  ∀ (Γ Δ : List Ty) (t : Term) (h : Typed (Γ ++ Ty.content :: Δ) t Ty.unit),
    wCtx Γ 0 → wCtx Δ 0 → BinderDiscipline h

/-- `BinderWall` + the frame kill = the closing shape of the round. -/
theorem no_vanishing_of_binderWall (H : BinderWall) (t : Term)
    (h : Typed [Ty.content] t Ty.unit) : False :=
  no_unit_at_frame_of_zeroWeak (Γ := []) (Δ := []) h rfl rfl
    (frameTraversal_of_binderDiscipline (Γ := []) (Δ := []) h
      (fun p hp => by simp at hp) (fun p hp => by simp at hp)
      (H [] [] t h rfl rfl))

/-- The residual is NOT free: it settles open question #2 negatively. -/
theorem binderWall_forbids_openQ2 (H : BinderWall) : ¬ OpenQ2AtContent := by
  intro hex
  obtain ⟨t, ⟨ha⟩⟩ := hex
  exact carrier_binder_is_the_obstruction ha (H [] [] _ (carrierOfKnowledge ha) rfl rfl)

/-- If open question #2 is answered positively, the banked
`WeakHeadsNeutralAtContent` is FALSE — that def is not a place a future
round can discharge by structure alone. -/
theorem inTreeTraversal_false_of_openQ2 (hex : OpenQ2AtContent) :
    ¬ WeakHeadsNeutralAtContent := by
  obtain ⟨t, ⟨ha⟩⟩ := hex
  intro H
  exact not_zeroW_knowledge
    (H _ (carrierOfKnowledge ha) Ty.knowledge (carrierOfKnowledge_head ha))

/-! ### §4 The fix pockets — the non-contradiction checks -/

theorem not_allNonLinear_frame (Γ Δ : List Ty) :
    ¬ AllNonLinear (Γ ++ Ty.content :: Δ) := by
  intro h
  have hp : (Γ ++ Ty.content :: Δ)[Γ.length]? = some Ty.content := by
    rw [List.get?_append_ge (Nat.le_refl Γ.length), Nat.sub_self]
    rfl
  have hlin := allNonLinear_get h hp
  exact absurd hlin (by decide)

/-- Fix is gated off every frame, and the fix pockets are at UNFUNDED
contexts — the frame kill is silent there, not contradicted. -/
theorem fix_pockets_are_outside_the_frame_theory :
    (∀ (Γ Δ : List Ty), ¬ AllNonLinear (Γ ++ Ty.content :: Δ)) ∧
      (¬ ∃ w, wCtx [Ty.knower] w) :=
  ⟨not_allNonLinear_frame, knower_unfunded⟩

theorem frame_ne_nil (Γ Δ : List Ty) : Γ ++ Ty.content :: Δ ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp at hl

theorem frame_singleton_is_content {Γ Δ : List Ty} {a : Ty}
    (h : ([a] : List Ty) = Γ ++ Ty.content :: Δ) : a = Ty.content := by
  cases Γ with
  | nil => cases h; rfl
  | cons k' Γ' =>
      have hl := congrArg List.length h
      simp only [List.length_cons, List.length_append, List.length_nil] at hl
      omega

/-- … so a `var` root can never conclude `unit` at a frame. -/
theorem frame_var_root_type_is_content {Γ Δ : List Ty} {a : Ty}
    (h : ([a] : List Ty) = Γ ++ Ty.content :: Δ) : a ≠ Ty.unit := by
  rw [frame_singleton_is_content h]
  exact by decide

end SCProvenance2

/-! ## THE REFINEMENT — the arrow-knower conduit is DERIVABLE; `no_vanishing` is REFUTED (probe scProvenance3, transfer-landed)

Round 3 answered the endgame question in the direction nobody bet on:
`[content] ⊢ arrow knower knowledge` IS DERIVABLE — the LETE SWAP
(`Typing.lete`'s body context is `b :: a :: Γ₂`, the tensor's components
in REVERSE order, so a `pair`/`lete` round trip REORDERS the context)
brings the knower pocket's stream in front of the content, `red` turns
it into knowledge, and `lam knower` closes the conduit
(`arrowKnowerKnowledge`; same at `value` and at the `▷` codomain).

The conduit is Full and non-linear, so the round-2 residual is REFUTED:
`¬ BinderWall`, `¬ FrameTraversal`, both UNCONDITIONAL, both from ONE
explicit tree — `carrierAKK arrowKnowerKnowledge : [content] ⊢ unit`, the
record's own carrier shape applied to the conduit. **That tree is a
witness against the unrestricted `no_vanishing` (Linearity.lean:53): the
statement is FALSE.** The token is spent — as the `cons` head of the
epistemic cycle's stream (`[content, knower] ⊢ stream`), the shortest
content-carrying stream in the calculus) — then the conduit that read it
is weakened away for `unit`. Vanishing happens, but only THROUGH the
epistemic cycle: content → stream-head → red-pocket → weakened conduit.

WHAT SURVIVES, and why the 20-round record is consistent: the witness is
NOT cut-free (`carrierAKK_fn_not_atomic` — its discharging app is
lam-headed), so every cut-free fragment theorem stands; its weak head is
`arrow knower knowledge` (not ZeroW), so `no_vanishing_of_zeroWeak`
stands; it carries a fix, a weak, and live binders, so `no_vanishing_
noweak`/`_clean`/the march's conditional layers all stand. The
impossibility theorem was pointing at the truth all along: no model
sound at `weak` kills the stub because the stub is FALSE. And the
conduit is INERT at content frames (`no_arrowKnower_app_at_content`: no
app with an `arrow knower X` function concludes at `[content]` — the
knower argument would be closed (dead) or content-rooted (dead)), so
`[content] ⊢ knowledge` ITSELF stays dead (`red`'s argument is
unreachable), and `[content] ⊢ knower` is dead in-tree. The stream
question `[content] ⊢ stream` stays open (`stream_at_content_has_fix`:
any such tree carries a `FixNeedS` node; the root dispatch is
`app`/`cons`/`lete`).

SCOPE: everything here is FULL `Typed` grain (fix and weak inclusive).
The disposition of the Linearity.lean stub is a recorded fact, not a
silent edit: the statement as written is refuted by `carrierAKK`. -/
namespace SCProvenance3

open SCExtractor SCProvenance SCProvenance2

/-! ### §0 The type-level facts the witnesses lean on -/

/-- The knower pocket's stream source: the in-tree epistemic-cycle fixpoint
`[knower] ⊢ stream`, in the shape a `next` needs. -/
def fixStream : Typed [Ty.knower]
    (Term.fix (Term.lam (Ty.later Ty.stream) flip2)) Ty.stream :=
  Typed.fix knower_ctx_nonlinear (Typed.lam flip2Typed)

/-- … so `[knower] ⊢ ▷stream` (a `cons` tail, and the fix's output under the
guard). -/
def nextFixStream : Typed [Ty.knower]
    (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2))) (Ty.later Ty.stream) :=
  Typed.next fixStream

/-- The conduit's type is FULL in the counting model — on the model's veto
list, so no budget argument can exclude it. -/
theorem arrowKnowerKnowledge_full : Full (Ty.arrow Ty.knower Ty.knowledge) :=
  arrow_knower_knowledge_full

/-! ### §1 The stream frames — `cons` needs no knowledge, only a tail -/

/-- `cons (var 0) (var 0)` at `[content, ▷stream] ⊢ stream`: the SHORTEST
content-carrying stream derivation in the calculus. -/
def streamContentLater :
    Typed [Ty.content, Ty.later Ty.stream]
      (Term.cons (Term.var 0) (Term.var 0)) Ty.stream :=
  Typed.cons (Γ := [Ty.content]) (Δ := [Ty.later Ty.stream])
    (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content)
    (Typed.var : Typed [Ty.later Ty.stream] (Term.var 0) (Ty.later Ty.stream)) rfl

/-- … and with the knower pocket as the tail: `[content, knower] ⊢ stream` —
the epistemic cycle with a content payload. -/
def streamContentKnower :
    Typed [Ty.content, Ty.knower]
      (Term.cons (Term.var 0) (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2)))) Ty.stream :=
  Typed.cons (Γ := [Ty.content]) (Δ := [Ty.knower])
    (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content)
    nextFixStream rfl

/-! ### §2 The swap — `[knower, content] ⊢ stream`, and the conduits -/

/-- `lete`'s body is typed at `b :: a :: Γ₂` — the tensor's components
REVERSED. Reading `pair` forwards and `lete` backwards is the calculus's
only exchange, and it moves the knower pocket in FRONT of the content
position, which is where `lam` can bind it. -/
def streamKnowerContent :
    Typed [Ty.knower, Ty.content]
      (Term.lete (Term.pair (Term.var 0) (Term.var 0))
        (Term.cons (Term.var 0)
          (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2)))))
      Ty.stream :=
  Typed.lete (Γ₁ := [Ty.knower, Ty.content]) (Γ₂ := [])
    (Typed.pair (Γ := [Ty.knower]) (Δ := [Ty.content])
      (Typed.var : Typed [Ty.knower] (Term.var 0) Ty.knower)
      (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content) rfl)
    streamContentKnower rfl

/-- … and `lam` closes the conduit: `[content] ⊢ arrow knower stream`. -/
def arrowKnowerStream :
    Typed [Ty.content]
      (Term.lam Ty.knower
        (Term.lete (Term.pair (Term.var 0) (Term.var 0))
          (Term.cons (Term.var 0)
            (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2))))))
      (Ty.arrow Ty.knower Ty.stream) :=
  Typed.lam streamKnowerContent

/-- THE ARROW-KNOWER FAMILY IS INHABITED — `red` reads the pocket's
stream: `[knower, content] ⊢ knowledge`. -/
def knowledgeKnowerContent :
    Typed [Ty.knower, Ty.content]
      (Term.app Term.red
        (Term.lete (Term.pair (Term.var 0) (Term.var 0))
          (Term.cons (Term.var 0)
            (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2))))))
      Ty.knowledge :=
  Typed.app (Γ := []) (Δ := [Ty.knower, Ty.content])
    (a := Ty.stream) (b := Ty.knowledge) Typed.red streamKnowerContent rfl

/-- The conduit itself: `[content] ⊢ arrow knower knowledge` — the very
type `openQ2_reduces_to_derivability` named as the carrier that would put
a FULL-headed `weak` into a `[content]`-rooted tree. It is DERIVABLE. -/
def arrowKnowerKnowledge :
    Typed [Ty.content]
      (Term.lam Ty.knower
        (Term.app Term.red
          (Term.lete (Term.pair (Term.var 0) (Term.var 0))
            (Term.cons (Term.var 0)
              (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2)))))))
      (Ty.arrow Ty.knower Ty.knowledge) :=
  Typed.lam knowledgeKnowerContent

/-- The same at `value` — `obj` is the other stream reader. -/
def arrowKnowerValue :
    Typed [Ty.content]
      (Term.lam Ty.knower
        (Term.app Term.obj
          (Term.lete (Term.pair (Term.var 0) (Term.var 0))
            (Term.cons (Term.var 0)
              (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2)))))))
      (Ty.arrow Ty.knower Ty.value) :=
  Typed.lam
    (Typed.app (Γ := []) (Δ := [Ty.knower, Ty.content])
      (a := Ty.stream) (b := Ty.value) Typed.obj streamKnowerContent rfl)

/-- The guard shape: `[content] ⊢ arrow knower (▷stream)`. -/
def arrowKnowerLaterStream :
    Typed [Ty.content]
      (Term.lam Ty.knower
        (Term.next
          (Term.lete (Term.pair (Term.var 0) (Term.var 0))
            (Term.cons (Term.var 0)
              (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2)))))))
      (Ty.arrow Ty.knower (Ty.later Ty.stream)) :=
  Typed.lam (Typed.next streamKnowerContent)

/-! ### §3 The refutation -/

/-- ONE TREE: the record's own carrier shape at the conduit —
`λ(k : arrow knower knowledge). unit` applied to it. THIS IS A
`[content] ⊢ unit` DERIVATION: a kernel witness against the
unrestricted `no_vanishing`. -/
def carrierAKK {t : Term} (ha : Typed [Ty.content] t (Ty.arrow Ty.knower Ty.knowledge)) :
    Typed [Ty.content]
      (Term.app (Term.lam (Ty.arrow Ty.knower Ty.knowledge) (Term.liftAt 0 Term.unit)) t)
      Ty.unit :=
  Typed.app (Γ := []) (Δ := [Ty.content])
    (a := Ty.arrow Ty.knower Ty.knowledge) (b := Ty.unit)
    (Typed.lam (Typed.weak (k := Ty.arrow Ty.knower Ty.knowledge) (t := Term.unit)
      (τ := Ty.unit) arrow_knower_knowledge_nonlinear Typed.unit))
    ha rfl

/-- The head is really in the tree (traversal, not assertion). -/
theorem carrierAKK_has_head :
    Ty.arrow Ty.knower Ty.knowledge ∈ weakHeads (carrierAKK arrowKnowerKnowledge) := by
  unfold carrierAKK
  simp only [weakHeads]
  exact List.mem_append.mpr (Or.inl (by simp))

/-- … and it is the BINDER's type, so the binder discipline fails. -/
theorem carrierAKK_binder :
    Ty.arrow Ty.knower Ty.knowledge ∈ binderTys (carrierAKK arrowKnowerKnowledge) := by
  unfold carrierAKK
  simp only [binderTys]
  exact List.mem_append.mpr (Or.inl (by simp))

theorem carrierAKK_not_binderDiscipline :
    ¬ BinderDiscipline (carrierAKK arrowKnowerKnowledge) := by
  intro hB
  rcases hB _ carrierAKK_binder with hz | hl
  · exact not_zeroW_arrow_knower Ty.knowledge hz
  · exact absurd hl (by decide)

/-- ROUND 2'S RESIDUAL, REFUTED: `BinderWall` is FALSE. -/
theorem not_binderWall : ¬ BinderWall := by
  intro H
  exact carrierAKK_not_binderDiscipline
    (H [] [] _ (carrierAKK arrowKnowerKnowledge) rfl rfl)

/-- ROUND 2'S `FrameTraversal`, REFUTED UNCONDITIONALLY. -/
theorem not_frameTraversal : ¬ FrameTraversal := by
  intro H
  have hz : ZeroW (Ty.arrow Ty.knower Ty.knowledge) :=
    H [] [] _ (carrierAKK arrowKnowerKnowledge)
      (fun p hp => by simp at hp) (fun p hp => by simp at hp)
      (Ty.arrow Ty.knower Ty.knowledge) carrierAKK_has_head
  exact not_zeroW_arrow_knower Ty.knowledge hz

/-- Round 2's transfer HYPOTHESIS is not derivable. -/
theorem binderDiscipline_uniformly_false :
    ¬ (∀ (t : Term) (h : Typed [Ty.content] t Ty.unit), BinderDiscipline h) := by
  intro H
  exact carrierAKK_not_binderDiscipline (H _ _)

/-- SCOPE: the refuting tree is NOT cut-free — its discharging `app` is
lam-headed, so `IsAtomic` fails. Nothing here touches a cut-free binder
wall. -/
theorem carrierAKK_fn_not_atomic :
    ¬ IsAtomic (Term.lam (Ty.arrow Ty.knower Ty.knowledge) (Term.liftAt 0 Term.unit)) := by
  intro h
  rcases h with h | h | h | h | h <;> exact Term.noConfusion h

/-! ### §4 The stream question, measured -/

/-- A `[content]`-rooted stream MUST carry a fixpoint whose payload
carries the stream need (`spropF`: `[content]` has no supply position). -/
theorem stream_at_content_has_fix {t : Term} (h : Typed [Ty.content] t Ty.stream) :
    FixNeedS h := by
  rcases spropF h True.intro with ⟨i, b, hpos, hsup⟩ | hfix
  · exact absurd hsup (content_ctx_nosupply i b hpos)
  · exact hfix

/-- THE ROOT DISPATCH at `[content] ⊢ stream`: only `app`/`cons`/`lete`
can be the root; every other rule dies on its conclusion type, the
linearity of `content`, or the fix gate. -/
theorem stream_content_root_dispatch {t : Term} (h : Typed [Ty.content] t Ty.stream) :
    (∃ (Γ Δ : List Ty) (a : Ty) (fn arg : Term) (_ : Γ ++ Δ = [Ty.content]),
        Nonempty ((Typed Γ fn (Ty.arrow a Ty.stream)) × (Typed Δ arg a)))
    ∨ (∃ (Γ Δ : List Ty) (hd tl : Term) (_ : Γ ++ Δ = [Ty.content]),
        Nonempty ((Typed Γ hd Ty.content) × (Typed Δ tl (Ty.later Ty.stream))))
    ∨ (∃ (Γ₁ Γ₂ : List Ty) (a b : Ty) (scr body : Term)
          (_ : Γ₁ ++ Γ₂ = [Ty.content]),
        Nonempty ((Typed Γ₁ scr (Ty.tensor a b)) × (Typed (b :: a :: Γ₂) body Ty.stream))) := by
  cases h with
  | app hf ha hs => exact Or.inl ⟨_, _, _, _, _, hs, ⟨hf, ha⟩⟩
  | cons hc ht hs => exact Or.inr (Or.inl ⟨_, _, _, _, hs, ⟨hc, ht⟩⟩)
  | lete ht hb hs => exact Or.inr (Or.inr ⟨_, _, _, _, _, _, hs, ⟨ht, hb⟩⟩)
  | fix hΓ _ => exact absurd hΓ (not_allNonLinear_frame [] [])
  | contr hk _ => exact absurd hk (by decide)
  | weak hk _ => exact absurd hk (by decide)

/-- … and a content-rooted stream IMPLIES the conduit — the conduit is a
consequence of the target, not an obstruction to it. -/
theorem stream_at_content_imp_arrowKnowerStream {t : Term}
    (h : Typed [Ty.content] t Ty.stream) :
    ∃ t', Nonempty (Typed [Ty.content] t' (Ty.arrow Ty.knower Ty.stream)) :=
  ⟨_, ⟨Typed.lam (Typed.weak (k := Ty.knower) (t := t) (τ := Ty.stream)
    (by decide) h)⟩⟩

/-- THE CONDUITS ARE INERT AT CONTENT FRAMES — the family's whole point.
An `app` whose function is typed at `[content]` with an `arrow knower X`
type CANNOT conclude at `[content]`: the split is `[] ++ [content]` or
`[content] ++ []`, and each kills the knower argument (no closed knower;
no `[content]`-rooted knower). The conduit is inhabited but inert. -/
theorem no_arrowKnower_app_at_content {X : Ty} {fn arg : Term} {Γ Δ : List Ty}
    (_hf : Typed Γ fn (Ty.arrow Ty.knower X)) (ha : Typed Δ arg Ty.knower)
    (hs : Γ ++ Δ = [Ty.content]) : False := by
  rcases coreV3_append_eq_singleton (c := Ty.content) hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact no_closed_knower ha
  · subst h1; subst h2; exact no_knower_at_content ha

/-- The wall the inertness consumes, named. -/
def KnowerAtContent : Prop := ∃ t, Nonempty (Typed [Ty.content] t Ty.knower)

/-- The `[content]`-rooted knower is dead UNCONDITIONALLY (fix-inclusive
and weak-inclusive, in-tree). -/
theorem no_knowerAtContent : ¬ KnowerAtContent := by
  rintro ⟨t, ⟨h⟩⟩
  exact no_knower_at_content h

/-! ### §5 The ladder — why the round stops here -/

/-- The pocket mechanism in full: a content-knower, `gen`'d into a
content⊗knower and swapped by `lete`, is exactly §1's own stream witness. -/
theorem stream_at_content_of_knowerAtContent (H : KnowerAtContent) :
    ∃ t, Nonempty (Typed [Ty.content] t Ty.stream) := by
  obtain ⟨t, ⟨ha⟩⟩ := H
  refine ⟨Term.lete (Term.app Term.gen t)
    (Term.lete (Term.pair (Term.var 0) (Term.var 0))
      (Term.cons (Term.var 0)
        (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2))))), ⟨?_⟩⟩
  exact Typed.lete (Γ₁ := [Ty.content]) (Γ₂ := [])
    (Typed.app (Γ := []) (Δ := [Ty.content])
      (a := Ty.knower) (b := Ty.tensor Ty.content Ty.knower) Typed.gen ha rfl)
    streamKnowerContent rfl

/-- … and the target itself: `KnowerAtContent` refutes `no_vanishing`
outright in two nodes — which is why its in-tree death is the
consistency fact holding the knower route closed. -/
theorem unit_at_content_of_knowerAtContent (H : KnowerAtContent) :
    ∃ t, Nonempty (Typed [Ty.content] t Ty.unit) := by
  obtain ⟨t, ⟨ha⟩⟩ := H
  exact ⟨_, ⟨Typed.app (Γ := []) (Δ := [Ty.content])
    (a := Ty.knower) (b := Ty.unit)
    (Typed.lam (Typed.weak (k := Ty.knower) (t := Term.unit) (τ := Ty.unit)
      (by decide) Typed.unit)) ha rfl⟩⟩

/-- The ladder's rung below: `[content] ⊢ knowledge` gives the target too
(the round-1 carrier) — and the conduit's inertness is what keeps that
rung unreachable. -/
theorem unit_at_content_of_knowledgeAtContent
    (hex : ∃ t, Nonempty (Typed [Ty.content] t Ty.knowledge)) :
    ∃ t, Nonempty (Typed [Ty.content] t Ty.unit) := by
  obtain ⟨t, ⟨ha⟩⟩ := hex
  exact ⟨_, ⟨SCExtractor.carrierOfKnowledge ha⟩⟩

end SCProvenance3

/-! ## THE CONTRACTION TWIN — the same treatment, and the opposite verdict (probe scContraction, transfer-landed)

`no_contraction_content` (Linearity.lean:40) got the same falsify-first
hunt that refuted its twin — and SURVIVES it, for a measured reason:
the minting contraction EXISTS one frame up (`[knower] ⊢ C⊗C`,
`[knower, content] ⊢ C⊗C`, `[content, knower] ⊢ C⊗C`,
`[knower, knower] ⊢ C⊗C` — `gen` mints content from any knower in
scope, the lete swap reorders, `weak` discards the knower), and the
clone conduit `[content] ⊢ arrow knower (C⊗C)` exists in both
`[content]`- and `[]`-typed forms — but its type is LINEAR
(`contractionConduit_linear`), the exact opposite of the twin's
`arrow knower knowledge`. A linear type is what `weak`, `contr` and
`fix` all REFUSE, so the conduit cannot leak out of its pocket; and its
one move — firing at a knower value at `[content]` — is dead
(`no_contractionConduit_fire_at_content`, `no_knower_at_content`).
`twin_conduits_differ` states the asymmetry in one line: THIS IS THE
DIFFERENCE BETWEEN THE TWO STUBBED LAWS.

The root dispatch at `[content] ⊢ C⊗C`: only `pair | lete | app`. The
`pair` root is DEAD (a prefix split of `[content]` leaves a
`[] ⊢ content` premise, and `[]` funds nothing — `cprop`). The `app`
root at a closed function is dead whenever the argument supplies
nothing. THE REMAINING WALL, named: the `lete` root whose token is
spent on the scrutinee — the record's compound-source family again;
closing it needs a two-supply lemma under a no-knower frame ("a
tensor at a content-only frame cannot have both components
supplying"), which is the march's standing open core. Also measured:
`[content] ⊢ content` is NOT var-only (`content_redex`:
`(λx. x)(var 0)`) — the pair kill works by the split, not by
leaf-shape. NOT DECIDED: the target itself — neither proved nor
refuted; the restricted kernel's `no_contraction_restricted` is
unaffected. -/
namespace SCContraction

open SCExtractor SCProvenance SCProvenance2 SCProvenance3

/-- A gen-fire at the knower frame: `gen` mints `C ⊗ K` from a knower. -/
def genFireKnower :
    Typed [Ty.knower] (Term.app Term.gen (Term.var 0))
      (Ty.tensor Ty.content Ty.knower) :=
  Typed.app (Γ := []) (Δ := [Ty.knower])
    (a := Ty.knower) (b := Ty.tensor Ty.content Ty.knower)
    Typed.gen (Typed.var : Typed [Ty.knower] (Term.var 0) Ty.knower) rfl

/-- THE POCKET CLONE — `[knower, content] ⊢ C ⊗ C`: the lete swap puts the
minted content beside the root token; `weak` discards the knower. -/
def contractionKnowerContent :
    Typed [Ty.knower, Ty.content]
      (Term.lete (Term.app Term.gen (Term.var 0))
        (Term.pair (Term.var 1) (Term.var 0)))
      (Ty.tensor Ty.content Ty.content) :=
  Typed.lete (Γ₁ := [Ty.knower]) (Γ₂ := [Ty.content])
    (a := Ty.content) (b := Ty.knower)
    genFireKnower
    (Typed.pair (Γ := [Ty.knower, Ty.content]) (Δ := [Ty.content])
      (a := Ty.content) (b := Ty.content)
      (Typed.weak (k := Ty.knower) (t := Term.var 0) (τ := Ty.content) (by decide)
        (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content))
      (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content) rfl)
    rfl

/-- THE KNOWER-FRAME CONTRACTION — `[knower] ⊢ C ⊗ C` in five nodes: the
knower alone mints both contents. -/
def contractionKnower :
    Typed [Ty.knower]
      (Term.lete (Term.app Term.gen (Term.var 0))
        (Term.lete (Term.app Term.gen (Term.var 0))
          (Term.pair (Term.var 1) (Term.var 0))))
      (Ty.tensor Ty.content Ty.content) :=
  Typed.lete (Γ₁ := [Ty.knower]) (Γ₂ := [])
    (a := Ty.content) (b := Ty.knower)
    genFireKnower
    contractionKnowerContent rfl

theorem contraction_at_knower :
    Nonempty (Typed [Ty.knower]
      (Term.lete (Term.app Term.gen (Term.var 0))
        (Term.lete (Term.app Term.gen (Term.var 0))
          (Term.pair (Term.var 1) (Term.var 0))))
      (Ty.tensor Ty.content Ty.content)) :=
  ⟨contractionKnower⟩

/-- THE CONDUIT — `lam knower` closes the pocket:
`[content] ⊢ arrow knower (C⊗C)`, the contraction twin of
`arrowKnowerKnowledge`, at exactly the same frame. -/
def contractionConduit :
    Typed [Ty.content]
      (Term.lam Ty.knower
        (Term.lete (Term.app Term.gen (Term.var 0))
          (Term.pair (Term.var 1) (Term.var 0))))
      (Ty.arrow Ty.knower (Ty.tensor Ty.content Ty.content)) :=
  Typed.lam contractionKnowerContent

/-- … and at the empty context — the form `app` needs. -/
def contractionConduit0 :
    Typed []
      (Term.lam Ty.knower
        (Term.lete (Term.app Term.gen (Term.var 0))
          (Term.lete (Term.app Term.gen (Term.var 0))
            (Term.pair (Term.var 1) (Term.var 0)))))
      (Ty.arrow Ty.knower (Ty.tensor Ty.content Ty.content)) :=
  Typed.lam contractionKnower

/-- The conduit's type is LINEAR — the exact opposite of the twin's. -/
theorem contractionConduit_linear :
    (Ty.arrow Ty.knower (Ty.tensor Ty.content Ty.content)).isLinear = true := rfl

/-- … so it can never satisfy `weak`'s / `contr`'s gate. -/
theorem contractionConduit_not_gate :
    (Ty.arrow Ty.knower (Ty.tensor Ty.content Ty.content)).isLinear ≠ false := by
  rw [contractionConduit_linear]; decide

/-- THE DIFFERENCE BETWEEN THE TWO STUBBED LAWS, both sides computed: the
vanishing conduit is non-linear (weak-able — the binder wall fell), the
contraction conduit is linear (inert). -/
theorem twin_conduits_differ :
    (Ty.arrow Ty.knower Ty.knowledge).isLinear = false
      ∧ (Ty.arrow Ty.knower (Ty.tensor Ty.content Ty.content)).isLinear = true :=
  ⟨arrow_knower_knowledge_nonlinear, contractionConduit_linear⟩

/-- THE LADDER: `KnowerAtContent` would refute the stub in one `app` node —
and that rung is dead (`no_knower_at_content`). -/
theorem contraction_at_content_of_knowerAtContent (H : KnowerAtContent) :
    ∃ t, Nonempty (Typed [Ty.content] t (Ty.tensor Ty.content Ty.content)) := by
  obtain ⟨t, ⟨ha⟩⟩ := H
  exact ⟨_, ⟨Typed.app (Γ := []) (Δ := [Ty.content])
    (a := Ty.knower) (b := Ty.tensor Ty.content Ty.content)
    contractionConduit0 ha rfl⟩⟩

/-- THE CONDUIT CANNOT FIRE AT A CONTENT FRAME — inhabited but inert,
the measured shape of the wall. -/
theorem no_contractionConduit_fire_at_content {fn arg : Term} {Γ Δ : List Ty}
    (hf : Typed Γ fn (Ty.arrow Ty.knower (Ty.tensor Ty.content Ty.content)))
    (ha : Typed Δ arg Ty.knower)
    (hs : Γ ++ Δ = [Ty.content]) : False :=
  no_arrowKnower_app_at_content (X := Ty.tensor Ty.content Ty.content) hf ha hs

theorem no_closed_conduit_refutation {arg : Term}
    (ha : Typed [Ty.content] arg Ty.knower) : False :=
  Dcare.no_knower_at_content ha

/-- ROOT DISPATCH: only `pair`, `lete`, `app` can root the target. -/
theorem contraction_root_dispatch {t : Term}
    (h : Typed [Ty.content] t (Ty.tensor Ty.content Ty.content)) :
    (∃ l r : Term, t = Term.pair l r)
      ∨ (∃ (scr body : Term), t = Term.lete scr body)
      ∨ (∃ fn arg, t = Term.app fn arg) := by
  cases h with
  | pair _ _ _ => exact Or.inl ⟨_, _, rfl⟩
  | lete _ _ _ => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  | app _ _ _ => exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  | fix hΓ _ => exact absurd hΓ (not_allNonLinear_frame [] [])
  | contr hk _ => exact absurd hk (by decide)
  | weak hk _ => exact absurd hk (by decide)

/-- THE `pair` ROOT IS DEAD: a prefix split of `[content]` leaves a
`[] ⊢ content` premise, and `cprop` kills it (the empty context funds
nothing). -/
theorem no_pair_root_contraction {Γ Δ : List Ty} {l r : Term}
    (hl : Typed Γ l Ty.content) (hr : Typed Δ r Ty.content)
    (hs : Γ ++ Δ = [Ty.content]) : False := by
  rcases coreV3_append_eq_singleton (c := Ty.content) hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2
    obtain ⟨i, b, hpos, _⟩ := cprop hr True.intro
    rw [List.get?_nil'] at hpos
    exact nomatch hpos
  · subst h1; subst h2
    obtain ⟨i, b, hpos, _⟩ := cprop hl True.intro
    rw [List.get?_nil'] at hpos
    exact nomatch hpos

theorem pair_rule_dead_at_content :
    ¬ ∃ (Γ Δ : List Ty) (l r : Term),
        Nonempty (Typed Γ l Ty.content) ∧ Nonempty (Typed Δ r Ty.content)
          ∧ Γ ++ Δ = [Ty.content] := by
  rintro ⟨Γ, Δ, l, r, ⟨hl⟩, ⟨hr⟩, hs⟩
  exact no_pair_root_contraction hl hr hs

/-- THE `app` ROOT AT A CLOSED FUNCTION is dead whenever the argument's
type supplies nothing — the node the R1/R2 conduits terminate in. -/
theorem no_closed_fn_contraction_of_nosupply {fn : Term} {a : Ty}
    (hf : Typed [] fn (Ty.arrow a (Ty.tensor Ty.content Ty.content)))
    (hns : ¬ CSupply a) : False := by
  obtain ⟨i, b, hpos, _⟩ := cprop hf ⟨Or.inl True.intro, fun hc => hns (Or.inl hc),
    fun hk => hns (Or.inr hk)⟩
  rw [List.get?_nil'] at hpos
  exact nomatch hpos

theorem no_closed_fn_app_root {fn arg : Term} {a : Ty}
    (hf : Typed [] fn (Ty.arrow a (Ty.tensor Ty.content Ty.content)))
    (_ha : Typed [Ty.content] arg a)
    (hns : ¬ CSupply a) : False :=
  no_closed_fn_contraction_of_nosupply hf hns

/-- `[content] ⊢ content` is NOT var-only — `(λx. x)(var 0)` — so the pair
kill above works by the SPLIT, not by leaf-shape. -/
def content_redex :
    Typed [Ty.content] (Term.app (Term.lam Ty.content (Term.var 0)) (Term.var 0))
      Ty.content :=
  Typed.app (Γ := []) (Δ := [Ty.content]) (a := Ty.content) (b := Ty.content)
    (Typed.lam (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content))
    (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content) rfl

theorem content_redex_not_var :
    Term.app (Term.lam Ty.content (Term.var 0)) (Term.var 0) ≠ Term.var 0 := by
  intro h; exact Term.noConfusion h

/-- The clone's home frame: `[content, content] ⊢ C⊗C` in two nodes. -/
def contractionTwoContents :
    Typed [Ty.content, Ty.content] (Term.pair (Term.var 0) (Term.var 0))
      (Ty.tensor Ty.content Ty.content) :=
  Typed.pair (Γ := [Ty.content]) (Δ := [Ty.content])
    (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content)
    (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content) rfl

/-- `[content, knower] ⊢ C⊗C` — the swap, composed with the pocket clone. -/
def contractionContentKnower :
    Typed [Ty.content, Ty.knower]
      (Term.lete (Term.pair (Term.var 0) (Term.var 0))
        (Term.lete (Term.app Term.gen (Term.var 0))
          (Term.pair (Term.var 1) (Term.var 0))))
      (Ty.tensor Ty.content Ty.content) :=
  Typed.lete (Γ₁ := [Ty.content, Ty.knower]) (Γ₂ := [])
    (a := Ty.content) (b := Ty.knower)
    (Typed.pair (Γ := [Ty.content]) (Δ := [Ty.knower])
      (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content)
      (Typed.var : Typed [Ty.knower] (Term.var 0) Ty.knower) rfl)
    contractionKnowerContent rfl

/-- `[C⊗K] ⊢ content` — a content read OUT of a tensor-component frame:
the component frame is not barren when the knower is alive. -/
def contentOfTensorComponent :
    Typed [Ty.tensor Ty.content Ty.knower]
      (Term.lete (Term.var 0) (Term.var 1)) Ty.content :=
  Typed.lete (Γ₁ := [Ty.tensor Ty.content Ty.knower]) (Γ₂ := [])
    (a := Ty.content) (b := Ty.knower)
    (Typed.var : Typed [Ty.tensor Ty.content Ty.knower] (Term.var 0)
      (Ty.tensor Ty.content Ty.knower))
    (Typed.weak (k := Ty.knower) (t := Term.var 0) (τ := Ty.content) (by decide)
      (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content))
    rfl

/-- `[knower, knower] ⊢ C⊗C` — two minted contents, both read. -/
def contractionTwoKnowers :
    Typed [Ty.knower, Ty.knower]
      (Term.lete
        (Term.pair (Term.app Term.gen (Term.var 0)) (Term.app Term.gen (Term.var 0)))
        (Term.lete (Term.var 0)
          (Term.pair (Term.var 1) (Term.lete (Term.var 0) (Term.var 1)))))
      (Ty.tensor Ty.content Ty.content) :=
  Typed.lete (Γ₁ := [Ty.knower, Ty.knower]) (Γ₂ := [])
    (a := Ty.tensor Ty.content Ty.knower) (b := Ty.tensor Ty.content Ty.knower)
    (Typed.pair (Γ := [Ty.knower]) (Δ := [Ty.knower])
      (a := Ty.tensor Ty.content Ty.knower) (b := Ty.tensor Ty.content Ty.knower)
      genFireKnower genFireKnower rfl)
    (Typed.lete (Γ₁ := [Ty.tensor Ty.content Ty.knower])
      (Γ₂ := [Ty.tensor Ty.content Ty.knower])
      (a := Ty.content) (b := Ty.knower)
      (Typed.var : Typed [Ty.tensor Ty.content Ty.knower] (Term.var 0)
        (Ty.tensor Ty.content Ty.knower))
      (Typed.pair (Γ := [Ty.knower, Ty.content])
        (Δ := [Ty.tensor Ty.content Ty.knower])
        (Typed.weak (k := Ty.knower) (t := Term.var 0) (τ := Ty.content) (by decide)
          (Typed.var : Typed [Ty.content] (Term.var 0) Ty.content))
        contentOfTensorComponent rfl)
      rfl)
    rfl

end SCContraction

/-! ## The no-weak fragment's two laws — landed where the record promised them

The fragment record at the NoWeakFrag section (and the paper's §5)
cite `no_vanishing_noweak` and `no_contraction_noweak`; these are the
declarations. Both are the counting model's verdict at the no-weak
grain: a `NoWeak` tree has no weak heads at all
(`weakHeads_nil_of_noweak`), so the model's weak-arm obligation is
vacuous, and `fix` is sound unconditionally (the guard reads ⊤) — the
fragment is everything except `weak`. (The Guarded kernel's
`no_vanishing_restricted`/`no_contraction_restricted` are these two
theorems under the kernel's names.) -/

open SCExtractor SCProvenance
/-- A `NoWeak` tree lists no weak heads: the counting model's weak-arm
obligation is vacuous for it. (17 arms; the `weak` arm is `False` by
the definition.) -/
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

/-- The no-weak fragment's UNITARITY law, as promised by the fragment
record and cited by the paper: `[content] ⊬ unit` in every tree with no
`weak` node — `fix` included, `gen`/`contr`/`cons`/`snoc`/the constants
inside. -/
theorem no_vanishing_noweak {t : Term} (h : Typed [Ty.content] t Ty.unit)
    (hN : NoWeakFrag.NoWeak h) : False :=
  no_vanishing_of_zeroWeak h (by
    intro k hk
    rw [weakHeads_nil_of_noweak h hN] at hk
    exact absurd hk (by simp))

/-- The no-weak fragment's NO-CLONING law: `[content] ⊬ content ⊗ content`
in every tree with no `weak` node. The arithmetic: the frame costs `1`,
but `content ⊗ content` needs `m + n` with both `≥ 1`. -/
theorem no_contraction_noweak {t : Term}
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
end Dcare
