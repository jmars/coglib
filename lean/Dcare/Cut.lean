import Dcare.Typing
import Dcare.Count
import Dcare.Subst
import Dcare.Path

/-!
# The linear cut (subject reduction's engine)

THE ONE-HOLE SPLICE: substituting an argument for a LINEAR binder's
single occurrence, rebuilding the derivation frame by frame along the
spine from the binder's leaf to the root. The convention (verified
per-frame, obs 85): the argument's context is INSERTED where the binder
was — side premises keep their contexts and their terms — so the
insertion point is preserved up every frame and no exchange is ever
needed.

The `contr` frame's duplicated-position case (binder = the contracted
`k`) is closed by the linearity hypothesis: the duplicated position is
non-linear, the substituted binder is linear — they cannot coincide.
This is the only place the cut uses linearity beyond `uses = 1`, and it
is exactly the case the chase never generates (its binders carry
positive weight, hence are linear).

The size clause is the splice's termination engine: the leaf (size 1)
is replaced by the argument, everything else is renamed — so the reduct
is smaller than the redex by construction whenever the argument is not
a variable.
-/

namespace Dcare

/-- Split cancellation, LEFT: if the substituted position lies in the
left piece of a split, the left piece itself splits at it. -/
theorem append_cancel_left : ∀ (ΓL Γ₁ Δ₁ : List Ty) (a : Ty) (ΓR : List Ty),
    Γ₁ ++ Δ₁ = ΓL ++ a :: ΓR → ΓL.length < Γ₁.length →
    ∃ Γ₁R, Γ₁ = ΓL ++ a :: Γ₁R ∧ ΓR = Γ₁R ++ Δ₁ := by
  intro ΓL
  induction ΓL with
  | nil =>
      intro Γ₁ Δ₁ a ΓR heq hlen
      cases Γ₁ with
      | nil =>
          simp only [List.length_nil] at hlen
          omega
      | cons x Γ₁' =>
          simp only [List.cons_append, List.nil_append] at heq
          injection heq with hxa htail
          subst hxa
          exact ⟨Γ₁', rfl, htail.symm⟩
  | cons x ΓL' ih =>
      intro Γ₁ Δ₁ a ΓR heq hlen
      cases Γ₁ with
      | nil =>
          simp only [List.length_nil] at hlen
          omega
      | cons y Γ₁' =>
          simp only [List.cons_append] at heq
          injection heq with hxy heq'
          subst hxy
          have hlen' : ΓL'.length < Γ₁'.length := by
            simp only [List.length_cons] at hlen
            omega
          obtain ⟨Γ₁R, hsplit, hrest⟩ := ih Γ₁' Δ₁ a ΓR heq' hlen'
          exact ⟨Γ₁R, by rw [hsplit]; rfl, hrest⟩

/-- Split cancellation, RIGHT: if the substituted position lies in the
right piece of a split, the right piece itself splits at it. -/
theorem append_cancel_right : ∀ (ΓL Γ₁ Δ₁ : List Ty) (a : Ty) (ΓR : List Ty),
    Γ₁ ++ Δ₁ = ΓL ++ a :: ΓR → Γ₁.length ≤ ΓL.length →
    ∃ Δ₁L, Δ₁ = Δ₁L ++ a :: ΓR ∧ ΓL = Γ₁ ++ Δ₁L := by
  intro ΓL Γ₁ Δ₁ a ΓR heq hlen
  induction Δ₁ generalizing ΓL Γ₁ with
  | nil =>
      rw [List.append_nil] at heq
      have hlen' : Γ₁.length = (ΓL ++ a :: ΓR).length := by rw [heq]
      simp only [List.length_append, List.length_cons] at hlen'
      omega
  | cons y Δ₁' ih =>
      cases ΓL with
      | nil =>
          have h0 : Γ₁.length = 0 := by simpa using hlen
          cases Γ₁ with
          | nil =>
              simp only [List.nil_append] at heq
              injection heq with hy hR
              subst hy
              subst hR
              exact ⟨[], rfl, rfl⟩
          | cons z Γ₁'' =>
              simp only [List.length_cons] at h0
              omega
      | cons x ΓL' =>
          cases Γ₁ with
          | nil =>
              simp only [List.nil_append, List.cons_append] at heq
              injection heq with hyx hrest
              subst hyx
              have hlen' : (0 : Nat) ≤ ΓL'.length := by omega
              obtain ⟨Δ₁L, hsplit, hrest'⟩ := ih ΓL' (List.nil : List Ty) hrest hlen'
              exact ⟨y :: Δ₁L, by rw [hsplit]; rfl, by rw [hrest']; rfl⟩
          | cons z Γ₁' =>
              simp only [List.cons_append] at heq
              injection heq with hzx heq'
              subst hzx
              by_cases hlt : Γ₁'.length < ΓL'.length
              · have hlen' : (Γ₁' ++ [y]).length ≤ ΓL'.length := by
                  rw [List.length_append, List.length_cons, List.length_nil]
                  simp only [List.length_cons] at hlen
                  omega
                have heq'' : (Γ₁' ++ [y]) ++ Δ₁' = ΓL' ++ a :: ΓR := by
                  rw [List.append_assoc]
                  exact heq'
                obtain ⟨Δ₁L, hsplit, hrest⟩ := ih ΓL' (Γ₁' ++ [y]) heq'' hlen'
                refine ⟨y :: Δ₁L, by rw [hsplit]; rfl, ?_⟩
                rw [hrest]
                simp [List.append_assoc]
              · -- lengths equal: the binder is y itself
                have hlen'' : Γ₁'.length = ΓL'.length := by
                  simp only [List.length_cons] at hlen
                  omega
                obtain ⟨hpx, hrest⟩ := List.append_inj heq' hlen''
                subst hpx
                injection hrest with hy hR
                subst hy
                subst hR
                exact ⟨[], rfl, by simp⟩


/-- Transport a derivation along a TERM equation: the equation carries
the typing to the renamed term; the counters — functions of the
derivation alone — come along unchanged. The `contr` frame's rebuild:
the splice's premise reduct is typed at `t''`, and `mergeAt 0 ∘
unmergeAt 0 = id` renames it into the `mergeAt`-shape `Typed.contr`
demands. -/
theorem term_transport : ∀ {Γ : List Ty} {τ : Ty} {t₁ t₂ : Term} (heq : t₁ = t₂)
    (h : Typed Γ t₁ τ),
    ∃ (h' : Typed Γ t₂ τ), fixCount h' = fixCount h ∧ mintCount h' = mintCount h := by
  intro Γ τ t₁ t₂ heq h
  refine ⟨Eq.rec (motive := fun s _ => Typed Γ s τ) h heq, ?_, ?_⟩
  · subst heq; rfl
  · subst heq; rfl

/-- THE LINEAR CUT (the one-hole splice): substituting an argument for a
LINEAR binder's single occurrence, rebuilding the derivation frame by
frame along the spine from the binder's leaf to the root. The argument's
context is INSERTED where the binder was; side premises keep their
contexts and their terms (the insert-at-binder convention — no exchange
ever needed). The `contr` frame's duplicated-position case is closed by
linearity (the duplicated position is non-linear, the substituted binder
linear); the fix frame is vacuous — a fix's context is all-non-linear,
so a linear binder can never sit in it. The size clause is the engine:
the leaf (size 1) is replaced by the argument, everything else renamed —
the reduct is the body plus the argument minus the leaf. The counter
clauses carry cleanliness through the splice (S2's obligation). -/
theorem linear_cut :
    ∀ {Γ : List Ty} {body : Term} {σ : Ty} (h : Typed Γ body σ)
      (ΓL : List Ty) (a : Ty) (ΓR : List Ty) (Δ : List Ty) (arg : Term),
    (ha : Typed Δ arg a) → (hsplit : Γ = ΓL ++ a :: ΓR) → (hlin : a.isLinear = true) →
    (husage : uses h ΓL.length = 1) →
    ∃ (body' : Term) (h' : Typed (ΓL ++ Δ ++ ΓR) body' σ),
      ((tsize body' : Nat) : Int) = ((tsize body : Nat) : Int) + (((tsize arg : Nat) : Int) - 1) ∧
      fixCount h' = fixCount h + fixCount ha ∧
      mintCount h' = mintCount h + mintCount ha
  | _, _, _, @Typed.var a₀, ΓL, a, ΓR, Δ, arg, ha, hsplit, _, _ =>
      by
      cases ΓL with
      | nil =>
          rw [List.nil_append] at hsplit
          injection hsplit with hta hR
          subst hta
          subst hR
          rw [List.nil_append, List.append_nil]
          exact ⟨arg, ha, by simp only [tsize]; omega, by simp only [fixCount]; omega,
            by simp only [mintCount]; omega⟩
      | cons x ΓL₀ =>
          have hlen := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons, List.length_nil,
            List.length_cons] at hlen
          omega
  | _, _, _, Typed.unit, _, _, _, _, _, _, hsplit, _, _ =>
      by
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | _, _, _, Typed.nil, _, _, _, _, _, _, hsplit, _, _ =>
      by
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | _, _, _, Typed.gen, _, _, _, _, _, _, hsplit, _, _ =>
      by
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | _, _, _, Typed.red, _, _, _, _, _, _, hsplit, _, _ =>
      by
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | _, _, _, Typed.obj, _, _, _, _, _, _, hsplit, _, _ =>
      by
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | _, _, _, Typed.terminate, _, _, _, _, _, _, hsplit, _, _ =>
      by
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | _, _, _, @Typed.lam Γ₀ a₀ b₀ body₀ hbody, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, husage =>
      by
      have hsplit₀ : a₀ :: Γ₀ = (a₀ :: ΓL) ++ a :: ΓR := by
        rw [List.cons_append]; exact congrArg (fun l => a₀ :: l) hsplit
      have hu₀ : uses hbody (List.length (a₀ :: ΓL)) = 1 := by
        show uses hbody (ΓL.length + 1) = 1
        exact husage
      obtain ⟨body', hbody', hsz, hfc, hmc⟩ :=
        linear_cut hbody (a₀ :: ΓL) a ΓR Δ arg ha hsplit₀ hlin hu₀
      exact ⟨Term.lam a₀ body', Typed.lam hbody', by simp only [tsize]; omega,
        by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
  | _, _, _, @Typed.next Γ₀ a₀ t₀ h₀, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, husage =>
      by
      obtain ⟨t', h₀', hsz, hfc, hmc⟩ :=
        linear_cut h₀ ΓL a ΓR Δ arg ha hsplit hlin husage
      exact ⟨Term.next t', Typed.next h₀', by simp only [tsize]; omega,
        by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
  | _, _, _, @Typed.fix Γ₀ a₀ body₀ hΓ h₀, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, _ =>
      by
      have hpos : Γ₀[ΓL.length]? = some a := by
        rw [hsplit, List.get?_append_ge (Nat.le_refl _)]; simp
      have hkn := hΓ ΓL.length a hpos
      rw [hlin] at hkn
      exact Bool.noConfusion hkn
  | _, _, _, @Typed.app E Γ₁ Δ₁ a₁ b₁ fn₁ arg₁ hf ha₁ hs, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, husage =>
      by
      have hsplit' := hs.trans hsplit
      simp only [uses] at husage
      by_cases hlt : ΓL.length < Γ₁.length
      · rw [if_pos hlt] at husage
        obtain ⟨Γ₁R, hsplitL, hrest⟩ := append_cancel_left ΓL Γ₁ Δ₁ a ΓR hsplit' hlt
        obtain ⟨fn', hf', hsz, hfc, hmc⟩ :=
          linear_cut hf ΓL a Γ₁R Δ arg ha hsplitL hlin husage
        have hs' : (ΓL ++ Δ ++ Γ₁R) ++ Δ₁ = ΓL ++ Δ ++ ΓR := by
          rw [hrest]; simp [List.append_assoc]
        exact ⟨Term.app fn' arg₁, Typed.app hf' ha₁ hs', by simp only [tsize]; omega,
          by simp only [fixCount]; omega,
          by simp only [mintCount]; omega⟩
      · have hge : Γ₁.length ≤ ΓL.length := Nat.not_lt.mp hlt
        rw [if_neg (Nat.not_lt.mpr hge)] at husage
        obtain ⟨Δ₁L, hsplitR, hrestR⟩ := append_cancel_right ΓL Γ₁ Δ₁ a ΓR hsplit' hge
        have hlen := congrArg List.length hrestR
        simp only [List.length_append] at hlen
        have hdl : Δ₁L.length = ΓL.length - Γ₁.length := by omega
        have hu₂ : uses ha₁ Δ₁L.length = 1 := by rw [hdl]; exact husage
        obtain ⟨arg₁', ha₁', hsz, hfc, hmc⟩ :=
          linear_cut ha₁ Δ₁L a ΓR Δ arg ha hsplitR hlin hu₂
        have hs'' : Γ₁ ++ (Δ₁L ++ Δ ++ ΓR) = ΓL ++ Δ ++ ΓR := by
          simp only [List.append_assoc]
          rw [← List.append_assoc Γ₁ Δ₁L (Δ ++ ΓR), ← hrestR]
        exact ⟨Term.app fn₁ arg₁', Typed.app hf ha₁' hs'', by simp only [tsize]; omega,
          by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
  | _, _, _, @Typed.pair E Γ₁ Δ₁ a₁ b₁ l r hl hr hs, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, husage =>
      by
      have hsplit' := hs.trans hsplit
      simp only [uses] at husage
      by_cases hlt : ΓL.length < Γ₁.length
      · rw [if_pos hlt] at husage
        obtain ⟨Γ₁R, hsplitL, hrest⟩ := append_cancel_left ΓL Γ₁ Δ₁ a ΓR hsplit' hlt
        obtain ⟨l', hl', hsz, hfc, hmc⟩ :=
          linear_cut hl ΓL a Γ₁R Δ arg ha hsplitL hlin husage
        have hs' : (ΓL ++ Δ ++ Γ₁R) ++ Δ₁ = ΓL ++ Δ ++ ΓR := by
          rw [hrest]; simp [List.append_assoc]
        exact ⟨Term.pair l' r, Typed.pair hl' hr hs', by simp only [tsize]; omega,
          by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
      · have hge : Γ₁.length ≤ ΓL.length := Nat.not_lt.mp hlt
        rw [if_neg (Nat.not_lt.mpr hge)] at husage
        obtain ⟨Δ₁L, hsplitR, hrestR⟩ := append_cancel_right ΓL Γ₁ Δ₁ a ΓR hsplit' hge
        have hlen := congrArg List.length hrestR
        simp only [List.length_append] at hlen
        have hdl : Δ₁L.length = ΓL.length - Γ₁.length := by omega
        have hu₂ : uses hr Δ₁L.length = 1 := by rw [hdl]; exact husage
        obtain ⟨r', hr', hsz, hfc, hmc⟩ :=
          linear_cut hr Δ₁L a ΓR Δ arg ha hsplitR hlin hu₂
        have hs'' : Γ₁ ++ (Δ₁L ++ Δ ++ ΓR) = ΓL ++ Δ ++ ΓR := by
          simp only [List.append_assoc]
          rw [← List.append_assoc Γ₁ Δ₁L (Δ ++ ΓR), ← hrestR]
        exact ⟨Term.pair l r', Typed.pair hl hr' hs'', by simp only [tsize]; omega,
          by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
  | _, _, _, @Typed.cons E Γ₁ Δ₁ hd tl hc ht hs, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, husage =>
      by
      have hsplit' := hs.trans hsplit
      simp only [uses] at husage
      by_cases hlt : ΓL.length < Γ₁.length
      · rw [if_pos hlt] at husage
        obtain ⟨Γ₁R, hsplitL, hrest⟩ := append_cancel_left ΓL Γ₁ Δ₁ a ΓR hsplit' hlt
        obtain ⟨hd', hc', hsz, hfc, hmc⟩ :=
          linear_cut hc ΓL a Γ₁R Δ arg ha hsplitL hlin husage
        have hs' : (ΓL ++ Δ ++ Γ₁R) ++ Δ₁ = ΓL ++ Δ ++ ΓR := by
          rw [hrest]; simp [List.append_assoc]
        exact ⟨Term.cons hd' tl, Typed.cons hc' ht hs', by simp only [tsize]; omega,
          by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
      · have hge : Γ₁.length ≤ ΓL.length := Nat.not_lt.mp hlt
        rw [if_neg (Nat.not_lt.mpr hge)] at husage
        obtain ⟨Δ₁L, hsplitR, hrestR⟩ := append_cancel_right ΓL Γ₁ Δ₁ a ΓR hsplit' hge
        have hlen := congrArg List.length hrestR
        simp only [List.length_append] at hlen
        have hdl : Δ₁L.length = ΓL.length - Γ₁.length := by omega
        have hu₂ : uses ht Δ₁L.length = 1 := by rw [hdl]; exact husage
        obtain ⟨tl', ht', hsz, hfc, hmc⟩ :=
          linear_cut ht Δ₁L a ΓR Δ arg ha hsplitR hlin hu₂
        have hs'' : Γ₁ ++ (Δ₁L ++ Δ ++ ΓR) = ΓL ++ Δ ++ ΓR := by
          simp only [List.append_assoc]
          rw [← List.append_assoc Γ₁ Δ₁L (Δ ++ ΓR), ← hrestR]
        exact ⟨Term.cons hd tl', Typed.cons hc ht' hs'', by simp only [tsize]; omega,
          by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
  | _, _, _, @Typed.snoc E Γ₁ Δ₁ t u ht hu hs, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, husage =>
      by
      have hsplit' := hs.trans hsplit
      simp only [uses] at husage
      by_cases hlt : ΓL.length < Γ₁.length
      · rw [if_pos hlt] at husage
        obtain ⟨Γ₁R, hsplitL, hrest⟩ := append_cancel_left ΓL Γ₁ Δ₁ a ΓR hsplit' hlt
        obtain ⟨t', ht', hsz, hfc, hmc⟩ :=
          linear_cut ht ΓL a Γ₁R Δ arg ha hsplitL hlin husage
        have hs' : (ΓL ++ Δ ++ Γ₁R) ++ Δ₁ = ΓL ++ Δ ++ ΓR := by
          rw [hrest]; simp [List.append_assoc]
        exact ⟨Term.snoc t' u, Typed.snoc ht' hu hs', by simp only [tsize]; omega,
          by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
      · have hge : Γ₁.length ≤ ΓL.length := Nat.not_lt.mp hlt
        rw [if_neg (Nat.not_lt.mpr hge)] at husage
        obtain ⟨Δ₁L, hsplitR, hrestR⟩ := append_cancel_right ΓL Γ₁ Δ₁ a ΓR hsplit' hge
        have hlen := congrArg List.length hrestR
        simp only [List.length_append] at hlen
        have hdl : Δ₁L.length = ΓL.length - Γ₁.length := by omega
        have hu₂ : uses hu Δ₁L.length = 1 := by rw [hdl]; exact husage
        obtain ⟨u', hu', hsz, hfc, hmc⟩ :=
          linear_cut hu Δ₁L a ΓR Δ arg ha hsplitR hlin hu₂
        have hs'' : Γ₁ ++ (Δ₁L ++ Δ ++ ΓR) = ΓL ++ Δ ++ ΓR := by
          simp only [List.append_assoc]
          rw [← List.append_assoc Γ₁ Δ₁L (Δ ++ ΓR), ← hrestR]
        exact ⟨Term.snoc t u', Typed.snoc ht hu' hs'', by simp only [tsize]; omega,
          by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a₁ b₁ c₁ t₁ body₁ ht hb hs, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, husage =>
      by
      have hsplit' := hs.trans hsplit
      simp only [uses] at husage
      by_cases hlt : ΓL.length < Γ₁.length
      · rw [if_pos hlt] at husage
        obtain ⟨Γ₁R, hsplitL, hrest⟩ := append_cancel_left ΓL Γ₁ Γ₂ a ΓR hsplit' hlt
        obtain ⟨t', ht', hsz, hfc, hmc⟩ :=
          linear_cut ht ΓL a Γ₁R Δ arg ha hsplitL hlin husage
        have hs' : (ΓL ++ Δ ++ Γ₁R) ++ Γ₂ = ΓL ++ Δ ++ ΓR := by
          rw [hrest]; simp [List.append_assoc]
        exact ⟨Term.lete t' body₁, Typed.lete ht' hb hs', by simp only [tsize]; omega,
          by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
      · have hge : Γ₁.length ≤ ΓL.length := Nat.not_lt.mp hlt
        rw [if_neg (Nat.not_lt.mpr hge)] at husage
        obtain ⟨Γ₂L, hsplitR, hrestR⟩ := append_cancel_right ΓL Γ₁ Γ₂ a ΓR hsplit' hge
        have hlen := congrArg List.length hrestR
        simp only [List.length_append] at hlen
        have hgl : Γ₂L.length = ΓL.length - Γ₁.length := by omega
        have hsplitB : b₁ :: a₁ :: Γ₂ = (b₁ :: a₁ :: Γ₂L) ++ a :: ΓR := by
          rw [List.cons_append, List.cons_append, hsplitR]
        have hu₂ : uses hb (List.length (b₁ :: a₁ :: Γ₂L)) = 1 := by
          have hlen2 : List.length (b₁ :: a₁ :: Γ₂L) = ΓL.length - Γ₁.length + 2 := by
            simp only [List.length_cons]; omega
          rw [hlen2]; exact husage
        obtain ⟨body', hb', hsz, hfc, hmc⟩ :=
          linear_cut hb (b₁ :: a₁ :: Γ₂L) a ΓR Δ arg ha hsplitB hlin hu₂
        have hs'' : Γ₁ ++ (Γ₂L ++ Δ ++ ΓR) = ΓL ++ Δ ++ ΓR := by
          simp only [List.append_assoc]
          rw [← List.append_assoc Γ₁ Γ₂L (Δ ++ ΓR), ← hrestR]
        exact ⟨Term.lete t₁ body', Typed.lete ht hb' hs'', by simp only [tsize]; omega,
          by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩
  | _, _, _, @Typed.contr Γ₀ k t₀ τ hk h₀, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, husage =>
      by
      cases ΓL with
      | nil =>
          rw [List.nil_append] at hsplit
          injection hsplit with hka hR
          subst hka
          rw [hlin] at hk
          exact Bool.noConfusion hk
      | cons k' ΓL₀ =>
          rw [List.cons_append] at hsplit
          injection hsplit with hkk hR
          subst hkk
          simp only [uses] at husage
          rw [if_neg (by simp : ¬ (List.length (k :: ΓL₀) = 0))] at husage
          have hu₀ : uses h₀ (List.length (k :: k :: ΓL₀)) = 1 := husage
          have hsplit₀ : k :: k :: Γ₀ = (k :: k :: ΓL₀) ++ a :: ΓR := by
            rw [List.cons_append, List.cons_append, hR]
          obtain ⟨t'', h₀', hsz, hfc, hmc⟩ :=
            linear_cut h₀ (k :: k :: ΓL₀) a ΓR Δ arg ha hsplit₀ hlin hu₀
          have hmu : Term.mergeAt 0 (Term.unmergeAt 0 t'') = t'' :=
            mergeAt_unmergeAt 0 t''
          obtain ⟨h₀'', hfct, hmct⟩ := term_transport hmu.symm h₀'
          refine ⟨Term.unmergeAt 0 t'', Typed.contr hk h₀'', ?_, ?_, ?_⟩
          · rw [unmergeAt_tsize 0 t'']
            have hmg := mergeAt_tsize 0 t₀
            rw [hmg] at hsz
            omega
          · simp only [fixCount]; omega
          · simp only [mintCount]; omega
  | _, _, _, @Typed.weak Γ₀ k t₀ τ hk h₀, ΓL, a, ΓR, Δ, arg, ha, hsplit, hlin, husage =>
      by
      cases ΓL with
      | nil =>
          have hcontra : (0 : Nat) = 1 := husage
          exact absurd hcontra (by decide)
      | cons k' ΓL₀ =>
          rw [List.cons_append] at hsplit
          injection hsplit with hkk hR
          subst hkk
          simp only [uses] at husage
          rw [if_neg (by simp : ¬ (List.length (k :: ΓL₀) = 0))] at husage
          have hu₀ : uses h₀ (List.length ΓL₀) = 1 := husage
          obtain ⟨t', h₀', hsz, hfc, hmc⟩ :=
            linear_cut h₀ ΓL₀ a ΓR Δ arg ha hR hlin hu₀
          refine ⟨Term.liftAt 0 t', Typed.weak hk h₀', ?_, ?_, ?_⟩
          · rw [liftAt_tsize 0 t', liftAt_tsize 0 t₀]
            omega
          · simp only [fixCount]; omega
          · simp only [mintCount]; omega

/-- THE REDEX SPECIALIZATION (subject reduction's engine at a fire): the
cut at the λ-binder — position 0, left piece empty — rebuilds the body at
the argument's context spliced in front. The size clause reads in Nat:
the reduct plus the two consumed nodes (fire + binder) equals the redex —
so every linear beta step strictly shrinks the term. -/
theorem linear_beta_splice {Γf Δ : List Ty} {a b : Ty} {body arg : Term}
    (hbody : Typed (a :: Γf) body b) (ha : Typed Δ arg a)
    (hlin : a.isLinear = true) (hu : uses hbody 0 = 1) :
    ∃ (body' : Term) (h' : Typed (Δ ++ Γf) body' b),
      tsize body' + 3 = tsize (Term.app (Term.lam a body) arg) ∧
      fixCount h' = fixCount (Typed.lam hbody) + fixCount ha ∧
      mintCount h' = mintCount (Typed.lam hbody) + mintCount ha := by
  have htp := tsize_pos arg
  obtain ⟨body', h', hsz, hfc, hmc⟩ :=
    linear_cut hbody [] a Γf Δ arg ha rfl hlin hu
  exact ⟨body', h', by simp only [tsize]; omega,
    by simp only [fixCount]; omega, by simp only [mintCount]; omega⟩

end Dcare
