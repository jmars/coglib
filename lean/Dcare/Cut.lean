import Dcare.Typing
import Dcare.Count
import Dcare.Subst

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

end Dcare
