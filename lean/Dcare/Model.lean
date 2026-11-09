import Dcare.Typing

/-!
# The barren-world interpretation (v4: the world after the last knower)

An INHABITATION model, not a productivity model. EVERYTHING downstream of
a living knower is barren — `content`, `knower`, `stream`, `knowledge`,
`value` all denote `False`; only the inert types remain: the archive
(`trace`), `unit`, and the delay (`▷`). The interpretation is the
diagnostic claim in miniature: strip the knower and everything derived
from it collapses; records and deferrals are all that stay.

Soundness then kills the whole non-derivability family at once:
`no_closed_content`/`no_closed_knower` (closed resources),
`no_trace_to_stream` (trace-only contexts interpret True, stream False),
and the past-cannot family (a closed `trace → knowledge` would be a
function `True → (True → False)` — soundness constructs it from the
derivation, which is the absurdity).

Why `fix` is sound here: ▷ collapses to `True`, so a guarded fixpoint is
discharged by a truth token — the unit delay is exactly the one-interval
deferral the later modality licenses. The model is blind to productivity
(by design — productivity is the operational semantics' business); it
sees inhabitation only.

The gated structural rules are sound here for every type (copy/discard
of proofs are free) — this model certifies resource EXISTENCE, not
resource COUNT; the count is the derivation-indexed counting lemma
(`Dcare.Count`).
-/

namespace Dcare

def interp : Ty → Prop
  | .content => False
  | .knower => False
  | .knowledge | .value | .stream => False
  | .unit | .trace => True
  | .later _ => True
  | .tensor a b => interp a ∧ interp b
  | .arrow a b => interp a → interp b

def interpCtx : List Ty → Prop
  | [] => True
  | a :: Γ => interp a ∧ interpCtx Γ

theorem interp_append : ∀ (Γ₁ Δ : List Ty),
    interpCtx (Γ₁ ++ Δ) → interpCtx Γ₁ ∧ interpCtx Δ
  | [], _, _ => ⟨True.intro, by assumption⟩
  | _ :: Γ₁, Δ, x =>
      ⟨⟨x.1, (interp_append Γ₁ Δ x.2).1⟩, (interp_append Γ₁ Δ x.2).2⟩

/-- Split-aware packaging: no need to name the split's contexts. -/
theorem interp_append' {E Γ Δ : List Ty} (hs : Γ ++ Δ = E) :
    interpCtx E → interpCtx Γ ∧ interpCtx Δ := by
  subst hs; exact interp_append Γ Δ

theorem get?_zero_cons {a : Ty} {Γ : List Ty} : (a :: Γ)[0]? = some a := rfl

theorem get?_succ_cons {a : Ty} {Γ : List Ty} {i : Nat} : (a :: Γ)[i + 1]? = Γ[i]? := rfl

theorem get?_nil {i : Nat} : ([] : List Ty)[i]? = none := rfl

theorem lookup_interp {Γ : List Ty} {i : Nat} {a : Ty} (h : Γ[i]? = some a) :
    interpCtx Γ → interp a := by
  induction i generalizing Γ with
  | zero =>
      cases Γ with
      | nil => rw [get?_nil] at h; contradiction
      | cons _ _ =>
          rw [get?_zero_cons] at h
          injection h with h'
          subst h'
          exact fun γ => γ.1
  | succ n ih =>
      cases Γ with
      | nil => rw [get?_nil] at h; contradiction
      | cons _ _ => rw [get?_succ_cons] at h; exact fun γ => ih h γ.2

/-- Soundness of the barren-world interpretation: every derivable sequent
is valid in the barren world. -/
theorem sound {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ) :
    interpCtx Γ → interp τ := by
  induction h with
  | var => intro γ; exact γ.1
  | lam _ ih => intro γ x; exact ih ⟨x, γ⟩
  | app _ _ hs ihf iha =>
      intro γ
      exact ihf (interp_append' hs γ).1 (iha (interp_append' hs γ).2)
  | pair _ _ hs ihl ihr =>
      intro γ
      exact ⟨ihl (interp_append' hs γ).1, ihr (interp_append' hs γ).2⟩
  | lete _ _ hs iht ihb =>
      intro γ
      exact ihb ⟨(iht (interp_append' hs γ).1).2,
        ⟨(iht (interp_append' hs γ).1).1, (interp_append' hs γ).2⟩⟩
  | unit => intro _; exact True.intro
  | next _ _ => intro _; exact True.intro
  | fix _ _ ih => intro γ; exact ih γ True.intro
  | cons _ _ hs ihc _ =>
      -- v2: `stream` is barren, and the content premise supplies the
      -- falsehood — soundness of `cons` is a FLOW through its resource.
      intro γ
      exact ihc (interp_append' hs γ).1
  | nil => intro _; exact True.intro
  | snoc _ _ hs _ _ =>
      intro _; exact True.intro
  | gen => intro _ k; exact k.elim
  | red => intro _ s; exact s.elim
  | obj => intro _ s; exact s.elim
  | terminate => intro _ _; exact True.intro
  | contr _ _ ih => intro p; exact ih ⟨p.1, p⟩
  | weak _ _ ih => intro p; exact ih p.2

/-- Content ex nihilo requires a living knower: no closed term inhabits
the content type. The coalgebra made visible as an inhabitation fact. -/
theorem no_closed_content {t : Term} (h : Typed [] t Ty.content) : False :=
  (sound h True.intro).elim

/-- Dually, no closed term is a knower: knower-status is never free. -/
theorem no_closed_knower {t : Term} (h : Typed [] t Ty.knower) : False :=
  (sound h True.intro).elim

end Dcare
