import Dcare.Typing
import Dcare.ListAux

/-!
# Derivation-indexed counting

With split-only rules, flat TERM-indexed counting is unmoored: a composed
term's de Bruijn indices are sub-context-relative (`app (var 0) (var 0)`
at `[arrow content content, content]` uses index 0 for two different
hypotheses). The count is therefore carried by the DERIVATION: `uses h i`
counts how many var-leaves of `h` spend the hypothesis at position `i`,
each rule threading splits and binders explicitly. This required `Typed`
to be `Type`-valued (derivation data).

`single_linear_use` — the counting lemma: every LINEAR hypothesis is
spent exactly once. First corollary: `no_weakening_content`. Still to
come: the upper bound (`uses ≤ 1` for linear, hence `no_contraction`)
and the flow/weight analysis behind `no_vanishing`.
-/

namespace Dcare

def uses : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat → Nat
  | _, _, _, Typed.var => fun i => if i = 0 then 1 else 0
  | _, _, _, @Typed.lam _ _ _ _ h => fun i => uses h (i + 1)
  | _, _, _, @Typed.app _ Γ _ _ _ _ _ hf ha _ =>
      fun i => if i < Γ.length then uses hf i else uses ha (i - Γ.length)
  | _, _, _, @Typed.pair _ Γ _ _ _ _ _ hl hr _ =>
      fun i => if i < Γ.length then uses hl i else uses hr (i - Γ.length)
  | _, _, _, @Typed.lete _ Γ₁ _ _ _ _ _ _ ht hb _ =>
      fun i => if i < Γ₁.length then uses ht i else uses hb (i - Γ₁.length + 2)
  | _, _, _, Typed.unit => fun _ => 0
  | _, _, _, @Typed.next _ _ _ h => fun i => uses h i
  | _, _, _, @Typed.fix _ _ _ _ h => fun i => uses h i
  | _, _, _, @Typed.cons _ Γ _ _ _ hc ht _ =>
      fun i => if i < Γ.length then uses hc i else uses ht (i - Γ.length)
  | _, _, _, Typed.nil => fun _ => 0
  | _, _, _, @Typed.snoc _ Γ _ _ _ ht hu _ =>
      fun i => if i < Γ.length then uses ht i else uses hu (i - Γ.length)
  | _, _, _, Typed.gen => fun _ => 0
  | _, _, _, Typed.red => fun _ => 0
  | _, _, _, Typed.obj => fun _ => 0
  | _, _, _, Typed.terminate => fun _ => 0
  | _, _, _, @Typed.contr _ _ _ _ _ h =>
      fun i => if i = 0 then uses h 0 + uses h 1 else uses h (i + 1)
  | _, _, _, @Typed.weak _ _ _ _ _ h =>
      fun i => if i = 0 then 0 else uses h (i - 1)

/-- The counting lemma: every LINEAR hypothesis of a derivation is spent
exactly once — neither discarded nor duplicated. -/
theorem single_linear_use : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ)
    (i : Nat) (a : Ty), Γ[i]? = some a → a.isLinear = true → uses h i = 1 := by
  intro Γ t τ h
  induction h with
  | var =>
      intro i a hpos _
      cases i with
      | zero => rfl
      | succ n =>
          rw [List.get?_succ_cons', List.get?_nil'] at hpos
          contradiction
  | lam _ ih =>
      intro i a hpos hlin
      exact ih (i + 1) a (by rw [List.get?_succ_cons']; exact hpos) hlin
  | app hf ha hs ihf iha =>
      rename_i _ Γ _ _ _ _ _
      intro i a hpos hlin
      by_cases hlt : i < Γ.length
      · show (if i < Γ.length then uses hf i else uses ha (i - Γ.length)) = 1
        rw [if_pos hlt]
        exact ihf i a (by rw [← List.get?_append_lt hlt, hs]; exact hpos) hlin
      · show (if i < Γ.length then uses hf i else uses ha (i - Γ.length)) = 1
        rw [if_neg hlt]
        have hge : Γ.length ≤ i := Nat.not_lt.mp hlt
        exact iha (i - Γ.length) a
          (by rw [← List.get?_append_ge hge, hs]; exact hpos) hlin
  | pair hl hr hs ihl ihr =>
      rename_i _ Γ _ _ _ _ _
      intro i a hpos hlin
      by_cases hlt : i < Γ.length
      · show (if i < Γ.length then uses hl i else uses hr (i - Γ.length)) = 1
        rw [if_pos hlt]
        exact ihl i a (by rw [← List.get?_append_lt hlt, hs]; exact hpos) hlin
      · show (if i < Γ.length then uses hl i else uses hr (i - Γ.length)) = 1
        rw [if_neg hlt]
        have hge : Γ.length ≤ i := Nat.not_lt.mp hlt
        exact ihr (i - Γ.length) a
          (by rw [← List.get?_append_ge hge, hs]; exact hpos) hlin
  | lete ht hb hs iht ihb =>
      rename_i _ Γ₁ _ _ _ _ _ _
      intro i a hpos hlin
      by_cases hlt : i < Γ₁.length
      · show (if i < Γ₁.length then uses ht i else uses hb (i - Γ₁.length + 2)) = 1
        rw [if_pos hlt]
        exact iht i a (by rw [← List.get?_append_lt hlt, hs]; exact hpos) hlin
      · show (if i < Γ₁.length then uses ht i else uses hb (i - Γ₁.length + 2)) = 1
        rw [if_neg hlt]
        have hge : Γ₁.length ≤ i := Nat.not_lt.mp hlt
        exact ihb (i - Γ₁.length + 2) a
          (by rw [List.get?_add_two, ← List.get?_append_ge hge, hs]; exact hpos) hlin
  | unit => intro i a hpos _; rw [List.get?_nil'] at hpos; contradiction
  | next _ ih => intro i a hpos hlin; exact ih i a hpos hlin
  | fix _ _ ih => intro i a hpos hlin; exact ih i a hpos hlin
  | cons hc ht hs ihc iht =>
      rename_i _ Γ _ _ _
      intro i a hpos hlin
      by_cases hlt : i < Γ.length
      · show (if i < Γ.length then uses hc i else uses ht (i - Γ.length)) = 1
        rw [if_pos hlt]
        exact ihc i a (by rw [← List.get?_append_lt hlt, hs]; exact hpos) hlin
      · show (if i < Γ.length then uses hc i else uses ht (i - Γ.length)) = 1
        rw [if_neg hlt]
        have hge : Γ.length ≤ i := Nat.not_lt.mp hlt
        exact iht (i - Γ.length) a
          (by rw [← List.get?_append_ge hge, hs]; exact hpos) hlin
  | nil => intro i a hpos _; rw [List.get?_nil'] at hpos; contradiction
  | snoc ht hu hs iht ihu =>
      rename_i _ Γ _ _ _
      intro i a hpos hlin
      by_cases hlt : i < Γ.length
      · show (if i < Γ.length then uses ht i else uses hu (i - Γ.length)) = 1
        rw [if_pos hlt]
        exact iht i a (by rw [← List.get?_append_lt hlt, hs]; exact hpos) hlin
      · show (if i < Γ.length then uses ht i else uses hu (i - Γ.length)) = 1
        rw [if_neg hlt]
        have hge : Γ.length ≤ i := Nat.not_lt.mp hlt
        exact ihu (i - Γ.length) a
          (by rw [← List.get?_append_ge hge, hs]; exact hpos) hlin
  | gen => intro i a hpos _; rw [List.get?_nil'] at hpos; contradiction
  | red => intro i a hpos _; rw [List.get?_nil'] at hpos; contradiction
  | obj => intro i a hpos _; rw [List.get?_nil'] at hpos; contradiction
  | terminate =>
      intro i a hpos _; rw [List.get?_nil'] at hpos; contradiction
  | contr hk h ih =>
      rename_i _ k _ _
      intro i a hpos hlin
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hka
          subst hka
          rw [hlin] at hk
          exact Bool.noConfusion hk
      | succ n =>
          show (if n + 1 = 0 then uses h 0 + uses h 1 else uses h (n + 1 + 1)) = 1
          rw [if_neg (Nat.succ_ne_zero n)]
          exact ih (n + 1 + 1) a
            (by rw [List.get?_add_two, ← List.get?_succ_cons']; exact hpos) hlin
  | weak hk h ih =>
      rename_i _ k _ _
      intro i a hpos hlin
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hka
          subst hka
          rw [hlin] at hk
          exact Bool.noConfusion hk
      | succ n =>
          show (if n + 1 = 0 then 0 else uses h (n + 1 - 1)) = 1
          rw [if_neg (Nat.succ_ne_zero n), Nat.succ_sub_one]
          exact ih n a (by rw [← List.get?_succ_cons']; exact hpos) hlin

end Dcare
