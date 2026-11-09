/-!
# List plumbing for the counting lemmas

Pure list facts, no dependencies. (Some overlap with `Dcare.Model`'s
private lemmas — kept separate so neither depends on the other.)
-/

theorem List.get?_nil' {α : Type} {i : Nat} : ([] : List α)[i]? = none := rfl

theorem List.get?_zero_cons' {α : Type} {x : α} {l : List α} : (x :: l)[0]? = some x := rfl

theorem List.get?_succ_cons' {α : Type} {x : α} {l : List α} {i : Nat} :
    (x :: l)[i + 1]? = l[i]? := rfl

theorem List.get?_add_two {α : Type} {x y : α} {l : List α} {j : Nat} :
    (x :: y :: l)[j + 2]? = l[j]? := rfl

theorem List.get?_append_lt {α : Type} {Γ Δ : List α} {i : Nat} (h : i < Γ.length) :
    (Γ ++ Δ)[i]? = Γ[i]? := by
  induction Γ generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons x Γ' ih =>
      cases i with
      | zero => rfl
      | succ n =>
          show (x :: (Γ' ++ Δ))[n + 1]? = (x :: Γ')[n + 1]?
          rw [List.get?_succ_cons', List.get?_succ_cons']
          exact ih (Nat.succ_lt_succ_iff.mp h)

theorem List.get?_append_ge {α : Type} {Γ Δ : List α} {i : Nat} (h : Γ.length ≤ i) :
    (Γ ++ Δ)[i]? = Δ[i - Γ.length]? := by
  induction Γ generalizing i with
  | nil => rfl
  | cons x Γ' ih =>
      cases i with
      | zero => exact absurd h (Nat.not_succ_le_zero Γ'.length)
      | succ n =>
          show (x :: (Γ' ++ Δ))[n + 1]? = Δ[n + 1 - (Γ'.length + 1)]?
          rw [List.get?_succ_cons', ih (Nat.succ_le_succ_iff.mp h),
            Nat.succ_sub_succ_eq_sub]

/-- A position that returns `some` is within the list. -/
theorem List.get?_some_lt {α : Type} : ∀ {l : List α} {i : Nat} {b : α},
    l[i]? = some b → i < l.length
  | [], i, b, h => by rw [List.get?_nil'] at h; contradiction
  | x :: l', 0, b, h => by
      rw [List.get?_zero_cons'] at h
      injection h with _
      exact Nat.zero_lt_succ _
  | x :: l', i + 1, b, h => by
      rw [List.get?_succ_cons'] at h
      exact Nat.succ_lt_succ_iff.mpr (List.get?_some_lt h)
