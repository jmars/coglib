import Dcare.Syntax

/-!
# Substitution: the data layer for the linear cut

The multiplicative (split-context) cut needs a depth-aware single
substitution on de Bruijn terms: `substG k m arg body` replaces the
binder at depth `k` by `arg` (lifted by `m + k` — `m` is the base lift
carrying `arg`'s context past the body's own), decrements the indices
above it, and leaves local binders alone.

THE SIZE LAW is the linear-beta engine: substitution replaces each
occurrence of the substituted variable (size 1) by a copy of `arg`
(size `tsize arg`), so

  tsize (substG k m arg body) = tsize body + occCount k body * (tsize arg - 1)

as an integer equation. At a LINEAR binder — one occurrence — the
substituted term is strictly smaller than the redex
`app (lam a body) arg`, which is why the linear-beta step relation
terminates by size alone (no type-based termination argument needed).
-/

namespace Dcare

/-- Term size (nodes, constants included). -/
def tsize : Term → Nat
  | .var _ => 1
  | .lam _ b => 1 + tsize b
  | .app f x => 1 + tsize f + tsize x
  | .pair l r => 1 + tsize l + tsize r
  | .lete t b => 1 + tsize t + tsize b
  | .unit => 1
  | .next t => 1 + tsize t
  | .fix t => 1 + tsize t
  | .cons h t => 1 + tsize h + tsize t
  | .nil => 1
  | .snoc t u => 1 + tsize t + tsize u
  | .gen => 1
  | .red => 1
  | .obj => 1
  | .terminate => 1

/-- Lift every free variable by `n` (iterated `Term.liftAt 0`). -/
def Term.liftN : Nat → Term → Term
  | 0, t => t
  | n + 1, t => Term.liftN n (Term.liftAt 0 t)

/-- Occurrences of de Bruijn index `k` in a term (the count the linear
discipline drives to exactly one). -/
def occCount : Nat → Term → Nat
  | k, .var i => if i = k then 1 else 0
  | k, .lam _ b => occCount (k + 1) b
  | k, .app f x => occCount k f + occCount k x
  | k, .pair l r => occCount k l + occCount k r
  | k, .lete t b => occCount k t + occCount (k + 2) b
  | k, .next t => occCount k t
  | k, .fix t => occCount k t
  | k, .cons h t => occCount k h + occCount k t
  | k, .snoc t u => occCount k t + occCount k u
  | _, .unit => 0
  | _, .nil => 0
  | _, .gen => 0
  | _, .red => 0
  | _, .obj => 0
  | _, .terminate => 0

/-- Depth-aware single substitution: `substG k m arg body` — index `k`
is the substituted binder (replaced by `arg` lifted by `m + k`), indices
above `k` decrement, indices below `k` are local binders. -/
def substG : Nat → Nat → Term → Term → Term
  | k, m, arg, .var i =>
      if i < k then .var i
      else if i = k then Term.liftN (m + k) arg
      else .var (i - 1)
  | k, m, arg, .lam a b => .lam a (substG (k + 1) m arg b)
  | k, m, arg, .app f x => .app (substG k m arg f) (substG k m arg x)
  | k, m, arg, .pair l r => .pair (substG k m arg l) (substG k m arg r)
  | k, m, arg, .lete t b => .lete (substG k m arg t) (substG (k + 2) m arg b)
  | _, _, _, .unit => .unit
  | k, m, arg, .next t => .next (substG k m arg t)
  | k, m, arg, .fix t => .fix (substG k m arg t)
  | k, m, arg, .cons h t => .cons (substG k m arg h) (substG k m arg t)
  | _, _, _, .nil => .nil
  | k, m, arg, .snoc t u => .snoc (substG k m arg t) (substG k m arg u)
  | _, _, _, .gen => .gen
  | _, _, _, .red => .red
  | _, _, _, .obj => .obj
  | _, _, _, .terminate => .terminate

/-- Lifting preserves term size (each `liftAt` is a renaming). -/
theorem liftAt_tsize : ∀ (d : Nat) (t : Term), tsize (Term.liftAt d t) = tsize t := by
  intro d t
  induction t generalizing d with
  | var i => simp only [Term.liftAt, tsize]; split <;> rfl
  | lam a b ih => simp only [Term.liftAt, tsize, ih (d + 1)]
  | app f x ihf ihx => simp only [Term.liftAt, tsize, ihf d, ihx d]
  | pair l r ihl ihr => simp only [Term.liftAt, tsize, ihl d, ihr d]
  | lete t b iht ihb => simp only [Term.liftAt, tsize, iht d, ihb (d + 2)]
  | unit => simp [Term.liftAt, tsize]
  | next t ih => simp only [Term.liftAt, tsize, ih d]
  | fix t ih => simp only [Term.liftAt, tsize, ih d]
  | cons h t ihh iht => simp only [Term.liftAt, tsize, ihh d, iht d]
  | nil => simp [Term.liftAt, tsize]
  | snoc t u iht ihu => simp only [Term.liftAt, tsize, iht d, ihu d]
  | gen => simp [Term.liftAt, tsize]
  | red => simp [Term.liftAt, tsize]
  | obj => simp [Term.liftAt, tsize]
  | terminate => simp [Term.liftAt, tsize]

/-- Iterated lifting preserves term size. -/
theorem liftN_tsize : ∀ (n : Nat) (t : Term), tsize (Term.liftN n t) = tsize t := by
  intro n t
  induction n generalizing t with
  | zero => rfl
  | succ n' ih => rw [Term.liftN, ih (Term.liftAt 0 t), liftAt_tsize 0 t]

/-- THE SUBSTITUTION SIZE LAW: substitution replaces each occurrence of
the substituted variable (size 1) by a copy of `arg`, so the size moves
by `occCount * (size arg - 1)`. Integer-valued to avoid truncation; the
product is eliminated per-case by `Int.add_sub_cancel_left` before
omega (omega rejects nonlinear hypotheses). -/
theorem substG_tsize : ∀ (k m : Nat) (arg body : Term),
    (tsize (substG k m arg body) : Int)
      = (tsize body : Int) + (occCount k body : Int) * ((tsize arg : Int) - 1) := by
  intro k m arg body
  induction body generalizing k with
  | var i =>
      by_cases hlt : i < k
      · have hocc0 : occCount k (Term.var i) = 0 := by
          rw [occCount, if_neg (by omega : ¬ i = k)]
        have hsub : substG k m arg (Term.var i) = Term.var i := by
          rw [substG, if_pos hlt]
        rw [hsub, hocc0]
        simp [tsize]
      · by_cases heq : i = k
        · have hocc1 : occCount k (Term.var i) = 1 := by
            rw [occCount, if_pos heq]
          have hsub : substG k m arg (Term.var i) = Term.liftN (m + k) arg := by
            rw [substG, if_neg hlt, if_pos heq]
          rw [hsub, hocc1, liftN_tsize, tsize]
          omega
        · have hocc0 : occCount k (Term.var i) = 0 := by
            rw [occCount, if_neg heq]
          have hsub : substG k m arg (Term.var i) = Term.var (i - 1) := by
            rw [substG, if_neg hlt, if_neg heq]
          rw [hsub, hocc0]
          simp [tsize]
  | lam a b ih =>
      have h := ih (k + 1)
      have e : ((occCount (k + 1) b : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG (k + 1) m arg b) : Int) - (tsize b : Int) := by
        rw [h]; omega
      simp only [substG, occCount, tsize]
      rw [e]
      omega
  | app f x ihf ihx =>
      have h1 := ihf k
      have h2 := ihx k
      have e1 : ((occCount k f : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg f) : Int) - (tsize f : Int) := by
        rw [h1]; omega
      have e2 : ((occCount k x : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg x) : Int) - (tsize x : Int) := by
        rw [h2]; omega
      have hd : ((occCount k f + occCount k x : Nat) : Int) * ((tsize arg : Int) - 1)
          = (occCount k f : Int) * ((tsize arg : Int) - 1)
            + (occCount k x : Int) * ((tsize arg : Int) - 1) := by
        rw [Int.natCast_add, Int.add_mul]
      simp only [substG, occCount, tsize]
      rw [hd, e1, e2]
      omega
  | pair l r ihl ihr =>
      have h1 := ihl k
      have h2 := ihr k
      have e1 : ((occCount k l : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg l) : Int) - (tsize l : Int) := by
        rw [h1]; omega
      have e2 : ((occCount k r : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg r) : Int) - (tsize r : Int) := by
        rw [h2]; omega
      have hd : ((occCount k l + occCount k r : Nat) : Int) * ((tsize arg : Int) - 1)
          = (occCount k l : Int) * ((tsize arg : Int) - 1)
            + (occCount k r : Int) * ((tsize arg : Int) - 1) := by
        rw [Int.natCast_add, Int.add_mul]
      simp only [substG, occCount, tsize]
      rw [hd, e1, e2]
      omega
  | lete t b iht ihb =>
      have h1 := iht k
      have h2 := ihb (k + 2)
      have e1 : ((occCount k t : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg t) : Int) - (tsize t : Int) := by
        rw [h1]; omega
      have e2 : ((occCount (k + 2) b : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG (k + 2) m arg b) : Int) - (tsize b : Int) := by
        rw [h2]; omega
      have hd : ((occCount k t + occCount (k + 2) b : Nat) : Int) * ((tsize arg : Int) - 1)
          = (occCount k t : Int) * ((tsize arg : Int) - 1)
            + (occCount (k + 2) b : Int) * ((tsize arg : Int) - 1) := by
        rw [Int.natCast_add, Int.add_mul]
      simp only [substG, occCount, tsize]
      rw [hd, e1, e2]
      omega
  | unit => simp [substG, occCount, tsize]
  | next t ih =>
      have h := ih k
      have e : ((occCount k t : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg t) : Int) - (tsize t : Int) := by
        rw [h]; omega
      simp only [substG, occCount, tsize]
      rw [e]
      omega
  | fix t ih =>
      have h := ih k
      have e : ((occCount k t : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg t) : Int) - (tsize t : Int) := by
        rw [h]; omega
      simp only [substG, occCount, tsize]
      rw [e]
      omega
  | cons h t ihh iht =>
      have h1 := ihh k
      have h2 := iht k
      have e1 : ((occCount k h : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg h) : Int) - (tsize h : Int) := by
        rw [h1]; omega
      have e2 : ((occCount k t : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg t) : Int) - (tsize t : Int) := by
        rw [h2]; omega
      have hd : ((occCount k h + occCount k t : Nat) : Int) * ((tsize arg : Int) - 1)
          = (occCount k h : Int) * ((tsize arg : Int) - 1)
            + (occCount k t : Int) * ((tsize arg : Int) - 1) := by
        rw [Int.natCast_add, Int.add_mul]
      simp only [substG, occCount, tsize]
      rw [hd, e1, e2]
      omega
  | nil => simp [substG, occCount, tsize]
  | snoc t u iht ihu =>
      have h1 := iht k
      have h2 := ihu k
      have e1 : ((occCount k t : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg t) : Int) - (tsize t : Int) := by
        rw [h1]; omega
      have e2 : ((occCount k u : Nat) : Int) * ((tsize arg : Int) - 1)
          = (tsize (substG k m arg u) : Int) - (tsize u : Int) := by
        rw [h2]; omega
      have hd : ((occCount k t + occCount k u : Nat) : Int) * ((tsize arg : Int) - 1)
          = (occCount k t : Int) * ((tsize arg : Int) - 1)
            + (occCount k u : Int) * ((tsize arg : Int) - 1) := by
        rw [Int.natCast_add, Int.add_mul]
      simp only [substG, occCount, tsize]
      rw [hd, e1, e2]
      omega
  | gen => simp [substG, occCount, tsize]
  | red => simp [substG, occCount, tsize]
  | obj => simp [substG, occCount, tsize]
  | terminate => simp [substG, occCount, tsize]

/-- Terms are nonempty. -/
theorem tsize_pos : ∀ t : Term, 0 < tsize t := by
  intro t
  cases t <;> simp only [tsize] <;> omega

/-- THE LINEAR SHRINK: substituting at a binder with exactly ONE
occurrence strictly decreases the size of the redex — the engine of
linear-beta's size termination. -/
theorem linear_redex_shrink (a : Ty) {body arg : Term}
    (hocc : occCount 0 body = 1) :
    tsize (substG 0 0 arg body) + 2 < tsize (Term.app (Term.lam a body) arg) := by
  have h := substG_tsize 0 0 arg body
  rw [hocc] at h
  have harg : (0 : Int) < (tsize arg : Int) := by exact_mod_cast tsize_pos arg
  have hgoal : ((tsize (substG 0 0 arg body) + 2 : Nat) : Int)
      < ((tsize (Term.app (Term.lam a body) arg) : Nat) : Int) := by
    simp only [Term.app, Term.lam, tsize]
    omega
  exact_mod_cast hgoal

end Dcare
