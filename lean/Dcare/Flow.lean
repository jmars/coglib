import Dcare.Typing
import Dcare.ListAux
import Dcare.Count

/-!
# Token flow: conservation with owed leaves

The resource accounting behind the remaining non-derivability theorems.
Inhabitation models cannot see exact-use facts (insight ledger #22 — a
barren context makes every sequent vacuously valid), so the count moves
to the derivation, as with `uses`:

- `leaves τ` — content tokens the type CARRIES. Arrows count the CODOMAIN
  only: a domain content is a demand, not a held token.
- `genFire h` — coalgebra firings: each gen-application can mint one
  content token from a knower.
- `sink h` — tokens archived into the opaque sinks: each `snoc` (trace)
  and `cons` (stream) firing swallows one content token.
- `owed h` — lam-bound domain leaves not yet discharged, plus
  contraction's duplicate. Conservative: application drops the demand
  without crediting the argument's supply.

**conservation**: `leaves τ + sink h ≤ ctxLeaves Γ + genFire h + owed h`.
Every rule balances (the app-case drops the domain demand; the lete-case
cancels the tensor pair against the body's extended context).

The two sharp lemmas that finish `no_contraction_content` and
`no_vanishing` (routes, not yet proven):
- KNOWER-SUPPLY: every gen-firing's knower traces to a knower-typed
  hypothesis of Γ; binders only defer the demand to an application,
  whose argument recurses. `no_knower_at_knowerfree` below is the closed
  piece (via the lush model: everything true except the knower).
- TRACE-REACH: a trace-typed sub-result must reach the conclusion's type
  — traces have no consumer, so a sink token whose carrier cannot reach
  the conclusion makes the derivation unfinishable.
-/

namespace Dcare

/-- Content tokens a type carries; arrows count codomain only. -/
def leaves : Ty → Nat
  | .content => 1
  | .knower | .knowledge | .value | .unit | .trace | .stream => 0
  | .later a => leaves a
  | .tensor a b => leaves a + leaves b
  | .arrow _ b => leaves b

def ctxLeaves : List Ty → Nat
  | [] => 0
  | a :: Γ => leaves a + ctxLeaves Γ

theorem ctxLeaves_append (Γ Δ : List Ty) :
    ctxLeaves (Γ ++ Δ) = ctxLeaves Γ + ctxLeaves Δ := by
  induction Γ with
  | nil => simp [ctxLeaves]
  | cons _ Γ' ih => rw [List.cons_append, ctxLeaves, ctxLeaves, ih]; omega

/-- Coalgebra firings in a derivation. -/
def genFire : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, Typed.gen => 1
  | _, _, _, @Typed.lam _ _ _ _ h => genFire h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => genFire hf + genFire ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => genFire hl + genFire hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => genFire ht + genFire hb
  | _, _, _, @Typed.next _ _ _ h => genFire h
  | _, _, _, @Typed.fix _ _ _ _ h => genFire h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => genFire hc + genFire ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => genFire ht + genFire hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => genFire h
  | _, _, _, @Typed.weak _ _ _ _ _ h => genFire h
  | _, _, _, _ => 0

/-- Tokens archived into the opaque sinks (snoc → trace, cons → stream). -/
def sink : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, @Typed.lam _ _ _ _ h => sink h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => sink hf + sink ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => sink hl + sink hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => sink ht + sink hb
  | _, _, _, @Typed.next _ _ _ h => sink h
  | _, _, _, @Typed.fix _ _ _ _ h => sink h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => sink hc + sink ht + 1
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => sink ht + sink hu + 1
  | _, _, _, @Typed.contr _ _ _ _ _ h => sink h
  | _, _, _, @Typed.weak _ _ _ _ _ h => sink h
  | _, _, _, _ => 0

/-- Lam-bound domain leaves not yet discharged; contraction's duplicate. -/
def owed : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, @Typed.lam _ a _ _ h => owed h + leaves a
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => owed hf + owed ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => owed hl + owed hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => owed ht + owed hb
  | _, _, _, @Typed.next _ _ _ h => owed h
  | _, _, _, @Typed.fix _ _ _ _ h => owed h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => owed hc + owed ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => owed ht + owed hu
  | _, _, _, @Typed.contr _ k _ _ _ h => owed h + leaves k
  | _, _, _, @Typed.weak _ _ _ _ _ h => owed h
  | _, _, _, _ => 0

/-- The resource account balances: what the conclusion carries plus what
was archived never exceeds what the context supplied, the coalgebra
minted, and the undischarged borrowings. -/
theorem conservation : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    leaves τ + sink h ≤ ctxLeaves Γ + genFire h + owed h := by
  intro Γ t τ h
  induction h with
  | var => simp only [sink, genFire, owed, ctxLeaves]; omega
  | lam h ih =>
      simp only [sink, genFire, owed, ctxLeaves, leaves] at ih ⊢
      omega
  | app _ _ hs ihf iha =>
      rename_i _ Γ Δ _ _ _ _ _
      subst hs
      rw [ctxLeaves_append]
      simp only [sink, genFire, owed, leaves] at ihf iha ⊢
      omega
  | pair _ _ hs ihl ihr =>
      rename_i _ Γ Δ _ _ _ _ _
      subst hs
      rw [ctxLeaves_append]
      simp only [sink, genFire, owed, leaves] at ihl ihr ⊢
      omega
  | lete _ _ hs iht ihb =>
      rename_i _ Γ₁ Γ₂ _ _ _ _ _ _
      subst hs
      rw [ctxLeaves_append]
      simp only [sink, genFire, owed, ctxLeaves, leaves] at iht ihb ⊢
      omega
  | unit => simp only [sink, genFire, owed, leaves, ctxLeaves]; omega
  | next _ ih =>
      simp only [sink, genFire, owed, leaves, leaves] at ih ⊢
      omega
  | fix _ _ ih =>
      simp only [sink, genFire, owed, leaves, leaves] at ih ⊢
      omega
  | cons _ _ hs ihc iht =>
      rename_i _ Γ Δ _ _ _
      subst hs
      rw [ctxLeaves_append]
      simp only [sink, genFire, owed, leaves] at ihc iht ⊢
      omega
  | nil => simp only [sink, genFire, owed, leaves, ctxLeaves]; omega
  | snoc _ _ hs iht ihu =>
      rename_i _ Γ Δ _ _ _
      subst hs
      rw [ctxLeaves_append]
      simp only [sink, genFire, owed, leaves] at iht ihu ⊢
      omega
  | gen => simp only [sink, genFire, owed, leaves, ctxLeaves]; omega
  | red => simp only [sink, genFire, owed, leaves, ctxLeaves]; omega
  | obj => simp only [sink, genFire, owed, leaves, ctxLeaves]; omega
  | terminate => simp only [sink, genFire, owed, leaves, ctxLeaves]; omega
  | contr _ _ ih =>
      simp only [sink, genFire, owed, ctxLeaves, leaves] at ih ⊢
      omega
  | weak _ _ ih =>
      simp only [sink, genFire, owed, ctxLeaves, leaves] at ih ⊢
      omega

/-! ## The lush model: no knower at knower-free contexts -/

/-- The lush world: everything is true except the knower. -/
def interpL : Ty → Prop
  | .knower => False
  | .tensor a b => interpL a ∧ interpL b
  | .arrow a b => interpL a → interpL b
  | _ => True

def interpLCtx : List Ty → Prop
  | [] => True
  | a :: Γ => interpL a ∧ interpLCtx Γ

theorem interpL_of_knowerfree : ∀ {a : Ty}, KnowerFree a → interpL a
  | .content, _ => True.intro
  | .knowledge, _ => True.intro
  | .value, _ => True.intro
  | .trace, _ => True.intro
  | .stream, _ => True.intro
  | .unit, _ => True.intro
  | .later _, _ => True.intro
  | .tensor _ _, KnowerFree.tensor hl hr =>
      ⟨interpL_of_knowerfree hl, interpL_of_knowerfree hr⟩
  | .arrow _ _, KnowerFree.arrow _ hr =>
      fun _ => interpL_of_knowerfree hr

def KnowerFreeCtx (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (a : Ty), Γ[i]? = some a → KnowerFree a

theorem interpLCtx_knowerfree {Γ : List Ty} (h : KnowerFreeCtx Γ) : interpLCtx Γ := by
  induction Γ with
  | nil => exact True.intro
  | cons a Γ' ih =>
      have ha := interpL_of_knowerfree (h 0 a List.get?_zero_cons')
      have h' : KnowerFreeCtx Γ' := fun i x hi =>
        h (i + 1) x (by rw [List.get?_succ_cons']; exact hi)
      exact ⟨ha, ih h'⟩

theorem interpL_append : ∀ (Γ₁ Δ : List Ty),
    interpLCtx (Γ₁ ++ Δ) → interpLCtx Γ₁ ∧ interpLCtx Δ
  | [], _, x => ⟨True.intro, x⟩
  | _ :: Γ₁, Δ, x =>
      ⟨⟨x.1, (interpL_append Γ₁ Δ x.2).1⟩, (interpL_append Γ₁ Δ x.2).2⟩

theorem interpL_append' {E Γ Δ : List Ty} (hs : Γ ++ Δ = E) :
    interpLCtx E → interpLCtx Γ ∧ interpLCtx Δ := by
  subst hs
  exact interpL_append Γ Δ

/-- Lush soundness. -/
theorem soundL : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    interpLCtx Γ → interpL τ := by
  intro Γ t τ h
  induction h with
  | var => intro γ; exact γ.1
  | lam _ ih => intro γ x; exact ih ⟨x, γ⟩
  | app _ _ hs ihf iha =>
      intro γ
      exact ihf (interpL_append' hs γ).1 (iha (interpL_append' hs γ).2)
  | pair _ _ hs ihl ihr =>
      intro γ
      exact ⟨ihl (interpL_append' hs γ).1, ihr (interpL_append' hs γ).2⟩
  | lete _ _ hs iht ihb =>
      intro γ
      exact ihb ⟨(iht (interpL_append' hs γ).1).2,
        ⟨(iht (interpL_append' hs γ).1).1, (interpL_append' hs γ).2⟩⟩
  | unit => intro _; exact True.intro
  | next _ _ => intro _; exact True.intro
  | fix _ _ ih => intro γ; exact ih γ True.intro
  | cons _ _ hs _ _ => intro _; exact True.intro
  | nil => intro _; exact True.intro
  | snoc _ _ hs _ _ => intro _; exact True.intro
  | gen => intro _ k; exact k.elim
  | red => intro _ s; exact s
  | obj => intro _ s; exact s
  | terminate => intro _ _; exact True.intro
  | contr _ _ ih => intro p; exact ih ⟨p.1, p⟩
  | weak _ _ ih => intro p; exact ih p.2

/-- No knower-typed term exists at a knower-free context — the closed
piece of the knower-supply lemma: a gen-firing inside a knower-free
context derivation cannot get its knower from the context. -/
theorem no_knower_at_knowerfree {Δ : List Ty} {x : Term}
    (h : Typed Δ x Ty.knower) (hf : KnowerFreeCtx Δ) : False :=
  (soundL h (interpLCtx_knowerfree hf)).elim

/-- Non-linear types carry no content tokens: linearity and leaves track
the same content-occurrence. (The one asymmetry — arrow domains make a
type linear without carrying a token — does not affect the claim:
non-linear means both sides non-linear.) -/
theorem nonlinear_leaves : ∀ (a : Ty), a.isLinear = false → leaves a = 0 := by
  intro a
  cases a with
  | content => intro h; exact Bool.noConfusion h
  | knower => intro _; rfl
  | knowledge => intro _; rfl
  | value => intro _; rfl
  | unit => intro _; rfl
  | trace => intro _; rfl
  | stream => intro _; rfl
  | later a' => intro h; exact nonlinear_leaves a' h
  | tensor a' b' =>
      intro h
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using h)
      rw [leaves, nonlinear_leaves a' h'.1, nonlinear_leaves b' h'.2]
  | arrow a' b' =>
      intro h
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using h)
      rw [leaves, nonlinear_leaves b' h'.2]

/-- Total content-leaves of all var-nodes in a derivation (each var-spend
counted at its node's type). -/
def varLeaves : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, @Typed.var a => leaves a
  | _, _, _, @Typed.lam _ _ _ _ h => varLeaves h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => varLeaves hf + varLeaves ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => varLeaves hl + varLeaves hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => varLeaves ht + varLeaves hb
  | _, _, _, @Typed.next _ _ _ h => varLeaves h
  | _, _, _, @Typed.fix _ _ _ _ h => varLeaves h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => varLeaves hc + varLeaves ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => varLeaves ht + varLeaves hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => varLeaves h
  | _, _, _, @Typed.weak _ _ _ _ _ h => varLeaves h
  | _, _, _, _ => 0

/-- UPPER FLOW: every content token the conclusion carries traces to a
var-spend, a borrowing (lam-annotation or contraction duplicate), or a
coalgebra mint. The inequality is deliberately loose — application drops
the argument's whole account — which is exactly why the remaining two
theorems need the discharge/surfacing lemmas on top. -/
theorem leaves_bound : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    leaves τ ≤ varLeaves h + owed h + genFire h := by
  intro Γ t τ h
  induction h with
  | var => simp only [varLeaves, owed, genFire]; omega
  | lam _ ih => simp only [varLeaves, owed, genFire, leaves] at ih ⊢; omega
  | app _ _ _ ihf iha =>
      rename_i _ _ _ b _ _ _ _
      simp only [varLeaves, owed, genFire, leaves] at ihf iha ⊢
      omega
  | pair _ _ _ ihl ihr =>
      rename_i _ _ _ a b _ _ _
      simp only [varLeaves, owed, genFire, leaves] at ihl ihr ⊢
      omega
  | lete _ _ _ iht ihb =>
      rename_i _ _ _ a b c _ _ _
      simp only [varLeaves, owed, genFire, leaves] at iht ihb ⊢
      omega
  | unit => simp only [varLeaves, owed, genFire, leaves]; omega
  | next _ ih => simp only [varLeaves, owed, genFire, leaves] at ih ⊢; omega
  | fix _ _ ih => simp only [varLeaves, owed, genFire, leaves] at ih ⊢; omega
  | cons _ _ _ _ _ => simp only [varLeaves, owed, genFire, leaves]; omega
  | nil => simp only [varLeaves, owed, genFire, leaves]; omega
  | snoc _ _ _ _ _ => simp only [varLeaves, owed, genFire, leaves]; omega
  | gen => simp only [varLeaves, owed, genFire, leaves]; omega
  | red => simp only [varLeaves, owed, genFire, leaves]; omega
  | obj => simp only [varLeaves, owed, genFire, leaves]; omega
  | terminate => simp only [varLeaves, owed, genFire, leaves]; omega
  | contr _ _ ih => simp only [varLeaves, owed, genFire] at ih ⊢; omega
  | weak _ _ ih => simp only [varLeaves, owed, genFire] at ih ⊢; omega

/-! ## Knower-need propagation -/

/-- Knower-NEED: the type carries a knower-demand that its context must
fund. Arrows count CODOMAINS only, and only when the domain itself needs
nothing — `arrow knower knower` needs NOTHING (its need is its
argument's business; the identity does not borrow from its context). The
conjunction is what makes the propagation lemma true. -/
def NeedsK : Ty → Prop
  | .knower => True
  | .tensor a b => NeedsK a ∨ NeedsK b
  | .arrow a b => NeedsK b ∧ ¬ NeedsK a
  | _ => False

theorem kprop : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    NeedsK τ → ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ NeedsK b
  | _, _, _, Typed.var, hK => ⟨0, _, List.get?_zero_cons', hK⟩
  | _, _, _, @Typed.lam Γ a b _ h, ⟨hb, hna⟩ => by
      have hk := kprop h hb
      match hk with
      | ⟨0, b', hpos, hneed⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact (hna hneed).elim
      | ⟨n + 1, b', hpos, hneed⟩ =>
          rw [List.get?_succ_cons'] at hpos
          exact ⟨n, b', hpos, hneed⟩
  | _, _, _, @Typed.app E Γ Δ a b fn arg hf ha hs, hK => by
      by_cases hx : NeedsK a
      · obtain ⟨j, b', hpos, hneed⟩ := kprop ha hx
        refine ⟨Γ.length + j, b', ?_, hneed⟩
        rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
          Nat.add_sub_cancel_left]
        exact hpos
      · obtain ⟨i, b', hpos, hneed⟩ := kprop hf ⟨hK, hx⟩
        refine ⟨i, b', ?_, hneed⟩
        have hlt : i < Γ.length := List.get?_some_lt hpos
        rw [← hs, List.get?_append_lt hlt]
        exact hpos
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hK => by
      rcases hK with hK | hK
      · obtain ⟨i, b', hpos, hneed⟩ := kprop hl hK
        refine ⟨i, b', ?_, hneed⟩
        have hlt : i < Γ.length := List.get?_some_lt hpos
        rw [← hs, List.get?_append_lt hlt]
        exact hpos
      · obtain ⟨j, b', hpos, hneed⟩ := kprop hr hK
        refine ⟨Γ.length + j, b', ?_, hneed⟩
        rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
          Nat.add_sub_cancel_left]
        exact hpos
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hK => by
      have hk := kprop hb hK
      match hk with
      | ⟨0, b', hpos, hneed⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          obtain ⟨i, b₂, hpos₂, hneed₂⟩ := kprop ht (Or.inr hneed)
          have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
          refine ⟨i, b₂, ?_, hneed₂⟩
          rw [← hs, List.get?_append_lt hlt]
          exact hpos₂
      | ⟨1, b', hpos, hneed⟩ =>
          rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          obtain ⟨i, b₂, hpos₂, hneed₂⟩ := kprop ht (Or.inl hneed)
          have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
          refine ⟨i, b₂, ?_, hneed₂⟩
          rw [← hs, List.get?_append_lt hlt]
          exact hpos₂
      | ⟨m + 2, b', hpos, hneed⟩ =>
          rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
          refine ⟨Γ₁.length + m, b', ?_, hneed⟩
          rw [← hs, List.get?_append_ge (Nat.le_add_right Γ₁.length m),
            Nat.add_sub_cancel_left]
          exact hpos
  | _, _, _, Typed.unit, hK => False.elim hK
  | _, _, _, @Typed.next _ _ _ _, hK => False.elim hK
  | _, _, _, @Typed.fix _ _ _ _ h, hK => kprop h ⟨hK, fun hf => hf⟩
  | _, _, _, @Typed.cons _ _ _ _ _ _ _ _, hK => False.elim hK
  | _, _, _, Typed.nil, hK => False.elim hK
  | _, _, _, @Typed.snoc _ _ _ _ _ _ _ _, hK => False.elim hK
  | _, _, _, Typed.gen, ⟨hb, hna⟩ => (hna True.intro).elim
  | _, _, _, Typed.red, ⟨hb, _⟩ => False.elim hb
  | _, _, _, Typed.obj, ⟨hb, _⟩ => False.elim hb
  | _, _, _, Typed.terminate, ⟨hb, _⟩ => False.elim hb
  | _, _, _, @Typed.contr Γ k t τ _ h, hK => by
      have hk := kprop h hK
      match hk with
      | ⟨0, b', hpos, hneed⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact ⟨0, _, List.get?_zero_cons', hneed⟩
      | ⟨1, b', hpos, hneed⟩ =>
          rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact ⟨0, _, List.get?_zero_cons', hneed⟩
      | ⟨m + 2, b', hpos, hneed⟩ =>
          rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
          exact ⟨m + 1, b', by rw [List.get?_succ_cons']; exact hpos, hneed⟩
  | _, _, _, @Typed.weak Γ k t τ _ h, hK => by
      obtain ⟨i, b', hpos, hneed⟩ := kprop h hK
      exact ⟨i + 1, b', by rw [List.get?_succ_cons']; exact hpos, hneed⟩


/-! ## Content-surfacing: net flow over the integers -/

/-- Net content-flow of a type. Arrows subtract their DOMAIN: a function
owes its codomain's tokens and is owed its domain's — so application
DISCHARGES the demand automatically in the arithmetic (see netprop_core). -/
def net : Ty → Int
  | .content => 1
  | .knower | .knowledge | .value | .unit | .trace | .stream => 0
  | .later a => net a
  | .tensor a b => net a + net b
  | .arrow a b => net b - net a

def ctxNet : List Ty → Int
  | [] => 0
  | a :: Γ => net a + ctxNet Γ

theorem ctxNet_append (Γ Δ : List Ty) :
    ctxNet (Γ ++ Δ) = ctxNet Γ + ctxNet Δ := by
  induction Γ with
  | nil => simp [ctxNet]
  | cons _ Γ' ih => rw [List.cons_append, ctxNet, ctxNet, ih]; omega

/-- Nodes outside the multiplicative core (var/lam/app/pair/lete/unit/
next): gen/red/obj/terminate/fix/cons/snoc/contr/weak. -/
def coreCount : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, @Typed.gen => 1
  | _, _, _, @Typed.red => 1
  | _, _, _, @Typed.obj => 1
  | _, _, _, @Typed.terminate => 1
  | _, _, _, @Typed.fix _ _ _ _ _ => 1
  | _, _, _, @Typed.cons _ _ _ _ _ _ _ _ => 1
  | _, _, _, @Typed.snoc _ _ _ _ _ _ _ _ => 1
  | _, _, _, @Typed.contr _ _ _ _ _ _ => 1
  | _, _, _, @Typed.weak _ _ _ _ _ _ => 1
  | _, _, _, @Typed.lam _ _ _ _ h => coreCount h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => coreCount hf + coreCount ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => coreCount hl + coreCount hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => coreCount ht + coreCount hb
  | _, _, _, @Typed.next _ _ _ h => coreCount h
  | _, _, _, _ => 0

/-- NET FLOW, core fragment: in the multiplicative core, the conclusion's
net content never exceeds the context's. The app-case is the discharge:
the function's domain-demand is paid by the argument's account in the
integer arithmetic; the lam-case is the borrow, cancelled by the same
subtraction. -/

theorem netprop_core : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    coreCount h = 0 → net τ ≤ ctxNet Γ := by
  intro Γ t τ h
  induction h with
  | var => intro _; simp only [net, ctxNet]; omega
  | lam _ ih =>
      intro hc
      simp only [coreCount] at hc
      have := ih hc
      simp only [net, ctxNet] at ⊢ this
      omega
  | app _ _ hs ihf iha =>
      intro hc
      simp only [coreCount] at hc
      have h1 := ihf (by omega)
      have h2 := iha (by omega)
      subst hs
      rw [ctxNet_append]
      rename_i _ _ _ X _ _ _ _
      simp only [net] at h1 ⊢
      omega
  | pair _ _ hs ihl ihr =>
      intro hc
      simp only [coreCount] at hc
      have h1 := ihl (by omega)
      have h2 := ihr (by omega)
      subst hs
      rw [ctxNet_append]
      simp only [net] at h1 h2 ⊢
      omega
  | lete _ _ hs iht ihb =>
      intro hc
      simp only [coreCount] at hc
      have h1 := iht (by omega)
      have h2 := ihb (by omega)
      subst hs
      rw [ctxNet_append]
      rename_i _ _ _ a b _ _ _ _
      simp only [net, ctxNet] at h1 h2 ⊢
      omega
  | unit => intro _; simp only [net, ctxNet]; omega
  | next _ ih =>
      intro hc
      simp only [coreCount] at hc
      simp only [net] at ih ⊢
      exact ih hc
  | fix _ _ _ => intro hc; simp only [coreCount] at hc; omega
  | cons _ _ _ _ _ => intro hc; simp only [coreCount] at hc; omega
  | nil => intro _; simp only [net, ctxNet]; omega
  | snoc _ _ _ _ _ => intro hc; simp only [coreCount] at hc; omega
  | gen => intro hc; simp only [coreCount] at hc; omega
  | red => intro hc; simp only [coreCount] at hc; omega
  | obj => intro hc; simp only [coreCount] at hc; omega
  | terminate => intro hc; simp only [coreCount] at hc; omega
  | contr _ _ _ => intro hc; simp only [coreCount] at hc; omega
  | weak _ _ _ => intro hc; simp only [coreCount] at hc; omega

/-- NO CONTRACTION, core fragment (PROVEN): in the multiplicative core,
one content hypothesis cannot be spent as two — the integer flow closes
it: `net (C ⊗ C) = 2 > 1 = ctxNet [content]`. -/
theorem no_contraction_core {t : Term}
    (h : Typed [Ty.content] t (.tensor Ty.content Ty.content))
    (hc : coreCount h = 0) : False := by
  have := netprop_core h hc
  simp only [net, ctxNet] at this
  omega

/-- Non-linear types have net EXACTLY zero — the net-analogue of
nonlinear_leaves. The induction closes because an arrow with a
content-domain is LINEAR (the gate excludes it), so non-linear arrows
have non-linear domains, whose net is zero by induction. -/
theorem nonlinear_net : ∀ (a : Ty), a.isLinear = false → net a = 0 := by
  intro a
  cases a with
  | content => intro h; exact Bool.noConfusion h
  | knower => intro _; rfl
  | knowledge => intro _; rfl
  | value => intro _; rfl
  | unit => intro _; rfl
  | trace => intro _; rfl
  | stream => intro _; rfl
  | later a' => intro h; exact nonlinear_net a' h
  | tensor a' b' =>
      intro h
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using h)
      rw [net, nonlinear_net a' h'.1, nonlinear_net b' h'.2]; rfl
  | arrow a' b' =>
      intro h
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using h)
      rw [net, nonlinear_net b' h'.2, nonlinear_net a' h'.1]; rfl

def fixCount : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, @Typed.fix _ _ _ _ h => 1 + fixCount h
  | _, _, _, @Typed.lam _ _ _ _ h => fixCount h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => fixCount hf + fixCount ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => fixCount hl + fixCount hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => fixCount ht + fixCount hb
  | _, _, _, @Typed.next _ _ _ h => fixCount h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => fixCount hc + fixCount ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => fixCount ht + fixCount hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => fixCount h
  | _, _, _, @Typed.weak _ _ _ _ _ h => fixCount h
  | _, _, _, _ => 0

/-- ITEM 1+3: full net flow for every rule except fix. genFire is the
NODE count — inert gens legitimately carry net into conclusions through
their arrow types, so nodes (not fires) are the right supply-side count;
contr/weak close by nonlinear_net (the gated type has net zero). -/
theorem netprop_nofix : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    fixCount h = 0 → net τ ≤ ctxNet Γ + (genFire h : Int) := by
  intro Γ t τ h
  induction h with
  | var => intro _; simp only [net, ctxNet, genFire]; omega
  | lam _ ih =>
      intro hf
      simp only [fixCount] at hf
      have hI := ih hf
      simp only [net, ctxNet, genFire] at hI ⊢
      omega
  | app _ _ hs ihf iha =>
      intro hf
      simp only [fixCount] at hf
      have h1 := ihf (by omega)
      have h2 := iha (by omega)
      subst hs
      rw [ctxNet_append]
      rename_i _ _ _ X _ _ _ _
      simp only [net, genFire] at h1 h2 ⊢
      omega
  | pair _ _ hs ihl ihr =>
      intro hf
      simp only [fixCount] at hf
      have h1 := ihl (by omega)
      have h2 := ihr (by omega)
      subst hs
      rw [ctxNet_append]
      simp only [net, genFire] at h1 h2 ⊢
      omega
  | lete _ _ hs iht ihb =>
      intro hf
      simp only [fixCount] at hf
      have h1 := iht (by omega)
      have h2 := ihb (by omega)
      subst hs
      rw [ctxNet_append]
      rename_i _ _ _ a b _ _ _ _
      simp only [net, ctxNet, genFire] at h1 h2 ⊢
      omega
  | unit => intro _; simp only [net, ctxNet, genFire]; omega
  | next _ ih =>
      intro hf
      simp only [fixCount] at hf
      simp only [net] at ih ⊢
      exact ih hf
  | fix _ _ _ => intro hf; simp only [fixCount] at hf; omega
  | cons _ _ hs ihc iht =>
      intro hf
      simp only [fixCount] at hf
      have h1 := ihc (by omega)
      have h2 := iht (by omega)
      subst hs
      rw [ctxNet_append]
      simp only [net, genFire] at h1 h2 ⊢
      omega
  | nil => intro _; simp only [net, ctxNet, genFire]; omega
  | snoc _ _ hs iht ihu =>
      intro hf
      simp only [fixCount] at hf
      have h1 := iht (by omega)
      have h2 := ihu (by omega)
      subst hs
      rw [ctxNet_append]
      simp only [net, genFire] at h1 h2 ⊢
      omega
  | gen => intro _; simp only [net, ctxNet, genFire]; omega
  | red => intro _; simp only [net, ctxNet, genFire]; omega
  | obj => intro _; simp only [net, ctxNet, genFire]; omega
  | terminate => intro _; simp only [net, ctxNet, genFire]; omega
  | contr hk h ih =>
      intro hf
      simp only [fixCount] at hf
      have hI := ih hf
      have hk0 := nonlinear_net _ hk
      simp only [ctxNet, genFire] at hI ⊢
      omega
  | weak hk h ih =>
      intro hf
      simp only [fixCount] at hf
      have hI := ih hf
      have hk0 := nonlinear_net _ hk
      simp only [ctxNet, genFire] at hI ⊢
      omega


/-- NO CONTRACTION, fix-free and gen-free (PROVEN — strictly broader than
the core fragment: the sinks and the gated structural rules included;
only fix and the coalgebra excluded). The full version additionally
needs the fires-vs-nodes distinction: a bare gen-node's net reaches a
C⊗C-conclusion only by firing, and firing requires a knower-term at a
[content]-rooted site (KPROP) — the reach-path analysis, documented. -/
theorem no_contraction_nogen {t : Term}
    (h : Typed [Ty.content] t (.tensor Ty.content Ty.content))
    (hf : fixCount h = 0) (hg : genFire h = 0) : False := by
  have hn := netprop_nofix h hf
  have hg0 : (genFire h : Int) = 0 := by exact Int.ofNat_eq_zero.mpr hg
  rw [hg0] at hn
  simp only [net, ctxNet] at hn
  omega


/-! ## The spend equality (item 4): net τ = Σ uses·net -/

/-- Net-weighted spend over a context, from a base position. -/
def spendNetFrom (base : Nat) : List Ty → (Nat → Nat) → Int
  | [], _ => 0
  | a :: Γ, u => (u base : Int) * net a + spendNetFrom (base + 1) Γ u

def spendNet {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ) : Int :=
  spendNetFrom 0 Γ (uses h)

theorem spendNetFrom_congr : ∀ (Γ : List Ty) (u v : Nat → Nat) (b : Nat),
    (∀ i, b ≤ i → i < b + Γ.length → u i = v i) →
    spendNetFrom b Γ u = spendNetFrom b Γ v
  | [], _, _, _, _ => rfl
  | a :: Γ', u, v, b, huv => by
      have hlen : (a :: Γ').length = Γ'.length + 1 := rfl
      have h1 : u b = v b := huv b (Nat.le_refl b) (by rw [hlen]; omega)
      have h2 : spendNetFrom (b + 1) Γ' u = spendNetFrom (b + 1) Γ' v :=
        spendNetFrom_congr Γ' u v (b + 1) fun i hi hii =>
          huv i (Nat.le_trans (Nat.le_succ b) hi) (by show i < b + (Γ'.length + 1); omega)
      rw [spendNetFrom, spendNetFrom, h1, h2]

theorem spendNetFrom_append : ∀ (Γ₁ Δ : List Ty) (u : Nat → Nat) (b : Nat),
    spendNetFrom b (Γ₁ ++ Δ) u = spendNetFrom b Γ₁ u + spendNetFrom (b + Γ₁.length) Δ u
  | [], _, _, _ => by simp [spendNetFrom]
  | a :: Γ', Δ, u, b => by
      rw [List.cons_append, spendNetFrom, spendNetFrom,
        spendNetFrom_append Γ' Δ u (b + 1)]
      have hidx : b + (a :: Γ').length = b + 1 + Γ'.length := by
        simp only [List.length_cons]; omega
      rw [hidx]
      omega

theorem spendNetFrom_shift : ∀ (Γ : List Ty) (u : Nat → Nat) (b n : Nat),
    spendNetFrom (b + n) Γ u = spendNetFrom b Γ (fun i => u (i + n))
  | [], _, _, _ => rfl
  | _ :: Γ', u, b, n => by
      rw [spendNetFrom, spendNetFrom]
      have hbr : b + n + 1 = b + 1 + n := by omega
      rw [hbr, spendNetFrom_shift Γ' u (b + 1) n]
/-- Nodes that break the net EQUALITY: gen (mints), fix (unroll
accounting), cons/snoc (destroy into sinks). -/
def pureCount : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, Typed.gen => 1
  | _, _, _, @Typed.fix _ _ _ _ h => 1 + pureCount h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => 1 + pureCount hc + pureCount ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => 1 + pureCount ht + pureCount hu
  | _, _, _, @Typed.lam _ _ _ _ h => pureCount h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => pureCount hf + pureCount ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => pureCount hl + pureCount hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => pureCount ht + pureCount hb
  | _, _, _, @Typed.next _ _ _ h => pureCount h
  | _, _, _, @Typed.red => 0
  | _, _, _, @Typed.obj => 0
  | _, _, _, @Typed.terminate => 0
  | _, _, _, @Typed.contr _ _ _ _ _ h => pureCount h
  | _, _, _, @Typed.weak _ _ _ _ _ h => pureCount h
  | _, _, _, _ => 0

/-- FUSION HELPER: at any hypothesis position, the net-weighted spend is
EXACT — linear positions are spent exactly once (single_linear_use),
non-linear positions have net exactly zero (nonlinear_net). -/
theorem binder_exact : ∀ (a : Ty) {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ)
    {i : Nat} (hpos : Γ[i]? = some a), (uses h i : Int) * net a = net a := by
  intro a Γ t τ h i hpos
  cases hlin : a.isLinear with
  | true =>
      have hu := single_linear_use h i a hpos hlin
      rw [hu]
      simp
  | false =>
      have h0 := nonlinear_net a hlin
      rw [h0, Int.mul_zero]
/-- Rebasing: two use-functions that agree at absolute positions give
the same spend over the same context. -/
theorem spendNetFrom_rebase : ∀ (Γ : List Ty) (v u : Nat → Nat) (b b' : Nat),
    (∀ i, v (b + i) = u (b' + i)) → spendNetFrom b Γ v = spendNetFrom b' Γ u
  | [], _, _, _, _, _ => rfl
  | _ :: Γ', v, u, b, b', hvu => by
      have h1 : v b = u b' := by
        have := hvu 0
        simpa [Nat.add_zero] using this
      have h2 : spendNetFrom (b + 1) Γ' v = spendNetFrom (b' + 1) Γ' u :=
        spendNetFrom_rebase Γ' v u (b + 1) (b' + 1) fun i =>
          by rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm 1 i]; exact hvu (i + 1)
      rw [spendNetFrom, spendNetFrom, h1, h2]
theorem netEq : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    pureCount h = 0 → net τ = spendNet h
  | _, _, _, Typed.var, _ => by
      simp only [spendNet, spendNetFrom, uses, net]
      simp
  | _, _, _, @Typed.lam Γ a b body h, hc => by
      have ih := netEq h (by simpa only [pureCount] using hc)
      have hb := binder_exact a h (List.get?_zero_cons')
      have hsplit : spendNet (Γ := a :: Γ) h
          = (uses h 0 : Int) * net a + spendNetFrom 1 Γ (uses h) := rfl
      rw [hsplit] at ih
      have hreb : spendNetFrom 0 Γ (uses (@Typed.lam Γ a b body h))
          = spendNetFrom 1 Γ (uses h) :=
        spendNetFrom_rebase Γ (uses (@Typed.lam Γ a b body h)) (uses h) 0 1
          fun i => by rw [Nat.zero_add, Nat.add_comm 1 i]; rfl
      show net (a.arrow b) = _
      simp only [spendNet, net]
      rw [hb] at ih
      clear hb
      rw [hreb]
      omega
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hc => by
      obtain ⟨hc1, hc2⟩ : pureCount hf = 0 ∧ pureCount ha = 0 := by
        simpa only [pureCount, Nat.add_eq_zero_iff] using hc
      have ihf := netEq hf hc1
      have iha := netEq ha hc2
      subst hs
      have h1 : spendNetFrom 0 Γ (uses (@Typed.app (Γ ++ Δ) Γ Δ X b fn arg hf ha rfl))
          = spendNetFrom 0 Γ (uses hf) :=
        spendNetFrom_congr Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hf i else uses ha (i - Γ.length)) = uses hf i
          rw [if_pos (by omega)]
      have h2 : spendNetFrom (0 + Γ.length) Δ (uses (@Typed.app (Γ ++ Δ) Γ Δ X b fn arg hf ha rfl))
          = spendNetFrom 0 Δ (uses ha) :=
        spendNetFrom_rebase Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hf (0 + Γ.length + i)
                else uses ha (0 + Γ.length + i - Γ.length)) = uses ha (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      simp only [spendNet] at ihf iha ⊢
      rw [spendNetFrom_append, h1, h2, ← ihf, ← iha]
      simp only [net]
      omega
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hc => by
      obtain ⟨hc1, hc2⟩ : pureCount hl = 0 ∧ pureCount hr = 0 := by
        simpa only [pureCount, Nat.add_eq_zero_iff] using hc
      have ihl := netEq hl hc1
      have ihr := netEq hr hc2
      subst hs
      have h1 : spendNetFrom 0 Γ (uses (@Typed.pair (Γ ++ Δ) Γ Δ a b l r hl hr rfl))
          = spendNetFrom 0 Γ (uses hl) :=
        spendNetFrom_congr Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hl i else uses hr (i - Γ.length)) = uses hl i
          rw [if_pos (by omega)]
      have h2 : spendNetFrom (0 + Γ.length) Δ (uses (@Typed.pair (Γ ++ Δ) Γ Δ a b l r hl hr rfl))
          = spendNetFrom 0 Δ (uses hr) :=
        spendNetFrom_rebase Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hl (0 + Γ.length + i)
                else uses hr (0 + Γ.length + i - Γ.length)) = uses hr (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      simp only [spendNet] at ihl ihr ⊢
      rw [spendNetFrom_append, h1, h2, ← ihl, ← ihr]
      simp only [net]
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hc => by
      obtain ⟨hc1, hc2⟩ : pureCount ht = 0 ∧ pureCount hb = 0 := by
        simpa only [pureCount, Nat.add_eq_zero_iff] using hc
      have iht := netEq ht hc1
      have ihb := netEq hb hc2
      have hb0 := binder_exact b hb (List.get?_zero_cons')
      have hb1 := binder_exact a hb (by rw [List.get?_succ_cons']; exact List.get?_zero_cons')
      have hsplit : spendNet (Γ := b :: a :: Γ₂) hb
          = (uses hb 0 : Int) * net b + ((uses hb 1 : Int) * net a
            + spendNetFrom 2 Γ₂ (uses hb)) := rfl
      rw [hsplit] at ihb
      rw [hb0, hb1] at ihb
      clear hb0 hb1
      subst hs
      have h1 : spendNetFrom 0 Γ₁ (uses (@Typed.lete (Γ₁ ++ Γ₂) Γ₁ Γ₂ a b c t body ht hb rfl))
          = spendNetFrom 0 Γ₁ (uses ht) :=
        spendNetFrom_congr Γ₁ _ _ 0 fun i _ hilt => by
          show (if i < Γ₁.length then uses ht i else uses hb (i - Γ₁.length + 2)) = uses ht i
          rw [if_pos (by omega)]
      have h2 : spendNetFrom (0 + Γ₁.length) Γ₂ (uses (@Typed.lete (Γ₁ ++ Γ₂) Γ₁ Γ₂ a b c t body ht hb rfl))
          = spendNetFrom 2 Γ₂ (uses hb) :=
        spendNetFrom_rebase Γ₂ _ _ (0 + Γ₁.length) 2 fun i => by
          show (if 0 + Γ₁.length + i < Γ₁.length then uses ht (0 + Γ₁.length + i)
                else uses hb (0 + Γ₁.length + i - Γ₁.length + 2)) = uses hb (2 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.add_comm 2 i]
      show net c = _
      simp only [spendNet]
      rw [spendNetFrom_append, h1, h2]
      simp only [spendNet] at iht
      simp only [net] at iht ihb ⊢
      omega
  | _, _, _, Typed.unit, _ => by simp only [net, spendNet, spendNetFrom]
  | _, _, _, @Typed.next Γ a t h, hc => by
      have ih := netEq h (by simpa only [pureCount] using hc)
      exact ih
  | _, _, _, Typed.nil, _ => by simp only [net, spendNet, spendNetFrom]
  | _, _, _, @Typed.red, _ => by
      simp only [net, spendNet, spendNetFrom, uses]
      omega
  | _, _, _, @Typed.obj, _ => by
      simp only [net, spendNet, spendNetFrom, uses]
      omega
  | _, _, _, @Typed.terminate, _ => by
      simp only [net, spendNet, spendNetFrom, uses]
      omega
  | _, _, _, @Typed.contr Γ k t τ hk h, hc => by
      have ih := netEq h (by simpa only [pureCount] using hc)
      have hk0 := nonlinear_net k hk
      have hsplitI : spendNet (Γ := k :: k :: Γ) h
          = (uses h 0 : Int) * net k + ((uses h 1 : Int) * net k
            + spendNetFrom 2 Γ (uses h)) := rfl
      rw [hsplitI, hk0] at ih
      simp only [Int.mul_zero, Int.add_zero, Int.zero_add] at ih
      have hreb : spendNetFrom (0 + 1) Γ (uses (@Typed.contr Γ k t τ hk h))
          = spendNetFrom 2 Γ (uses h) :=
        spendNetFrom_rebase Γ _ _ (0 + 1) 2 fun i => by
          have h1 : (1 + i : Nat) ≠ 0 := by omega
          simp only [uses, if_neg h1]
          congr 1
          omega
      show net τ = _
      rw [spendNet, spendNetFrom]
      rw [hreb, hk0]
      simp only [Int.mul_zero, Int.add_zero, Int.zero_add]
      exact ih
  | _, _, _, @Typed.weak Γ k t τ hk h, hc => by
      have ih := netEq h (by simpa only [pureCount] using hc)
      show net τ = _
      rw [spendNet, spendNetFrom]
      have hreb : spendNetFrom (0 + 1) Γ (uses (@Typed.weak Γ k t τ hk h))
          = spendNetFrom 0 Γ (uses h) :=
        spendNetFrom_rebase Γ _ _ (0 + 1) 0 fun i => by
          have h1 : (1 + i : Nat) ≠ 0 := by omega
          simp only [uses, if_neg h1, Nat.add_sub_cancel_left, Nat.zero_add]
      rw [hreb]
      have h0 : (uses (@Typed.weak Γ k t τ hk h) 0 : Int) = 0 := rfl
      rw [h0, Int.zero_mul, Int.zero_add]
      exact ih
  | _, _, _, @Typed.fix _ _ _ _ _, hc => by simp only [pureCount] at hc; omega
  | _, _, _, @Typed.gen, hc => by simp only [pureCount] at hc; omega
  | _, _, _, @Typed.cons _ _ _ _ _ _ _ _, hc => by simp only [pureCount] at hc; omega
  | _, _, _, @Typed.snoc _ _ _ _ _ _ _ _, hc => by simp only [pureCount] at hc; omega

/-- NO VANISHING, equality fragment (PROVEN): the content hypothesis
cannot be consumed into a content-free conclusion — the spend equality
gives 0 = 1. -/
theorem no_vanishing_eq {t : Term}
    (h : Typed [Ty.content] t Ty.unit) (hc : pureCount h = 0) : False := by
  have he := netEq h hc
  have hu : uses h 0 = 1 := single_linear_use h 0 Ty.content rfl rfl
  simp only [net, spendNet, spendNetFrom] at he
  rw [hu] at he
  omega

/-- NO CONTRACTION, equality fragment (PROVEN): two tokens cannot be
carried out of one — the spend equality gives 2 = 1. -/
theorem no_contraction_eq {t : Term}
    (h : Typed [Ty.content] t (.tensor Ty.content Ty.content))
    (hc : pureCount h = 0) : False := by
  have he := netEq h hc
  have hu : uses h 0 = 1 := single_linear_use h 0 Ty.content rfl rfl
  simp only [net, spendNet, spendNetFrom] at he
  rw [hu] at he
  omega


/-! ## The full-rule flow equality -/

/-- Sink nodes: each cons/snoc firing swallows one content token into an
opaque type (stream/trace). -/
def sinks : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => sinks hc + sinks ht + 1
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => sinks ht + sinks hu + 1
  | _, _, _, @Typed.lam _ _ _ _ h => sinks h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => sinks hf + sinks ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => sinks hl + sinks hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => sinks ht + sinks hb
  | _, _, _, @Typed.next _ _ _ h => sinks h
  | _, _, _, @Typed.fix _ a _ _ h => sinks h
  | _, _, _, @Typed.contr _ _ _ _ _ h => sinks h
  | _, _, _, @Typed.weak _ _ _ _ _ h => sinks h
  | _, _, _, _ => 0

/-- Mint nodes: each guarded fixpoint licenses its conclusion's net (the
unroll re-uses the intuitionistic context — the legalized duplication);
each gen node carries one credit. -/
def fixMint : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Int
  | _, _, _, @Typed.fix _ a _ _ h => fixMint h + net a
  | _, _, _, @Typed.lam _ _ _ _ h => fixMint h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => fixMint hf + fixMint ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => fixMint hl + fixMint hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => fixMint ht + fixMint hb
  | _, _, _, @Typed.next _ _ _ h => fixMint h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => fixMint hc + fixMint ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => fixMint ht + fixMint hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => fixMint h
  | _, _, _, @Typed.weak _ _ _ _ _ h => fixMint h
  | _, _, _, _ => 0

/-- THE FULL FLOW EQUALITY, every rule: what the conclusion carries plus
what was archived equals what the context spent plus what the coalgebra
minted plus what the unrolls licensed. Nothing is created, nothing
vanishes — every token is accounted. -/
theorem flowEq : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    net τ + (sinks h : Int) = spendNet h + (genFire h : Int) + fixMint h
  | _, _, _, Typed.var => by
      simp only [spendNet, spendNetFrom, uses, net, sinks, genFire, fixMint]
      simp
  | _, _, _, @Typed.lam Γ a b body h => by
      have ih := flowEq h
      have hb := binder_exact a h (List.get?_zero_cons')
      have hsplit : spendNet (Γ := a :: Γ) h
          = (uses h 0 : Int) * net a + spendNetFrom 1 Γ (uses h) := rfl
      rw [hsplit] at ih
      have hreb : spendNetFrom 0 Γ (uses (@Typed.lam Γ a b body h))
          = spendNetFrom 1 Γ (uses h) :=
        spendNetFrom_rebase Γ (uses (@Typed.lam Γ a b body h)) (uses h) 0 1
          fun i => by rw [Nat.zero_add, Nat.add_comm 1 i]; rfl
      show net (a.arrow b) + _ = _
      simp only [spendNet, net, sinks, genFire, fixMint] at ih ⊢
      rw [hb] at ih
      clear hb
      rw [hreb]
      omega
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs => by
      have ihf := flowEq hf
      have iha := flowEq ha
      subst hs
      have h1 : spendNetFrom 0 Γ (uses (@Typed.app (Γ ++ Δ) Γ Δ X b fn arg hf ha rfl))
          = spendNetFrom 0 Γ (uses hf) :=
        spendNetFrom_congr Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hf i else uses ha (i - Γ.length)) = uses hf i
          rw [if_pos (by omega)]
      have h2 : spendNetFrom (0 + Γ.length) Δ (uses (@Typed.app (Γ ++ Δ) Γ Δ X b fn arg hf ha rfl))
          = spendNetFrom 0 Δ (uses ha) :=
        spendNetFrom_rebase Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hf (0 + Γ.length + i)
                else uses ha (0 + Γ.length + i - Γ.length)) = uses ha (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show net b + _ = _
      simp only [spendNet] at ihf iha ⊢
      rw [spendNetFrom_append, h1, h2] at ⊢
      simp only [net, sinks, genFire, fixMint] at ihf iha ⊢
      omega
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs => by
      have ihl := flowEq hl
      have ihr := flowEq hr
      subst hs
      have h1 : spendNetFrom 0 Γ (uses (@Typed.pair (Γ ++ Δ) Γ Δ a b l r hl hr rfl))
          = spendNetFrom 0 Γ (uses hl) :=
        spendNetFrom_congr Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hl i else uses hr (i - Γ.length)) = uses hl i
          rw [if_pos (by omega)]
      have h2 : spendNetFrom (0 + Γ.length) Δ (uses (@Typed.pair (Γ ++ Δ) Γ Δ a b l r hl hr rfl))
          = spendNetFrom 0 Δ (uses hr) :=
        spendNetFrom_rebase Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hl (0 + Γ.length + i)
                else uses hr (0 + Γ.length + i - Γ.length)) = uses hr (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show net (a.tensor b) + _ = _
      simp only [spendNet] at ihl ihr ⊢
      rw [spendNetFrom_append, h1, h2] at ⊢
      simp only [net, sinks, genFire, fixMint] at ihl ihr ⊢
      omega
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs => by
      have iht := flowEq ht
      have ihb := flowEq hb
      have hb0 := binder_exact b hb (List.get?_zero_cons')
      have hb1 := binder_exact a hb (by rw [List.get?_succ_cons']; exact List.get?_zero_cons')
      have hsplit : spendNet (Γ := b :: a :: Γ₂) hb
          = (uses hb 0 : Int) * net b + ((uses hb 1 : Int) * net a
            + spendNetFrom 2 Γ₂ (uses hb)) := rfl
      rw [hsplit] at ihb
      rw [hb0, hb1] at ihb
      clear hb0 hb1
      subst hs
      have h1 : spendNetFrom 0 Γ₁ (uses (@Typed.lete (Γ₁ ++ Γ₂) Γ₁ Γ₂ a b c t body ht hb rfl))
          = spendNetFrom 0 Γ₁ (uses ht) :=
        spendNetFrom_congr Γ₁ _ _ 0 fun i _ hilt => by
          show (if i < Γ₁.length then uses ht i else uses hb (i - Γ₁.length + 2)) = uses ht i
          rw [if_pos (by omega)]
      have h2 : spendNetFrom (0 + Γ₁.length) Γ₂ (uses (@Typed.lete (Γ₁ ++ Γ₂) Γ₁ Γ₂ a b c t body ht hb rfl))
          = spendNetFrom 2 Γ₂ (uses hb) :=
        spendNetFrom_rebase Γ₂ _ _ (0 + Γ₁.length) 2 fun i => by
          show (if 0 + Γ₁.length + i < Γ₁.length then uses ht (0 + Γ₁.length + i)
                else uses hb (0 + Γ₁.length + i - Γ₁.length + 2)) = uses hb (2 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.add_comm 2 i]
      show net c + _ = _
      simp only [spendNet] at iht ihb ⊢
      rw [spendNetFrom_append, h1, h2] at ⊢
      -- iht already spendNet-free
      simp only [net, sinks, genFire, fixMint] at iht ihb ⊢
      omega
  | _, _, _, Typed.unit => by
      simp [net, spendNet, spendNetFrom, sinks, genFire, fixMint]
  | _, _, _, @Typed.next Γ a t h => flowEq h
  | _, _, _, Typed.nil => by
      simp [net, spendNet, spendNetFrom, sinks, genFire, fixMint]
  | _, _, _, @Typed.red => by
      simp [net, spendNet, spendNetFrom, uses, sinks, genFire, fixMint]
  | _, _, _, @Typed.obj => by
      simp [net, spendNet, spendNetFrom, uses, sinks, genFire, fixMint]
  | _, _, _, @Typed.terminate => by
      simp [net, spendNet, spendNetFrom, uses, sinks, genFire, fixMint]
  | _, _, _, @Typed.gen => by
      simp [net, spendNet, spendNetFrom, uses, sinks, genFire, fixMint]
  | _, _, _, @Typed.fix Γ a body hΓ h => by
      have ih := flowEq h
      have harr : net (Ty.arrow (Ty.later a) a) = net a - net (Ty.later a) := rfl
      rw [harr] at ih
      have hla : net (Ty.later a) = net a := rfl
      rw [hla, Int.sub_self, Int.zero_add] at ih
      show net a + _ = _
      rw [spendNet] at ih
      rw [spendNet]
      have huf : spendNetFrom 0 Γ (uses (@Typed.fix Γ a body hΓ h)) = spendNetFrom 0 Γ (uses h) := rfl
      rw [huf]
      simp only [sinks, genFire, fixMint] at ih ⊢
      omega
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs => by
      have ihc := flowEq hc
      have iht := flowEq ht
      subst hs
      have h1 : spendNetFrom 0 Γ (uses (@Typed.cons (Γ ++ Δ) Γ Δ hd tl hc ht rfl))
          = spendNetFrom 0 Γ (uses hc) :=
        spendNetFrom_congr Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hc i else uses ht (i - Γ.length)) = uses hc i
          rw [if_pos (by omega)]
      have h2 : spendNetFrom (0 + Γ.length) Δ (uses (@Typed.cons (Γ ++ Δ) Γ Δ hd tl hc ht rfl))
          = spendNetFrom 0 Δ (uses ht) :=
        spendNetFrom_rebase Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hc (0 + Γ.length + i)
                else uses ht (0 + Γ.length + i - Γ.length)) = uses ht (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show net Ty.stream + _ = _
      simp only [spendNet] at ihc iht ⊢
      rw [spendNetFrom_append, h1, h2] at ⊢
      simp only [net, sinks, genFire, fixMint] at ihc iht ⊢
      omega
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs => by
      have iht := flowEq ht
      have ihu := flowEq hu
      subst hs
      have h1 : spendNetFrom 0 Γ (uses (@Typed.snoc (Γ ++ Δ) Γ Δ t u ht hu rfl))
          = spendNetFrom 0 Γ (uses ht) :=
        spendNetFrom_congr Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses ht i else uses hu (i - Γ.length)) = uses ht i
          rw [if_pos (by omega)]
      have h2 : spendNetFrom (0 + Γ.length) Δ (uses (@Typed.snoc (Γ ++ Δ) Γ Δ t u ht hu rfl))
          = spendNetFrom 0 Δ (uses hu) :=
        spendNetFrom_rebase Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses ht (0 + Γ.length + i)
                else uses hu (0 + Γ.length + i - Γ.length)) = uses hu (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show net Ty.trace + _ = _
      simp only [spendNet] at iht ihu ⊢
      rw [spendNetFrom_append, h1, h2] at ⊢
      simp only [net, sinks, genFire, fixMint] at iht ihu ⊢
      omega
  | _, _, _, @Typed.contr Γ k t τ hk h => by
      have ih := flowEq h
      have hk0 := nonlinear_net k hk
      have hsplitI : spendNet (Γ := k :: k :: Γ) h
          = (uses h 0 : Int) * net k + ((uses h 1 : Int) * net k
            + spendNetFrom 2 Γ (uses h)) := rfl
      rw [hsplitI, hk0] at ih
      simp only [Int.mul_zero, Int.add_zero, Int.zero_add] at ih
      have hreb : spendNetFrom (0 + 1) Γ (uses (@Typed.contr Γ k t τ hk h))
          = spendNetFrom 2 Γ (uses h) :=
        spendNetFrom_rebase Γ _ _ (0 + 1) 2 fun i => by
          have h1 : (1 + i : Nat) ≠ 0 := by omega
          simp only [uses, if_neg h1]
          congr 1
          omega
      show net τ + _ = _
      rw [spendNet, spendNetFrom]
      rw [hreb, hk0]
      simp only [Int.mul_zero, Int.add_zero, Int.zero_add]
      simp only [sinks, genFire, fixMint]
      exact ih
  | _, _, _, @Typed.weak Γ k t τ hk h => by
      have ih := flowEq h
      have hk0 := nonlinear_net k hk
      show net τ + _ = _
      rw [spendNet, spendNetFrom]
      have hreb : spendNetFrom (0 + 1) Γ (uses (@Typed.weak Γ k t τ hk h))
          = spendNetFrom 0 Γ (uses h) :=
        spendNetFrom_rebase Γ _ _ (0 + 1) 0 fun i => by
          have h1 : (1 + i : Nat) ≠ 0 := by omega
          simp [uses, h1, Nat.add_sub_cancel_left, Nat.zero_add]
      rw [hreb]
      have h0 : (uses (@Typed.weak Γ k t τ hk h) 0 : Int) * net k = 0 := by
        simp only [uses, hk0, Int.mul_zero]
      rw [h0, Int.zero_add]
      simp only [sinks, genFire, fixMint]
      exact ih

end Dcare
