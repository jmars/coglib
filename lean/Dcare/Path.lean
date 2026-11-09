import Dcare.Typing
import Dcare.ListAux
import Dcare.Count
import Dcare.Flow
import Dcare.Model

/-!
# Path machinery: derivation size, subderivations, content-need

The last two non-derivability theorems (`no_contraction_content`,
`no_vanishing`) are reach statements: a token archived at a sink, or minted
by the coalgebra, would have to REACH the conclusion of a `[content]`-rooted
derivation, and the conclusion carries nothing (`unit`) or one token where
two are claimed (`C ⊗ C`). Inhabitation models cannot see this (insight
#22), so the analysis walks the derivation tree itself:

- `size` / `Sub` / `Sub_size` — derivation measure and subderivation
  relation, the frame for strong induction;
- `NeedsC` / `cprop` — CONTENT-need propagation, the analogue of `kprop`
  with a TRIPLE conjunction on arrows: `NeedsC (arrow a b) := NeedsC b ∧
  ¬NeedsC a ∧ ¬NeedsK a`. The third conjunct is load-bearing — a
  knower-domain supplies content transitively (`gen` fires on the
  argument), and the naive double conjunction is falsified by
  `λknower (app gen (var 0)) : arrow K (content ⊗ K)` at `[]`, which
  needs content but is supplied by its own domain.
-/

namespace Dcare

/-! ## Derivation size and subderivations -/

/-- Size of a derivation: one per node. -/
def size : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, Typed.var => 1
  | _, _, _, @Typed.lam _ _ _ _ h => 1 + size h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => 1 + size hf + size ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => 1 + size hl + size hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => 1 + size ht + size hb
  | _, _, _, Typed.unit => 1
  | _, _, _, @Typed.next _ _ _ h => 1 + size h
  | _, _, _, @Typed.fix _ _ _ _ h => 1 + size h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => 1 + size hc + size ht
  | _, _, _, Typed.nil => 1
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => 1 + size ht + size hu
  | _, _, _, Typed.gen => 1
  | _, _, _, Typed.red => 1
  | _, _, _, Typed.obj => 1
  | _, _, _, Typed.terminate => 1
  | _, _, _, @Typed.contr _ _ _ _ _ h => 1 + size h
  | _, _, _, @Typed.weak _ _ _ _ _ h => 1 + size h

/-- `Sub h d`: `d` is a PROPER subderivation of `h` — a premise, at any
depth ≥ 1. The premise-position constructors are the walking frame for
the reach arguments (a value's journey UP the tree). -/
inductive Sub : {Γ₁ : List Ty} → {t₁ : Term} → {τ₁ : Ty} → Typed Γ₁ t₁ τ₁ →
                {Γ₂ : List Ty} → {t₂ : Term} → {τ₂ : Ty} → Typed Γ₂ t₂ τ₂ → Prop where
  | lam {Γ a b body} {h : Typed (a :: Γ) body b}
      {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub h d) : Sub (Typed.lam h) d
  | appL {E Γ Δ a b fn arg} {hf : Typed Γ fn (.arrow a b)} {ha : Typed Δ arg a}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub hf d) :
      Sub (Typed.app hf ha hs) d
  | appR {E Γ Δ a b fn arg} {hf : Typed Γ fn (.arrow a b)} {ha : Typed Δ arg a}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub ha d) :
      Sub (Typed.app hf ha hs) d
  | pairL {E Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub hl d) :
      Sub (Typed.pair hl hr hs) d
  | pairR {E Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub hr d) :
      Sub (Typed.pair hl hr hs) d
  | leteT {E Γ₁ Γ₂ a b c t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E}
      {Γ' t' τ'} {d : Typed Γ' t' τ'} (s : Sub ht d) :
      Sub (Typed.lete ht hb hs) d
  | leteB {E Γ₁ Γ₂ a b c t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E}
      {Γ' t' τ'} {d : Typed Γ' t' τ'} (s : Sub hb d) :
      Sub (Typed.lete ht hb hs) d
  | next {Γ a t} {h : Typed Γ t a} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂}
      (s : Sub h d) : Sub (Typed.next h) d
  | fix {Γ a body} {hΓ : AllNonLinear Γ} {h : Typed Γ body (.arrow (.later a) a)}
      {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub h d) : Sub (Typed.fix hΓ h) d
  | consH {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub hc d) :
      Sub (Typed.cons hc ht hs) d
  | consT {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub ht d) :
      Sub (Typed.cons hc ht hs) d
  | snocT {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub ht d) :
      Sub (Typed.snoc ht hu hs) d
  | snocU {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub hu d) :
      Sub (Typed.snoc ht hu hs) d
  | contr {Γ k t τ} {hk : k.isLinear = false} {h : Typed (k :: k :: Γ) (Term.mergeAt 0 t) τ}
      {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub h d) : Sub (Typed.contr hk h) d
  | weak {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false} {h : Typed Γ t τ}
      {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} (s : Sub h d) : Sub (Typed.weak hk h) d

/-- Subderivations are strictly smaller — the well-founded measure for the
reach inductions. -/
theorem Sub_size : ∀ {Γ₁ t₁ τ₁} {h : Typed Γ₁ t₁ τ₁} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂},
    Sub h d → size d < size h := by
  intro Γ₁ t₁ τ₁ h Γ₂ t₂ τ₂ d hs
  induction hs with
  | lam s ih => simp only [size] at *; omega
  | appL s ih => simp only [size] at *; omega
  | appR s ih => simp only [size] at *; omega
  | pairL s ih => simp only [size] at *; omega
  | pairR s ih => simp only [size] at *; omega
  | leteT s ih => simp only [size] at *; omega
  | leteB s ih => simp only [size] at *; omega
  | next s ih => simp only [size] at *; omega
  | fix s ih => simp only [size] at *; omega
  | consH s ih => simp only [size] at *; omega
  | consT s ih => simp only [size] at *; omega
  | snocT s ih => simp only [size] at *; omega
  | snocU s ih => simp only [size] at *; omega
  | contr s ih => simp only [size] at *; omega
  | weak s ih => simp only [size] at *; omega

/-! ## Content-need propagation -/

/-- Content-NEED: the type carries a content-demand its context must fund.
Arrows: codomain must need, domain must need NEITHER content (the obvious)
NOR a knower (the subtle — a knower-domain supplies content transitively:
`gen` fires on the argument; without the third conjunct the lemma is
falsified by `λknower (app gen (var 0)) : arrow K (content ⊗ K)` at `[]`). -/
def NeedsC : Ty → Prop
  | .content => True
  | .tensor a b => NeedsC a ∨ NeedsC b
  | .arrow a b => NeedsC b ∧ ¬ NeedsC a ∧ ¬ NeedsK a
  | _ => False

/-- A hypothesis can fund a content-demand: by being the content, or by
being a knower-supply (the coalgebra mints content from knowers). -/
def CSupply (b : Ty) : Prop := NeedsC b ∨ NeedsK b

/-- CONTENT-NEED PROPAGATION: a content-needing conclusion forces a
supplying hypothesis — content itself, or a knower for the coalgebra. No
`gen` disjunct: the coalgebra CONSUMES knowers, it never conjures content
from nothing (its own type needs nothing — the supply is its argument's
business). The kprop template, with the app-case split three ways. -/
theorem cprop : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    NeedsC τ → ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ CSupply b
  | _, _, _, Typed.var, hK => ⟨0, _, List.get?_zero_cons', Or.inl hK⟩
  | _, _, _, @Typed.lam Γ a b _ h, ⟨hb, hna, hnk⟩ => by
      have hk := cprop h hb
      match hk with
      | ⟨0, b', hpos, hsup⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hsup with hc | hk'
          · exact (hna hc).elim
          · exact (hnk hk').elim
      | ⟨n + 1, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons'] at hpos
          exact ⟨n, b', hpos, hsup⟩
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hK => by
      by_cases hx : NeedsC X
      · obtain ⟨j, b', hpos, hsup⟩ := cprop ha hx
        refine ⟨Γ.length + j, b', ?_, hsup⟩
        rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
          Nat.add_sub_cancel_left]
        exact hpos
      · by_cases hk : NeedsK X
        · obtain ⟨j, b', hpos, hsup⟩ := kprop ha hk
          refine ⟨Γ.length + j, b', ?_, Or.inr hsup⟩
          rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
            Nat.add_sub_cancel_left]
          exact hpos
        · obtain ⟨i, b', hpos, hsup⟩ := cprop hf ⟨hK, hx, hk⟩
          refine ⟨i, b', ?_, hsup⟩
          have hlt : i < Γ.length := List.get?_some_lt hpos
          rw [← hs, List.get?_append_lt hlt]
          exact hpos
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hK => by
      rcases hK with hK | hK
      · obtain ⟨i, b', hpos, hsup⟩ := cprop hl hK
        refine ⟨i, b', ?_, hsup⟩
        have hlt : i < Γ.length := List.get?_some_lt hpos
        rw [← hs, List.get?_append_lt hlt]
        exact hpos
      · obtain ⟨j, b', hpos, hsup⟩ := cprop hr hK
        refine ⟨Γ.length + j, b', ?_, hsup⟩
        rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
          Nat.add_sub_cancel_left]
        exact hpos
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hK => by
      have hk := cprop hb hK
      match hk with
      | ⟨0, b', hpos, hsup⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hsup with hc | hk'
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := cprop ht (Or.inr hc)
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := kprop ht (Or.inr hk')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, Or.inr hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
      | ⟨1, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hsup with hc | hk'
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := cprop ht (Or.inl hc)
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := kprop ht (Or.inl hk')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, Or.inr hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
      | ⟨m + 2, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
          refine ⟨Γ₁.length + m, b', ?_, hsup⟩
          rw [← hs, List.get?_append_ge (Nat.le_add_right Γ₁.length m),
            Nat.add_sub_cancel_left]
          exact hpos
  | _, _, _, Typed.unit, hK => False.elim hK
  | _, _, _, @Typed.next _ _ _ _, hK => False.elim hK
  | _, _, _, @Typed.fix _ _ _ _ h, hK => cprop h ⟨hK, fun hf => hf, fun hf => hf⟩
  | _, _, _, @Typed.cons _ _ _ _ _ _ _ _, hK => False.elim hK
  | _, _, _, Typed.nil, hK => False.elim hK
  | _, _, _, @Typed.snoc _ _ _ _ _ _ _ _, hK => False.elim hK
  | _, _, _, Typed.gen, hK => (hK.2.2 True.intro).elim
  | _, _, _, Typed.red, ⟨hb, _, _⟩ => False.elim hb
  | _, _, _, Typed.obj, ⟨hb, _, _⟩ => False.elim hb
  | _, _, _, Typed.terminate, ⟨hb, _, _⟩ => False.elim hb
  | _, _, _, @Typed.contr Γ k t τ _ h, hK => by
      have hk := cprop h hK
      match hk with
      | ⟨0, b', hpos, hsup⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact ⟨0, _, List.get?_zero_cons', hsup⟩
      | ⟨1, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact ⟨0, _, List.get?_zero_cons', hsup⟩
      | ⟨m + 2, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
          exact ⟨m + 1, b', by rw [List.get?_succ_cons']; exact hpos, hsup⟩
  | _, _, _, @Typed.weak Γ k t τ _ h, hK => by
      obtain ⟨i, b', hpos, hsup⟩ := cprop h hK
      exact ⟨i + 1, b', by rw [List.get?_succ_cons']; exact hpos, hsup⟩

/-- Content-need implies linearity: every type that demands content is
itself linear (a content leaf anywhere makes the type linear). -/
theorem needsC_linear : ∀ a : Ty, NeedsC a → a.isLinear = true := by
  intro a
  induction a with
  | content => intro _; rfl
  | knower | knowledge | value | trace | stream | unit => intro h; exact h.elim
  | later a' _ => intro h; exact h.elim
  | tensor a' b' iha ihb =>
      intro h
      rcases h with h | h
      · simp [Ty.isLinear, iha h]
      · simp [Ty.isLinear, ihb h]
  | arrow a' b' iha ihb =>
      intro h
      simp [Ty.isLinear, ihb h.1]

/-- No content at a no-supply context: the contrapositive workhorse. -/
theorem no_content_nosupply {Γ : List Ty} {t : Term}
    (h : Typed Γ t Ty.content)
    (hns : ∀ (i : Nat) (b : Ty), Γ[i]? = some b → ¬ CSupply b) : False := by
  obtain ⟨i, b, hpos, hsup⟩ := cprop h True.intro
  exact hns i b hpos hsup

/-- The delayed world supplies nothing: no content-demand can be funded
from a `▷ stream` hypothesis (and a fortiori from a context of them). -/
theorem no_content_at_later_stream {Γ : List Ty} {t : Term}
    (h : Typed Γ t Ty.content)
    (hns : ∀ (i : Nat) (b : Ty), Γ[i]? = some b → b = Ty.later Ty.stream) : False := by
  refine no_content_nosupply h ?_
  intro i b hpos hsup
  rw [hns i b hpos] at hsup
  rcases hsup with hc | hk
  · exact hc
  · exact hk

/-- A guarded fixpoint at a content-carrying type NEEDS A KNOWER: its body
must produce the content from the delayed world, the delayed world supplies
nothing (`cprop`), and the all-non-linear side condition excludes a content
supply — so the supply is a knower. Every `fixMint` credit is knower-fed. -/
theorem fix_knower_supply {Γ : List Ty} {a : Ty} {body : Term}
    (hΓ : AllNonLinear Γ) (h : Typed Γ body (.arrow (.later a) a))
    (ha : NeedsC a) : ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ NeedsK b := by
  obtain ⟨i, b, hpos, hsup⟩ := cprop h ⟨ha, fun hf => hf, fun hf => hf⟩
  rcases hsup with hc | hk
  · exfalso
    have hlin := needsC_linear b hc
    have hnlin := hΓ i b hpos
    rw [hlin] at hnlin
    exact Bool.noConfusion hnlin
  · exact ⟨i, b, hpos, hk⟩

/-! ## The closed-liveness base -/

/-- No closed stream exists — the barren world (stream ↦ False) in one
line. Streams are knower-sustained; from nothing, nothing flows. -/
theorem no_closed_stream {t : Term} (h : Typed [] t Ty.stream) : False :=
  (sound h True.intro).elim

/-! ## The trace-token account (tFlowEq) -/

/-- Trace-NET: the trace-token content of a type. Arrows subtract the
DOMAIN — a function owes its codomain's trace-tokens and is owed its
domain's — the same integer move that makes application DISCHARGE the
demand in the arithmetic. This is what makes killer-apps (a trace
consumed by `arrow trace c` with `c` unmentioning) arithmetic-neutral:
the killer-fn's own type carries the trace-DEBT, and debts cannot cancel
without mints. -/
def tnet : Ty → Int
  | .trace => 1
  | .later a => tnet a
  | .tensor a b => tnet a + tnet b
  | .arrow a b => tnet b - tnet a
  | _ => 0

/-- Non-linear types carry no trace-tokens: trace-containing types are
linear (`isLinear` propagates by OR/underlying), so the gated structural
rules never move a token. The `nonlinear_net` template. -/
theorem nonlinear_tnet : ∀ a : Ty, a.isLinear = false → tnet a = 0 := by
  intro a
  cases a with
  | content => intro h; exact Bool.noConfusion h
  | trace => intro h; exact Bool.noConfusion h
  | stream => intro h; exact Bool.noConfusion h
  | knower | knowledge | value | unit => intro _; rfl
  | later a' => intro h; exact nonlinear_tnet a' h
  | tensor a' b' =>
      intro h
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using h)
      rw [tnet, nonlinear_tnet a' h'.1, nonlinear_tnet b' h'.2]; rfl
  | arrow a' b' =>
      intro h
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using h)
      rw [tnet, nonlinear_tnet b' h'.2, nonlinear_tnet a' h'.1]; rfl

/-- Weight-generic spend: `Σ uses · w(hyp)` over a context, from a base
position. Instantiated at `net` this reproduces `spendNet`; the trace
account instantiates it at `tnet`. -/
def wSpendFrom (w : Ty → Int) (base : Nat) : List Ty → (Nat → Nat) → Int
  | [], _ => 0
  | a :: Γ, u => (u base : Int) * w a + wSpendFrom w (base + 1) Γ u

theorem wSpendFrom_congr : ∀ (w : Ty → Int) (Γ : List Ty) (u v : Nat → Nat) (b : Nat),
    (∀ i, b ≤ i → i < b + Γ.length → u i = v i) →
    wSpendFrom w b Γ u = wSpendFrom w b Γ v
  | _, [], _, _, _, _ => rfl
  | w, a :: Γ', u, v, b, huv => by
      have hlen : (a :: Γ').length = Γ'.length + 1 := rfl
      have h1 : u b = v b := huv b (Nat.le_refl b) (by rw [hlen]; omega)
      have h2 : wSpendFrom w (b + 1) Γ' u = wSpendFrom w (b + 1) Γ' v :=
        wSpendFrom_congr w Γ' u v (b + 1) fun i hi hii =>
          huv i (Nat.le_trans (Nat.le_succ b) hi) (by show i < b + (Γ'.length + 1); omega)
      rw [wSpendFrom, wSpendFrom, h1, h2]

theorem wSpendFrom_append : ∀ (w : Ty → Int) (Γ₁ Δ : List Ty) (u : Nat → Nat) (b : Nat),
    wSpendFrom w b (Γ₁ ++ Δ) u = wSpendFrom w b Γ₁ u + wSpendFrom w (b + Γ₁.length) Δ u
  | _, [], _, _, _ => by simp [wSpendFrom]
  | w, a :: Γ', Δ, u, b => by
      rw [List.cons_append, wSpendFrom, wSpendFrom,
        wSpendFrom_append w Γ' Δ u (b + 1)]
      have hidx : b + (a :: Γ').length = b + 1 + Γ'.length := by
        simp only [List.length_cons]; omega
      rw [hidx]
      omega

theorem wSpendFrom_shift : ∀ (w : Ty → Int) (Γ : List Ty) (u : Nat → Nat) (b n : Nat),
    wSpendFrom w (b + n) Γ u = wSpendFrom w b Γ (fun i => u (i + n))
  | _, [], _, _, _ => rfl
  | w, _ :: Γ', u, b, n => by
      rw [wSpendFrom, wSpendFrom]
      have hbr : b + n + 1 = b + 1 + n := by omega
      rw [hbr, wSpendFrom_shift w Γ' u (b + 1) n]

theorem wSpendFrom_rebase : ∀ (w : Ty → Int) (Γ : List Ty) (v u : Nat → Nat) (b b' : Nat),
    (∀ i, v (b + i) = u (b' + i)) → wSpendFrom w b Γ v = wSpendFrom w b' Γ u
  | _, [], _, _, _, _, _ => rfl
  | w, _ :: Γ', v, u, b, b', hvu => by
      have h1 : v b = u b' := by
        have := hvu 0
        simpa [Nat.add_zero] using this
      have h2 : wSpendFrom w (b + 1) Γ' v = wSpendFrom w (b' + 1) Γ' u :=
        wSpendFrom_rebase w Γ' v u (b + 1) (b' + 1) fun i =>
          by rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm 1 i]; exact hvu (i + 1)
      rw [wSpendFrom, wSpendFrom, h1, h2]

/-- Trace-weighted spend of a derivation's context. -/
def tSpend {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ) : Int :=
  wSpendFrom tnet 0 Γ (uses h)

/-- FUSION for traces: at any hypothesis position the trace-weighted
spend is EXACT — linear positions spent exactly once, non-linear
positions carry no trace-token. -/
theorem binder_texact : ∀ (a : Ty) {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ)
    {i : Nat} (hpos : Γ[i]? = some a), (uses h i : Int) * tnet a = tnet a := by
  intro a Γ t τ h i hpos
  cases hlin : a.isLinear with
  | true =>
      have hu := single_linear_use h i a hpos hlin
      rw [hu]
      simp
  | false =>
      have h0 := nonlinear_tnet a hlin
      rw [h0, Int.mul_zero]

/-- Trace MINTS: `nil` (a trace from nothing), `terminate` (`K → trace`),
and the guarded fixpoint's licensed conclusion-tokens. -/
def tMint : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Int
  | _, _, _, Typed.nil => 1
  | _, _, _, Typed.terminate => 1
  | _, _, _, @Typed.fix _ a _ _ h => tMint h + tnet a
  | _, _, _, @Typed.lam _ _ _ _ h => tMint h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => tMint hf + tMint ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => tMint hl + tMint hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => tMint ht + tMint hb
  | _, _, _, @Typed.next _ _ _ h => tMint h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => tMint hc + tMint ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => tMint ht + tMint hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => tMint h
  | _, _, _, @Typed.weak _ _ _ _ _ h => tMint h
  | _, _, _, _ => 0

/-- THE TRACE FLOW EQUALITY: the trace-tokens the conclusion carries
equal what the context spent plus what was minted. Every rule balances;
no sinks are needed because a trace consumed by a killer-app is paid for
by the killer-fn's own type-debt (`tnet (arrow trace c) = tnet c − 1`).
The journey lemma as arithmetic. -/
theorem tFlowEq : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    tnet τ = tSpend h + tMint h
  | _, _, _, Typed.var => by
      simp [tSpend, wSpendFrom, uses, tnet, tMint]
  | _, _, _, @Typed.lam Γ a b body h => by
      have ih := tFlowEq h
      have hb := binder_texact a h (List.get?_zero_cons')
      have hsplit : tSpend (Γ := a :: Γ) h
          = (uses h 0 : Int) * tnet a + wSpendFrom tnet 1 Γ (uses h) := rfl
      rw [hsplit] at ih
      have hreb : wSpendFrom tnet 0 Γ (uses (@Typed.lam Γ a b body h))
          = wSpendFrom tnet 1 Γ (uses h) :=
        wSpendFrom_rebase tnet Γ (uses (@Typed.lam Γ a b body h)) (uses h) 0 1
          fun i => by rw [Nat.zero_add, Nat.add_comm 1 i]; rfl
      show tnet (a.arrow b) = _
      simp only [tSpend, tnet, tMint] at ih ⊢
      rw [hb] at ih
      clear hb
      rw [hreb]
      omega
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs => by
      have ihf := tFlowEq hf
      have iha := tFlowEq ha
      subst hs
      have h1 : wSpendFrom tnet 0 Γ (uses (@Typed.app (Γ ++ Δ) Γ Δ X b fn arg hf ha rfl))
          = wSpendFrom tnet 0 Γ (uses hf) :=
        wSpendFrom_congr tnet Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hf i else uses ha (i - Γ.length)) = uses hf i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom tnet (0 + Γ.length) Δ (uses (@Typed.app (Γ ++ Δ) Γ Δ X b fn arg hf ha rfl))
          = wSpendFrom tnet 0 Δ (uses ha) :=
        wSpendFrom_rebase tnet Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hf (0 + Γ.length + i)
                else uses ha (0 + Γ.length + i - Γ.length)) = uses ha (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show tnet b = _
      simp only [tSpend] at ihf iha ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [tnet, tMint] at ihf iha ⊢
      omega
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs => by
      have ihl := tFlowEq hl
      have ihr := tFlowEq hr
      subst hs
      have h1 : wSpendFrom tnet 0 Γ (uses (@Typed.pair (Γ ++ Δ) Γ Δ a b l r hl hr rfl))
          = wSpendFrom tnet 0 Γ (uses hl) :=
        wSpendFrom_congr tnet Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hl i else uses hr (i - Γ.length)) = uses hl i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom tnet (0 + Γ.length) Δ (uses (@Typed.pair (Γ ++ Δ) Γ Δ a b l r hl hr rfl))
          = wSpendFrom tnet 0 Δ (uses hr) :=
        wSpendFrom_rebase tnet Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hl (0 + Γ.length + i)
                else uses hr (0 + Γ.length + i - Γ.length)) = uses hr (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show tnet (a.tensor b) = _
      simp only [tSpend] at ihl ihr ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [tnet, tMint] at ihl ihr ⊢
      omega
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs => by
      have iht := tFlowEq ht
      have ihb := tFlowEq hb
      have hb0 := binder_texact b hb (List.get?_zero_cons')
      have hb1 := binder_texact a hb (by rw [List.get?_succ_cons']; exact List.get?_zero_cons')
      have hsplit : tSpend (Γ := b :: a :: Γ₂) hb
          = (uses hb 0 : Int) * tnet b + ((uses hb 1 : Int) * tnet a
            + wSpendFrom tnet 2 Γ₂ (uses hb)) := rfl
      rw [hsplit] at ihb
      rw [hb0, hb1] at ihb
      clear hb0 hb1
      subst hs
      have h1 : wSpendFrom tnet 0 Γ₁ (uses (@Typed.lete (Γ₁ ++ Γ₂) Γ₁ Γ₂ a b c t body ht hb rfl))
          = wSpendFrom tnet 0 Γ₁ (uses ht) :=
        wSpendFrom_congr tnet Γ₁ _ _ 0 fun i _ hilt => by
          show (if i < Γ₁.length then uses ht i else uses hb (i - Γ₁.length + 2)) = uses ht i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom tnet (0 + Γ₁.length) Γ₂ (uses (@Typed.lete (Γ₁ ++ Γ₂) Γ₁ Γ₂ a b c t body ht hb rfl))
          = wSpendFrom tnet 2 Γ₂ (uses hb) :=
        wSpendFrom_rebase tnet Γ₂ _ _ (0 + Γ₁.length) 2 fun i => by
          show (if 0 + Γ₁.length + i < Γ₁.length then uses ht (0 + Γ₁.length + i)
                else uses hb (0 + Γ₁.length + i - Γ₁.length + 2)) = uses hb (2 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.add_comm 2 i]
      show tnet c = _
      simp only [tSpend] at iht ihb ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [tnet, tMint] at iht ihb ⊢
      omega
  | _, _, _, Typed.unit => by
      simp [tnet, tSpend, wSpendFrom, tMint]
  | _, _, _, @Typed.next Γ a t h => tFlowEq h
  | _, _, _, Typed.nil => by
      simp [tnet, tSpend, wSpendFrom, tMint]
  | _, _, _, @Typed.red => by
      simp [tnet, tSpend, wSpendFrom, uses, tMint]
  | _, _, _, @Typed.obj => by
      simp [tnet, tSpend, wSpendFrom, uses, tMint]
  | _, _, _, @Typed.terminate => by
      simp [tnet, tSpend, wSpendFrom, uses, tMint]
  | _, _, _, @Typed.gen => by
      simp [tnet, tSpend, wSpendFrom, uses, tMint]
  | _, _, _, @Typed.fix Γ a body hΓ h => by
      have ih := tFlowEq h
      have harr : tnet (Ty.arrow (Ty.later a) a) = tnet a - tnet (Ty.later a) := rfl
      rw [harr] at ih
      have hla : tnet (Ty.later a) = tnet a := rfl
      rw [hla, Int.sub_self] at ih
      show tnet a = _
      have huf : wSpendFrom tnet 0 Γ (uses (@Typed.fix Γ a body hΓ h))
          = wSpendFrom tnet 0 Γ (uses h) := rfl
      rw [tSpend, huf]
      rw [tSpend] at ih
      simp only [tMint] at ih ⊢
      omega
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs => by
      have ihc := tFlowEq hc
      have iht := tFlowEq ht
      subst hs
      have h1 : wSpendFrom tnet 0 Γ (uses (@Typed.cons (Γ ++ Δ) Γ Δ hd tl hc ht rfl))
          = wSpendFrom tnet 0 Γ (uses hc) :=
        wSpendFrom_congr tnet Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hc i else uses ht (i - Γ.length)) = uses hc i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom tnet (0 + Γ.length) Δ (uses (@Typed.cons (Γ ++ Δ) Γ Δ hd tl hc ht rfl))
          = wSpendFrom tnet 0 Δ (uses ht) :=
        wSpendFrom_rebase tnet Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hc (0 + Γ.length + i)
                else uses ht (0 + Γ.length + i - Γ.length)) = uses ht (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show tnet Ty.stream = _
      simp only [tSpend] at ihc iht ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [tnet, tMint] at ihc iht ⊢
      omega
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs => by
      have iht := tFlowEq ht
      have ihu := tFlowEq hu
      subst hs
      have h1 : wSpendFrom tnet 0 Γ (uses (@Typed.snoc (Γ ++ Δ) Γ Δ t u ht hu rfl))
          = wSpendFrom tnet 0 Γ (uses ht) :=
        wSpendFrom_congr tnet Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses ht i else uses hu (i - Γ.length)) = uses ht i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom tnet (0 + Γ.length) Δ (uses (@Typed.snoc (Γ ++ Δ) Γ Δ t u ht hu rfl))
          = wSpendFrom tnet 0 Δ (uses hu) :=
        wSpendFrom_rebase tnet Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses ht (0 + Γ.length + i)
                else uses hu (0 + Γ.length + i - Γ.length)) = uses hu (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show tnet Ty.trace = _
      simp only [tSpend] at iht ihu ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [tnet, tMint] at iht ihu ⊢
      omega
  | _, _, _, @Typed.contr Γ k t τ hk h => by
      have ih := tFlowEq h
      have hk0 := nonlinear_tnet k hk
      have hsplitI : tSpend (Γ := k :: k :: Γ) h
          = (uses h 0 : Int) * tnet k + ((uses h 1 : Int) * tnet k
            + wSpendFrom tnet 2 Γ (uses h)) := rfl
      rw [hsplitI, hk0] at ih
      simp only [Int.mul_zero, Int.add_zero, Int.zero_add] at ih
      have hreb : wSpendFrom tnet (0 + 1) Γ (uses (@Typed.contr Γ k t τ hk h))
          = wSpendFrom tnet 2 Γ (uses h) :=
        wSpendFrom_rebase tnet Γ _ _ (0 + 1) 2 fun i => by
          have h1 : (1 + i : Nat) ≠ 0 := by omega
          simp only [uses, if_neg h1]
          congr 1
          omega
      show tnet τ = _
      rw [tSpend, wSpendFrom]
      rw [hreb, hk0]
      simp only [Int.mul_zero, Int.add_zero, Int.zero_add]
      simp only [tMint]
      exact ih
  | _, _, _, @Typed.weak Γ k t τ hk h => by
      have ih := tFlowEq h
      have hk0 := nonlinear_tnet k hk
      show tnet τ = _
      rw [tSpend, wSpendFrom]
      have hreb : wSpendFrom tnet (0 + 1) Γ (uses (@Typed.weak Γ k t τ hk h))
          = wSpendFrom tnet 0 Γ (uses h) :=
        wSpendFrom_rebase tnet Γ _ _ (0 + 1) 0 fun i => by
          have h1 : (1 + i : Nat) ≠ 0 := by omega
          simp only [uses, if_neg h1, Nat.add_sub_cancel_left, Nat.zero_add]
      rw [hreb]
      have h0 : (uses (@Typed.weak Γ k t τ hk h) 0 : Int) * tnet k = 0 := by
        rw [hk0, Int.mul_zero]
      rw [h0, Int.zero_add]
      simp only [tMint]
      exact ih

/-- At a unit-rooted `[content]` derivation the trace-mints balance to
zero: the root spends no trace-tokens and `unit` carries none. -/
theorem tMint_zero_at_unit_root {t : Term} (h : Typed [Ty.content] t Ty.unit) :
    tMint h = 0 := by
  have he := tFlowEq h
  have hu : uses h 0 = 1 := single_linear_use h 0 Ty.content rfl rfl
  simp only [tnet, tSpend, wSpendFrom] at he
  rw [hu] at he
  omega

/-! ## Stream-need and trace-need propagation -/

/-- Stream-NEED. Arrows: codomain must need, domain must need NEITHER
streams nor knowers — a knower-domain supplies streams transitively (the
epistemic-cycle fixpoint lives at `[knower]`). -/
def NeedsS : Ty → Prop
  | .stream => True
  | .later a => NeedsS a
  | .tensor a b => NeedsS a ∨ NeedsS b
  | .arrow a b => NeedsS b ∧ ¬ NeedsS a ∧ ¬ NeedsK a
  | _ => False

def SSupply (b : Ty) : Prop := NeedsS b ∨ NeedsK b

/-- STREAM-NEED PROPAGATION, fix-free: a stream-needing conclusion
forces a stream-or-knower hypothesis. Fixpoints are EXCLUDED (the fix
case is genuinely different: `NeedsS (▷a) = NeedsS a`, so the fix's own
body-type never needs, and `fix @ stream` at a knower context is the
epistemic cycle — the legitimate self-carrier); fix nodes are handled by
the reach analysis instead. -/
theorem sprop : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    fixCount h = 0 → NeedsS τ → ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ SSupply b
  | _, _, _, Typed.var, _, hK => ⟨0, _, List.get?_zero_cons', Or.inl hK⟩
  | _, _, _, @Typed.lam Γ a b _ h, hfc, ⟨hb, hna, hnk⟩ => by
      have hk := sprop h (by simpa only [fixCount] using hfc) hb
      match hk with
      | ⟨0, b', hpos, hsup⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hsup with hs | hk'
          · exact (hna hs).elim
          · exact (hnk hk').elim
      | ⟨n + 1, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons'] at hpos
          exact ⟨n, b', hpos, hsup⟩
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hc, hK => by
      obtain ⟨hc1, hc2⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hc
      by_cases hx : NeedsS X
      · obtain ⟨j, b', hpos, hsup⟩ := sprop ha hc2 hx
        refine ⟨Γ.length + j, b', ?_, hsup⟩
        rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
          Nat.add_sub_cancel_left]
        exact hpos
      · by_cases hk : NeedsK X
        · obtain ⟨j, b', hpos, hsup⟩ := kprop ha hk
          refine ⟨Γ.length + j, b', ?_, Or.inr hsup⟩
          rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
            Nat.add_sub_cancel_left]
          exact hpos
        · obtain ⟨i, b', hpos, hsup⟩ := sprop hf hc1 ⟨hK, hx, hk⟩
          refine ⟨i, b', ?_, hsup⟩
          have hlt : i < Γ.length := List.get?_some_lt hpos
          rw [← hs, List.get?_append_lt hlt]
          exact hpos
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hc, hK => by
      obtain ⟨hc1, hc2⟩ : fixCount hl = 0 ∧ fixCount hr = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hc
      rcases hK with hK | hK
      · obtain ⟨i, b', hpos, hsup⟩ := sprop hl hc1 hK
        refine ⟨i, b', ?_, hsup⟩
        have hlt : i < Γ.length := List.get?_some_lt hpos
        rw [← hs, List.get?_append_lt hlt]
        exact hpos
      · obtain ⟨j, b', hpos, hsup⟩ := sprop hr hc2 hK
        refine ⟨Γ.length + j, b', ?_, hsup⟩
        rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
          Nat.add_sub_cancel_left]
        exact hpos
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hc, hK => by
      obtain ⟨hc1, hc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hc
      have hk := sprop hb hc2 hK
      match hk with
      | ⟨0, b', hpos, hsup⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hsup with hs' | hk'
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := sprop ht hc1 (Or.inr hs')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := kprop ht (Or.inr hk')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, Or.inr hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
      | ⟨1, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hsup with hs' | hk'
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := sprop ht hc1 (Or.inl hs')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := kprop ht (Or.inl hk')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, Or.inr hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
      | ⟨m + 2, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
          refine ⟨Γ₁.length + m, b', ?_, hsup⟩
          rw [← hs, List.get?_append_ge (Nat.le_add_right Γ₁.length m),
            Nat.add_sub_cancel_left]
          exact hpos
  | _, _, _, Typed.unit, _, hK => False.elim hK
  | _, _, _, @Typed.next _ _ _ h, hc, hK =>
      sprop h (by simpa only [fixCount] using hc) hK
  | _, _, _, @Typed.fix _ _ _ _ _, hc, _ => by
      simp only [fixCount] at hc; omega
  | _, _, _, @Typed.cons _ Γ Δ hd tl hc' ht hs, hc, _ => by
      obtain ⟨hc1, hc2⟩ : fixCount hc' = 0 ∧ fixCount ht = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hc
      obtain ⟨j, b', hpos, hsup⟩ := sprop ht hc2 True.intro
      refine ⟨Γ.length + j, b', ?_, hsup⟩
      rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
        Nat.add_sub_cancel_left]
      exact hpos
  | _, _, _, Typed.nil, _, hK => False.elim hK
  | _, _, _, @Typed.snoc _ _ _ _ _ _ _ _, _, hK => False.elim hK
  | _, _, _, Typed.gen, _, hK => (hK.2.2 True.intro).elim
  | _, _, _, Typed.red, _, ⟨hb, _, _⟩ => False.elim hb
  | _, _, _, Typed.obj, _, ⟨hb, _, _⟩ => False.elim hb
  | _, _, _, Typed.terminate, _, ⟨hb, _, _⟩ => False.elim hb
  | _, _, _, @Typed.contr Γ k t τ _ h, hc, hK => by
      have hk := sprop h (by simpa only [fixCount] using hc) hK
      match hk with
      | ⟨0, b', hpos, hsup⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact ⟨0, _, List.get?_zero_cons', hsup⟩
      | ⟨1, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact ⟨0, _, List.get?_zero_cons', hsup⟩
      | ⟨m + 2, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
          exact ⟨m + 1, b', by rw [List.get?_succ_cons']; exact hpos, hsup⟩
  | _, _, _, @Typed.weak Γ k t τ _ h, hc, hK => by
      obtain ⟨i, b', hpos, hsup⟩ := sprop h (by simpa only [fixCount] using hc) hK
      exact ⟨i + 1, b', by rw [List.get?_succ_cons']; exact hpos, hsup⟩

/-- No stream at a no-supply context, fix-free: with neither a stream
hypothesis nor a knower to sustain the cycle, the guarded stream type is
uninhabited. -/
theorem no_stream_nosupply {Γ : List Ty} {t : Term}
    (h : Typed Γ t Ty.stream) (hf : fixCount h = 0)
    (hns : ∀ (i : Nat) (b : Ty), Γ[i]? = some b → ¬ SSupply b) : False := by
  obtain ⟨i, b, hpos, hsup⟩ := sprop h hf True.intro
  exact hns i b hpos hsup

/-- Trace-NEED. The trace-analogue: a trace-val needs a trace-carrying
hypothesis, a content hypothesis (`snoc` archives content into trace),
or a knower (`terminate`). Arrows exclude all three in the domain. -/
def NeedsT : Ty → Prop
  | .trace => True
  | .later a => NeedsT a
  | .tensor a b => NeedsT a ∨ NeedsT b
  | .arrow a b => NeedsT b ∧ ¬ (NeedsT a ∨ NeedsC a ∨ NeedsK a)
  | _ => False

def TSupply (b : Ty) : Prop := NeedsT b ∨ NeedsC b ∨ NeedsK b

/-- Trace-pure nodes: `nil` and `terminate` (trace MINTS — a trace from
nothing) and fixpoints (as in `sprop`). A trace-needing derivation free
of these forces its context to supply. -/
def tracePure : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, Typed.nil => 1
  | _, _, _, Typed.terminate => 1
  | _, _, _, @Typed.fix _ _ _ _ _ => 1
  | _, _, _, @Typed.lam _ _ _ _ h => tracePure h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => tracePure hf + tracePure ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => tracePure hl + tracePure hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => tracePure ht + tracePure hb
  | _, _, _, @Typed.next _ _ _ h => tracePure h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => tracePure hc + tracePure ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => tracePure ht + tracePure hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => tracePure h
  | _, _, _, @Typed.weak _ _ _ _ _ h => tracePure h
  | _, _, _, _ => 0

/-- TRACE-NEED PROPAGATION, mint-free: a trace-needing conclusion free of
trace-mints (`nil`, `terminate`, fixpoints) forces a trace/content/knower
hypothesis. The mints are exactly the trace-sources-from-nothing; with
them excluded, every trace-token is inherited from the context. -/
theorem tprop : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    tracePure h = 0 → NeedsT τ → ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ TSupply b
  | _, _, _, Typed.var, _, hK => ⟨0, _, List.get?_zero_cons', Or.inl hK⟩
  | _, _, _, @Typed.lam Γ a b _ h, hp, ⟨hb, hna⟩ => by
      have hk := tprop h (by simpa only [tracePure] using hp) hb
      match hk with
      | ⟨0, b', hpos, hsup⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hsup with ht | hc | hk'
          · exact (hna (Or.inl ht)).elim
          · exact (hna (Or.inr (Or.inl hc))).elim
          · exact (hna (Or.inr (Or.inr hk'))).elim
      | ⟨n + 1, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons'] at hpos
          exact ⟨n, b', hpos, hsup⟩
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hp, hK => by
      obtain ⟨hc1, hc2⟩ : tracePure hf = 0 ∧ tracePure ha = 0 := by
        simpa only [tracePure, Nat.add_eq_zero_iff] using hp
      by_cases hx : NeedsT X
      · obtain ⟨j, b', hpos, hsup⟩ := tprop ha hc2 hx
        refine ⟨Γ.length + j, b', ?_, hsup⟩
        rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
          Nat.add_sub_cancel_left]
        exact hpos
      · by_cases hcc : NeedsC X
        · obtain ⟨j, b', hpos, hsup⟩ := cprop ha hcc
          rcases hsup with hc'' | hk''
          · refine ⟨Γ.length + j, b', ?_, Or.inr (Or.inl hc'')⟩
            rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
              Nat.add_sub_cancel_left]
            exact hpos
          · refine ⟨Γ.length + j, b', ?_, Or.inr (Or.inr hk'')⟩
            rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
              Nat.add_sub_cancel_left]
            exact hpos
        · by_cases hk : NeedsK X
          · obtain ⟨j, b', hpos, hsup⟩ := kprop ha hk
            refine ⟨Γ.length + j, b', ?_, Or.inr (Or.inr hsup)⟩
            rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
              Nat.add_sub_cancel_left]
            exact hpos
          · obtain ⟨i, b', hpos, hsup⟩ := tprop hf hc1 ⟨hK, by
              intro hs'; rcases hs' with h | h | h
              · exact hx h
              · exact hcc h
              · exact hk h⟩
            refine ⟨i, b', ?_, hsup⟩
            have hlt : i < Γ.length := List.get?_some_lt hpos
            rw [← hs, List.get?_append_lt hlt]
            exact hpos
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hp, hK => by
      obtain ⟨hc1, hc2⟩ : tracePure hl = 0 ∧ tracePure hr = 0 := by
        simpa only [tracePure, Nat.add_eq_zero_iff] using hp
      rcases hK with hK | hK
      · obtain ⟨i, b', hpos, hsup⟩ := tprop hl hc1 hK
        refine ⟨i, b', ?_, hsup⟩
        have hlt : i < Γ.length := List.get?_some_lt hpos
        rw [← hs, List.get?_append_lt hlt]
        exact hpos
      · obtain ⟨j, b', hpos, hsup⟩ := tprop hr hc2 hK
        refine ⟨Γ.length + j, b', ?_, hsup⟩
        rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length j),
          Nat.add_sub_cancel_left]
        exact hpos
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hp, hK => by
      obtain ⟨hc1, hc2⟩ : tracePure ht = 0 ∧ tracePure hb = 0 := by
        simpa only [tracePure, Nat.add_eq_zero_iff] using hp
      have hk := tprop hb hc2 hK
      match hk with
      | ⟨0, b', hpos, hsup⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hsup with ht' | hc' | hk'
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := tprop ht hc1 (Or.inr ht')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := cprop ht (Or.inr hc')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            rcases hsup₂ with hc'' | hk''
            · refine ⟨i, b₂, ?_, Or.inr (Or.inl hc'')⟩
              rw [← hs, List.get?_append_lt hlt]
              exact hpos₂
            · refine ⟨i, b₂, ?_, Or.inr (Or.inr hk'')⟩
              rw [← hs, List.get?_append_lt hlt]
              exact hpos₂
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := kprop ht (Or.inr hk')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, Or.inr (Or.inr hsup₂)⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
      | ⟨1, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rcases hsup with ht' | hc' | hk'
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := tprop ht hc1 (Or.inl ht')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, hsup₂⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := cprop ht (Or.inl hc')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            rcases hsup₂ with hc'' | hk''
            · refine ⟨i, b₂, ?_, Or.inr (Or.inl hc'')⟩
              rw [← hs, List.get?_append_lt hlt]
              exact hpos₂
            · refine ⟨i, b₂, ?_, Or.inr (Or.inr hk'')⟩
              rw [← hs, List.get?_append_lt hlt]
              exact hpos₂
          · obtain ⟨i, b₂, hpos₂, hsup₂⟩ := kprop ht (Or.inl hk')
            have hlt : i < Γ₁.length := List.get?_some_lt hpos₂
            refine ⟨i, b₂, ?_, Or.inr (Or.inr hsup₂)⟩
            rw [← hs, List.get?_append_lt hlt]
            exact hpos₂
      | ⟨m + 2, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
          refine ⟨Γ₁.length + m, b', ?_, hsup⟩
          rw [← hs, List.get?_append_ge (Nat.le_add_right Γ₁.length m),
            Nat.add_sub_cancel_left]
          exact hpos
  | _, _, _, Typed.unit, _, hK => False.elim hK
  | _, _, _, @Typed.next _ _ _ h, hp, hK =>
      tprop h (by simpa only [tracePure] using hp) hK
  | _, _, _, @Typed.fix _ _ _ _ _, hp, _ => by
      simp only [tracePure] at hp; omega
  | _, _, _, @Typed.cons _ _ _ _ _ _ _ _, _, hK => False.elim hK
  | _, _, _, Typed.nil, hp, _ => by simp only [tracePure] at hp; omega
  | _, _, _, @Typed.snoc _ Γ Δ t u ht hu hs, hp, _ => by
      obtain ⟨hc1, hc2⟩ : tracePure ht = 0 ∧ tracePure hu = 0 := by
        simpa only [tracePure, Nat.add_eq_zero_iff] using hp
      obtain ⟨j, b', hpos, hsup⟩ := tprop ht hc1 True.intro
      refine ⟨j, b', ?_, hsup⟩
      have hlt : j < Γ.length := List.get?_some_lt hpos
      rw [← hs, List.get?_append_lt hlt]
      exact hpos
  | _, _, _, Typed.gen, _, ⟨hb, hnk⟩ => (hnk (Or.inr (Or.inr True.intro))).elim
  | _, _, _, Typed.red, _, ⟨hb, _⟩ => False.elim hb
  | _, _, _, Typed.obj, _, ⟨hb, _⟩ => False.elim hb
  | _, _, _, Typed.terminate, hp, _ => by
      simp only [tracePure] at hp; omega
  | _, _, _, @Typed.contr Γ k t τ _ h, hp, hK => by
      have hk := tprop h (by simpa only [tracePure] using hp) hK
      match hk with
      | ⟨0, b', hpos, hsup⟩ =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact ⟨0, _, List.get?_zero_cons', hsup⟩
      | ⟨1, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact ⟨0, _, List.get?_zero_cons', hsup⟩
      | ⟨m + 2, b', hpos, hsup⟩ =>
          rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
          exact ⟨m + 1, b', by rw [List.get?_succ_cons']; exact hpos, hsup⟩
  | _, _, _, @Typed.weak Γ k t τ _ h, hp, hK => by
      obtain ⟨i, b', hpos, hsup⟩ := tprop h (by simpa only [tracePure] using hp) hK
      exact ⟨i + 1, b', by rw [List.get?_succ_cons']; exact hpos, hsup⟩

/-- No trace at a no-supply context, mint-free: with no trace-hypothesis,
no content token to archive, no knower to terminate, and no mint from
nothing, the trace type is uninhabited. -/
theorem no_trace_nosupply {Γ : List Ty} {t : Term}
    (h : Typed Γ t Ty.trace) (hf : tracePure h = 0)
    (hns : ∀ (i : Nat) (b : Ty), Γ[i]? = some b → ¬ TSupply b) : False := by
  obtain ⟨i, b, hpos, hsup⟩ := tprop h hf True.intro
  exact hns i b hpos hsup

/-! ## The stream keystone: no stream without supply -/

/-! ## The stream keystone: no stream without supply -/

theorem size_pos : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ), 0 < size h := by
  intro Γ t τ h
  cases h <;> simp only [size] <;> omega

/-- Stream-need implies linearity: a stream-carrying type is linear
(`isLinear` propagates by OR/underlying and `stream` is linear). -/
theorem needsS_linear : ∀ a : Ty, NeedsS a → a.isLinear = true := by
  intro a
  induction a with
  | stream => intro _; rfl
  | content | knower | knowledge | value | trace | unit => intro h; exact False.elim h
  | later a' ih => intro h; exact ih h
  | tensor a' b' iha ihb =>
      intro h
      rcases h with h | h
      · simp [Ty.isLinear, iha h]
      · simp [Ty.isLinear, ihb h]
  | arrow a' b' iha ihb =>
      intro h
      simp [Ty.isLinear, ihb h.1]

/-- No type is its own later: finiteness of the type algebra. -/
theorem ne_later_self : ∀ a : Ty, a ≠ .later a := by
  intro a
  induction a with
  | content => intro h; exact Ty.noConfusion h
  | knower => intro h; exact Ty.noConfusion h
  | knowledge => intro h; exact Ty.noConfusion h
  | value => intro h; exact Ty.noConfusion h
  | stream => intro h; exact Ty.noConfusion h
  | trace => intro h; exact Ty.noConfusion h
  | unit => intro h; exact Ty.noConfusion h
  | later a' ih => intro h; injection h with he; exact ih he
  | tensor a' b' iha ihb => intro h; exact Ty.noConfusion h
  | arrow a' b' iha ihb => intro h; exact Ty.noConfusion h

/-- Split-piece of a no-supply context is no-supply. -/
theorem nosupply_split {E : List Ty} (hE : ∀ (i : Nat) (a : Ty), E[i]? = some a → ¬ SSupply a)
    {Γ Δ : List Ty} (hs : Γ ++ Δ = E) :
    (∀ (i : Nat) (a : Ty), Γ[i]? = some a → ¬ SSupply a) ∧ (∀ (i : Nat) (a : Ty), Δ[i]? = some a → ¬ SSupply a) := by
  constructor
  · intro i a hpos
    have hlt : i < Γ.length := List.get?_some_lt hpos
    exact hE i a (by rw [← hs, List.get?_append_lt hlt]; exact hpos)
  · intro i a hpos
    have hlt : i < Δ.length := List.get?_some_lt hpos
    refine hE (Γ.length + i) a ?_
    rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length i),
      Nat.add_sub_cancel_left]
    exact hpos

/-- Size equations (definitional), for the fuel-arithmetic. -/
theorem size_lam {Γ a b body} (h : Typed (a :: Γ) body b) :
    size (Typed.lam h) = 1 + size h := rfl
theorem size_app {E Γ Δ a b fn arg} {hf : Typed Γ fn (.arrow a b)} {ha : Typed Δ arg a}
    {hs : Γ ++ Δ = E} : size (Typed.app hf ha hs) = 1 + size hf + size ha := rfl
theorem size_pair {E Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b} {hs : Γ ++ Δ = E} :
    size (Typed.pair hl hr hs) = 1 + size hl + size hr := rfl
theorem size_lete {E Γ₁ Γ₂ a b c t body} {ht : Typed Γ₁ t (.tensor a b)}
    {hb : Typed (b :: a :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E} :
    size (Typed.lete ht hb hs) = 1 + size ht + size hb := rfl
theorem size_next {Γ a t} (h : Typed Γ t a) : size (Typed.next h) = 1 + size h := rfl
theorem size_cons {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
    {hs : Γ ++ Δ = E} : size (Typed.cons hc ht hs) = 1 + size hc + size ht := rfl
theorem size_snoc {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
    {hs : Γ ++ Δ = E} : size (Typed.snoc ht hu hs) = 1 + size ht + size hu := rfl
theorem size_contr {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false}
    (h : Typed (k :: k :: Γ) (Term.mergeAt 0 t) τ) : size (Typed.contr hk h) = 1 + size h := rfl
theorem size_weak {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false} (h : Typed Γ t τ) :
    size (Typed.weak hk h) = 1 + size h := rfl

/-- NO STREAM WITHOUT SUPPLY (fix-free): every stream-needing derivation
needs a stream-carrying or knower hypothesis. This is `sprop` with the
conclusion-side WIDENED from `τ = stream` to `NeedsS τ` — the widening
is what dissolves the producer-spine: at an application, EITHER the fn's
own type needs streams (recurse on the fn) OR the fn's domain is stream-
or knower-carrying (recurse on / kill the arg). The closed instance is
the no-closed-▷stream keystone. Fixpoints stay excluded (their case is
the self-carrier); the fix-free fragment is what the token-death
analysis needs first. -/
theorem no_stream_without_supply :
    ∀ (n : Nat), ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ), size h ≤ n →
    fixCount h = 0 → (∀ (i : Nat) (a : Ty), Γ[i]? = some a → ¬ SSupply a) → NeedsS τ → False
  | 0, _, _, _, h, hn, _, _, _ => absurd hn (Nat.not_le_of_lt (size_pos h))
  | n + 1, _, _, _, Typed.var, _, _, hns, hK =>
      hns 0 _ List.get?_zero_cons' (Or.inl hK)
  | n + 1, _, _, _, @Typed.lam Γ a b body h, hsz, hf, hns, ⟨hb, hna, hnk⟩ =>
      no_stream_without_supply n h (by rw [size_lam] at hsz; omega) hf
        (by intro (i : Nat) (b' : Ty) hpos
            cases i with
            | zero =>
                rw [List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                intro hsup
                rcases hsup with hs' | hk'
                · exact hna hs'
                · exact hnk hk'
            | succ m =>
                rw [List.get?_succ_cons'] at hpos
                exact hns m b' hpos)
        hb
  | n + 1, _, _, _, @Typed.app E Γ Δ X b fn arg hf' ha' hs, hsz, hf, hns, hK => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hf' = 0 ∧ fixCount ha' = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hf
      obtain ⟨hns1, hns2⟩ := nosupply_split hns hs
      by_cases hN : NeedsS (Ty.arrow X b)
      · exact no_stream_without_supply n hf' (by rw [size_app] at hsz; omega) hfc1 hns1 hN
      · have hdx : NeedsS X ∨ NeedsK X := by
          refine Classical.byContradiction fun hcon => ?_
          have hn1 : ¬ NeedsS X := fun x => hcon (Or.inl x)
          have hn2 : ¬ NeedsK X := fun x => hcon (Or.inr x)
          exact hN ⟨hK, hn1, hn2⟩
        rcases hdx with hx | hx
        · exact no_stream_without_supply n ha' (by rw [size_app] at hsz; omega) hfc2 hns2 hx
        · obtain ⟨i, b', hpos, hneed⟩ := kprop ha' hx
          exact hns2 i b' hpos (Or.inr hneed)
  | n + 1, _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hsz, hf, hns, hK => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hl = 0 ∧ fixCount hr = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hf
      obtain ⟨hns1, hns2⟩ := nosupply_split hns hs
      rcases hK with hK | hK
      · exact no_stream_without_supply n hl (by rw [size_pair] at hsz; omega) hfc1 hns1 hK
      · exact no_stream_without_supply n hr (by rw [size_pair] at hsz; omega) hfc2 hns2 hK
  | n + 1, _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hsz, hf, hns, hK => by
      obtain ⟨hfc1, hfc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hf
      obtain ⟨hns1, hns2⟩ := nosupply_split hns hs
      by_cases hbs : NeedsS a ∨ NeedsS b
      · exact no_stream_without_supply n ht (by rw [size_lete] at hsz; omega) hfc1 hns1 hbs
      · by_cases hbk : NeedsK a ∨ NeedsK b
        · obtain ⟨i, b', hpos, hneed⟩ := kprop ht hbk
          have hlt : i < Γ₁.length := List.get?_some_lt hpos
          exact hns1 i b' hpos (Or.inr hneed)
        · refine no_stream_without_supply n hb (by rw [size_lete] at hsz; omega) hfc2 ?_ hK
          intro (i : Nat) (b' : Ty) hpos
          cases i with
          | zero =>
              rw [List.get?_zero_cons'] at hpos
              injection hpos with he
              subst he
              intro hsup
              rcases hsup with hs' | hk'
              · exact hbs (Or.inr hs')
              · exact hbk (Or.inr hk')
          | succ m =>
              rw [List.get?_succ_cons'] at hpos
              cases m with
              | zero =>
                  rw [List.get?_zero_cons'] at hpos
                  injection hpos with he
                  subst he
                  intro hsup
                  rcases hsup with hs' | hk'
                  · exact hbs (Or.inl hs')
                  · exact hbk (Or.inl hk')
              | succ k =>
                  rw [List.get?_succ_cons'] at hpos
                  exact hns2 k b' hpos
  | n + 1, _, _, _, Typed.unit, _, _, _, hK => False.elim hK
  | n + 1, _, _, _, @Typed.next Γ a t h, hsz, hf, hns, hK =>
      no_stream_without_supply n h (by rw [size_next] at hsz; omega) hf hns hK
  | n + 1, _, _, _, @Typed.fix _ _ _ _ _, _, hf, _, _ => by
      simp only [fixCount] at hf; omega
  | n + 1, _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, hsz, hf, hns, _ => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hc = 0 ∧ fixCount ht = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hf
      obtain ⟨_, hns2⟩ := nosupply_split hns hs
      exact no_stream_without_supply n ht (by rw [size_cons] at hsz; omega) hfc2 hns2 True.intro
  | n + 1, _, _, _, Typed.nil, _, _, _, hK => False.elim hK
  | n + 1, _, _, _, @Typed.snoc _ _ _ _ _ _ _ _, _, _, _, hK => False.elim hK
  | n + 1, _, _, _, Typed.gen, _, _, _, hK => hK.2.2 True.intro
  | n + 1, _, _, _, Typed.red, _, _, _, hK => False.elim hK.1
  | n + 1, _, _, _, Typed.obj, _, _, _, hK => False.elim hK.1
  | n + 1, _, _, _, Typed.terminate, _, _, _, hK => False.elim hK.1
  | n + 1, _, _, _, @Typed.contr Γ k t τ hk h, hsz, hf, hns, hK => by
      refine no_stream_without_supply n h (by rw [size_contr] at hsz; omega) hf ?_ hK
      intro (i : Nat) (b' : Ty) hpos
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact hns 0 k List.get?_zero_cons'
      | succ m =>
          cases m with
          | zero =>
              rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
              injection hpos with he
              subst he
              exact hns 0 k List.get?_zero_cons'
          | succ k' =>
              rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
              exact hns (k' + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
  | n + 1, _, _, _, @Typed.weak Γ k t τ hk h, hsz, hf, hns, hK => by
      refine no_stream_without_supply n h (by rw [size_weak] at hsz; omega) hf ?_ hK
      intro (i : Nat) (b' : Ty) hpos
      exact hns (i + 1) b' (by rw [List.get?_succ_cons']; exact hpos)

/-- The closed keystone, fix-free: no closed term inhabits `▷ stream`
— the guarded stream is knower-sustained, and from nothing at all,
nothing flows. -/
theorem no_closed_later_stream {t : Term}
    (h : Typed [] t (.later Ty.stream)) (hf : fixCount h = 0) : False :=
  no_stream_without_supply (size h) h (Nat.le_refl _) hf (by
    intro (i : Nat) (a : Ty) hpos
    rw [List.get?_nil'] at hpos
    contradiction)
    True.intro

/-! ## The fix-case walk: fixes at non-arrow types -/

/-- Type size, for the var-kill: a fix's own `▷a`-annot is strictly
bigger than every strip/sub-part of `a` that the produce-descent
visits, so the produce can never be a bare annot-var. -/
def tySize : Ty → Nat
  | .content | .knower | .knowledge | .value | .stream | .trace | .unit => 1
  | .later a => 1 + tySize a
  | .tensor a b => 1 + tySize a + tySize b
  | .arrow a b => 1 + tySize a + tySize b

theorem tySize_pos (a : Ty) : 0 < tySize a := by
  cases a <;> simp only [tySize] <;> omega

theorem tySize_later (a : Ty) : tySize a < tySize (.later a) := by
  simp only [tySize]; omega

/-- Arrow-typed fixpoints: excluded from the walk. A fix at an ARROW
type is exactly a fix whose produce can be a λ with a token-consuming
domain (the mint-trap shape `fix @ (arrow content b)`); those need the
spend-starvation argument and stay a separate unit. Fixes at stream,
▷stream and tensor types — the ones the stream analysis is about — are
allowed. -/
def IsArrowTy : Ty → Bool
  | .arrow _ _ => true
  | _ => false

def arrowFixCount : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, @Typed.fix _ a _ _ h => (if IsArrowTy a then 1 else 0) + arrowFixCount h
  | _, _, _, @Typed.lam _ _ _ _ h => arrowFixCount h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => arrowFixCount hf + arrowFixCount ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => arrowFixCount hl + arrowFixCount hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => arrowFixCount ht + arrowFixCount hb
  | _, _, _, @Typed.next _ _ _ h => arrowFixCount h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => arrowFixCount hc + arrowFixCount ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => arrowFixCount ht + arrowFixCount hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => arrowFixCount h
  | _, _, _, @Typed.weak _ _ _ _ _ h => arrowFixCount h
  | _, _, _, _ => 0

end Dcare
