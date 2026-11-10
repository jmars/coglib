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
  /-- The DIRECT-premise bases (a path must be able to start: without
  these the relation is empty — every constructor wrapped another `Sub`,
  so nothing was ever a subderivation of anything). -/
  | lamD {Γ a b body} {h : Typed (a :: Γ) body b} : Sub (Typed.lam h) h
  | appLD {E Γ Δ a b fn arg} {hf : Typed Γ fn (.arrow a b)} {ha : Typed Δ arg a}
      {hs : Γ ++ Δ = E} : Sub (Typed.app hf ha hs) hf
  | appRD {E Γ Δ a b fn arg} {hf : Typed Γ fn (.arrow a b)} {ha : Typed Δ arg a}
      {hs : Γ ++ Δ = E} : Sub (Typed.app hf ha hs) ha
  | pairLD {E Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} : Sub (Typed.pair hl hr hs) hl
  | pairRD {E Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} : Sub (Typed.pair hl hr hs) hr
  | leteTD {E Γ₁ Γ₂ a b c t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E} :
      Sub (Typed.lete ht hb hs) ht
  | leteBD {E Γ₁ Γ₂ a b c t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E} :
      Sub (Typed.lete ht hb hs) hb
  | nextD {Γ a t} {h : Typed Γ t a} : Sub (Typed.next h) h
  | fixD {Γ a body} {hΓ : AllNonLinear Γ} {h : Typed Γ body (.arrow (.later a) a)} :
      Sub (Typed.fix hΓ h) h
  | consHD {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} : Sub (Typed.cons hc ht hs) hc
  | consTD {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} : Sub (Typed.cons hc ht hs) ht
  | snocTD {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} : Sub (Typed.snoc ht hu hs) ht
  | snocUD {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} : Sub (Typed.snoc ht hu hs) hu
  | contrD {Γ k t τ} {hk : k.isLinear = false} {h : Typed (k :: k :: Γ) (Term.mergeAt 0 t) τ} :
      Sub (Typed.contr hk h) h
  | weakD {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false}
      {h : Typed Γ t τ} : Sub (Typed.weak hk h) h

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
  | lamD => simp only [size]; omega
  | appLD => simp only [size]; omega
  | appRD => simp only [size]; omega
  | pairLD => simp only [size]; omega
  | pairRD => simp only [size]; omega
  | leteTD => simp only [size]; omega
  | leteBD => simp only [size]; omega
  | nextD => simp only [size]; omega
  | fixD => simp only [size]; omega
  | consHD => simp only [size]; omega
  | consTD => simp only [size]; omega
  | snocTD => simp only [size]; omega
  | snocUD => simp only [size]; omega
  | contrD => simp only [size]; omega
  | weakD => simp only [size]; omega

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

/-! ## The closed-liveness base (ascent foundations) -/

/-- No closed stream exists — the barren world (stream ↦ False) in one
line. Streams are knower-sustained; from nothing, nothing flows. -/
theorem no_closed_stream {t : Term} (h : Typed [] t Ty.stream) : False :=
  (sound h True.intro).elim

/-- No closed knowledge: knowledge is reduction's output, and reduction
reads only the live stream. -/
theorem no_closed_knowledge {t : Term} (h : Typed [] t Ty.knowledge) : False :=
  (sound h True.intro).elim

/-- No closed value: valuation reads only the live stream. -/
theorem no_closed_value {t : Term} (h : Typed [] t Ty.value) : False :=
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

/-- The trace-budget extraction, Σ-to-∃: if no spent position of the
context carries a positive trace-weight, the whole weighted spend is
non-positive. The contrapositive is the ORIGIN lemma — a positive
trace-spend REQUIRES a spent trace-carrying position. -/
theorem wSpendFrom_nonpos :
    ∀ (w : Ty → Int) (base : Nat) (Γ : List Ty) (u : Nat → Nat),
    (∀ (i : Nat) (a : Ty), Γ[i]? = some a → (u (base + i) : Int) * w a ≤ 0) →
    wSpendFrom w base Γ u ≤ 0
  | _, _, [], _, _ => by simp only [wSpendFrom]; omega
  | w, base, a :: Γ', u, hcon => by
      have hhead : (u base : Int) * w a ≤ 0 := by
        have := hcon 0 a (List.get?_zero_cons')
        simpa only [Nat.add_zero] using this
      have htail := wSpendFrom_nonpos w (base + 1) Γ' u (fun (i : Nat) (a' : Ty) hpos => by
        have hh := hcon (i + 1) a' (by simpa only [List.get?_succ_cons'] using hpos)
        have hidx : base + 1 + i = base + (i + 1) := by omega
        rw [← hidx] at hh
        exact hh)
      simp only [wSpendFrom]
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

theorem size_fix {Γ : List Ty} {a : Ty} {body : Term} {hΓ : AllNonLinear Γ}
    (h : Typed Γ body (.arrow (.later a) a)) :
    size (Typed.fix hΓ h) = 1 + size h := rfl

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

/-! ## The measured boundary: binder-level killers (negative result) -/

/-- The killer-for-content type: consumes a content token, returns unit. -/
def ACU : Ty := .arrow .content .unit

/-- The (A′)-shaped statement "unit/EndsInUnit at a token-context with no
killer-HYPOTHESES is impossible" is FALSE, and this is the witness: the
killer enters as a λ-DOMAIN — a freely written annotation — not as a
context hypothesis. The body fires it on the token, perfectly legally.

  λ(k : arrow content unit). app (var 0) (var 0)
    : arrow (arrow content unit) unit   at [content]

Consequence (measured, do not re-derive): the no-killer condition must
hold at the BINDER level (no killer-shaped λ-domain or lete-component
anywhere in the derivation), and discharging THAT condition at a
`[content] ⊢ unit` root is exactly the ascent: killer-domains are free
to write, so the theorem must show their values cannot die in a
unit-rooted tree — their deaths are fires needing arguments of ever
deeper annotated types, bottoming at closed values, all of which are
dead (no closed content/knower/stream/▷stream; no nil/terminate in a
mint-free tree). The same ascent covers the ▷stream-annotation
smugglers and the producer-spine: the three onion layers are ONE lemma.
-/
def killerBinder : Term := .lam ACU (.app (.var 0) (.var 0))

def killerBinderTyped : Typed [Ty.content] killerBinder (.arrow ACU .unit) :=
  Typed.lam
    (Typed.app (Γ := [ACU]) (Δ := [Ty.content]) Typed.var Typed.var rfl)

/-- Unit AT a killer-carrying context: the no-killer-hypothesis condition
is load-bearing and cannot be dropped — the body of the witness above. -/
theorem unit_at_killer_context :
    ∃ t, Nonempty (Typed [ACU, Ty.content] t Ty.unit) :=
  ⟨.app (.var 0) (.var 0), ⟨Typed.app (Γ := [ACU]) (Δ := [Ty.content])
    Typed.var Typed.var rfl⟩⟩

/-- And the witness itself: a killer-for-content VALUES exist at a
token context with no killer hypothesis in sight — the killer is the
annotation, and annotations are free. -/
theorem killer_binder_witness :
    ∃ t, Nonempty (Typed [Ty.content] t (.arrow ACU .unit)) :=
  ⟨killerBinder, ⟨killerBinderTyped⟩⟩

/-! ## The conditional kill: unit/inert conclusions at token contexts -/

/-- Fully inert: no live subtype ANYWHERE, domains included. Content,
trace, stream, knower and ▷-of-live are live; knowledge, value and unit
are inert; tensors and arrows are inert iff both parts are. This one
predicate subsumes the no-killer, no-smuggler and no-annotation
conditions of the earlier attempts: a killer's type contains its token
in the domain, a smuggler's contains ▷stream, an annotation-supply
contains its live payload. -/
def allInert : Ty → Bool
  | .content | .trace | .stream | .knower => false
  | .knowledge | .value | .unit => true
  | .later a => allInert a
  | .tensor a b | .arrow a b => allInert a && allInert b

/-- Ends-in-inert: an arrow-spine whose eventual codomain is inert.
unit itself is the degenerate spine. -/
def endsInInert : Ty → Bool
  | .arrow _ σ => endsInInert σ
  | τ => allInert τ

/-- The spine has a content domain somewhere: the producers whose fire
consumes the token. -/
def hasContentDomain : Ty → Bool
  | .arrow a σ => (a == Ty.content) || hasContentDomain σ
  | _ => false

/-- A hypothesis is OK for the clean context: the token itself, or
fully inert. -/
def binderOK (a : Ty) : Bool := (a == Ty.content) || allInert a

/-- The spine has a KILL domain: a content domain (the token-fire) or a
live domain (excluded from hypotheses by CleanCtx and from binders by
liveBind — so a producer with a kill domain must bottom at a λ whose
binder is the token or at a banned hypothesis). -/
def hasKillDomain : Ty → Bool
  | .arrow a σ => (a == Ty.content) || (!binderOK a) || hasKillDomain σ
  | _ => false

/-- Clean context: every hypothesis is the token or fully inert. -/
def CleanCtx (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (b : Ty), Γ[i]? = some b → binderOK b = true

/-- Live binders: λ-domains and lete-components that are neither the
token nor inert. The conditional kill assumes ZERO of these; discharging
that at a `[content]`-rooted tree is the ascent (the annotation-values'
death-chase), and is the residual unit. -/
def liveBind : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, @Typed.lam _ a _ _ h =>
      (if binderOK a then 0 else 1) + liveBind h
  | _, _, _, @Typed.lete _ _ _ a b _ _ _ ht hb _ =>
      (if binderOK a then 0 else 1) + (if binderOK b then 0 else 1)
        + liveBind ht + liveBind hb
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => liveBind hf + liveBind ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => liveBind hl + liveBind hr
  | _, _, _, @Typed.next _ _ _ h => liveBind h
  | _, _, _, @Typed.fix _ _ _ _ h => liveBind h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => liveBind hc + liveBind ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => liveBind ht + liveBind hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => liveBind h
  | _, _, _, @Typed.weak _ _ _ _ _ h => liveBind h
  | _, _, _, _ => 0

/-- Trace mints: nil and terminate nodes (a trace from nothing). -/
def mintCount : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, Typed.nil => 1
  | _, _, _, Typed.terminate => 1
  | _, _, _, @Typed.lam _ _ _ _ h => mintCount h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => mintCount hf + mintCount ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => mintCount hl + mintCount hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => mintCount ht + mintCount hb
  | _, _, _, @Typed.next _ _ _ h => mintCount h
  | _, _, _, @Typed.fix _ _ _ _ h => mintCount h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => mintCount hc + mintCount ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => mintCount ht + mintCount hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => mintCount h
  | _, _, _, @Typed.weak _ _ _ _ _ h => mintCount h
  | _, _, _, _ => 0

/-! ## The trace family: no archival at clean contexts -/

/-- Inert types carry no trace-demand and no knower-demand. -/
theorem allInert_notNeedsT : ∀ a : Ty, allInert a = true → NeedsT a → False := by
  intro a
  induction a with
  | content | knower | knowledge | value | stream | unit => intro _ h; exact h
  | trace => intro hi _; exact Bool.noConfusion hi
  | later a' ih => intro hi h; exact ih hi h
  | tensor a' b' iha ihb =>
      intro hi h
      rcases h with h | h
      · exact iha (by simp [allInert] at hi; exact hi.1) h
      · exact ihb (by simp [allInert] at hi; exact hi.2) h
  | arrow a' b' iha ihb =>
      intro hi h
      exact ihb (by simp [allInert] at hi; exact hi.2) h.1

theorem allInert_notNeedsK : ∀ a : Ty, allInert a = true → NeedsK a → False := by
  intro a
  induction a with
  | content | knowledge | value | stream | unit | trace => intro _ h; exact h
  | knower => intro hi _; exact Bool.noConfusion hi
  | later a' _ => intro _ h; exact h
  | tensor a' b' iha ihb =>
      intro hi h
      rcases h with h | h
      · exact iha (by simp [allInert] at hi; exact hi.1) h
      · exact ihb (by simp [allInert] at hi; exact hi.2) h
  | arrow a' b' iha ihb =>
      intro hi h
      exact ihb (by simp [allInert] at hi; exact hi.2) h.1

/-- A clean hypothesis is neither trace- nor knower-carrying: the token
itself carries neither demand, and inert types carry none. -/
theorem binderOK_notNeedsT {a : Ty} (hb : binderOK a = true) (h : NeedsT a) : False := by
  by_cases hac : a = Ty.content
  · subst hac; exact h
  · have hq : (a == Ty.content) = false := by
      rcases Bool.eq_false_or_eq_true (a == Ty.content) with h1 | h1
      · exact absurd (eq_of_beq h1) hac
      · exact h1
    rw [binderOK, hq, Bool.false_or] at hb
    exact allInert_notNeedsT _ hb h

theorem binderOK_notNeedsK {a : Ty} (hb : binderOK a = true) (h : NeedsK a) : False := by
  by_cases hac : a = Ty.content
  · subst hac; exact h
  · have hq : (a == Ty.content) = false := by
      rcases Bool.eq_false_or_eq_true (a == Ty.content) with h1 | h1
      · exact absurd (eq_of_beq h1) hac
      · exact h1
    rw [binderOK, hq, Bool.false_or] at hb
    exact allInert_notNeedsK _ hb h

/-- Clean contexts split cleanly. -/
theorem cleanctx_split {E : List Ty} (hcc : CleanCtx E) {Γ Δ : List Ty} (hs : Γ ++ Δ = E) :
    CleanCtx Γ ∧ CleanCtx Δ := by
  constructor
  · intro i b hpos
    have hlt : i < Γ.length := List.get?_some_lt hpos
    exact hcc i b (by rw [← hs, List.get?_append_lt hlt]; exact hpos)
  · intro i b hpos
    have hlt : i < Δ.length := List.get?_some_lt hpos
    refine hcc (Γ.length + i) b ?_
    rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length i), Nat.add_sub_cancel_left]
    exact hpos

/-- The domain carries content somewhere (the token-fire or a
positive-position content-carrying domain). -/
def CarriesContent (a : Ty) : Prop := a = Ty.content ∨ NeedsC a

def HasTokenDomain : Ty → Prop
  | .arrow a σ => CarriesContent a ∨ HasTokenDomain σ
  | _ => False

/-- Inert types ban content everywhere, so content-need contradicts. -/
theorem needsC_notallInert : ∀ a : Ty, NeedsC a → allInert a = false := by
  intro a
  induction a with
  | content => intro _; rfl
  | knower | knowledge | value | stream | trace | unit => intro h; exact h.elim
  | later a' _ => intro h; exact h.elim
  | tensor a' b' iha ihb =>
      intro h
      rcases h with h | h
      · simp only [allInert, iha h, Bool.false_and]
      · simp only [allInert, ihb h, Bool.and_false]
  | arrow a' b' iha ihb =>
      intro h
      simp only [allInert, ihb h.1, Bool.and_false]

/-- A token-domain spine is never inert. -/
theorem hasTokenDomain_notallInert : ∀ τ : Ty, HasTokenDomain τ → allInert τ = false := by
  intro τ
  cases τ with
  | arrow a σ =>
      intro hcar
      rcases hcar with hc | hs
      · rcases hc with rfl | hnc
        · simp [allInert]
        · simp [allInert, needsC_notallInert _ hnc]
      · simp [allInert, hasTokenDomain_notallInert _ hs]
  | content | knower | knowledge | value | stream | trace | unit | later _ | tensor _ _ =>
      intro h
      exact False.elim h

/-- Live-binder inversion for λ. -/
theorem liveBind_lam_inv {Γ : List Ty} {a b : Ty} {body : Term} (h : Typed (a :: Γ) body b)
    (hl : liveBind (Typed.lam h) = 0) : binderOK a = true ∧ liveBind h = 0 := by
  simp only [liveBind] at hl
  by_cases hb : binderOK a = true
  · rw [if_pos hb] at hl
    exact ⟨hb, by omega⟩
  · rw [if_neg hb] at hl
    omega

/-- Live-binder inversion for lete. -/
theorem liveBind_lete_inv {E Γ₁ Γ₂ : List Ty} {a b c : Ty} {t body : Term}
    {ht : Typed Γ₁ t (.tensor a b)}
    {hb : Typed (b :: a :: Γ₂) body c} (hs : Γ₁ ++ Γ₂ = E)
    (hl : liveBind (Typed.lete ht hb hs) = 0) :
    binderOK a = true ∧ binderOK b = true ∧ liveBind ht = 0 ∧ liveBind hb = 0 := by
  simp only [liveBind] at hl
  by_cases h1 : binderOK a = true
  · rw [if_pos h1] at hl
    by_cases h2 : binderOK b = true
    · rw [if_pos h2] at hl
      exact ⟨h1, h2, by omega, by omega⟩

    · rw [if_neg h2] at hl
      omega
  · rw [if_neg h1] at hl
    omega

/-- The token can flow through this type's fire: some domain in the
spine IS content, content-needing, or itself a token-consumer (the
extension — the identity on `arrow content content` consumes tokens
without `CarriesContent` seeing it). -/
def TokenThrough : Ty → Prop
  | .arrow a σ => (a = Ty.content ∨ NeedsC a ∨ HasTokenDomain a) ∨ TokenThrough σ
  | _ => False

/-- A token-through type is never inert — some domain in its spine is
live, and domains are inside `allInert`'s conjunction. -/
theorem tokenThrough_notallInert : ∀ τ : Ty, TokenThrough τ → allInert τ = false := by
  intro τ
  induction τ with
  | content | knower | knowledge | value | stream | trace | unit => intro h; exact h.elim
  | later a' _ => intro h; exact h.elim
  | tensor a' b' _ _ => intro h; exact h.elim
  | arrow a' b' iha ihb =>
      intro h
      rcases h with h | h
      · rcases h with rfl | h | h
        · simp [allInert]
        · simp [allInert, needsC_notallInert _ h]
        · simp [allInert, hasTokenDomain_notallInert _ h]
      · simp [allInert, ihb h]

/-- DEEP-CONSUME: the TRANSITIVE CLOSURE of token consumption — some
domain in the spine, AT ANY DEPTH (domains of domains included), is,
carries, or consumes the token. `TokenThrough` recurses transitively
through codomains but only ONE level into domains; `DeepConsume` closes
the lattice (obs 50: a two-level consumer — `arrow (arrow content unit)
unit` — is `TokenThrough`-true and `HasTokenDomain`-false; only the
closure sees it). -/
def DeepConsume : Ty → Prop
  | .arrow a σ => (a = Ty.content ∨ NeedsC a ∨ DeepConsume a) ∨ DeepConsume σ
  | _ => False

theorem deepConsume_notallInert : ∀ τ : Ty, DeepConsume τ → allInert τ = false := by
  intro τ
  induction τ with
  | content | knower | knowledge | value | stream | trace | unit => intro h; exact h.elim
  | later a' _ => intro h; exact h.elim
  | tensor a' b' _ _ => intro h; exact h.elim
  | arrow a' b' iha ihb =>
      intro h
      rcases h with h | h
      · rcases h with rfl | h | h
        · simp [allInert]
        · simp [allInert, needsC_notallInert _ h]
        · simp [allInert, iha h]
      · simp [allInert, ihb h]

theorem hasTokenDomain_deepConsume : ∀ τ : Ty, HasTokenDomain τ → DeepConsume τ := by
  intro τ
  induction τ with
  | content | knower | knowledge | value | stream | trace | unit | later _ | tensor _ _ =>
      intro h; exact h.elim
  | arrow a' b' _ ihb =>
      intro h
      rcases h with h | h
      · rcases h with rfl | h
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr (ihb h)

theorem tokenThrough_deepConsume : ∀ τ : Ty, TokenThrough τ → DeepConsume τ := by
  intro τ
  induction τ with
  | content | knower | knowledge | value | stream | trace | unit | later _ | tensor _ _ =>
      intro h; exact h.elim
  | arrow a' b' iha ihb =>
      intro h
      rcases h with h | h
      · rcases h with rfl | h | h
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr (hasTokenDomain_deepConsume _ h)))
      · exact Or.inr (ihb h)

theorem deepConsume_notbinderOK {τ : Ty} (h : DeepConsume τ) : binderOK τ = false := by
  have hai := deepConsume_notallInert τ h
  rcases Bool.eq_false_or_eq_true (binderOK τ) with h1 | h1
  · exfalso
    rw [binderOK] at h1
    rcases Bool.eq_false_or_eq_true (τ == Ty.content) with h2 | h2
    · exact absurd (eq_of_beq h2) (fun hc => by rw [hc] at h; exact h.elim)
    · rw [h2, Bool.false_or] at h1
      rw [hai] at h1
      exact Bool.noConfusion h1
  · exact h1

/-! ## Extraction: the type-preserving producer walk -/

/-- EXTRACTION: a fix-free, mint-free, live-binder-free producer of an
arrow-type with a content-carrying domain bottoms at a λ whose binder is
EXACTLY that domain — the produce-body, returned with a clean context and
zero counters. TYPE-PRESERVATION is the whole trick (obs 36): the walked
type IS the invariant, so the spine needs no conjunction re-derivation —
the same move that widened `no_stream_without_supply` past the
producer-spine. The binder-exact form is what the kill's content-row
needs: the token lands at position 0 of the returned context.

Every extraction path terminates at a `lam` of the ORIGINAL type: the
app-spine's double descent returns a produce of `arrow Y σ` and extracts
THAT at the original type; lete descends into a body of the same type;
contr/weak pass the inner result through (the statement asks nothing
about the input context). -/
def extract_produce :
    ∀ (n : Nat), ∀ {Γ : List Ty} {Y σ : Ty} {τ : Ty} {f : Term} (h : Typed Γ f τ),
    size h ≤ n → τ = .arrow Y σ → DeepConsume (.arrow Y σ) → fixCount h = 0 →
    mintCount h = 0 → liveBind h = 0 → CleanCtx Γ →
    ∃ (Γ' : List Ty) (t' : Term) (h' : Typed (Y :: Γ') t' σ),
      size h' ≤ n ∧ CleanCtx (Y :: Γ') ∧ fixCount h' = 0 ∧ mintCount h' = 0 ∧
      liveBind h' = 0
  | 0, _, _, _, _, _, h, hn, _, _, _, _, _, _ =>
      absurd hn (Nat.not_le_of_lt (size_pos h))
  | n + 1, _, _, _, _, _, Typed.var, _, heq, hdom, _, _, _, hcc => by
      cases heq
      have hai := deepConsume_notallInert _ hdom
      have hbo := hcc 0 _ List.get?_zero_cons'
      rw [binderOK, hai, Bool.or_false] at hbo
      exact Ty.noConfusion (eq_of_beq hbo)
  | n + 1, _, _, _, _, _, @Typed.lam Γ a b body h, hsz, heq, hdom, hfc, hmc,
      hlb, hcc => by
      injection heq with h1 h2
      subst h1
      subst h2
      obtain ⟨hbY, hlb1⟩ := liveBind_lam_inv h hlb
      refine ⟨_, _, h, ?_, ?_, ?_, ?_, hlb1⟩
      · rw [size_lam] at hsz; omega
      · intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hbY
        | succ m =>
            rw [List.get?_succ_cons'] at hpos
            exact hcc m b' hpos
      · simpa only [fixCount] using hfc
      · simpa only [mintCount] using hmc
  | n + 1, _, _, _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hsz, heq, hdom,
      hfc, hmc, hlb, hcc => by
      subst heq
      obtain ⟨hfc1, _⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, _⟩ : mintCount hf = 0 ∧ mintCount ha = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hlb1, _⟩ : liveBind hf = 0 ∧ liveBind ha = 0 := by
        simpa only [liveBind, Nat.add_eq_zero_iff] using hlb
      have hszf : size hf ≤ n := by rw [size_app] at hsz; omega
      obtain ⟨hcc1, _⟩ := cleanctx_split hcc hs
      obtain ⟨Γ₁, t₁, h₁, hs1, hc1, hf1, hm1, hl1⟩ :=
        extract_produce n hf hszf rfl (Or.inr hdom) hfc1 hmc1 hlb1 hcc1
      obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hl2⟩ :=
        extract_produce n h₁ hs1 rfl hdom hf1 hm1 hl1 hc1
      exact ⟨Γ', t', h', by omega, hc2, hf2, hm2, hl2⟩
  | n + 1, _, _, _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, _, heq, _, _, _,
      _, _ => by
      exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hsz, heq,
      hdom, hfc, hmc, hlb, hcc => by
      subst heq
      obtain ⟨hba, hbb, _, hlb2⟩ := liveBind_lete_inv hs hlb
      obtain ⟨_, hfc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨_, hmc2⟩ : mintCount ht = 0 ∧ mintCount hb = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨_, hcc2⟩ := cleanctx_split hcc hs
      have hszb : size hb ≤ n := by rw [size_lete] at hsz; omega
      have hccb : CleanCtx (b :: a :: Γ₂) := by
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hbb
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hba
            | succ k =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc2 k b' hpos
      obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hl2⟩ :=
        extract_produce n hb hszb rfl hdom hfc2 hmc2 hlb2 hccb
      exact ⟨Γ', t', h', by omega, hc2, hf2, hm2, hl2⟩
  | n + 1, _, _, _, _, _, Typed.unit, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, @Typed.next Γ a t h, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, @Typed.fix _ a body hΓ h, _, heq, hdom, hfc, _, _, _ => by
      cases heq
      exact absurd hfc (by simp only [fixCount]; omega)
  | n + 1, _, _, _, _, _, Typed.cons hc ht hs, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, Typed.nil, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, Typed.snoc ht hu hs, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, Typed.gen, _, heq, hdom, _, _, _, _ => by
      injection heq with h1 h2
      subst h1
      subst h2
      simp only [DeepConsume] at hdom
      rcases hdom with h | h
      · rcases h with h | h | h
        · exact Ty.noConfusion h
        · exact h.elim
        · exact h.elim
      · exact h.elim
  | n + 1, _, _, _, _, _, Typed.red, _, heq, hdom, _, _, _, _ => by
      injection heq with h1 h2
      subst h1
      subst h2
      simp only [DeepConsume] at hdom
      rcases hdom with h | h
      · rcases h with h | h | h
        · exact Ty.noConfusion h
        · exact h.elim
        · exact h.elim
      · exact h.elim
  | n + 1, _, _, _, _, _, Typed.obj, _, heq, hdom, _, _, _, _ => by
      injection heq with h1 h2
      subst h1
      subst h2
      simp only [DeepConsume] at hdom
      rcases hdom with h | h
      · rcases h with h | h | h
        · exact Ty.noConfusion h
        · exact h.elim
        · exact h.elim
      · exact h.elim
  | n + 1, _, _, _, _, _, Typed.terminate, _, heq, hdom, _, _, _, _ => by
      injection heq with h1 h2
      subst h1
      subst h2
      simp only [DeepConsume] at hdom
      rcases hdom with h | h
      · rcases h with h | h | h
        · exact Ty.noConfusion h
        · exact h.elim
        · exact h.elim
      · exact h.elim
  | n + 1, _, _, _, _, _, @Typed.contr Γ k t τ hk h, hsz, heq, hdom, hfc, hmc,
      hlb, hcc => by
      subst heq
      have hccc : CleanCtx (k :: k :: Γ) := by
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hcc 0 _ List.get?_zero_cons'
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hcc 0 _ List.get?_zero_cons'
            | succ m' =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc (m' + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hl2⟩ :=
        extract_produce n h (by rw [size_contr] at hsz; omega) rfl hdom
          (by simpa only [fixCount] using hfc) (by simpa only [mintCount] using hmc)
          (by simpa only [liveBind] using hlb) hccc
      exact ⟨Γ', t', h', by omega, hc2, hf2, hm2, hl2⟩
  | n + 1, _, _, _, _, _, @Typed.weak Γ k t τ hk h, hsz, heq, hdom, hfc, hmc,
      hlb, hcc => by
      subst heq
      have hccp : CleanCtx Γ := by
        intro (i : Nat) (b' : Ty) hpos
        exact hcc (i + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hl2⟩ :=
        extract_produce n h (by rw [size_weak] at hsz; omega) rfl hdom
          (by simpa only [fixCount] using hfc) (by simpa only [mintCount] using hmc)
          (by simpa only [liveBind] using hlb) hccp
      exact ⟨Γ', t', h', by omega, hc2, hf2, hm2, hl2⟩

/-- NO TRACE AT CLEAN: the no-archival theorem. In the liveBind-clean
fix-free mint-free fragment, NO trace-needing conclusion exists at a
clean context — every trace-spine bottoms at a banned λ-domain (liveBind),
a banned hypothesis (CleanCtx), a mint (nil/terminate), or a fixpoint.
The app-case is obs 36's repaired three-branch analysis: with `NeedsT b`
on the table, `¬NeedsT (arrow X b)` IS the three-way disjunction over X's
needs — the NeedsC branch extracts the producer and recurses on the
produce-body with the invoking node's own `NeedsT b`. -/
theorem no_trace_at_clean :
    ∀ (n : Nat), ∀ {Γ : List Ty} {τ : Ty} {t : Term} (h : Typed Γ t τ),
    size h ≤ n → fixCount h = 0 → mintCount h = 0 → liveBind h = 0 →
    CleanCtx Γ → NeedsT τ → False
  | 0, _, _, _, h, hn, _, _, _, _, _ => absurd hn (Nat.not_le_of_lt (size_pos h))
  | n + 1, _, _, _, Typed.var, _, _, _, _, hcc, hK =>
      binderOK_notNeedsT (hcc 0 _ List.get?_zero_cons') hK
  | n + 1, _, _, _, @Typed.lam Γ a b body h, hsz, hfc, hmc, hlb, hcc,
      ⟨hb, hneg⟩ => by
      obtain ⟨hbY, hlb1⟩ := liveBind_lam_inv h hlb
      refine no_trace_at_clean n h (by rw [size_lam] at hsz; omega) ?_ ?_ hlb1 ?_ hb
      · simpa only [fixCount] using hfc
      · simpa only [mintCount] using hmc
      · intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hbY
        | succ m =>
            rw [List.get?_succ_cons'] at hpos
            exact hcc m b' hpos
  | n + 1, _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hsz, hfc, hmc, hlb,
      hcc, hK => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hf = 0 ∧ mintCount ha = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hlb1, hlb2⟩ : liveBind hf = 0 ∧ liveBind ha = 0 := by
        simpa only [liveBind, Nat.add_eq_zero_iff] using hlb
      obtain ⟨hcc1, hcc2⟩ := cleanctx_split hcc hs
      by_cases hN : NeedsT (Ty.arrow X b)
      · exact no_trace_at_clean n hf (by rw [size_app] at hsz; omega) hfc1 hmc1 hlb1
          hcc1 hN
      · have hdx : NeedsT X ∨ NeedsC X ∨ NeedsK X :=
          Classical.byContradiction fun hcon =>
            hN ⟨hK, fun hd => hcon hd⟩
        rcases hdx with hx | hx | hx
        · exact no_trace_at_clean n ha (by rw [size_app] at hsz; omega) hfc2 hmc2 hlb2
            hcc2 hx
        · obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hl2⟩ :=
            extract_produce n hf (by rw [size_app] at hsz; omega) rfl
              (by simp only [DeepConsume]; left; right; left; exact hx) hfc1 hmc1 hlb1 hcc1
          exact no_trace_at_clean n h' hs2 hf2 hm2 hl2 hc2 hK
        · obtain ⟨i, b', hpos, hneed⟩ := kprop ha hx
          exact binderOK_notNeedsK (hcc2 i b' hpos) hneed
  | n + 1, _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hsz, hfc, hmc, hlb,
      hcc, hK => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hl = 0 ∧ fixCount hr = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hl = 0 ∧ mintCount hr = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hlb1, hlb2⟩ : liveBind hl = 0 ∧ liveBind hr = 0 := by
        simpa only [liveBind, Nat.add_eq_zero_iff] using hlb
      obtain ⟨hcc1, hcc2⟩ := cleanctx_split hcc hs
      rcases hK with hK | hK
      · exact no_trace_at_clean n hl (by rw [size_pair] at hsz; omega) hfc1 hmc1 hlb1
          hcc1 hK
      · exact no_trace_at_clean n hr (by rw [size_pair] at hsz; omega) hfc2 hmc2 hlb2
          hcc2 hK
  | n + 1, _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hsz, hfc, hmc,
      hlb, hcc, hK => by
      obtain ⟨hba, hbb, hlb1, hlb2⟩ := liveBind_lete_inv hs hlb
      obtain ⟨hfc1, hfc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount ht = 0 ∧ mintCount hb = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hcc1, hcc2⟩ := cleanctx_split hcc hs
      by_cases hbs : NeedsT a ∨ NeedsT b
      · exact no_trace_at_clean n ht (by rw [size_lete] at hsz; omega) hfc1 hmc1 hlb1
          hcc1 hbs
      · refine no_trace_at_clean n hb (by rw [size_lete] at hsz; omega) hfc2 hmc2 hlb2
          ?_ hK
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hbb
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hba
            | succ k =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc2 k b' hpos
  | n + 1, _, _, _, Typed.unit, _, _, _, _, _, hK => False.elim hK
  | n + 1, _, _, _, @Typed.next Γ a t h, hsz, hfc, hmc, hlb, hcc, hK =>
      no_trace_at_clean n h (by rw [size_next] at hsz; omega) hfc hmc hlb hcc hK
  | n + 1, _, _, _, @Typed.fix _ _ _ _ _, _, hfc, _, _, _, _ =>
      absurd hfc (by simp only [fixCount]; omega)
  | n + 1, _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, _, _, _, _, _, hK =>
      False.elim hK
  | n + 1, _, _, _, Typed.nil, _, _, hmc, _, _, _ =>
      absurd hmc (by simp only [mintCount]; omega)
  | n + 1, _, _, _, @Typed.snoc E Γ Δ t u ht hu hs, hsz, hfc, hmc, hlb, hcc, _ => by
      obtain ⟨hfc1, _⟩ : fixCount ht = 0 ∧ fixCount hu = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, _⟩ : mintCount ht = 0 ∧ mintCount hu = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hlb1, _⟩ : liveBind ht = 0 ∧ liveBind hu = 0 := by
        simpa only [liveBind, Nat.add_eq_zero_iff] using hlb
      obtain ⟨hcc1, _⟩ := cleanctx_split hcc hs
      exact no_trace_at_clean n ht (by rw [size_snoc] at hsz; omega) hfc1 hmc1 hlb1
        hcc1 True.intro
  | n + 1, _, _, _, Typed.gen, _, _, _, _, _, hK => hK.2 (Or.inr (Or.inr True.intro))
  | n + 1, _, _, _, Typed.red, _, _, _, _, _, hK => False.elim hK.1
  | n + 1, _, _, _, Typed.obj, _, _, _, _, _, hK => False.elim hK.1
  | n + 1, _, _, _, Typed.terminate, _, _, _, _, _, hK =>
      hK.2 (Or.inr (Or.inr True.intro))
  | n + 1, _, _, _, @Typed.contr Γ k t τ hk h, hsz, hfc, hmc, hlb, hcc, hK => by
      have hccc : CleanCtx (k :: k :: Γ) := by
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hcc 0 _ List.get?_zero_cons'
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hcc 0 _ List.get?_zero_cons'
            | succ m' =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc (m' + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      exact no_trace_at_clean n h (by rw [size_contr] at hsz; omega)
        (by simpa only [fixCount] using hfc) (by simpa only [mintCount] using hmc)
        (by simpa only [liveBind] using hlb) hccc hK
  | n + 1, _, _, _, @Typed.weak Γ k t τ hk h, hsz, hfc, hmc, hlb, hcc, hK => by
      have hccp : CleanCtx Γ := by
        intro (i : Nat) (b' : Ty) hpos
        exact hcc (i + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      exact no_trace_at_clean n h (by rw [size_weak] at hsz; omega)
        (by simpa only [fixCount] using hfc) (by simpa only [mintCount] using hmc)
        (by simpa only [liveBind] using hlb) hccp hK

/-! ## The kill: no inert-ending value swallows the token -/

/-- Inert types carry no stream-demand (the `allInert_notNeedsT`
template; `NeedsS`'s arrow-case is a triple conjunction, `.1` carries
the codomain). -/
theorem allInert_notNeedsS : ∀ a : Ty, allInert a = true → NeedsS a → False := by
  intro a
  induction a with
  | content | knower | knowledge | value | unit => intro _ h; exact h
  | stream | trace => intro hi _; exact Bool.noConfusion hi
  | later a' ih => intro hi h; exact ih hi h
  | tensor a' b' iha ihb =>
      intro hi h
      rcases h with h | h
      · exact iha (by simp [allInert] at hi; exact hi.1) h
      · exact ihb (by simp [allInert] at hi; exact hi.2) h
  | arrow a' b' iha ihb =>
      intro hi h
      exact ihb (by simp [allInert] at hi; exact hi.2) h.1

/-- A clean hypothesis carries no stream-demand either. -/
theorem binderOK_notNeedsS {a : Ty} (hb : binderOK a = true) (h : NeedsS a) : False := by
  by_cases hac : a = Ty.content
  · subst hac; exact h
  · have hq : (a == Ty.content) = false := by
      rcases Bool.eq_false_or_eq_true (a == Ty.content) with h1 | h1
      · exact absurd (eq_of_beq h1) hac
      · exact h1
    rw [binderOK, hq, Bool.false_or] at hb
    exact allInert_notNeedsS _ hb h

/-- Inert types end in inert. -/
theorem allInert_endsInInert : ∀ a : Ty, allInert a = true → endsInInert a = true := by
  intro a
  induction a with
  | content | knower | knowledge | value | stream | trace | unit => intro hi; exact hi
  | later a' ih => intro hi; exact hi
  | tensor a' b' _ _ => intro hi; exact hi
  | arrow a' b' _ ihb =>
      intro hi
      exact ihb (by simp [allInert] at hi; exact hi.2)

/-- The GAP-CLASS: need-free, non-inert, not the token, and NOT a
token-consumer. Values of such types cannot be CONSUMED in the clean
fragment: the consumer's λ-bottom binds one (liveBind-banned), a
var-bottom holds one (CleanCtx-banned), and no constant's type carries
one (their domains are stream/knower — need-carrying). This class is
what the five-row table's else-row dispatches on — and note what it
EXCLUDES: `arrow content content` (the identity type) is NOT gap-class
(it is a token-consumer), which is why the extract-contradiction row
handles it and this lemma never has to. -/
def D2 (τ : Ty) : Prop :=
  binderOK τ = false ∧ τ ≠ Ty.content ∧ ¬DeepConsume τ ∧ ¬HasTokenDomain τ ∧ ¬NeedsC τ ∧
    ¬NeedsK τ ∧ ¬NeedsS τ ∧ ¬NeedsT τ

/-- Some domain in the arrow-spine is gap-class. -/
def hasD2Domain : Ty → Prop
  | .arrow a σ => D2 a ∨ hasD2Domain σ
  | _ => False

theorem hasD2Domain_notbinderOK : ∀ τ : Ty, hasD2Domain τ → binderOK τ = false := by
  intro τ
  induction τ with
  | content | knower | knowledge | value | stream | trace | unit | later _ | tensor _ _ =>
      intro h; exact h.elim
  | arrow a' b' _ ihb =>
      intro h
      rcases h with hd | hd
      · have hai : allInert a' = false := by
          obtain ⟨hbo, _⟩ := hd
          exact (Bool.or_eq_false_iff.mp hbo).2
        simp only [binderOK, allInert, hai, Bool.false_and, Bool.or_false]; rfl
      · have hbi : allInert b' = false := (Bool.or_eq_false_iff.mp (ihb hd)).2
        rw [binderOK, allInert, hbi, Bool.and_false, Bool.or_false]; rfl

/-- NO D2-CONSUMER: in the liveBind-clean fix-free mint-free fragment,
no derivation at a clean context consumes a gap-class argument. The
λ-bottom is liveBind-banned, the var-bottom CleanCtx-banned, the four
constants type-banned (their domains need things, so they are not
gap-class); spines and lete-bodies recurse type-preservingly. This is
the producer-side kill that replaces the unsound recursion INTO
gap-class arguments (obs 44's correction). -/
theorem no_d2_producer :
    ∀ (n : Nat), ∀ {Γ : List Ty} {τ : Ty} {t : Term} (h : Typed Γ t τ),
    size h ≤ n → hasD2Domain τ → fixCount h = 0 → mintCount h = 0 →
    liveBind h = 0 → CleanCtx Γ → False
  | 0, _, _, _, h, hn, _, _, _, _, _ => absurd hn (Nat.not_le_of_lt (size_pos h))
  | n + 1, _, _, _, Typed.var, _, hdom, _, _, _, hcc => by
      have hb := hasD2Domain_notbinderOK _ hdom
      have hbt := hcc 0 _ List.get?_zero_cons'
      rw [hb] at hbt
      exact Bool.noConfusion hbt
  | n + 1, _, _, _, @Typed.lam Γ a b body h, hsz, hdom, hfc, hmc, hlb, hcc => by
      obtain ⟨hbY, hlb1⟩ := liveBind_lam_inv h hlb
      rcases hdom with hd | hd
      · rw [hd.1] at hbY
        exact Bool.noConfusion hbY
      · refine no_d2_producer n h (by rw [size_lam] at hsz; omega) hd ?_ ?_ hlb1 ?_
        · simpa only [fixCount] using hfc
        · simpa only [mintCount] using hmc
        · intro (i : Nat) (b' : Ty) hpos
          cases i with
          | zero =>
              rw [List.get?_zero_cons'] at hpos
              injection hpos with he
              subst he
              exact hbY
          | succ m =>
              rw [List.get?_succ_cons'] at hpos
              exact hcc m b' hpos
  | n + 1, _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hsz, hdom, hfc, hmc, hlb,
      hcc => by
      obtain ⟨hfc1, _⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, _⟩ : mintCount hf = 0 ∧ mintCount ha = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hlb1, _⟩ : liveBind hf = 0 ∧ liveBind ha = 0 := by
        simpa only [liveBind, Nat.add_eq_zero_iff] using hlb
      obtain ⟨hcc1, _⟩ := cleanctx_split hcc hs
      exact no_d2_producer n hf (by rw [size_app] at hsz; omega) (Or.inr hdom) hfc1 hmc1
        hlb1 hcc1
  | n + 1, _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hsz, hdom, hfc, hmc,
      hlb, hcc => by
      obtain ⟨hba, hbb, _, hlb2⟩ := liveBind_lete_inv hs hlb
      obtain ⟨_, hfc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨_, hmc2⟩ : mintCount ht = 0 ∧ mintCount hb = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨_, hcc2⟩ := cleanctx_split hcc hs
      refine no_d2_producer n hb (by rw [size_lete] at hsz; omega) hdom hfc2 hmc2 hlb2 ?_
      intro (i : Nat) (b' : Ty) hpos
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact hbb
      | succ m =>
          cases m with
          | zero =>
              rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
              injection hpos with he
              subst he
              exact hba
          | succ k =>
              rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
              exact hcc2 k b' hpos
  | n + 1, _, _, _, Typed.unit, _, hdom, _, _, _, _ => hdom.elim
  | n + 1, _, _, _, @Typed.next _ _ _ _, _, hdom, _, _, _, _ => hdom.elim
  | n + 1, _, _, _, @Typed.fix _ _ _ _ _, _, _, hfc, _, _, _ =>
      absurd hfc (by simp only [fixCount]; omega)
  | n + 1, _, _, _, Typed.cons hc ht hs, _, hdom, _, _, _, _ => hdom.elim
  | n + 1, _, _, _, Typed.nil, _, hdom, _, _, _, _ => hdom.elim
  | n + 1, _, _, _, Typed.snoc ht hu hs, _, hdom, _, _, _, _ => hdom.elim
  | n + 1, _, _, _, Typed.gen, _, hdom, _, _, _, _ => by
      rcases hdom with hd | hd
      · exact hd.2.2.2.2.2.1 True.intro
      · exact hd.elim
  | n + 1, _, _, _, Typed.red, _, hdom, _, _, _, _ => by
      rcases hdom with hd | hd
      · exact hd.2.2.2.2.2.2.1 True.intro
      · exact hd.elim
  | n + 1, _, _, _, Typed.obj, _, hdom, _, _, _, _ => by
      rcases hdom with hd | hd
      · exact hd.2.2.2.2.2.2.1 True.intro
      · exact hd.elim
  | n + 1, _, _, _, Typed.terminate, _, hdom, _, _, _, _ => by
      rcases hdom with hd | hd
      · exact hd.2.2.2.2.2.1 True.intro
      · exact hd.elim
  | n + 1, _, _, _, @Typed.contr Γ k t τ hk h, hsz, hdom, hfc, hmc, hlb, hcc => by
      refine no_d2_producer n h (by rw [size_contr] at hsz; omega) hdom ?_ ?_ ?_ ?_
      · simpa only [fixCount] using hfc
      · simpa only [mintCount] using hmc
      · simpa only [liveBind] using hlb
      · intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hcc 0 _ List.get?_zero_cons'
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hcc 0 _ List.get?_zero_cons'
            | succ m' =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc (m' + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
  | n + 1, _, _, _, @Typed.weak Γ k t τ hk h, hsz, hdom, hfc, hmc, hlb, hcc => by
      refine no_d2_producer n h (by rw [size_weak] at hsz; omega) hdom ?_ ?_ ?_ ?_
      · simpa only [fixCount] using hfc
      · simpa only [mintCount] using hmc
      · simpa only [liveBind] using hlb
      · intro (i : Nat) (b' : Ty) hpos
        exact hcc (i + 1) b' (by rw [List.get?_succ_cons']; exact hpos)

/-- THE CONDITIONAL KILL: in the liveBind-clean fix-free mint-free
fragment, no inert-ending conclusion can swallow the token — the token
must die, and every death-route is banned or bottoms at a closed value.
The app-case is the five-row table on the consumed type X:
(1) X = content → extract the producer, the produce-body's binder IS
the token (CleanCtx forces the extracted binder to be binderOK, and a
content-carrying binderOK type is the token); (2) NeedsC X → extract,
the concluded CleanCtx contradicts needsC_notallInert (the binder would
have to be the token); (3) HasTokenDomain X → extract, same
contradiction; (4) NeedsK/NeedsS/NeedsT X → the supply lemmas kill the
argument; (5) else X is inert (recurse — an inert value cannot swallow
the token) or gap-class (no_d2_producer kills the CONSUMER — obs 44's
correction: never recurse into the gap-argument itself). -/
theorem kill_clean :
    ∀ (n : Nat), ∀ {Γ : List Ty} {τ : Ty} {t : Term} (h : Typed Γ t τ),
    size h ≤ n → fixCount h = 0 → mintCount h = 0 → liveBind h = 0 →
    CleanCtx Γ → (∃ (i : Nat), Γ[i]? = some Ty.content) →
    endsInInert τ = true → False
  | 0, _, _, _, h, hn, _, _, _, _, _, _ => absurd hn (Nat.not_le_of_lt (size_pos h))
  | n + 1, _, _, _, Typed.var, _, _, _, _, hcc, htok, hE => by
      obtain ⟨i, hpos⟩ := htok
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          simp only [endsInInert, allInert] at hE
          exact Bool.noConfusion hE
      | succ m =>
          rw [List.get?_succ_cons'] at hpos
          rw [List.get?_nil'] at hpos
          contradiction
  | n + 1, _, _, _, @Typed.lam Γ a b body h, hsz, hfc, hmc, hlb, hcc, htok, hE => by
      obtain ⟨hbY, hlb1⟩ := liveBind_lam_inv h hlb
      have hbod : endsInInert b = true := by
        rw [endsInInert] at hE; exact hE
      refine kill_clean n h (by rw [size_lam] at hsz; omega) ?_ ?_ hlb1 ?_ ?_ hbod
      · simpa only [fixCount] using hfc
      · simpa only [mintCount] using hmc
      · intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hbY
        | succ m =>
            rw [List.get?_succ_cons'] at hpos
            exact hcc m b' hpos
      · by_cases hac : a = Ty.content
        · rw [hac]
          exact ⟨0, List.get?_zero_cons'⟩
        · obtain ⟨i, hpos⟩ := htok
          exact ⟨i + 1, by rw [List.get?_succ_cons']; exact hpos⟩
  | n + 1, _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hsz, hfc, hmc, hlb, hcc,
      htok, hE => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hf = 0 ∧ mintCount ha = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hlb1, hlb2⟩ : liveBind hf = 0 ∧ liveBind ha = 0 := by
        simpa only [liveBind, Nat.add_eq_zero_iff] using hlb
      obtain ⟨hcc1, hcc2⟩ := cleanctx_split hcc hs
      obtain ⟨i, hpos⟩ := htok
      by_cases hlt : i < Γ.length
      · refine kill_clean n hf (by rw [size_app] at hsz; omega) hfc1 hmc1 hlb1 hcc1 ?_ ?_
        · exact ⟨i, by rw [← hs, List.get?_append_lt hlt] at hpos; exact hpos⟩
        · rw [endsInInert]; exact hE
      · have hge : Γ.length ≤ i := Nat.le_of_not_lt hlt
        rw [← hs, List.get?_append_ge hge] at hpos
        by_cases hx0 : X = Ty.content
        · obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hl2⟩ :=
            extract_produce n hf (by rw [size_app] at hsz; omega) rfl
              (by simp only [DeepConsume]; left; left; exact hx0) hfc1 hmc1 hlb1 hcc1
          exact kill_clean n h' hs2 hf2 hm2 hl2 hc2
            ⟨0, by rw [List.get?_zero_cons', hx0]⟩ hE
        · by_cases hx1 : NeedsC X
          · obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hl2⟩ :=
              extract_produce n hf (by rw [size_app] at hsz; omega) rfl
                (by simp only [DeepConsume]; left; right; left; exact hx1) hfc1 hmc1 hlb1
                hcc1
            have hq : (X == Ty.content) = false := by
              rcases Bool.eq_false_or_eq_true (X == Ty.content) with h1 | h1
              · exact absurd (eq_of_beq h1) hx0
              · exact h1
            have hbx := hc2 0 _ List.get?_zero_cons'
            rw [binderOK, hq, Bool.false_or] at hbx
            rw [needsC_notallInert X hx1] at hbx
            exact Bool.noConfusion hbx
          · by_cases hx2 : HasTokenDomain X
            · obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hl2⟩ :=
                extract_produce n hf (by rw [size_app] at hsz; omega) rfl
                  (by simp only [DeepConsume]; left; right; right; exact hasTokenDomain_deepConsume _ hx2) hfc1 hmc1
                  hlb1 hcc1
              have hq : (X == Ty.content) = false := by
                rcases Bool.eq_false_or_eq_true (X == Ty.content) with h1 | h1
                · exact absurd (eq_of_beq h1) hx0
                · exact h1
              have hbx := hc2 0 _ List.get?_zero_cons'
              rw [binderOK, hq, Bool.false_or] at hbx
              rw [hasTokenDomain_notallInert X hx2] at hbx
              exact Bool.noConfusion hbx
            · by_cases hx3 : NeedsK X
              · obtain ⟨j, b', hpos', hneed⟩ := kprop ha hx3
                exact binderOK_notNeedsK (hcc2 j b' hpos') hneed
              · by_cases hx4 : NeedsS X
                · refine no_stream_without_supply n ha
                    (by rw [size_app] at hsz; omega) hfc2 ?_ hx4
                  intro (j : Nat) (b' : Ty) hpos'
                  have hbo := hcc2 j b' hpos'
                  by_cases hbc : b' = Ty.content
                  · subst hbc; intro hsup; rcases hsup with h | h
                    · exact h
                    · exact h
                  · have hq : (b' == Ty.content) = false := by
                      rcases Bool.eq_false_or_eq_true (b' == Ty.content) with h1 | h1
                      · exact absurd (eq_of_beq h1) hbc
                      · exact h1
                    rw [binderOK, hq, Bool.false_or] at hbo
                    intro hsup
                    rcases hsup with h | h
                    · exact allInert_notNeedsS _ hbo h
                    · exact allInert_notNeedsK _ hbo h
                · by_cases hx5 : NeedsT X
                  · exact no_trace_at_clean n ha (by rw [size_app] at hsz; omega) hfc2
                      hmc2 hlb2 hcc2 hx5
                  · by_cases hxDC : DeepConsume X
                    · obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hl2⟩ :=
                        extract_produce n hf (by rw [size_app] at hsz; omega) rfl
                          (by simp only [DeepConsume]; left; right; right; exact hxDC)
                          hfc1 hmc1 hlb1 hcc1
                      have hbt := hc2 0 _ List.get?_zero_cons'
                      rw [deepConsume_notbinderOK hxDC] at hbt
                      exact Bool.noConfusion hbt
                    · rcases Bool.eq_false_or_eq_true (binderOK X) with hbx | hbx
                      · rcases Bool.eq_false_or_eq_true (X == Ty.content) with h1 | h1
                        · exact absurd (eq_of_beq h1) hx0
                        · have hai : allInert X = true := by
                            rw [binderOK, h1, Bool.false_or] at hbx
                            exact hbx
                          exact kill_clean n ha (by rw [size_app] at hsz; omega) hfc2 hmc2
                            hlb2 hcc2 ⟨i - Γ.length, hpos⟩ (allInert_endsInInert X hai)
                      · exact no_d2_producer n hf (by rw [size_app] at hsz; omega)
                          (Or.inl ⟨hbx, hx0, hxDC, hx2, hx1, hx3, hx4, hx5⟩) hfc1 hmc1
                          hlb1 hcc1
  | n + 1, _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hsz, hfc, hmc, hlb, hcc,
      htok, hE => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hl = 0 ∧ fixCount hr = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hl = 0 ∧ mintCount hr = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hlb1, hlb2⟩ : liveBind hl = 0 ∧ liveBind hr = 0 := by
        simpa only [liveBind, Nat.add_eq_zero_iff] using hlb
      obtain ⟨hcc1, hcc2⟩ := cleanctx_split hcc hs
      obtain ⟨hia, hib⟩ : allInert a = true ∧ allInert b = true := by
        simp only [endsInInert, allInert, Bool.and_eq_true] at hE
        exact hE
      obtain ⟨i, hpos⟩ := htok
      by_cases hlt : i < Γ.length
      · rw [← hs, List.get?_append_lt hlt] at hpos
        exact kill_clean n hl (by rw [size_pair] at hsz; omega) hfc1 hmc1 hlb1 hcc1
          ⟨i, hpos⟩ (allInert_endsInInert a hia)
      · have hge : Γ.length ≤ i := Nat.le_of_not_lt hlt
        rw [← hs, List.get?_append_ge hge] at hpos
        exact kill_clean n hr (by rw [size_pair] at hsz; omega) hfc2 hmc2 hlb2 hcc2
          ⟨i - Γ.length, hpos⟩ (allInert_endsInInert b hib)
  | n + 1, _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hsz, hfc, hmc, hlb,
      hcc, htok, hE => by
      obtain ⟨hba, hbb, hlb1, hlb2⟩ := liveBind_lete_inv hs hlb
      obtain ⟨hfc1, hfc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount ht = 0 ∧ mintCount hb = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hcc1, hcc2⟩ := cleanctx_split hcc hs
      have hbodyctx : CleanCtx (b :: a :: Γ₂) := by
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hbb
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hba
            | succ k =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc2 k b' hpos
      by_cases hcb : a = Ty.content ∨ b = Ty.content
      · rcases hcb with rfl | rfl
        · exact kill_clean n hb (by rw [size_lete] at hsz; omega) hfc2 hmc2 hlb2 hbodyctx
            ⟨1, by rw [List.get?_succ_cons']; exact List.get?_zero_cons'⟩ hE
        · exact kill_clean n hb (by rw [size_lete] at hsz; omega) hfc2 hmc2 hlb2 hbodyctx
            ⟨0, List.get?_zero_cons'⟩ hE
      · obtain ⟨i, hpos⟩ := htok
        by_cases hlt : i < Γ₁.length
        · rw [← hs, List.get?_append_lt hlt] at hpos
          have hia : allInert a = true := by
            rcases Bool.eq_false_or_eq_true (a == Ty.content) with h1 | h1
            · exact absurd (eq_of_beq h1) (fun hc => hcb (Or.inl hc))
            · rw [binderOK, h1, Bool.false_or] at hba
              exact hba
          have hib : allInert b = true := by
            rcases Bool.eq_false_or_eq_true (b == Ty.content) with h1 | h1
            · exact absurd (eq_of_beq h1) (fun hc => hcb (Or.inr hc))
            · rw [binderOK, h1, Bool.false_or] at hbb
              exact hbb
          exact kill_clean n ht (by rw [size_lete] at hsz; omega) hfc1 hmc1 hlb1 hcc1
            ⟨i, hpos⟩ (allInert_endsInInert (Ty.tensor a b) (by
              simp [allInert, hia, hib]))
        · have hge : Γ₁.length ≤ i := Nat.le_of_not_lt hlt
          rw [← hs, List.get?_append_ge hge] at hpos
          exact kill_clean n hb (by rw [size_lete] at hsz; omega) hfc2 hmc2 hlb2 hbodyctx
            ⟨i - Γ₁.length + 2, by
              rw [List.get?_succ_cons', List.get?_succ_cons']; exact hpos⟩ hE
  | n + 1, _, _, _, Typed.unit, _, _, _, _, _, htok, _ => by
      obtain ⟨i, hpos⟩ := htok
      rw [List.get?_nil'] at hpos
      contradiction
  | n + 1, _, _, _, @Typed.next Γ a t h, hsz, hfc, hmc, hlb, hcc, htok, hE =>
      kill_clean n h (by rw [size_next] at hsz; omega) hfc hmc hlb hcc htok
        (allInert_endsInInert a (by
          simp only [endsInInert, allInert] at hE; exact hE))
  | n + 1, _, _, _, @Typed.fix _ _ _ _ _, _, hfc, _, _, _, _, _ =>
      absurd hfc (by simp only [fixCount]; omega)
  | n + 1, _, _, _, Typed.cons hc ht hs, _, _, _, _, _, _, hE => by
      simp only [endsInInert, allInert] at hE
      exact Bool.noConfusion hE
  | n + 1, _, _, _, Typed.nil, _, _, _, _, _, htok, _ => by
      obtain ⟨i, hpos⟩ := htok
      rw [List.get?_nil'] at hpos
      contradiction
  | n + 1, _, _, _, Typed.snoc ht hu hs, _, _, _, _, _, _, hE => by
      simp only [endsInInert, allInert] at hE
      exact Bool.noConfusion hE
  | n + 1, _, _, _, Typed.gen, _, _, _, _, _, htok, _ => by
      obtain ⟨i, hpos⟩ := htok
      rw [List.get?_nil'] at hpos
      contradiction
  | n + 1, _, _, _, Typed.red, _, _, _, _, _, htok, _ => by
      obtain ⟨i, hpos⟩ := htok
      rw [List.get?_nil'] at hpos
      contradiction
  | n + 1, _, _, _, Typed.obj, _, _, _, _, _, htok, _ => by
      obtain ⟨i, hpos⟩ := htok
      rw [List.get?_nil'] at hpos
      contradiction
  | n + 1, _, _, _, Typed.terminate, _, _, _, _, _, htok, _ => by
      obtain ⟨i, hpos⟩ := htok
      rw [List.get?_nil'] at hpos
      contradiction
  | n + 1, _, _, _, @Typed.contr Γ k t τ hk h, hsz, hfc, hmc, hlb, hcc, htok, hE => by
      have hne : k ≠ Ty.content := by
        intro hc
        subst hc
        rw [needsC_linear Ty.content True.intro] at hk
        exact Bool.noConfusion hk
      refine kill_clean n h (by rw [size_contr] at hsz; omega) ?_ ?_ ?_ ?_ ?_ hE
      · simpa only [fixCount] using hfc
      · simpa only [mintCount] using hmc
      · simpa only [liveBind] using hlb
      · intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hcc 0 _ List.get?_zero_cons'
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hcc 0 _ List.get?_zero_cons'
            | succ m' =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc (m' + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      · obtain ⟨i, hpos⟩ := htok
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            exact absurd he hne
        | succ m =>
            rw [List.get?_succ_cons'] at hpos
            exact ⟨m + 2, by
              rw [List.get?_succ_cons', List.get?_succ_cons']; exact hpos⟩
  | n + 1, _, _, _, @Typed.weak Γ k t τ hk h, hsz, hfc, hmc, hlb, hcc, htok, hE => by
      have hne : k ≠ Ty.content := by
        intro hc
        subst hc
        rw [needsC_linear Ty.content True.intro] at hk
        exact Bool.noConfusion hk
      refine kill_clean n h (by rw [size_weak] at hsz; omega) ?_ ?_ ?_ ?_ ?_ hE
      · simpa only [fixCount] using hfc
      · simpa only [mintCount] using hmc
      · simpa only [liveBind] using hlb
      · intro (i : Nat) (b' : Ty) hpos
        exact hcc (i + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      · obtain ⟨i, hpos⟩ := htok
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            exact absurd he hne
        | succ m =>
            rw [List.get?_succ_cons'] at hpos
            exact ⟨m, hpos⟩

/-- NO VANISHING, clean fragment: in the liveBind-clean fix-free
mint-free fragment the token cannot vanish into a `unit` conclusion —
the standard `A ⊬ 1`, at its deepest fragment yet (gen, cons, snoc and
the structural rules are INSIDE; only fixpoints, trace-mints and live
binders are excluded). -/
theorem no_vanishing_clean {t : Term} (h : Typed [Ty.content] t Ty.unit)
    (hf : fixCount h = 0) (hm : mintCount h = 0) (hl : liveBind h = 0) : False :=
  kill_clean (size h) h (Nat.le_refl _) hf hm hl
    (by
      intro (i : Nat) (b : Ty) hpos
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          rfl
      | succ m =>
          rw [List.get?_succ_cons'] at hpos
          rw [List.get?_nil'] at hpos
          contradiction)
    ⟨0, List.get?_zero_cons'⟩
    rfl

/-- In a fix-free tree the trace-mint counters agree — `tMint`'s only
divergence from `mintCount` is the fix-case's `tnet a` term. -/
theorem tMint_eq_mintCount_nofix :
    ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    fixCount h = 0 → tMint h = mintCount h := by
  intro Γ t τ h
  induction h with
  | var | unit | nil | gen | red | obj | terminate => intro _; rfl
  | lam _ ih =>
      intro hf
      simpa only [tMint, mintCount, fixCount] using ih hf
  | app _ _ _ ihf iha =>
      intro hf
      simp only [fixCount, Nat.add_eq_zero_iff] at hf
      simp only [tMint, mintCount]
      have e1 := ihf hf.1
      have e2 := iha hf.2
      omega
  | pair _ _ _ ihl ihr =>
      intro hf
      simp only [fixCount, Nat.add_eq_zero_iff] at hf
      simp only [tMint, mintCount]
      have e1 := ihl hf.1
      have e2 := ihr hf.2
      omega
  | lete _ _ _ iht ihb =>
      intro hf
      simp only [fixCount, Nat.add_eq_zero_iff] at hf
      simp only [tMint, mintCount]
      have e1 := iht hf.1
      have e2 := ihb hf.2
      omega
  | next _ ih =>
      intro hf
      simpa only [tMint, mintCount, fixCount] using ih hf
  | fix _ _ _ =>
      intro hf
      exact absurd hf (by simp only [fixCount]; omega)
  | cons _ _ _ ihc iht =>
      intro hf
      simp only [fixCount, Nat.add_eq_zero_iff] at hf
      simp only [tMint, mintCount]
      have e1 := ihc hf.1
      have e2 := iht hf.2
      omega
  | snoc _ _ _ iht ihu =>
      intro hf
      simp only [fixCount, Nat.add_eq_zero_iff] at hf
      simp only [tMint, mintCount]
      have e1 := iht hf.1
      have e2 := ihu hf.2
      omega
  | contr _ _ ih =>
      intro hf
      simpa only [tMint, mintCount, fixCount] using ih hf
  | weak _ _ ih =>
      intro hf
      simpa only [tMint, mintCount, fixCount] using ih hf

/-- The FREE DISCHARGE for the ascent's front door: at a fix-free
`[content] ⊢ unit` root, the trace-mint count is zero — the root spends
no trace-tokens and carries none, so `nil`/`terminate` nodes are
arithmetically excluded before the march begins. -/
theorem mintCount_zero_at_unit_root {t : Term} (h : Typed [Ty.content] t Ty.unit)
    (hf : fixCount h = 0) : mintCount h = 0 := by
  have e1 := tMint_eq_mintCount_nofix h hf
  have e2 := tMint_zero_at_unit_root h
  omega

/-! ## The park-free fragment and the obligation discipline -/

/-- The DISCIPLINE PREDICATE: a hypothesis (or λ-domain) is the token's
kind (content), inert, or GAP-CLASS — live but carrying no demand and
consuming nothing. Contexts satisfying it at every position are the
march's obligation contexts; `ParkFree` requires it of every λ-domain
and lete-component in the tree. -/
def DomOK (a : Ty) : Prop := binderOK a = true ∨ D2 a

/-- The (i)-fix's key lemma (obs 49/50): a deep-consuming type is not
discipline-OK — neither clean (allInert fails) nor gap-class (the
¬DeepConsume conjunct fails). Consumer-of-consumer chains at every
depth die at the discipline. -/
theorem deepConsume_notDomOK {τ : Ty} (h : DeepConsume τ) (hd : DomOK τ) : False := by
  rcases hd with hb | hb
  · have hnb := deepConsume_notbinderOK h
    rw [hnb] at hb
    exact Bool.noConfusion hb
  · exact hb.2.2.1 h

/-- The discipline at every position of the context. -/
def OblCtx (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (b : Ty), Γ[i]? = some b → DomOK b

/-- PARK-FREE: every λ-domain and lete-component in the tree is
`DomOK` — no domain CONSUMES tokens, none needs a knower, stream, trace,
or content, unless it is the token's own kind. This is the obs-44 fix
generalized: the statement-shaped bodies a march must never enter live
behind non-DomOK domains, and `ParkFree` bans the doorway. Strictly
weaker than `liveBind = 0` (which forces every domain binderOK):
park-free trees may bind GAP-CLASS domains. -/
def ParkFree : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Prop
  | _, _, _, @Typed.lam _ a _ _ h => DomOK a ∧ ParkFree h
  | _, _, _, @Typed.lete _ _ _ a b _ _ _ ht hb _ =>
      DomOK a ∧ DomOK b ∧ ParkFree ht ∧ ParkFree hb
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => ParkFree hf ∧ ParkFree ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => ParkFree hl ∧ ParkFree hr
  | _, _, _, @Typed.next _ _ _ h => ParkFree h
  | _, _, _, @Typed.fix _ _ _ _ h => ParkFree h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => ParkFree hc ∧ ParkFree ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => ParkFree ht ∧ ParkFree hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => ParkFree h
  | _, _, _, @Typed.weak _ _ _ _ _ h => ParkFree h
  | _, _, _, _ => True

theorem ParkFree_lam_inv {Γ : List Ty} {a b : Ty} {body : Term}
    (h : Typed (a :: Γ) body b) (hp : ParkFree (Typed.lam h)) :
    DomOK a ∧ ParkFree h := hp

theorem ParkFree_lete_inv {E Γ₁ Γ₂ : List Ty} {a b c : Ty} {t body : Term}
    {ht : Typed Γ₁ t (.tensor a b)}
    {hb : Typed (b :: a :: Γ₂) body c} (hs : Γ₁ ++ Γ₂ = E)
    (hp : ParkFree (Typed.lete ht hb hs)) :
    DomOK a ∧ DomOK b ∧ ParkFree ht ∧ ParkFree hb := hp

theorem ParkFree_appL {E : List Ty} {Γ Δ : List Ty} {X b : Ty} {fn arg : Term}
    {hf : Typed Γ fn (.arrow X b)} {ha : Typed Δ arg X} {hs : Γ ++ Δ = E}
    (hp : ParkFree (Typed.app hf ha hs)) : ParkFree hf := hp.1

theorem ParkFree_appR {E : List Ty} {Γ Δ : List Ty} {X b : Ty} {fn arg : Term}
    {hf : Typed Γ fn (.arrow X b)} {ha : Typed Δ arg X} {hs : Γ ++ Δ = E}
    (hp : ParkFree (Typed.app hf ha hs)) : ParkFree ha := hp.2

theorem ParkFree_pairL {E : List Ty} {Γ Δ : List Ty} {a b : Ty} {l r : Term}
    {hl : Typed Γ l a} {hr : Typed Δ r b} {hs : Γ ++ Δ = E}
    (hp : ParkFree (Typed.pair hl hr hs)) : ParkFree hl := hp.1

theorem ParkFree_pairR {E : List Ty} {Γ Δ : List Ty} {a b : Ty} {l r : Term}
    {hl : Typed Γ l a} {hr : Typed Δ r b} {hs : Γ ++ Δ = E}
    (hp : ParkFree (Typed.pair hl hr hs)) : ParkFree hr := hp.2

theorem OblCtx_split {E : List Ty} (hd : OblCtx E) {Γ Δ : List Ty}
    (hs : Γ ++ Δ = E) : OblCtx Γ ∧ OblCtx Δ := by
  constructor
  · intro (i : Nat) (b : Ty) hpos
    have hlt : i < Γ.length := List.get?_some_lt hpos
    exact hd i b (by rw [← hs, List.get?_append_lt hlt]; exact hpos)
  · intro (i : Nat) (b : Ty) hpos
    have hlt : i < Δ.length := List.get?_some_lt hpos
    refine hd (Γ.length + i) b ?_
    rw [← hs, List.get?_append_ge (Nat.le_add_right Γ.length i), Nat.add_sub_cancel_left]
    exact hpos

/-- Obligation hypotheses carry no knower/stream/trace demands (the
token's kind and inert types carry none; gap-class types carry none by
definition). -/
theorem DomOK_notNeedsK {b : Ty} (hd : DomOK b) (h : NeedsK b) : False := by
  rcases hd with hd | hd
  · exact binderOK_notNeedsK hd h
  · exact hd.2.2.2.2.2.1 h

theorem DomOK_notNeedsS {b : Ty} (hd : DomOK b) (h : NeedsS b) : False := by
  rcases hd with hd | hd
  · exact binderOK_notNeedsS hd h
  · exact hd.2.2.2.2.2.2.1 h

theorem DomOK_notNeedsT {b : Ty} (hd : DomOK b) (h : NeedsT b) : False := by
  rcases hd with hd | hd
  · exact binderOK_notNeedsT hd h
  · exact hd.2.2.2.2.2.2.2 h

/-- EXTRACTION, obligation version: the type-preserving producer walk at
discipline contexts in park-free trees. The substitution-copy of
`extract_produce` — `liveBind` becomes `ParkFree` (the lam/lete cases
return the DOMOK of the domain directly, no inversion lemma needed) and
`CleanCtx` becomes `OblCtx`. The trigger stays `HasTokenDomain` — the
DIRECT-consumer trigger — whose var/constants kills are trigger-internal
and carry over unchanged. -/
theorem extract_produce' :
    ∀ (n : Nat), ∀ {Γ : List Ty} {Y σ τ : Ty} {f : Term} (h : Typed Γ f τ),
    size h ≤ n → τ = .arrow Y σ → DeepConsume (.arrow Y σ) → fixCount h = 0 →
    mintCount h = 0 → ParkFree h → OblCtx Γ →
    ∃ (Γ' : List Ty) (t' : Term) (h' : Typed (Y :: Γ') t' σ),
      size h' ≤ n ∧ OblCtx (Y :: Γ') ∧ fixCount h' = 0 ∧ mintCount h' = 0 ∧
      ParkFree h'
  | 0, _, _, _, _, _, h, hn, _, _, _, _, _, _ =>
      absurd hn (Nat.not_le_of_lt (size_pos h))
  | n + 1, _, _, _, _, _, Typed.var, _, heq, hdom, _, _, _, hcc => by
      cases heq
      rcases hcc 0 _ List.get?_zero_cons' with hb | hb
      · have hai := deepConsume_notallInert _ hdom
        rw [binderOK, hai, Bool.or_false] at hb
        exact Ty.noConfusion (eq_of_beq hb)
      · exact (hb.2.2.1 hdom).elim
  | n + 1, _, _, _, _, _, @Typed.lam Γ a b body h, hsz, heq, hdom, hfc, hmc,
      hp, hcc => by
      injection heq with h1 h2
      subst h1
      subst h2
      obtain ⟨hdy, hpf⟩ := ParkFree_lam_inv h hp
      refine ⟨Γ, body, h, ?_, ?_, ?_, ?_, hpf⟩
      · rw [size_lam] at hsz; omega
      · intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hdy
        | succ m =>
            rw [List.get?_succ_cons'] at hpos
            exact hcc m b' hpos
      · simpa only [fixCount] using hfc
      · simpa only [mintCount] using hmc
  | n + 1, _, _, _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hsz, heq, hdom,
      hfc, hmc, hp, hcc => by
      subst heq
      obtain ⟨hfc1, _⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, _⟩ : mintCount hf = 0 ∧ mintCount ha = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hp1, _⟩ := hp
      obtain ⟨hcc1, _⟩ := OblCtx_split hcc hs
      have hszf : size hf ≤ n := by rw [size_app] at hsz; omega
      obtain ⟨Γ₁, t₁, h₁, hs1, hc1, hf1, hm1, hp1'⟩ :=
        extract_produce' n hf hszf rfl (Or.inr hdom) hfc1 hmc1 hp1 hcc1
      obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hp2⟩ :=
        extract_produce' n h₁ hs1 rfl hdom hf1 hm1 hp1' hc1
      exact ⟨Γ', t', h', by omega, hc2, hf2, hm2, hp2⟩
  | n + 1, _, _, _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, _, heq, _, _, _,
      _, _ => by
      exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hsz, heq,
      hdom, hfc, hmc, hp, hcc => by
      subst heq
      obtain ⟨hda, hdb, _, hpb⟩ := ParkFree_lete_inv hs hp
      obtain ⟨_, hfc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨_, hmc2⟩ : mintCount ht = 0 ∧ mintCount hb = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨_, hcc2⟩ := OblCtx_split hcc hs
      have hszb : size hb ≤ n := by rw [size_lete] at hsz; omega
      have hccb : OblCtx (b :: a :: Γ₂) := by
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hdb
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hda
            | succ k =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc2 k b' hpos
      obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hp2⟩ :=
        extract_produce' n hb hszb rfl hdom hfc2 hmc2 hpb hccb
      exact ⟨Γ', t', h', by omega, hc2, hf2, hm2, hp2⟩
  | n + 1, _, _, _, _, _, Typed.unit, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, @Typed.next Γ a t h, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, @Typed.fix _ a body hΓ h, _, heq, hdom, hfc, _, _, _ => by
      cases heq
      exact absurd hfc (by simp only [fixCount]; omega)
  | n + 1, _, _, _, _, _, Typed.cons hc ht hs, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, Typed.nil, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, Typed.snoc ht hu hs, _, heq, _, _, _, _, _ =>
      by exact Ty.noConfusion heq
  | n + 1, _, _, _, _, _, Typed.gen, _, heq, hdom, _, _, _, _ => by
      injection heq with h1 h2
      subst h1
      subst h2
      simp only [DeepConsume] at hdom
      rcases hdom with h | h
      · rcases h with h | h | h
        · exact Ty.noConfusion h
        · exact h.elim
        · exact h.elim
      · exact h.elim
  | n + 1, _, _, _, _, _, Typed.red, _, heq, hdom, _, _, _, _ => by
      injection heq with h1 h2
      subst h1
      subst h2
      simp only [DeepConsume] at hdom
      rcases hdom with h | h
      · rcases h with h | h | h
        · exact Ty.noConfusion h
        · exact h.elim
        · exact h.elim
      · exact h.elim
  | n + 1, _, _, _, _, _, Typed.obj, _, heq, hdom, _, _, _, _ => by
      injection heq with h1 h2
      subst h1
      subst h2
      simp only [DeepConsume] at hdom
      rcases hdom with h | h
      · rcases h with h | h | h
        · exact Ty.noConfusion h
        · exact h.elim
        · exact h.elim
      · exact h.elim
  | n + 1, _, _, _, _, _, Typed.terminate, _, heq, hdom, _, _, _, _ => by
      injection heq with h1 h2
      subst h1
      subst h2
      simp only [DeepConsume] at hdom
      rcases hdom with h | h
      · rcases h with h | h | h
        · exact Ty.noConfusion h
        · exact h.elim
        · exact h.elim
      · exact h.elim
  | n + 1, _, _, _, _, _, @Typed.contr Γ k t τ hk h, hsz, heq, hdom, hfc, hmc,
      hp, hcc => by
      subst heq
      have hccp : OblCtx (k :: k :: Γ) := by
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hcc 0 _ List.get?_zero_cons'
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hcc 0 _ List.get?_zero_cons'
            | succ m' =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc (m' + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hp2⟩ :=
        extract_produce' n h (by rw [size_contr] at hsz; omega) rfl hdom
          (by simpa only [fixCount] using hfc) (by simpa only [mintCount] using hmc)
          (by simpa only [ParkFree] using hp) hccp
      exact ⟨Γ', t', h', by omega, hc2, hf2, hm2, hp2⟩
  | n + 1, _, _, _, _, _, @Typed.weak Γ k t τ hk h, hsz, heq, hdom, hfc, hmc,
      hp, hcc => by
      subst heq
      have hccp : OblCtx Γ := by
        intro (i : Nat) (b' : Ty) hpos
        exact hcc (i + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hp2⟩ :=
        extract_produce' n h (by rw [size_weak] at hsz; omega) rfl hdom
          (by simpa only [fixCount] using hfc) (by simpa only [mintCount] using hmc)
          (by simpa only [ParkFree] using hp) hccp
      exact ⟨Γ', t', h', by omega, hc2, hf2, hm2, hp2⟩

/-- NO TRACE AT OBLIGATIONS: the no-archival theorem at discipline
contexts in park-free trees — `no_trace_at_clean` with `ParkFree` for
`liveBind` and `OblCtx` for `CleanCtx`. Every trace-spine still bottoms
at a banned domain (non-DomOK), a banned hypothesis, a mint, or a
fixpoint. -/
theorem no_trace_at_oblig :
    ∀ (n : Nat), ∀ {Γ : List Ty} {τ : Ty} {t : Term} (h : Typed Γ t τ),
    size h ≤ n → fixCount h = 0 → mintCount h = 0 → ParkFree h →
    OblCtx Γ → NeedsT τ → False
  | 0, _, _, _, h, hn, _, _, _, _, _ => absurd hn (Nat.not_le_of_lt (size_pos h))
  | n + 1, _, _, _, Typed.var, _, _, _, _, hcc, hK =>
      DomOK_notNeedsT (hcc 0 _ List.get?_zero_cons') hK
  | n + 1, _, _, _, @Typed.lam Γ a b body h, hsz, hfc, hmc, hp, hcc,
      ⟨hb, hneg⟩ => by
      obtain ⟨hda, hpf⟩ := ParkFree_lam_inv h hp
      refine no_trace_at_oblig n h (by rw [size_lam] at hsz; omega) ?_ ?_ hpf ?_ hb
      · simpa only [fixCount] using hfc
      · simpa only [mintCount] using hmc
      · intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hda
        | succ m =>
            rw [List.get?_succ_cons'] at hpos
            exact hcc m b' hpos
  | n + 1, _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hsz, hfc, hmc, hp,
      hcc, hK => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hf = 0 ∧ mintCount ha = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hcc1, hcc2⟩ := OblCtx_split hcc hs
      by_cases hN : NeedsT (Ty.arrow X b)
      · exact no_trace_at_oblig n hf (by rw [size_app] at hsz; omega) hfc1 hmc1 hp1
          hcc1 hN
      · have hdx : NeedsT X ∨ NeedsC X ∨ NeedsK X :=
          Classical.byContradiction fun hcon =>
            hN ⟨hK, fun hd => hcon hd⟩
        rcases hdx with hx | hx | hx
        · exact no_trace_at_oblig n ha (by rw [size_app] at hsz; omega) hfc2 hmc2 hp2
            hcc2 hx
        · obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hp2'⟩ :=
            extract_produce' n hf (by rw [size_app] at hsz; omega) rfl
              (Or.inl (Or.inr (Or.inl hx))) hfc1 hmc1 hp1 hcc1
          exact no_trace_at_oblig n h' hs2 hf2 hm2 hp2' hc2 hK
        · obtain ⟨i, b', hpos, hneed⟩ := kprop ha hx
          exact DomOK_notNeedsK (hcc2 i b' hpos) hneed
  | n + 1, _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hsz, hfc, hmc, hp,
      hcc, hK => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hl = 0 ∧ fixCount hr = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hl = 0 ∧ mintCount hr = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hcc1, hcc2⟩ := OblCtx_split hcc hs
      rcases hK with hK | hK
      · exact no_trace_at_oblig n hl (by rw [size_pair] at hsz; omega) hfc1 hmc1 hp1
          hcc1 hK
      · exact no_trace_at_oblig n hr (by rw [size_pair] at hsz; omega) hfc2 hmc2 hp2
          hcc2 hK
  | n + 1, _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hsz, hfc, hmc,
      hp, hcc, hK => by
      obtain ⟨hda, hdb, hpt, hpb⟩ := ParkFree_lete_inv hs hp
      obtain ⟨hfc1, hfc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount ht = 0 ∧ mintCount hb = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hcc1, hcc2⟩ := OblCtx_split hcc hs
      by_cases hbs : NeedsT a ∨ NeedsT b
      · exact no_trace_at_oblig n ht (by rw [size_lete] at hsz; omega) hfc1 hmc1 hpt
          hcc1 hbs
      · refine no_trace_at_oblig n hb (by rw [size_lete] at hsz; omega) hfc2 hmc2 hpb
          ?_ hK
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hdb
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hda
            | succ k =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc2 k b' hpos
  | n + 1, _, _, _, Typed.unit, _, _, _, _, _, hK => False.elim hK
  | n + 1, _, _, _, @Typed.next Γ a t h, hsz, hfc, hmc, hp, hcc, hK =>
      no_trace_at_oblig n h (by rw [size_next] at hsz; omega) hfc hmc
        (by simpa only [ParkFree] using hp) hcc hK
  | n + 1, _, _, _, @Typed.fix _ _ _ _ _, _, hfc, _, _, _, _ =>
      absurd hfc (by simp only [fixCount]; omega)
  | n + 1, _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, _, _, _, _, _, hK =>
      False.elim hK
  | n + 1, _, _, _, Typed.nil, _, _, hmc, _, _, _ =>
      absurd hmc (by simp only [mintCount]; omega)
  | n + 1, _, _, _, @Typed.snoc E Γ Δ t u ht hu hs, hsz, hfc, hmc, hp, hcc, _ => by
      obtain ⟨hfc1, _⟩ : fixCount ht = 0 ∧ fixCount hu = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, _⟩ : mintCount ht = 0 ∧ mintCount hu = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hp1, _⟩ := hp
      obtain ⟨hcc1, _⟩ := OblCtx_split hcc hs
      exact no_trace_at_oblig n ht (by rw [size_snoc] at hsz; omega) hfc1 hmc1 hp1
        hcc1 True.intro
  | n + 1, _, _, _, Typed.gen, _, _, _, _, _, hK => hK.2 (Or.inr (Or.inr True.intro))
  | n + 1, _, _, _, Typed.red, _, _, _, _, _, hK => False.elim hK.1
  | n + 1, _, _, _, Typed.obj, _, _, _, _, _, hK => False.elim hK.1
  | n + 1, _, _, _, Typed.terminate, _, _, _, _, _, hK =>
      hK.2 (Or.inr (Or.inr True.intro))
  | n + 1, _, _, _, @Typed.contr Γ k t τ hk h, hsz, hfc, hmc, hp, hcc, hK => by
      have hccp : OblCtx (k :: k :: Γ) := by
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hcc 0 _ List.get?_zero_cons'
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hcc 0 _ List.get?_zero_cons'
            | succ m' =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc (m' + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      exact no_trace_at_oblig n h (by rw [size_contr] at hsz; omega)
        (by simpa only [fixCount] using hfc) (by simpa only [mintCount] using hmc)
        (by simpa only [ParkFree] using hp) hccp hK
  | n + 1, _, _, _, @Typed.weak Γ k t τ hk h, hsz, hfc, hmc, hp, hcc, hK => by
      have hccp : OblCtx Γ := by
        intro (i : Nat) (b' : Ty) hpos
        exact hcc (i + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
      exact no_trace_at_oblig n h (by rw [size_weak] at hsz; omega)
        (by simpa only [fixCount] using hfc) (by simpa only [mintCount] using hmc)
        (by simpa only [ParkFree] using hp) hccp hK

/-- NO DEEP CONSUMER: at discipline contexts in park-free trees, no
producer consumes a deep-consuming argument — the extraction's concluded
discipline puts `DomOK X` at the produce-binder, and `DeepConsume X`
kills both of its branches. Consumer-of-consumer chains at EVERY depth
die here; the content-domain fire-head (the legal `λ(c:content)` chain)
is outside this lemma by the `DeepConsume X`-at-`X ≠ content` shape of
its calling rows. -/
theorem no_deep_consumer {Γ : List Ty} {X b : Ty} {f : Term}
    (hf : Typed Γ f (.arrow X b)) (hdc : DeepConsume X)
    (hfc : fixCount hf = 0) (hmc : mintCount hf = 0) (hp : ParkFree hf)
    (hcc : OblCtx Γ) : False := by
  obtain ⟨Γ', t', h', hs2, hc2, hf2, hm2, hp2⟩ :=
    extract_produce' (size hf) hf (Nat.le_refl _) rfl
      (Or.inl (Or.inr (Or.inr hdc))) hfc hmc hp hcc
  exact deepConsume_notDomOK hdc (hc2 0 _ List.get?_zero_cons')

/-! ## The composition: vanishing at the park-free fragment

`flowEq`'s arithmetic forces a sink at a fix-free `[content] ⊢ unit`
root (`sinks = 1 + genFire`); the extraction below carries the
discipline down to the sink's killed premise; the premise dies by its
own sort's kill — the trace by `no_trace_at_oblig`, the stream-tail by
`no_stream_without_supply`. The token-march of the interval-4 design
(`kill_oblig`) is never taken: the accounting already transmuted the
token into sink-counts, and each sink dies at its own sort. Every
wall-case of the march is an artifact of walking the token; on this
route they cannot arise. -/

/-- A fix-free tree carries no unroll-credit either: `fixMint` only
mints at fix nodes, so the two counters vanish together. -/
theorem fixMint_eq_zero :
    ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    fixCount h = 0 → fixMint h = 0
  | _, _, _, @Typed.fix _ _ _ _ _, hf => by simp only [fixCount] at hf; omega
  | _, _, _, @Typed.lam _ _ _ _ h, hf => by
      simpa only [fixCount, fixMint] using fixMint_eq_zero h hf
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _, hfc => by
      obtain ⟨h1, h2⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      simp only [fixMint]
      rw [fixMint_eq_zero hf h1, fixMint_eq_zero ha h2]
      omega
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _, hf => by
      obtain ⟨h1, h2⟩ : fixCount hl = 0 ∧ fixCount hr = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hf
      simp only [fixMint]
      rw [fixMint_eq_zero hl h1, fixMint_eq_zero hr h2]
      omega
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _, hf => by
      obtain ⟨h1, h2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hf
      simp only [fixMint]
      rw [fixMint_eq_zero ht h1, fixMint_eq_zero hb h2]
      omega
  | _, _, _, @Typed.next _ _ _ h, hf => by
      simpa only [fixCount, fixMint] using fixMint_eq_zero h hf
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _, hf => by
      obtain ⟨h1, h2⟩ : fixCount hc = 0 ∧ fixCount ht = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hf
      simp only [fixMint]
      rw [fixMint_eq_zero hc h1, fixMint_eq_zero ht h2]
      omega
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _, hf => by
      obtain ⟨h1, h2⟩ : fixCount ht = 0 ∧ fixCount hu = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hf
      simp only [fixMint]
      rw [fixMint_eq_zero ht h1, fixMint_eq_zero hu h2]
      omega
  | _, _, _, @Typed.contr _ _ _ _ _ h, hf => by
      simpa only [fixCount, fixMint] using fixMint_eq_zero h hf
  | _, _, _, @Typed.weak _ _ _ _ _ h, hf => by
      simpa only [fixCount, fixMint] using fixMint_eq_zero h hf
  | _, _, _, Typed.var, _ => by simp only [fixMint]
  | _, _, _, Typed.unit, _ => by simp only [fixMint]
  | _, _, _, Typed.nil, _ => by simp only [fixMint]
  | _, _, _, Typed.gen, _ => by simp only [fixMint]
  | _, _, _, Typed.red, _ => by simp only [fixMint]
  | _, _, _, Typed.obj, _ => by simp only [fixMint]
  | _, _, _, Typed.terminate, _ => by simp only [fixMint]

/-- An obligation context supplies no stream-demand: the token's kind,
inert types, and gap-class types need neither a stream nor a knower. -/
theorem oblctx_noSSupply {Γ : List Ty} (hcc : OblCtx Γ) :
    ∀ (i : Nat) (a : Ty), Γ[i]? = some a → ¬ SSupply a := by
  intro (i : Nat) (a : Ty) hpos
  have hd := hcc i a hpos
  intro hsup
  rcases hsup with h | h
  · exact DomOK_notNeedsS hd h
  · exact DomOK_notNeedsK hd h

/-- SINK-EXTRACTION with discipline-carry: in a park-free tree at an
obligation context, a sink node's KILLED premise — the snoc's trace, the
cons's `▷stream` tail — is itself at an obligation context, park-free,
with clean counters. The discipline descends to the sink; this is the
piece that turns `flowEq`'s arithmetic into a proof. -/
theorem sinks_extract :
    ∀ {Γ : List Ty} {τ : Ty} {t : Term} (h : Typed Γ t τ),
    0 < sinks h → fixCount h = 0 → mintCount h = 0 → ParkFree h → OblCtx Γ →
    (∃ (Γ' : List Ty) (t' : Term) (ht : Typed Γ' t' Ty.trace),
        fixCount ht = 0 ∧ mintCount ht = 0 ∧ ParkFree ht ∧ OblCtx Γ')
    ∨ (∃ (Γ' : List Ty) (t' : Term) (ht : Typed Γ' t' (.later Ty.stream)),
        fixCount ht = 0 ∧ mintCount ht = 0 ∧ ParkFree ht ∧ OblCtx Γ')
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs, _, hfc, hmc, hp, hcc => by
      obtain ⟨hfc1, _⟩ : fixCount ht = 0 ∧ fixCount hu = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, _⟩ : mintCount ht = 0 ∧ mintCount hu = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hpt, _⟩ := hp
      obtain ⟨hcc1, _⟩ := OblCtx_split hcc hs
      exact Or.inl ⟨Γ, t, ht, hfc1, hmc1, hpt, hcc1⟩
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, _, hfc, hmc, hp, hcc => by
      obtain ⟨_, hfc2⟩ : fixCount hc = 0 ∧ fixCount ht = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨_, hmc2⟩ : mintCount hc = 0 ∧ mintCount ht = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨_, hpt⟩ := hp
      obtain ⟨_, hcc2⟩ := OblCtx_split hcc hs
      exact Or.inr ⟨Δ, tl, ht, hfc2, hmc2, hpt, hcc2⟩
  | _, _, _, @Typed.lam Γ a b body h, hsink, hfc, hmc, hp, hcc => by
      obtain ⟨hda, hpf⟩ := ParkFree_lam_inv h hp
      refine sinks_extract h hsink (by simpa only [fixCount] using hfc)
        (by simpa only [mintCount] using hmc) hpf ?_
      intro (i : Nat) (b' : Ty) hpos
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact hda
      | succ m =>
          rw [List.get?_succ_cons'] at hpos
          exact hcc m b' hpos
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hsink, hfc, hmc, hp, hcc => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hf = 0 ∧ mintCount ha = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hcc1, hcc2⟩ := OblCtx_split hcc hs
      simp only [sinks] at hsink
      by_cases hsl : 0 < sinks hf
      · exact sinks_extract hf hsl hfc1 hmc1 hp1 hcc1
      · have hsr : 0 < sinks ha := by omega
        exact sinks_extract ha hsr hfc2 hmc2 hp2 hcc2
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs, hsink, hfc, hmc, hp, hcc => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hl = 0 ∧ fixCount hr = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hl = 0 ∧ mintCount hr = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hcc1, hcc2⟩ := OblCtx_split hcc hs
      simp only [sinks] at hsink
      by_cases hsl : 0 < sinks hl
      · exact sinks_extract hl hsl hfc1 hmc1 hp1 hcc1
      · have hsr : 0 < sinks hr := by omega
        exact sinks_extract hr hsr hfc2 hmc2 hp2 hcc2
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs, hsink, hfc, hmc, hp,
      hcc => by
      obtain ⟨hda, hdb, hpt, hpb⟩ := ParkFree_lete_inv hs hp
      obtain ⟨hfc1, hfc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount ht = 0 ∧ mintCount hb = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      obtain ⟨hcc1, hcc2⟩ := OblCtx_split hcc hs
      simp only [sinks] at hsink
      by_cases hst : 0 < sinks ht
      · exact sinks_extract ht hst hfc1 hmc1 hpt hcc1
      · have hsb : 0 < sinks hb := by omega
        refine sinks_extract hb hsb hfc2 hmc2 hpb ?_
        intro (i : Nat) (b' : Ty) hpos
        cases i with
        | zero =>
            rw [List.get?_zero_cons'] at hpos
            injection hpos with he
            subst he
            exact hdb
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                injection hpos with he
                subst he
                exact hda
            | succ k =>
                rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
                exact hcc2 k b' hpos
  | _, _, _, @Typed.next Γ a t h, hsink, hfc, hmc, hp, hcc =>
      sinks_extract h hsink (by simpa only [fixCount] using hfc)
        (by simpa only [mintCount] using hmc) hp hcc
  | _, _, _, @Typed.contr Γ k t τ hk h, hsink, hfc, hmc, hp, hcc => by
      refine sinks_extract h hsink (by simpa only [fixCount] using hfc)
        (by simpa only [mintCount] using hmc) (by simpa only [ParkFree] using hp)
        ?_
      intro (i : Nat) (b' : Ty) hpos
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact hcc 0 _ List.get?_zero_cons'
      | succ m =>
          cases m with
          | zero =>
              rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
              injection hpos with he
              subst he
              exact hcc 0 _ List.get?_zero_cons'
          | succ m' =>
              rw [List.get?_succ_cons', List.get?_succ_cons'] at hpos
              exact hcc (m' + 1) b' (by rw [List.get?_succ_cons']; exact hpos)
  | _, _, _, @Typed.weak Γ k t τ hk h, hsink, hfc, hmc, hp, hcc =>
      sinks_extract h hsink (by simpa only [fixCount] using hfc)
        (by simpa only [mintCount] using hmc) (by simpa only [ParkFree] using hp)
        (by
          intro (i : Nat) (b' : Ty) hpos
          exact hcc (i + 1) b' (by rw [List.get?_succ_cons']; exact hpos))
  | _, _, _, @Typed.fix _ _ _ _ _, _, hfc, _, _, _ =>
      absurd hfc (by simp only [fixCount]; omega)
  | _, _, _, Typed.var, hsink, _, _, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, Typed.unit, hsink, _, _, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, Typed.nil, hsink, _, _, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, Typed.gen, hsink, _, _, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, Typed.red, hsink, _, _, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, Typed.obj, hsink, _, _, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, Typed.terminate, hsink, _, _, _, _ => by
      simp only [sinks] at hsink; omega

/-- NO VANISHING, park-free fragment: with every λ-domain and
lete-component discipline-OK (a strictly weaker restriction than
`liveBind = 0`, which forces every domain binderOK), a fix-free
`[content] ⊢ unit` is impossible. The token never vanishes because
nothing can archive it and nothing can consume it — the sinks the flow
equality forces are dead at their own sorts. -/
theorem no_vanishing_parkfree {t : Term} (h : Typed [Ty.content] t Ty.unit)
    (hf : fixCount h = 0) (hp : ParkFree h) : False := by
  have hmc : mintCount h = 0 := mintCount_zero_at_unit_root h hf
  have hfm : fixMint h = 0 := fixMint_eq_zero h hf
  have hus : uses h 0 = 1 := single_linear_use h 0 Ty.content rfl rfl
  have hsp : spendNet h = 1 := by
    simp only [spendNet, spendNetFrom, hus, net, Int.mul_one, Int.add_zero]
    omega
  have hfe := flowEq (Γ := [Ty.content]) (t := t) (τ := Ty.unit) h
  simp only [net] at hfe
  rw [hsp, hfm] at hfe
  have hsink : 0 < sinks h := by omega
  have hcc : OblCtx [Ty.content] := by
    intro (i : Nat) (b : Ty) hpos
    cases i with
    | zero =>
        rw [List.get?_zero_cons'] at hpos
        injection hpos with he
        subst he
        exact Or.inl rfl
    | succ m =>
        rw [List.get?_succ_cons'] at hpos
        rw [List.get?_nil'] at hpos
        contradiction
  rcases sinks_extract h hsink hf hmc hp hcc with
    ⟨Γ', t', ht, hfc', hmc', hp', hcc'⟩ | ⟨Γ', t', ht, hfc', hmc', hp', hcc'⟩
  · exact no_trace_at_oblig (size ht) ht (Nat.le_refl _) hfc' hmc' hp' hcc'
      True.intro
  · exact no_stream_without_supply (size ht) ht (Nat.le_refl _) hfc'
      (oblctx_noSSupply hcc') (by simp [NeedsS])

/-- ORIGIN (the arithmetic base of the undisciplined chase, generalized):
a fix-free mint-free derivation whose conclusion CARRIES trace-tokens
SPENDS a trace-carrying position of its context — the origin exists and
is USED. `tFlowEq` books the budget; the knower-route to traces
(`terminate`, a mint) is banned, so no supply-disjunct survives. -/
theorem origin_lemma {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ)
    (hfc : fixCount h = 0) (hmc : mintCount h = 0) (hpos : 0 < tnet τ) :
    ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ tnet b > 0 ∧ uses h i ≥ 1 := by
  have htm : tMint h = 0 := by
    rw [tMint_eq_mintCount_nofix h hfc, hmc]
    omega
  have he := tFlowEq h
  rw [htm, Int.add_zero] at he
  refine Classical.byContradiction fun hcon => ?_
  have hle : tSpend h ≤ 0 := by
    simp only [tSpend]
    refine wSpendFrom_nonpos tnet 0 Γ (uses h) ?_
    intro (i : Nat) (a : Ty) hpos'
    simp only [Nat.zero_add]
    by_cases ht : tnet a > 0
    · have hu : uses h i = 0 := by
        rcases Nat.lt_or_ge (uses h i) 1 with hlt | hge
        · omega
        · exact absurd ⟨i, a, hpos', ht, hge⟩ hcon
      rw [hu]
      simp
    · have hle' : tnet a ≤ 0 := by omega
      exact Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hle'
  omega

/-- TRACE-ORIGIN: the trace-typed instance of `origin_lemma`. -/
theorem trace_origin {Γ : List Ty} {t : Term} (h : Typed Γ t Ty.trace)
    (hfc : fixCount h = 0) (hmc : mintCount h = 0) :
    ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ tnet b > 0 ∧ uses h i ≥ 1 :=
  origin_lemma h hfc hmc (by simp [tnet])

/-! ## The chase: paths, premises, and the undisciplined kill

The undisciplined chase walks a trace-carrying VALUE to its death. The
walk needs, at each node, its PARENT and its SLOT there — carried by a
`Path` certificate built innermost-last (matching a `step` exposes the
parent and the `Prem` slot), with the counters descending along
premises and sizes strictly decreasing. -/

/-- `Prem c v`: `v` is a DIRECT premise of `c` — the slot map for the
chase's parent-analysis. -/
inductive Prem : {E : List Ty} → {tc : Term} → {τc : Ty} → Typed E tc τc →
    {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Prop where
  | lamP {a b body} {h : Typed (a :: E) body b} : Prem (.lam h) h
  | appFP {Γ Δ X b fn arg} {hf : Typed Γ fn (.arrow X b)} {ha : Typed Δ arg X}
      {hs : Γ ++ Δ = E} : Prem (.app hf ha hs) hf
  | appAP {Γ Δ X b fn arg} {hf : Typed Γ fn (.arrow X b)} {ha : Typed Δ arg X}
      {hs : Γ ++ Δ = E} : Prem (.app hf ha hs) ha
  | pairLP {Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} : Prem (.pair hl hr hs) hl
  | pairRP {Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} : Prem (.pair hl hr hs) hr
  | leteTP {Γ₁ Γ₂ a b c' t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c'} {hs : Γ₁ ++ Γ₂ = E} : Prem (.lete ht hb hs) ht
  | leteBP {Γ₁ Γ₂ a b c' t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c'} {hs : Γ₁ ++ Γ₂ = E} : Prem (.lete ht hb hs) hb
  | nextP {a t} {h : Typed E t a} : Prem (.next h) h
  | fixP {a body} {hΓ : AllNonLinear E} {h : Typed E body (.arrow (.later a) a)} :
      Prem (.fix hΓ h) h
  | consHP {Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} : Prem (.cons hc ht hs) hc
  | consTP {Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} : Prem (.cons hc ht hs) ht
  | snocTP {Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} : Prem (.snoc ht hu hs) ht
  | snocUP {Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} : Prem (.snoc ht hu hs) hu
  | contrP {k : Ty} {t τ} {hk : k.isLinear = false} {h : Typed (k :: k :: E) (Term.mergeAt 0 t) τ} :
      Prem (.contr hk h) h
  | weakP {k : Ty} {t τ} {hk : k.isLinear = false} {h : Typed E t τ} : Prem (.weak hk h) h

/-- `Path root v`: the containment certificate, built innermost-last —
matching a `step` exposes the parent's path and the slot `v` occupies
there. -/
inductive Path {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀) :
    {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Prop where
  | here : Path root root
  | step {E tc τc} {c : Typed E tc τc} {Γ t τ} {v : Typed Γ t τ}
      (p : Path root c) (s : Prem c v) : Path root v

/-- Premises are strictly smaller. -/
theorem Prem_size : ∀ {E tc τc} {c : Typed E tc τc} {Γ t τ} {v : Typed Γ t τ},
    Prem c v → size v < size c
  | _, _, _, _, _, _, _, _, Prem.lamP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.appFP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.appAP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.pairLP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.pairRP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.leteTP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.leteBP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.nextP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.fixP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.consHP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.consTP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.snocTP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.snocUP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.contrP => by simp only [size]; omega
  | _, _, _, _, _, _, _, _, Prem.weakP => by simp only [size]; omega

/-- The counters descend along premises. -/
theorem Prem_clean : ∀ {E tc τc} {c : Typed E tc τc} {Γ t τ} {v : Typed Γ t τ},
    Prem c v → fixCount c = 0 → mintCount c = 0 → fixCount v = 0 ∧ mintCount v = 0
  | _, _, _, _, _, _, _, _, Prem.lamP, hfc, hmc => by
      simp only [fixCount, mintCount] at *
      exact ⟨hfc, hmc⟩
  | _, _, _, _, _, _, _, _, Prem.appFP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h1, m1⟩
  | _, _, _, _, _, _, _, _, Prem.appAP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h2, m2⟩
  | _, _, _, _, _, _, _, _, Prem.pairLP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h1, m1⟩
  | _, _, _, _, _, _, _, _, Prem.pairRP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h2, m2⟩
  | _, _, _, _, _, _, _, _, Prem.leteTP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h1, m1⟩
  | _, _, _, _, _, _, _, _, Prem.leteBP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h2, m2⟩
  | _, _, _, _, _, _, _, _, Prem.nextP, hfc, hmc => by
      simp only [fixCount, mintCount] at *
      exact ⟨hfc, hmc⟩
  | _, _, _, _, _, _, _, _, Prem.fixP, hfc, _ => by
      simp only [fixCount] at hfc; omega
  | _, _, _, _, _, _, _, _, Prem.consHP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h1, m1⟩
  | _, _, _, _, _, _, _, _, Prem.consTP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h2, m2⟩
  | _, _, _, _, _, _, _, _, Prem.snocTP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h1, m1⟩
  | _, _, _, _, _, _, _, _, Prem.snocUP, hfc, hmc => by
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨m1, m2⟩ : mintCount _ = 0 ∧ mintCount _ = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact ⟨h2, m2⟩
  | _, _, _, _, _, _, _, _, Prem.contrP, hfc, hmc => by
      simp only [fixCount, mintCount] at *
      exact ⟨hfc, hmc⟩
  | _, _, _, _, _, _, _, _, Prem.weakP, hfc, hmc => by
      simp only [fixCount, mintCount] at *
      exact ⟨hfc, hmc⟩

/-- Σ-to-≤ : a weighted spend over a context of entirely non-positive
weights is non-positive (the sibling of `wSpendFrom_nonpos`). -/
theorem wSpendFrom_nonpos_all :
    ∀ (base : Nat) (Γ : List Ty) (u : Nat → Nat),
    (∀ (i : Nat) (a : Ty), Γ[i]? = some a → tnet a ≤ 0) →
    wSpendFrom tnet base Γ u ≤ 0
  | _, [], _, _ => by simp only [wSpendFrom]; omega
  | base, a :: Γ', u, hcon => by
      have hhead : (u base : Int) * tnet a ≤ 0 := by
        have hle := hcon 0 a (List.get?_zero_cons')
        exact Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hle
      have htail := wSpendFrom_nonpos_all (base + 1) Γ' u (fun (i : Nat) (a' : Ty) hpos => by
        exact hcon (i + 1) a' (by simpa only [List.get?_succ_cons'] using hpos))
      simp only [wSpendFrom]
      omega

/-- NO λ-PRODUCER over a non-positive context (the λ-bottom seed of the
producer lemma): a clean λ's body cannot conclude a tnet-positive type
when every context position (its own domain included) is non-positive —
`tFlowEq` books the impossible budget. The domain-sign condition of the
original corner is unnecessary: linearity plays no role, only the
weights. -/
theorem lam_no_producer {Γ : List Ty} {c σ : Ty} {body : Term}
    (h : Typed (c :: Γ) body σ)
    (hfc : fixCount h = 0) (hmc : mintCount h = 0)
    (hnp : ∀ (j : Nat) (b : Ty), (c :: Γ)[j]? = some b → tnet b ≤ 0)
    (hσ : 0 < tnet σ) : False := by
  have htm : tMint h = 0 := by
    rw [tMint_eq_mintCount_nofix h hfc, hmc]
    omega
  have he := tFlowEq h
  rw [htm, Int.add_zero] at he
  have hle : tSpend h ≤ 0 := by
    simp only [tSpend]
    exact wSpendFrom_nonpos_all 0 (c :: Γ) (uses h) hnp
  omega

/-! ## The read-locator: a spent position's read, with its parent -/

/-- READ-LOCATE: a spent position is read by a var-node in one of three
positions: deep (the read sits under a strict subderivation-parent),
direct (one of `d`'s own premises is the read), or top (`d` itself is
the read). The locator descends by `uses`' own split arithmetic — the
position flows to exactly one premise at each rule. The consumer round
case-maps on the returned `Prem` slot; the var-evidence travels as
explicit equalities (no casts across the Type-valued family). -/
theorem read_locate : ∀ (n : Nat) {Γ : List Ty} {τ : Ty} {t : Term} (d : Typed Γ t τ),
    size d ≤ n → ∀ (i : Nat) (a : Ty), Γ[i]? = some a → uses d i ≥ 1 →
    (∃ (E : List Ty) (tp : Term) (τp : Ty) (p : Typed E tp τp),
        Sub d p ∧ ∃ (Γv : List Ty) (tv : Term) (τv : Ty) (v : Typed Γv tv τv),
          Prem p v ∧ tv = Term.var 0 ∧ τv = a)
    ∨ (∃ (Γv : List Ty) (tv : Term) (τv : Ty) (v : Typed Γv tv τv),
          Prem d v ∧ tv = Term.var 0 ∧ τv = a)
    ∨ (Γ = [a] ∧ t = Term.var 0 ∧ τ = a ∧ i = 0)
  | _, _, _, _, Typed.var, _, i, a, hpos, _ => by
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with he
          subst he
          exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
      | succ m =>
          rw [List.get?_succ_cons'] at hpos
          rw [List.get?_nil'] at hpos
          contradiction
  | 0, _, _, _, h, hn, _, _, _, _ => absurd hn (Nat.not_le_of_lt (size_pos h))
  | n + 1, _, _, _, @Typed.lam Γ c b body hbody, hn, i, a, hpos, hus => by
      rcases read_locate n hbody (by rw [size_lam] at hn; omega) (i + 1) a
        (by rw [List.get?_succ_cons']; exact hpos)
        (by simpa only [uses] using hus) with
        ⟨E, tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, _, _, hi⟩
      · exact Or.inl ⟨E, tp, τp, p, Sub.lam hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
      · exact Or.inl ⟨_, _, _, hbody, Sub.lamD, Γv, tv, τv, v, hprem, htv, hτv⟩
      · omega
  | n + 1, _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs, hn, i, a, hpos, hus => by
      by_cases hlt : i < Γ.length
      · rcases read_locate n hf (by rw [size_app] at hn; omega) i a
          (by rw [← hs, List.get?_append_lt hlt] at hpos; exact hpos)
          (by simpa only [uses, if_pos hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.appL hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, hf, Sub.appLD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨Γ, fn, Ty.arrow X b, hf, Prem.appFP, htv, hτv⟩)
      · have hge : Γ.length ≤ i := Nat.not_lt.mp hlt
        rcases read_locate n ha (by rw [size_app] at hn; omega) (i - Γ.length) a
          (by rw [← hs, List.get?_append_ge hge] at hpos; exact hpos)
          (by simpa only [uses, if_neg hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.appR hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, ha, Sub.appRD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨Δ, arg, X, ha, Prem.appAP, htv, hτv⟩)
  | n + 1, _, _, _, @Typed.pair E Γ Δ x y l r hl hr hs, hn, i, a, hpos, hus => by
      by_cases hlt : i < Γ.length
      · rcases read_locate n hl (by rw [size_pair] at hn; omega) i a
          (by rw [← hs, List.get?_append_lt hlt] at hpos; exact hpos)
          (by simpa only [uses, if_pos hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.pairL hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, hl, Sub.pairLD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨Γ, l, x, hl, Prem.pairLP, htv, hτv⟩)
      · have hge : Γ.length ≤ i := Nat.not_lt.mp hlt
        rcases read_locate n hr (by rw [size_pair] at hn; omega) (i - Γ.length) a
          (by rw [← hs, List.get?_append_ge hge] at hpos; exact hpos)
          (by simpa only [uses, if_neg hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.pairR hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, hr, Sub.pairRD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨Δ, r, y, hr, Prem.pairRP, htv, hτv⟩)
  | n + 1, _, _, _, @Typed.lete E Γ₁ Γ₂ x y c t body ht hb hs, hn, i, a, hpos, hus => by
      by_cases hlt : i < Γ₁.length
      · rcases read_locate n ht (by rw [size_lete] at hn; omega) i a
          (by rw [← hs, List.get?_append_lt hlt] at hpos; exact hpos)
          (by simpa only [uses, if_pos hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.leteT hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, ht, Sub.leteTD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨Γ₁, t, Ty.tensor x y, ht, Prem.leteTP, htv, hτv⟩)
      · have hge : Γ₁.length ≤ i := Nat.not_lt.mp hlt
        rcases read_locate n hb (by rw [size_lete] at hn; omega) (i - Γ₁.length + 2) a
          (by rw [List.get?_add_two, ← List.get?_append_ge hge, hs]; exact hpos)
          (by simpa only [uses, if_neg hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.leteB hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, hb, Sub.leteBD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨y :: x :: Γ₂, body, c, hb, Prem.leteBP, htv, hτv⟩)
  | n + 1, _, _, _, @Typed.next Γ x t h, hn, i, a, hpos, hus => by
      rcases read_locate n h (by rw [size_next] at hn; omega) i a hpos hus with
        ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
      · exact Or.inl ⟨E', tp, τp, p, Sub.next hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
      · exact Or.inl ⟨_, _, _, h, Sub.nextD, Γv, tv, τv, v, hprem, htv, hτv⟩
      · exact Or.inr (Or.inl ⟨Γ, t, x, h, Prem.nextP, htv, hτv⟩)
  | n + 1, _, _, _, @Typed.fix Γ x body hΓ h, hn, i, a, hpos, hus => by
      rcases read_locate n h (by rw [size_fix] at hn; omega) i a hpos hus with
        ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
      · exact Or.inl ⟨E', tp, τp, p, Sub.fix hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
      · exact Or.inl ⟨_, _, _, h, Sub.fixD, Γv, tv, τv, v, hprem, htv, hτv⟩
      · exact Or.inr (Or.inl ⟨Γ, body, Ty.arrow (Ty.later x) x, h, Prem.fixP, htv, hτv⟩)
  | n + 1, _, _, _, @Typed.contr Γ k t τ hk h, hn, i, a, hpos, hus => by
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hka
          have hsplit : uses h 0 + uses h 1 ≥ 1 := hus
          rcases Nat.lt_or_ge (uses h 0) 1 with hlt | hge
          · rcases read_locate n h (by rw [size_contr] at hn; omega) 1 a
              (by rw [List.get?_succ_cons', hka]; rfl) (by omega) with
              ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
            · exact Or.inl ⟨E', tp, τp, p, Sub.contr hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
            · exact Or.inl ⟨_, _, _, h, Sub.contrD, Γv, tv, τv, v, hprem, htv, hτv⟩
            · exact Or.inr (Or.inl ⟨k :: k :: Γ, Term.mergeAt 0 t, τ, h, Prem.contrP, htv, hτv⟩)
          · rcases read_locate n h (by rw [size_contr] at hn; omega) 0 a
              (by rw [hka]; rfl) (by omega) with
              ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
            · exact Or.inl ⟨E', tp, τp, p, Sub.contr hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
            · exact Or.inl ⟨_, _, _, h, Sub.contrD, Γv, tv, τv, v, hprem, htv, hτv⟩
            · exact Or.inr (Or.inl ⟨k :: k :: Γ, Term.mergeAt 0 t, τ, h, Prem.contrP, htv, hτv⟩)
      | succ m =>
          have hus' : uses h (m + 1 + 1) ≥ 1 := by
            simpa only [uses, if_neg (Nat.succ_ne_zero m)] using hus
          rw [List.get?_succ_cons'] at hpos
          rcases read_locate n h (by rw [size_contr] at hn; omega) (m + 1 + 1) a
            (by rw [List.get?_add_two]; exact hpos) hus' with
            ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, _, _, hi⟩
          · exact Or.inl ⟨E', tp, τp, p, Sub.contr hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
          · exact Or.inl ⟨_, _, _, h, Sub.contrD, Γv, tv, τv, v, hprem, htv, hτv⟩
          · omega
  | n + 1, _, _, _, @Typed.weak Γ k t τ hk h, hn, i, a, hpos, hus => by
      cases i with
      | zero =>
          have h0 : uses (Typed.weak hk h) 0 = 0 := rfl
          rw [h0] at hus
          omega
      | succ m =>
          rw [List.get?_succ_cons'] at hpos
          rcases read_locate n h (by rw [size_weak] at hn; omega) m a hpos
            (by simpa only [uses, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel] using hus) with
            ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
          · exact Or.inl ⟨E', tp, τp, p, Sub.weak hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
          · exact Or.inl ⟨_, _, _, h, Sub.weakD, Γv, tv, τv, v, hprem, htv, hτv⟩
          · exact Or.inr (Or.inl ⟨Γ, t, τ, h, Prem.weakP, htv, hτv⟩)
  | n + 1, _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, hn, i, a, hpos, hus => by
      by_cases hlt : i < Γ.length
      · rcases read_locate n hc (by rw [size_cons] at hn; omega) i a
          (by rw [← hs, List.get?_append_lt hlt] at hpos; exact hpos)
          (by simpa only [uses, if_pos hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.consH hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, hc, Sub.consHD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨Γ, hd, Ty.content, hc, Prem.consHP, htv, hτv⟩)
      · have hge : Γ.length ≤ i := Nat.not_lt.mp hlt
        rcases read_locate n ht (by rw [size_cons] at hn; omega) (i - Γ.length) a
          (by rw [← hs, List.get?_append_ge hge] at hpos; exact hpos)
          (by simpa only [uses, if_neg hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.consT hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, ht, Sub.consTD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨Δ, tl, Ty.later Ty.stream, ht, Prem.consTP, htv, hτv⟩)
  | n + 1, _, _, _, @Typed.snoc E Γ Δ t u ht hu hs, hn, i, a, hpos, hus => by
      by_cases hlt : i < Γ.length
      · rcases read_locate n ht (by rw [size_snoc] at hn; omega) i a
          (by rw [← hs, List.get?_append_lt hlt] at hpos; exact hpos)
          (by simpa only [uses, if_pos hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.snocT hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, ht, Sub.snocTD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨Γ, t, Ty.trace, ht, Prem.snocTP, htv, hτv⟩)
      · have hge : Γ.length ≤ i := Nat.not_lt.mp hlt
        rcases read_locate n hu (by rw [size_snoc] at hn; omega) (i - Γ.length) a
          (by rw [← hs, List.get?_append_ge hge] at hpos; exact hpos)
          (by simpa only [uses, if_neg hlt] using hus) with
          ⟨E', tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ | ⟨_, htv, hτv, _⟩
        · exact Or.inl ⟨E', tp, τp, p, Sub.snocU hsub, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inl ⟨_, _, _, hu, Sub.snocUD, Γv, tv, τv, v, hprem, htv, hτv⟩
        · exact Or.inr (Or.inl ⟨Δ, u, Ty.content, hu, Prem.snocUP, htv, hτv⟩)
  | n + 1, _, _, _, Typed.unit, _, _, _, _, hus => by
      simp only [uses] at hus; omega
  | n + 1, _, _, _, Typed.nil, _, _, _, _, hus => by
      simp only [uses] at hus; omega
  | n + 1, _, _, _, Typed.gen, _, _, _, _, hus => by
      simp only [uses] at hus; omega
  | n + 1, _, _, _, Typed.red, _, _, _, _, hus => by
      simp only [uses] at hus; omega
  | n + 1, _, _, _, Typed.obj, _, _, _, _, hus => by
      simp only [uses] at hus; omega
  | n + 1, _, _, _, Typed.terminate, _, _, _, _, hus => by
      simp only [uses] at hus; omega

/-- Sub is transitive: deep-inside composes. Induction on the OUTER
certificate — every direct base pairs with its wrapping constructor,
every wrapping case re-wraps the IH. -/
theorem Sub_trans : ∀ {E₁ : List Ty} {t₁ : Term} {τ₁ : Ty} {a : Typed E₁ t₁ τ₁}
    {E₂ : List Ty} {t₂ : Term} {τ₂ : Ty} {b : Typed E₂ t₂ τ₂},
    Sub a b → ∀ {E₃ : List Ty} {t₃ : Term} {τ₃ : Ty} {c : Typed E₃ t₃ τ₃}, Sub b c → Sub a c := by
  intro E₁ t₁ τ₁ a E₂ t₂ τ₂ b h1
  induction h1 with
  | lam s ih => intro _ _ _ _ h2; exact Sub.lam (ih h2)
  | appL s ih => intro _ _ _ _ h2; exact Sub.appL (ih h2)
  | appR s ih => intro _ _ _ _ h2; exact Sub.appR (ih h2)
  | pairL s ih => intro _ _ _ _ h2; exact Sub.pairL (ih h2)
  | pairR s ih => intro _ _ _ _ h2; exact Sub.pairR (ih h2)
  | leteT s ih => intro _ _ _ _ h2; exact Sub.leteT (ih h2)
  | leteB s ih => intro _ _ _ _ h2; exact Sub.leteB (ih h2)
  | next s ih => intro _ _ _ _ h2; exact Sub.next (ih h2)
  | fix s ih => intro _ _ _ _ h2; exact Sub.fix (ih h2)
  | consH s ih => intro _ _ _ _ h2; exact Sub.consH (ih h2)
  | consT s ih => intro _ _ _ _ h2; exact Sub.consT (ih h2)
  | snocT s ih => intro _ _ _ _ h2; exact Sub.snocT (ih h2)
  | snocU s ih => intro _ _ _ _ h2; exact Sub.snocU (ih h2)
  | contr s ih => intro _ _ _ _ h2; exact Sub.contr (ih h2)
  | weak s ih => intro _ _ _ _ h2; exact Sub.weak (ih h2)
  | lamD => intro _ _ _ _ h2; exact Sub.lam h2
  | appLD => intro _ _ _ _ h2; exact Sub.appL h2
  | appRD => intro _ _ _ _ h2; exact Sub.appR h2
  | pairLD => intro _ _ _ _ h2; exact Sub.pairL h2
  | pairRD => intro _ _ _ _ h2; exact Sub.pairR h2
  | leteTD => intro _ _ _ _ h2; exact Sub.leteT h2
  | leteBD => intro _ _ _ _ h2; exact Sub.leteB h2
  | nextD => intro _ _ _ _ h2; exact Sub.next h2
  | fixD => intro _ _ _ _ h2; exact Sub.fix h2
  | consHD => intro _ _ _ _ h2; exact Sub.consH h2
  | consTD => intro _ _ _ _ h2; exact Sub.consT h2
  | snocTD => intro _ _ _ _ h2; exact Sub.snocT h2
  | snocUD => intro _ _ _ _ h2; exact Sub.snocU h2
  | contrD => intro _ _ _ _ h2; exact Sub.contr h2
  | weakD => intro _ _ _ _ h2; exact Sub.weak h2

/-- A node INTRODUCES a position of type `a` into its premise's
context: λ-domains and lete-components. -/
inductive Introduces : {E : List Ty} → {tp : Term} → {τp : Ty} → Typed E tp τp → Ty → Prop where
  | lamI {E : List Ty} {σ : Ty} {body : Term} {a : Ty} (hb : Typed (a :: E) body σ) :
      Introduces (Typed.lam hb) a
  | leteIY {E Γ₁ Γ₂ : List Ty} {x y c : Ty} {s body : Term}
      {ht : Typed Γ₁ s (.tensor x y)} {hb : Typed (y :: x :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E} :
      Introduces (Typed.lete ht hb hs) y
  | leteIX {E Γ₁ Γ₂ : List Ty} {x y c : Ty} {s body : Term}
      {ht : Typed Γ₁ s (.tensor x y)} {hb : Typed (y :: x :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E} :
      Introduces (Typed.lete ht hb hs) x

/-! ## Position provenance

A position in a subderivation's context either is supplied by the root's
own context or was INTRODUCED by a binder on the path down — the
position-trace-up of the chase's origin analysis. Pure position
existence: no spend, no sign condition. The induction matches the
containment certificate and then the PARENT-SLOT certificate (whose
pattern carries the parent's context as its FIRST slot); each case's
position preimage is the split arithmetic (prefix sides keep the index,
suffix sides shift by the split, `contr` merges 0/1, `weak` shifts past
the drop). -/

/-- POSITION-INTRODUCED: walking a `Path` from the root, every context
position of the endpoint either pre-exists in the root's context or is
introduced by a λ-domain / lete-component AT A NODE ON THE PATH strictly
above the endpoint. -/
theorem pos_introduced {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d) :
    ∀ (i : Nat) (a : Ty), Γ[i]? = some a →
    (∃ (j : Nat), Γ₀[j]? = some a) ∨
    (∃ (E' : List Ty) (tp : Term) (τp : Ty) (β : Typed E' tp τp),
        Path root β ∧ Introduces β a ∧ Sub β d) := by
  induction hp with
  | here => intro i a hpos; exact Or.inl ⟨i, hpos⟩
  | step p s ih =>
      intro i a hpos
      match s with
      | @Prem.lamP E' dom bb body hbody =>
          cases i with
          | zero =>
              rw [List.get?_zero_cons'] at hpos
              injection hpos with hdom
              subst hdom
              exact Or.inr ⟨_, _, _, Typed.lam hbody, p, Introduces.lamI hbody, Sub.lamD⟩
          | succ m =>
              rw [List.get?_succ_cons'] at hpos
              rcases ih m a hpos with
                ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
              · exact Or.inl ⟨j, hj⟩
              · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.lamD⟩
      | @Prem.appFP E' Γf Δ X bb fn arg hf ha hs =>
          have hlt : i < Γf.length := List.get?_some_lt hpos
          rcases ih i a
            (by rw [← hs, List.get?_append_lt hlt]; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.appLD⟩
      | @Prem.appAP E' Γf Δ X bb fn arg hf ha hs =>
          have hge : Γf.length ≤ Γf.length + i := Nat.le_add_right Γf.length i
          rcases ih (Γf.length + i) a
            (by rw [← hs, List.get?_append_ge hge, Nat.add_sub_cancel_left]; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.appRD⟩
      | @Prem.pairLP E' Γf Δ x y l r hl hr hs =>
          have hlt : i < Γf.length := List.get?_some_lt hpos
          rcases ih i a
            (by rw [← hs, List.get?_append_lt hlt]; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.pairLD⟩
      | @Prem.pairRP E' Γf Δ x y l r hl hr hs =>
          have hge : Γf.length ≤ Γf.length + i := Nat.le_add_right Γf.length i
          rcases ih (Γf.length + i) a
            (by rw [← hs, List.get?_append_ge hge, Nat.add_sub_cancel_left]; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.pairRD⟩
      | @Prem.leteTP E' Γ₁ Γ₂ x y cc s' body ht hb hs =>
          have hlt : i < Γ₁.length := List.get?_some_lt hpos
          rcases ih i a
            (by rw [← hs, List.get?_append_lt hlt]; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.leteTD⟩
      | @Prem.leteBP E' Γ₁ Γ₂ x y cc s' body ht hb hs =>
          cases i with
          | zero =>
              rw [List.get?_zero_cons'] at hpos
              injection hpos with hyy
              subst hyy
              exact Or.inr ⟨_, _, _, Typed.lete ht hb hs, p, Introduces.leteIY,
                Sub.leteBD⟩
          | succ m =>
              cases m with
              | zero =>
                  rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                  injection hpos with hxx
                  subst hxx
                  exact Or.inr ⟨_, _, _, Typed.lete ht hb hs, p, Introduces.leteIX,
                    Sub.leteBD⟩
              | succ m' =>
                  rw [List.get?_add_two] at hpos
                  have hge : Γ₁.length ≤ Γ₁.length + m' := Nat.le_add_right Γ₁.length m'
                  rcases ih (Γ₁.length + m') a
                    (by rw [← hs, List.get?_append_ge hge, Nat.add_sub_cancel_left]; exact hpos) with
                    ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
                  · exact Or.inl ⟨j, hj⟩
                  · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.leteBD⟩
      | @Prem.nextP E' x t' h =>
          rcases ih i a hpos with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.nextD⟩
      | @Prem.fixP E' x body hΓ h =>
          rcases ih i a hpos with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.fixD⟩
      | @Prem.consHP E' Γf Δ hd tl hc ht hs =>
          have hlt : i < Γf.length := List.get?_some_lt hpos
          rcases ih i a
            (by rw [← hs, List.get?_append_lt hlt]; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.consHD⟩
      | @Prem.consTP E' Γf Δ hd tl hc ht hs =>
          have hge : Γf.length ≤ Γf.length + i := Nat.le_add_right Γf.length i
          rcases ih (Γf.length + i) a
            (by rw [← hs, List.get?_append_ge hge, Nat.add_sub_cancel_left]; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.consTD⟩
      | @Prem.snocTP E' Γf Δ u' c' ht hu hs =>
          have hlt : i < Γf.length := List.get?_some_lt hpos
          rcases ih i a
            (by rw [← hs, List.get?_append_lt hlt]; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.snocTD⟩
      | @Prem.snocUP E' Γf Δ u' c' ht hu hs =>
          have hge : Γf.length ≤ Γf.length + i := Nat.le_add_right Γf.length i
          rcases ih (Γf.length + i) a
            (by rw [← hs, List.get?_append_ge hge, Nat.add_sub_cancel_left]; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.snocUD⟩
      | @Prem.contrP E' k t' τ' hk h =>
          cases i with
          | zero =>
              rw [List.get?_zero_cons'] at hpos
              injection hpos with hka
              subst hka
              rcases ih 0 k (by rw [List.get?_zero_cons']) with
                ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
              · exact Or.inl ⟨j, hj⟩
              · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.contrD⟩
          | succ m =>
              cases m with
              | zero =>
                  rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
                  injection hpos with hka
                  subst hka
                  rcases ih 0 k (by rw [List.get?_zero_cons']) with
                    ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
                  · exact Or.inl ⟨j, hj⟩
                  · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.contrD⟩
              | succ m' =>
                  rw [List.get?_add_two] at hpos
                  rcases ih (m' + 1) a
                    (by rw [List.get?_succ_cons']; exact hpos) with
                    ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
                  · exact Or.inl ⟨j, hj⟩
                  · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.contrD⟩
      | @Prem.weakP E' k t' τ' hk h =>
          rcases ih (i + 1) a
            (by rw [List.get?_succ_cons']; exact hpos) with
            ⟨j, hj⟩ | ⟨E₂, tp, τp, β, hpβ, hint, hsub⟩
          · exact Or.inl ⟨j, hj⟩
          · exact Or.inr ⟨_, _, _, β, hpβ, hint, Sub_trans hsub Sub.weakD⟩

/-- Counters descend along any containment path. -/
theorem Path_clean {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d) :
    fixCount root = 0 → mintCount root = 0 → fixCount d = 0 ∧ mintCount d = 0 := by
  induction hp with
  | here => intro hfc hmc; exact ⟨hfc, hmc⟩
  | step p s ih =>
      intro hfc hmc
      obtain ⟨hfc', hmc'⟩ := ih hfc hmc
      exact Prem_clean s hfc' hmc'

/-- Every non-root node on a path has its parent on the path — the
containment certificate inverts one level. The root case returns the
index equalities (contexts/terms/types — no casts across the
Type-valued family). -/
theorem parent_locate {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d) :
    (∃ (E : List Ty) (tp : Term) (τp : Ty) (c : Typed E tp τp),
      Path root c ∧ Prem c d) ∨ (Γ = Γ₀ ∧ t = t₀ ∧ τ = τ₀) := by
  cases hp with
  | here => exact Or.inr ⟨rfl, rfl, rfl⟩
  | step p s => exact Or.inl ⟨_, _, _, _, p, s⟩

/-- SINK-EXTRACTION, counters-only (the undisciplined version): in a
fix-free mint-free tree, a sink node's KILLED premise is itself fix-free
and mint-free — no discipline is carried (undisciplined contexts are the
S3 chase's subject; the counters are what descend unconditionally). The
containment certificate rides along: the chase enters at the extracted
premise WITH its `Path` from the root. -/
theorem sinks_extract' :
    ∀ {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀),
    ∀ {Γ : List Ty} {τ : Ty} {t : Term} (h : Typed Γ t τ), Path root h →
    0 < sinks h → fixCount h = 0 → mintCount h = 0 →
    (∃ (Γ' : List Ty) (t' : Term) (ht : Typed Γ' t' Ty.trace),
        Path root ht ∧ fixCount ht = 0 ∧ mintCount ht = 0)
    ∨ (∃ (Γ' : List Ty) (t' : Term) (ht : Typed Γ' t' (.later Ty.stream)),
        Path root ht ∧ fixCount ht = 0 ∧ mintCount ht = 0)
  | _, _, _, root, _, _, _, @Typed.snoc E Γ Δ t u ht hu hs, hp, _, hfc, hmc => by
      obtain ⟨hfc1, _⟩ : fixCount ht = 0 ∧ fixCount hu = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, _⟩ : mintCount ht = 0 ∧ mintCount hu = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact Or.inl ⟨Γ, t, ht, Path.step hp Prem.snocTP, hfc1, hmc1⟩
  | _, _, _, root, _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs, hp, _, hfc, hmc => by
      obtain ⟨_, hfc2⟩ : fixCount hc = 0 ∧ fixCount ht = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨_, hmc2⟩ : mintCount hc = 0 ∧ mintCount ht = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      exact Or.inr ⟨Δ, tl, ht, Path.step hp Prem.consTP, hfc2, hmc2⟩
  | _, _, _, root, _, _, _, @Typed.lam _ _ _ _ h, hp, hsink, hfc, hmc =>
      sinks_extract' root h (Path.step hp Prem.lamP) hsink
        (by simpa only [fixCount] using hfc)
        (by simpa only [mintCount] using hmc)
  | _, _, _, root, _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _, hp, hsink, hfc, hmc => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hf = 0 ∧ fixCount ha = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hf = 0 ∧ mintCount ha = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      simp only [sinks] at hsink
      by_cases hsl : 0 < sinks hf
      · exact sinks_extract' root hf (Path.step hp Prem.appFP) hsl hfc1 hmc1
      · have hsr : 0 < sinks ha := by omega
        exact sinks_extract' root ha (Path.step hp Prem.appAP) hsr hfc2 hmc2
  | _, _, _, root, _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _, hp, hsink, hfc, hmc => by
      obtain ⟨hfc1, hfc2⟩ : fixCount hl = 0 ∧ fixCount hr = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount hl = 0 ∧ mintCount hr = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      simp only [sinks] at hsink
      by_cases hsl : 0 < sinks hl
      · exact sinks_extract' root hl (Path.step hp Prem.pairLP) hsl hfc1 hmc1
      · have hsr : 0 < sinks hr := by omega
        exact sinks_extract' root hr (Path.step hp Prem.pairRP) hsr hfc2 hmc2
  | _, _, _, root, _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _, hp, hsink, hfc, hmc => by
      obtain ⟨hfc1, hfc2⟩ : fixCount ht = 0 ∧ fixCount hb = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      obtain ⟨hmc1, hmc2⟩ : mintCount ht = 0 ∧ mintCount hb = 0 := by
        simpa only [mintCount, Nat.add_eq_zero_iff] using hmc
      simp only [sinks] at hsink
      by_cases hst : 0 < sinks ht
      · exact sinks_extract' root ht (Path.step hp Prem.leteTP) hst hfc1 hmc1
      · have hsb : 0 < sinks hb := by omega
        exact sinks_extract' root hb (Path.step hp Prem.leteBP) hsb hfc2 hmc2
  | _, _, _, root, _, _, _, @Typed.next _ _ _ h, hp, hsink, hfc, hmc =>
      sinks_extract' root h (Path.step hp Prem.nextP) hsink
        (by simpa only [fixCount] using hfc)
        (by simpa only [mintCount] using hmc)
  | _, _, _, root, _, _, _, @Typed.contr _ _ _ _ _ h, hp, hsink, hfc, hmc =>
      sinks_extract' root h (Path.step hp Prem.contrP) hsink
        (by simpa only [fixCount] using hfc)
        (by simpa only [mintCount] using hmc)
  | _, _, _, root, _, _, _, @Typed.weak _ _ _ _ _ h, hp, hsink, hfc, hmc =>
      sinks_extract' root h (Path.step hp Prem.weakP) hsink
        (by simpa only [fixCount] using hfc)
        (by simpa only [mintCount] using hmc)
  | _, _, _, _, _, _, _, @Typed.fix _ _ _ _ _, _, _, hfc, _ =>
      absurd hfc (by simp only [fixCount]; omega)
  | _, _, _, _, _, _, _, Typed.var, _, hsink, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, _, _, _, _, Typed.unit, _, hsink, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, _, _, _, _, Typed.nil, _, hsink, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, _, _, _, _, Typed.gen, _, hsink, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, _, _, _, _, Typed.red, _, hsink, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, _, _, _, _, Typed.obj, _, hsink, _, _ => by
      simp only [sinks] at hsink; omega
  | _, _, _, _, _, _, _, Typed.terminate, _, hsink, _, _ => by
      simp only [sinks] at hsink; omega

/-! ## The stream account: `snet`, `sFlowEq`, `stream_origin`

The cons-side of the kill needs its own arithmetic: `tnet` counts traces
only (`tnet stream = 0`), so a `▷stream` conclusion balances nothing
there. `snet` counts stream-tokens instead. The MINT SIGNATURE differs
from `tMint` in the load-bearing way: `red` and `obj` are NEGATIVE mints
(debts — their own types owe a stream-token: `snet (arrow stream
knowledge) = −1`), while `nil`/`terminate`/`gen` mint nothing at the
stream sort. A stream consumed by a `red`-fire is paid for by the
constant's own type-debt — the same neutrality `tFlowEq` gives
killer-apps, at a constant. The fixpoint MINTS the stream it unrolls
(`+ snet a`) — the epistemic cycle is the only stream source in the
grammar, which is exactly why the fix-free fragment can afford this
account. -/

/-- Stream-net: stream ↦ 1, arrows owe codomain and are owed domain. -/
def snet : Ty → Int
  | .stream => 1
  | .later a => snet a
  | .tensor a b => snet a + snet b
  | .arrow a b => snet b - snet a
  | _ => 0

/-- Non-linear types carry no stream-tokens (stream is linear). -/
theorem nonlinear_snet : ∀ a : Ty, a.isLinear = false → snet a = 0 := by
  intro a
  cases a with
  | content => intro h; exact Bool.noConfusion h
  | trace => intro h; exact Bool.noConfusion h
  | stream => intro h; exact Bool.noConfusion h
  | knower | knowledge | value | unit => intro _; rfl
  | later a' => intro h; exact nonlinear_snet a' h
  | tensor a' b' =>
      intro h
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using h)
      rw [snet, nonlinear_snet a' h'.1, nonlinear_snet b' h'.2]; rfl
  | arrow a' b' =>
      intro h
      have h' := Bool.or_eq_false_iff.mp (by simpa only [Ty.isLinear] using h)
      rw [snet, nonlinear_snet b' h'.2, nonlinear_snet a' h'.1]; rfl

/-- Stream-weighted spend of a derivation's context. -/
def sSpend {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ) : Int :=
  wSpendFrom snet 0 Γ (uses h)

/-- FUSION for streams: at any hypothesis position the stream-weighted
spend is EXACT. -/
theorem binder_sexact : ∀ (a : Ty) {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ)
    {i : Nat} (hpos : Γ[i]? = some a), (uses h i : Int) * snet a = snet a := by
  intro a Γ t τ h i hpos
  cases hlin : a.isLinear with
  | true =>
      have hu := single_linear_use h i a hpos hlin
      rw [hu]
      simp
  | false =>
      have h0 := nonlinear_snet a hlin
      rw [h0, Int.mul_zero]

/-- Stream MINTS: `red`/`obj` are DEBTS (each owes one stream-token),
the guarded fixpoint mints its conclusion's tokens. -/
def sMint : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Int
  | _, _, _, Typed.red => -1
  | _, _, _, Typed.obj => -1
  | _, _, _, @Typed.fix _ a _ _ h => sMint h + snet a
  | _, _, _, @Typed.lam _ _ _ _ h => sMint h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => sMint hf + sMint ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => sMint hl + sMint hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => sMint ht + sMint hb
  | _, _, _, @Typed.next _ _ _ h => sMint h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => sMint hc + sMint ht
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => sMint ht + sMint hu
  | _, _, _, @Typed.contr _ _ _ _ _ h => sMint h
  | _, _, _, @Typed.weak _ _ _ _ _ h => sMint h
  | _, _, _, _ => 0

/-- THE STREAM FLOW EQUALITY: the stream-tokens the conclusion carries
equal what the context spent plus what was minted (the fixpoint) minus
what the reducers owe (`red`/`obj` debts). The `tFlowEq` template at the
stream weight. -/
theorem sFlowEq : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    snet τ = sSpend h + sMint h
  | _, _, _, Typed.var => by
      simp [sSpend, wSpendFrom, uses, snet, sMint]
  | _, _, _, @Typed.lam Γ a b body h => by
      have ih := sFlowEq h
      have hb := binder_sexact a h (List.get?_zero_cons')
      have hsplit : sSpend (Γ := a :: Γ) h
          = (uses h 0 : Int) * snet a + wSpendFrom snet 1 Γ (uses h) := rfl
      rw [hsplit] at ih
      have hreb : wSpendFrom snet 0 Γ (uses (@Typed.lam Γ a b body h))
          = wSpendFrom snet 1 Γ (uses h) :=
        wSpendFrom_rebase snet Γ (uses (@Typed.lam Γ a b body h)) (uses h) 0 1
          fun i => by rw [Nat.zero_add, Nat.add_comm 1 i]; rfl
      show snet (a.arrow b) = _
      simp only [sSpend, snet, sMint] at ih ⊢
      rw [hb] at ih
      clear hb
      rw [hreb]
      omega
  | _, _, _, @Typed.app E Γ Δ X b fn arg hf ha hs => by
      have ihf := sFlowEq hf
      have iha := sFlowEq ha
      subst hs
      have h1 : wSpendFrom snet 0 Γ (uses (@Typed.app (Γ ++ Δ) Γ Δ X b fn arg hf ha rfl))
          = wSpendFrom snet 0 Γ (uses hf) :=
        wSpendFrom_congr snet Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hf i else uses ha (i - Γ.length)) = uses hf i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom snet (0 + Γ.length) Δ (uses (@Typed.app (Γ ++ Δ) Γ Δ X b fn arg hf ha rfl))
          = wSpendFrom snet 0 Δ (uses ha) :=
        wSpendFrom_rebase snet Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hf (0 + Γ.length + i)
                else uses ha (0 + Γ.length + i - Γ.length)) = uses ha (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show snet b = _
      simp only [sSpend] at ihf iha ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [snet, sMint] at ihf iha ⊢
      omega
  | _, _, _, @Typed.pair E Γ Δ a b l r hl hr hs => by
      have ihl := sFlowEq hl
      have ihr := sFlowEq hr
      subst hs
      have h1 : wSpendFrom snet 0 Γ (uses (@Typed.pair (Γ ++ Δ) Γ Δ a b l r hl hr rfl))
          = wSpendFrom snet 0 Γ (uses hl) :=
        wSpendFrom_congr snet Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hl i else uses hr (i - Γ.length)) = uses hl i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom snet (0 + Γ.length) Δ (uses (@Typed.pair (Γ ++ Δ) Γ Δ a b l r hl hr rfl))
          = wSpendFrom snet 0 Δ (uses hr) :=
        wSpendFrom_rebase snet Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hl (0 + Γ.length + i)
                else uses hr (0 + Γ.length + i - Γ.length)) = uses hr (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show snet (a.tensor b) = _
      simp only [sSpend] at ihl ihr ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [snet, sMint] at ihl ihr ⊢
      omega
  | _, _, _, @Typed.lete E Γ₁ Γ₂ a b c t body ht hb hs => by
      have iht := sFlowEq ht
      have ihb := sFlowEq hb
      have hb0 := binder_sexact b hb (List.get?_zero_cons')
      have hb1 := binder_sexact a hb (by rw [List.get?_succ_cons']; exact List.get?_zero_cons')
      have hsplit : sSpend (Γ := b :: a :: Γ₂) hb
          = (uses hb 0 : Int) * snet b + ((uses hb 1 : Int) * snet a
            + wSpendFrom snet 2 Γ₂ (uses hb)) := rfl
      rw [hsplit] at ihb
      rw [hb0, hb1] at ihb
      clear hb0 hb1
      subst hs
      have h1 : wSpendFrom snet 0 Γ₁ (uses (@Typed.lete (Γ₁ ++ Γ₂) Γ₁ Γ₂ a b c t body ht hb rfl))
          = wSpendFrom snet 0 Γ₁ (uses ht) :=
        wSpendFrom_congr snet Γ₁ _ _ 0 fun i _ hilt => by
          show (if i < Γ₁.length then uses ht i else uses hb (i - Γ₁.length + 2)) = uses ht i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom snet (0 + Γ₁.length) Γ₂ (uses (@Typed.lete (Γ₁ ++ Γ₂) Γ₁ Γ₂ a b c t body ht hb rfl))
          = wSpendFrom snet 2 Γ₂ (uses hb) :=
        wSpendFrom_rebase snet Γ₂ _ _ (0 + Γ₁.length) 2 fun i => by
          show (if 0 + Γ₁.length + i < Γ₁.length then uses ht (0 + Γ₁.length + i)
                else uses hb (0 + Γ₁.length + i - Γ₁.length + 2)) = uses hb (2 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.add_comm 2 i]
      show snet c = _
      simp only [sSpend] at iht ihb ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [snet, sMint] at iht ihb ⊢
      omega
  | _, _, _, Typed.unit => by
      simp [snet, sSpend, wSpendFrom, sMint]
  | _, _, _, @Typed.next Γ a t h => sFlowEq h
  | _, _, _, Typed.nil => by
      simp [snet, sSpend, wSpendFrom, sMint]
  | _, _, _, @Typed.red => by
      simp [snet, sSpend, wSpendFrom, uses, sMint]
  | _, _, _, @Typed.obj => by
      simp [snet, sSpend, wSpendFrom, uses, sMint]
  | _, _, _, @Typed.terminate => by
      simp [snet, sSpend, wSpendFrom, uses, sMint]
  | _, _, _, @Typed.gen => by
      simp [snet, sSpend, wSpendFrom, uses, sMint]
  | _, _, _, @Typed.fix Γ a body hΓ h => by
      have ih := sFlowEq h
      have harr : snet (Ty.arrow (Ty.later a) a) = snet a - snet (Ty.later a) := rfl
      rw [harr] at ih
      have hla : snet (Ty.later a) = snet a := rfl
      rw [hla, Int.sub_self] at ih
      show snet a = _
      have huf : wSpendFrom snet 0 Γ (uses (@Typed.fix Γ a body hΓ h))
          = wSpendFrom snet 0 Γ (uses h) := rfl
      rw [sSpend, huf]
      rw [sSpend] at ih
      simp only [sMint] at ih ⊢
      omega
  | _, _, _, @Typed.cons E Γ Δ hd tl hc ht hs => by
      have ihc := sFlowEq hc
      have iht := sFlowEq ht
      subst hs
      have h1 : wSpendFrom snet 0 Γ (uses (@Typed.cons (Γ ++ Δ) Γ Δ hd tl hc ht rfl))
          = wSpendFrom snet 0 Γ (uses hc) :=
        wSpendFrom_congr snet Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses hc i else uses ht (i - Γ.length)) = uses hc i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom snet (0 + Γ.length) Δ (uses (@Typed.cons (Γ ++ Δ) Γ Δ hd tl hc ht rfl))
          = wSpendFrom snet 0 Δ (uses ht) :=
        wSpendFrom_rebase snet Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses hc (0 + Γ.length + i)
                else uses ht (0 + Γ.length + i - Γ.length)) = uses ht (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show snet Ty.stream = _
      simp only [sSpend] at ihc iht ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [snet, sMint] at ihc iht ⊢
      omega
  | _, _, _, @Typed.snoc E Γ Δ t u ht hu hs => by
      have iht := sFlowEq ht
      have ihu := sFlowEq hu
      subst hs
      have h1 : wSpendFrom snet 0 Γ (uses (@Typed.snoc (Γ ++ Δ) Γ Δ t u ht hu rfl))
          = wSpendFrom snet 0 Γ (uses ht) :=
        wSpendFrom_congr snet Γ _ _ 0 fun i _ hilt => by
          show (if i < Γ.length then uses ht i else uses hu (i - Γ.length)) = uses ht i
          rw [if_pos (by omega)]
      have h2 : wSpendFrom snet (0 + Γ.length) Δ (uses (@Typed.snoc (Γ ++ Δ) Γ Δ t u ht hu rfl))
          = wSpendFrom snet 0 Δ (uses hu) :=
        wSpendFrom_rebase snet Δ _ _ (0 + Γ.length) 0 fun i => by
          show (if 0 + Γ.length + i < Γ.length then uses ht (0 + Γ.length + i)
                else uses hu (0 + Γ.length + i - Γ.length)) = uses hu (0 + i)
          rw [if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]
          rw [Nat.zero_add]
      show snet Ty.trace = _
      simp only [sSpend] at iht ihu ⊢
      rw [wSpendFrom_append, h1, h2] at ⊢
      simp only [snet, sMint] at iht ihu ⊢
      omega
  | _, _, _, @Typed.contr Γ k t τ hk h => by
      have ih := sFlowEq h
      have hk0 := nonlinear_snet k hk
      have hsplitI : sSpend (Γ := k :: k :: Γ) h
          = (uses h 0 : Int) * snet k + ((uses h 1 : Int) * snet k
            + wSpendFrom snet 2 Γ (uses h)) := rfl
      rw [hsplitI, hk0] at ih
      simp only [Int.mul_zero, Int.add_zero, Int.zero_add] at ih
      have hreb : wSpendFrom snet (0 + 1) Γ (uses (@Typed.contr Γ k t τ hk h))
          = wSpendFrom snet 2 Γ (uses h) :=
        wSpendFrom_rebase snet Γ _ _ (0 + 1) 2 fun i => by
          have h1 : (1 + i : Nat) ≠ 0 := by omega
          simp only [uses, if_neg h1]
          congr 1
          omega
      show snet τ = _
      rw [sSpend, wSpendFrom]
      rw [hreb, hk0]
      simp only [Int.mul_zero, Int.add_zero, Int.zero_add]
      simp only [sMint]
      exact ih
  | _, _, _, @Typed.weak Γ k t τ hk h => by
      have ih := sFlowEq h
      have hk0 := nonlinear_snet k hk
      show snet τ = _
      rw [sSpend, wSpendFrom]
      have hreb : wSpendFrom snet (0 + 1) Γ (uses (@Typed.weak Γ k t τ hk h))
          = wSpendFrom snet 0 Γ (uses h) :=
        wSpendFrom_rebase snet Γ _ _ (0 + 1) 0 fun i => by
          have h1 : (1 + i : Nat) ≠ 0 := by omega
          simp only [uses, if_neg h1, Nat.add_sub_cancel_left, Nat.zero_add]
      rw [hreb]
      have h0 : (uses (@Typed.weak Γ k t τ hk h) 0 : Int) * snet k = 0 := by
        rw [hk0, Int.mul_zero]
      rw [h0, Int.zero_add]
      simp only [sMint]
      exact ih

/-- Fix-free stream-mints are debts or zero: the only positive mint is
the fixpoint's (the epistemic cycle), excluded. -/
theorem sMint_nonpos : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    fixCount h = 0 → sMint h ≤ 0 := by
  intro Γ t τ h
  induction h with
  | red => intro _; simp only [sMint]; omega
  | obj => intro _; simp only [sMint]; omega
  | unit => intro _; simp only [sMint]; omega
  | nil => intro _; simp only [sMint]; omega
  | gen => intro _; simp only [sMint]; omega
  | terminate => intro _; simp only [sMint]; omega
  | var => intro _; simp only [sMint]; omega
  | lam _ ih =>
      intro hfc
      have hm := ih (by simpa only [fixCount] using hfc)
      simp only [sMint] at *
      omega
  | next _ ih =>
      intro hfc
      have hm := ih (by simpa only [fixCount] using hfc)
      simp only [sMint] at *
      omega
  | contr _ _ ih =>
      intro hfc
      have hm := ih (by simpa only [fixCount] using hfc)
      simp only [sMint] at *
      omega
  | weak _ _ ih =>
      intro hfc
      have hm := ih (by simpa only [fixCount] using hfc)
      simp only [sMint] at *
      omega
  | app _ _ _ ihf iha =>
      intro hfc
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      have e1 := ihf h1
      have e2 := iha h2
      simp only [sMint] at *
      omega
  | pair _ _ _ ihl ihr =>
      intro hfc
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      have e1 := ihl h1
      have e2 := ihr h2
      simp only [sMint] at *
      omega
  | lete _ _ _ iht ihb =>
      intro hfc
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      have e1 := iht h1
      have e2 := ihb h2
      simp only [sMint] at *
      omega
  | cons _ _ _ ihc iht =>
      intro hfc
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      have e1 := ihc h1
      have e2 := iht h2
      simp only [sMint] at *
      omega
  | snoc _ _ _ iht ihu =>
      intro hfc
      obtain ⟨h1, h2⟩ : fixCount _ = 0 ∧ fixCount _ = 0 := by
        simpa only [fixCount, Nat.add_eq_zero_iff] using hfc
      have e1 := iht h1
      have e2 := ihu h2
      simp only [sMint] at *
      omega
  | fix _ _ _ =>
      intro hfc
      simp only [fixCount] at hfc
      omega

/-- STREAM-ORIGIN (the cons-side base of the chase): a fix-free
`▷stream`-conclusion derivation SPENDS a stream-carrying position of its
context — `sFlowEq` books the budget; the only positive mint is the
fixpoint's, banned. -/
theorem stream_origin {Γ : List Ty} {t : Term}
    (h : Typed Γ t (.later Ty.stream)) (hfc : fixCount h = 0) :
    ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ snet b > 0 ∧ uses h i ≥ 1 := by
  have hsm : sMint h ≤ 0 := sMint_nonpos h hfc
  have he := sFlowEq h
  simp only [snet] at he
  refine Classical.byContradiction fun hcon => ?_
  have hle : sSpend h ≤ 0 := by
    simp only [sSpend]
    refine wSpendFrom_nonpos snet 0 Γ (uses h) ?_
    intro (i : Nat) (a : Ty) hpos'
    simp only [Nat.zero_add]
    by_cases ht : snet a > 0
    · have hu : uses h i = 0 := by
        rcases Nat.lt_or_ge (uses h i) 1 with hlt | hge
        · omega
        · exact absurd ⟨i, a, hpos', ht, hge⟩ hcon
      rw [hu]
      simp
    · have hle' : snet a ≤ 0 := by omega
      exact Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hle'
  omega


end Dcare
