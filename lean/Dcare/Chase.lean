import Dcare.Path
import Dcare.Cut

/-!
# The chase: subject reduction along a path

The on-demand-reduction engine (obs 82 (E), obs 88's S2): when the chase
meets a linear redex, REDUCE — the tree shrinks, the cycle cannot re-form.
This file is the congruence half: replacing a subderivation by one of the
same type, equal counters, and size down by `k` rebuilds the whole tree
with the same judgment type, equal counters, and size down by the same
`k`.

TWO frame classes are excluded from `BFree`, each for a measured reason:

* FIX frames: the rebuild would need `AllNonLinear` of the replacement's
  context, which no package carries (the fix layer, S5, revisits this
  when fixes enter — and in the fix-free chase the counters exclude fix
  frames anyway).

* BINDER frames (`lam` premises, `lete` bodies, `contr` premises): the
  frame re-binds the head of its premise's context, but the SPLICE
  reorders the redex's context pieces (`Δa ++ Γf`), so when the binder's
  piece reaches the redex's fn-side with a nonempty argument context, the
  head moves and the constructor cannot re-apply — this calculus has no
  exchange. The reduced TERM remains typable (the split rules admit the
  rotated order), but finding that derivation is a RETYPING, not a
  congruence — outside a package that carries only the derivation. S3's
  design pass decides how the chase routes around binder-crossing
  reductions.
-/

namespace Dcare

/-- The paths an opaque replacement can be lifted along: concatenation
and pass-through frames only. Inverting a `BFree` certificate exposes the
frame structure directly — no premise-casing needed. -/
inductive BFree {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (d : Typed Γ₀ t₀ τ₀) :
    {Γ : List Ty} → {t : Term} → {τ : Ty} → {r : Typed Γ t τ} → Path d r → Prop where
  | here : BFree d Path.here
  | appF {E Γ Δ X b fn arg} {hf : Typed Γ fn (.arrow X b)} {ha : Typed Δ arg X}
      {hs : Γ ++ Δ = E} {p : Path d (.app hf ha hs)} :
      BFree d p → BFree d (Path.step p Prem.appFP)
  | appA {E Γ Δ X b fn arg} {hf : Typed Γ fn (.arrow X b)} {ha : Typed Δ arg X}
      {hs : Γ ++ Δ = E} {p : Path d (.app hf ha hs)} :
      BFree d p → BFree d (Path.step p Prem.appAP)
  | pairL {E Γ Δ a b l r₁} {hl : Typed Γ l a} {hr : Typed Δ r₁ b}
      {hs : Γ ++ Δ = E} {p : Path d (.pair hl hr hs)} :
      BFree d p → BFree d (Path.step p Prem.pairLP)
  | pairR {E Γ Δ a b l r₁} {hl : Typed Γ l a} {hr : Typed Δ r₁ b}
      {hs : Γ ++ Δ = E} {p : Path d (.pair hl hr hs)} :
      BFree d p → BFree d (Path.step p Prem.pairRP)
  | leteT {E Γ₁ Γ₂ a b c₁ t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c₁} {hs : Γ₁ ++ Γ₂ = E}
      {p : Path d (.lete ht hb hs)} :
      BFree d p → BFree d (Path.step p Prem.leteTP)
  | next {E a t} {h : Typed E t a} {p : Path d (.next h)} :
      BFree d p → BFree d (Path.step p Prem.nextP)
  | consH {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} {p : Path d (.cons hc ht hs)} :
      BFree d p → BFree d (Path.step p Prem.consHP)
  | consT {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} {p : Path d (.cons hc ht hs)} :
      BFree d p → BFree d (Path.step p Prem.consTP)
  | snocT {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} {p : Path d (.snoc ht hu hs)} :
      BFree d p → BFree d (Path.step p Prem.snocTP)
  | snocU {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} {p : Path d (.snoc ht hu hs)} :
      BFree d p → BFree d (Path.step p Prem.snocUP)
  | weak {E : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false}
      {h : Typed E t τ} {p : Path d (.weak hk h)} :
      BFree d p → BFree d (Path.step p Prem.weakP)

/-- The congruence: a replacement package at a node on a `BFree` path
lifts to a replacement package at the root. The rebuilt tree's contexts
are free (the judgment type is preserved; contexts are the splice's
business, not the congruence's). -/
theorem rebuild_along : ∀ (k : Nat) {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty}
    (d : Typed Γ₀ t₀ τ₀),
    ∀ {Γr : List Ty} {tr : Term} {τr : Ty} (r : Typed Γr tr τr) (hp : Path d r),
    BFree d hp →
    ∀ {Γr' : List Ty} {tr' : Term} (r' : Typed Γr' tr' τr),
    tsize tr' + k = tsize tr →
    fixCount r' = fixCount r → mintCount r' = mintCount r →
    ∃ (Γ₀' : List Ty) (t₀' : Term) (d' : Typed Γ₀' t₀' τ₀),
      tsize t₀' + k = tsize t₀ ∧ fixCount d' = fixCount d ∧ mintCount d' = mintCount d := by
  intro k Γ₀ t₀ τ₀ d
  intro Γr tr τr r hp hbf
  induction hbf with
  | here =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ⟨Γr', tr', r', hsz, hfc', hmc'⟩
  | @appF E Γ Δ X b fn arg hf ha hs p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.app r' ha rfl : Typed (Γr' ++ Δ) (Term.app tr' arg) b)
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @appA E Γ Δ X b fn arg hf ha hs p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.app hf r' rfl : Typed (Γ ++ Γr') (Term.app fn tr') b)
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @pairL E Γ Δ a b l r₁ hl hr hs p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.pair r' hr rfl :
        Typed (Γr' ++ Δ) (Term.pair tr' r₁) (.tensor a b))
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @pairR E Γ Δ a b l r₁ hl hr hs p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.pair hl r' rfl :
        Typed (Γ ++ Γr') (Term.pair l tr') (.tensor a b))
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @leteT E Γ₁ Γ₂ a b c₁ t body ht hb hs p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.lete r' hb rfl :
        Typed (Γr' ++ Γ₂) (Term.lete tr' body) c₁)
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @next E a t h p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.next r' : Typed Γr' (Term.next tr') (.later a))
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @consH E Γ Δ hd tl hc ht hs p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.cons r' ht rfl :
        Typed (Γr' ++ Δ) (Term.cons tr' tl) .stream)
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @consT E Γ Δ hd tl hc ht hs p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.cons hc r' rfl :
        Typed (Γ ++ Γr') (Term.cons hd tr') .stream)
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @snocT E Γ Δ t u ht hu hs p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.snoc r' hu rfl :
        Typed (Γr' ++ Δ) (Term.snoc tr' u) .trace)
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @snocU E Γ Δ t u ht hu hs p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.snoc ht r' rfl :
        Typed (Γ ++ Γr') (Term.snoc t tr') .trace)
        (by simp only [tsize]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)
  | @weak E k' t τ hk h p hbf' ih =>
      intro Γr' tr' r' hsz hfc' hmc'
      exact ih (Typed.weak hk r' :
        Typed (k' :: Γr') (Term.liftAt 0 tr') τ)
        (by rw [liftAt_tsize 0 tr', liftAt_tsize 0 t]; omega)
        (by simp only [fixCount]; omega) (by simp only [mintCount]; omega)

/-- REDUCTION AT A LINEAR REDEX on a `BFree` chain: the fire consumes
the λ and the leaf, the splice rebuilds the body, and the congruence
lifts the package to the root — the tree survives with the same judgment
type, equal counters, and its size down by exactly the three consumed
nodes (fire + binder + leaf). This is the move that breaks every cycle
the walkers could not escape: after the reduction the λs are GONE. -/
theorem reduce_at {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (d : Typed Γ₀ t₀ τ₀)
    {E Γf Δa : List Ty} {a b : Ty} {body arg : Term}
    (hbody : Typed (a :: Γf) body b) (harg : Typed Δa arg a) (hs : Γf ++ Δa = E)
    (hlin : a.isLinear = true) (hu : uses hbody 0 = 1)
    (hp : Path d (@Typed.app E Γf Δa a b (Term.lam a body) arg (Typed.lam hbody) harg hs))
    (hbf : BFree d hp) :
    ∃ (Γ₀' : List Ty) (t₀' : Term) (d' : Typed Γ₀' t₀' τ₀),
      tsize t₀' + 3 = tsize t₀ ∧
      fixCount d' = fixCount d ∧ mintCount d' = mintCount d := by
  obtain ⟨body', hbody', hsz, hfc₀, hmc₀⟩ := linear_beta_splice hbody harg hlin hu
  refine rebuild_along 3 d _ hp hbf hbody' hsz ?_ ?_
  · simp only [fixCount] at hfc₀ ⊢; omega
  · simp only [mintCount] at hmc₀ ⊢; omega

/-- The token spends exactly itself: at the singleton `[content]`
context the weighted spend is the one use of `net content = 1`. -/
theorem spendNet_singleton {t : Term} {τ : Ty} (h : Typed [Ty.content] t τ) :
    spendNet h = 1 := by
  have hu : uses h 0 = 1 := single_linear_use h 0 Ty.content rfl rfl
  rw [spendNet]
  simp only [spendNetFrom, hu, net]
  omega

/-!
## The assembly, conditional on the chase

Everything around the chase is proven: the front door (mint-freeness),
the accounting (`flowEq` turns the token into a sink-count), the
sink-extraction (the killed premise with clean counters), and the two
arithmetic origins (a tnet-positive spend under the trace premise; an
snet-positive spend under the ▷stream tail). What remains is THE CHASE
itself — killing a positive spent position at a clean node.

THE CHASE STATEMENTS ARE ROOT-CARRYING, and must be: the root-free form
(this file's first pinning, interval 7) is REFUTED by
`Typed.var : [trace] ⊢ var 0 : trace` — clean, position 0 tnet-positive,
spent once. A positive position can only be impossible RELATIVE to a
root that supplies nothing positive; the `[content]` context is exactly
that profile (`root_content_nonpos` below), and the `Path` certificate
is what lets `pos_introduced` turn a positive position into an
introducer below the root. The unit-conclusion pin is the ride's
root-kill (a tensor-typed value cannot be the root) and the
lam-introducer's root-kill (a λ concludes an arrow).
-/

/-- The root's supply profile: `[content]` supplies no tnet-positive
position — the one fact that makes an introducer mandatory for every
positive position below the root. -/
theorem root_content_nonpos : ∀ (j : Nat) (b : Ty), [Ty.content][j]? = some b → tnet b ≤ 0 := by
  intro j b hpos
  cases j with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with hb
      subst hb
      simp [tnet]
  | succ m =>
      rw [List.get?_succ_cons', List.get?_nil'] at hpos
      contradiction

/-- `no_vanishing_fixfree` reduced to the chase: the trace-side and
stream-side position-kills are the only missing pieces. The chase
hypotheses are the honest S3 targets — root-carrying, path-certified,
against the `[content]` supply profile (see the module doc above for
why the root-free form was refuted and re-pinned). -/
theorem no_vanishing_fixfree_of_chase
    (hchaseT : ∀ {t₀ : Term} (root : Typed [Ty.content] t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ}, Path root d →
      ∀ (i : Nat) (b : Ty), Γ[i]? = some b → tnet b > 0 → uses d i ≥ 1 → False)
    (hchaseS : ∀ {t₀ : Term} (root : Typed [Ty.content] t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γ : List Ty} {t : Term} {d : Typed Γ t (.later Ty.stream)}, Path root d →
      ∀ (i : Nat) (b : Ty), Γ[i]? = some b → snet b > 0 → uses d i ≥ 1 → False) :
    ∀ (t : Term) (h : Typed [Ty.content] t Ty.unit), fixCount h = 0 → False := by
  intro t h hf
  have hm : mintCount h = 0 := mintCount_zero_at_unit_root h hf
  have hfm : fixMint h = 0 := fixMint_eq_zero h hf
  have hsp : spendNet h = 1 := spendNet_singleton h
  have he := flowEq h
  simp only [net] at he
  rw [hsp, hfm, Int.add_zero] at he
  have hsinks : 0 < sinks h := by
    have h1 : (1 : Int) ≤ ↑(sinks h) := by omega
    exact_mod_cast h1
  obtain hsink | hsink := sinks_extract' h h Path.here hsinks hf hm
  · obtain ⟨Γ', t', ht, hpath, hfc', hmc'⟩ := hsink
    obtain ⟨i, b, hpos, hpos', hu⟩ :=
      origin_lemma ht hfc' hmc' (by simp [tnet])
    exact hchaseT h hf hm hpath i b hpos hpos' hu
  · obtain ⟨Γ', t', htl, hpath, hfc', hmc'⟩ := hsink
    obtain ⟨i, b, hpos, hpos', hu⟩ := stream_origin htl hfc'
    exact hchaseS h hf hm hpath i b hpos hpos' hu

/-- Path concatenation. -/
theorem Path_append {Γc : List Ty} {tc : Term} {τc : Ty} (c : Typed Γc tc τc)
    {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀) :
    ∀ {Γ : List Ty} {t : Term} {τ : Ty} {v : Typed Γ t τ}, Path c v → Path root c → Path root v := by
  intro Γ t τ v hp
  induction hp with
  | here => exact fun hpc => hpc
  | step p s ih => exact fun hpc => Path.step (ih hpc) s

/-- Every subderivation is reachable by a path. -/
theorem sub_path : ∀ {Γ₁ : List Ty} {t₁ : Term} {τ₁ : Ty} {h : Typed Γ₁ t₁ τ₁}
    {Γ₂ : List Ty} {t₂ : Term} {τ₂ : Ty} {d : Typed Γ₂ t₂ τ₂}, Sub h d → Path h d := by
  intro Γ₁ t₁ τ₁ h Γ₂ t₂ τ₂ d s
  induction s with
  | lam s ih => exact Path_append _ _ ih (Path.step Path.here Prem.lamP)
  | appL s ih => exact Path_append _ _ ih (Path.step Path.here Prem.appFP)
  | appR s ih => exact Path_append _ _ ih (Path.step Path.here Prem.appAP)
  | pairL s ih => exact Path_append _ _ ih (Path.step Path.here Prem.pairLP)
  | pairR s ih => exact Path_append _ _ ih (Path.step Path.here Prem.pairRP)
  | leteT s ih => exact Path_append _ _ ih (Path.step Path.here Prem.leteTP)
  | leteB s ih => exact Path_append _ _ ih (Path.step Path.here Prem.leteBP)
  | next s ih => exact Path_append _ _ ih (Path.step Path.here Prem.nextP)
  | fix s ih => exact Path_append _ _ ih (Path.step Path.here Prem.fixP)
  | consH s ih => exact Path_append _ _ ih (Path.step Path.here Prem.consHP)
  | consT s ih => exact Path_append _ _ ih (Path.step Path.here Prem.consTP)
  | snocT s ih => exact Path_append _ _ ih (Path.step Path.here Prem.snocTP)
  | snocU s ih => exact Path_append _ _ ih (Path.step Path.here Prem.snocUP)
  | contr s ih => exact Path_append _ _ ih (Path.step Path.here Prem.contrP)
  | weak s ih => exact Path_append _ _ ih (Path.step Path.here Prem.weakP)
  | lamD => exact Path.step Path.here Prem.lamP
  | appLD => exact Path.step Path.here Prem.appFP
  | appRD => exact Path.step Path.here Prem.appAP
  | pairLD => exact Path.step Path.here Prem.pairLP
  | pairRD => exact Path.step Path.here Prem.pairRP
  | leteTD => exact Path.step Path.here Prem.leteTP
  | leteBD => exact Path.step Path.here Prem.leteBP
  | nextD => exact Path.step Path.here Prem.nextP
  | fixD => exact Path.step Path.here Prem.fixP
  | consHD => exact Path.step Path.here Prem.consHP
  | consTD => exact Path.step Path.here Prem.consTP
  | snocTD => exact Path.step Path.here Prem.snocTP
  | snocUD => exact Path.step Path.here Prem.snocUP
  | contrD => exact Path.step Path.here Prem.contrP
  | weakD => exact Path.step Path.here Prem.weakP

theorem get?_zero_of_singleton {Γ : List Ty} {c : Ty} (h : Γ = [c]) : Γ[0]? = some c := by
  rw [h]; exact List.get?_zero_cons'

/-- The read's position at its parent (the position-preimage table, obs
74's M1): a var-shaped premise reading `a` at `[a]` sits at a concrete
position of the parent's context — the parent spends it — for every
SPLIT frame; the `lam` parent is the identity-λ (the read IS the body);
the `contr`/`lete`-body parents die by length, the content/▷stream
premise slots die by tnet-positivity. -/
theorem prem_position : ∀ {E : List Ty} {tc : Term} {τc : Ty} {p : Typed E tc τc}
    {Γv : List Ty} {tv : Term} {τv : Ty} {v : Typed Γv tv τv}, Prem p v →
    tv = Term.var 0 → Γv = [τv] → tnet τv > 0 →
    (∃ (i : Nat), E[i]? = some τv ∧ uses p i ≥ 1)
    ∨ (E = [] ∧ ∃ (a' : Ty), tc = Term.lam a' (Term.var 0)) := by
  intro E tc τc p Γv tv τv v s htv hΓ hta
  have hlin : τv.isLinear = true := by
    rcases Bool.eq_false_or_eq_true τv.isLinear with h | h
    · exact h
    · rw [nonlinear_tnet τv h] at hta; omega
  match s, htv, hΓ with
  | @Prem.lamP E' a' b body h, htv, hΓ' =>
      injection hΓ' with haE hE
      exact Or.inr ⟨hE, ⟨a', by rw [htv, haE]⟩⟩
  | @Prem.appFP E' Γ' Δ X b fn arg hf ha hs, _, hΓ' =>
      refine Or.inl ⟨0, ?_, ?_⟩
      · rw [← hs, List.get?_append_lt (by rw [hΓ']; simp)]
        rw [hΓ']; exact List.get?_zero_cons'
      · simp only [uses]
        rw [if_pos (by rw [hΓ']; simp : (0 : Nat) < Γ'.length)]
        exact Nat.le_of_eq (Eq.symm (single_linear_use hf 0 _ (get?_zero_of_singleton hΓ') hlin))
  | @Prem.appAP E' Γ' Δ X b fn arg hf ha hs, _, hΓ' =>
      refine Or.inl ⟨Γ'.length, ?_, ?_⟩
      · rw [← hs, List.get?_append_ge (Nat.le_refl _)]
        rw [hΓ']; simp
      · simp only [uses]
        rw [if_neg (Nat.not_lt.mpr (Nat.le_refl _)), Nat.sub_self]
        exact Nat.le_of_eq (Eq.symm (single_linear_use ha 0 _ (get?_zero_of_singleton hΓ') hlin))
  | @Prem.pairLP E' Γ' Δ x y l r hl hr hs, _, hΓ' =>
      refine Or.inl ⟨0, ?_, ?_⟩
      · rw [← hs, List.get?_append_lt (by rw [hΓ']; simp)]
        rw [hΓ']; exact List.get?_zero_cons'
      · simp only [uses]
        rw [if_pos (by rw [hΓ']; simp : (0 : Nat) < Γ'.length)]
        exact Nat.le_of_eq (Eq.symm (single_linear_use hl 0 _ (get?_zero_of_singleton hΓ') hlin))
  | @Prem.pairRP E' Γ' Δ x y l r hl hr hs, _, hΓ' =>
      refine Or.inl ⟨Γ'.length, ?_, ?_⟩
      · rw [← hs, List.get?_append_ge (Nat.le_refl _)]
        rw [hΓ']; simp
      · simp only [uses]
        rw [if_neg (Nat.not_lt.mpr (Nat.le_refl _)), Nat.sub_self]
        exact Nat.le_of_eq (Eq.symm (single_linear_use hr 0 _ (get?_zero_of_singleton hΓ') hlin))
  | @Prem.leteTP E' Γ₁ Γ₂ x y c t body ht hb hs, _, hΓ₁ =>
      refine Or.inl ⟨0, ?_, ?_⟩
      · rw [← hs, List.get?_append_lt (by rw [hΓ₁]; simp)]
        rw [hΓ₁]; exact List.get?_zero_cons'
      · simp only [uses]
        rw [if_pos (by rw [hΓ₁]; simp : (0 : Nat) < Γ₁.length)]
        exact Nat.le_of_eq (Eq.symm (single_linear_use ht 0 _ (get?_zero_of_singleton hΓ₁) hlin))
  | @Prem.leteBP E' Γ₁ Γ₂ x y c t body ht hb hs, _, hΓ₂ =>
      have hlen := congrArg List.length hΓ₂
      simp only [List.length_cons, List.length_nil] at hlen
      omega
  | @Prem.nextP E' a' t h, _, hΓ' =>
      refine Or.inl ⟨0, ?_, ?_⟩
      · rw [hΓ']; exact List.get?_zero_cons'
      · simp only [uses]
        exact Nat.le_of_eq (Eq.symm (single_linear_use h 0 _ (get?_zero_of_singleton hΓ') hlin))
  | @Prem.fixP E' a' body hnl h, _, hΓeq =>
      refine Or.inl ⟨0, ?_, ?_⟩
      · rw [hΓeq]; exact List.get?_zero_cons'
      · simp only [uses]
        exact Nat.le_of_eq (Eq.symm (single_linear_use h 0 _ (get?_zero_of_singleton hΓeq) hlin))
  | @Prem.consHP E' Γ' Δ hd tl hc ht hs, _, _ =>
      have h0 : tnet Ty.content = 0 := rfl
      rw [h0] at hta; omega
  | @Prem.consTP E' Γ' Δ hd tl hc ht hs, _, _ =>
      have h0 : tnet (Ty.later Ty.stream) = 0 := rfl
      rw [h0] at hta; omega
  | @Prem.snocTP E' Γ' Δ t u ht hu hs, _, hΓ' =>
      refine Or.inl ⟨0, ?_, ?_⟩
      · rw [← hs, List.get?_append_lt (by rw [hΓ']; simp)]
        rw [hΓ']; exact List.get?_zero_cons'
      · simp only [uses]
        rw [if_pos (by rw [hΓ']; simp : (0 : Nat) < Γ'.length)]
        exact Nat.le_of_eq (Eq.symm (single_linear_use ht 0 _ (get?_zero_of_singleton hΓ') hlin))
  | @Prem.snocUP E' Γ' Δ t u ht hu hs, _, _ =>
      have h0 : tnet Ty.content = 0 := rfl
      rw [h0] at hta; omega
  | @Prem.contrP E' k t τ hk h, _, hΓ₂ =>
      have hlen := congrArg List.length hΓ₂
      simp only [List.length_cons, List.length_nil] at hlen
      omega
  | @Prem.weakP E' k t τ hk h, _, hΓ' =>
      refine Or.inl ⟨1, ?_, ?_⟩
      · exact List.get?_succ_cons'.trans (by rw [hΓ']; exact List.get?_zero_cons')
      · simp only [uses]
        rw [if_neg (by omega)]
        exact Nat.le_of_eq (Eq.symm (single_linear_use h 0 _ (get?_zero_of_singleton hΓ') hlin))

/-- Lifting at zero never yields `var 0` — every variable moves up. -/
theorem liftAt0_ne_var0 : ∀ (t : Term), Term.liftAt 0 t ≠ Term.var 0 := by
  intro t
  cases t with
  | var i =>
      simp only [Term.liftAt]
      by_cases h0 : (0 : Nat) ≤ i
      · rw [if_pos h0]; exact fun he => by injection he; omega
      · rw [if_neg h0]; omega
  | lam _ _ | app _ _ | pair _ _ | lete _ _ | unit | next _ | fix _ | cons _ _
  | nil | snoc _ _ | gen | red | obj | terminate =>
      simp only [Term.liftAt]; intro he; cases he

/-- CANONICAL FORMS for the var-read: a derivation concluding `var 0`
lives at the singleton `[a]` for its type `a` — the read's context is
exactly the piece it reads. This is what makes `prem_position` applicable
to `read_locate`'s output (the singleton hypothesis is always
satisfiable). Stated with the term-equation as a hypothesis so the
induction runs past the `weak`/`contr` frames. -/
theorem var_canonical : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (v : Typed Γ t τ),
    t = Term.var 0 → ∃ (a : Ty), Γ = [a] ∧ τ = a := by
  intro Γ t τ v
  induction v with
  | var => intro _; exact ⟨_, rfl, rfl⟩
  | contr hk h ih =>
      intro hte
      obtain ⟨a, hc, _⟩ := ih (by rw [hte] <;> rfl)
      have hlen := congrArg List.length hc
      simp only [List.length_cons, List.length_nil] at hlen
      omega
  | weak hk h ih =>
      intro hte
      exact absurd hte (liftAt0_ne_var0 _)
  | lam _ _ | app _ _ _ | pair _ _ _ | lete _ _ _ | unit | next _ | fix _ _
  | cons _ _ _ | nil | snoc _ _ _ | gen | red | obj | terminate =>
      intro hte; cases hte

/-- ONE ROUND OF THE CHASE, decomposed: every state (a positive spent
position at a clean node) either DESCENDS — a strictly smaller state of
the same kind, with its path certificate — or sits at a READ-CONFIG: the
read is a direct premise of a node at-or-below the current one (the
fire/ride/var-fn/identity-λ shapes the fuel-chase analyzes), or the node
IS the read (TOP — the introducer analysis). The descent disjunct is
what the fuel pays in node-size; the configs are the corner/ride/var-fn
machinery's entries. -/
theorem chase_step {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d)
    (hfc : fixCount root = 0) (hmc : mintCount root = 0)
    (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (htb : tnet b > 0) (hu : uses d i ≥ 1) :
    (∃ (Γ' : List Ty) (t' : Term) (τ' : Ty) (d' : Typed Γ' t' τ') (i' : Nat) (b' : Ty)
        (hp' : Path root d'),
        Γ'[i']? = some b' ∧ tnet b' > 0 ∧ uses d' i' ≥ 1 ∧
        fixCount d' = 0 ∧ mintCount d' = 0 ∧ size d' < size d)
    ∨ (∃ (E : List Ty) (tc : Term) (τc : Ty) (d' : Typed E tc τc) (hp' : Path root d')
        (hle : size d' ≤ size d) (Γv : List Ty) (tv : Term) (τv : Ty) (v : Typed Γv tv τv),
        tv = Term.var 0 ∧ Γv = [τv] ∧ tnet τv > 0 ∧ Prem d' v ∧
        ((∃ (i' : Nat), E[i']? = some τv ∧ uses d' i' ≥ 1)
         ∨ (E = [] ∧ ∃ (a' : Ty), tc = Term.lam a' (Term.var 0))))
    ∨ (Γ = [b] ∧ t = Term.var 0 ∧ τ = b ∧ i = 0) := by
  have hclean := Path_clean root hp hfc hmc
  rcases read_locate (size d) d (Nat.le_refl _) i b hpos hu with
    deep | direct | top
  · -- DEEP: the read's parent p is a proper subderivation — locate the
    -- state at p, or the parent is the identity-λ.
    obtain ⟨E, tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ := deep
    have hta : tnet τv > 0 := by rw [hτv]; exact htb
    obtain ⟨a, hcΓ, hcτ⟩ := var_canonical v htv
    have hcΓv : Γv = [τv] := hcτ ▸ hcΓ
    have hp' : Path root p := Path_append d root (sub_path hsub) hp
    have hpc := Path_clean root hp' hfc hmc
    rcases prem_position (p := p) (v := v) hprem htv hcΓv hta with
      ⟨iₚ, hposₚ, huₚ⟩ | ⟨hE, hlami⟩
    · refine Or.inl ⟨E, tp, τp, p, iₚ, τv, hp', hposₚ, hta, huₚ, hpc.1, hpc.2, ?_⟩
      exact Sub_size hsub
    · -- the identity-λ config: the read IS the λ's body; the node spends
      -- no position (its context is empty) — its own domain introduces.
      refine Or.inr (Or.inl ⟨E, tp, τp, p, hp', Nat.le_of_lt (Sub_size hsub),
        Γv, tv, τv, v, htv, hcΓv, hta, hprem, Or.inr ⟨hE, hlami⟩⟩)
  · -- DIRECT: the read is a premise of the state's own node — the config.
    obtain ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ := direct
    have hta : tnet τv > 0 := by rw [hτv]; exact htb
    obtain ⟨a, hcΓ, hcτ⟩ := var_canonical v htv
    have hcΓv : Γv = [τv] := hcτ ▸ hcΓ
    exact Or.inr (Or.inl ⟨Γ, t, τ, d, hp, Nat.le_refl _, Γv, tv, τv, v, htv, hcΓv, hta, hprem,
      Or.inl ⟨i, by rw [hτv]; exact hpos, hu⟩⟩)
  · -- TOP: the node IS the read.
    exact Or.inr (Or.inr ‹_›)

/-!
## The config-side machinery

`chase_step`'s descent loop is closed; what remains analyzes the
READ-CONFIGS and TOP. The lemmas below are the DESCENT moves — stable
under every payload design (they produce strictly smaller states of the
same kind, no payload change). The ascent moves (the corner's
introducer-consumer analysis; the rides) pay piece-fuel and are the
payload-chase's subject.
-/

/-- Positive positions need introducers: under a `[content]`-rooted
unit tree, every tnet-positive position at a path-reachable node was
introduced by a binder (`λ`-domain or `lete`-component) containing the
node. This is the entry move of every corner/TOP analysis. -/
theorem introducer_of_positive {t₀ : Term} {root : Typed [Ty.content] t₀ Ty.unit}
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d)
    (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (htb : tnet b > 0) :
    ∃ (E' : List Ty) (tp : Term) (τp : Ty) (β : Typed E' tp τp),
      Path root β ∧ Introduces β b ∧ Sub β d := by
  rcases pos_introduced root hp i b hpos with ⟨j, hj⟩ | hintro
  · exact absurd htb (by have hle := root_content_nonpos j b hj; omega)
  · exact hintro

/-- READ-CONFIG, the read is a fire's FN with a tnet-POSITIVE argument
type: the argument is a positive-conclusion clean node on the path —
`origin_lemma` turns it into a strictly smaller chase state. -/
theorem config_fn_positive_arg {t₀ : Term} {root : Typed [Ty.content] t₀ Ty.unit}
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {E Γ Δ : List Ty} {X σ : Ty} {fn arg : Term}
    {hf : Typed Γ fn (.arrow X σ)} {ha : Typed Δ arg X} {hs : Γ ++ Δ = E}
    (hp : Path root (Typed.app hf ha hs)) (hX : tnet X > 0) :
    ∃ (j : Nat) (b : Ty), Δ[j]? = some b ∧ tnet b > 0 ∧ uses ha j ≥ 1 ∧
      fixCount ha = 0 ∧ mintCount ha = 0 ∧ Path root ha ∧
      size ha < size (Typed.app hf ha hs) := by
  have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
  obtain ⟨hfca, hmca⟩ := Prem_clean (Prem.appAP (hf := hf) (ha := ha) (hs := hs)) hfc hmc
  obtain ⟨j, b, hpos, htb, hu⟩ := origin_lemma ha hfca hmca hX
  exact ⟨j, b, hpos, htb, hu, hfca, hmca, Path.step hp Prem.appAP, Prem_size Prem.appAP⟩

/-- READ-CONFIG, the read is a fire's ARG whose fn is λ-headed (the
killer): the killer's body spends its own binder-position exactly once
(M2 — `single_linear_use` at the linear binder), a strictly smaller
state on the path. NOTE the positivity transfer: the killed position's
type IS the read's type, so the state's tnet-positivity survives. This
is the move that does NOT transfer at the CORNER's appAP consumer
(killing the introducer's own arrow type loses the sign) — see the
module doc. -/
theorem config_arg_lam_killer {t₀ : Term} {root : Typed [Ty.content] t₀ Ty.unit}
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {E Γ : List Ty} {τv σ : Ty} {body : Term}
    {hb : Typed (τv :: Γ) body σ} {ha : Typed [τv] (Term.var 0) τv}
    {hs : Γ ++ [τv] = E}
    (hp : Path root (Typed.app (Typed.lam hb) ha hs)) (htv : tnet τv > 0) :
    Path root hb ∧ fixCount hb = 0 ∧ mintCount hb = 0 ∧
      (τv :: Γ)[0]? = some τv ∧ tnet τv > 0 ∧ uses hb 0 ≥ 1 ∧
      size hb < size (Typed.app (Typed.lam hb) ha hs) := by
  have hlin : τv.isLinear = true := by
    rcases Bool.eq_false_or_eq_true τv.isLinear with h | h
    · exact h
    · rw [nonlinear_tnet τv h] at htv; omega
  have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
  obtain ⟨hfcf, hmcf⟩ := Prem_clean (Prem.appFP (ha := ha)) hfc hmc
  obtain ⟨hfcb, hmcb⟩ := Prem_clean (Prem.lamP (h := hb)) hfcf hmcf
  refine ⟨Path.step (Path.step hp Prem.appFP) Prem.lamP, hfcb, hmcb,
    List.get?_zero_cons', htv, ?_, ?_⟩
  · exact Nat.le_of_eq (Eq.symm (single_linear_use hb 0 τv List.get?_zero_cons' hlin))
  · have h1 : size hb < size (Typed.lam hb) := Prem_size Prem.lamP
    have h2 : size (Typed.lam hb) < size (Typed.app (Typed.lam hb) ha hs) := Prem_size Prem.appFP
    omega

/-- THE CHAIN MOVE at the positive-domain class: the read (a var-read of
`T = arrow b σ` with `tnet b > 0`) consumed as a λ-headed fire's ARGUMENT
— the killer's λ has domain `T` exactly, so the killer's body spends
position 0 of the SAME type `T` (TYPE-STABLE: the killer-of-killer
regression does not grow types). The body's position-0 spend is exactly
one (M2 — the binder is linear because `b` is trace-carrying, hence
linear, hence so is `arrow b σ`). This is `config_arg_lam_killer` with
the class hypothesis in place of `tnet T > 0` — the sign of `tnet T`
itself is UNKNOWN at the corner (the killed type there is the
introducer's own arrow type), which is exactly why the chain carries the
DOMAIN-sign rather than the whole-type sign. -/
theorem killer_step {t₀ : Term} {root : Typed [Ty.content] t₀ Ty.unit}
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {E Γ : List Ty} {T b σ : Ty} {body : Term}
    {hb : Typed (T :: Γ) body σ} {ha : Typed [T] (Term.var 0) T}
    {hs : Γ ++ [T] = E}
    (hp : Path root (Typed.app (Typed.lam hb) ha hs))
    (hT : T = Ty.arrow b σ) (htb : tnet b > 0) :
    Path root hb ∧ fixCount hb = 0 ∧ mintCount hb = 0 ∧
      (T :: Γ)[0]? = some T ∧ uses hb 0 ≥ 1 ∧
      size hb < size (Typed.app (Typed.lam hb) ha hs) := by
  have hblin : b.isLinear = true := by
    rcases Bool.eq_false_or_eq_true b.isLinear with h | h
    · exact h
    · rw [nonlinear_tnet b h] at htb; omega
  have hTlin : T.isLinear = true := by
    rw [hT]; simp only [Ty.isLinear, hblin, Bool.true_or]
  have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
  obtain ⟨hfcf, hmcf⟩ := Prem_clean (Prem.appFP (ha := ha)) hfc hmc
  obtain ⟨hfcb, hmcb⟩ := Prem_clean (Prem.lamP (h := hb)) hfcf hmcf
  refine ⟨Path.step (Path.step hp Prem.appFP) Prem.lamP, hfcb, hmcb,
    List.get?_zero_cons', ?_, ?_⟩
  · exact Nat.le_of_eq (Eq.symm (single_linear_use hb 0 T List.get?_zero_cons' hTlin))
  · have h1 : size hb < size (Typed.lam hb) := Prem_size Prem.lamP
    have h2 : size (Typed.lam hb) < size (Typed.app (Typed.lam hb) ha hs) := Prem_size Prem.appFP
    omega

/-! ## The freshness engine

The position-lifting half of the chase's freshness facts (obs 130's
statement, the 30-case `Sub` map): a used position of a subderivation's
context either is supplied by the ancestor's own context or was
INTRODUCED by a λ-domain / lete-component at-or-above the subderivation.
The introducer is where the position's value was bound — the target of
every corner/TOP analysis. -/

/-- A used position of `d`'s context lifts to `h`'s context, or was
introduced by a binder `β` with `Sub β d`. Induction on the `Sub`
certificate: split frames lift the position by prefix/suffix arithmetic
(the `prem_position` idiom), binder frames introduce at positions 0/1,
`contr`/`weak` map positions, and wrapping arms thread the IH. -/
theorem uses_sub_ge_or_binder : ∀ {Γ₁ : List Ty} {t₁ : Term} {τ₁ : Ty} {h : Typed Γ₁ t₁ τ₁}
    {Γ₂ : List Ty} {t₂ : Term} {τ₂ : Ty} {d : Typed Γ₂ t₂ τ₂}, Sub h d →
    ∀ (i : Nat) (A : Ty), Γ₂[i]? = some A → uses d i ≥ 1 →
    (∃ (j : Nat), Γ₁[j]? = some A ∧ uses h j ≥ 1)
    ∨ (∃ (Eβ : List Ty) (tβ : Term) (τβ : Ty) (β : Typed Eβ tβ τβ),
        Introduces β A ∧ Sub β d) := by
  intro Γ₁ t₁ τ₁ h Γ₂ t₂ τ₂ d hs
  induction hs with
  | @lam Γ' a' b' body' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · cases j with
        | zero =>
            rw [List.get?_zero_cons'] at hj
            injection hj with hA
            subst hA
            exact Or.inr ⟨_, _, _, Typed.lam h', Introduces.lamI h', Sub.lam s⟩
        | succ m =>
            rw [List.get?_succ_cons'] at hj
            exact Or.inl ⟨m, hj, by simpa only [uses] using huj⟩
      · exact Or.inr hβ
  | @appL E' Γ' Δ' a' b' fn' arg' hf' ha' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · have hlt : j < Γ'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using huj
      · exact Or.inr hβ
  | @appR E' Γ' Δ' a' b' fn' arg' hf' ha' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · refine Or.inl ⟨Γ'.length + j, ?_, ?_⟩
        · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length j), Nat.add_sub_cancel_left]
          exact hj
        · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length j)),
            Nat.add_sub_cancel_left] using huj
      · exact Or.inr hβ
  | @pairL E' Γ' Δ' a' b' l' r' hl' hr' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · have hlt : j < Γ'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using huj
      · exact Or.inr hβ
  | @pairR E' Γ' Δ' a' b' l' r' hl' hr' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · refine Or.inl ⟨Γ'.length + j, ?_, ?_⟩
        · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length j), Nat.add_sub_cancel_left]
          exact hj
        · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length j)),
            Nat.add_sub_cancel_left] using huj
      · exact Or.inr hβ
  | @leteT E' Γ₁' Γ₂' a' b' c' t' body' ht' hb' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · have hlt : j < Γ₁'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using huj
      · exact Or.inr hβ
  | @leteB E' Γ₁' Γ₂' a' b' c' t' body' ht' hb' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · cases j with
        | zero =>
            rw [List.get?_zero_cons'] at hj
            injection hj with hA
            subst hA
            exact Or.inr ⟨_, _, _, Typed.lete ht' hb' hs', Introduces.leteIY, Sub.leteB s⟩
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hj
                injection hj with hA
                subst hA
                exact Or.inr ⟨_, _, _, Typed.lete ht' hb' hs', Introduces.leteIX, Sub.leteB s⟩
            | succ m' =>
                rw [List.get?_add_two] at hj
                refine Or.inl ⟨Γ₁'.length + m', ?_, ?_⟩
                · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ₁'.length m'),
                    Nat.add_sub_cancel_left]
                  exact hj
                · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ₁'.length m')),
                    Nat.add_sub_cancel_left] using huj
      · exact Or.inr hβ
  | @next Γ' a' t' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · exact Or.inl ⟨j, hj, by simpa only [uses] using huj⟩
      · exact Or.inr hβ
  | @fix Γ' a' body' hΓ' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · exact Or.inl ⟨j, hj, by simpa only [uses] using huj⟩
      · exact Or.inr hβ
  | @consH E' Γ' Δ' hd' tl' hc' ht' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · have hlt : j < Γ'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using huj
      · exact Or.inr hβ
  | @consT E' Γ' Δ' hd' tl' hc' ht' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · refine Or.inl ⟨Γ'.length + j, ?_, ?_⟩
        · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length j), Nat.add_sub_cancel_left]
          exact hj
        · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length j)),
            Nat.add_sub_cancel_left] using huj
      · exact Or.inr hβ
  | @snocT E' Γ' Δ' t' u' ht' hu' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · have hlt : j < Γ'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using huj
      · exact Or.inr hβ
  | @snocU E' Γ' Δ' t' u' ht' hu' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · refine Or.inl ⟨Γ'.length + j, ?_, ?_⟩
        · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length j), Nat.add_sub_cancel_left]
          exact hj
        · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length j)),
            Nat.add_sub_cancel_left] using huj
      · exact Or.inr hβ
  | @contr Γ' k' t' τ' hk' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · cases j with
        | zero =>
            rw [List.get?_zero_cons'] at hj
            injection hj with hA
            subst hA
            refine Or.inl ⟨0, List.get?_zero_cons', ?_⟩
            show (if (0 : Nat) = 0 then uses h' 0 + uses h' 1 else uses h' (0 + 1)) ≥ 1
            rw [if_pos rfl]
            exact Nat.le_trans huj (Nat.le_add_right (uses h' 0) (uses h' 1))
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hj
                injection hj with hA
                subst hA
                refine Or.inl ⟨0, List.get?_zero_cons', ?_⟩
                show (if (0 : Nat) = 0 then uses h' 0 + uses h' 1 else uses h' (0 + 1)) ≥ 1
                rw [if_pos rfl]
                exact Nat.le_trans huj (Nat.le_add_left (uses h' 1) (uses h' 0))
            | succ m' =>
                rw [List.get?_add_two] at hj
                refine Or.inl ⟨m' + 1, ?_, ?_⟩
                · rw [List.get?_succ_cons']
                  exact hj
                · simpa only [uses, if_neg (Nat.succ_ne_zero m')] using huj
      · exact Or.inr hβ
  | @weak Γ' k' t' τ' hk' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos hu
      rcases ih i A hpos hu with ⟨j, hj, huj⟩ | hβ
      · refine Or.inl ⟨j + 1, ?_, ?_⟩
        · rw [List.get?_succ_cons']
          exact hj
        · simpa only [uses, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel] using huj
      · exact Or.inr hβ
  | @lamD Γ' a' b' body' h' =>
      intro i A hpos hu
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hA
          subst hA
          exact Or.inr ⟨_, _, _, Typed.lam h', Introduces.lamI h', Sub.lamD⟩
      | succ m =>
          rw [List.get?_succ_cons'] at hpos
          exact Or.inl ⟨m, hpos, by simpa only [uses] using hu⟩
  | @appLD E' Γ' Δ' a' b' fn' arg' hf' ha' hs' =>
      intro i A hpos hu
      have hlt : i < Γ'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using hu
  | @appRD E' Γ' Δ' a' b' fn' arg' hf' ha' hs' =>
      intro i A hpos hu
      refine Or.inl ⟨Γ'.length + i, ?_, ?_⟩
      · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length i), Nat.add_sub_cancel_left]
        exact hpos
      · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length i)),
          Nat.add_sub_cancel_left] using hu
  | @pairLD E' Γ' Δ' a' b' l' r' hl' hr' hs' =>
      intro i A hpos hu
      have hlt : i < Γ'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using hu
  | @pairRD E' Γ' Δ' a' b' l' r' hl' hr' hs' =>
      intro i A hpos hu
      refine Or.inl ⟨Γ'.length + i, ?_, ?_⟩
      · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length i), Nat.add_sub_cancel_left]
        exact hpos
      · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length i)),
          Nat.add_sub_cancel_left] using hu
  | @leteTD E' Γ₁' Γ₂' a' b' c' t' body' ht' hb' hs' =>
      intro i A hpos hu
      have hlt : i < Γ₁'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using hu
  | @leteBD E' Γ₁' Γ₂' a' b' c' t' body' ht' hb' hs' =>
      intro i A hpos hu
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hA
          subst hA
          exact Or.inr ⟨_, _, _, Typed.lete ht' hb' hs', Introduces.leteIY, Sub.leteBD⟩
      | succ m =>
          cases m with
          | zero =>
              rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
              injection hpos with hA
              subst hA
              exact Or.inr ⟨_, _, _, Typed.lete ht' hb' hs', Introduces.leteIX, Sub.leteBD⟩
          | succ m' =>
              rw [List.get?_add_two] at hpos
              refine Or.inl ⟨Γ₁'.length + m', ?_, ?_⟩
              · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ₁'.length m'),
                  Nat.add_sub_cancel_left]
                exact hpos
              · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ₁'.length m')),
                  Nat.add_sub_cancel_left] using hu
  | @nextD Γ' a' t' h' =>
      intro i A hpos hu
      exact Or.inl ⟨i, hpos, by simpa only [uses] using hu⟩
  | @fixD Γ' a' body' hΓ' h' =>
      intro i A hpos hu
      exact Or.inl ⟨i, hpos, by simpa only [uses] using hu⟩
  | @consHD E' Γ' Δ' hd' tl' hc' ht' hs' =>
      intro i A hpos hu
      have hlt : i < Γ'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using hu
  | @consTD E' Γ' Δ' hd' tl' hc' ht' hs' =>
      intro i A hpos hu
      refine Or.inl ⟨Γ'.length + i, ?_, ?_⟩
      · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length i), Nat.add_sub_cancel_left]
        exact hpos
      · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length i)),
          Nat.add_sub_cancel_left] using hu
  | @snocTD E' Γ' Δ' t' u' ht' hu' hs' =>
      intro i A hpos hu
      have hlt : i < Γ'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using hu
  | @snocUD E' Γ' Δ' t' u' ht' hu' hs' =>
      intro i A hpos hu
      refine Or.inl ⟨Γ'.length + i, ?_, ?_⟩
      · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length i), Nat.add_sub_cancel_left]
        exact hpos
      · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length i)),
          Nat.add_sub_cancel_left] using hu
  | @contrD Γ' k' t' τ' hk' h' =>
      intro i A hpos hu
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hA
          subst hA
          refine Or.inl ⟨0, List.get?_zero_cons', ?_⟩
          show (if (0 : Nat) = 0 then uses h' 0 + uses h' 1 else uses h' (0 + 1)) ≥ 1
          rw [if_pos rfl]
          exact Nat.le_trans hu (Nat.le_add_right (uses h' 0) (uses h' 1))
      | succ m =>
          cases m with
          | zero =>
              rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
              injection hpos with hA
              subst hA
              refine Or.inl ⟨0, List.get?_zero_cons', ?_⟩
              show (if (0 : Nat) = 0 then uses h' 0 + uses h' 1 else uses h' (0 + 1)) ≥ 1
              rw [if_pos rfl]
              exact Nat.le_trans hu (Nat.le_add_left (uses h' 1) (uses h' 0))
          | succ m' =>
              rw [List.get?_add_two] at hpos
              refine Or.inl ⟨m' + 1, ?_, ?_⟩
              · rw [List.get?_succ_cons']
                exact hpos
              · simpa only [uses, if_neg (Nat.succ_ne_zero m')] using hu
  | @weakD Γ' k' t' τ' hk' h' =>
      intro i A hpos hu
      refine Or.inl ⟨i + 1, ?_, ?_⟩
      · rw [List.get?_succ_cons']
        exact hpos
      · simpa only [uses, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel] using hu

/-- A position at or beyond the context's length is never spent — the
OFF-SIDE ZERO at every split frame: a read threads through splits only
into the side whose context holds the position, so nothing in `h`'s
subtree can target a slot its own context does not have. This is the
engine behind "the arg-side piece is not read by the fn-side subtree". -/
theorem uses_zero_of_ge_length : ∀ {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ),
    ∀ (i : Nat), Γ.length ≤ i → uses h i = 0
  | _, _, _, Typed.var, i, hge => by
      cases i with
      | zero =>
          simp only [List.length_cons, List.length_nil] at hge
          omega
      | succ m => rfl
  | _, _, _, @Typed.lam Γ' a' b' body' h', i, hge => by
      have := uses_zero_of_ge_length h' (i + 1)
        (by simpa only [List.length_cons] using Nat.succ_le_succ hge)
      simpa only [uses] using this
  | _, _, _, @Typed.app E' Γ' Δ' a' b' fn' arg' hf' ha' hs', i, hge => by
      by_cases hlt : i < Γ'.length
      · rw [← hs', List.length_append] at hge
        omega
      · have := uses_zero_of_ge_length ha' (i - Γ'.length)
          (by rw [← hs', List.length_append] at hge; omega)
        simpa only [uses, if_neg hlt] using this
  | _, _, _, @Typed.pair E' Γ' Δ' a' b' l' r' hl' hr' hs', i, hge => by
      by_cases hlt : i < Γ'.length
      · rw [← hs', List.length_append] at hge
        omega
      · have := uses_zero_of_ge_length hr' (i - Γ'.length)
          (by rw [← hs', List.length_append] at hge; omega)
        simpa only [uses, if_neg hlt] using this
  | _, _, _, @Typed.lete E' Γ₁' Γ₂' a' b' c' t' body' ht' hb' hs', i, hge => by
      by_cases hlt : i < Γ₁'.length
      · rw [← hs', List.length_append] at hge
        omega
      · have := uses_zero_of_ge_length hb' (i - Γ₁'.length + 2)
          (by rw [← hs', List.length_append] at hge
              simp only [List.length_cons] at hge ⊢
              omega)
        simpa only [uses, if_neg hlt] using this
  | _, _, _, Typed.unit, _, _ => rfl
  | _, _, _, @Typed.next Γ' a' t' h', i, hge => by
      have := uses_zero_of_ge_length h' i hge
      simpa only [uses] using this
  | _, _, _, @Typed.fix Γ' a' body' hΓ' h', i, hge => by
      have := uses_zero_of_ge_length h' i hge
      simpa only [uses] using this
  | _, _, _, @Typed.cons E' Γ' Δ' hd' tl' hc' ht' hs', i, hge => by
      by_cases hlt : i < Γ'.length
      · rw [← hs', List.length_append] at hge
        omega
      · have := uses_zero_of_ge_length ht' (i - Γ'.length)
          (by rw [← hs', List.length_append] at hge; omega)
        simpa only [uses, if_neg hlt] using this
  | _, _, _, Typed.nil, _, _ => rfl
  | _, _, _, @Typed.snoc E' Γ' Δ' t' u' ht' hu' hs', i, hge => by
      by_cases hlt : i < Γ'.length
      · rw [← hs', List.length_append] at hge
        omega
      · have := uses_zero_of_ge_length hu' (i - Γ'.length)
          (by rw [← hs', List.length_append] at hge; omega)
        simpa only [uses, if_neg hlt] using this
  | _, _, _, Typed.gen, _, _ => rfl
  | _, _, _, Typed.red, _, _ => rfl
  | _, _, _, Typed.obj, _, _ => rfl
  | _, _, _, Typed.terminate, _, _ => rfl
  | _, _, _, @Typed.contr Γ' k' t' τ' hk' h', i, hge => by
      cases i with
      | zero =>
          simp only [List.length_cons] at hge
          omega
      | succ m =>
          have := uses_zero_of_ge_length h' (m + 1 + 1)
            (by simp only [List.length_cons] at hge ⊢; omega)
          simpa only [uses, if_neg (Nat.succ_ne_zero m)] using this
  | _, _, _, @Typed.weak Γ' k' t' τ' hk' h', i, hge => by
      cases i with
      | zero => rfl
      | succ m =>
          have := uses_zero_of_ge_length h' m
            (by simp only [List.length_cons] at hge; omega)
          simpa only [uses, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel] using this

/-- `Sub` is irreflexive — a derivation is never a PROPER subderivation
of itself (the size measure drops along every step). -/
theorem Sub_irrefl : ∀ {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ},
    ¬ Sub d d := by
  intro Γ t τ d hs
  have hsz := Sub_size hs
  omega

/-- The zero-descend mirror of `uses_sub_ge_or_binder`: a position of
`d`'s context either threads UP to a position of `h`'s context whose
spend BOUNDS it (`uses d i ≤ uses h j` — so `uses h j = 0` forces
`uses d i = 0`), or was introduced by a binder between `h` and `d`
(the fresh pieces — the exception the uniqueness argument handles at
the consumer). Same 30-case `Sub` map; the binder positions take the
second disjunct. -/
theorem uses_sub_le : ∀ {Γ₁ : List Ty} {t₁ : Term} {τ₁ : Ty} {h : Typed Γ₁ t₁ τ₁}
    {Γ₂ : List Ty} {t₂ : Term} {τ₂ : Ty} {d : Typed Γ₂ t₂ τ₂}, Sub h d →
    ∀ (i : Nat) (A : Ty), Γ₂[i]? = some A →
    (∃ (j : Nat), Γ₁[j]? = some A ∧ uses d i ≤ uses h j)
    ∨ (∃ (Eβ : List Ty) (tβ : Term) (τβ : Ty) (β : Typed Eβ tβ τβ),
        Introduces β A ∧ Sub β d) := by
  intro Γ₁ t₁ τ₁ h Γ₂ t₂ τ₂ d hs
  induction hs with
  | @lam Γ' a' b' body' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · cases j with
        | zero =>
            rw [List.get?_zero_cons'] at hj
            injection hj with hA
            subst hA
            exact Or.inr ⟨_, _, _, Typed.lam h', Introduces.lamI h', Sub.lam s⟩
        | succ m =>
            rw [List.get?_succ_cons'] at hj
            refine Or.inl ⟨m, hj, ?_⟩
            simpa only [uses] using hle
      · exact Or.inr hβ
  | @appL E' Γ' Δ' a' b' fn' arg' hf' ha' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · have hlt : j < Γ'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using hle
      · exact Or.inr hβ
  | @appR E' Γ' Δ' a' b' fn' arg' hf' ha' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · refine Or.inl ⟨Γ'.length + j, ?_, ?_⟩
        · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length j), Nat.add_sub_cancel_left]
          exact hj
        · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length j)),
            Nat.add_sub_cancel_left] using hle
      · exact Or.inr hβ
  | @pairL E' Γ' Δ' a' b' l' r' hl' hr' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · have hlt : j < Γ'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using hle
      · exact Or.inr hβ
  | @pairR E' Γ' Δ' a' b' l' r' hl' hr' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · refine Or.inl ⟨Γ'.length + j, ?_, ?_⟩
        · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length j), Nat.add_sub_cancel_left]
          exact hj
        · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length j)),
            Nat.add_sub_cancel_left] using hle
      · exact Or.inr hβ
  | @leteT E' Γ₁' Γ₂' a' b' c' t' body' ht' hb' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · have hlt : j < Γ₁'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using hle
      · exact Or.inr hβ
  | @leteB E' Γ₁' Γ₂' a' b' c' t' body' ht' hb' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · cases j with
        | zero =>
            rw [List.get?_zero_cons'] at hj
            injection hj with hA
            subst hA
            exact Or.inr ⟨_, _, _, Typed.lete ht' hb' hs', Introduces.leteIY, Sub.leteB s⟩
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hj
                injection hj with hA
                subst hA
                exact Or.inr ⟨_, _, _, Typed.lete ht' hb' hs', Introduces.leteIX, Sub.leteB s⟩
            | succ m' =>
                rw [List.get?_add_two] at hj
                refine Or.inl ⟨Γ₁'.length + m', ?_, ?_⟩
                · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ₁'.length m'),
                    Nat.add_sub_cancel_left]
                  exact hj
                · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ₁'.length m')),
                    Nat.add_sub_cancel_left] using hle
      · exact Or.inr hβ
  | @next Γ' a' t' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · refine Or.inl ⟨j, hj, ?_⟩
        simpa only [uses] using hle
      · exact Or.inr hβ
  | @fix Γ' a' body' hΓ' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · refine Or.inl ⟨j, hj, ?_⟩
        simpa only [uses] using hle
      · exact Or.inr hβ
  | @consH E' Γ' Δ' hd' tl' hc' ht' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · have hlt : j < Γ'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using hle
      · exact Or.inr hβ
  | @consT E' Γ' Δ' hd' tl' hc' ht' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · refine Or.inl ⟨Γ'.length + j, ?_, ?_⟩
        · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length j), Nat.add_sub_cancel_left]
          exact hj
        · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length j)),
            Nat.add_sub_cancel_left] using hle
      · exact Or.inr hβ
  | @snocT E' Γ' Δ' t' u' ht' hu' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · have hlt : j < Γ'.length := List.get?_some_lt hj
        refine Or.inl ⟨j, ?_, ?_⟩
        · rw [← hs', List.get?_append_lt hlt]
          exact hj
        · simpa only [uses, if_pos hlt] using hle
      · exact Or.inr hβ
  | @snocU E' Γ' Δ' t' u' ht' hu' hs' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · refine Or.inl ⟨Γ'.length + j, ?_, ?_⟩
        · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length j), Nat.add_sub_cancel_left]
          exact hj
        · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length j)),
            Nat.add_sub_cancel_left] using hle
      · exact Or.inr hβ
  | @contr Γ' k' t' τ' hk' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · cases j with
        | zero =>
            rw [List.get?_zero_cons'] at hj
            injection hj with hA
            subst hA
            refine Or.inl ⟨0, List.get?_zero_cons', ?_⟩
            show (if (0 : Nat) = 0 then uses h' 0 + uses h' 1 else uses h' (0 + 1)) ≥ uses d' i
            rw [if_pos rfl]
            exact Nat.le_trans hle (Nat.le_add_right (uses h' 0) (uses h' 1))
        | succ m =>
            cases m with
            | zero =>
                rw [List.get?_succ_cons', List.get?_zero_cons'] at hj
                injection hj with hA
                subst hA
                refine Or.inl ⟨0, List.get?_zero_cons', ?_⟩
                show (if (0 : Nat) = 0 then uses h' 0 + uses h' 1 else uses h' (0 + 1)) ≥ uses d' i
                rw [if_pos rfl]
                exact Nat.le_trans hle (Nat.le_add_left (uses h' 1) (uses h' 0))
            | succ m' =>
                rw [List.get?_add_two] at hj
                refine Or.inl ⟨m' + 1, ?_, ?_⟩
                · rw [List.get?_succ_cons']
                  exact hj
                · simpa only [uses, if_neg (Nat.succ_ne_zero m')] using hle
      · exact Or.inr hβ
  | @weak Γ' k' t' τ' hk' h' Γ₂' t₂' τ₂' d' s ih =>
      intro i A hpos
      rcases ih i A hpos with ⟨j, hj, hle⟩ | hβ
      · refine Or.inl ⟨j + 1, ?_, ?_⟩
        · rw [List.get?_succ_cons']
          exact hj
        · simpa only [uses, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel] using hle
      · exact Or.inr hβ
  | @lamD Γ' a' b' body' h' =>
      intro i A hpos
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hA
          subst hA
          exact Or.inr ⟨_, _, _, Typed.lam h', Introduces.lamI h', Sub.lamD⟩
      | succ m =>
          rw [List.get?_succ_cons'] at hpos
          refine Or.inl ⟨m, hpos, ?_⟩
          simpa only [uses] using Nat.le_refl (uses h' (m + 1))
  | @appLD E' Γ' Δ' a' b' fn' arg' hf' ha' hs' =>
      intro i A hpos
      have hlt : i < Γ'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using Nat.le_refl (uses hf' i)
  | @appRD E' Γ' Δ' a' b' fn' arg' hf' ha' hs' =>
      intro i A hpos
      refine Or.inl ⟨Γ'.length + i, ?_, ?_⟩
      · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length i), Nat.add_sub_cancel_left]
        exact hpos
      · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length i)),
          Nat.add_sub_cancel_left] using Nat.le_refl (uses ha' i)
  | @pairLD E' Γ' Δ' a' b' l' r' hl' hr' hs' =>
      intro i A hpos
      have hlt : i < Γ'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using Nat.le_refl (uses hl' i)
  | @pairRD E' Γ' Δ' a' b' l' r' hl' hr' hs' =>
      intro i A hpos
      refine Or.inl ⟨Γ'.length + i, ?_, ?_⟩
      · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length i), Nat.add_sub_cancel_left]
        exact hpos
      · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length i)),
          Nat.add_sub_cancel_left] using Nat.le_refl (uses hr' i)
  | @leteTD E' Γ₁' Γ₂' a' b' c' t' body' ht' hb' hs' =>
      intro i A hpos
      have hlt : i < Γ₁'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using Nat.le_refl (uses ht' i)
  | @leteBD E' Γ₁' Γ₂' a' b' c' t' body' ht' hb' hs' =>
      intro i A hpos
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hA
          subst hA
          exact Or.inr ⟨_, _, _, Typed.lete ht' hb' hs', Introduces.leteIY, Sub.leteBD⟩
      | succ m =>
          cases m with
          | zero =>
              rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
              injection hpos with hA
              subst hA
              exact Or.inr ⟨_, _, _, Typed.lete ht' hb' hs', Introduces.leteIX, Sub.leteBD⟩
          | succ m' =>
              rw [List.get?_add_two] at hpos
              refine Or.inl ⟨Γ₁'.length + m', ?_, ?_⟩
              · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ₁'.length m'),
                  Nat.add_sub_cancel_left]
                exact hpos
              · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ₁'.length m')),
                  Nat.add_sub_cancel_left] using Nat.le_refl (uses hb' (m' + 2))
  | @nextD Γ' a' t' h' =>
      intro i A hpos
      refine Or.inl ⟨i, hpos, ?_⟩
      simpa only [uses] using Nat.le_refl (uses h' i)
  | @fixD Γ' a' body' hΓ' h' =>
      intro i A hpos
      refine Or.inl ⟨i, hpos, ?_⟩
      simpa only [uses] using Nat.le_refl (uses h' i)
  | @consHD E' Γ' Δ' hd' tl' hc' ht' hs' =>
      intro i A hpos
      have hlt : i < Γ'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using Nat.le_refl (uses hc' i)
  | @consTD E' Γ' Δ' hd' tl' hc' ht' hs' =>
      intro i A hpos
      refine Or.inl ⟨Γ'.length + i, ?_, ?_⟩
      · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length i), Nat.add_sub_cancel_left]
        exact hpos
      · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length i)),
          Nat.add_sub_cancel_left] using Nat.le_refl (uses ht' i)
  | @snocTD E' Γ' Δ' t' u' ht' hu' hs' =>
      intro i A hpos
      have hlt : i < Γ'.length := List.get?_some_lt hpos
      refine Or.inl ⟨i, ?_, ?_⟩
      · rw [← hs', List.get?_append_lt hlt]
        exact hpos
      · simpa only [uses, if_pos hlt] using Nat.le_refl (uses ht' i)
  | @snocUD E' Γ' Δ' t' u' ht' hu' hs' =>
      intro i A hpos
      refine Or.inl ⟨Γ'.length + i, ?_, ?_⟩
      · rw [← hs', List.get?_append_ge (Nat.le_add_right Γ'.length i), Nat.add_sub_cancel_left]
        exact hpos
      · simpa only [uses, if_neg (Nat.not_lt.mpr (Nat.le_add_right Γ'.length i)),
          Nat.add_sub_cancel_left] using Nat.le_refl (uses hu' i)
  | @contrD Γ' k' t' τ' hk' h' =>
      intro i A hpos
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hA
          subst hA
          refine Or.inl ⟨0, List.get?_zero_cons', ?_⟩
          show (if (0 : Nat) = 0 then uses h' 0 + uses h' 1 else uses h' (0 + 1)) ≥ uses h' 0
          rw [if_pos rfl]
          exact Nat.le_add_right (uses h' 0) (uses h' 1)
      | succ m =>
          cases m with
          | zero =>
              rw [List.get?_succ_cons', List.get?_zero_cons'] at hpos
              injection hpos with hA
              subst hA
              refine Or.inl ⟨0, List.get?_zero_cons', ?_⟩
              show (if (0 : Nat) = 0 then uses h' 0 + uses h' 1 else uses h' (0 + 1)) ≥ uses h' 1
              rw [if_pos rfl]
              exact Nat.le_add_left (uses h' 1) (uses h' 0)
          | succ m' =>
              rw [List.get?_add_two] at hpos
              refine Or.inl ⟨m' + 1, ?_, ?_⟩
              · rw [List.get?_succ_cons']
                exact hpos
              · simpa only [uses, if_neg (Nat.succ_ne_zero m')] using Nat.le_refl (uses h' (m' + 2))
  | @weakD Γ' k' t' τ' hk' h' =>
      intro i A hpos
      refine Or.inl ⟨i + 1, ?_, ?_⟩
      · rw [List.get?_succ_cons']
        exact hpos
      · simpa only [uses, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel] using Nat.le_refl (uses h' i)

/-- READ-CONFIG, the read is a `lete`'s SCRUTINEE: the piece's type is
`tensor x y` with a positive trace-net — so some component is
trace-net-positive; the component is a binder of the body's context
(`y :: x :: Γ₂` — position 0 for `y`, 1 for `x`), linear
(trace-carrying), hence spent exactly once by the body (M2). The next
state is the body at the component's position — a strictly smaller
path-reachable positive state. -/
theorem config_lete_elim {t₀ : Term} {root : Typed [Ty.content] t₀ Ty.unit}
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {E Γ₁ Γ₂ : List Ty} {x y c : Ty} {s body : Term}
    {ht : Typed Γ₁ s (.tensor x y)} {hb : Typed (y :: x :: Γ₂) body c}
    {hs : Γ₁ ++ Γ₂ = E}
    (hp : Path root (Typed.lete ht hb hs)) (hxy : tnet x + tnet y > 0) :
    ∃ (j : Nat) (b : Ty), (y :: x :: Γ₂)[j]? = some b ∧ tnet b > 0 ∧
      uses hb j ≥ 1 ∧ fixCount hb = 0 ∧ mintCount hb = 0 ∧ Path root hb ∧
      size hb < size (Typed.lete ht hb hs) := by
  have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
  obtain ⟨hfcb, hmcb⟩ := Prem_clean (Prem.leteBP (ht := ht) (hb := hb) (hs := hs)) hfc hmc
  by_cases hty : tnet y > 0
  · have hlin : y.isLinear = true := by
      rcases Bool.eq_false_or_eq_true y.isLinear with h | h
      · exact h
      · rw [nonlinear_tnet y h] at hty; omega
    exact ⟨0, y, List.get?_zero_cons', hty,
      Nat.le_of_eq (Eq.symm (single_linear_use hb 0 y List.get?_zero_cons' hlin)),
      hfcb, hmcb, Path.step hp Prem.leteBP, Prem_size Prem.leteBP⟩
  · have htx : tnet x > 0 := by omega
    have hlin : x.isLinear = true := by
      rcases Bool.eq_false_or_eq_true x.isLinear with h | h
      · exact h
      · rw [nonlinear_tnet x h] at htx; omega
    refine ⟨1, x, ?_, htx, ?_, hfcb, hmcb, Path.step hp Prem.leteBP, Prem_size Prem.leteBP⟩
    · exact List.get?_succ_cons'.trans List.get?_zero_cons'
    · exact Nat.le_of_eq (Eq.symm (single_linear_use hb 1 x
        (List.get?_succ_cons'.trans List.get?_zero_cons') hlin))

/-- Every premise slot is a proper-subderivation step. -/
theorem sub_of_prem : ∀ {E tc τc} {c : Typed E tc τc} {Γ t τ} {v : Typed Γ t τ},
    Prem c v → Sub c v
  | _, _, _, _, _, _, _, _, Prem.lamP => Sub.lamD
  | _, _, _, _, _, _, _, _, Prem.appFP => Sub.appLD
  | _, _, _, _, _, _, _, _, Prem.appAP => Sub.appRD
  | _, _, _, _, _, _, _, _, Prem.pairLP => Sub.pairLD
  | _, _, _, _, _, _, _, _, Prem.pairRP => Sub.pairRD
  | _, _, _, _, _, _, _, _, Prem.leteTP => Sub.leteTD
  | _, _, _, _, _, _, _, _, Prem.leteBP => Sub.leteBD
  | _, _, _, _, _, _, _, _, Prem.nextP => Sub.nextD
  | _, _, _, _, _, _, _, _, Prem.fixP => Sub.fixD
  | _, _, _, _, _, _, _, _, Prem.consHP => Sub.consHD
  | _, _, _, _, _, _, _, _, Prem.consTP => Sub.consTD
  | _, _, _, _, _, _, _, _, Prem.snocTP => Sub.snocTD
  | _, _, _, _, _, _, _, _, Prem.snocUP => Sub.snocUD
  | _, _, _, _, _, _, _, _, Prem.contrP => Sub.contrD
  | _, _, _, _, _, _, _, _, Prem.weakP => Sub.weakD

/-- The consuming slots: the fire's fn-side, the fire's arg-side, and
the lete-scrutinee — where a value's term-occurrence is consumed. Every
other slot is a ride: the value's term rides inside the composite. -/
inductive ConsumingPrem : {E : List Ty} → {tc : Term} → {τc : Ty} → {c : Typed E tc τc} →
    {Γ : List Ty} → {t : Term} → {τ : Ty} → {v : Typed Γ t τ} →
    Prem c v → Prop where
  | appFP {E Γ Δ X b fn arg} {hf : Typed Γ fn (.arrow X b)} {ha : Typed Δ arg X}
      {hs : Γ ++ Δ = E} :
      ConsumingPrem (Prem.appFP (Γ := Γ) (Δ := Δ) (X := X) (b := b) (fn := fn)
        (arg := arg) (hf := hf) (ha := ha) (hs := hs))
  | appAP {E Γ Δ X b fn arg} {hf : Typed Γ fn (.arrow X b)} {ha : Typed Δ arg X}
      {hs : Γ ++ Δ = E} :
      ConsumingPrem (Prem.appAP (Γ := Γ) (Δ := Δ) (X := X) (b := b) (fn := fn)
        (arg := arg) (hf := hf) (ha := ha) (hs := hs))
  | leteTP {E Γ₁ Γ₂ a b c' t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c'} {hs : Γ₁ ++ Γ₂ = E} :
      ConsumingPrem (Prem.leteTP (Γ₁ := Γ₁) (Γ₂ := Γ₂) (a := a) (b := b) (c' := c')
        (t := t) (body := body) (ht := ht) (hb := hb) (hs := hs))

/-- The chase's root shape: a `[content]`-rooted unit tree has a
premise — it is headed by an app or a lete (every other rule is type-,
context-, or linearity-blocked at `[content] ⊢ unit`). -/
theorem root_unit_prem : ∀ (t : Term) (h : Typed [Ty.content] t Ty.unit),
    ∃ (Γ' : List Ty) (t' : Term) (τ' : Ty) (n' : Typed Γ' t' τ'), Prem h n' := by
  intro t h
  cases h with
  | app hf ha hs => exact ⟨_, _, _, hf, Prem.appFP⟩
  | lete ht hb hs => exact ⟨_, _, _, ht, Prem.leteTP⟩
  | fix hΓ h =>
      have hc : Ty.content.isLinear = false := hΓ 0 Ty.content rfl
      simp only [Ty.isLinear] at hc
      contradiction
  | contr hk h =>
      simp only [Ty.isLinear] at hk
      contradiction
  | weak hk h =>
      simp only [Ty.isLinear] at hk
      contradiction

/-! ## The value-climb

A value's term-occurrence climbs the parent chain through ride slots
until a consuming slot — the corner's entry: from the introducer's
λ-value to the fire that consumes it. -/

/-- The ride slots — the constructive complement of `ConsumingPrem`:
every non-consuming premise slot, one constructor each. The climb's
`RootReach` chain records these (no negation, so the dependent
eliminator never fights the chain's consumers). -/
inductive RidePrem : {E : List Ty} → {tc : Term} → {τc : Ty} → {c : Typed E tc τc} →
    {Γ : List Ty} → {t : Term} → {τ : Ty} → {v : Typed Γ t τ} → Prem c v → Prop where
  | lamP {E : List Ty} {a b : Ty} {body : Term} {h : Typed (a :: E) body b} :
      RidePrem (Prem.lamP (h := h))
  | pairLP {E Γ Δ : List Ty} {a b : Ty} {l r : Term} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} : RidePrem (Prem.pairLP (hl := hl) (hr := hr) (hs := hs))
  | pairRP {E Γ Δ : List Ty} {a b : Ty} {l r : Term} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} : RidePrem (Prem.pairRP (hl := hl) (hr := hr) (hs := hs))
  | nextP {E : List Ty} {a : Ty} {t : Term} {h : Typed E t a} :
      RidePrem (Prem.nextP (h := h))
  | fixP {E : List Ty} {a : Ty} {body : Term} {hΓ : AllNonLinear E}
      {h : Typed E body (.arrow (.later a) a)} : RidePrem (Prem.fixP (hΓ := hΓ) (h := h))
  | consHP {E Γ Δ : List Ty} {hd tl : Term} {hc : Typed Γ hd .content}
      {ht : Typed Δ tl (.later .stream)} {hs : Γ ++ Δ = E} :
      RidePrem (Prem.consHP (hc := hc) (ht := ht) (hs := hs))
  | consTP {E Γ Δ : List Ty} {hd tl : Term} {hc : Typed Γ hd .content}
      {ht : Typed Δ tl (.later .stream)} {hs : Γ ++ Δ = E} :
      RidePrem (Prem.consTP (hc := hc) (ht := ht) (hs := hs))
  | snocTP {E Γ Δ : List Ty} {t u : Term} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} : RidePrem (Prem.snocTP (ht := ht) (hu := hu) (hs := hs))
  | snocUP {E Γ Δ : List Ty} {t u : Term} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} : RidePrem (Prem.snocUP (ht := ht) (hu := hu) (hs := hs))
  | contrP {E : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false}
      {h : Typed (k :: k :: E) (Term.mergeAt 0 t) τ} :
      RidePrem (Prem.contrP (hk := hk) (h := h))
  | weakP {E : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false}
      {h : Typed E t τ} : RidePrem (Prem.weakP (hk := hk) (h := h))
  | leteBP {E Γ₁ Γ₂ : List Ty} {a b c' : Ty} {t body : Term}
      {ht : Typed Γ₁ t (.tensor a b)} {hb : Typed (b :: a :: Γ₂) body c'} {hs : Γ₁ ++ Γ₂ = E} :
      RidePrem (Prem.leteBP (ht := ht) (hb := hb) (hs := hs))

/-- The root-reach chain: the climb's chain of ride slots from `n` up
to the root — the stuck case, which the corner's consumer refutes via
the value's type. Each step records the ride slot and the parent's
path (for the clean-counters facts the refutation needs at fix frames). -/
inductive RootReach {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀) :
    {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Prop where
  | self : RootReach root root
  | up {E : List Ty} {tc : Term} {τc : Ty} {c : Typed E tc τc}
      {Γ : List Ty} {t : Term} {τ : Ty} {n : Typed Γ t τ}
      (s : Prem c n) (hride : RidePrem s) (hp : Path root c)
      (r : RootReach root c) : RootReach root n

/-- THE RIDE-CLIMB: from any node on a path, climbing through ride
slots reaches a consuming slot — unless the chain rides into the root
(the `RootReach` case). The recursion is structural on the `Path`
certificate: each ride step's recursive call is at a strict prefix. -/
theorem value_climb : ∀ {t₀ : Term} (root : Typed [Ty.content] t₀ Ty.unit)
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} {n : Typed Γ t τ} (hp : Path root n),
    (∃ (E' : List Ty) (tc' : Term) (τc' : Ty) (c : Typed E' tc' τc') (hpc : Path root c)
        (s : Prem c n), ConsumingPrem s)
    ∨ (∃ (E' : List Ty) (tc' : Term) (τc' : Ty) (c : Typed E' tc' τc')
        (Γ₀' : List Ty) (t₀' : Term) (τ₀' : Ty) (n₀ : Typed Γ₀' t₀' τ₀')
        (hpc : Path root c) (s : Prem c n₀), ConsumingPrem s ∧ Sub n₀ n)
    ∨ RootReach root n := by
  intro t₀ root hrf hrm Γ t τ n hp
  induction hp with
  | here => exact Or.inr (Or.inr RootReach.self)
  | step p s ih =>
      match s with
      | @Prem.appFP E' Γ' Δ X b fn arg hf ha hs =>
          exact Or.inl ⟨E', Term.app fn arg, b, Typed.app hf ha hs, p, Prem.appFP,
            ConsumingPrem.appFP⟩
      | @Prem.appAP E' Γ' Δ X b fn arg hf ha hs =>
          exact Or.inl ⟨E', Term.app fn arg, b, Typed.app hf ha hs, p, Prem.appAP,
            ConsumingPrem.appAP⟩
      | @Prem.leteTP E' Γ₁ Γ₂ a b c' t' body ht hb hs =>
          exact Or.inl ⟨E', Term.lete t' body, c', Typed.lete ht hb hs, p, Prem.leteTP,
            ConsumingPrem.leteTP⟩
      | @Prem.lamP E' a b body h =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', E', Term.lam a body, Ty.arrow a b,
              Typed.lam h, hpc', s', ⟨hcons, sub_of_prem Prem.lamP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.lamP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.lamP RidePrem.lamP p hreach))
      | @Prem.pairLP E' Γ' Δ a b l r hl hr hs =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', E', Term.pair l r, Ty.tensor a b,
              Typed.pair hl hr hs, hpc', s', ⟨hcons, sub_of_prem Prem.pairLP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.pairLP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.pairLP RidePrem.pairLP p hreach))
      | @Prem.pairRP E' Γ' Δ a b l r hl hr hs =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', E', Term.pair l r, Ty.tensor a b,
              Typed.pair hl hr hs, hpc', s', ⟨hcons, sub_of_prem Prem.pairRP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.pairRP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.pairRP RidePrem.pairRP p hreach))
      | @Prem.nextP E' a t' h =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', E', Term.next t', Ty.later a, Typed.next h,
              hpc', s', ⟨hcons, sub_of_prem Prem.nextP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.nextP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.nextP RidePrem.nextP p hreach))
      | @Prem.fixP E' a body hΓ h =>
          -- a fix node on the path contradicts the clean counters
          have hfc := (Path_clean root p hrf hrm).1
          simp only [fixCount] at hfc
          omega
      | @Prem.consHP E' Γ' Δ hd tl hc ht hs =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', E', Term.cons hd tl, Ty.stream,
              Typed.cons hc ht hs, hpc', s', ⟨hcons, sub_of_prem Prem.consHP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.consHP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.consHP RidePrem.consHP p hreach))
      | @Prem.consTP E' Γ' Δ hd tl hc ht hs =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', E', Term.cons hd tl, Ty.stream,
              Typed.cons hc ht hs, hpc', s', ⟨hcons, sub_of_prem Prem.consTP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.consTP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.consTP RidePrem.consTP p hreach))
      | @Prem.snocTP E' Γ' Δ t' u ht hu hs =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', E', Term.snoc t' u, Ty.trace,
              Typed.snoc ht hu hs, hpc', s', ⟨hcons, sub_of_prem Prem.snocTP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.snocTP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.snocTP RidePrem.snocTP p hreach))
      | @Prem.snocUP E' Γ' Δ t' u ht hu hs =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', E', Term.snoc t' u, Ty.trace,
              Typed.snoc ht hu hs, hpc', s', ⟨hcons, sub_of_prem Prem.snocUP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.snocUP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.snocUP RidePrem.snocUP p hreach))
      | @Prem.contrP E' k t' τ' hk h =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', k :: E', t', τ', Typed.contr hk h,
              hpc', s', ⟨hcons, sub_of_prem Prem.contrP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.contrP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.contrP RidePrem.contrP p hreach))
      | @Prem.weakP E' k t' τ' hk h =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', k :: E', Term.liftAt 0 t', τ', Typed.weak hk h,
              hpc', s', ⟨hcons, sub_of_prem Prem.weakP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.weakP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.weakP RidePrem.weakP p hreach))
      | @Prem.leteBP E' Γ₁ Γ₂ a b c'' t' body ht hb hs =>
          rcases ih with
            ⟨E'', tc'', τc'', c', hpc', s', hcons⟩
          | ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀, hpc', s', hcons, hsub⟩
          | hreach
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', E', Term.lete t' body, c'',
              Typed.lete ht hb hs, hpc', s', ⟨hcons, sub_of_prem Prem.leteBP⟩⟩)
          · refine Or.inr (Or.inl ⟨E'', tc'', τc'', c', Γ₀', t₀', τ₀', n₀,
              hpc', s', ⟨hcons, Sub_trans hsub (sub_of_prem Prem.leteBP)⟩⟩)
          · exact Or.inr (Or.inr (RootReach.up Prem.leteBP RidePrem.leteBP p hreach))

/-- THE ROOT-REACH REFUTATION: a ride-chain from a non-unit-typed node
cannot reach the root — the chain's slots are all non-consuming, and a
unit-root's only non-consuming slot is its lete's body-slot, whose
child is unit-typed; the non-unit type propagates up every other ride
slot, and the chain cannot pass the root. This is what lets the
corner's consumer discard `value_climb`'s third disjunct for an
arrow-typed introducer. -/
theorem no_root_reach : ∀ {t₀ : Term} (root : Typed [Ty.content] t₀ Ty.unit)
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} {n : Typed Γ t τ},
    RootReach root n → τ ≠ Ty.unit → False := by
  intro t₀ root hrf hrm Γ t τ n hr
  induction hr with
  | self =>
      intro hne'
      exact absurd rfl hne'
  | @up E tc τc c Γ' t' τ' n' s hride hp r ih =>
      intro hne'
      cases hride with
      | lamP => exact ih (by intro h; cases h)
      | pairLP => exact ih (by intro h; cases h)
      | pairRP => exact ih (by intro h; cases h)
      | nextP => exact ih (by intro h; cases h)
      | fixP =>
          have hfc := (Path_clean root hp hrf hrm).1
          simp only [fixCount] at hfc
          omega
      | consHP => exact ih (by intro h; cases h)
      | consTP => exact ih (by intro h; cases h)
      | snocTP => exact ih (by intro h; cases h)
      | snocUP => exact ih (by intro h; cases h)
      | contrP => exact ih hne'
      | weakP => exact ih hne'
      | leteBP => exact ih hne'

/-! ## The data-slot path

The chase's fuel encodes the level (the node's depth) as a number, and
`Path` is Prop-valued — `plen` is large-elimination-refused (obs 110's
probe). The depth is therefore carried as DATA: a list of slot tags,
with the correspondence proven via the ∃-witness route (obs 80 M2 —
legal where plain large elimination is refused). -/

/-- The 15 premise slots as data. -/
inductive Slot : Type where
  | lamP | appFP | appAP | pairLP | pairRP | leteTP | leteBP | nextP | fixP
  | consHP | consTP | snocTP | snocUP | contrP | weakP
  deriving Inhabited

/-- `SlotsOf root d l`: `l` is the slot-tag list of the path `root → d`,
innermost-last (the same order `Path` builds). -/
inductive SlotsOf {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀) :
    {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → List Slot → Prop where
  | here : SlotsOf root root []
  | lamP {E : List Ty} {a b : Ty} {body : Term} {h : Typed (a :: E) body b} {l : List Slot}
      (p : Path root (Typed.lam h)) (hs : SlotsOf root (Typed.lam h) l) :
      SlotsOf root h (Slot.lamP :: l)
  | appFP {E Γ Δ : List Ty} {X b : Ty} {fn arg : Term} {hf : Typed Γ fn (.arrow X b)}
      {ha : Typed Δ arg X} {hs : Γ ++ Δ = E} {l : List Slot}
      (p : Path root (Typed.app hf ha hs)) (hs' : SlotsOf root (Typed.app hf ha hs) l) :
      SlotsOf root hf (Slot.appFP :: l)
  | appAP {E Γ Δ : List Ty} {X b : Ty} {fn arg : Term} {hf : Typed Γ fn (.arrow X b)}
      {ha : Typed Δ arg X} {hs : Γ ++ Δ = E} {l : List Slot}
      (p : Path root (Typed.app hf ha hs)) (hs' : SlotsOf root (Typed.app hf ha hs) l) :
      SlotsOf root ha (Slot.appAP :: l)
  | pairLP {E Γ Δ : List Ty} {a b : Ty} {l r : Term} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} {l' : List Slot}
      (p : Path root (Typed.pair hl hr hs)) (hs' : SlotsOf root (Typed.pair hl hr hs) l') :
      SlotsOf root hl (Slot.pairLP :: l')
  | pairRP {E Γ Δ : List Ty} {a b : Ty} {l r : Term} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} {l' : List Slot}
      (p : Path root (Typed.pair hl hr hs)) (hs' : SlotsOf root (Typed.pair hl hr hs) l') :
      SlotsOf root hr (Slot.pairRP :: l')
  | leteTP {E Γ₁ Γ₂ : List Ty} {a b c' : Ty} {t body : Term} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c'} {hs : Γ₁ ++ Γ₂ = E} {l : List Slot}
      (p : Path root (Typed.lete ht hb hs)) (hs' : SlotsOf root (Typed.lete ht hb hs) l) :
      SlotsOf root ht (Slot.leteTP :: l)
  | leteBP {E Γ₁ Γ₂ : List Ty} {a b c' : Ty} {t body : Term} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c'} {hs : Γ₁ ++ Γ₂ = E} {l : List Slot}
      (p : Path root (Typed.lete ht hb hs)) (hs' : SlotsOf root (Typed.lete ht hb hs) l) :
      SlotsOf root hb (Slot.leteBP :: l)
  | nextP {E : List Ty} {a : Ty} {t : Term} {h : Typed E t a} {l : List Slot}
      (p : Path root (Typed.next h)) (hs : SlotsOf root (Typed.next h) l) :
      SlotsOf root h (Slot.nextP :: l)
  | fixP {E : List Ty} {a : Ty} {body : Term} {hΓ : AllNonLinear E}
      {h : Typed E body (.arrow (.later a) a)} {l : List Slot}
      (p : Path root (Typed.fix hΓ h)) (hs : SlotsOf root (Typed.fix hΓ h) l) :
      SlotsOf root h (Slot.fixP :: l)
  | consHP {E Γ Δ : List Ty} {hd tl : Term} {hc : Typed Γ hd .content}
      {ht : Typed Δ tl (.later .stream)} {hs : Γ ++ Δ = E} {l : List Slot}
      (p : Path root (Typed.cons hc ht hs)) (hs' : SlotsOf root (Typed.cons hc ht hs) l) :
      SlotsOf root hc (Slot.consHP :: l)
  | consTP {E Γ Δ : List Ty} {hd tl : Term} {hc : Typed Γ hd .content}
      {ht : Typed Δ tl (.later .stream)} {hs : Γ ++ Δ = E} {l : List Slot}
      (p : Path root (Typed.cons hc ht hs)) (hs' : SlotsOf root (Typed.cons hc ht hs) l) :
      SlotsOf root ht (Slot.consTP :: l)
  | snocTP {E Γ Δ : List Ty} {t u : Term} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} {l : List Slot}
      (p : Path root (Typed.snoc ht hu hs)) (hs' : SlotsOf root (Typed.snoc ht hu hs) l) :
      SlotsOf root ht (Slot.snocTP :: l)
  | snocUP {E Γ Δ : List Ty} {t u : Term} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} {l : List Slot}
      (p : Path root (Typed.snoc ht hu hs)) (hs' : SlotsOf root (Typed.snoc ht hu hs) l) :
      SlotsOf root hu (Slot.snocUP :: l)
  | contrP {E : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false}
      {h : Typed (k :: k :: E) (Term.mergeAt 0 t) τ} {l : List Slot}
      (p : Path root (Typed.contr hk h)) (hs : SlotsOf root (Typed.contr hk h) l) :
      SlotsOf root h (Slot.contrP :: l)
  | weakP {E : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false}
      {h : Typed E t τ} {l : List Slot}
      (p : Path root (Typed.weak hk h)) (hs : SlotsOf root (Typed.weak hk h) l) :
      SlotsOf root h (Slot.weakP :: l)

/-- The conversion: every path has a slot-tag list (the ∃-witness route
— the list is DATA, the correspondence is the `SlotsOf` certificate). -/
theorem path_slots : ∀ {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d),
    ∃ (l : List Slot), SlotsOf root d l := by
  intro Γ₀ t₀ τ₀ root Γ t τ d hp
  induction hp with
  | here => exact ⟨[], SlotsOf.here⟩
  | step p s ih =>
      rcases ih with ⟨l, hs⟩
      cases s with
      | lamP => exact ⟨Slot.lamP :: l, SlotsOf.lamP p hs⟩
      | appFP => exact ⟨Slot.appFP :: l, SlotsOf.appFP p hs⟩
      | appAP => exact ⟨Slot.appAP :: l, SlotsOf.appAP p hs⟩
      | pairLP => exact ⟨Slot.pairLP :: l, SlotsOf.pairLP p hs⟩
      | pairRP => exact ⟨Slot.pairRP :: l, SlotsOf.pairRP p hs⟩
      | leteTP => exact ⟨Slot.leteTP :: l, SlotsOf.leteTP p hs⟩
      | leteBP => exact ⟨Slot.leteBP :: l, SlotsOf.leteBP p hs⟩
      | nextP => exact ⟨Slot.nextP :: l, SlotsOf.nextP p hs⟩
      | fixP => exact ⟨Slot.fixP :: l, SlotsOf.fixP p hs⟩
      | consHP => exact ⟨Slot.consHP :: l, SlotsOf.consHP p hs⟩
      | consTP => exact ⟨Slot.consTP :: l, SlotsOf.consTP p hs⟩
      | snocTP => exact ⟨Slot.snocTP :: l, SlotsOf.snocTP p hs⟩
      | snocUP => exact ⟨Slot.snocUP :: l, SlotsOf.snocUP p hs⟩
      | contrP => exact ⟨Slot.contrP :: l, SlotsOf.contrP p hs⟩
      | weakP => exact ⟨Slot.weakP :: l, SlotsOf.weakP p hs⟩

/-- SlotsOf composes along the path: the tags of `c → d` prepend the
tags of `root → c`. The induction is on the INNER certificate (each
inner step re-roots its parent's certificate through the outer path). -/
theorem slots_of_append : ∀ {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀)
    {Γc : List Ty} {tc : Term} {τc : Ty} {c : Typed Γc tc τc} {l : List Slot} (hp : Path root c),
    SlotsOf root c l →
    ∀ {Γ : List Ty} {t : Term} {τ : Ty} {v : Typed Γ t τ} {l' : List Slot},
      SlotsOf c v l' → SlotsOf root v (l' ++ l) := by
  intro Γ₀ t₀ τ₀ root Γc tc τc c l hp hc Γ t τ v l' hv
  induction hv generalizing l with
  | here => simpa using hc
  | lamP p hs ih =>
      exact SlotsOf.lamP (Path_append c root p hp) (ih hc)
  | appFP p hs ih =>
      exact SlotsOf.appFP (Path_append c root p hp) (ih hc)
  | appAP p hs ih =>
      exact SlotsOf.appAP (Path_append c root p hp) (ih hc)
  | pairLP p hs ih =>
      exact SlotsOf.pairLP (Path_append c root p hp) (ih hc)
  | pairRP p hs ih =>
      exact SlotsOf.pairRP (Path_append c root p hp) (ih hc)
  | leteTP p hs ih =>
      exact SlotsOf.leteTP (Path_append c root p hp) (ih hc)
  | leteBP p hs ih =>
      exact SlotsOf.leteBP (Path_append c root p hp) (ih hc)
  | nextP p hs ih =>
      exact SlotsOf.nextP (Path_append c root p hp) (ih hc)
  | fixP p hs ih =>
      exact SlotsOf.fixP (Path_append c root p hp) (ih hc)
  | consHP p hs ih =>
      exact SlotsOf.consHP (Path_append c root p hp) (ih hc)
  | consTP p hs ih =>
      exact SlotsOf.consTP (Path_append c root p hp) (ih hc)
  | snocTP p hs ih =>
      exact SlotsOf.snocTP (Path_append c root p hp) (ih hc)
  | snocUP p hs ih =>
      exact SlotsOf.snocUP (Path_append c root p hp) (ih hc)
  | contrP p hs ih =>
      exact SlotsOf.contrP (Path_append c root p hp) (ih hc)
  | weakP p hs ih =>
      exact SlotsOf.weakP (Path_append c root p hp) (ih hc)

/-! ## The Sub-length — the chase fuel's level

The level (the node's depth) must be DATA for the one-Nat fuel, and
`Path`/`Sub` are Prop-valued. The slot-LIST approach runs into the
derivation DAG (the same node can sit at two positions — pair h h — so
list-functionality fails). The clean measure: the LENGTH OF THE SUB
CERTIFICATE ITSELF, as a canonical inductive relation — the canonical
construction makes the compositionality (`Sub_trans`) hold by
induction, with no functionality lemma needed. -/

/-- `SubLen s n`: `n` is the canonical length of the `Sub` certificate
`s` (one per constructor). The 15 bases have length 1; the wrapping
constructors add one to their premise's length. -/
inductive SubLen : {Γ₁ : List Ty} → {t₁ : Term} → {τ₁ : Ty} → {h : Typed Γ₁ t₁ τ₁} →
    {Γ₂ : List Ty} → {t₂ : Term} → {τ₂ : Ty} → {d : Typed Γ₂ t₂ τ₂} →
    Sub h d → Nat → Prop where
  | lam {Γ a b body} {h : Typed (a :: Γ) body b} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂}
      {s : Sub h d} {n : Nat} : SubLen s n → SubLen (Sub.lam (h := h) s) (n + 1)
  | appL {E Γ Δ a b fn arg} {hf : Typed Γ fn (.arrow a b)} {ha : Typed Δ arg a}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub hf d} {n : Nat} :
      SubLen s n → SubLen (Sub.appL (hf := hf) (ha := ha) (hs := hs) s) (n + 1)
  | appR {E Γ Δ a b fn arg} {hf : Typed Γ fn (.arrow a b)} {ha : Typed Δ arg a}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub ha d} {n : Nat} :
      SubLen s n → SubLen (Sub.appR (hf := hf) (ha := ha) (hs := hs) s) (n + 1)
  | pairL {E Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub hl d} {n : Nat} :
      SubLen s n → SubLen (Sub.pairL (hl := hl) (hr := hr) (hs := hs) s) (n + 1)
  | pairR {E Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub hr d} {n : Nat} :
      SubLen s n → SubLen (Sub.pairR (hl := hl) (hr := hr) (hs := hs) s) (n + 1)
  | leteT {E Γ₁ Γ₂ a b c t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E}
      {Γ' t' τ'} {d : Typed Γ' t' τ'} {s : Sub ht d} {n : Nat} :
      SubLen s n → SubLen (Sub.leteT (ht := ht) (hb := hb) (hs := hs) s) (n + 1)
  | leteB {E Γ₁ Γ₂ a b c t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E}
      {Γ' t' τ'} {d : Typed Γ' t' τ'} {s : Sub hb d} {n : Nat} :
      SubLen s n → SubLen (Sub.leteB (ht := ht) (hb := hb) (hs := hs) s) (n + 1)
  | next {Γ a t} {h : Typed Γ t a} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂}
      {s : Sub h d} {n : Nat} : SubLen s n → SubLen (Sub.next (h := h) s) (n + 1)
  | fix {Γ a body} {hΓ : AllNonLinear Γ} {h : Typed Γ body (.arrow (.later a) a)}
      {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub h d} {n : Nat} :
      SubLen s n → SubLen (Sub.fix (hΓ := hΓ) (h := h) s) (n + 1)
  | consH {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub hc d} {n : Nat} :
      SubLen s n → SubLen (Sub.consH (hc := hc) (ht := ht) (hs := hs) s) (n + 1)
  | consT {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub ht d} {n : Nat} :
      SubLen s n → SubLen (Sub.consT (hc := hc) (ht := ht) (hs := hs) s) (n + 1)
  | snocT {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub ht d} {n : Nat} :
      SubLen s n → SubLen (Sub.snocT (ht := ht) (hu := hu) (hs := hs) s) (n + 1)
  | snocU {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub hu d} {n : Nat} :
      SubLen s n → SubLen (Sub.snocU (ht := ht) (hu := hu) (hs := hs) s) (n + 1)
  | contr {Γ k t τ} {hk : k.isLinear = false} {h : Typed (k :: k :: Γ) (Term.mergeAt 0 t) τ}
      {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub h d} {n : Nat} :
      SubLen s n → SubLen (Sub.contr (hk := hk) (h := h) s) (n + 1)
  | weak {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false}
      {h : Typed Γ t τ} {Γ₂ t₂ τ₂} {d : Typed Γ₂ t₂ τ₂} {s : Sub h d} {n : Nat} :
      SubLen s n → SubLen (Sub.weak (hk := hk) (h := h) s) (n + 1)
  | lamD {Γ a b body} {h : Typed (a :: Γ) body b} : SubLen (Sub.lamD (h := h)) 1
  | appLD {E Γ Δ a b fn arg} {hf : Typed Γ fn (.arrow a b)} {ha : Typed Δ arg a}
      {hs : Γ ++ Δ = E} : SubLen (Sub.appLD (hf := hf) (ha := ha) (hs := hs)) 1
  | appRD {E Γ Δ a b fn arg} {hf : Typed Γ fn (.arrow a b)} {ha : Typed Δ arg a}
      {hs : Γ ++ Δ = E} : SubLen (Sub.appRD (hf := hf) (ha := ha) (hs := hs)) 1
  | pairLD {E Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} : SubLen (Sub.pairLD (hl := hl) (hr := hr) (hs := hs)) 1
  | pairRD {E Γ Δ a b l r} {hl : Typed Γ l a} {hr : Typed Δ r b}
      {hs : Γ ++ Δ = E} : SubLen (Sub.pairRD (hl := hl) (hr := hr) (hs := hs)) 1
  | leteTD {E Γ₁ Γ₂ a b c t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E} :
      SubLen (Sub.leteTD (ht := ht) (hb := hb) (hs := hs)) 1
  | leteBD {E Γ₁ Γ₂ a b c t body} {ht : Typed Γ₁ t (.tensor a b)}
      {hb : Typed (b :: a :: Γ₂) body c} {hs : Γ₁ ++ Γ₂ = E} :
      SubLen (Sub.leteBD (ht := ht) (hb := hb) (hs := hs)) 1
  | nextD {Γ a t} {h : Typed Γ t a} : SubLen (Sub.nextD (h := h)) 1
  | fixD {Γ a body} {hΓ : AllNonLinear Γ} {h : Typed Γ body (.arrow (.later a) a)} :
      SubLen (Sub.fixD (hΓ := hΓ) (h := h)) 1
  | consHD {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} : SubLen (Sub.consHD (hc := hc) (ht := ht) (hs := hs)) 1
  | consTD {E Γ Δ hd tl} {hc : Typed Γ hd .content} {ht : Typed Δ tl (.later .stream)}
      {hs : Γ ++ Δ = E} : SubLen (Sub.consTD (hc := hc) (ht := ht) (hs := hs)) 1
  | snocTD {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} : SubLen (Sub.snocTD (ht := ht) (hu := hu) (hs := hs)) 1
  | snocUD {E Γ Δ t u} {ht : Typed Γ t .trace} {hu : Typed Δ u .content}
      {hs : Γ ++ Δ = E} : SubLen (Sub.snocUD (ht := ht) (hu := hu) (hs := hs)) 1
  | contrD {Γ k t τ} {hk : k.isLinear = false} {h : Typed (k :: k :: Γ) (Term.mergeAt 0 t) τ} :
      SubLen (Sub.contrD (hk := hk) (h := h)) 1
  | weakD {Γ : List Ty} {k : Ty} {t : Term} {τ : Ty} {hk : k.isLinear = false}
      {h : Typed Γ t τ} : SubLen (Sub.weakD (hk := hk) (h := h)) 1

/-- Every `Sub` certificate has a canonical length. -/
theorem sub_len_exists : ∀ {Γ₁ : List Ty} {t₁ : Term} {τ₁ : Ty} {h : Typed Γ₁ t₁ τ₁}
    {Γ₂ : List Ty} {t₂ : Term} {τ₂ : Ty} {d : Typed Γ₂ t₂ τ₂} (s : Sub h d),
    ∃ (n : Nat), SubLen s n := by
  intro Γ₁ t₁ τ₁ h Γ₂ t₂ τ₂ d s
  induction s with
  | lam s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.lam hn⟩
  | appL s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.appL hn⟩
  | appR s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.appR hn⟩
  | pairL s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.pairL hn⟩
  | pairR s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.pairR hn⟩
  | leteT s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.leteT hn⟩
  | leteB s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.leteB hn⟩
  | next s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.next hn⟩
  | fix s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.fix hn⟩
  | consH s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.consH hn⟩
  | consT s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.consT hn⟩
  | snocT s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.snocT hn⟩
  | snocU s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.snocU hn⟩
  | contr s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.contr hn⟩
  | weak s ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, SubLen.weak hn⟩
  | lamD => exact ⟨1, SubLen.lamD⟩
  | appLD => exact ⟨1, SubLen.appLD⟩
  | appRD => exact ⟨1, SubLen.appRD⟩
  | pairLD => exact ⟨1, SubLen.pairLD⟩
  | pairRD => exact ⟨1, SubLen.pairRD⟩
  | leteTD => exact ⟨1, SubLen.leteTD⟩
  | leteBD => exact ⟨1, SubLen.leteBD⟩
  | nextD => exact ⟨1, SubLen.nextD⟩
  | fixD => exact ⟨1, SubLen.fixD⟩
  | consHD => exact ⟨1, SubLen.consHD⟩
  | consTD => exact ⟨1, SubLen.consTD⟩
  | snocTD => exact ⟨1, SubLen.snocTD⟩
  | snocUD => exact ⟨1, SubLen.snocUD⟩
  | contrD => exact ⟨1, SubLen.contrD⟩
  | weakD => exact ⟨1, SubLen.weakD⟩

/-- The length composes over `Sub_trans`: the length of the composite
is the sum — the canonical construction makes this hold by induction. -/
theorem sub_len_trans : ∀ {E₁ : List Ty} {t₁ : Term} {τ₁ : Ty} {a : Typed E₁ t₁ τ₁}
    {E₂ : List Ty} {t₂ : Term} {τ₂ : Ty} {b : Typed E₂ t₂ τ₂} {s₁ : Sub a b}
    {n₁ : Nat}, SubLen s₁ n₁ →
    ∀ {E₃ : List Ty} {t₃ : Term} {τ₃ : Ty} {c : Typed E₃ t₃ τ₃} {s₂ : Sub b c}
      {n₂ : Nat}, SubLen s₂ n₂ → SubLen (Sub_trans s₁ s₂) (n₁ + n₂) := by
  intro E₁ t₁ τ₁ a E₂ t₂ τ₂ b s₁ n₁ h1
  induction h1 with
  | lam h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.lam (ih h2)
  | appL h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.appL (ih h2)
  | appR h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.appR (ih h2)
  | pairL h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.pairL (ih h2)
  | pairR h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.pairR (ih h2)
  | leteT h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.leteT (ih h2)
  | leteB h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.leteB (ih h2)
  | next h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.next (ih h2)
  | fix h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.fix (ih h2)
  | consH h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.consH (ih h2)
  | consT h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.consT (ih h2)
  | snocT h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.snocT (ih h2)
  | snocU h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.snocU (ih h2)
  | contr h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.contr (ih h2)
  | weak h ih => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SubLen.weak (ih h2)
  | lamD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.lam h2
  | appLD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.appL h2
  | appRD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.appR h2
  | pairLD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.pairL h2
  | pairRD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.pairR h2
  | leteTD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.leteT h2
  | leteBD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.leteB h2
  | nextD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.next h2
  | fixD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.fix h2
  | consHD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.consH h2
  | consTD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.consT h2
  | snocTD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.snocT h2
  | snocUD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.snocU h2
  | contrD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.contr h2
  | weakD => intro E₃ t₃ τ₃ c s₂ n₂ h2; simpa only [Nat.add_comm] using SubLen.weak h2


/-! ## The corner's level machinery

The corner's level-drop (the one-liner's formal form): the factored
position-introduction — the new piece's introducer's path is a strict
prefix of the old chain — plus the composition lemmas that let the
factored form thread through the arms. (The `sub_path` unfoldings use
per-arm PINNED rewrites — the bare constructors in the theorem
equations re-raise the metavariable failure under `simp`.) -/

/-- `Path_append` associates: appending a two-segment path is the same
as appending segment by segment. -/
theorem path_append_assoc : ∀ {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀)
    {Γc : List Ty} {tc : Term} {τc : Ty} {c : Typed Γc tc τc} (hpc : Path root c)
    {Γm : List Ty} {tm : Term} {τm : Ty} {m : Typed Γm tm τm} (hp1 : Path c m),
    ∀ {Γ : List Ty} {t : Term} {τ : Ty} {v : Typed Γ t τ} (hp2 : Path m v),
    Path_append m root hp2 (Path_append c root hp1 hpc) =
    Path_append c root (Path_append m c hp2 hp1) hpc := by
  intro Γ₀ t₀ τ₀ root Γc tc τc c hpc Γm tm τm m hp1 Γ t τ v hp2
  induction hp2 with
  | here => rfl
  | step p s ih => simp only [Path_append, ih]

/-- `sub_path` commutes with `Sub_trans`: the path of the composite is
the composition of the paths. -/
theorem sub_path_trans : ∀ {E₁ : List Ty} {t₁ : Term} {τ₁ : Ty} {a : Typed E₁ t₁ τ₁}
    {E₂ : List Ty} {t₂ : Term} {τ₂ : Ty} {b : Typed E₂ t₂ τ₂} (h1 : Sub a b),
    ∀ {E₃ : List Ty} {t₃ : Term} {τ₃ : Ty} {c : Typed E₃ t₃ τ₃} (h2 : Sub b c),
    sub_path (Sub_trans h1 h2) = Path_append b a (sub_path h2) (sub_path h1) := by
  intro E₁ t₁ τ₁ a E₂ t₂ τ₂ b h1
  induction h1 with
  | @lam Γ a' b' body h Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @appL E Γ Δ X b' fn arg hf ha hs Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @appR E Γ Δ X b' fn arg hf ha hs Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @pairL E Γ Δ a' b' l r hl hr hs Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @pairR E Γ Δ a' b' l r hl hr hs Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @leteT E Γ₁ Γ₂ a' b' c' t body ht hb hs Γ₂' t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @leteB E Γ₁ Γ₂ a' b' c' t body ht hb hs Γ₂' t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @next Γ a' t h Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @fix Γ a' body hΓ h Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @consH E Γ Δ hd tl hc ht hs Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @consT E Γ Δ hd tl hc ht hs Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @snocT E Γ Δ t u ht hu hs Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @snocU E Γ Δ t u ht hu hs Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @contr Γ k t τ hk h Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @weak Γ k t τ hk h Γ₂ t₂ τ₂ d s ih =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @lamD Γ a' b' body h =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @appLD E Γ Δ X b' fn arg hf ha hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @appRD E Γ Δ X b' fn arg hf ha hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @pairLD E Γ Δ a' b' l r hl hr hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @pairRD E Γ Δ a' b' l r hl hr hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @leteTD E Γ₁ Γ₂ a' b' c' t body ht hb hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @leteBD E Γ₁ Γ₂ a' b' c' t body ht hb hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @nextD Γ a' t h =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @fixD Γ a' body hΓ h =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @consHD E Γ Δ hd tl hc ht hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @consTD E Γ Δ hd tl hc ht hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @snocTD E Γ Δ t u ht hu hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @snocUD E Γ Δ t u ht hu hs =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @contrD Γ k t τ hk h =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]

  | @weakD Γ k t τ hk h =>
      intro E₃ t₃ τ₃ c h2
      simp only [Sub_trans]



end Dcare
