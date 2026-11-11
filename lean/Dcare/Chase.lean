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

end Dcare
