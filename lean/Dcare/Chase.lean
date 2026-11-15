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

/-- The supplement's inertness: no tnet-positive and no snet-positive
position. The S6 fix-layer frame — a `▷a` annotation is inert in both
weights, so a stack of them rides as context-plumbing, and the chase
(which tracks only positive positions) never enters a state on it. -/
def Inert (Γ : List Ty) : Prop :=
  ∀ (j : Nat) (b : Ty), Γ[j]? = some b → tnet b ≤ 0 ∧ snet b ≤ 0

/-- The empty supplement is inert (vacuously — no positions). -/
theorem inert_nil : Inert [] := by
  intro j b hpos
  rw [List.get?_nil'] at hpos
  contradiction

/-- The root's supply profile: `[content] ++ Γ₀` supplies no
tnet-positive position when the supplement Γ₀ is inert — the one fact
that makes an introducer mandatory for every positive position below a
supplemented root. The `[content]`-rooted form is the `Γ₀ := []`
instance. -/
theorem root_content_nonpos {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) :
    ∀ (j : Nat) (b : Ty), ([Ty.content] ++ Γ₀)[j]? = some b → tnet b ≤ 0 := by
  intro j b hpos
  have hpos' : (Ty.content :: Γ₀)[j]? = some b := by simpa using hpos
  cases j with
  | zero =>
      rw [List.get?_zero_cons'] at hpos'
      injection hpos' with hb
      subst hb
      simp [tnet]
  | succ m =>
      rw [List.get?_succ_cons'] at hpos'
      exact (hΓ₀ m b hpos').1

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
        fixCount d' = 0 ∧ mintCount d' = 0 ∧ size d' < size d ∧ b' = b)
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
    · refine Or.inl ⟨E, tp, τp, p, iₚ, τv, hp', hposₚ, hta, huₚ, hpc.1, hpc.2, ?_, hτv⟩
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
theorem introducer_of_positive {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀)
    {t₀ : Term} {root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit}
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d)
    (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (htb : tnet b > 0) :
    ∃ (E' : List Ty) (tp : Term) (τp : Ty) (β : Typed E' tp τp),
      Path root β ∧ Introduces β b ∧ Sub β d := by
  rcases pos_introduced root hp i b hpos with ⟨j, hj⟩ | hintro
  · exact absurd htb (by have hle := root_content_nonpos hΓ₀ j b hj; omega)
  · exact hintro

/-- READ-CONFIG, the read is a fire's FN with a tnet-POSITIVE argument
type: the argument is a positive-conclusion clean node on the path —
`origin_lemma` turns it into a strictly smaller chase state. -/
theorem config_fn_positive_arg {Γ₀ : List Ty} {t₀ : Term}
    {root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit}
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
theorem config_arg_lam_killer {Γ₀ : List Ty} {t₀ : Term}
    {root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit}
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
theorem killer_step {Γ₀ : List Ty} {t₀ : Term}
    {root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit}
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
theorem config_lete_elim {Γ₀ : List Ty} {t₀ : Term}
    {root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit}
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

/-- THE RIDE'S COMP-LANDING (fp11's obs-156, sign-independent): the
ridden component's type `τv` is positive by the STATE, so at the ride's
lete-terminal the landing comp's type IS `τv` — positive regardless of
the composite's sign. The comp is linear (`τv` positive ⇒ trace-carrying
⇒ linear), spent exactly once by the body (`single_linear_use`); the
body is a strictly smaller path-reachable node. This is the ride's
budget-priced move at EVERY sign — no composite-positivity hypothesis
(the READ-config's `config_lete_elim` funding is not needed here). The
caller supplies `τv = x ∨ τv = y` from the ridden side (pairLP → x,
pairRP → y). -/
theorem ride_comp_landing {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {E Γ₁ Γ₂ : List Ty} {x y c : Ty} {s body : Term}
    {ht : Typed Γ₁ s (.tensor x y)} {hb : Typed (y :: x :: Γ₂) body c}
    {hs : Γ₁ ++ Γ₂ = E} {τv : Ty}
    (hp : Path root (Typed.lete ht hb hs))
    (hτv : τv = x ∨ τv = y) (htv : tnet τv > 0) :
    ∃ (j : Nat), (y :: x :: Γ₂)[j]? = some τv ∧ uses hb j ≥ 1 ∧
      fixCount hb = 0 ∧ mintCount hb = 0 ∧ Path root hb ∧
      size hb < size (Typed.lete ht hb hs) := by
  have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
  obtain ⟨hfcb, hmcb⟩ := Prem_clean (Prem.leteBP (ht := ht) (hb := hb) (hs := hs)) hfc hmc
  have hlin : τv.isLinear = true := by
    rcases Bool.eq_false_or_eq_true τv.isLinear with h | h
    · exact h
    · rw [nonlinear_tnet τv h] at htv; omega
  rcases hτv with hx | hy
  · rw [hx] at hlin
    have hpos1x : (y :: x :: Γ₂)[1]? = some x :=
      (List.get?_succ_cons'.trans List.get?_zero_cons')
    have hpos1 : (y :: x :: Γ₂)[1]? = some τv :=
      hpos1x.trans (congrArg some hx.symm)
    exact ⟨1, hpos1,
      Nat.le_of_eq (Eq.symm (single_linear_use hb 1 x hpos1x hlin)),
      hfcb, hmcb, Path.step hp Prem.leteBP, Prem_size Prem.leteBP⟩
  · rw [hy] at hlin
    have hpos0y : (y :: x :: Γ₂)[0]? = some y := List.get?_zero_cons'
    have hpos0 : (y :: x :: Γ₂)[0]? = some τv :=
      hpos0y.trans (congrArg some hy.symm)
    exact ⟨0, hpos0,
      Nat.le_of_eq (Eq.symm (single_linear_use hb 0 y hpos0y hlin)),
      hfcb, hmcb, Path.step hp Prem.leteBP, Prem_size Prem.leteBP⟩

/-- THE RIDE-THREAD (fp11's obs-156 (b), positivity-free): the
composite's journey inside a killer-dive. State: `(d, i)` with the
tracked piece `tensor a b` at position `i`, `tnet a > 0` (the positive
side, by the state — the caller orients the pair's sides). The walk
locates the piece's read (`read_locate` — no positivity hypothesis),
dives through λ-killers (type-stable, size ↓ — the killer's domain IS
the composite), and lands at the composite's own lete-opening: the
`a`-comp is positive, `ride_comp_landing` returns the positive state.
The exits: a RIDE-parent (the composite rides into a wrap, or TOP — the
caller re-dispatches, paying the rides-budget), or a FIRE whose fn is
NOT λ-headed (the caller re-dispatches the var-fn/spine/transparent
configs). -/
theorem ride_thread {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hrf : fixCount root = 0) (hrm : mintCount root = 0) :
    ∀ (n : Nat) {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ},
    size d ≤ n →
    Path root d →
    ∀ (i : Nat) (a b : Ty), Γ[i]? = some (Ty.tensor a b) → uses d i ≥ 1 →
    tnet a > 0 →
    (∃ (Γ' : List Ty) (t' : Term) (τ' : Ty) (d' : Typed Γ' t' τ') (i' : Nat) (b' : Ty)
        (hp' : Path root d'),
      Γ'[i']? = some b' ∧ tnet b' > 0 ∧ uses d' i' ≥ 1 ∧
      fixCount d' = 0 ∧ mintCount d' = 0)
    ∨ (∃ (E' : List Ty) (tc' : Term) (τc' : Ty) (c : Typed E' tc' τc'),
        Path root c)
    ∨ (∃ (Γf : List Ty) (fn : Term) (X' b'' : Ty)
          (hf : Typed Γf fn (Ty.arrow X' b'')) (hX' : X' = Ty.tensor a b)
          (Γa : List Ty) (arg : Term) (ha : Typed Γa arg X')
          (E : List Ty) (hs : Γf ++ Γa = E),
        Path root (Typed.app hf ha hs)) := by
  intro n
  induction n with
  | zero =>
      intro Γ t τ d hn hp i a b hpos hu hta
      exact absurd hn (Nat.not_le_of_lt (size_pos d))
  | succ n ih =>
      intro Γ t τ d hn hp i a b hpos hu hta
      have hlin_a : a.isLinear = true := by
        rcases Bool.eq_false_or_eq_true a.isLinear with h | h
        · exact h
        · rw [nonlinear_tnet a h] at hta; omega
      have hlin_T : (Ty.tensor a b).isLinear = true := by
        simp only [Ty.isLinear, hlin_a, Bool.true_or]
      rcases read_locate (size d) d (Nat.le_refl _) i (Ty.tensor a b) hpos hu with
        deep | direct | top
      · -- DEEP: the read's parent p, Sub d p — the slot analysis at p.
        obtain ⟨E, tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ := deep
        have hp' : Path root p := Path_append d root (sub_path hsub) hp
        have hszp : size p ≤ n := by have h1 := Sub_size hsub; omega
        -- the slot map at p (the read v is the tracked composite).
        match hprem with
        | @Prem.appAP E' Γf Δ X b' fn arg hf ha hs =>
            cases hf with
            | lam hb =>
                -- THE DIVE: the killer's body at position 0 : tensor a b.
                have hX : X = Ty.tensor a b := hτv
                have hposb : (X :: Γf)[0]? = some (Ty.tensor a b) :=
                  (List.get?_zero_cons' : (X :: Γf)[0]? = some X).trans (congrArg some hX)
                have hlinX : X.isLinear = true := by rw [hX]; exact hlin_T
                have hub : uses hb 0 ≥ 1 :=
                  Nat.le_of_eq (Eq.symm (single_linear_use hb 0 X List.get?_zero_cons' hlinX))
                have hpb : Path root hb :=
                  Path.step (Path.step hp' Prem.appFP) Prem.lamP
                have hszb : size hb ≤ n := by
                  rw [size_app] at hszp
                  rw [size_lam] at hszp
                  omega
                exact ih hszb hpb 0 a b hposb hub hta
            | var =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.var, hX,
                  Δ, arg, ha, E', hs, hp'⟩)
            | app hg ha' hs₁ =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.app hg ha' hs₁, hX,
                  Δ, arg, ha, E', hs, hp'⟩)
            | lete ht hb hs₁ =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.lete ht hb hs₁, hX,
                  Δ, arg, ha, E', hs, hp'⟩)
            | fix hΓ h =>
                have ⟨hfc, _⟩ := Path_clean root hp' hrf hrm
                obtain ⟨hfcf, _⟩ :=
                  Prem_clean (Prem.appFP (hf := Typed.fix hΓ h) (ha := ha) (hs := hs)) hfc
                    (by omega)
                have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfcf
                omega
            | gen => cases hτv
            | red => cases hτv
            | obj => cases hτv
            | terminate => cases hτv
            | contr hk h =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.contr hk h, hX,
                  Δ, arg, ha, E', hs, hp'⟩)
            | weak hk h =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.weak hk h, hX,
                  Δ, arg, ha, E', hs, hp'⟩)
        | @Prem.appFP E' Γf Δ X b' fn arg hf ha hs =>
            -- the read = the fire's FN: arrow-typed — the composite is not.
            cases hτv
        | @Prem.leteTP E' Γ₁ Γ₂ x y c' s' body ht hb hs =>
            -- THE OPENING: the composite is the scrutinee — the landing.
            have hxy : Ty.tensor x y = Ty.tensor a b := hτv.trans rfl
            injection hxy with hx hy
            have hta' : tnet a > 0 := hta
            obtain ⟨j, hposj, huj, hfcj, hmcj, hpj, hszj⟩ :=
              ride_comp_landing root hrf hrm (hp := hp') (hτv := Or.inl hx.symm) (htv := hta)
            exact Or.inl ⟨y :: x :: Γ₂, body, c', hb, j, a, hpj, hposj, hta, huj, hfcj, hmcj⟩
        | @Prem.pairLP E' Γf Δ x y l r hl hr hs =>
            exact Or.inr (Or.inl ⟨E', Term.pair l r, Ty.tensor x y, Typed.pair hl hr hs, hp'⟩)
        | @Prem.pairRP E' Γf Δ x y l r hl hr hs =>
            exact Or.inr (Or.inl ⟨E', Term.pair l r, Ty.tensor x y, Typed.pair hl hr hs, hp'⟩)
        | @Prem.nextP E' a' t' h =>
            exact Or.inr (Or.inl ⟨E', Term.next t', Ty.later a', Typed.next h, hp'⟩)
        | @Prem.lamP E' a' b' body h =>
            exact Or.inr (Or.inl ⟨E', Term.lam a' body, Ty.arrow a' b', Typed.lam h, hp'⟩)
        | @Prem.weakP E' k t' τ' hk h =>
            exact Or.inr (Or.inl ⟨k :: E', _, τ', Typed.weak hk h, hp'⟩)
        | @Prem.contrP E' k t' τ' hk h =>
            exact Or.inr (Or.inl ⟨k :: E', _, τ', Typed.contr hk h, hp'⟩)
        | @Prem.leteBP E' Γ₁ Γ₂ x y c' s' body ht hb hs =>
            exact Or.inr (Or.inl ⟨E', Term.lete s' body, c', Typed.lete ht hb hs, hp'⟩)
        | @Prem.consHP E' Γf Δ hd tl hc ht hs =>
            cases hτv
        | @Prem.consTP E' Γf Δ hd tl hc ht hs =>
            cases hτv
        | @Prem.snocTP E' Γf Δ t' u' ht hu' hs =>
            cases hτv
        | @Prem.snocUP E' Γf Δ t' u' ht hu' hs =>
            cases hτv
        | @Prem.fixP E' a' body hΓ h =>
            have ⟨hfc, _⟩ := Path_clean root hp' hrf hrm
            have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfc
            omega
      · -- DIRECT: the read is a premise of d itself — the same slot map at d.
        obtain ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ := direct
        match hprem with
        | @Prem.appAP E' Γf Δ X b' fn arg hf ha hs =>
            cases hf with
            | lam hb =>
                have hX : X = Ty.tensor a b := hτv
                have hposb : (X :: Γf)[0]? = some (Ty.tensor a b) :=
                  (List.get?_zero_cons' : (X :: Γf)[0]? = some X).trans (congrArg some hX)
                have hlinX : X.isLinear = true := by rw [hX]; exact hlin_T
                have hub : uses hb 0 ≥ 1 :=
                  Nat.le_of_eq (Eq.symm (single_linear_use hb 0 X List.get?_zero_cons' hlinX))
                have hpb : Path root hb :=
                  Path.step (Path.step hp Prem.appFP) Prem.lamP
                have hszb : size hb ≤ n := by
                  rw [size_app] at hn
                  rw [size_lam] at hn
                  omega
                exact ih hszb hpb 0 a b hposb hub hta
            | var =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.var, hX,
                  Δ, arg, ha, E', hs, hp⟩)
            | app hg ha' hs₁ =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.app hg ha' hs₁, hX,
                  Δ, arg, ha, E', hs, hp⟩)
            | lete ht hb hs₁ =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.lete ht hb hs₁, hX,
                  Δ, arg, ha, E', hs, hp⟩)
            | fix hΓ h =>
                have ⟨hfc, _⟩ := Path_clean root hp hrf hrm
                obtain ⟨hfcf, _⟩ :=
                  Prem_clean (Prem.appFP (hf := Typed.fix hΓ h) (ha := ha) (hs := hs)) hfc
                    (by omega)
                have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfcf
                omega
            | gen => cases hτv
            | red => cases hτv
            | obj => cases hτv
            | terminate => cases hτv
            | contr hk h =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.contr hk h, hX,
                  Δ, arg, ha, E', hs, hp⟩)
            | weak hk h =>
                have hX : X = Ty.tensor a b := hτv
                exact Or.inr (Or.inr ⟨_, _, X, b', Typed.weak hk h, hX,
                  Δ, arg, ha, E', hs, hp⟩)
        | @Prem.appFP E' Γf Δ X b' fn arg hf ha hs =>
            cases hτv
        | @Prem.leteTP E' Γ₁ Γ₂ x y c' s' body ht hb hs =>
            have hxy : Ty.tensor x y = Ty.tensor a b := hτv.trans rfl
            injection hxy with hx hy
            obtain ⟨j, hposj, huj, hfcj, hmcj, hpj, hszj⟩ :=
              ride_comp_landing root hrf hrm (hp := hp) (hτv := Or.inl hx.symm) (htv := hta)
            exact Or.inl ⟨y :: x :: Γ₂, body, c', hb, j, a, hpj, hposj, hta, huj, hfcj, hmcj⟩
        | @Prem.pairLP E' Γf Δ x y l r hl hr hs =>
            exact Or.inr (Or.inl ⟨E', Term.pair l r, Ty.tensor x y, Typed.pair hl hr hs, hp⟩)
        | @Prem.pairRP E' Γf Δ x y l r hl hr hs =>
            exact Or.inr (Or.inl ⟨E', Term.pair l r, Ty.tensor x y, Typed.pair hl hr hs, hp⟩)
        | @Prem.nextP E' a' t' h =>
            exact Or.inr (Or.inl ⟨E', Term.next t', Ty.later a', Typed.next h, hp⟩)
        | @Prem.lamP E' a' b' body h =>
            exact Or.inr (Or.inl ⟨E', Term.lam a' body, Ty.arrow a' b', Typed.lam h, hp⟩)
        | @Prem.weakP E' k t' τ' hk h =>
            exact Or.inr (Or.inl ⟨k :: E', _, τ', Typed.weak hk h, hp⟩)
        | @Prem.contrP E' k t' τ' hk h =>
            exact Or.inr (Or.inl ⟨k :: E', _, τ', Typed.contr hk h, hp⟩)
        | @Prem.leteBP E' Γ₁ Γ₂ x y c' s' body ht hb hs =>
            exact Or.inr (Or.inl ⟨E', Term.lete s' body, c', Typed.lete ht hb hs, hp⟩)
        | @Prem.consHP E' Γf Δ hd tl hc ht hs =>
            cases hτv
        | @Prem.consTP E' Γf Δ hd tl hc ht hs =>
            cases hτv
        | @Prem.snocTP E' Γf Δ t' u' ht hu' hs =>
            cases hτv
        | @Prem.snocUP E' Γf Δ t' u' ht hu' hs =>
            cases hτv
        | @Prem.fixP E' a' body hΓ h =>
            have ⟨hfc, _⟩ := Path_clean root hp hrf hrm
            have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfc
            omega
      · -- TOP: the node IS the read — the parent exit (the caller's
        -- parent-analysis re-dispatches); at the root the singleton
        -- `[tensor a b]` forces the supplement empty and the head
        -- content — the length-equation kill (the root's context
        -- supplies no tensor).
        obtain ⟨hcΓt, _, _, _⟩ := top
        rcases parent_locate root hp with
          ⟨E, tp, τp, c, hpc, s⟩
        | ⟨hΓr, htr, hτr⟩
        · exact Or.inr (Or.inl ⟨E, tp, τp, c, hpc⟩)
        · have hlen : ([Ty.content] ++ Γ₀).length = 1 := by
            rw [← hΓr]; rw [hcΓt]; rfl
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen
          have hΓ₀nil : Γ₀ = [] := by
            cases Γ₀ with
            | nil => rfl
            | cons c cs => simp at hlen
          rw [hΓ₀nil] at hΓr
          rw [hΓr] at hpos
          have hpos' : (Ty.content :: [])[i]? = some (Ty.tensor a b) := by simpa using hpos
          cases i with
          | zero =>
              rw [List.get?_zero_cons'] at hpos'
              injection hpos' with hCT
              cases hCT
          | succ m =>
              rw [List.get?_succ_cons', List.get?_nil'] at hpos'
              contradiction

/-- THE RIDES-BUDGET: the tree's lete-component count (each lete binds
two comps) — the chase's rides-counter initialization, the pin's fuel
clause `rides ≤ size root` (bounded by 2·size; each ride event
decrements the carried counter, which starts at this def). -/
def rideBudget : {Γ : List Ty} → {t : Term} → {τ : Ty} → Typed Γ t τ → Nat
  | _, _, _, Typed.var => 0
  | _, _, _, @Typed.lam _ _ _ _ h => rideBudget h
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => rideBudget hf + rideBudget ha
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => rideBudget hl + rideBudget hr
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => 2 + rideBudget ht + rideBudget hb
  | _, _, _, Typed.unit => 0
  | _, _, _, @Typed.next _ _ _ h => rideBudget h
  | _, _, _, @Typed.fix _ _ _ _ h => rideBudget h
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => rideBudget hc + rideBudget ht
  | _, _, _, Typed.nil => 0
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => rideBudget ht + rideBudget hu
  | _, _, _, Typed.gen => 0
  | _, _, _, Typed.red => 0
  | _, _, _, Typed.obj => 0
  | _, _, _, Typed.terminate => 0
  | _, _, _, @Typed.contr _ _ _ _ _ h => rideBudget h
  | _, _, _, @Typed.weak _ _ _ _ _ h => rideBudget h

/-- The rides-budget is bounded by twice the tree's size — the global
bound the one-Nat fuel encoding uses (each lete node contributes 2 to
the budget and ≥1 to the size). -/
theorem rideBudget_le_size : ∀ {Γ : List Ty} {t : Term} {τ : Ty}
    (h : Typed Γ t τ), rideBudget h ≤ 2 * size h
  | _, _, _, Typed.var => by simp only [rideBudget, size]; omega
  | _, _, _, @Typed.lam _ _ _ _ h => by
      simp only [rideBudget, size]
      have := rideBudget_le_size h
      omega
  | _, _, _, @Typed.app _ _ _ _ _ _ _ hf ha _ => by
      simp only [rideBudget, size]
      have := rideBudget_le_size hf
      have := rideBudget_le_size ha
      omega
  | _, _, _, @Typed.pair _ _ _ _ _ _ _ hl hr _ => by
      simp only [rideBudget, size]
      have := rideBudget_le_size hl
      have := rideBudget_le_size hr
      omega
  | _, _, _, @Typed.lete _ _ _ _ _ _ _ _ ht hb _ => by
      simp only [rideBudget, size]
      have := rideBudget_le_size ht
      have := rideBudget_le_size hb
      omega
  | _, _, _, Typed.unit => by simp only [rideBudget, size]; omega
  | _, _, _, @Typed.next _ _ _ h => by
      simp only [rideBudget, size]
      have := rideBudget_le_size h
      omega
  | _, _, _, @Typed.fix _ _ _ _ h => by
      simp only [rideBudget, size]
      have := rideBudget_le_size h
      omega
  | _, _, _, @Typed.cons _ _ _ _ _ hc ht _ => by
      simp only [rideBudget, size]
      have := rideBudget_le_size hc
      have := rideBudget_le_size ht
      omega
  | _, _, _, Typed.nil => by simp only [rideBudget, size]; omega
  | _, _, _, @Typed.snoc _ _ _ _ _ ht hu _ => by
      simp only [rideBudget, size]
      have := rideBudget_le_size ht
      have := rideBudget_le_size hu
      omega
  | _, _, _, Typed.gen => by simp only [rideBudget, size]; omega
  | _, _, _, Typed.red => by simp only [rideBudget, size]; omega
  | _, _, _, Typed.obj => by simp only [rideBudget, size]; omega
  | _, _, _, Typed.terminate => by simp only [rideBudget, size]; omega
  | _, _, _, @Typed.contr _ _ _ _ _ h => by
      simp only [rideBudget, size]
      have := rideBudget_le_size h
      omega
  | _, _, _, @Typed.weak _ _ _ _ _ h => by
      simp only [rideBudget, size]
      have := rideBudget_le_size h
      omega

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
theorem root_unit_prem : ∀ {Γ₀ : List Ty} (t : Term)
    (h : Typed ([Ty.content] ++ Γ₀) t Ty.unit),
    ∃ (Γ' : List Ty) (t' : Term) (τ' : Ty) (n' : Typed Γ' t' τ'), Prem h n' := by
  intro Γ₀ t h
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
theorem value_climb : ∀ {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} {n : Typed Γ t τ} (hp : Path root n),
    (∃ (E' : List Ty) (tc' : Term) (τc' : Ty) (c : Typed E' tc' τc') (hpc : Path root c)
        (s : Prem c n), ConsumingPrem s)
    ∨ (∃ (E' : List Ty) (tc' : Term) (τc' : Ty) (c : Typed E' tc' τc')
        (Γ₀' : List Ty) (t₀' : Term) (τ₀' : Ty) (n₀ : Typed Γ₀' t₀' τ₀')
        (hpc : Path root c) (s : Prem c n₀), ConsumingPrem s ∧ Sub n₀ n)
    ∨ RootReach root n := by
  intro Γ₀ t₀ root hrf hrm Γ t τ n hp
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
theorem no_root_reach : ∀ {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} {n : Typed Γ t τ},
    RootReach root n → τ ≠ Ty.unit → False := by
  intro Γ₀ t₀ root hrf hrm Γ t τ n hr
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



/-! ## The corner's level machinery (route b, size-encoded)

The corner's position-introduction at the fire's argument — the
specialized walk (obs 138's route (b), fp8's #94 shape): the corner
always walks at the fire's arg (the last slot `Prem F' w'` known), so
the base-arm problem of the general len-carrying re-derivation never
arises. The return package carries the INTERMEDIATE `Sub β F'` (the
unfactored `pos_introduced` computes it at the appAP arm and composes
past it) — the certificate the drop's containment chain needs.

The LEVEL is size-encoded (fp8's #100 endorsement, superseding the
SubLen route): `size root − size β` for the piece's introducer β — a
Nat computable from the state, strictly dropped at the corner
(`Sub β' F'` from the walk + `Prem F' β_old` give the strict size
chain), non-increasing at M1/M2, arbitrary at the rides, bounded by
`size root`. Two distinct nodes' sizes never need a certificate
equality — the derivation DAG is untouched. SubLen/sub_len_trans stay
banked (proven, off the fuel's critical path).
-/

/-- THE SPECIALIZED CORNER WALK: a position of the fire's ARGUMENT's
context either is root-supplied or was introduced by a binder β with
`Path root β`, `Introduces β b`, `Sub β F'` (β strictly above the fire —
the intermediate at `pos_introduced`'s appAP arm), and `Sub β ha`
(β ⊇ the argument). Three lines on the unfactored `pos_introduced`
applied at the fire's own context. -/
theorem corner_introducer {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty}
    (root : Typed Γ₀ t₀ τ₀)
    {E Γ Δ : List Ty} {X σ : Ty} {fn arg : Term}
    {hf : Typed Γ fn (.arrow X σ)} {ha : Typed Δ arg X} {hs : Γ ++ Δ = E}
    (hpF : Path root (Typed.app hf ha hs))
    (j : Nat) (b : Ty) (hpos : Δ[j]? = some b) :
    (∃ (k : Nat), Γ₀[k]? = some b) ∨
    (∃ (E' : List Ty) (tp : Term) (τp : Ty) (β : Typed E' tp τp),
        Path root β ∧ Introduces β b ∧ Sub β (Typed.app hf ha hs) ∧ Sub β ha) := by
  have hge : Γ.length ≤ Γ.length + j := Nat.le_add_right Γ.length j
  rcases pos_introduced root hpF (Γ.length + j) b
      (by rw [← hs, List.get?_append_ge hge, Nat.add_sub_cancel_left]; exact hpos) with
    ⟨k, hk⟩ | ⟨E', tp, τp, β, hpβ, hint, sβ⟩
  · exact Or.inl ⟨k, hk⟩
  · exact Or.inr ⟨E', tp, τp, β, hpβ, hint, sβ, Sub_trans sβ Sub.appRD⟩

/-- Path containment bounds the size: a node on the root-chain is no
larger than the root. -/
theorem path_size {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d) :
    size d ≤ size root := by
  induction hp with
  | here => exact Nat.le_refl _
  | step p s ih => exact Nat.le_trans (Nat.le_of_lt (Prem_size s)) ih

/-- THE CORNER'S LEVEL DROP, size-encoded: the new introducer β' sits
strictly above the fire (`Sub β' F'`), the fire strictly above the old
introducer (`sub_of_prem Prem.appFP`), so the composition gives
`Sub β' β_old` — sizes strictly grow down the chain, and the
size-deficit level `size root − size β` strictly drops. The one-liner's
arithmetic with no SubLen, no functionality, no upward certificates:
two distinct nodes' sizes never need a certificate equality. -/
theorem corner_level_drop {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty}
    (root : Typed Γ₀ t₀ τ₀)
    {E Γ Δ : List Ty} {X σ : Ty} {fn arg : Term}
    {hf : Typed Γ fn (.arrow X σ)} {ha : Typed Δ arg X} {hs : Γ ++ Δ = E}
    {E' : List Ty} {tp : Term} {τp : Ty} {β' : Typed E' tp τp}
    (hpβ' : Path root β') (sβ'F : Sub β' (Typed.app hf ha hs)) :
    size root - size β' < size root - size hf := by
  have hle : size β' ≤ size root := path_size root hpβ'
  have hchain : Sub β' hf := Sub_trans sβ'F (sub_of_prem Prem.appFP)
  have hsz : size hf < size β' := Sub_size hchain
  omega

/-! ## THE PIECE-CORNER (the corner round)

The chase's corner at the state's piece introducer: the introducer's
VALUE (a λ or lete term) is consumed at a fire; when consumed as the
FN, the fire's ARGUMENT carries the piece type (tnet-positive by the
state), so the origin at the argument gives the next state, and the
next introducer (the specialized walk) sits strictly above the fire —
the size-deficit level strictly drops (`corner_level_drop`). The
consuming-slot alternatives are the NAMED EXITS the chase's round-map
dispatches: the killer-of-promise (the value consumed as an ARG — the
M3-macro entry), the lete-introducer (the class-corner entry), and the
spine-case (`value_climb`'s deep terminal).

The dispatch helpers below are stated with the premise as a VARIABLE
index and with clash-free binders, so the plain `cases` arms bind the
constructor args by their declaration names — the closed-premise /
stuck-index wall (trap 37/77's family) is avoided by case order, and
the premise-is-the-fn identification rides the ∃-WITNESS (the premise
term `v` itself), never an equation.
-/

/-- CONSUMING-SLOT DISPATCH: a `ConsumingPrem` certificate decomposes
into the consuming fire's pieces with the path — the premise `v` rides
as the witness (for appFP, the fire's fn IS `v`, carried with the
type-cast that the caller discharges by cases; for appAP, its arg IS
`v`), so no index equation is ever stated. -/
theorem consuming_fire {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty}
    (root : Typed Γ₀ t₀ τ₀)
    {Ec : List Ty} {tcc : Term} {τcc : Ty} (c : Typed Ec tcc τcc)
    {Γv : List Ty} {tv : Term} {τv : Ty} (v : Typed Γv tv τv)
    (hpc : Path root c) (s : Prem c v) :
    ConsumingPrem s →
    (∃ (Δ : List Ty) (X b : Ty) (arg : Term) (hτ : τv = Ty.arrow X b)
        (ha : Typed Δ arg X) (hs : Γv ++ Δ = Ec),
        Path root (Typed.app (hτ ▸ v) ha hs))
    ∨ (∃ (Γf : List Ty) (b : Ty) (fn : Term) (hf : Typed Γf fn (Ty.arrow τv b))
          (E'' : List Ty) (hs : Γf ++ Γv = E''),
        Path root (Typed.app hf v hs))
    ∨ (∃ (a b : Ty), τv = Ty.tensor a b) := by
  intro hcons
  cases hcons with
  | @appFP _ Δ' X' _ _ arg' hf' ha' hs' =>
      exact Or.inl ⟨Δ', X', τcc, arg', rfl, ha', hs', hpc⟩
  | @appAP Γ' _ _ _ fn' _ hf' _ hs' =>
      exact Or.inr (Or.inl ⟨Γ', τcc, fn', hf', _, hs', hpc⟩)
  | @leteTP _ _ a' b' _ _ _ _ _ _ =>
      exact Or.inr (Or.inr ⟨a', b', rfl⟩)

/-- THE CORNER ROUND, GENERALIZED (interval 12): the piece's
introducer's value's consumer is a fire; the fn-consumer case is the
piece-corner (the argument carries the piece type — `origin_lemma` gives
the next state, the specialized walk's next introducer drops the
size-deficit level). Exits: the killer-of-promise (the value consumed as
an ARG — the macro's entry), the lete-introducer (the comp-entry), the
spine-case (the consuming premise contains the introducer), RootReach.

The statement carries ONLY the introducer `β`, its kind (`Introduces β
b`), and the piece's positivity `tnet b > 0` — the fire-pin and the
arrow-shape are UNUSED by the body (measured: the earlier fire-pin
hypotheses appeared only in the signature), so the corner applies at
EVERY config whose piece is positive: the appFP config, the appAP
config, and the TOP analysis alike. The piece-corner exit prices the
descent strictly better than the direct origin-at-arg (the new
introducer sits above the CONSUMER fire, level ↓ strict via
`corner_level_drop`, vs the arg-origin's level-↓-or-equal). -/
theorem corner_piece {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
    (hpβ : Path root β) {b : Ty} (hint : Introduces β b) (htb : tnet b > 0) :
    (∃ (Δ' : List Ty) (arg' : Term) (ha' : Typed Δ' arg' b)
        (j : Nat) (b' : Ty), Δ'[j]? = some b' ∧ tnet b' > 0 ∧ uses ha' j ≥ 1 ∧
      fixCount ha' = 0 ∧ mintCount ha' = 0 ∧ Path root ha' ∧
      ∃ (E' : List Ty) (tp : Term) (τp : Ty) (β' : Typed E' tp τp),
        Path root β' ∧ Introduces β' b' ∧
        size root - size β' < size root - size β)
    ∨ (∃ (Γ' : List Ty) (fn' : Term) (b'' : Ty) (hf' : Typed Γ' fn' (Ty.arrow τβ b''))
          (E'' : List Ty) (hs' : Γ' ++ Eβ = E''),
        Path root (Typed.app hf' β hs'))
    ∨ (∃ (x y : Ty), b = y ∨ b = x)
    ∨ (∃ (E' : List Ty) (tc' : Term) (τc' : Ty) (c : Typed E' tc' τc')
          (Γ₀' : List Ty) (t₀' : Term) (τ₀' : Ty) (n₀ : Typed Γ₀' t₀' τ₀')
          (hpc : Path root c) (s' : Prem c n₀),
        ConsumingPrem s' ∧ Sub n₀ β)
    ∨ RootReach root β := by
  rcases value_climb root hrf hrm hpβ with
    ⟨E', tc', τc', c, hpc, s', hcons⟩
  | ⟨E', tc', τc', c, Γ₀', t₀', τ₀', n₀, hpc, s', hcons', hsub⟩
  | hreach
  · -- the direct terminal: dispatch the consuming slot (the helper's
    -- premise-variable form keeps the elimination off the stuck-index
    -- wall; the premise β rides as the witness)
    rcases consuming_fire root c β hpc s' hcons with
      ⟨Δ', X', b', arg', hτ, ha', hs', hpcw⟩
    | ⟨Γf, b', fn', hf', E2, hs', hpcw⟩
    | ⟨a', b'', hτt⟩
    · -- the fire = Typed.app (hτ ▸ β) ha' hs' — case the introducer's
      -- kind (β is a variable here, so the elimination runs)
      cases hint with
      | @lamI σβ' body' _ hb' =>
          -- β := Typed.lam hb' — the cast discharges, the fire becomes
          -- Typed.app (Typed.lam hb') ha' hs'
          cases hτ
          have ⟨hfcw, hmcw⟩ := Path_clean root hpcw hrf hrm
          obtain ⟨hfcw2, hmcw2⟩ := Prem_clean (Prem.appAP (hf := Typed.lam hb') (ha := ha') (hs := hs')) hfcw hmcw
          obtain ⟨j, b, hpos, htb', hu⟩ := origin_lemma ha' hfcw2 hmcw2 htb
          rcases corner_introducer root hpcw j b hpos with
            ⟨k, hk⟩ | ⟨Eβ0, tp, τp, β', hpβ', hint', sβ'F, sβ'w⟩
          · exact absurd htb' (by have hle := root_content_nonpos hΓ₀ k b hk; omega)
          · refine Or.inl ⟨Δ', arg', ha', j, b, hpos, htb', hu, hfcw2, hmcw2,
              Path.step hpcw Prem.appAP, Eβ0, tp, τp, β', hpβ', hint', ?_⟩
            · exact corner_level_drop root hpβ' sβ'F
      | @leteIY Γ₁' Γ₂' x' _ _ s' body' ht' hb' hsβ' =>
          -- the lete-introducer: the comp-entry
          exact Or.inr (Or.inr (Or.inl ⟨x', b, Or.inl rfl⟩))
      | @leteIX Γ₁' Γ₂' _ y'' _ s' body' ht' hb' hsβ' =>
          -- the other component — same entry, the x-side
          exact Or.inr (Or.inr (Or.inl ⟨b, y'', Or.inr rfl⟩))
    · -- the killer-of-promise: β's value consumed as an ARG — the
      -- M3-macro entry, a named exit (the fire = Typed.app hf' β hs')
      exact Or.inr (Or.inl ⟨Γf, fn', b', hf', E2, hs', hpcw⟩)
    · -- the scrutinee is β — the ride-landing, emitted as the
      -- comp-entry (the lam-scrutinee is type-blocked: the
      -- tensor/arrow mismatch refutes it via hτt)
      cases hint with
      | @lamI σβ' body' _ hb' =>
          -- the scrutinee's tensor type vs the lam's arrow type
          cases hτt
      | @leteIY Γ₁' Γ₂' x' _ _ s' body' ht' hb' hsβ' =>
          exact Or.inr (Or.inr (Or.inl ⟨x', b, Or.inl rfl⟩))
      | @leteIX Γ₁' Γ₂' _ y'' _ s' body' ht' hb' hsβ' =>
          exact Or.inr (Or.inr (Or.inl ⟨b, y'', Or.inr rfl⟩))
  · -- the spine-case exit (the consuming premise contains the introducer)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E', tc', τc', c, Γ₀', t₀', τ₀', n₀, hpc, s', hcons', hsub⟩)))
  · -- the RootReach case: the ride-chain reached the root — a named
    -- exit (a λ-introducer's type is an arrow, never unit — but a
    -- lete-introducer CAN conclude unit, so the chain is not refutable
    -- in general; the chase's round-map handles it)
    exact Or.inr (Or.inr (Or.inr (Or.inr hreach)))


/-- THE CHASE'S ROUND-MOVE PACKAGE: what the round-map returns to the
chase's induction — a fuel-decreasing state (descent / corner) or a
macro entry. Parameterized by the state node `d` and the current
piece's introducer `β` (the level = size root − size β). The descent
preserves the piece (the caller keeps `β`); the corner carries the new
introducer and the level drop; the macro entries carry the
`corner_piece` exit data. -/
inductive ChaseMove {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    {Γ : List Ty} {t : Term} {τ : Ty} (d : Typed Γ t τ)
    {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
    {b : Ty} : Prop where
  | descent {Γ' : List Ty} {t' : Term} {τ' : Ty} (d' : Typed Γ' t' τ')
      (hp' : Path root d') (i' : Nat) (b' : Ty)
      (hpos' : Γ'[i']? = some b') (htb' : tnet b' > 0) (hu' : uses d' i' ≥ 1)
      (hsz' : size d' < size d) (hτb : b' = b) : ChaseMove root d β
  | corner {Γ' : List Ty} {t' : Term} {τ' : Ty} (d' : Typed Γ' t' τ')
      (hp' : Path root d') (i' : Nat) (b' : Ty)
      (hpos' : Γ'[i']? = some b') (htb' : tnet b' > 0) (hu' : uses d' i' ≥ 1)
      (hfc' : fixCount d' = 0) (hmc' : mintCount d' = 0)
      {E' : List Ty} {tp : Term} {τp : Ty} (β' : Typed E' tp τp)
      (hpβ' : Path root β') (hint' : Introduces β' b')
      (hdrop : size root - size β' < size root - size β) : ChaseMove root d β
  | macroKiller {Γ' : List Ty} (fn' : Term) (b'' : Ty)
      (hf' : Typed Γ' fn' (Ty.arrow τβ b''))
      (E'' : List Ty) (hs' : Γ' ++ Eβ = E'')
      (hpF : Path root (Typed.app hf' β hs')) : ChaseMove root d β
  | macroComp (x y : Ty) (hxy : b = y ∨ b = x) : ChaseMove root d β
  | macroSpine {E' : List Ty} (tc' : Term) (τc' : Ty) (c : Typed E' tc' τc')
      {Γ₀' : List Ty} (t₀' : Term) (τ₀' : Ty) (n₀ : Typed Γ₀' t₀' τ₀')
      (hpc : Path root c) (s' : Prem c n₀)
      (hcons : ConsumingPrem s') (hsub : Sub n₀ β) : ChaseMove root d β

/-- THE CORNER DISPATCH, UNIFORM: `corner_piece` at the piece's
introducer prices EVERY config — the corner move (level ↓ strict), the
killer-of-promise (the macro's entry), the lete-introducer (the
macro's comp-entry), the spine-case, and RootReach (λ-introducers die
by `no_root_reach`, lete-introducers emit the comp-entry). The corner
is about the INTRODUCER's value's fate, which is config-independent —
the appFP/appAP/ride/TOP configs all route here. -/
theorem corner_dispatch {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} (d : Typed Γ t τ)
    {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
    (hpβ : Path root β) {b : Ty} (hint : Introduces β b) (htb : tnet b > 0) :
    ChaseMove (b := b) root d β := by
  rcases corner_piece root hΓ₀ hrf hrm β hpβ hint htb with
    ⟨Δ', arg', ha', j, b'', hposj, htb'', huj, hfcj, hmcj, hpj,
      Eβ0, tp, τp, β', hpβ', hint', hdrop⟩
  | ⟨Γf, fn', b'', hf', E2, hs', hpcw⟩
  | ⟨x, y, hxy⟩
  | ⟨E', tc', τc', c, Γ₀', t₀', τ₀', n₀, hpc, s', hcons', hsub⟩
  | hreach
  · exact ChaseMove.corner ha' hpj j b'' hposj htb'' huj hfcj hmcj β' hpβ' hint' hdrop
  · exact ChaseMove.macroKiller fn' b'' hf' E2 hs' hpcw
  · exact ChaseMove.macroComp x y hxy
  · exact ChaseMove.macroSpine tc' τc' c t₀' τ₀' n₀ hpc s' hcons' hsub
  · -- RootReach: a λ-introducer's value cannot reach the root (arrow ≠
    -- unit — `no_root_reach`); a lete-introducer's can (unit-concluding)
    -- — the comp-entry.
    cases hint with
    | @lamI σβ body _ hb =>
        exact False.elim (no_root_reach root hrf hrm hreach (by intro h; cases h))
    | @leteIY Γ₁ Γ₂ x y c' s' body' ht hb hs =>
        exact ChaseMove.macroComp x b (Or.inl rfl)
    | @leteIX Γ₁ Γ₂ x y c' s' body' ht hb hs =>
        exact ChaseMove.macroComp b y (Or.inr rfl)

/-- THE CHASE'S ROUND: from the state (d, i) with `tnet b > 0` under a
clean [content]-rooted tree, the move package — the descent (same
piece, size ↓ — `chase_step`), or the corner dispatch at the piece's
introducer (every config and TOP route there). -/
theorem chase_round {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d)
    (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (htb : tnet b > 0) (hu : uses d i ≥ 1)
    {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
    (hpβ : Path root β) (hint : Introduces β b) :
    ChaseMove (b := b) root d β := by
  rcases chase_step root hp hrf hrm i b hpos htb hu with
    ⟨Γ', t', τ', d', i', b', hp', hpos', htb', hu', hfc', hmc', hsz', hτb⟩
  | ⟨E, tc, τc, d', hp', hle, Γv, tv, τv, v, htv, hcΓv, hta, hprem, hposOr⟩
  | top
  · exact ChaseMove.descent d' hp' i' b' hpos' htb' hu' hsz' hτb
  · exact corner_dispatch root hΓ₀ hrf hrm d β hpβ hint htb
  · exact corner_dispatch root hΓ₀ hrf hrm d β hpβ hint htb

/-- Sub-or-equal: the chain's exit packages carry the exit node's
relation to the chain state without the heterogeneous-Eq trap (the
`d = hw` case is the origin-at-`d`-itself exit; the `Sub` case is the
deeper exit). -/
inductive SubEq {Γ₁ : List Ty} {t₁ : Term} {τ₁ : Ty} (d : Typed Γ₁ t₁ τ₁) :
    {Γ₂ : List Ty} → {t₂ : Term} → {τ₂ : Ty} → Typed Γ₂ t₂ τ₂ → Prop where
  | sub {Γ₂ : List Ty} {t₂ : Term} {τ₂ : Ty} {hw : Typed Γ₂ t₂ τ₂} : Sub d hw → SubEq d hw
  | refl : SubEq d d

/-- `SubEq` transitivity — the chain's exit anchors compose with the
entry state: the macro's span-containment (each exit's node relates to
the chain's entry) is the `Sub` case of the transitive composite. -/
theorem SubEq_trans {Γ₁ : List Ty} {t₁ : Term} {τ₁ : Ty} {d : Typed Γ₁ t₁ τ₁}
    {Γ₂ : List Ty} {t₂ : Term} {τ₂ : Ty} {e : Typed Γ₂ t₂ τ₂}
    {Γ₃ : List Ty} {t₃ : Term} {τ₃ : Ty} {f : Typed Γ₃ t₃ τ₃} :
    SubEq d e → SubEq e f → SubEq d f := by
  intro h1 h2
  cases h1 with
  | sub h =>
      cases h2 with
      | sub h' => exact SubEq.sub (Sub_trans h h')
      | refl => exact SubEq.sub h
  | refl =>
      cases h2 with
      | sub h' => exact SubEq.sub h'
      | refl => exact SubEq.refl

/-- THE CLASS-FLAVORED `prem_position`: the whole-type positivity is
replaced by the PC class (the position's type is `arrow b σ` with
`tnet b > 0`), which is exactly what the killer-chain's state carries —
its position type's OWN tnet sign is unknown, only the domain's is
known. The linearity for `single_linear_use` then comes from the
class's domain. -/
theorem prem_position_class : ∀ {E : List Ty} {tc : Term} {τc : Ty} {p : Typed E tc τc}
    {Γv : List Ty} {tv : Term} {τv : Ty} {v : Typed Γv tv τv}, Prem p v →
    tv = Term.var 0 → Γv = [τv] →
    ∀ {b σ : Ty}, τv = Ty.arrow b σ → tnet b > 0 →
    (∃ (i : Nat), E[i]? = some τv ∧ uses p i ≥ 1)
    ∨ (E = [] ∧ ∃ (a' : Ty), tc = Term.lam a' (Term.var 0)) := by
  intro E tc τc p Γv tv τv v s htv hΓ
  intro b σ hτv htb
  have hblin : b.isLinear = true := by
    rcases Bool.eq_false_or_eq_true b.isLinear with h | h
    · exact h
    · rw [nonlinear_tnet b h] at htb; omega
  have hlin : τv.isLinear = true := by
    rw [hτv]; simp only [Ty.isLinear, hblin, Bool.true_or]
  match s, htv, hΓ with
  | @Prem.lamP E' a' b' body h, htv, hΓ' =>
      injection hΓ' with haE hE
      exact Or.inr ⟨hE, ⟨a', by rw [htv, haE]⟩⟩
  | @Prem.appFP E' Γ' Δ X b' fn arg hf ha hs, _, hΓ' =>
      refine Or.inl ⟨0, ?_, ?_⟩
      · rw [← hs, List.get?_append_lt (by rw [hΓ']; simp)]
        rw [hΓ']; exact List.get?_zero_cons'
      · simp only [uses]
        rw [if_pos (by rw [hΓ']; simp : (0 : Nat) < Γ'.length)]
        exact Nat.le_of_eq (Eq.symm (single_linear_use hf 0 _ (get?_zero_of_singleton hΓ') hlin))
  | @Prem.appAP E' Γ' Δ X b' fn arg hf ha hs, _, hΓ' =>
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
      cases hτv
  | @Prem.consTP E' Γ' Δ hd tl hc ht hs, _, _ =>
      cases hτv
  | @Prem.snocTP E' Γ' Δ t u ht hu hs, _, hΓ' =>
      cases hτv
  | @Prem.snocUP E' Γ' Δ t u ht hu hs, _, _ =>
      cases hτv
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

/-- THE CHAIN'S EXIT PACKAGE: what the killer-chain returns to the
macro — a named inductive instead of a nested Or, one constructor per
exit the macro's round-map dispatches on. Each constructor carries its
own ANCHOR `d'` and its own `Path` data (the chain's internal
recursions exit at inner nodes; the exits are consumed as bare
∃-packages — the anchor relations the macro needs are re-derived at S3
from the descent certificates, fp9's verdict #112). `T` is the PC class
type (`T = arrow b σ`, `tnet b > 0`). -/
inductive ChainExit {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit) (T : Ty) : Prop where
  | pos {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Δ : List Ty} {X : Ty} {w : Term} {hw : Typed Δ w X} {j : Nat} {b' : Ty}
      (hX : tnet X > 0) (hpos : Δ[j]? = some b') (htb : tnet b' > 0) (hu : uses hw j ≥ 1)
      (hfc : fixCount hw = 0) (hmc : mintCount hw = 0) (hpw : Path root hw)
      (hrel : SubEq d' hw)
      {E' : List Ty} {tp : Term} {τp : Ty} {β' : Typed E' tp τp}
      (hpβ : Path root β') (hint : Introduces β' b') (sβ : Sub β' hw) : ChainExit root T
  | ride1 {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
      (hpc : Path root c) (s : Prem c d') (hcons : ConsumingPrem s) : ChainExit root T
  | ride2 {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
      {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
      (hpc : Path root c) (s : Prem c n₀) (hcons : ConsumingPrem s)
      (hsub : Sub n₀ d') : ChainExit root T
  | rideReach {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      (hp : Path root d') (hreach : RootReach root d') (hne : τd ≠ Ty.unit) : ChainExit root T
  | top {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      (hcΓ : Γd = [T]) (htv : td = Term.var 0) (hcτ : τd = T)
      {Ec : List Ty} {tc : Term} {τc : Ty} (c : Typed Ec tc τc)
      (hpc : Path root c) (s : Prem c d') (hsub : Sub c d') : ChainExit root T
  | varFn {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Γf : List Ty} {v : Typed [T] (Term.var 0) T} {hs : Γf ++ [T] = Γd}
      {hf : Typed Γf (Term.var 0) (Ty.arrow T τd)}
      (hp : Path root d') (ht : tnet τd ≤ 0) : ChainExit root T
  | spineLam {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Γf : List Ty} {Δa : List Ty} {Wb σb : Ty} {body arg : Term}
      {hb : Typed (Wb :: Γf) body σb} {ha : Typed Δa arg Wb}
      {E' : List Ty} {hs' : Γf ++ Δa = E'}
      (hp : Path root (Typed.app (Typed.lam hb) ha hs'))
      (hsub : Sub d' (Typed.app (Typed.lam hb) ha hs'))
      (hW : tnet Wb ≤ 0) (hc : tnet σb ≤ 0) : ChainExit root T
  | spineVar {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Δa : List Ty} {Wb σb : Ty} {arg : Term} {ha : Typed Δa arg Wb}
      {E' : List Ty} {hs' : [Ty.arrow Wb σb] ++ Δa = E'}
      (hp : Path root (Typed.app Typed.var ha hs'))
      (hsub : Sub d' (Typed.app Typed.var ha hs'))
      (hc : tnet σb ≤ 0) : ChainExit root T
  | killerOther {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Γf : List Ty} {fn : Term} {a b : Ty} (hf : Typed Γf fn (.arrow a b))
      {Γa : List Ty} {arg : Term} (ha : Typed Γa arg a)
      {E : List Ty} (hs : Γf ++ Γa = E)
      (hp : Path root (Typed.app hf ha hs))
      (hrel : SubEq d' (Typed.app hf ha hs)) : ChainExit root T
  | identityLam {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      (hp : Path root d')
      {E' : List Ty} {tp : Term} {τp : Ty} {p : Typed E' tp τp}
      (hsub : Sub d' p) (hE : E' = [])
      (hlam : ∃ (a' : Ty), tp = Term.lam a' (Term.var 0)) : ChainExit root T

/-- THE SPINE EXIT: the chain's appAP config with an app-spine head —
`fn = app g u'` with `g : arrow W (arrow T' σ')`. At each level: an
origin fires at the arg (`tnet W > 0`) or at the fire (`tnet (arrow T'
σ') > 0`); else descend into the spine head. The bottom is a `var`
(spineVar), a `λ` (spineLam — the redex/parasite config, discriminated
by the chase on `W.isLinear`), a constant — IMPOSSIBLE, since the
codomain is arrow-shaped (`gen`/`red`/`obj`/`terminate` have
tensor/atom codomains; the arms auto-drop) — or a transparent
(`lete`/`contr`/`weak`) frame, which exits as `killerOther`. The
codomain is kept as `arrow T' σ'` exactly so the constants are
type-blocked. -/
theorem spine_exit {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γd : List Ty} {td : Term} {τd : Ty} (d : Typed Γd td τd) (T : Ty) :
    ∀ n {Γg : List Ty} {gt : Term} {W T' σ' : Ty}
      (g : Typed Γg gt (.arrow W (.arrow T' σ'))), size g ≤ n →
    ∀ {Γu : List Ty} {u' : Term} (hu' : Typed Γu u' W)
      (E : List Ty) (hs : Γg ++ Γu = E),
    Path root (Typed.app g hu' hs) → Sub d (Typed.app g hu' hs) →
    ∃ (Γd' : List Ty) (td' : Term) (τd' : Ty) (d' : Typed Γd' td' τd'),
      size d' ≤ size d ∧ SubEq d d' ∧ ChainExit root T := by
  intro n Γg gt W T' σ' g hn Γu u' hu' E hs hp hsub
  by_cases hW : tnet W > 0
  · have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
    obtain ⟨hfca, hmca⟩ := Prem_clean (Prem.appAP (hf := g) (ha := hu') (hs := hs)) hfc hmc
    obtain ⟨j, b', hpos, htb, hu⟩ := origin_lemma hu' hfca hmca hW
    obtain ⟨Eβ, tpβ, τpβ, β', hpβ, hint, sβ⟩ :=
      introducer_of_positive hΓ₀ (Path.step hp Prem.appAP) j b' hpos htb
    exact ⟨Γu, u', W, hu',
      (by have h1 := Sub_size (Sub_trans hsub Sub.appRD); omega),
      SubEq.sub (Sub_trans hsub (sub_of_prem Prem.appAP)),
      ChainExit.pos hu' hW hpos htb hu hfca hmca (Path.step hp Prem.appAP)
        SubEq.refl hpβ hint sβ⟩
  · have hW' : tnet W ≤ 0 := by omega
    by_cases hc : tnet (.arrow T' σ') > 0
    · have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
      obtain ⟨j, b', hpos, htb, hu⟩ := origin_lemma (Typed.app g hu' hs) hfc hmc hc
      obtain ⟨Eβ, tpβ, τpβ, β', hpβ, hint, sβ⟩ :=
        introducer_of_positive hΓ₀ hp j b' hpos htb
      exact ⟨E, Term.app gt u', .arrow T' σ', Typed.app g hu' hs,
        (by exact Nat.le_of_lt (Sub_size hsub)),
        SubEq.sub hsub,
        ChainExit.pos (Typed.app g hu' hs) hc hpos htb hu hfc hmc hp
          SubEq.refl hpβ hint sβ⟩
    · have hc' : tnet (.arrow T' σ') ≤ 0 := by omega
      cases g with
      | var =>
          exact ⟨Γd, td, τd, d, Nat.le_refl _, SubEq.refl,
            ChainExit.spineVar d hp hsub hc'⟩
      | lam hb =>
          exact ⟨Γd, td, τd, d, Nat.le_refl _, SubEq.refl,
            ChainExit.spineLam d hp hsub hW' hc'⟩
      | app hg ha hs₁ =>
          rcases spine_exit root hΓ₀ hrf hrm d T n hg
            (by rw [size_app] at hn; omega) ha Γg hs₁
            (Path_append (Typed.app (Typed.app hg ha hs₁) hu' hs) root
              (sub_path (Sub.appLD (hf := Typed.app hg ha hs₁) (ha := hu') (hs := hs))) hp)
            (Sub_trans hsub (Sub.appLD (hf := Typed.app hg ha hs₁) (ha := hu') (hs := hs))) with
            ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
          exact ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
      | lete ht hb hs₁ =>
          exact ⟨_, _, _,
            Typed.app (Typed.lete ht hb hs₁) hu' hs,
            (by exact Nat.le_of_lt (Sub_size hsub)),
            SubEq.sub hsub,
            ChainExit.killerOther (Typed.app (Typed.lete ht hb hs₁) hu' hs)
              (Typed.lete ht hb hs₁) hu' hs hp SubEq.refl⟩
      | fix hΓ h =>
          have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
          obtain ⟨hfcf, hmcf⟩ :=
            Prem_clean (Prem.appFP (hf := Typed.fix hΓ h) (ha := hu') (hs := hs)) hfc hmc
          have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfcf
          omega
      | contr hk h =>
          exact ⟨_, _, _,
            Typed.app (Typed.contr hk h) hu' hs,
            (by exact Nat.le_of_lt (Sub_size hsub)),
            SubEq.sub hsub,
            ChainExit.killerOther (Typed.app (Typed.contr hk h) hu' hs)
              (Typed.contr hk h) hu' hs hp SubEq.refl⟩
      | weak hk h =>
          exact ⟨_, _, _,
            Typed.app (Typed.weak hk h) hu' hs,
            (by exact Nat.le_of_lt (Sub_size hsub)),
            SubEq.sub hsub,
            ChainExit.killerOther (Typed.app (Typed.weak hk h) hu' hs)
              (Typed.weak hk h) hu' hs hp SubEq.refl⟩

/-- THE GENERAL-DOMAIN KILLER-STEP: `killer_step` with the killer's
domain `X` only equationally the class type — the arm's read is in the
raw `Typed Δ arg X` shape, converted via `htv`/`hcΓ` (the landed
`killer_step` is the `X := T` instance). -/
theorem killer_step_gen {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {E Γf Δ : List Ty} {X b σ b' : Ty} {body arg : Term}
    {hb : Typed (X :: Γf) body b'} {ha : Typed Δ arg X} {hs : Γf ++ Δ = E}
    (hp : Path root (Typed.app (Typed.lam hb) ha hs))
    (htv : arg = Term.var 0) (hcΓ : Δ = [X])
    (hX : X = Ty.arrow b σ) (htb : tnet b > 0) :
    Path root hb ∧ fixCount hb = 0 ∧ mintCount hb = 0 ∧
      (X :: Γf)[0]? = some X ∧ uses hb 0 ≥ 1 ∧
      size hb < size (Typed.app (Typed.lam hb) ha hs) := by
  have hblin : b.isLinear = true := by
    rcases Bool.eq_false_or_eq_true b.isLinear with h | h
    · exact h
    · rw [nonlinear_tnet b h] at htb; omega
  have hXlin : X.isLinear = true := by
    rw [hX]; simp only [Ty.isLinear, hblin, Bool.true_or]
  have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
  obtain ⟨hfcf, hmcf⟩ := Prem_clean (Prem.appFP (hf := Typed.lam hb) (ha := ha) (hs := hs)) hfc hmc
  obtain ⟨hfcb, hmcb⟩ := Prem_clean (Prem.lamP (h := hb)) hfcf hmcf
  refine ⟨Path.step (Path.step hp Prem.appFP) Prem.lamP, hfcb, hmcb,
    List.get?_zero_cons', ?_, ?_⟩
  · exact Nat.le_of_eq (Eq.symm (single_linear_use hb 0 X List.get?_zero_cons' hXlin))
  · have h1 : size hb < size (Typed.lam hb) := Prem_size Prem.lamP
    have h2 : size (Typed.lam hb) < size (Typed.app (Typed.lam hb) ha hs) :=
      Prem_size (Prem.appFP (hf := Typed.lam hb) (ha := ha) (hs := hs))
    omega

/-- THE CHAIN'S DIRECT-CONFIG ANALYSIS: the read is a direct premise of
the state `d`. The helper matches the PREMISE (not `d` itself) and the
witnesses are built from the arm's bound data — the rebuilt fires carry
their own `Path` data, so the d-defeq never matters (fp9's verdict
#112: the chain's state IS the rebuilt fire). `hrec` is the
killer-chain's own one-step recursion (the killer-dive continuation). -/
theorem chain_direct {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d) (T : Ty)
    {b σ : Ty} (hT : T = Ty.arrow b σ) (htb : tnet b > 0)
    (hblin : b.isLinear = true) (hTlin : T.isLinear = true)
    (hfc : fixCount d = 0) (hmc : mintCount d = 0)
    (hrec : ∀ {Γ' : List Ty} {t' : Term} {τ' : Ty} {d' : Typed Γ' t' τ'},
      size d' < size d →
      ∀ (hp' : Path root d') (i' : Nat), Γ'[i']? = some T → uses d' i' ≥ 1 →
      ∃ (Γd' : List Ty) (td' : Term) (τd' : Ty) (d'' : Typed Γd' td' τd'),
        size d'' ≤ size d' ∧ SubEq d' d'' ∧ ChainExit root T) :
    ∀ {Γv : List Ty} {tv : Term} {τv : Ty} (v : Typed Γv tv τv), Prem d v →
    tv = Term.var 0 → Γv = [τv] → τv = T →
    ∀ (i : Nat), Γ[i]? = some T → uses d i ≥ 1 →
    ∃ (Γd' : List Ty) (td' : Term) (τd' : Ty) (d' : Typed Γd' td' τd'),
      size d' ≤ size d ∧ SubEq d d' ∧ ChainExit root T := by
  intro Γv tv τv v s htv hcΓv hτv i hpos hu
  match s with
  | @Prem.appFP E' Γf Δ X b' fn arg hf ha hs =>
      have hty : Ty.arrow X b' = Ty.arrow b σ := hτv.trans hT
      injection hty with hX hb'
      have hXb : tnet X > 0 := by rw [hX]; exact htb
      obtain ⟨hfca, hmca⟩ :=
        Prem_clean (Prem.appAP (hf := hf) (ha := ha) (hs := hs)) hfc hmc
      obtain ⟨j, b'', hposj, htb'', huj⟩ := origin_lemma ha hfca hmca hXb
      obtain ⟨Eβ, tpβ, τpβ, β', hpβ, hint, sβ⟩ :=
        introducer_of_positive hΓ₀ (Path.step hp Prem.appAP) j b'' hposj htb''
      exact ⟨Δ, arg, X, ha,
        (by exact Nat.le_of_lt (Prem_size (Prem.appAP (hf := hf) (ha := ha) (hs := hs)))),
        SubEq.sub (sub_of_prem Prem.appAP),
        ChainExit.pos ha hXb hposj htb'' huj hfca hmca
          (Path.step hp Prem.appAP) SubEq.refl hpβ hint sβ⟩
  | @Prem.appAP E' Γf Δ X b' fn arg hf ha hs =>
      cases hf with
      | lam hb =>
          rcases killer_step_gen root hrf hrm (hb := hb) (ha := ha) (hs := hs)
              hp htv hcΓv (hτv.trans hT) htb with
            ⟨hpb, hfcb, hmcb, hposb, hub, hszb⟩
          rcases hrec (by rw [size_app] at hszb ⊢; omega) hpb 0
              (by rw [← hτv]; exact hposb) hub with
            ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
          exact ⟨Γd', td', τd', d', by omega,
            SubEq_trans (SubEq.sub (Sub_trans (sub_of_prem Prem.appFP) (sub_of_prem Prem.lamP)))
              hsub',
            hexit⟩
      | var =>
          by_cases hcb : tnet b' > 0
          · obtain ⟨j, b'', hposj, htb'', huj⟩ :=
              origin_lemma (Typed.app Typed.var ha hs) hfc hmc hcb
            obtain ⟨Eβ, tpβ, τpβ, β', hpβ, hint, sβ⟩ :=
              introducer_of_positive hΓ₀ hp j b'' hposj htb''
            exact ⟨E', Term.app (Term.var 0) arg, b', Typed.app Typed.var ha hs,
              Nat.le_refl _, SubEq.refl,
              ChainExit.pos (d' := Typed.app Typed.var ha hs) (hw := Typed.app Typed.var ha hs)
                hcb hposj htb'' huj hfc hmc hp SubEq.refl hpβ hint sβ⟩
          · exact ⟨E', Term.app (Term.var 0) arg, b', Typed.app Typed.var ha hs,
              Nat.le_refl _, SubEq.refl,
              ChainExit.varFn (d' := Typed.app Typed.var ha hs)
                (v := hτv ▸ (hcΓv ▸ (htv ▸ ha))) (hs := hτv ▸ (hcΓv ▸ hs))
                (hf := hτv ▸ Typed.var) hp (by omega)⟩
      | app hg ha' hs₁ =>
          rcases spine_exit root hΓ₀ hrf hrm (Typed.app (Typed.app hg ha' hs₁) ha hs) T
            (size hg) hg (Nat.le_refl _) ha' Γf hs₁
            (Path_append (Typed.app (Typed.app hg ha' hs₁) ha hs) root
              (sub_path (Sub.appLD (hf := Typed.app hg ha' hs₁) (ha := ha) (hs := hs))) hp)
            (Sub.appLD (hf := Typed.app hg ha' hs₁) (ha := ha) (hs := hs)) with
            ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
          exact ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
      | fix hΓ h =>
          obtain ⟨hfcf, hmcf⟩ :=
            Prem_clean (Prem.appFP (hf := Typed.fix hΓ h) (ha := ha) (hs := hs)) hfc hmc
          have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfcf
          omega
      | gen =>
          cases (hτv.trans hT)
      | red =>
          cases (hτv.trans hT)
      | obj =>
          cases (hτv.trans hT)
      | terminate =>
          cases (hτv.trans hT)
      | lete ht hb hs' =>
          exact ⟨E', _, _, Typed.app (Typed.lete ht hb hs') ha hs,
              Nat.le_refl _, SubEq.refl,
            ChainExit.killerOther (Typed.app (Typed.lete ht hb hs') ha hs)
              (Typed.lete ht hb hs') ha hs hp SubEq.refl⟩
      | contr hk h =>
          exact ⟨E', _, _, Typed.app (Typed.contr hk h) ha hs,
              Nat.le_refl _, SubEq.refl,
            ChainExit.killerOther (Typed.app (Typed.contr hk h) ha hs)
              (Typed.contr hk h) ha hs hp SubEq.refl⟩
      | weak hk h =>
          exact ⟨E', _, _, Typed.app (Typed.weak hk h) ha hs,
              Nat.le_refl _, SubEq.refl,
            ChainExit.killerOther (Typed.app (Typed.weak hk h) ha hs)
              (Typed.weak hk h) ha hs hp SubEq.refl⟩
  | @Prem.pairLP E' Γf Δ x y l r hl hr hs =>
      rcases value_climb root hrf hrm hp with
        ⟨Ec, tc, τc, c, hpc, sc, hcons⟩
      | ⟨Ec, tc, τc, c, Γ₀, t₀, τ₀, n₀, hpc, sc, hcons, hsub⟩
      | hreach
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit.ride1 (Typed.pair hl hr hs) hpc sc hcons⟩
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit.ride2 (Typed.pair hl hr hs) hpc sc hcons hsub⟩
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit.rideReach (Typed.pair hl hr hs) hp hreach (by intro h; cases h)⟩
  | @Prem.pairRP E' Γf Δ x y l r hl hr hs =>
      rcases value_climb root hrf hrm hp with
        ⟨Ec, tc, τc, c, hpc, sc, hcons⟩
      | ⟨Ec, tc, τc, c, Γ₀, t₀, τ₀, n₀, hpc, sc, hcons, hsub⟩
      | hreach
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit.ride1 (Typed.pair hl hr hs) hpc sc hcons⟩
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit.ride2 (Typed.pair hl hr hs) hpc sc hcons hsub⟩
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit.rideReach (Typed.pair hl hr hs) hp hreach (by intro h; cases h)⟩
  | @Prem.leteTP E' Γ₁ Γ₂ x y c' t' body ht hb hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.leteBP E' Γ₁ Γ₂ x y c' t' body ht hb hs =>
      have hlen := congrArg List.length hcΓv
      simp only [List.length_cons, List.length_nil] at hlen
      exact absurd hlen (by omega)
  | @Prem.nextP E' a' t' h =>
      rcases value_climb root hrf hrm hp with
        ⟨Ec, tc, τc, c, hpc, sc, hcons⟩
      | ⟨Ec, tc, τc, c, Γ₀, t₀, τ₀, n₀, hpc, sc, hcons, hsub⟩
      | hreach
      · exact ⟨E', _, _, Typed.next h,
          Nat.le_refl _, SubEq.refl,
          ChainExit.ride1 (Typed.next h) hpc sc hcons⟩
      · exact ⟨E', _, _, Typed.next h,
          Nat.le_refl _, SubEq.refl,
          ChainExit.ride2 (Typed.next h) hpc sc hcons hsub⟩
      · exact ⟨E', _, _, Typed.next h,
          Nat.le_refl _, SubEq.refl,
          ChainExit.rideReach (Typed.next h) hp hreach (by intro h; cases h)⟩
  | @Prem.fixP E' a' body hnl h =>
      have hty : Ty.arrow (Ty.later a') a' = Ty.arrow b σ := hτv.trans hT
      have hcontra : (Ty.arrow (Ty.later a') a').isLinear = false :=
        hnl 0 (Ty.arrow (Ty.later a') a')
          (get?_zero_of_singleton (c := Ty.arrow (Ty.later a') a') hcΓv)
      have htrue : (Ty.arrow (Ty.later a') a').isLinear = true := hty.symm ▸ (hT ▸ hTlin)
      rw [hcontra] at htrue
      cases htrue
  | @Prem.consHP E' Γf Δ hd tl hc ht hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.consTP E' Γf Δ hd tl hc ht hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.snocTP E' Γf Δ t' u' ht hu hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.snocUP E' Γf Δ t' u' ht hu hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.contrP E' k t' τ' hk h =>
      have hlen := congrArg List.length hcΓv
      simp only [List.length_cons, List.length_nil] at hlen
      exact absurd hlen (by omega)
  | @Prem.lamP E' a' b' body h =>
      have hlen := congrArg List.length hcΓv
      simp only [List.length_cons, List.length_nil] at hlen
      have hlen' : E'.length = 0 := by omega
      cases E' with
      | nil =>
          rw [List.get?_nil'] at hpos
          contradiction
      | cons x xs =>
          have hbad : xs.length + 1 = 0 := by
            simp only [List.length_cons] at hlen'
            exact hlen'
          exact absurd hbad (by omega)
  | @Prem.weakP E' k t' τ' hk h =>
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hkT
          have hcontra : T.isLinear = false := by
            rw [hkT] at hk
            exact hk
          rw [hcontra] at hTlin
          cases hTlin
      | succ j =>
          rw [List.get?_succ_cons'] at hpos
          cases j with
          | zero =>
              rcases hrec (by exact Prem_size (Prem.weakP (hk := hk) (h := h)))
                  (Path.step hp (Prem.weakP (hk := hk) (h := h))) 0
                  (hτv ▸ (hcΓv.symm ▸ List.get?_zero_cons'))
                  (by simpa only [uses, if_neg (by decide : ¬ (1 : Nat) = 0)] using hu) with
                ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
              exact ⟨Γd', td', τd', d',
                by have h1 := Prem_size (Prem.weakP (hk := hk) (h := h)); omega,
                SubEq_trans (SubEq.sub (sub_of_prem Prem.weakP)) hsub', hexit⟩
          | succ m =>
              rw [hcΓv, List.get?_succ_cons', List.get?_nil'] at hpos
              contradiction

/-- THE KILLER-CHAIN: the M3-family internal loop at the PC class —
state `(d, i)` with `Γ[i]? = some T`, `T = arrow b σ`, `tnet b > 0`.
The chain descends (type-stable, size strictly dropping) through
killer-of-killer dives (`killer_step`) and transparent frames, and
exits with the `ChainExit` package the macro's round-map dispatches on:
`pos` (an origin fires — the chase resumes at a strictly smaller or
shallower state), the rides, `top` (the node IS the read — the macro
analyzes the parent fire), `varFn` (a var-headed fire whose conclusion
sign is dead — the quartet's var-fn hypothesis), the spine bottoms, the
transparent-killer configs (`killerOther`), or the identity-λ (the
macro's ascent). The exits are consumed as bare ∃-packages (fp9's
#112: the anchor relations are re-derived at S3 from the descent
certificates). -/
theorem killer_chain {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0) :
    ∀ n {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ}, size d ≤ n →
    ∀ (hp : Path root d) (i : Nat) (T : Ty), Γ[i]? = some T → uses d i ≥ 1 →
    ∀ {b σ : Ty}, T = Ty.arrow b σ → tnet b > 0 →
    ∃ (Γd' : List Ty) (td' : Term) (τd' : Ty) (d' : Typed Γd' td' τd'),
      size d' ≤ size d ∧ SubEq d d' ∧ ChainExit root T := by
  intro n
  induction n with
  | zero =>
      intro Γ t τ d hn hp i T hpos hu b σ hT htb
      exact absurd hn (Nat.not_le_of_lt (size_pos d))
  | succ n ih =>
      intro Γ t τ d hn hp i T hpos hu b σ hT htb
      have hblin : b.isLinear = true := by
        rcases Bool.eq_false_or_eq_true b.isLinear with h | h
        · exact h
        · rw [nonlinear_tnet b h] at htb; omega
      have hTlin : T.isLinear = true := by
        rw [hT]; simp only [Ty.isLinear, hblin, Bool.true_or]
      have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
      rcases read_locate (size d) d (Nat.le_refl _) i T hpos hu with
        deep | direct | top
      · obtain ⟨E, tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ := deep
        obtain ⟨a, hcΓ, hcτ⟩ := var_canonical v htv
        have hcΓv : Γv = [τv] := hcτ ▸ hcΓ
        have hp' : Path root p := Path_append d root (sub_path hsub) hp
        rcases prem_position_class hprem htv hcΓv (b := b) (σ := σ) (hτv.trans hT) htb with
          ⟨iₚ, hposₚ, huₚ⟩ | ⟨hE, hlami⟩
        · have hposT : E[iₚ]? = some T := by rw [hτv] at hposₚ; exact hposₚ
          rcases ih (by have hs' := Sub_size hsub; omega) hp' iₚ T hposT huₚ hT htb with
            ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
          exact ⟨Γd', td', τd', d', by have h1 := Sub_size hsub; omega,
            SubEq_trans (SubEq.sub hsub) hsub', hexit⟩
        · exact ⟨Γ, t, τ, d, Nat.le_refl _, SubEq.refl,
            ChainExit.identityLam d hp hsub hE hlami⟩
      · obtain ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ := direct
        obtain ⟨a, hcΓ, hcτ⟩ := var_canonical v htv
        have hcΓv : Γv = [τv] := hcτ ▸ hcΓ
        exact chain_direct root hΓ₀ hrf hrm hp T hT htb hblin hTlin hfc hmc
          (fun {Γ' t' τ'} {d'} hsz hp' i' hpos' hu' =>
            ih (by omega) hp' i' T hpos' hu' hT htb)
          v hprem htv hcΓv hτv i hpos hu
      · obtain ⟨hcΓ, htv, hcτ, hi⟩ := top
        obtain hloc | hroot := parent_locate root hp
        · obtain ⟨Ec, tc, τc, c, hpc, s⟩ := hloc
          have hsubc : Sub c d := sub_of_prem s
          exact ⟨Γ, t, τ, d, Nat.le_refl _, SubEq.refl,
            ChainExit.top d hcΓ htv hcτ c hpc s hsubc⟩
        · obtain ⟨hΓ, ht, hτ⟩ := hroot
          -- the root's context vs the singleton `[T]`: the length
          -- equation forces the supplement empty, then the old
          -- content-vs-arrow kill.
          have hlen : ([Ty.content] ++ Γ₀).length = 1 := by
            rw [← hΓ]; rw [hcΓ]; rfl
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen
          have hΓ₀nil : Γ₀ = [] := by
            cases Γ₀ with
            | nil => rfl
            | cons c cs => simp at hlen
          rw [hΓ₀nil] at hΓ
          rw [hΓ] at hpos
          have hpos' : (Ty.content :: [])[i]? = some T := by simpa using hpos
          cases i with
          | zero =>
              rw [List.get?_zero_cons'] at hpos'
              injection hpos' with hTc
              rw [hT] at hTc
              cases hTc
          | succ m =>
              rw [List.get?_succ_cons', List.get?_nil'] at hpos'
              contradiction

/-!
## THE CHASE PIN (interval 10, restored interval 11; S6-generalized interval 14)

The top-level chase statements, pinned verbatim so every intermediate
lemma (`killer_chain`, the macro, the ride accounting) is typed against
the exact consumer. The assembly `no_vanishing_fixfree_of_chase` at the
top of this file is already WIRED for these shapes — its local
hypotheses `hchaseT`/`hchaseS` are exactly the statements below at
`Γ₀ := []` (the S6 fix-layer frame generalizes the root to
`[content] ++ Γ₀` under an inert supplement; the assembly's `[content]`
shape is the `Γ₀ := []` instance, which is why the conditional passes
`inert_nil`). When proven, the theorems are DECLARED with these exact
statements (names `chase_trace` / `chase_stream`) and instantiate the
assembly with a single `:=`.

```lean
theorem chase_trace {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d)
    (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (htb : tnet b > 0)
    (hu : uses d i ≥ 1) : False

theorem chase_stream {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {d : Typed Γ t (.later Ty.stream)} (hp : Path root d)
    (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (hsb : snet b > 0)
    (hu : uses d i ≥ 1) : False
```

THE FUEL (the induction measure): one Nat encoding the lexicographic
triple LEX(rides, level, size) with GLOBAL bounds — `level := size root −
size β` (β the state's piece introducer, via `introducer_of_positive`;
`corner_level_drop` proves the corner's strict drop), `size := size d`,
and `rides` a strictly decreasing Nat initialized ≤ `size root` (each
ride event decrements it; the bound rides ≤ size root is maintained by
decrease alone — no freshness lemma is needed for the arithmetic). The
encoding: `fuel := rides·(S+1)² + level·(S+1) + size` with
`S = size root`; corner: level ↓ strict at fixed rides; ride: rides ↓
at arbitrary level/size; descent: size ↓ at fixed rides+level.

THE QUARTET — the four configs the round-map cannot price; they ride as
named HYPOTHESES of the chase theorems until the sweep prices them (the
honest conditional layer — visible in the statement, never silent):

1. var-fn: the read is the ARG of a fire whose fn is a var-read, and
   no origin fires (the arg-type is tnet-nonpositive).
2. parasite-spine: a spine config whose spine-head's domain is
   non-linear with `tnet ≤ 0`.
3. BFree-blocked: a linear redex whose chain to the current anchor is
   not `BFree` (the congruence cannot lift it).
4. identity-killer-stuck: the PC-class state at the identity killer
   `λ(T). var 0` with `tnet T ≤ 0` (the dive lands at itself, every
   origin sign is stuck).

The transparent-killer configs (`ChainExit.killerOther`) are NOT a
fifth hypothesis: they are priced INSIDE the macro as a plain descent
(the frame's premise is strictly smaller than the fire, and the position
image rides the same `pos_image` arithmetic as D1's sibling side).

Their exact statement forms are pinned in `killer_chain`'s exit
disjunction (above), which the chase's round-map dispatches on.
-/

/-! ## THE CHASE, TRACE SIDE (interval 13)

The trace-side position-kill: one induction on the fuel encoding
LEX(level, size) — `fuel = level·(S+1) + size` with `S = size root`,
`level := size root − size β` (β the piece's introducer). The priced
moves are the round-map's descent (size ↓ at fixed β) and the corner's
level drop (the corner exit carries the shallower introducer). The
macro's exits ride as NAMED HYPOTHESES — the honest conditional layer:
every config below is a pinned future lemma (the record's quartet
extended with the pos-deeper continuation, the rides, the
top/identity configs, and the transparent/comp entries). When a
hypothesis is priced, the chase's statement shrinks by one argument;
the assembly stays conditional until then. -/

theorem chase_trace {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    (hvarfire : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Δa : List Ty} {Wb σb : Ty} {fn arg : Term}
        {hf : Typed Γf fn (Ty.arrow Wb σb)} {ha : Typed Δa arg Wb} {E' : List Ty}
        {hs : Γf ++ Δa = E'} (htv : fn = Term.var 0),
        Path root d' → False)
    (hspine : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Δa : List Ty} {Wb σb : Ty} {body arg : Term}
        {hb : Typed (Wb :: Γf) body σb} {ha : Typed Δa arg Wb} {E' : List Ty}
        {hs' : Γf ++ Δa = E'}
        (hp : Path root (Typed.app (Typed.lam hb) ha hs'))
        (hsub : Sub d' (Typed.app (Typed.lam hb) ha hs'))
        (hW : tnet Wb ≤ 0) (hc : tnet σb ≤ 0), False)
    (htrans : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Γa : List Ty} {fn : Term} {a b : Ty} (hf : Typed Γf fn (Ty.arrow a b))
        {arg : Term} (ha : Typed Γa arg a) {E : List Ty} (hs : Γf ++ Γa = E)
        (hp : Path root (Typed.app hf ha hs))
        (hrel : SubEq d' (Typed.app hf ha hs)), False)
    (hdeep : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Δ : List Ty} {X : Ty} {w : Term} {hw : Typed Δ w X} {j : Nat} {b' : Ty}
        (hX : tnet X > 0) (hpos : Δ[j]? = some b') (htb : tnet b' > 0) (hu : uses hw j ≥ 1)
        (hfc : fixCount hw = 0) (hmc : mintCount hw = 0) (hpw : Path root hw)
        (hrel : SubEq d' hw)
        {E' : List Ty} {tp : Term} {τp : Ty} {β' : Typed E' tp τp}
        (hpβ : Path root β') (hint : Introduces β' b') (sβ : Sub β' hw)
        {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β₀ : Typed Eβ tβ τβ),
        size β' ≤ size β₀ → False)
    (hride1 : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        (hpc : Path root c) (s : Prem c d') (hcons : ConsumingPrem s), False)
    (hride2 : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
        (hpc : Path root c) (s : Prem c n₀) (hcons : ConsumingPrem s) (hsub : Sub n₀ d'),
        False)
    (htop : ∀ {T : Ty} {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        (hcΓ : Γd = [T]) (htv : td = Term.var 0) (hcτ : τd = T)
        {Ec : List Ty} {tc : Term} {τc : Ty} (c : Typed Ec tc τc)
        (hpc : Path root c) (s : Prem c d') (hsub : Sub c d'), False)
    (hidentity : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        (hp : Path root d')
        {E' : List Ty} {tp : Term} {τp : Ty} {p : Typed E' tp τp}
        (hsub : Sub d' p) (hE : E' = [])
        (hlam : ∃ (a' : Ty), tp = Term.lam a' (Term.var 0)), False)
    (hcomp : ∀ {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
        {b x y : Ty}, Introduces β b → b = y ∨ b = x → False)
    (hspineCase : ∀ {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
        {Eβ : List Ty} {tβ : Term} {τβ : Ty} {β : Typed Eβ tβ τβ}
        {s : Prem c n₀}, Path root c → ConsumingPrem s → Sub n₀ β → False) :
    ∀ (fuel : Nat) {Γ : List Ty} {t : Term} {τ : Ty} (d : Typed Γ t τ) (hp : Path root d)
      (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (htb : tnet b > 0) (hu : uses d i ≥ 1)
      {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
      (hpβ : Path root β) (hint : Introduces β b),
      (size root - size β) * (size root + 1) + size d ≤ fuel → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro Γ t τ d hp i b hpos htb hu Eβ tβ τβ β hpβ hint hbound
      have h1 := size_pos d
      omega
  | succ fuel ih =>
      intro Γ t τ d hp i b hpos htb hu Eβ tβ τβ β hpβ hint hbound
      cases chase_round root hΓ₀ hrf hrm hp i b hpos htb hu β hpβ hint with
      | descent d' hp' i' b' hpos' htb' hu' hsz' hτb =>
          exact ih d' hp' i' b' hpos' htb' hu' β hpβ (hτb ▸ hint) (by omega)
      | corner d' hp' i' b' hpos' htb' hu' hfc' hmc' β' hpβ' hint' hdrop =>
          have hsz' : size d' ≤ size root := path_size root hp'
          have hle' : (size root - size β') + 1 ≤ size root - size β := by omega
          have h1 := Nat.mul_le_mul_right (size root + 1) hle'
          rw [Nat.add_mul] at h1
          simp only [Nat.one_mul] at h1
          exact ih d' hp' i' b' hpos' htb' hu' β' hpβ' hint' (by omega)
      | @macroKiller Γf fn' b'' hf' E'' hs' hpF =>
          -- the killer-of-promise entry: the introducer's value killed as
          -- an ARG at the fire. Case the introducer's kind via a `have`
          -- whose goal carries the type equations (the substitution
          -- drives inside the have, the outer binders survive); the
          -- lete-introducers fire the comp-entry hypothesis.
          have hβlam : ∃ (σβ' : Ty) (body' : Term) (hbβ : Typed (b :: Eβ) body' σβ'),
              tβ = Term.lam b body' ∧ τβ = Ty.arrow b σβ' := by
            cases hint with
            | @lamI σβ' body' _ hbβ => exact ⟨σβ', body', hbβ, rfl, rfl⟩
            | @leteIY Γ₁' Γ₂' x' _ _ s' body' ht' hb' hsβ' =>
                exact False.elim (hcomp (β := Typed.lete ht' hb' hsβ') (x := x')
                  (Introduces.leteIY (ht := ht') (hb := hb') (hs := hsβ')) (Or.inl rfl))
            | @leteIX Γ₁' Γ₂' _ y'' _ s' body' ht' hb' hsβ' =>
                exact False.elim (hcomp (β := Typed.lete ht' hb' hsβ') (y := y'')
                  (Introduces.leteIX (ht := ht') (hb := hb') (hs := hsβ')) (Or.inr rfl))
          obtain ⟨σβ', body', hbβ, htβ, hτβ⟩ := hβlam
          -- the killer's domain = τβ = arrow b σβ' with the piece b the
          -- λ's domain (positivity by the state).
          have hlinb : b.isLinear = true := by
            rcases Bool.eq_false_or_eq_true b.isLinear with h | h
            · exact h
            · rw [nonlinear_tnet b h] at htb; omega
          have hlinτ : τβ.isLinear = true := by
            rw [hτβ]; simp only [Ty.isLinear, hlinb, Bool.true_or]
          cases hf' with
          | lam hb =>
              -- THE DIVE: the killer's body at position 0 : τβ — the
              -- chain at the PC class (the killer's domain IS the
              -- piece's type, positive by the state).
              have hub : uses hb 0 ≥ 1 :=
                Nat.le_of_eq (Eq.symm (single_linear_use hb 0 τβ List.get?_zero_cons' hlinτ))
              rcases killer_chain root hΓ₀ hrf hrm (size hb) (Nat.le_refl _)
                  (Path.step (Path.step hpF Prem.appFP) Prem.lamP) 0 τβ
                  List.get?_zero_cons' hub hτβ htb with
                ⟨Γd', td', τd', d', hsd, hsubE, hexit⟩
              cases hexit with
              | @pos Γd0 td0 τd0 d0 Δ X w hw j b0 hX hpos0 htb0 hu0 hfc0 hmc0
                  hpw hrel E0 tp τp β0' hpβ0 hint0 sβ0 =>
                  by_cases hsh : size β0' > size β
                  · have hszw : size hw ≤ size root := path_size root hpw
                    have hszβ' : size β0' ≤ size root := path_size root hpβ0
                    have hle' : (size root - size β0') + 1 ≤ size root - size β := by omega
                    have h1 := Nat.mul_le_mul_right (size root + 1) hle'
                    rw [Nat.add_mul] at h1
                    simp only [Nat.one_mul] at h1
                    have hb1 : (size root - size β0') * (size root + 1) + size hw ≤ fuel := by
                      calc
                        (size root - size β0') * (size root + 1) + size hw
                            ≤ (size root - size β0') * (size root + 1) + (size root + 1) := by
                              exact Nat.add_le_add_left
                                (Nat.le_trans (path_size root hpw) (Nat.le_succ _)) _
                        _ ≤ (size root - size β) * (size root + 1) := h1
                        _ ≤ fuel := by
                          have hsd := size_pos d
                          have hlt : (size root - size β) * (size root + 1) <
                              (size root - size β) * (size root + 1) + size d := by omega
                          omega
                    exact ih hw hpw j b0 hpos0 htb0 hu0 β0' hpβ0 hint0 hb1
                  · have hle : size β0' ≤ size β := by omega
                    exact hdeep d0 hX hpos0 htb0 hu0 hfc0 hmc0 hpw hrel hpβ0 hint0 sβ0 β hle
              | @ride1 Γd0 td0 τd0 d0 E0 tc0 τc0 c hpc s0 hcons0 =>
                  exact hride1 d0 hpc s0 hcons0
              | @ride2 Γd0 td0 τd0 d0 E0 tc0 τc0 c Γ₀0 t₀0 τ₀0 n₀ hpc s0 hcons0 hsub0 =>
                  exact hride2 d0 hpc s0 hcons0 hsub0
              | @rideReach Γd0 td0 τd0 d0 hp0 hreach0 hne0 =>
                  exact no_root_reach root hrf hrm hreach0 hne0
              | @top Γd0 td0 τd0 d0 hcΓ htv hcτ Ec tc τc c hpc s0 hsub0 =>
                  exact htop d0 hcΓ htv hcτ c hpc s0 hsub0
              | @varFn Γd0 td0 τd0 d0 Γf0 v0 hs0 hf0 hp0 ht0 =>
                  exact hvarfire d0 (Γf := Γf0) (Δa := [τβ]) (Wb := τβ) (σb := τd0)
                    (fn := Term.var 0) (arg := Term.var 0) (hf := hf0) (ha := v0)
                    (E' := Γd0) (hs := hs0) rfl hp0
              | @spineLam Γd0 td0 τd0 d0 Γf0 Δa0 Wb σb body arg hb0 ha0 E0 hs0'
                  hp0 hsub0 hW0 hc0 =>
                  exact hspine d0 hp0 hsub0 hW0 hc0
              | @spineVar Γd0 td0 τd0 d0 Δa0 Wb σb arg ha0 E0 hs0' hp0 hsub0 hc0 =>
                  exact hvarfire (Typed.app Typed.var ha0 hs0') (Γf := [Ty.arrow Wb σb]) (Δa := Δa0)
                    (Wb := Wb) (σb := σb)
                    (fn := Term.var 0) (arg := arg) (hf := Typed.var) (ha := ha0)
                    (E' := E0) (hs := hs0') rfl hp0
              | @killerOther Γd0 td0 τd0 d0 Γf0 fn0 a0 b0' hf0 Γa0 arg0 ha0 E0 hs0
                  hp0 hrel0 =>
                  exact htrans d0 hf0 ha0 hs0 hp0 hrel0
              | @identityLam Γd0 td0 τd0 d0 hp0 E0 tp τp p hsub0 hE0 hlam0 =>
                  exact hidentity d0 hp0 hsub0 hE0 hlam0
          | var =>
              exact hvarfire (Typed.app Typed.var β hs') (Γf := [Ty.arrow τβ b'']) (Δa := Eβ)
                (Wb := τβ) (σb := b'')
                (fn := Term.var 0) (arg := tβ) (hf := Typed.var) (ha := β)
                (E' := E'') (hs := hs') rfl hpF
          | app hg ha₁ hs₁ =>
              rcases spine_exit root hΓ₀ hrf hrm (Typed.app (Typed.app hg ha₁ hs₁) β hs') τβ
                  (size hg) hg (Nat.le_refl _) ha₁ Γf hs₁
                  (Path_append (Typed.app (Typed.app hg ha₁ hs₁) β hs') root
                    (sub_path (Sub.appLD (hf := Typed.app hg ha₁ hs₁) (ha := β) (hs := hs')))
                    hpF)
                  (Sub.appLD (hf := Typed.app hg ha₁ hs₁) (ha := β) (hs := hs')) with
                ⟨Γd', td', τd', d', hsd, hsubE, hexit⟩
              cases hexit with
              | @pos Γd0 td0 τd0 d0 Δ X w hw j b0 hX hpos0 htb0 hu0 hfc0 hmc0
                  hpw hrel E0 tp τp β0' hpβ0 hint0 sβ0 =>
                  by_cases hsh : size β0' > size β
                  · have hszw : size hw ≤ size root := path_size root hpw
                    have hszβ' : size β0' ≤ size root := path_size root hpβ0
                    have hle' : (size root - size β0') + 1 ≤ size root - size β := by omega
                    have h1 := Nat.mul_le_mul_right (size root + 1) hle'
                    rw [Nat.add_mul] at h1
                    simp only [Nat.one_mul] at h1
                    have hb1 : (size root - size β0') * (size root + 1) + size hw ≤ fuel := by
                      calc
                        (size root - size β0') * (size root + 1) + size hw
                            ≤ (size root - size β0') * (size root + 1) + (size root + 1) := by
                              exact Nat.add_le_add_left
                                (Nat.le_trans (path_size root hpw) (Nat.le_succ _)) _
                        _ ≤ (size root - size β) * (size root + 1) := h1
                        _ ≤ fuel := by
                          have hsd := size_pos d
                          have hlt : (size root - size β) * (size root + 1) <
                              (size root - size β) * (size root + 1) + size d := by omega
                          omega
                    exact ih hw hpw j b0 hpos0 htb0 hu0 β0' hpβ0 hint0 hb1
                  · have hle : size β0' ≤ size β := by omega
                    exact hdeep d0 hX hpos0 htb0 hu0 hfc0 hmc0 hpw hrel hpβ0 hint0 sβ0 β hle
              | @ride1 Γd0 td0 τd0 d0 E0 tc0 τc0 c hpc s0 hcons0 =>
                  exact hride1 d0 hpc s0 hcons0
              | @ride2 Γd0 td0 τd0 d0 E0 tc0 τc0 c Γ₀0 t₀0 τ₀0 n₀ hpc s0 hcons0 hsub0 =>
                  exact hride2 d0 hpc s0 hcons0 hsub0
              | @rideReach Γd0 td0 τd0 d0 hp0 hreach0 hne0 =>
                  exact no_root_reach root hrf hrm hreach0 hne0
              | @top Γd0 td0 τd0 d0 hcΓ htv hcτ Ec tc τc c hpc s0 hsub0 =>
                  exact htop d0 hcΓ htv hcτ c hpc s0 hsub0
              | @varFn Γd0 td0 τd0 d0 Γf0 v0 hs0 hf0 hp0 ht0 =>
                  exact hvarfire d0 (Γf := Γf0) (Δa := [τβ]) (Wb := τβ) (σb := τd0)
                    (fn := Term.var 0) (arg := Term.var 0) (hf := hf0) (ha := v0)
                    (E' := Γd0) (hs := hs0) rfl hp0
              | @identityLam Γd0 td0 τd0 d0 hp0 E0 tp τp p hsub0 hE0 hlam0 =>
                  exact hidentity d0 hp0 hsub0 hE0 hlam0
              | @spineLam Γd0 td0 τd0 d0 Γf0 Δa0 Wb σb body arg hb0 ha0 E0 hs0'
                  hp0 hsub0 hW0 hc0 =>
                  exact hspine d0 hp0 hsub0 hW0 hc0
              | @spineVar Γd0 td0 τd0 d0 Δa0 Wb σb arg ha0 E0 hs0' hp0 hsub0 hc0 =>
                  exact hvarfire (Typed.app Typed.var ha0 hs0') (Γf := [Ty.arrow Wb σb]) (Δa := Δa0)
                    (Wb := Wb) (σb := σb)
                    (fn := Term.var 0) (arg := arg) (hf := Typed.var) (ha := ha0)
                    (E' := E0) (hs := hs0') rfl hp0
              | @killerOther Γd0 td0 τd0 d0 Γf0 fn0 a0 b0' hf0 Γa0 arg0 ha0 E0 hs0
                  hp0 hrel0 =>
                  exact htrans d0 hf0 ha0 hs0 hp0 hrel0
          | lete ht hb hs₁ =>
              exact htrans (Typed.app (Typed.lete ht hb hs₁) β hs')
                (Typed.lete ht hb hs₁) β hs' hpF SubEq.refl
          | fix hΓ h =>
              have ⟨hfcF, hmcF⟩ := Path_clean root hpF hrf hrm
              obtain ⟨hfcf, hmcf⟩ :=
                Prem_clean (Prem.appFP (hf := Typed.fix hΓ h) (ha := β) (hs := hs')) hfcF hmcF
              have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfcf
              omega
          | gen =>
              cases hτβ
          | red =>
              cases hτβ
          | obj =>
              cases hτβ
          | terminate =>
              cases hτβ
          | contr hk h =>
              exact htrans (Typed.app (Typed.contr hk h) β hs')
                (Typed.contr hk h) β hs' hpF SubEq.refl
          | weak hk h =>
              exact htrans (Typed.app (Typed.weak hk h) β hs')
                (Typed.weak hk h) β hs' hpF SubEq.refl
      | macroComp x y hxy =>
          exact hcomp β hint hxy
      | macroSpine tc' τc' c t₀' τ₀' n₀ hpc s' hcons' hsub =>
          exact hspineCase hpc hcons' hsub

/-! ## THE CHASE, STREAM SIDE (interval 14)

The stream-side position-kill: `chase_trace`'s round-map at the snet
weight (fp13's obs-166 guidance — the parallel build, the LIVE/DEAD
slot flip). `snet` counts stream-tokens (`tnet stream = 0`, so the
cons-tail premise is invisible to the trace sort and the trace premise
invisible here): `prem_position_s`'s consTP arm is LIVE (the
▷stream-tail read, `snet (later stream) = 1`) while snocTP dies
(`snet trace = 0`) — the exact flip of the trace version. Everything
else is the trace template with tnet → snet, `origin_lemma` →
`snet_origin`, `nonlinear_tnet` → `nonlinear_snet`; the
ride/consuming/corner-geometry machinery is weight-agnostic and
carries over as-is. Of the ten hypotheses eight carry verbatim and two
flip sign conditions (hspine, hdeep). -/

/-- THE GENERAL SNET-ORIGIN: a fix-free derivation with an
snet-positive conclusion SPENDS a stream-carrying position —
`sFlowEq` books the budget, and the only positive mint is the
fixpoint's (`sMint_nonpos`), banned. `stream_origin` is the
▷stream-conclusion instance. -/
theorem snet_origin {Γ : List Ty} {t : Term} {τ : Ty} (h : Typed Γ t τ)
    (hfc : fixCount h = 0) (hpos : 0 < snet τ) :
    ∃ (i : Nat) (b : Ty), Γ[i]? = some b ∧ snet b > 0 ∧ uses h i ≥ 1 := by
  have hsm : sMint h ≤ 0 := sMint_nonpos h hfc
  have he := sFlowEq h
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

/-- The root's snet profile: `[content]` supplies no stream-positive
position. -/
theorem root_content_nonpos_s {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) :
    ∀ (j : Nat) (b : Ty), ([Ty.content] ++ Γ₀)[j]? = some b → snet b ≤ 0 := by
  intro j b hpos
  have hpos' : (Ty.content :: Γ₀)[j]? = some b := by simpa using hpos
  cases j with
  | zero =>
      rw [List.get?_zero_cons'] at hpos'
      injection hpos' with hb
      subst hb
      simp [snet]
  | succ m =>
      rw [List.get?_succ_cons'] at hpos'
      exact (hΓ₀ m b hpos').2

/-- Stream-positive positions need introducers (the snet instance of
`introducer_of_positive`). -/
theorem introducer_of_positive_s {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀)
    {t₀ : Term} {root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit}
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d)
    (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (hsb : snet b > 0) :
    ∃ (E' : List Ty) (tp : Term) (τp : Ty) (β : Typed E' tp τp),
      Path root β ∧ Introduces β b ∧ Sub β d := by
  rcases pos_introduced root hp i b hpos with ⟨j, hj⟩ | hintro
  · exact absurd hsb (by have hle := root_content_nonpos_s hΓ₀ j b hj; omega)
  · exact hintro

/-- The read's position at its parent, at the snet weight — with the
LIVE/DEAD flip: the cons-TAIL premise (`▷stream`, `snet = 1`) is live
here (position `Γ'.length`, the split's right side) while the snoc's
trace premise dies (`snet trace = 0`); content premises die at both
sorts. Every other arm is `prem_position`'s verbatim with the snet
linearity. -/
theorem prem_position_s : ∀ {E : List Ty} {tc : Term} {τc : Ty} {p : Typed E tc τc}
    {Γv : List Ty} {tv : Term} {τv : Ty} {v : Typed Γv tv τv}, Prem p v →
    tv = Term.var 0 → Γv = [τv] → snet τv > 0 →
    (∃ (i : Nat), E[i]? = some τv ∧ uses p i ≥ 1)
    ∨ (E = [] ∧ ∃ (a' : Ty), tc = Term.lam a' (Term.var 0)) := by
  intro E tc τc p Γv tv τv v s htv hΓ hsa
  have hlin : τv.isLinear = true := by
    rcases Bool.eq_false_or_eq_true τv.isLinear with h | h
    · exact h
    · rw [nonlinear_snet τv h] at hsa; omega
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
      have h0 : snet Ty.content = 0 := rfl
      rw [h0] at hsa; omega
  | @Prem.consTP E' Γ' Δ hd tl hc ht hs, _, hΓ' =>
      refine Or.inl ⟨Γ'.length, ?_, ?_⟩
      · rw [← hs, List.get?_append_ge (Nat.le_refl _)]
        rw [hΓ']; simp
      · simp only [uses]
        rw [if_neg (Nat.not_lt.mpr (Nat.le_refl _)), Nat.sub_self]
        exact Nat.le_of_eq (Eq.symm (single_linear_use ht 0 _ (get?_zero_of_singleton hΓ') hlin))
  | @Prem.snocTP E' Γ' Δ t u ht hu hs, _, _ =>
      have h0 : snet Ty.trace = 0 := rfl
      rw [h0] at hsa; omega
  | @Prem.snocUP E' Γ' Δ t u ht hu hs, _, _ =>
      have h0 : snet Ty.content = 0 := rfl
      rw [h0] at hsa; omega
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

/-- THE ROUND, stream side: `chase_step` at the snet weight (the
descent/config/TOP decomposition — `prem_position_s` is the only
substituted engine). -/
theorem chase_step_s {Γ₀ : List Ty} {t₀ : Term} {τ₀ : Ty} (root : Typed Γ₀ t₀ τ₀)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d)
    (hfc : fixCount root = 0) (hmc : mintCount root = 0)
    (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (hsb : snet b > 0) (hu : uses d i ≥ 1) :
    (∃ (Γ' : List Ty) (t' : Term) (τ' : Ty) (d' : Typed Γ' t' τ') (i' : Nat) (b' : Ty)
        (hp' : Path root d'),
        Γ'[i']? = some b' ∧ snet b' > 0 ∧ uses d' i' ≥ 1 ∧
        fixCount d' = 0 ∧ mintCount d' = 0 ∧ size d' < size d ∧ b' = b)
    ∨ (∃ (E : List Ty) (tc : Term) (τc : Ty) (d' : Typed E tc τc) (hp' : Path root d')
        (hle : size d' ≤ size d) (Γv : List Ty) (tv : Term) (τv : Ty) (v : Typed Γv tv τv),
        tv = Term.var 0 ∧ Γv = [τv] ∧ snet τv > 0 ∧ Prem d' v ∧
        ((∃ (i' : Nat), E[i']? = some τv ∧ uses d' i' ≥ 1)
         ∨ (E = [] ∧ ∃ (a' : Ty), tc = Term.lam a' (Term.var 0))))
    ∨ (Γ = [b] ∧ t = Term.var 0 ∧ τ = b ∧ i = 0) := by
  have hclean := Path_clean root hp hfc hmc
  rcases read_locate (size d) d (Nat.le_refl _) i b hpos hu with
    deep | direct | top
  · obtain ⟨E, tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ := deep
    have hsa : snet τv > 0 := by rw [hτv]; exact hsb
    obtain ⟨a, hcΓ, hcτ⟩ := var_canonical v htv
    have hcΓv : Γv = [τv] := hcτ ▸ hcΓ
    have hp' : Path root p := Path_append d root (sub_path hsub) hp
    have hpc := Path_clean root hp' hfc hmc
    rcases prem_position_s (p := p) (v := v) hprem htv hcΓv hsa with
      ⟨iₚ, hposₚ, huₚ⟩ | ⟨hE, hlami⟩
    · refine Or.inl ⟨E, tp, τp, p, iₚ, τv, hp', hposₚ, hsa, huₚ, hpc.1, hpc.2, ?_, hτv⟩
      exact Sub_size hsub
    · refine Or.inr (Or.inl ⟨E, tp, τp, p, hp', Nat.le_of_lt (Sub_size hsub),
        Γv, tv, τv, v, htv, hcΓv, hsa, hprem, Or.inr ⟨hE, hlami⟩⟩)
  · obtain ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ := direct
    have hsa : snet τv > 0 := by rw [hτv]; exact hsb
    obtain ⟨a, hcΓ, hcτ⟩ := var_canonical v htv
    have hcΓv : Γv = [τv] := hcτ ▸ hcΓ
    exact Or.inr (Or.inl ⟨Γ, t, τ, d, hp, Nat.le_refl _, Γv, tv, τv, v, htv, hcΓv, hsa, hprem,
      Or.inl ⟨i, by rw [hτv]; exact hpos, hu⟩⟩)
  · exact Or.inr (Or.inr ‹_›)

/-- THE PIECE-CORNER, stream side: `corner_piece` at the snet weight —
the corner round about the INTRODUCER's value's fate (config-
independent): the piece-corner (origin at the consumer fire's arg +
the specialized walk + the strict level drop — `snet_origin` +
`root_content_nonpos_s` are the only substitutions; `value_climb`,
`consuming_fire`, `corner_introducer`, `corner_level_drop` are
weight-agnostic), the killer-of-promise exit, the lete-introducer
comp-entry, the spine-case, and RootReach. -/
theorem corner_piece_s {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
    (hpβ : Path root β) {b : Ty} (hint : Introduces β b) (hsb : snet b > 0) :
    (∃ (Δ' : List Ty) (arg' : Term) (ha' : Typed Δ' arg' b)
        (j : Nat) (b' : Ty), Δ'[j]? = some b' ∧ snet b' > 0 ∧ uses ha' j ≥ 1 ∧
      fixCount ha' = 0 ∧ mintCount ha' = 0 ∧ Path root ha' ∧
      ∃ (E' : List Ty) (tp : Term) (τp : Ty) (β' : Typed E' tp τp),
        Path root β' ∧ Introduces β' b' ∧
        size root - size β' < size root - size β)
    ∨ (∃ (Γ' : List Ty) (fn' : Term) (b'' : Ty) (hf' : Typed Γ' fn' (Ty.arrow τβ b''))
          (E'' : List Ty) (hs' : Γ' ++ Eβ = E''),
        Path root (Typed.app hf' β hs'))
    ∨ (∃ (x y : Ty), b = y ∨ b = x)
    ∨ (∃ (E' : List Ty) (tc' : Term) (τc' : Ty) (c : Typed E' tc' τc')
          (Γ₀' : List Ty) (t₀' : Term) (τ₀' : Ty) (n₀ : Typed Γ₀' t₀' τ₀')
          (hpc : Path root c) (s' : Prem c n₀),
        ConsumingPrem s' ∧ Sub n₀ β)
    ∨ RootReach root β := by
  rcases value_climb root hrf hrm hpβ with
    ⟨E', tc', τc', c, hpc, s', hcons⟩
  | ⟨E', tc', τc', c, Γ₀', t₀', τ₀', n₀, hpc, s', hcons', hsub⟩
  | hreach
  · rcases consuming_fire root c β hpc s' hcons with
      ⟨Δ', X', b', arg', hτ, ha', hs', hpcw⟩
    | ⟨Γf, b', fn', hf', E2, hs', hpcw⟩
    | ⟨a', b'', hτt⟩
    · cases hint with
      | @lamI σβ' body' _ hb' =>
          cases hτ
          have ⟨hfcw, hmcw⟩ := Path_clean root hpcw hrf hrm
          obtain ⟨hfcw2, hmcw2⟩ := Prem_clean (Prem.appAP (hf := Typed.lam hb') (ha := ha') (hs := hs')) hfcw hmcw
          obtain ⟨j, b, hpos, hsb', hu⟩ := snet_origin ha' hfcw2 hsb
          rcases corner_introducer root hpcw j b hpos with
            ⟨k, hk⟩ | ⟨Eβ0, tp, τp, β', hpβ', hint', sβ'F, sβ'w⟩
          · exact absurd hsb' (by have hle := root_content_nonpos_s hΓ₀ k b hk; omega)
          · refine Or.inl ⟨Δ', arg', ha', j, b, hpos, hsb', hu, hfcw2, hmcw2,
              Path.step hpcw Prem.appAP, Eβ0, tp, τp, β', hpβ', hint', ?_⟩
            · exact corner_level_drop root hpβ' sβ'F
      | @leteIY Γ₁' Γ₂' x' _ _ s' body' ht' hb' hsβ' =>
          exact Or.inr (Or.inr (Or.inl ⟨x', b, Or.inl rfl⟩))
      | @leteIX Γ₁' Γ₂' _ y'' _ s' body' ht' hb' hsβ' =>
          exact Or.inr (Or.inr (Or.inl ⟨b, y'', Or.inr rfl⟩))
    · exact Or.inr (Or.inl ⟨Γf, fn', b', hf', E2, hs', hpcw⟩)
    · cases hint with
      | @lamI σβ' body' _ hb' =>
          cases hτt
      | @leteIY Γ₁' Γ₂' x' _ _ s' body' ht' hb' hsβ' =>
          exact Or.inr (Or.inr (Or.inl ⟨x', b, Or.inl rfl⟩))
      | @leteIX Γ₁' Γ₂' _ y'' _ s' body' ht' hb' hsβ' =>
          exact Or.inr (Or.inr (Or.inl ⟨b, y'', Or.inr rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E', tc', τc', c, Γ₀', t₀', τ₀', n₀, hpc, s', hcons', hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hreach)))

/-- THE CHASE'S ROUND-MOVE PACKAGE, stream side: `ChaseMove` with the
snet sign on the state fields (the macro entries are sign-free). -/
inductive ChaseMove_s {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    {Γ : List Ty} {t : Term} {τ : Ty} (d : Typed Γ t τ)
    {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
    {b : Ty} : Prop where
  | descent {Γ' : List Ty} {t' : Term} {τ' : Ty} (d' : Typed Γ' t' τ')
      (hp' : Path root d') (i' : Nat) (b' : Ty)
      (hpos' : Γ'[i']? = some b') (hsb' : snet b' > 0) (hu' : uses d' i' ≥ 1)
      (hsz' : size d' < size d) (hτb : b' = b) : ChaseMove_s root d β
  | corner {Γ' : List Ty} {t' : Term} {τ' : Ty} (d' : Typed Γ' t' τ')
      (hp' : Path root d') (i' : Nat) (b' : Ty)
      (hpos' : Γ'[i']? = some b') (hsb' : snet b' > 0) (hu' : uses d' i' ≥ 1)
      (hfc' : fixCount d' = 0) (hmc' : mintCount d' = 0)
      {E' : List Ty} {tp : Term} {τp : Ty} (β' : Typed E' tp τp)
      (hpβ' : Path root β') (hint' : Introduces β' b')
      (hdrop : size root - size β' < size root - size β) : ChaseMove_s root d β
  | macroKiller {Γ' : List Ty} (fn' : Term) (b'' : Ty)
      (hf' : Typed Γ' fn' (Ty.arrow τβ b''))
      (E'' : List Ty) (hs' : Γ' ++ Eβ = E'')
      (hpF : Path root (Typed.app hf' β hs')) : ChaseMove_s root d β
  | macroComp (x y : Ty) (hxy : b = y ∨ b = x) : ChaseMove_s root d β
  | macroSpine {E' : List Ty} (tc' : Term) (τc' : Ty) (c : Typed E' tc' τc')
      {Γ₀' : List Ty} (t₀' : Term) (τ₀' : Ty) (n₀ : Typed Γ₀' t₀' τ₀')
      (hpc : Path root c) (s' : Prem c n₀)
      (hcons : ConsumingPrem s') (hsub : Sub n₀ β) : ChaseMove_s root d β

/-- THE CORNER DISPATCH, stream side: `corner_dispatch` at the snet
weight — `corner_piece_s`'s five exits → the move package. -/
theorem corner_dispatch_s {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} (d : Typed Γ t τ)
    {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
    (hpβ : Path root β) {b : Ty} (hint : Introduces β b) (hsb : snet b > 0) :
    ChaseMove_s (b := b) root d β := by
  rcases corner_piece_s root hΓ₀ hrf hrm β hpβ hint hsb with
    ⟨Δ', arg', ha', j, b'', hposj, hsb'', huj, hfcj, hmcj, hpj,
      Eβ0, tp, τp, β', hpβ', hint', hdrop⟩
  | ⟨Γf, fn', b'', hf', E2, hs', hpcw⟩
  | ⟨x, y, hxy⟩
  | ⟨E', tc', τc', c, Γ₀', t₀', τ₀', n₀, hpc, s', hcons', hsub⟩
  | hreach
  · exact ChaseMove_s.corner ha' hpj j b'' hposj hsb'' huj hfcj hmcj β' hpβ' hint' hdrop
  · exact ChaseMove_s.macroKiller fn' b'' hf' E2 hs' hpcw
  · exact ChaseMove_s.macroComp x y hxy
  · exact ChaseMove_s.macroSpine tc' τc' c t₀' τ₀' n₀ hpc s' hcons' hsub
  · cases hint with
    | @lamI σβ body _ hb =>
        exact False.elim (no_root_reach root hrf hrm hreach (by intro h; cases h))
    | @leteIY Γ₁ Γ₂ x y c' s' body' ht hb hs =>
        exact ChaseMove_s.macroComp x b (Or.inl rfl)
    | @leteIX Γ₁ Γ₂ x y c' s' body' ht hb hs =>
        exact ChaseMove_s.macroComp b y (Or.inr rfl)

/-- THE CHASE'S ROUND, stream side: `chase_round` at the snet weight. -/
theorem chase_round_s {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d)
    (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (hsb : snet b > 0) (hu : uses d i ≥ 1)
    {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
    (hpβ : Path root β) (hint : Introduces β b) :
    ChaseMove_s (b := b) root d β := by
  rcases chase_step_s root hp hrf hrm i b hpos hsb hu with
    ⟨Γ', t', τ', d', i', b', hp', hpos', hsb', hu', hfc', hmc', hsz', hτb⟩
  | ⟨E, tc, τc, d', hp', hle, Γv, tv, τv, v, htv, hcΓv, hsa, hprem, hposOr⟩
  | top
  · exact ChaseMove_s.descent d' hp' i' b' hpos' hsb' hu' hsz' hτb
  · exact corner_dispatch_s root hΓ₀ hrf hrm d β hpβ hint hsb
  · exact corner_dispatch_s root hΓ₀ hrf hrm d β hpβ hint hsb

/-- THE CHAIN'S EXIT PACKAGE, stream side: `ChainExit` at the snet
weight — the sign fields flip (`pos`'s `hX`, the spine signs, the
varFn conclusion sign); the ride/top/killerOther/identityLam shapes
are sign-free and carry over verbatim. `T` is the snet PC class type
(`T = arrow b σ`, `snet b > 0`). -/
inductive ChainExit_s {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit) (T : Ty) : Prop where
  | pos {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Δ : List Ty} {X : Ty} {w : Term} {hw : Typed Δ w X} {j : Nat} {b' : Ty}
      (hX : snet X > 0) (hpos : Δ[j]? = some b') (hsb : snet b' > 0) (hu : uses hw j ≥ 1)
      (hfc : fixCount hw = 0) (hmc : mintCount hw = 0) (hpw : Path root hw)
      (hrel : SubEq d' hw)
      {E' : List Ty} {tp : Term} {τp : Ty} {β' : Typed E' tp τp}
      (hpβ : Path root β') (hint : Introduces β' b') (sβ : Sub β' hw) : ChainExit_s root T
  | ride1 {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
      (hpc : Path root c) (s : Prem c d') (hcons : ConsumingPrem s) : ChainExit_s root T
  | ride2 {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
      {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
      (hpc : Path root c) (s : Prem c n₀) (hcons : ConsumingPrem s)
      (hsub : Sub n₀ d') : ChainExit_s root T
  | rideReach {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      (hp : Path root d') (hreach : RootReach root d') (hne : τd ≠ Ty.unit) : ChainExit_s root T
  | top {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      (hcΓ : Γd = [T]) (htv : td = Term.var 0) (hcτ : τd = T)
      {Ec : List Ty} {tc : Term} {τc : Ty} (c : Typed Ec tc τc)
      (hpc : Path root c) (s : Prem c d') (hsub : Sub c d') : ChainExit_s root T
  | varFn {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Γf : List Ty} {v : Typed [T] (Term.var 0) T} {hs : Γf ++ [T] = Γd}
      {hf : Typed Γf (Term.var 0) (Ty.arrow T τd)}
      (hp : Path root d') (ht : snet τd ≤ 0) : ChainExit_s root T
  | spineLam {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Γf : List Ty} {Δa : List Ty} {Wb σb : Ty} {body arg : Term}
      {hb : Typed (Wb :: Γf) body σb} {ha : Typed Δa arg Wb}
      {E' : List Ty} {hs' : Γf ++ Δa = E'}
      (hp : Path root (Typed.app (Typed.lam hb) ha hs'))
      (hsub : Sub d' (Typed.app (Typed.lam hb) ha hs'))
      (hW : snet Wb ≤ 0) (hc : snet σb ≤ 0) : ChainExit_s root T
  | spineVar {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Δa : List Ty} {Wb σb : Ty} {arg : Term} {ha : Typed Δa arg Wb}
      {E' : List Ty} {hs' : [Ty.arrow Wb σb] ++ Δa = E'}
      (hp : Path root (Typed.app Typed.var ha hs'))
      (hsub : Sub d' (Typed.app Typed.var ha hs'))
      (hc : snet σb ≤ 0) : ChainExit_s root T
  | killerOther {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      {Γf : List Ty} {fn : Term} {a b : Ty} (hf : Typed Γf fn (.arrow a b))
      {Γa : List Ty} {arg : Term} (ha : Typed Γa arg a)
      {E : List Ty} (hs : Γf ++ Γa = E)
      (hp : Path root (Typed.app hf ha hs))
      (hrel : SubEq d' (Typed.app hf ha hs)) : ChainExit_s root T
  | identityLam {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
      (hp : Path root d')
      {E' : List Ty} {tp : Term} {τp : Ty} {p : Typed E' tp τp}
      (hsub : Sub d' p) (hE : E' = [])
      (hlam : ∃ (a' : Ty), tp = Term.lam a' (Term.var 0)) : ChainExit_s root T

/-- THE CLASS-FLAVORED `prem_position`, stream side: the position's
type is `arrow b σ` with `snet b > 0` — the linearity from the class's
domain via `nonlinear_snet`. -/
theorem prem_position_class_s : ∀ {E : List Ty} {tc : Term} {τc : Ty} {p : Typed E tc τc}
    {Γv : List Ty} {tv : Term} {τv : Ty} {v : Typed Γv tv τv}, Prem p v →
    tv = Term.var 0 → Γv = [τv] →
    ∀ {b σ : Ty}, τv = Ty.arrow b σ → snet b > 0 →
    (∃ (i : Nat), E[i]? = some τv ∧ uses p i ≥ 1)
    ∨ (E = [] ∧ ∃ (a' : Ty), tc = Term.lam a' (Term.var 0)) := by
  intro E tc τc p Γv tv τv v s htv hΓ
  intro b σ hτv hsb
  have hblin : b.isLinear = true := by
    rcases Bool.eq_false_or_eq_true b.isLinear with h | h
    · exact h
    · rw [nonlinear_snet b h] at hsb; omega
  have hlin : τv.isLinear = true := by
    rw [hτv]; simp only [Ty.isLinear, hblin, Bool.true_or]
  match s, htv, hΓ with
  | @Prem.lamP E' a' b' body h, htv, hΓ' =>
      injection hΓ' with haE hE
      exact Or.inr ⟨hE, ⟨a', by rw [htv, haE]⟩⟩
  | @Prem.appFP E' Γ' Δ X b' fn arg hf ha hs, _, hΓ' =>
      refine Or.inl ⟨0, ?_, ?_⟩
      · rw [← hs, List.get?_append_lt (by rw [hΓ']; simp)]
        rw [hΓ']; exact List.get?_zero_cons'
      · simp only [uses]
        rw [if_pos (by rw [hΓ']; simp : (0 : Nat) < Γ'.length)]
        exact Nat.le_of_eq (Eq.symm (single_linear_use hf 0 _ (get?_zero_of_singleton hΓ') hlin))
  | @Prem.appAP E' Γ' Δ X b' fn arg hf ha hs, _, hΓ' =>
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
      cases hτv
  | @Prem.consTP E' Γ' Δ hd tl hc ht hs, _, _ =>
      cases hτv
  | @Prem.snocTP E' Γ' Δ t u ht hu hs, _, hΓ' =>
      cases hτv
  | @Prem.snocUP E' Γ' Δ t u ht hu hs, _, _ =>
      cases hτv
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

/-- THE GENERAL-DOMAIN KILLER-STEP, stream side: `killer_step_gen` at
the snet weight (the class's domain positivity drives the linearity
via `nonlinear_snet`). -/
theorem killer_step_gen_s {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {E Γf Δ : List Ty} {X b σ b' : Ty} {body arg : Term}
    {hb : Typed (X :: Γf) body b'} {ha : Typed Δ arg X} {hs : Γf ++ Δ = E}
    (hp : Path root (Typed.app (Typed.lam hb) ha hs))
    (htv : arg = Term.var 0) (hcΓ : Δ = [X])
    (hX : X = Ty.arrow b σ) (hsb : snet b > 0) :
    Path root hb ∧ fixCount hb = 0 ∧ mintCount hb = 0 ∧
      (X :: Γf)[0]? = some X ∧ uses hb 0 ≥ 1 ∧
      size hb < size (Typed.app (Typed.lam hb) ha hs) := by
  have hblin : b.isLinear = true := by
    rcases Bool.eq_false_or_eq_true b.isLinear with h | h
    · exact h
    · rw [nonlinear_snet b h] at hsb; omega
  have hXlin : X.isLinear = true := by
    rw [hX]; simp only [Ty.isLinear, hblin, Bool.true_or]
  have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
  obtain ⟨hfcf, hmcf⟩ := Prem_clean (Prem.appFP (hf := Typed.lam hb) (ha := ha) (hs := hs)) hfc hmc
  obtain ⟨hfcb, hmcb⟩ := Prem_clean (Prem.lamP (h := hb)) hfcf hmcf
  refine ⟨Path.step (Path.step hp Prem.appFP) Prem.lamP, hfcb, hmcb,
    List.get?_zero_cons', ?_, ?_⟩
  · exact Nat.le_of_eq (Eq.symm (single_linear_use hb 0 X List.get?_zero_cons' hXlin))
  · have h1 : size hb < size (Typed.lam hb) := Prem_size Prem.lamP
    have h2 : size (Typed.lam hb) < size (Typed.app (Typed.lam hb) ha hs) :=
      Prem_size (Prem.appFP (hf := Typed.lam hb) (ha := ha) (hs := hs))
    omega

/-- THE SPINE EXIT, stream side: `spine_exit` at the snet weight. -/
theorem spine_exit_s {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γd : List Ty} {td : Term} {τd : Ty} (d : Typed Γd td τd) (T : Ty) :
    ∀ n {Γg : List Ty} {gt : Term} {W T' σ' : Ty}
      (g : Typed Γg gt (.arrow W (.arrow T' σ'))), size g ≤ n →
    ∀ {Γu : List Ty} {u' : Term} (hu' : Typed Γu u' W)
      (E : List Ty) (hs : Γg ++ Γu = E),
    Path root (Typed.app g hu' hs) → Sub d (Typed.app g hu' hs) →
    ∃ (Γd' : List Ty) (td' : Term) (τd' : Ty) (d' : Typed Γd' td' τd'),
      size d' ≤ size d ∧ SubEq d d' ∧ ChainExit_s root T := by
  intro n Γg gt W T' σ' g hn Γu u' hu' E hs hp hsub
  by_cases hW : snet W > 0
  · have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
    obtain ⟨hfca, hmca⟩ := Prem_clean (Prem.appAP (hf := g) (ha := hu') (hs := hs)) hfc hmc
    obtain ⟨j, b', hpos, hsb, hu⟩ := snet_origin hu' hfca hW
    obtain ⟨Eβ, tpβ, τpβ, β', hpβ, hint, sβ⟩ :=
      introducer_of_positive_s hΓ₀ (Path.step hp Prem.appAP) j b' hpos hsb
    exact ⟨Γu, u', W, hu',
      (by have h1 := Sub_size (Sub_trans hsub Sub.appRD); omega),
      SubEq.sub (Sub_trans hsub (sub_of_prem Prem.appAP)),
      ChainExit_s.pos hu' hW hpos hsb hu hfca hmca (Path.step hp Prem.appAP)
        SubEq.refl hpβ hint sβ⟩
  · have hW' : snet W ≤ 0 := by omega
    by_cases hc : snet (.arrow T' σ') > 0
    · have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
      obtain ⟨j, b', hpos, hsb, hu⟩ := snet_origin (Typed.app g hu' hs) hfc hc
      obtain ⟨Eβ, tpβ, τpβ, β', hpβ, hint, sβ⟩ :=
        introducer_of_positive_s hΓ₀ hp j b' hpos hsb
      exact ⟨E, Term.app gt u', .arrow T' σ', Typed.app g hu' hs,
        (by exact Nat.le_of_lt (Sub_size hsub)),
        SubEq.sub hsub,
        ChainExit_s.pos (Typed.app g hu' hs) hc hpos hsb hu hfc hmc hp
          SubEq.refl hpβ hint sβ⟩
    · have hc' : snet (.arrow T' σ') ≤ 0 := by omega
      cases g with
      | var =>
          exact ⟨Γd, td, τd, d, Nat.le_refl _, SubEq.refl,
            ChainExit_s.spineVar d hp hsub hc'⟩
      | lam hb =>
          exact ⟨Γd, td, τd, d, Nat.le_refl _, SubEq.refl,
            ChainExit_s.spineLam d hp hsub hW' hc'⟩
      | app hg ha hs₁ =>
          rcases spine_exit_s root hΓ₀ hrf hrm d T n hg
            (by rw [size_app] at hn; omega) ha Γg hs₁
            (Path_append (Typed.app (Typed.app hg ha hs₁) hu' hs) root
              (sub_path (Sub.appLD (hf := Typed.app hg ha hs₁) (ha := hu') (hs := hs))) hp)
            (Sub_trans hsub (Sub.appLD (hf := Typed.app hg ha hs₁) (ha := hu') (hs := hs))) with
            ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
          exact ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
      | lete ht hb hs₁ =>
          exact ⟨_, _, _,
            Typed.app (Typed.lete ht hb hs₁) hu' hs,
            (by exact Nat.le_of_lt (Sub_size hsub)),
            SubEq.sub hsub,
            ChainExit_s.killerOther (Typed.app (Typed.lete ht hb hs₁) hu' hs)
              (Typed.lete ht hb hs₁) hu' hs hp SubEq.refl⟩
      | fix hΓ h =>
          have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
          obtain ⟨hfcf, hmcf⟩ :=
            Prem_clean (Prem.appFP (hf := Typed.fix hΓ h) (ha := hu') (hs := hs)) hfc hmc
          have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfcf
          omega
      | contr hk h =>
          exact ⟨_, _, _,
            Typed.app (Typed.contr hk h) hu' hs,
            (by exact Nat.le_of_lt (Sub_size hsub)),
            SubEq.sub hsub,
            ChainExit_s.killerOther (Typed.app (Typed.contr hk h) hu' hs)
              (Typed.contr hk h) hu' hs hp SubEq.refl⟩
      | weak hk h =>
          exact ⟨_, _, _,
            Typed.app (Typed.weak hk h) hu' hs,
            (by exact Nat.le_of_lt (Sub_size hsub)),
            SubEq.sub hsub,
            ChainExit_s.killerOther (Typed.app (Typed.weak hk h) hu' hs)
              (Typed.weak hk h) hu' hs hp SubEq.refl⟩

/-- THE CHAIN'S DIRECT-CONFIG ANALYSIS, stream side: `chain_direct` at
the snet weight — the helper matches the PREMISE, the witnesses are
built from the arm's data (the rebuilt fires carry their own `Path`). -/
theorem chain_direct_s {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ} (hp : Path root d) (T : Ty)
    {b σ : Ty} (hT : T = Ty.arrow b σ) (hsb : snet b > 0)
    (hblin : b.isLinear = true) (hTlin : T.isLinear = true)
    (hfc : fixCount d = 0) (hmc : mintCount d = 0)
    (hrec : ∀ {Γ' : List Ty} {t' : Term} {τ' : Ty} {d' : Typed Γ' t' τ'},
      size d' < size d →
      ∀ (hp' : Path root d') (i' : Nat), Γ'[i']? = some T → uses d' i' ≥ 1 →
      ∃ (Γd' : List Ty) (td' : Term) (τd' : Ty) (d'' : Typed Γd' td' τd'),
        size d'' ≤ size d' ∧ SubEq d' d'' ∧ ChainExit_s root T) :
    ∀ {Γv : List Ty} {tv : Term} {τv : Ty} (v : Typed Γv tv τv), Prem d v →
    tv = Term.var 0 → Γv = [τv] → τv = T →
    ∀ (i : Nat), Γ[i]? = some T → uses d i ≥ 1 →
    ∃ (Γd' : List Ty) (td' : Term) (τd' : Ty) (d' : Typed Γd' td' τd'),
      size d' ≤ size d ∧ SubEq d d' ∧ ChainExit_s root T := by
  intro Γv tv τv v s htv hcΓv hτv i hpos hu
  match s with
  | @Prem.appFP E' Γf Δ X b' fn arg hf ha hs =>
      have hty : Ty.arrow X b' = Ty.arrow b σ := hτv.trans hT
      injection hty with hX hb'
      have hXb : snet X > 0 := by rw [hX]; exact hsb
      obtain ⟨hfca, hmca⟩ :=
        Prem_clean (Prem.appAP (hf := hf) (ha := ha) (hs := hs)) hfc hmc
      obtain ⟨j, b'', hposj, hsb'', huj⟩ := snet_origin ha hfca hXb
      obtain ⟨Eβ, tpβ, τpβ, β', hpβ, hint, sβ⟩ :=
        introducer_of_positive_s hΓ₀ (Path.step hp Prem.appAP) j b'' hposj hsb''
      exact ⟨Δ, arg, X, ha,
        (by exact Nat.le_of_lt (Prem_size (Prem.appAP (hf := hf) (ha := ha) (hs := hs)))),
        SubEq.sub (sub_of_prem Prem.appAP),
        ChainExit_s.pos ha hXb hposj hsb'' huj hfca hmca
          (Path.step hp Prem.appAP) SubEq.refl hpβ hint sβ⟩
  | @Prem.appAP E' Γf Δ X b' fn arg hf ha hs =>
      cases hf with
      | lam hb =>
          rcases killer_step_gen_s root hrf hrm (hb := hb) (ha := ha) (hs := hs)
              hp htv hcΓv (hτv.trans hT) hsb with
            ⟨hpb, hfcb, hmcb, hposb, hub, hszb⟩
          rcases hrec (by rw [size_app] at hszb ⊢; omega) hpb 0
              (by rw [← hτv]; exact hposb) hub with
            ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
          exact ⟨Γd', td', τd', d', by omega,
            SubEq_trans (SubEq.sub (Sub_trans (sub_of_prem Prem.appFP) (sub_of_prem Prem.lamP)))
              hsub',
            hexit⟩
      | var =>
          by_cases hcb : snet b' > 0
          · obtain ⟨j, b'', hposj, hsb'', huj⟩ :=
              snet_origin (Typed.app Typed.var ha hs) hfc hcb
            obtain ⟨Eβ, tpβ, τpβ, β', hpβ, hint, sβ⟩ :=
              introducer_of_positive_s hΓ₀ hp j b'' hposj hsb''
            exact ⟨E', Term.app (Term.var 0) arg, b', Typed.app Typed.var ha hs,
              Nat.le_refl _, SubEq.refl,
              ChainExit_s.pos (d' := Typed.app Typed.var ha hs) (hw := Typed.app Typed.var ha hs)
                hcb hposj hsb'' huj hfc hmc hp SubEq.refl hpβ hint sβ⟩
          · exact ⟨E', Term.app (Term.var 0) arg, b', Typed.app Typed.var ha hs,
              Nat.le_refl _, SubEq.refl,
              ChainExit_s.varFn (d' := Typed.app Typed.var ha hs)
                (v := hτv ▸ (hcΓv ▸ (htv ▸ ha))) (hs := hτv ▸ (hcΓv ▸ hs))
                (hf := hτv ▸ Typed.var) hp (by omega)⟩
      | app hg ha' hs₁ =>
          rcases spine_exit_s root hΓ₀ hrf hrm (Typed.app (Typed.app hg ha' hs₁) ha hs) T
            (size hg) hg (Nat.le_refl _) ha' Γf hs₁
            (Path_append (Typed.app (Typed.app hg ha' hs₁) ha hs) root
              (sub_path (Sub.appLD (hf := Typed.app hg ha' hs₁) (ha := ha) (hs := hs))) hp)
            (Sub.appLD (hf := Typed.app hg ha' hs₁) (ha := ha) (hs := hs)) with
            ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
          exact ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
      | fix hΓ h =>
          obtain ⟨hfcf, hmcf⟩ :=
            Prem_clean (Prem.appFP (hf := Typed.fix hΓ h) (ha := ha) (hs := hs)) hfc hmc
          have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfcf
          omega
      | gen =>
          cases (hτv.trans hT)
      | red =>
          cases (hτv.trans hT)
      | obj =>
          cases (hτv.trans hT)
      | terminate =>
          cases (hτv.trans hT)
      | lete ht hb hs' =>
          exact ⟨E', _, _, Typed.app (Typed.lete ht hb hs') ha hs,
              Nat.le_refl _, SubEq.refl,
            ChainExit_s.killerOther (Typed.app (Typed.lete ht hb hs') ha hs)
              (Typed.lete ht hb hs') ha hs hp SubEq.refl⟩
      | contr hk h =>
          exact ⟨E', _, _, Typed.app (Typed.contr hk h) ha hs,
              Nat.le_refl _, SubEq.refl,
            ChainExit_s.killerOther (Typed.app (Typed.contr hk h) ha hs)
              (Typed.contr hk h) ha hs hp SubEq.refl⟩
      | weak hk h =>
          exact ⟨E', _, _, Typed.app (Typed.weak hk h) ha hs,
              Nat.le_refl _, SubEq.refl,
            ChainExit_s.killerOther (Typed.app (Typed.weak hk h) ha hs)
              (Typed.weak hk h) ha hs hp SubEq.refl⟩
  | @Prem.pairLP E' Γf Δ x y l r hl hr hs =>
      rcases value_climb root hrf hrm hp with
        ⟨Ec, tc, τc, c, hpc, sc, hcons⟩
      | ⟨Ec, tc, τc, c, Γ₀, t₀, τ₀, n₀, hpc, sc, hcons, hsub⟩
      | hreach
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit_s.ride1 (Typed.pair hl hr hs) hpc sc hcons⟩
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit_s.ride2 (Typed.pair hl hr hs) hpc sc hcons hsub⟩
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit_s.rideReach (Typed.pair hl hr hs) hp hreach (by intro h; cases h)⟩
  | @Prem.pairRP E' Γf Δ x y l r hl hr hs =>
      rcases value_climb root hrf hrm hp with
        ⟨Ec, tc, τc, c, hpc, sc, hcons⟩
      | ⟨Ec, tc, τc, c, Γ₀, t₀, τ₀, n₀, hpc, sc, hcons, hsub⟩
      | hreach
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit_s.ride1 (Typed.pair hl hr hs) hpc sc hcons⟩
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit_s.ride2 (Typed.pair hl hr hs) hpc sc hcons hsub⟩
      · exact ⟨E', _, _, Typed.pair hl hr hs,
          Nat.le_refl _, SubEq.refl,
          ChainExit_s.rideReach (Typed.pair hl hr hs) hp hreach (by intro h; cases h)⟩
  | @Prem.leteTP E' Γ₁ Γ₂ x y c' t' body ht hb hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.leteBP E' Γ₁ Γ₂ x y c' t' body ht hb hs =>
      have hlen := congrArg List.length hcΓv
      simp only [List.length_cons, List.length_nil] at hlen
      exact absurd hlen (by omega)
  | @Prem.nextP E' a' t' h =>
      rcases value_climb root hrf hrm hp with
        ⟨Ec, tc, τc, c, hpc, sc, hcons⟩
      | ⟨Ec, tc, τc, c, Γ₀, t₀, τ₀, n₀, hpc, sc, hcons, hsub⟩
      | hreach
      · exact ⟨E', _, _, Typed.next h,
          Nat.le_refl _, SubEq.refl,
          ChainExit_s.ride1 (Typed.next h) hpc sc hcons⟩
      · exact ⟨E', _, _, Typed.next h,
          Nat.le_refl _, SubEq.refl,
          ChainExit_s.ride2 (Typed.next h) hpc sc hcons hsub⟩
      · exact ⟨E', _, _, Typed.next h,
          Nat.le_refl _, SubEq.refl,
          ChainExit_s.rideReach (Typed.next h) hp hreach (by intro h; cases h)⟩
  | @Prem.fixP E' a' body hnl h =>
      have hty : Ty.arrow (Ty.later a') a' = Ty.arrow b σ := hτv.trans hT
      have hcontra : (Ty.arrow (Ty.later a') a').isLinear = false :=
        hnl 0 (Ty.arrow (Ty.later a') a')
          (get?_zero_of_singleton (c := Ty.arrow (Ty.later a') a') hcΓv)
      have htrue : (Ty.arrow (Ty.later a') a').isLinear = true := hty.symm ▸ (hT ▸ hTlin)
      rw [hcontra] at htrue
      cases htrue
  | @Prem.consHP E' Γf Δ hd tl hc ht hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.consTP E' Γf Δ hd tl hc ht hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.snocTP E' Γf Δ t' u' ht hu hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.snocUP E' Γf Δ t' u' ht hu hs =>
      rw [hT] at hτv
      cases hτv
  | @Prem.contrP E' k t' τ' hk h =>
      have hlen := congrArg List.length hcΓv
      simp only [List.length_cons, List.length_nil] at hlen
      exact absurd hlen (by omega)
  | @Prem.lamP E' a' b' body h =>
      have hlen := congrArg List.length hcΓv
      simp only [List.length_cons, List.length_nil] at hlen
      have hlen' : E'.length = 0 := by omega
      cases E' with
      | nil =>
          rw [List.get?_nil'] at hpos
          contradiction
      | cons x xs =>
          have hbad : xs.length + 1 = 0 := by
            simp only [List.length_cons] at hlen'
            exact hlen'
          exact absurd hbad (by omega)
  | @Prem.weakP E' k t' τ' hk h =>
      cases i with
      | zero =>
          rw [List.get?_zero_cons'] at hpos
          injection hpos with hkT
          have hcontra : T.isLinear = false := by
            rw [hkT] at hk
            exact hk
          rw [hcontra] at hTlin
          cases hTlin
      | succ j =>
          rw [List.get?_succ_cons'] at hpos
          cases j with
          | zero =>
              rcases hrec (by exact Prem_size (Prem.weakP (hk := hk) (h := h)))
                  (Path.step hp (Prem.weakP (hk := hk) (h := h))) 0
                  (hτv ▸ (hcΓv.symm ▸ List.get?_zero_cons'))
                  (by simpa only [uses, if_neg (by decide : ¬ (1 : Nat) = 0)] using hu) with
                ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
              exact ⟨Γd', td', τd', d',
                by have h1 := Prem_size (Prem.weakP (hk := hk) (h := h)); omega,
                SubEq_trans (SubEq.sub (sub_of_prem Prem.weakP)) hsub', hexit⟩
          | succ m =>
              rw [hcΓv, List.get?_succ_cons', List.get?_nil'] at hpos
              contradiction

/-- THE KILLER-CHAIN, stream side: `killer_chain` at the snet PC class
(`T = arrow b σ`, `snet b > 0`) — descends type-stable through
killer-of-killer dives and transparent frames, exits with the
`ChainExit_s` package. -/
theorem killer_chain_s {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0) :
    ∀ n {Γ : List Ty} {t : Term} {τ : Ty} {d : Typed Γ t τ}, size d ≤ n →
    ∀ (hp : Path root d) (i : Nat) (T : Ty), Γ[i]? = some T → uses d i ≥ 1 →
    ∀ {b σ : Ty}, T = Ty.arrow b σ → snet b > 0 →
    ∃ (Γd' : List Ty) (td' : Term) (τd' : Ty) (d' : Typed Γd' td' τd'),
      size d' ≤ size d ∧ SubEq d d' ∧ ChainExit_s root T := by
  intro n
  induction n with
  | zero =>
      intro Γ t τ d hn hp i T hpos hu b σ hT hsb
      exact absurd hn (Nat.not_le_of_lt (size_pos d))
  | succ n ih =>
      intro Γ t τ d hn hp i T hpos hu b σ hT hsb
      have hblin : b.isLinear = true := by
        rcases Bool.eq_false_or_eq_true b.isLinear with h | h
        · exact h
        · rw [nonlinear_snet b h] at hsb; omega
      have hTlin : T.isLinear = true := by
        rw [hT]; simp only [Ty.isLinear, hblin, Bool.true_or]
      have ⟨hfc, hmc⟩ := Path_clean root hp hrf hrm
      rcases read_locate (size d) d (Nat.le_refl _) i T hpos hu with
        deep | direct | top
      · obtain ⟨E, tp, τp, p, hsub, Γv, tv, τv, v, hprem, htv, hτv⟩ := deep
        obtain ⟨a, hcΓ, hcτ⟩ := var_canonical v htv
        have hcΓv : Γv = [τv] := hcτ ▸ hcΓ
        have hp' : Path root p := Path_append d root (sub_path hsub) hp
        rcases prem_position_class_s hprem htv hcΓv (b := b) (σ := σ) (hτv.trans hT) hsb with
          ⟨iₚ, hposₚ, huₚ⟩ | ⟨hE, hlami⟩
        · have hposT : E[iₚ]? = some T := by rw [hτv] at hposₚ; exact hposₚ
          rcases ih (by have hs' := Sub_size hsub; omega) hp' iₚ T hposT huₚ hT hsb with
            ⟨Γd', td', τd', d', hsd, hsub', hexit⟩
          exact ⟨Γd', td', τd', d', by have h1 := Sub_size hsub; omega,
            SubEq_trans (SubEq.sub hsub) hsub', hexit⟩
        · exact ⟨Γ, t, τ, d, Nat.le_refl _, SubEq.refl,
            ChainExit_s.identityLam d hp hsub hE hlami⟩
      · obtain ⟨Γv, tv, τv, v, hprem, htv, hτv⟩ := direct
        obtain ⟨a, hcΓ, hcτ⟩ := var_canonical v htv
        have hcΓv : Γv = [τv] := hcτ ▸ hcΓ
        exact chain_direct_s root hΓ₀ hrf hrm hp T hT hsb hblin hTlin hfc hmc
          (fun {Γ' t' τ'} {d'} hsz hp' i' hpos' hu' =>
            ih (by omega) hp' i' T hpos' hu' hT hsb)
          v hprem htv hcΓv hτv i hpos hu
      · obtain ⟨hcΓ, htv, hcτ, hi⟩ := top
        obtain hloc | hroot := parent_locate root hp
        · obtain ⟨Ec, tc, τc, c, hpc, s⟩ := hloc
          have hsubc : Sub c d := sub_of_prem s
          exact ⟨Γ, t, τ, d, Nat.le_refl _, SubEq.refl,
            ChainExit_s.top d hcΓ htv hcτ c hpc s hsubc⟩
        · obtain ⟨hΓ, ht, hτ⟩ := hroot
          -- the root's context vs the singleton `[T]`: the length
          -- equation forces the supplement empty, then the old
          -- content-vs-arrow kill.
          have hlen : ([Ty.content] ++ Γ₀).length = 1 := by
            rw [← hΓ]; rw [hcΓ]; rfl
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen
          have hΓ₀nil : Γ₀ = [] := by
            cases Γ₀ with
            | nil => rfl
            | cons c cs => simp at hlen
          rw [hΓ₀nil] at hΓ
          rw [hΓ] at hpos
          have hpos' : (Ty.content :: [])[i]? = some T := by simpa using hpos
          cases i with
          | zero =>
              rw [List.get?_zero_cons'] at hpos'
              injection hpos' with hTc
              rw [hT] at hTc
              cases hTc
          | succ m =>
              rw [List.get?_succ_cons', List.get?_nil'] at hpos'
              contradiction

/-- THE STREAM-SIDE POSITION-KILL: `chase_trace` at the snet weight —
descents (size ↓ at fixed β), the corner (level ↓ via the shallower
introducer), the killer-of-promise inline (the have-cased kind → the
dive → `killer_chain_s` → the full `ChainExit_s` dispatch), and the
deaths (fixCount, const-type, rideReach via the `hne` field) — with
the same TEN named hypotheses as the trace side, the two sign-carrying
ones (hspine, hdeep) at the snet weight, the structural eight verbatim
(the honest conditional layer — the macro's fuel question stays a
visible interface). -/
theorem chase_stream {Γ₀ : List Ty} {t₀ : Term}
    (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit)
    (hΓ₀ : Inert Γ₀) (hrf : fixCount root = 0) (hrm : mintCount root = 0)
    (hvarfire : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Δa : List Ty} {Wb σb : Ty} {fn arg : Term}
        {hf : Typed Γf fn (Ty.arrow Wb σb)} {ha : Typed Δa arg Wb} {E' : List Ty}
        {hs : Γf ++ Δa = E'} (htv : fn = Term.var 0),
        Path root d' → False)
    (hspine : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Δa : List Ty} {Wb σb : Ty} {body arg : Term}
        {hb : Typed (Wb :: Γf) body σb} {ha : Typed Δa arg Wb} {E' : List Ty}
        {hs' : Γf ++ Δa = E'}
        (hp : Path root (Typed.app (Typed.lam hb) ha hs'))
        (hsub : Sub d' (Typed.app (Typed.lam hb) ha hs'))
        (hW : snet Wb ≤ 0) (hc : snet σb ≤ 0), False)
    (htrans : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Γa : List Ty} {fn : Term} {a b : Ty} (hf : Typed Γf fn (Ty.arrow a b))
        {arg : Term} (ha : Typed Γa arg a) {E : List Ty} (hs : Γf ++ Γa = E)
        (hp : Path root (Typed.app hf ha hs))
        (hrel : SubEq d' (Typed.app hf ha hs)), False)
    (hdeep : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Δ : List Ty} {X : Ty} {w : Term} {hw : Typed Δ w X} {j : Nat} {b' : Ty}
        (hX : snet X > 0) (hpos : Δ[j]? = some b') (hsb : snet b' > 0) (hu : uses hw j ≥ 1)
        (hfc : fixCount hw = 0) (hmc : mintCount hw = 0) (hpw : Path root hw)
        (hrel : SubEq d' hw)
        {E' : List Ty} {tp : Term} {τp : Ty} {β' : Typed E' tp τp}
        (hpβ : Path root β') (hint : Introduces β' b') (sβ : Sub β' hw)
        {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β₀ : Typed Eβ tβ τβ),
        size β' ≤ size β₀ → False)
    (hride1 : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        (hpc : Path root c) (s : Prem c d') (hcons : ConsumingPrem s), False)
    (hride2 : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
        (hpc : Path root c) (s : Prem c n₀) (hcons : ConsumingPrem s) (hsub : Sub n₀ d'),
        False)
    (htop : ∀ {T : Ty} {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        (hcΓ : Γd = [T]) (htv : td = Term.var 0) (hcτ : τd = T)
        {Ec : List Ty} {tc : Term} {τc : Ty} (c : Typed Ec tc τc)
        (hpc : Path root c) (s : Prem c d') (hsub : Sub c d'), False)
    (hidentity : ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        (hp : Path root d')
        {E' : List Ty} {tp : Term} {τp : Ty} {p : Typed E' tp τp}
        (hsub : Sub d' p) (hE : E' = [])
        (hlam : ∃ (a' : Ty), tp = Term.lam a' (Term.var 0)), False)
    (hcomp : ∀ {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
        {b x y : Ty}, Introduces β b → b = y ∨ b = x → False)
    (hspineCase : ∀ {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
        {Eβ : List Ty} {tβ : Term} {τβ : Ty} {β : Typed Eβ tβ τβ}
        {s : Prem c n₀}, Path root c → ConsumingPrem s → Sub n₀ β → False) :
    ∀ (fuel : Nat) {Γ : List Ty} {t : Term} {τ : Ty} (d : Typed Γ t τ) (hp : Path root d)
      (i : Nat) (b : Ty) (hpos : Γ[i]? = some b) (hsb : snet b > 0) (hu : uses d i ≥ 1)
      {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
      (hpβ : Path root β) (hint : Introduces β b),
      (size root - size β) * (size root + 1) + size d ≤ fuel → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro Γ t τ d hp i b hpos hsb hu Eβ tβ τβ β hpβ hint hbound
      have h1 := size_pos d
      omega
  | succ fuel ih =>
      intro Γ t τ d hp i b hpos hsb hu Eβ tβ τβ β hpβ hint hbound
      cases chase_round_s root hΓ₀ hrf hrm hp i b hpos hsb hu β hpβ hint with
      | descent d' hp' i' b' hpos' hsb' hu' hsz' hτb =>
          exact ih d' hp' i' b' hpos' hsb' hu' β hpβ (hτb ▸ hint) (by omega)
      | corner d' hp' i' b' hpos' hsb' hu' hfc' hmc' β' hpβ' hint' hdrop =>
          have hsz' : size d' ≤ size root := path_size root hp'
          have hle' : (size root - size β') + 1 ≤ size root - size β := by omega
          have h1 := Nat.mul_le_mul_right (size root + 1) hle'
          rw [Nat.add_mul] at h1
          simp only [Nat.one_mul] at h1
          exact ih d' hp' i' b' hpos' hsb' hu' β' hpβ' hint' (by omega)
      | @macroKiller Γf fn' b'' hf' E'' hs' hpF =>
          have hβlam : ∃ (σβ' : Ty) (body' : Term) (hbβ : Typed (b :: Eβ) body' σβ'),
              tβ = Term.lam b body' ∧ τβ = Ty.arrow b σβ' := by
            cases hint with
            | @lamI σβ' body' _ hbβ => exact ⟨σβ', body', hbβ, rfl, rfl⟩
            | @leteIY Γ₁' Γ₂' x' _ _ s' body' ht' hb' hsβ' =>
                exact False.elim (hcomp (β := Typed.lete ht' hb' hsβ') (x := x')
                  (Introduces.leteIY (ht := ht') (hb := hb') (hs := hsβ')) (Or.inl rfl))
            | @leteIX Γ₁' Γ₂' _ y'' _ s' body' ht' hb' hsβ' =>
                exact False.elim (hcomp (β := Typed.lete ht' hb' hsβ') (y := y'')
                  (Introduces.leteIX (ht := ht') (hb := hb') (hs := hsβ')) (Or.inr rfl))
          obtain ⟨σβ', body', hbβ, htβ, hτβ⟩ := hβlam
          have hlinb : b.isLinear = true := by
            rcases Bool.eq_false_or_eq_true b.isLinear with h | h
            · exact h
            · rw [nonlinear_snet b h] at hsb; omega
          have hlinτ : τβ.isLinear = true := by
            rw [hτβ]; simp only [Ty.isLinear, hlinb, Bool.true_or]
          cases hf' with
          | lam hb =>
              have hub : uses hb 0 ≥ 1 :=
                Nat.le_of_eq (Eq.symm (single_linear_use hb 0 τβ List.get?_zero_cons' hlinτ))
              rcases killer_chain_s root hΓ₀ hrf hrm (size hb) (Nat.le_refl _)
                  (Path.step (Path.step hpF Prem.appFP) Prem.lamP) 0 τβ
                  List.get?_zero_cons' hub hτβ hsb with
                ⟨Γd', td', τd', d', hsd, hsubE, hexit⟩
              cases hexit with
              | @pos Γd0 td0 τd0 d0 Δ X w hw j b0 hX hpos0 hsb0 hu0 hfc0 hmc0
                  hpw hrel E0 tp τp β0' hpβ0 hint0 sβ0 =>
                  by_cases hsh : size β0' > size β
                  · have hszw : size hw ≤ size root := path_size root hpw
                    have hszβ' : size β0' ≤ size root := path_size root hpβ0
                    have hle' : (size root - size β0') + 1 ≤ size root - size β := by omega
                    have h1 := Nat.mul_le_mul_right (size root + 1) hle'
                    rw [Nat.add_mul] at h1
                    simp only [Nat.one_mul] at h1
                    have hb1 : (size root - size β0') * (size root + 1) + size hw ≤ fuel := by
                      calc
                        (size root - size β0') * (size root + 1) + size hw
                            ≤ (size root - size β0') * (size root + 1) + (size root + 1) := by
                              exact Nat.add_le_add_left
                                (Nat.le_trans (path_size root hpw) (Nat.le_succ _)) _
                        _ ≤ (size root - size β) * (size root + 1) := h1
                        _ ≤ fuel := by
                          have hsd := size_pos d
                          have hlt : (size root - size β) * (size root + 1) <
                              (size root - size β) * (size root + 1) + size d := by omega
                          omega
                    exact ih hw hpw j b0 hpos0 hsb0 hu0 β0' hpβ0 hint0 hb1
                  · have hle : size β0' ≤ size β := by omega
                    exact hdeep d0 hX hpos0 hsb0 hu0 hfc0 hmc0 hpw hrel hpβ0 hint0 sβ0 β hle
              | @ride1 Γd0 td0 τd0 d0 E0 tc0 τc0 c hpc s0 hcons0 =>
                  exact hride1 d0 hpc s0 hcons0
              | @ride2 Γd0 td0 τd0 d0 E0 tc0 τc0 c Γ₀0 t₀0 τ₀0 n₀ hpc s0 hcons0 hsub0 =>
                  exact hride2 d0 hpc s0 hcons0 hsub0
              | @rideReach Γd0 td0 τd0 d0 hp0 hreach0 hne0 =>
                  exact no_root_reach root hrf hrm hreach0 hne0
              | @top Γd0 td0 τd0 d0 hcΓ htv hcτ Ec tc τc c hpc s0 hsub0 =>
                  exact htop d0 hcΓ htv hcτ c hpc s0 hsub0
              | @varFn Γd0 td0 τd0 d0 Γf0 v0 hs0 hf0 hp0 ht0 =>
                  exact hvarfire d0 (Γf := Γf0) (Δa := [τβ]) (Wb := τβ) (σb := τd0)
                    (fn := Term.var 0) (arg := Term.var 0) (hf := hf0) (ha := v0)
                    (E' := Γd0) (hs := hs0) rfl hp0
              | @spineLam Γd0 td0 τd0 d0 Γf0 Δa0 Wb σb body arg hb0 ha0 E0 hs0'
                  hp0 hsub0 hW0 hc0 =>
                  exact hspine d0 hp0 hsub0 hW0 hc0
              | @spineVar Γd0 td0 τd0 d0 Δa0 Wb σb arg ha0 E0 hs0' hp0 hsub0 hc0 =>
                  exact hvarfire (Typed.app Typed.var ha0 hs0') (Γf := [Ty.arrow Wb σb]) (Δa := Δa0)
                    (Wb := Wb) (σb := σb)
                    (fn := Term.var 0) (arg := arg) (hf := Typed.var) (ha := ha0)
                    (E' := E0) (hs := hs0') rfl hp0
              | @killerOther Γd0 td0 τd0 d0 Γf0 fn0 a0 b0' hf0 Γa0 arg0 ha0 E0 hs0
                  hp0 hrel0 =>
                  exact htrans d0 hf0 ha0 hs0 hp0 hrel0
              | @identityLam Γd0 td0 τd0 d0 hp0 E0 tp τp p hsub0 hE0 hlam0 =>
                  exact hidentity d0 hp0 hsub0 hE0 hlam0
          | var =>
              exact hvarfire (Typed.app Typed.var β hs') (Γf := [Ty.arrow τβ b'']) (Δa := Eβ)
                (Wb := τβ) (σb := b'')
                (fn := Term.var 0) (arg := tβ) (hf := Typed.var) (ha := β)
                (E' := E'') (hs := hs') rfl hpF
          | app hg ha₁ hs₁ =>
              rcases spine_exit_s root hΓ₀ hrf hrm (Typed.app (Typed.app hg ha₁ hs₁) β hs') τβ
                  (size hg) hg (Nat.le_refl _) ha₁ Γf hs₁
                  (Path_append (Typed.app (Typed.app hg ha₁ hs₁) β hs') root
                    (sub_path (Sub.appLD (hf := Typed.app hg ha₁ hs₁) (ha := β) (hs := hs')))
                    hpF)
                  (Sub.appLD (hf := Typed.app hg ha₁ hs₁) (ha := β) (hs := hs')) with
                ⟨Γd', td', τd', d', hsd, hsubE, hexit⟩
              cases hexit with
              | @pos Γd0 td0 τd0 d0 Δ X w hw j b0 hX hpos0 hsb0 hu0 hfc0 hmc0
                  hpw hrel E0 tp τp β0' hpβ0 hint0 sβ0 =>
                  by_cases hsh : size β0' > size β
                  · have hszw : size hw ≤ size root := path_size root hpw
                    have hszβ' : size β0' ≤ size root := path_size root hpβ0
                    have hle' : (size root - size β0') + 1 ≤ size root - size β := by omega
                    have h1 := Nat.mul_le_mul_right (size root + 1) hle'
                    rw [Nat.add_mul] at h1
                    simp only [Nat.one_mul] at h1
                    have hb1 : (size root - size β0') * (size root + 1) + size hw ≤ fuel := by
                      calc
                        (size root - size β0') * (size root + 1) + size hw
                            ≤ (size root - size β0') * (size root + 1) + (size root + 1) := by
                              exact Nat.add_le_add_left
                                (Nat.le_trans (path_size root hpw) (Nat.le_succ _)) _
                        _ ≤ (size root - size β) * (size root + 1) := h1
                        _ ≤ fuel := by
                          have hsd := size_pos d
                          have hlt : (size root - size β) * (size root + 1) <
                              (size root - size β) * (size root + 1) + size d := by omega
                          omega
                    exact ih hw hpw j b0 hpos0 hsb0 hu0 β0' hpβ0 hint0 hb1
                  · have hle : size β0' ≤ size β := by omega
                    exact hdeep d0 hX hpos0 hsb0 hu0 hfc0 hmc0 hpw hrel hpβ0 hint0 sβ0 β hle
              | @ride1 Γd0 td0 τd0 d0 E0 tc0 τc0 c hpc s0 hcons0 =>
                  exact hride1 d0 hpc s0 hcons0
              | @ride2 Γd0 td0 τd0 d0 E0 tc0 τc0 c Γ₀0 t₀0 τ₀0 n₀ hpc s0 hcons0 hsub0 =>
                  exact hride2 d0 hpc s0 hcons0 hsub0
              | @rideReach Γd0 td0 τd0 d0 hp0 hreach0 hne0 =>
                  exact no_root_reach root hrf hrm hreach0 hne0
              | @top Γd0 td0 τd0 d0 hcΓ htv hcτ Ec tc τc c hpc s0 hsub0 =>
                  exact htop d0 hcΓ htv hcτ c hpc s0 hsub0
              | @varFn Γd0 td0 τd0 d0 Γf0 v0 hs0 hf0 hp0 ht0 =>
                  exact hvarfire d0 (Γf := Γf0) (Δa := [τβ]) (Wb := τβ) (σb := τd0)
                    (fn := Term.var 0) (arg := Term.var 0) (hf := hf0) (ha := v0)
                    (E' := Γd0) (hs := hs0) rfl hp0
              | @identityLam Γd0 td0 τd0 d0 hp0 E0 tp τp p hsub0 hE0 hlam0 =>
                  exact hidentity d0 hp0 hsub0 hE0 hlam0
              | @spineLam Γd0 td0 τd0 d0 Γf0 Δa0 Wb σb body arg hb0 ha0 E0 hs0'
                  hp0 hsub0 hW0 hc0 =>
                  exact hspine d0 hp0 hsub0 hW0 hc0
              | @spineVar Γd0 td0 τd0 d0 Δa0 Wb σb arg ha0 E0 hs0' hp0 hsub0 hc0 =>
                  exact hvarfire (Typed.app Typed.var ha0 hs0') (Γf := [Ty.arrow Wb σb]) (Δa := Δa0)
                    (Wb := Wb) (σb := σb)
                    (fn := Term.var 0) (arg := arg) (hf := Typed.var) (ha := ha0)
                    (E' := E0) (hs := hs0') rfl hp0
              | @killerOther Γd0 td0 τd0 d0 Γf0 fn0 a0 b0' hf0 Γa0 arg0 ha0 E0 hs0
                  hp0 hrel0 =>
                  exact htrans d0 hf0 ha0 hs0 hp0 hrel0
          | lete ht hb hs₁ =>
              exact htrans (Typed.app (Typed.lete ht hb hs₁) β hs')
                (Typed.lete ht hb hs₁) β hs' hpF SubEq.refl
          | fix hΓ h =>
              have ⟨hfcF, hmcF⟩ := Path_clean root hpF hrf hrm
              obtain ⟨hfcf, hmcf⟩ :=
                Prem_clean (Prem.appFP (hf := Typed.fix hΓ h) (ha := β) (hs := hs')) hfcF hmcF
              have hff : 1 + fixCount h = 0 := by simpa only [fixCount] using hfcf
              omega
          | gen =>
              cases hτβ
          | red =>
              cases hτβ
          | obj =>
              cases hτβ
          | terminate =>
              cases hτβ
          | contr hk h =>
              exact htrans (Typed.app (Typed.contr hk h) β hs')
                (Typed.contr hk h) β hs' hpF SubEq.refl
          | weak hk h =>
              exact htrans (Typed.app (Typed.weak hk h) β hs')
                (Typed.weak hk h) β hs' hpF SubEq.refl
      | macroComp x y hxy =>
          exact hcomp β hint hxy
      | macroSpine tc' τc' c t₀' τ₀' n₀ hpc s' hcons' hsub =>
          exact hspineCase hpc hcons' hsub

/-- THE FIXFREE MILESTONE, CONDITIONAL (fp13's obs-166 name): both
chases plugged into the assembly — `[content] ⊢ unit` is impossible in
fix-free trees under the hypothesis layer. Each chase's ten hypotheses
are taken as separate arguments (the trace set at the tnet signs, the
stream set at the snet signs — each hypothesis is consumed exactly
once, which keeps the implicit binders elaboration-clean at both call
sites). The bare `no_vanishing_fixfree` stays reserved for the
UNRESTRICTED fixfree theorem when the hypotheses price out; this form
is the honest conditional layer, visible in the statement. -/
theorem no_vanishing_fixfree_conditional
    (hvarfireT : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Δa : List Ty} {Wb σb : Ty} {fn arg : Term}
        {hf : Typed Γf fn (Ty.arrow Wb σb)} {ha : Typed Δa arg Wb} {E' : List Ty}
        {hs : Γf ++ Δa = E'} (htv : fn = Term.var 0),
        Path root d' → False)
    (hspineT : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Δa : List Ty} {Wb σb : Ty} {body arg : Term}
        {hb : Typed (Wb :: Γf) body σb} {ha : Typed Δa arg Wb} {E' : List Ty}
        {hs' : Γf ++ Δa = E'}
        (hp : Path root (Typed.app (Typed.lam hb) ha hs'))
        (hsub : Sub d' (Typed.app (Typed.lam hb) ha hs'))
        (hW : tnet Wb ≤ 0) (hc : tnet σb ≤ 0), False)
    (htransT : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Γa : List Ty} {fn : Term} {a b : Ty} (hf : Typed Γf fn (Ty.arrow a b))
        {arg : Term} (ha : Typed Γa arg a) {E : List Ty} (hs : Γf ++ Γa = E)
        (hp : Path root (Typed.app hf ha hs))
        (hrel : SubEq d' (Typed.app hf ha hs)), False)
    (hdeepT : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Δ : List Ty} {X : Ty} {w : Term} {hw : Typed Δ w X} {j : Nat} {b' : Ty}
        (hX : tnet X > 0) (hpos : Δ[j]? = some b') (htb : tnet b' > 0) (hu : uses hw j ≥ 1)
        (hfc : fixCount hw = 0) (hmc : mintCount hw = 0) (hpw : Path root hw)
        (hrel : SubEq d' hw)
        {E' : List Ty} {tp : Term} {τp : Ty} {β' : Typed E' tp τp}
        (hpβ : Path root β') (hint : Introduces β' b') (sβ : Sub β' hw)
        {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β₀ : Typed Eβ tβ τβ),
        size β' ≤ size β₀ → False)
    (hride1T : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        (hpc : Path root c) (s : Prem c d') (hcons : ConsumingPrem s), False)
    (hride2T : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
        (hpc : Path root c) (s : Prem c n₀) (hcons : ConsumingPrem s) (hsub : Sub n₀ d'),
        False)
    (htopT : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {T : Ty} {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        (hcΓ : Γd = [T]) (htv : td = Term.var 0) (hcτ : τd = T)
        {Ec : List Ty} {tc : Term} {τc : Ty} (c : Typed Ec tc τc)
        (hpc : Path root c) (s : Prem c d') (hsub : Sub c d'), False)
    (hidentityT : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        (hp : Path root d')
        {E' : List Ty} {tp : Term} {τp : Ty} {p : Typed E' tp τp}
        (hsub : Sub d' p) (hE : E' = [])
        (hlam : ∃ (a' : Ty), tp = Term.lam a' (Term.var 0)), False)
    (hcompT : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
        {b x y : Ty}, Introduces β b → b = y ∨ b = x → False)
    (hspineCaseT : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
        {Eβ : List Ty} {tβ : Term} {τβ : Ty} {β : Typed Eβ tβ τβ}
        {s : Prem c n₀}, Path root c → ConsumingPrem s → Sub n₀ β → False)
    (hvarfireS : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Δa : List Ty} {Wb σb : Ty} {fn arg : Term}
        {hf : Typed Γf fn (Ty.arrow Wb σb)} {ha : Typed Δa arg Wb} {E' : List Ty}
        {hs : Γf ++ Δa = E'} (htv : fn = Term.var 0),
        Path root d' → False)
    (hspineS : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Δa : List Ty} {Wb σb : Ty} {body arg : Term}
        {hb : Typed (Wb :: Γf) body σb} {ha : Typed Δa arg Wb} {E' : List Ty}
        {hs' : Γf ++ Δa = E'}
        (hp : Path root (Typed.app (Typed.lam hb) ha hs'))
        (hsub : Sub d' (Typed.app (Typed.lam hb) ha hs'))
        (hW : snet Wb ≤ 0) (hc : snet σb ≤ 0), False)
    (htransS : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Γf Γa : List Ty} {fn : Term} {a b : Ty} (hf : Typed Γf fn (Ty.arrow a b))
        {arg : Term} (ha : Typed Γa arg a) {E : List Ty} (hs : Γf ++ Γa = E)
        (hp : Path root (Typed.app hf ha hs))
        (hrel : SubEq d' (Typed.app hf ha hs)), False)
    (hdeepS : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {Δ : List Ty} {X : Ty} {w : Term} {hw : Typed Δ w X} {j : Nat} {b' : Ty}
        (hX : snet X > 0) (hpos : Δ[j]? = some b') (hsb : snet b' > 0) (hu : uses hw j ≥ 1)
        (hfc : fixCount hw = 0) (hmc : mintCount hw = 0) (hpw : Path root hw)
        (hrel : SubEq d' hw)
        {E' : List Ty} {tp : Term} {τp : Ty} {β' : Typed E' tp τp}
        (hpβ : Path root β') (hint : Introduces β' b') (sβ : Sub β' hw)
        {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β₀ : Typed Eβ tβ τβ),
        size β' ≤ size β₀ → False)
    (hride1S : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        (hpc : Path root c) (s : Prem c d') (hcons : ConsumingPrem s), False)
    (hride2S : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
        (hpc : Path root c) (s : Prem c n₀) (hcons : ConsumingPrem s) (hsub : Sub n₀ d'),
        False)
    (htopS : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {T : Ty} {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        (hcΓ : Γd = [T]) (htv : td = Term.var 0) (hcτ : τd = T)
        {Ec : List Ty} {tc : Term} {τc : Ty} (c : Typed Ec tc τc)
        (hpc : Path root c) (s : Prem c d') (hsub : Sub c d'), False)
    (hidentityS : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Γd : List Ty} {td : Term} {τd : Ty} (d' : Typed Γd td τd)
        (hp : Path root d')
        {E' : List Ty} {tp : Term} {τp : Ty} {p : Typed E' tp τp}
        (hsub : Sub d' p) (hE : E' = [])
        (hlam : ∃ (a' : Ty), tp = Term.lam a' (Term.var 0)), False)
    (hcompS : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
        {b x y : Ty}, Introduces β b → b = y ∨ b = x → False)
    (hspineCaseS : ∀ {Γ₀ : List Ty} (hΓ₀ : Inert Γ₀) {t₀ : Term}
      (root : Typed ([Ty.content] ++ Γ₀) t₀ Ty.unit),
      fixCount root = 0 → mintCount root = 0 →
      ∀ {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
        {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
        {Eβ : List Ty} {tβ : Term} {τβ : Ty} {β : Typed Eβ tβ τβ}
        {s : Prem c n₀}, Path root c → ConsumingPrem s → Sub n₀ β → False) :
    ∀ (t : Term) (h : Typed [Ty.content] t Ty.unit), fixCount h = 0 → False :=
  no_vanishing_fixfree_of_chase
    (fun root hrf hrm Γ t τ d hp i b hpos htb hu =>
      let ⟨Eβ, tβ, τβ, β, hpβ, hint, sβ⟩ :=
        introducer_of_positive (hΓ₀ := inert_nil) (root := root) hp i b hpos htb
      chase_trace root inert_nil hrf hrm
        (hvarfireT inert_nil root hrf hrm) (hspineT inert_nil root hrf hrm)
        (htransT inert_nil root hrf hrm)
        (hdeepT inert_nil root hrf hrm) (hride1T inert_nil root hrf hrm)
        (hride2T inert_nil root hrf hrm)
        (htopT inert_nil root hrf hrm) (hidentityT inert_nil root hrf hrm)
        (fun {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
            {b : Ty} {x : Ty} {y : Ty} hintro hxy => hcompT inert_nil root hrf hrm (β := β) hintro hxy)
        (fun {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
            {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
            {Eβ : List Ty} {tβ : Term} {τβ : Ty} {β : Typed Eβ tβ τβ}
            {s : Prem c n₀} hpc hcons hsub =>
          hspineCaseT inert_nil root hrf hrm (E' := E') (tc' := tc') (τc' := τc') (c := c)
            (Γ₀' := Γ₀') (t₀' := t₀') (τ₀' := τ₀') (n₀ := n₀) (Eβ := Eβ) (tβ := tβ)
            (τβ := τβ) (β := β) (s := s) hpc hcons hsub)
        ((size root - size β) * (size root + 1) + size d) d hp i b hpos htb hu β hpβ hint
        (Nat.le_refl _))
    (fun root hrf hrm Γ t d hp i b hpos hsb hu =>
      let ⟨Eβ, tβ, τβ, β, hpβ, hint, sβ⟩ :=
        introducer_of_positive_s (hΓ₀ := inert_nil) (root := root) hp i b hpos hsb
      chase_stream root inert_nil hrf hrm
        (hvarfireS inert_nil root hrf hrm) (hspineS inert_nil root hrf hrm)
        (htransS inert_nil root hrf hrm)
        (hdeepS inert_nil root hrf hrm) (hride1S inert_nil root hrf hrm)
        (hride2S inert_nil root hrf hrm)
        (htopS inert_nil root hrf hrm) (hidentityS inert_nil root hrf hrm)
        (fun {Eβ : List Ty} {tβ : Term} {τβ : Ty} (β : Typed Eβ tβ τβ)
            {b : Ty} {x : Ty} {y : Ty} hintro hxy => hcompS inert_nil root hrf hrm (β := β) hintro hxy)
        (fun {E' : List Ty} {tc' : Term} {τc' : Ty} {c : Typed E' tc' τc'}
            {Γ₀' : List Ty} {t₀' : Term} {τ₀' : Ty} {n₀ : Typed Γ₀' t₀' τ₀'}
            {Eβ : List Ty} {tβ : Term} {τβ : Ty} {β : Typed Eβ tβ τβ}
            {s : Prem c n₀} hpc hcons hsub =>
          hspineCaseS inert_nil root hrf hrm (E' := E') (tc' := tc') (τc' := τc') (c := c)
            (Γ₀' := Γ₀') (t₀' := t₀') (τ₀' := τ₀') (n₀ := n₀) (Eβ := Eβ) (tβ := tβ)
            (τβ := τβ) (β := β) (s := s) hpc hcons hsub)
        ((size root - size β) * (size root + 1) + size d) d hp i b hpos hsb hu β hpβ hint
        (Nat.le_refl _))

/-! ## The march — the content-token walk (obs 172)

The unrestricted `no_vanishing` at the conditional level. The token
(`content`) is invisible to both conservation weights (`tnet content = 0`,
`snet content = 0`), so the unrestricted theorem is the token's own
death-walk — pure structure, no front door. The frame is MID-TOKEN
(`ΓL ++ [content] ++ ΓR`) with the supplements DISCIPLINED: every
position `MarchOK` (DomOK ∧ tnet ≤ 0 ∧ snet ≤ 0). The probe
`[ACU, content] ⊢ app (var 0) (var 0) : unit` violates the discipline —
which is exactly why a disciplined supplement cannot supply a killer.
The deep configs (killer-fires with non-unit codomains, rides, sinks,
spines, killer-bodies) ride as NAMED HYPOTHESES — the honest conditional
layer, visible in `no_vanishing_fix_conditional`. The frame splits reuse
`append_cancel_left`/`append_cancel_right` (Cut.lean). -/

/-- The march's discipline: DomOK and chase-inert in both weights. -/
def MarchOK (a : Ty) : Prop := DomOK a ∧ tnet a ≤ 0 ∧ snet a ≤ 0

/-- The discipline at every position of the context. -/
def MarchCtx (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (b : Ty), Γ[i]? = some b → MarchOK b

/-- The token's own kind is MarchOK (binderOK, tnet 0, snet 0). -/
theorem marchOK_content : MarchOK Ty.content :=
  ⟨Or.inl (by simp [binderOK]), by simp [tnet], by simp [snet]⟩

theorem marchCtx_nil : MarchCtx [] := by
  intro i b hpos
  rw [List.get?_nil'] at hpos
  contradiction

theorem marchCtx_cons {a : Ty} {Γ : List Ty} (ha : MarchOK a) (hΓ : MarchCtx Γ) :
    MarchCtx (a :: Γ) := by
  intro i b hpos
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with hb
      subst hb
      exact ha
  | succ i =>
      rw [List.get?_succ_cons'] at hpos
      exact hΓ i b hpos

theorem marchCtx_of_cons {a : Ty} {Γ : List Ty} (h : MarchCtx (a :: Γ)) : MarchCtx Γ := by
  intro i b hpos
  exact h (i + 1) b (by rw [List.get?_succ_cons']; exact hpos)

theorem marchCtx_piece_left {ΓL ΓR : List Ty} (h : MarchCtx (ΓL ++ ΓR)) : MarchCtx ΓL := by
  intro i b hpos
  have hlt : i < ΓL.length := List.get?_some_lt hpos
  have hpos' : (ΓL ++ ΓR)[i]? = some b := by
    rw [List.get?_append_lt hlt]; exact hpos
  exact h i b hpos'

theorem marchCtx_piece_right {ΓL ΓR : List Ty} (h : MarchCtx (ΓL ++ ΓR)) : MarchCtx ΓR := by
  intro i b hpos
  have hpos' : (ΓL ++ ΓR)[ΓL.length + i]? = some b := by
    rw [List.get?_append_ge (Nat.le_add_right _ _)]
    rw [Nat.add_sub_cancel_left]
    exact hpos
  exact h (ΓL.length + i) b hpos'

/-- The token sits at position `ΓL.length` of the mid-token frame. -/
theorem frame_token {ΓL ΓR : List Ty} :
    (ΓL ++ Ty.content :: ΓR)[ΓL.length]? = some Ty.content := by
  rw [List.get?_append_ge (Nat.le_refl _)]
  rw [Nat.sub_self]
  exact List.get?_zero_cons'

/-! ## The (A)/(B') mutual block — the token's death-walk

(A) `march`: the mid-token fragment `(ΓL ++ [content] ++ ΓR) ⊢ unit` is
impossible under the `MarchCtx` discipline — the ROOT-case walk: a
unit-concluding fire with the token as its argument and a content-domain
killer → the (B')-peel; a killer carrying the token → its λ-body is a
strictly smaller fragment (the mid-token frame's purpose); the lete-body,
weak and contr roots recurse with the grown disciplined supplement; the
deep configs (spines, killer-bodies, deep args, scrutinees, non-MarchOK
domains/comps/heads, killer-fires with non-unit codomains) ride as NAMED
HYPOTHESES.

(B') `killer_peel`: a content-domain killer at a disciplined context is
impossible — the λ-head's unit-body is a strictly smaller (A)-fragment;
the fix-head stacks ▷s (the body `arrow (▷a) a` recurses at the stack —
a fix's promise can only be honored at a deeper delay); var/const heads
die by the discipline/type; the spine and the general λ-shapes ride as
named hypotheses.

Termination: pure size — every mutual call is at a strictly smaller
derivation (strong induction on `size`). -/
/-- The unit-codomain closure: the codomain chain bottoms at unit. This
is the class the (B')-peel's statement ranges over — outside it the
peel's claim is FALSE (the identity killer `λ(c).var 0 : arrow content
content` exists, and so do its killer-of-killer variants whose inner
codomain is not a unit-killer). -/
def EndsInUnit : Ty → Prop
  | .unit => True
  | .arrow _ σ => EndsInUnit σ
  | _ => False

/-- A unit-codomain-closed type needs neither stream nor trace (the
needs propagate through arrows to the codomain, and bottom at unit where
both are False). This is the peel-scope fact the fix-case's `marchOK_later`
call needs. -/
theorem endsInUnit_notNeedsS : ∀ {σ : Ty}, EndsInUnit σ → ¬NeedsS σ
  | .unit, _ => by simp [NeedsS]
  | .arrow _ σ', h => by intro hc; exact @endsInUnit_notNeedsS σ' h hc.1
  | .content, h | .knower, h | .knowledge, h | .value, h | .stream, h | .trace, h
  | .later _, h | .tensor _ _, h =>
      by unfold EndsInUnit at h; exact False.elim h

theorem endsInUnit_notNeedsT : ∀ {σ : Ty}, EndsInUnit σ → ¬NeedsT σ
  | .unit, _ => by simp [NeedsT]
  | .arrow _ σ', h => by intro hc; exact @endsInUnit_notNeedsT σ' h hc.1
  | .content, h | .knower, h | .knowledge, h | .value, h | .stream, h | .trace, h
  | .later _, h | .tensor _ _, h =>
      by unfold EndsInUnit at h; exact False.elim h

/-- A later-type is MarchOK when its payload's weights are nonpositive and
its payload needs neither stream nor trace: `DomOK (▷a)` reduces to the
classical `allInert a ∨ ¬allInert a` (the binderOK branch vs the D2
branch — the D2 conjuncts that are not free for `later` are exactly
`¬NeedsS a` and `¬NeedsT a`, the transparent ones), and the weights ride
the payload's. This is why the (B')-peel's fix-case has no
discipline-violation residual: the ▷-stack never breaks the march
discipline from within the peel's scope. -/
theorem marchOK_later {a : Ty} (ht : tnet a ≤ 0) (hs : snet a ≤ 0)
    (hnS : ¬NeedsS a) (hnT : ¬NeedsT a) :
    MarchOK (Ty.later a) := by
  constructor
  · by_cases hA : allInert a
    · exact Or.inl (by simp [binderOK, allInert, hA])
    · refine Or.inr ⟨?_, ?_⟩
      · simp [binderOK, allInert, hA]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro h; cases h
        · simp [DeepConsume]
        · simp [HasTokenDomain]
        · simp [NeedsC]
        · simp [NeedsK]
        · exact hnS
        · exact hnT
  · constructor
    · simp only [tnet]; exact ht
    · simp only [snet]; exact hs

/-- The march discipline kills both demand-need predicates: a MarchOK type
needs neither a knower (unconditionally — the binderOK branch is content
whose NeedsK is False, or inert; the D2 branch carries ¬NeedsK) nor a
content (given ≠ content — the binderOK branch is inert, the D2 branch
carries ¬NeedsC). These are the (D)-dispatch's clean sub-cases: at a
disciplined context, a NeedsC/NeedsK-typed value contradicts the
context's own discipline (cprop/kprop supply a demand-funding position,
and every position is MarchOK — content excluded by the frame's
uniqueness). -/
theorem marchOK_notNeedsK : ∀ {a : Ty}, MarchOK a → ¬NeedsK a := by
  intro a h
  rcases h with ⟨hdom, _, _⟩
  rcases hdom with hb | hd
  · unfold binderOK at hb
    rcases Bool.or_eq_true_iff.mp hb with heq | hi
    · have hac : a = Ty.content := eq_of_beq heq
      subst hac
      exact fun h => by cases h
    · exact fun hk => allInert_notNeedsK _ hi hk
  · exact hd.2.2.2.2.2.1

theorem marchOK_notNeedsC : ∀ {a : Ty}, MarchOK a → a ≠ Ty.content → ¬NeedsC a := by
  intro a h hne
  rcases h with ⟨hdom, _, _⟩
  rcases hdom with hb | hd
  · unfold binderOK at hb
    rcases Bool.or_eq_true_iff.mp hb with heq | hi
    · have hac : a = Ty.content := eq_of_beq heq
      exact absurd hac hne
    · exact fun hc => Bool.noConfusion ((needsC_notallInert a hc).symm.trans hi)
  · exact hd.2.2.2.2.1

/-- The sequent-calculus ⊗-right inversion, ported: a pair-rooted
cloning derivation splits its context, and the singleton frame forces
one side closed — the closed side concludes content from the empty
context, which is impossible (`no_closed_content`). In the sequent
presentations of linear logic this is the *entire* no-cloning argument:
invert `⊗R` (the rule splits the context by definition), observe the
split of a singleton context leaves one side empty, and refute
derivability from empty. Our calculus is a natural deduction — the
pair is a constructor that hides under spines and fixpoints — so this
lemma is only the pair-root case; the remaining roots (application
spines, lete, fix) need the march's walk. -/
theorem pair_root_kill {l r : Term} {Γ₁ Γ₂ : List Ty}
    (hl : Typed Γ₁ l Ty.content) (hr : Typed Γ₂ r Ty.content)
    (hs : Γ₁ ++ Γ₂ = [Ty.content]) : False := by
  cases Γ₁ with
  | nil => exact no_closed_content hl
  | cons a Γ₁' =>
      cases Γ₁' with
      | nil =>
          rw [List.cons_append, List.nil_append] at hs
          injection hs with _ hΓ₂
          subst hΓ₂
          exact no_closed_content hr
      | cons a' Γ₁'' =>
          cases Γ₂ with
          | nil =>
              rw [List.append_nil] at hs
              injection hs with _ h2
              injection h2
          | cons b Γ₂' =>
              injection hs with _ h2
              injection h2

/-- THE STRENGTHENED FRAME DISCIPLINE. -/
def MarchOK' (a : Ty) : Prop := MarchOK a ∧ LiveDomOK a

/-- The later case is ONE LINE, and the hypothesis fp14 proposed for it is
VESTIGIAL: a `later` is never an arrow, so `LiveDomOK (▷a)` is
unconditional. -/
theorem marchOK_later' {a : Ty} (ht : tnet a ≤ 0) (hs : snet a ≤ 0)
    (hnS : ¬NeedsS a) (hnT : ¬NeedsT a) : MarchOK' (Ty.later a) :=
  ⟨marchOK_later ht hs hnS hnT, liveDomOK_later⟩

theorem marchOK'_content : MarchOK' Ty.content :=
  ⟨marchOK_content, liveDomOK_content⟩

theorem marchOK_unit : MarchOK Ty.unit := by
  refine ⟨Or.inl ?_, ?_, ?_⟩
  · simp [binderOK, allInert]
  · simp only [tnet]; omega
  · simp only [snet]; omega

theorem marchOK'_unit : MarchOK' Ty.unit := ⟨marchOK_unit, liveDomOK_unit⟩

/-! ## The hole family, and the discipline's verdict on each -/

/-- ATU — `arrow trace unit`: admitted by `MarchOK`, banned by `MarchOK'`. -/
theorem containsLive_ATU : ContainsLive (Ty.arrow Ty.trace Ty.unit) := Or.inl trivial
theorem marchOK_ATU : MarchOK (Ty.arrow Ty.trace Ty.unit) := by
  refine ⟨Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [binderOK, allInert]
  · intro h; exact Ty.noConfusion h
  · simp [DeepConsume, NeedsC]
  · simp [HasTokenDomain, CarriesContent, NeedsC]
  · simp [NeedsC]
  · simp [NeedsK]
  · simp [NeedsS]
  · simp [NeedsT]
  · simp only [tnet]; omega
  · simp only [snet]; omega
theorem marchOK'_ATU_false : ¬ MarchOK' (Ty.arrow Ty.trace Ty.unit) := by
  intro h
  exact h.2 ⟨Ty.trace, Ty.unit, rfl, trivial⟩

/-- LTU — `arrow (later trace) unit`: the weights CANNOT see it (`tnet`
goes negative through the domain), `ContainsLive` can. -/
theorem containsLive_LTU : ContainsLive (Ty.arrow (Ty.later Ty.trace) Ty.unit) := by simp [ContainsLive]
theorem marchOK_LTU : MarchOK (Ty.arrow (Ty.later Ty.trace) Ty.unit) := by
  refine ⟨Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [binderOK, allInert]
  · intro h; exact Ty.noConfusion h
  · simp [DeepConsume, NeedsC]
  · simp [HasTokenDomain, CarriesContent, NeedsC]
  · simp [NeedsC]
  · simp [NeedsK]
  · simp [NeedsS]
  · simp [NeedsT]
  · simp only [tnet]; omega
  · simp only [snet]; omega
theorem marchOK'_LTU_false : ¬ MarchOK' (Ty.arrow (Ty.later Ty.trace) Ty.unit) := by
  intro h
  exact h.2 ⟨_, _, rfl, by simp [ContainsLive]⟩

/-- LCU — `arrow (later content) unit`: `NeedsC` is opaque at `later`, so
`DeepConsume` misses it; `ContainsLive` recurses. -/
theorem containsLive_LCU : ContainsLive (Ty.arrow (Ty.later Ty.content) Ty.unit) := by simp [ContainsLive]
theorem marchOK_LCU : MarchOK (Ty.arrow (Ty.later Ty.content) Ty.unit) := by
  refine ⟨Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [binderOK, allInert]
  · intro h; exact Ty.noConfusion h
  · simp [DeepConsume, NeedsC]
  · simp [HasTokenDomain, CarriesContent, NeedsC]
  · simp [NeedsC]
  · simp [NeedsK]
  · simp [NeedsS]
  · simp [NeedsT]
  · simp only [tnet]; omega
  · simp only [snet]; omega
theorem marchOK'_LCU_false : ¬ MarchOK' (Ty.arrow (Ty.later Ty.content) Ty.unit) := by
  intro h
  exact h.2 ⟨_, _, rfl, by simp [ContainsLive]⟩

/-- K — the reviewer's counterexample type
`arrow (later (arrow unit content)) unit`. -/
def KTy : Ty := .arrow (.later (.arrow .unit .content)) .unit

theorem containsLive_K : ContainsLive KTy := by simp [ContainsLive, KTy]

theorem marchOK_KTy : MarchOK KTy := by
  refine ⟨Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [binderOK, allInert, KTy]
  · intro h; exact Ty.noConfusion h
  · simp [DeepConsume, NeedsC, KTy]
  · simp [HasTokenDomain, CarriesContent, NeedsC, KTy]
  · simp [NeedsC, KTy]
  · simp [NeedsK, KTy]
  · simp [NeedsS, KTy]
  · simp [NeedsT, KTy]
  · simp only [tnet, KTy]; omega
  · simp only [snet, KTy]; omega

theorem marchOK'_K_false : ¬ MarchOK' KTy := by
  intro h
  exact h.2 ⟨_, _, rfl, by simp [ContainsLive]⟩

/-- A `later`-wrapped arrow whose domain is live is itself banned — the
intended "var-supplied fix-killers are LiveDomOK-banned" case. -/
theorem containsLive_laterArrow {X σ : Ty} (h : ContainsLive X) :
    ContainsLive (Ty.later (Ty.arrow X σ)) := by simp only [ContainsLive]; exact Or.inl h

/-- THE RESIDUAL: `arrow (later stream) unit` passes `MarchOK'` — stream is
deliberately out of `ContainsLive` because its only producers starve at a
frame (see `not_marchOK_laterStream` + `no_fix_at_token_frame`). -/
theorem marchOK'_laterStreamUnit : MarchOK' (Ty.arrow (Ty.later Ty.stream) Ty.unit) := by
  refine ⟨⟨Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simp [binderOK, allInert]
  · intro h; exact Ty.noConfusion h
  · simp [DeepConsume, NeedsC]
  · simp [HasTokenDomain, CarriesContent, NeedsC]
  · simp [NeedsC]
  · simp [NeedsK]
  · simp [NeedsS]
  · simp [NeedsT]
  · simp only [tnet]; omega
  · simp only [snet]; omega
  · intro h
    obtain ⟨d, c, he, hlive⟩ := h
    injection he with hd _
    subst hd
    exact not_containsLive_stream hlive

/-- The starvation premises for the residual: a `▷stream` POSITION is
banned by the old weight, and no fix can be typed at a frame that carries
the token (the token is linear; `AllNonLinear` demands every position
non-linear) — so the `▷stream` argument of the residual arrow cannot be
produced. -/
theorem not_marchOK_laterStream : ¬ MarchOK (Ty.later Ty.stream) := by
  intro h
  have hs : snet (Ty.later Ty.stream) ≤ 0 := h.2.2
  simp only [snet] at hs
  omega

theorem no_fix_at_token_frame {Γ : List Ty} (hΓ : AllNonLinear Γ)
    (i : Nat) (hpos : Γ[i]? = some Ty.content) : False := by
  have h := hΓ i Ty.content hpos
  rw [show Ty.content.isLinear = true from rfl] at h
  exact Bool.noConfusion h

/-! ## (b) The witness trees -/

/-- The ATU hole: the token is archived by `snoc`, delayed by `next`, and
eaten by a `▷trace`-domain killer. -/
def holeLTU : Typed [Ty.arrow (Ty.later Ty.trace) Ty.unit, Ty.content]
    (.app (.var 0) (.next (.snoc .nil (.var 0)))) Ty.unit :=
  Typed.app (Γ := [Ty.arrow (Ty.later Ty.trace) Ty.unit]) (Δ := [Ty.content])
    Typed.var
    (Typed.next (Typed.snoc Typed.nil Typed.var rfl))
    rfl

/-- The LCU hole: `next` delays the token itself. -/
def holeLCU : Typed [Ty.arrow (Ty.later Ty.content) Ty.unit, Ty.content]
    (.app (.var 0) (.next (.var 0))) Ty.unit :=
  Typed.app (Γ := [Ty.arrow (Ty.later Ty.content) Ty.unit]) (Δ := [Ty.content])
    Typed.var
    (Typed.next Typed.var)
    rfl

/-- THE REVIEWER'S K WITNESS: the token dies into a delayed content-PRODUCER
(`λ(u). var 1`, weakened past the non-linear unit), which `K` eats. -/
def holeK : Typed [KTy, Ty.content]
    (.app (.var 0) (.next (.lam .unit (.var 1)))) Ty.unit :=
  Typed.app (Γ := [KTy]) (Δ := [Ty.content])
    Typed.var
    (Typed.next (Typed.lam (Typed.weak (k := Ty.unit) (by rfl) Typed.var)))
    rfl

/-- The tensor-domain hole (my addition — the `tensor` clause is
load-bearing: `pair (var 0) unit` is a legal token-derived value). -/
def holeTensor : Typed [Ty.arrow (Ty.tensor Ty.content Ty.unit) Ty.unit, Ty.content]
    (.app (.var 0) (.pair (.var 0) .unit)) Ty.unit :=
  Typed.app (Γ := [Ty.arrow (Ty.tensor Ty.content Ty.unit) Ty.unit]) (Δ := [Ty.content])
    Typed.var
    (Typed.pair Typed.var Typed.unit rfl)
    rfl


/-- NOT TOO WIDE: the inert-domain arrow `arrow unit unit` stays admitted —
inert fires are the walk's chase-noise, not frame violations (fp2's
constraint (iii)). -/
theorem marchOK'_arrowUnitUnit : MarchOK' (Ty.arrow Ty.unit Ty.unit) := by
  refine ⟨⟨Or.inl ?_, ?_, ?_⟩, ?_⟩
  · simp [binderOK, allInert]
  · simp only [tnet]; omega
  · simp only [snet]; omega
  · intro h
    obtain ⟨d, c, he, hlive⟩ := h
    injection he with hd _
    subst hd
    exact not_containsLive_unit hlive

/-! ## The primed frame discipline -/

/-- The discipline at every position of the context — strengthened:
  every supplement position is `MarchOK'` (domain-OK, chase-inert in both
  weights, and not an arrow with a token-receiving domain). -/
def MarchCtx' (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (b : Ty), Γ[i]? = some b → MarchOK' b

theorem marchCtx'_nil : MarchCtx' [] := by
  intro i b hpos
  rw [List.get?_nil'] at hpos
  contradiction

theorem marchCtx'_cons {a : Ty} {Γ : List Ty} (ha : MarchOK' a) (hΓ : MarchCtx' Γ) :
    MarchCtx' (a :: Γ) := by
  intro i b hpos
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with hb
      subst hb
      exact ha
  | succ i =>
      rw [List.get?_succ_cons'] at hpos
      exact hΓ i b hpos

theorem marchCtx'_of_cons {a : Ty} {Γ : List Ty} (h : MarchCtx' (a :: Γ)) : MarchCtx' Γ := by
  intro i b hpos
  exact h (i + 1) b (by rw [List.get?_succ_cons']; exact hpos)

theorem marchCtx'_piece_left {ΓL ΓR : List Ty} (h : MarchCtx' (ΓL ++ ΓR)) : MarchCtx' ΓL := by
  intro i b hpos
  have hlt : i < ΓL.length := List.get?_some_lt hpos
  have hpos' : (ΓL ++ ΓR)[i]? = some b := by
    rw [List.get?_append_lt hlt]; exact hpos
  exact h i b hpos'

theorem marchCtx'_piece_right {ΓL ΓR : List Ty} (h : MarchCtx' (ΓL ++ ΓR)) : MarchCtx' ΓR := by
  intro i b hpos
  have hpos' : (ΓL ++ ΓR)[ΓL.length + i]? = some b := by
    rw [List.get?_append_ge (Nat.le_add_right _ _)]
    rw [Nat.add_sub_cancel_left]
    exact hpos
  exact h (ΓL.length + i) b hpos'

/-- The append-intro (both pieces primed) — the walk's frame plumbing. -/
theorem marchCtx'_append {ΓL ΓR : List Ty} (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR) :
    MarchCtx' (ΓL ++ ΓR) := by
  intro i b hpos
  by_cases h : i < ΓL.length
  · rw [List.get?_append_lt h] at hpos
    exact hL i b hpos
  · rw [List.get?_append_ge (by omega)] at hpos
    exact hR (i - ΓL.length) b hpos

/-! ## The primed/plain bridge + the inert-blocking family (w13's batch) -/

/-- `MarchCtx'` at a singleton context. -/
theorem marchCtx'_singleton {a : Ty} (h : MarchOK' a) : MarchCtx' [a] := by
  intro i b hpos
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with he
      subst he
      exact h
  | succ n =>
      rw [List.get?_succ_cons', List.get?_nil'] at hpos
      simp at hpos

/-! ## The three contrast facts -/

theorem not_marchOK'_laterTrace : ¬ MarchOK' (Ty.later Ty.trace) := by
  intro h
  have ht : tnet (Ty.later Ty.trace) ≤ 0 := h.1.2.1
  simp only [tnet] at ht
  omega

/-- THE LIVENESS PREDICATE'S PAYOFF: a `▷trace`-domain arrow is never a
disciplined position — the domain is live, so `LiveDomOK` refuses it. -/
theorem not_marchOK'_arrowLaterTrace (σ : Ty) :
    ¬ MarchOK' (Ty.arrow (Ty.later Ty.trace) σ) := by
  intro h
  exact h.2 ⟨Ty.later Ty.trace, σ, rfl, by simp [ContainsLive]⟩

theorem not_marchOK'_trace : ¬ MarchOK' Ty.trace := by
  intro h
  have ht : tnet Ty.trace ≤ 0 := h.1.2.1
  simp only [tnet] at ht
  omega

theorem not_marchOK'_knower : ¬ MarchOK' Ty.knower := by
  intro h
  rcases h.1.1 with hb | hd
  · simp [binderOK, allInert] at hb
  · exact hd.2.2.2.2.2.1 trivial

/-! ## TARGET 2 — REFUTED-WITH-WITNESS

"MarchCtx' Γ → Typed Γ fn (arrow (later stream) unit) → False" is FALSE:
`arrow (▷stream) unit` is itself `MarchOK'` (the tree's
`marchOK'_laterStreamUnit`), so a disciplined context can hold it, and
`Typed.var` reads it. The residual is reachable as a POSITION, not merely
as an unfeedable closed arrow — the statement needs the token/root in
scope, or `¬ MarchOK'` of the type itself.
-/
theorem streamKiller_at_frame_refuted :
    ¬ (∀ {Γ : List Ty} {fn : Term}, MarchCtx' Γ →
        Typed Γ fn (.arrow (.later .stream) .unit) → False) := by
  intro hall
  exact hall (Γ := [Ty.arrow (Ty.later Ty.stream) Ty.unit]) (fn := .var 0)
    (marchCtx'_singleton marchOK'_laterStreamUnit) Typed.var

/-- The same statement WITH the token in the context is not refuted this
way — the var-witness context has no token, which is exactly the missing
hypothesis. (Recorded as a shape note, not a proof.) -/
theorem streamKiller_needs_token : ∀ (h : MarchOK' (Ty.arrow (Ty.later Ty.stream) Ty.unit)),
    MarchCtx' [Ty.arrow (Ty.later Ty.stream) Ty.unit] := fun _ => marchCtx'_singleton marchOK'_laterStreamUnit

/-! ## TARGET 3's comp classes

The two comp classes that are not `MarchOK'` and could appear in a `lete`:
`trace` (tnet 1) and `knower` (NeedsK kills D2). Both need a VALUE the
calculus cannot supply at a disciplined context: a trace-valued comp needs
a closed trace-killer (target 1's base), a knower comp needs a closed
knower (`no_closed_knower`, already in the tree). No witness found.
-/



/-! ## The primed/plain bridge -/

theorem marchCtx'_impl_marchCtx {Γ : List Ty} (h : MarchCtx' Γ) : MarchCtx Γ :=
  fun i b hpos => (h i b hpos).1

/-- The unit case is `march_block`'s (A) conjunct, verbatim, modulo the
frame projection. Nothing new is needed for X = unit. -/
theorem token_death_unit_of_A
    (hA : ∀ (fuel : Nat) (Γ ΓL ΓR : List Ty), MarchCtx ΓL → MarchCtx ΓR →
      Γ = ΓL ++ Ty.content :: ΓR →
      ∀ {t : Term} (h : Typed Γ t Ty.unit), size h ≤ fuel → False) :
    ∀ (fuel : Nat) {ΓL'' ΓR Δ : List Ty} {arg : Term},
      MarchCtx' ΓL'' → MarchCtx' ΓR → Δ = ΓL'' ++ Ty.content :: ΓR →
      ¬ ContainsLive Ty.unit → ¬ NeedsK Ty.unit → ¬ NeedsS Ty.unit →
      (ha : Typed Δ arg Ty.unit) → size ha ≤ fuel → False := by
  intro fuel ΓL'' ΓR Δ arg hL hR heq _ _ _ ha hsz
  exact hA fuel Δ ΓL'' ΓR (marchCtx'_impl_marchCtx hL) (marchCtx'_impl_marchCtx hR)
    heq ha hsz

/-! ## The inert-blocking family (the rides, type-blocked at the root) -/

theorem inert_not_content {X : Ty} (h : ¬ ContainsLive X) : X ≠ Ty.content :=
  fun he => h (by rw [he]; exact containsLive_content)

theorem inert_not_trace {X : Ty} (h : ¬ ContainsLive X) : X ≠ Ty.trace :=
  fun he => h (by rw [he]; exact containsLive_trace)

theorem inert_later {X : Ty} (h : ¬ ContainsLive X) : ¬ ContainsLive (Ty.later X) := h

theorem inert_tensor {X Y : Ty} (hx : ¬ ContainsLive X) (hy : ¬ ContainsLive Y) :
    ¬ ContainsLive (Ty.tensor X Y) := fun h => Or.elim h hx hy

theorem inert_arrow {X Y : Ty} (hx : ¬ ContainsLive X) (hy : ¬ ContainsLive Y) :
    ¬ ContainsLive (Ty.arrow X Y) := fun h => Or.elim h hx hy

theorem inert_arrow_dom {X Y : Ty} (h : ¬ ContainsLive (Ty.arrow X Y)) :
    ¬ ContainsLive X := fun hx => h (Or.inl hx)

theorem inert_arrow_cod {X Y : Ty} (h : ¬ ContainsLive (Ty.arrow X Y)) :
    ¬ ContainsLive Y := fun hy => h (Or.inr hy)

/-- CAVEAT for the walk: inertness is a DEMAND condition, not a linearity
one — `arrow stream unit` is inert by all three hypotheses yet linear (and
carries a stream), so `weak` cannot discard it. -/
theorem inert_but_linear :
    ¬ ContainsLive (Ty.arrow Ty.stream Ty.unit)
      ∧ ¬ NeedsK (Ty.arrow Ty.stream Ty.unit)
      ∧ ¬ NeedsS (Ty.arrow Ty.stream Ty.unit)
      ∧ (Ty.arrow Ty.stream Ty.unit).isLinear = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ContainsLive]
  · intro h; exact h.1
  · intro h; exact h.1
  · simp [Ty.isLinear]

/-! ## The statement pin (not proven here — the march's (A)-induction,
generalized from `unit` to an arbitrary inert X) -/

/-- `token_death`'s shape. The proof is `march_block`'s (A)-induction with
the conclusion type generalized; the rides are type-blocked (the family
above) and the killer cases are (B′) — so the case map is pure dispatch
EXCEPT at subterm spends, where the token rides into a binder context and
the frame must be re-established: that is the named residual
`hleteCompOK` (the lete's comps are MarchOK' — nothing landed implies it;
it is the record's comp-family residual, and its own proof is the same
"the comp's value cannot be built" regress as `hcompositeKiller`). -/
def TokenDeathShape (fuel : Nat) : Prop :=
  ∀ {ΓL'' ΓR Δ : List Ty} {X : Ty} {arg : Term},
    MarchCtx' ΓL'' → MarchCtx' ΓR → Δ = ΓL'' ++ Ty.content :: ΓR →
    ¬ ContainsLive X → ¬ NeedsK X → ¬ NeedsS X →
    (ha : Typed Δ arg X) → size ha ≤ fuel → False

/-! ## The arg-side carry/inert split (slice 2 foundation; w13 p12)

Setting (as it sits inside `march_block`'s (A)-app arg-side, main 15c5c45):
the (A)′-root is `app hf ha : unit` at the primed mid-token frame
`E = Γ₁ ++ Δ = ΓL ++ content :: ΓR`, token ∈ Δ, `X` the arg's type with
`X ≠ content` (that case now routes to (B′) unconditionally — the bridge
`marchCtx'_impl_marchCtx` is landed).

THIS FILE LANDS THE TWO DEAD SUB-ARMS OF THE CARRY CASE plus the small
lemmas they need, and pins the split. The INERT arm's pure dispatch is a
case map (documented below), not typed here: its λ-killer arm needs (B′)′
at arbitrary conclusions, which the tree's (B′)′ does not provide (its
class is `EndsInUnit σ`), so that arm is honestly a residual.
## THE INERT ARM's case map (the pure dispatch, for slice 2's typing)

Inside `ha`'s tree, with `X` inert (¬ContainsLive, ¬NeedsK, ¬NeedsS):

1. `single_linear_use` at the token position (content is linear) gives
   `uses ha tokIdx = 1` — the token IS spent inside ha.
2. `read_locate` finds the read `v : Typed [content] (var 0) content`;
   `prem_position` locates its parent slot.
3. The parent-slot dispatch on the READ's parent:
   - **app-fn** — type-blocked: v's type is content, and the fn slot needs
     an arrow.
   - **app-arg** (the killer fire `app hf' v : σ'`): `hf' : Typed Γ'
     hf' (arrow content σ')`. Heads:
     * var-headed → `not_marchOK'_arrowContent` + the frame ⇒ the position
       cannot be in the token frame ⇒ it is a binder annotation ⇒ the
       enclosing binder's body is the continuation (see 4);
     * λ-headed → **(B′)′ needs `EndsInUnit σ'`**, which an inner fire does
       not have ⇒ **RESIDUAL `hinnerKiller`** (this is the honest gap: the
       walk cannot kill a content-killer whose fire concludes a live or
       inert type, only a unit-closure one);
     * const-headed → domain-block (no constant's domain is content);
     * spine-headed → recurse (the inner fire is smaller);
     * lete/contr/weak-headed → transparent (position-map).
   - **pair-comp / next-arg / snoc-arg / cons-hd** — the rides: type-blocked
     AT THE ROOT (inert_later/inert_tensor, landed), but at a SUBTERM they
     move the token into the container's parent ⇒ the walk ascends one
     level and continues (this is the p11 root/subterm correction; the
     ascent is bounded by the tree).
   - **lam-body / lete-body** — the token enters a binder context; the
     frame must be re-established (`hleteCompOK`, the comp-family
     residual, for letes; `hlamDom`-shaped for λs).
4. Termination: descents (spine/transparent) strictly shrink; the rides
   ascend but consume a container; the fuel is the (A)-induction's `size`.
-/


/-! The CARRY arm: hcarryArg is NOT a new residual — NeedsK sub-arm DEAD
(kprop + frame + marchOK_notNeedsK), NeedsS sub-arm DEAD modulo the
fix-escape (spropF + frame + marchOK_notNeedsS), the ContainsLive
sub-arm routes to hlamDom (the fn is constructed: LiveDomOK refuses
arrow X unit with ContainsLive X as a position). The INERT arm has one
honest gap: hinnerKiller — the content-killer at an inner fire whose
conclusion is outside EndsInUnit. -/

/-! ## The small lemmas the map needs -/

theorem marchOK_notNeedsS : ∀ {a : Ty}, MarchOK a → ¬ NeedsS a := by
  intro a h
  rcases h with ⟨hdom, _, _⟩
  rcases hdom with hb | hd
  · exact binderOK_notNeedsS hb
  · exact hd.2.2.2.2.2.2.1

theorem marchOK'_notNeedsS {a : Ty} (h : MarchOK' a) : ¬ NeedsS a :=
  marchOK_notNeedsS h.1

theorem marchOK'_notNeedsK {a : Ty} (h : MarchOK' a) : ¬ NeedsK a :=
  marchOK_notNeedsK h.1

/-- The content-domain arrow is never a disciplined position. -/
theorem not_marchOK'_arrowContent (σ : Ty) : ¬ MarchOK' (Ty.arrow Ty.content σ) := by
  intro h
  exact h.2 ⟨Ty.content, σ, rfl, containsLive_content⟩

/-- The token frame is disciplined when its pieces are. -/
theorem marchCtx'_token {ΓL ΓR : List Ty} (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR) :
    MarchCtx' (ΓL ++ Ty.content :: ΓR) := by
  intro i b hpos
  by_cases hlt : i < ΓL.length
  · exact hL i b (by rw [List.get?_append_lt hlt] at hpos; exact hpos)
  · have hge : ΓL.length ≤ i := Nat.le_of_not_lt hlt
    rw [List.get?_append_ge hge] at hpos
    rcases Nat.eq_zero_or_pos (i - ΓL.length) with h0 | hpos'
    · rw [h0, List.get?_zero_cons'] at hpos
      injection hpos with he
      subst he
      exact marchOK'_content
    · obtain ⟨j, hj⟩ : ∃ j, i - ΓL.length = j + 1 := ⟨i - ΓL.length - 1, by omega⟩
      rw [hj, List.get?_succ_cons'] at hpos
      exact hR j b hpos

/-! ## The CARRY/inert split (the dRoute classes, verbatim) -/

theorem carry_or_inert {X : Ty} :
    (ContainsLive X ∨ NeedsK X ∨ NeedsS X)
      ∨ (¬ ContainsLive X ∧ ¬ NeedsK X ∧ ¬ NeedsS X) := by
  by_cases h1 : ContainsLive X
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : NeedsK X
    · exact Or.inl (Or.inr (Or.inl h2))
    · by_cases h3 : NeedsS X
      · exact Or.inl (Or.inr (Or.inr h3))
      · exact Or.inr ⟨h1, h2, h3⟩

/-! ## The two dead CARRY sub-arms -/

/-- NeedsK sub-arm: DEAD. -/
theorem carry_needsK_dead {ΓL ΓR Δ : List Ty} {X : Ty} {arg : Term}
    (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR) (heq : Δ = ΓL ++ Ty.content :: ΓR)
    (hK : NeedsK X) (ha : Typed Δ arg X) : False := by
  obtain ⟨i, b, hpos, hneed⟩ := kprop ha hK
  have hctx : MarchCtx' Δ := by rw [heq]; exact marchCtx'_token hL hR
  exact marchOK'_notNeedsK (hctx i b hpos) hneed

/-- NeedsS sub-arm: DEAD, modulo the fix-escape (`hnofix`). -/
theorem carry_needsS_dead {ΓL ΓR Δ : List Ty} {X : Ty} {arg : Term}
    (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR) (heq : Δ = ΓL ++ Ty.content :: ΓR)
    (ha : Typed Δ arg X) (hnofix : FixNeedS ha → False) (hS : NeedsS X) : False := by
  rcases spropF_uses ha hS with ⟨i, b, hpos, hsup, _⟩ | hesc
  · have hctx : MarchCtx' Δ := by rw [heq]; exact marchCtx'_token hL hR
    rcases hsup with hs | hk
    · exact marchOK'_notNeedsS (hctx i b hpos) hs
    · exact marchOK'_notNeedsK (hctx i b hpos) hk
  · exact hnofix hesc

/-- The two dead arms composed: any CARRY type that is not live is dead
outright, so the carry arm's only live obligation is the ContainsLive
sub-arm (which routes to `hlamDom`). -/
theorem carry_nonlive_dead {ΓL ΓR Δ : List Ty} {X : Ty} {arg : Term}
    (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR) (heq : Δ = ΓL ++ Ty.content :: ΓR)
    (ha : Typed Δ arg X) (hnofix : FixNeedS ha → False)
    (h : NeedsK X ∨ NeedsS X) : False := by
  rcases h with hK | hS
  · exact carry_needsK_dead hL hR heq hK ha
  · exact carry_needsS_dead hL hR heq ha hnofix hS


/-! ## The redispatch backbone + the five restated pins (w13 p13, w14 repair)

THE REDISPATCH: at ¬MarchOK' X, split on nok'_split — ¬LiveDomOK X
(the constructed-killer regress: the carry analysis routes it) or
¬MarchOK X (the (D)-dispatch: dRoute at X). -/


/-- THE REDISPATCH BACKBONE: `¬MarchOK' X` splits into the plain-discipline
failure and the liveness failure. -/
theorem nok'_split {X : Ty} (h : ¬ MarchOK' X) : ¬ MarchOK X ∨ ¬ LiveDomOK X := by
  by_cases h1 : MarchOK X
  · right
    intro h2
    exact h ⟨h1, h2⟩
  · left; exact h1

/-- w14's hdeepArg witness dies under `EndsInUnit σ`: the trace-identity's
codomain is `trace`, and `EndsInUnit trace` is FALSE. -/
theorem not_endsInUnit_trace : ¬ EndsInUnit Ty.trace := by
  unfold EndsInUnit
  exact fun h => h

/-- The witness shape itself, for the record: the trace-identity killer
(`fn = lam trace (var 0) : arrow trace trace`) — it needs σ = trace, which
`EndsInUnit σ` excludes. -/
def traceIdentity : Typed [] (.lam Ty.trace (.var 0)) (Ty.arrow Ty.trace Ty.trace) :=
  Typed.lam Typed.var

/-- And hlamDom's witness dies under the killer-context discipline: the
killerBinder's domain is ACU, which is not MarchOK'. -/
theorem hlamDom_guard_kills_witness : ¬ MarchOK' (Ty.arrow Ty.content Ty.unit) :=
  not_marchOK'_arrowContent Ty.unit

/-! ## The interval-17 falsity map (all three kernel-checked)

TWO rounds of witnesses beyond w14's obs-246 set, found by re-deriving
the pin-install against the walk's site data. Together they settle
which restatements are sound:

W1 — the content-domain killer with an `EndsInUnit` chain codomain at
`[]`. Kills every `hdeepArg` restatement WITHOUT a codomain constraint:
the produce's own λ-binders may be ¬MarchOK' (ACU), so the produce's
inner frame is NOT an (A)-instance and the killer EXISTS.

W2 — a SECOND lete-witness for `hscrut`, independent of w14's #3: the
token rides as the content comp and the produce's ACU-binder fires on
it. The comps are BOTH MarchOK' (`unit`, `content`) — so this witness
kills the comps-discipline restatement AND the arg-carrying walk-site
candidate (the walk's current arg is the closed unit at `W := unit`,
which exists). Only `¬ContainsLive σ'` excludes it — which the walk's
`lete` site cannot supply.

W3 — the trace-DOMAIN killer whose chain carries the ATU one level in:
the trace is consumable as the ATU-fire's arg (the "trace unconsumable
at position 0" claim was about the INNERMOST binder only). Kills the
banked `HDeepArg'` pin (the `X ≠ content` guard and `EndsInUnit σ`
conjuncts do not exclude it). The sound `:6612` repair is the
UNIT-CODOMAIN specialization — `fn : Γ₁ ⊢ arrow X unit` — which W1/W3
cannot instantiate (their codomains are chains).

CONSEQUENCE for the walk sites (`:6844`/`:6909`): every candidate that
does not reach the ORIGIN's arg is refuted at spine depth ≥ 1 (the
refuter grows the produce chain and places the ACU at the innermost
level, supplying fresh unit args at each level) — those residuals need
the walk to carry the origin's arg (the next increment). -/

/-- W1's inner fire: the ACU-fn consuming the content at `[ACU, content]`. -/
def W1_inner : Typed [ACU, Ty.content] (.app (.var 0) (.var 0)) Ty.unit :=
  Typed.app (Γ := [ACU]) (Δ := [Ty.content]) Typed.var Typed.var rfl

/-- W1: `λ(c:content).λ(f:ACU).app f c` — a content-domain killer whose
codomain `arrow ACU unit` is `EndsInUnit`, at `[]`. -/
def W1_fn : Typed [] (.lam Ty.content (.lam ACU (.app (.var 0) (.var 0))))
    (.arrow Ty.content (.arrow ACU Ty.unit)) :=
  Typed.lam (Typed.lam W1_inner)

theorem W1_endsInUnit : EndsInUnit (.arrow ACU Ty.unit) := by simp [EndsInUnit]

/-- The guard-free `hdeepArg` restatement is FALSE — W1 fires on the token. -/
def DeepArgUnguarded : Prop :=
  ∀ {Γ₁ ΓL'' ΓR : List Ty} {X σ : Ty} {fn arg : Term},
    MarchCtx' Γ₁ → EndsInUnit σ →
    Typed Γ₁ fn (Ty.arrow X σ) → Typed (ΓL'' ++ Ty.content :: ΓR) arg X → False

theorem deepArg_unguarded_refuted (h : DeepArgUnguarded) : False := by
  have ha : Typed ([] ++ Ty.content :: []) (.var 0) Ty.content := Typed.var
  exact h marchCtx'_nil W1_endsInUnit W1_fn ha

/-- W2's produce-fire: the ACU-binder (position 0) consuming the content
comp (position 3), with the two non-linear unit positions weak-lifted. -/
def W2_arg : Typed [Ty.unit, Ty.unit, Ty.content]
    (Term.liftAt 0 (Term.liftAt 0 (.var 0))) Ty.content :=
  Typed.weak rfl (Typed.weak rfl Typed.var)

def W2_fire : Typed [ACU, Ty.unit, Ty.unit, Ty.content]
    (.app (.var 0) (Term.liftAt 0 (Term.liftAt 0 (.var 0)))) Ty.unit :=
  Typed.app (Γ := [ACU]) (Δ := [Ty.unit, Ty.unit, Ty.content])
    Typed.var W2_arg rfl

/-- W2's body: `λ(u:unit).λ(f:ACU).app f (var 3)` — the produce at the
comps frame `[unit, content]`, concluding the walk's telescope
`arrow unit (arrow ACU unit)`. -/
def W2_hb : Typed [Ty.unit, Ty.content]
    (.lam Ty.unit (.lam ACU (.app (.var 0) (Term.liftAt 0 (Term.liftAt 0 (.var 0))))))
    (.arrow Ty.unit (.arrow ACU Ty.unit)) :=
  Typed.lam (Typed.lam W2_fire)

/-- W2's scrutinee: `pair (var 0) unit` — the token read directly as the
content comp. -/
def W2_ht : Typed [Ty.content, Ty.unit]
    (.pair (.var 0) (Term.liftAt 0 Term.unit)) (.tensor Ty.content Ty.unit) :=
  Typed.pair Typed.var (Typed.weak rfl Typed.unit) rfl

/-- W2's σ' is LIVE — the `¬ContainsLive σ'` conjunct (HScrut''') excludes
this witness; every weaker restatement falls to it. -/
theorem W2_sigma_live : ContainsLive (Ty.arrow Ty.unit (.arrow ACU Ty.unit)) :=
  Or.inr (Or.inl (Or.inl trivial))

theorem W2_sigma_endsInUnit : EndsInUnit (Ty.arrow Ty.unit (.arrow ACU Ty.unit)) := by
  simp [EndsInUnit]

/-- The LANDED `hscrut` shape (march_block's) has a SECOND witness (W2)
with MarchOK' comps — the comps-discipline restatement falls too. -/
def ScrutLanded : Prop :=
  ∀ {Γa Γb ΓL ΓR₁ : List Ty} {a' b' σ' : Ty} {t body : Term},
    MarchCtx' ΓL → MarchCtx' ΓR₁ → MarchCtx' (b' :: a' :: Γb) →
    Typed Γa t (Ty.tensor a' b') → Typed (b' :: a' :: Γb) body σ' →
    Γa ++ Γb = ΓL ++ Ty.content :: ΓR₁ → ΓL.length < Γa.length →
    EndsInUnit σ' → False

theorem scrut_landed_refuted_2 (h : ScrutLanded) : False :=
  h marchCtx'_nil (marchCtx'_cons marchOK'_unit marchCtx'_nil)
    (marchCtx'_cons marchOK'_unit (marchCtx'_cons marchOK'_content marchCtx'_nil))
    W2_ht W2_hb rfl (by decide) W2_sigma_endsInUnit

/-- The arg-carrying walk-site candidate falls as well (W2's arg is the
closed unit at `W := unit`). -/
def ScrutWCarrying : Prop :=
  ∀ {Γa Γb Γu ΓL ΓR₃ : List Ty} {a' b' W σ : Ty} {t body u : Term},
    MarchCtx' ΓL → MarchCtx' ΓR₃ → MarchCtx' Γb → MarchCtx' Γu →
    Typed Γa t (Ty.tensor a' b') → Typed (b' :: a' :: Γb) body (Ty.arrow W σ) →
    Typed Γu u W →
    Γa = ΓL ++ Ty.content :: ΓR₃ → ΓL.length < Γa.length →
    EndsInUnit σ → False

theorem scrutW_carried_refuted (h : ScrutWCarrying) : False :=
  h marchCtx'_nil (marchCtx'_cons marchOK'_unit marchCtx'_nil)
    marchCtx'_nil marchCtx'_nil
    W2_ht W2_hb Typed.unit rfl (by decide) (by simp [EndsInUnit])

/-- W3's inner fire: the ATU-fn consuming the trace at
`[arrow trace unit, trace]` — the trace consumable as the fire's arg. -/
def W3_fire : Typed [Ty.arrow Ty.trace Ty.unit, Ty.trace] (.app (.var 0) (.var 0)) Ty.unit :=
  Typed.app (Γ := [Ty.arrow Ty.trace Ty.unit]) (Δ := [Ty.trace]) Typed.var Typed.var rfl

/-- W3: `λ(t:trace).λ(f:ATU).app f t` — the trace-domain killer with the
ATU one level in. -/
def W3_fn : Typed []
    (.lam Ty.trace (.lam (Ty.arrow Ty.trace Ty.unit) (.app (.var 0) (.var 0))))
    (.arrow Ty.trace (.arrow (Ty.arrow Ty.trace Ty.unit) Ty.unit)) :=
  Typed.lam (Typed.lam W3_fire)

def W3_arg : Typed ([] ++ Ty.content :: []) (.snoc .nil (.var 0)) Ty.trace :=
  Typed.snoc Typed.nil Typed.var rfl

/-- The banked `HDeepArg'` pin (guard + EndsInUnit) is FALSE — W3
satisfies every conjunct. -/
def DeepArgGuarded : Prop :=
  ∀ {Γ₁ ΓL'' ΓR : List Ty} {X σ : Ty} {fn arg : Term},
    MarchCtx' Γ₁ → X ≠ Ty.content → EndsInUnit σ →
    Typed Γ₁ fn (Ty.arrow X σ) → Typed (ΓL'' ++ Ty.content :: ΓR) arg X → False

theorem deepArg_guarded_refuted (h : DeepArgGuarded) : False := by
  have hX : (Ty.trace : Ty) ≠ Ty.content := by decide
  exact h marchCtx'_nil hX (by simp [EndsInUnit]) W3_fn W3_arg

/-! ## The restated shapes, as pins (REVISED, interval 17)

`HScrut'` (comps discipline) is REMOVED — refuted by W2 above. The old
`HLamDom'` (killer-context discipline) is SUPERSEDED by `HLamDomFired`:
the `:6804` call site sits in the `¬MarchOK' W` branch, where the
killer-context hypothesis is contradictory (unsuppliable), while the
FIRED-killer shape — carrying the walk's own arg — kills the
killerBinder witness through the (B')-dead ACU-arg, and the deeper-W
witnesses die on the MLL-dead produce frames (the hunt: `trace`/
`▷trace`/`knower`/`AUW`-domains all dead; `later content` dies on the
`▷content`-unconsumable body; `tensor content unit` dies on the
lete-comp regress). `HPeelLam'`/`HPeelLete'` stand unchanged. -/

/-- The fired-killer pin (the `:6804` install target, INSTALLED below):
a ¬MarchOK'-domain λ with a unit body at the mid-token fn-frame, FIRED
on a primed arg. -/
def HLamDomFired : Prop :=
  ∀ {Γg Γu ΓL ΓR₃ : List Ty} {W : Ty} {body u : Term},
    MarchCtx' ΓL → MarchCtx' ΓR₃ → MarchCtx' Γu →
    ¬ MarchOK' W →
    Typed (W :: Γg) body Ty.unit → Typed Γu u W →
    Γg = ΓL ++ Ty.content :: ΓR₃ → False

def HPeelLam' : Prop :=
  ∀ {Γ : List Ty} {X σ : Ty} {body : Term},
    MarchCtx' (X :: Γ) → DeepConsume (Ty.arrow X σ) →
    (X = Ty.content ∨ ∃ a', X = Ty.later a') → MarchOK' X →
    EndsInUnit σ → Typed (X :: Γ) body σ → False

def HPeelLete' : Prop :=
  ∀ {Γ Γb : List Ty} {X σ y x : Ty} {fn : Term},
    MarchCtx' (y :: x :: Γb) → DeepConsume (Ty.arrow X σ) →
    (X = Ty.content ∨ ∃ a', X = Ty.later a') → MarchOK' X →
    EndsInUnit σ → Typed (y :: x :: Γb) fn (Ty.arrow X σ) →
    ¬ (MarchOK y ∧ MarchOK x) → False


/-! ## The composed-install helpers (w13 p19, w14 rounds 1–2 — all T3'd)

The MidToken boundary facts (`(A)`'s frame equation `Γ = ΓL ++ content
:: ΓR` is `MidToken` natively), the two known witnesses' exclusions,
and the guard's self-dead later-arm. The round-2 resolution DROPS
`MidToken` from the composed (B′) — the (A)-statement carries the frame
equation natively, so only `¬ContainsLive σ` threads (B′). -/

/-- The token equation: the frame carries the token. `(A)`'s own frame
hypothesis `Γ = ΓL ++ content :: ΓR` is this predicate. -/
def MidToken (Γ : List Ty) : Prop := ∃ ΓL ΓR, Γ = ΓL ++ Ty.content :: ΓR

/-- The closed witness (#4) is excluded: `[]` is not mid-token. -/
theorem not_midToken_nil : ¬ MidToken [] := by
  rintro ⟨ΓL, ΓR, h⟩
  have hlen := congrArg List.length h
  simp only [List.length_nil, List.length_append, List.length_cons] at hlen
  omega

/-- The (A)-root `[content]` IS mid-token (the singleton frame). -/
theorem midToken_single : MidToken [Ty.content] :=
  ⟨[], [], rfl⟩

/-- `ACU = arrow content unit` is live (content in the domain). -/
theorem containsLive_ACU : ContainsLive ACU := by
  unfold ACU
  exact containsLive_arrow.mpr (Or.inl containsLive_content)

/-- The killer-of-killer's codomain `arrow ACU unit` IS live — this is
what `¬ContainsLive σ` excludes at the fired instance (w14 round 1's
P1: `app (lam content killerBinder) (var 0)` legally fires at the token
frame). -/
theorem containsLive_killerOfKiller_cod : ContainsLive (Ty.arrow ACU Ty.unit) :=
  containsLive_arrow.mpr (Or.inl containsLive_ACU)

/-- `killerBinder`'s type is `arrow ACU unit`, NOT `ACU`: the
killer-of-killer cannot be fired on itself. This failed construction is
the T3 evidence (w13 p19): to build a `unit`-typed body at a token frame
you must fire a killer on a token-derived argument, and the only
token-derived argument at `[content]` is the token itself — the march
(A). -/
theorem killerBinder_type_is_not_ACU :
    (Ty.arrow ACU Ty.unit) ≠ ACU := by
  intro h
  unfold ACU at h
  injection h with h1 _
  exact Ty.noConfusion h1

/-- The guard's `X = later a` arm is self-dead (w14 round 2's A1):
`DeepConsume (arrow (later a) σ)` forces `DeepConsume σ`, hence
`ContainsLive σ` — contradicting `¬ContainsLive σ`. -/
theorem laterDom_dead {a σ : Ty}
    (h : DeepConsume (Ty.arrow (Ty.later a) σ))
    (hnl : ¬ ContainsLive σ) : False := by
  unfold DeepConsume at h
  rcases h with h | h
  · rcases h with h | h | h
    · exact Ty.noConfusion h
    · cases h
    · cases h
  · exact hnl (deepConsume_containsLive σ h)

/-! ## The round-3 crop: (C) is DELETED, not folded (w13 p21, kernel)

The folded (C)+¬ContainsLive σ is REFUTED: the hscrut witness's (C)-shape
σ is `unit` (the fire's conclusion is `arrow ACU unit` — the CODOMAIN is
unit), so the codomain predicate is SATISFIED at the witness; the escape
is the DOMAIN side (X = ACU, off the guard), which (C) never guarded.
The σ-slot is STATEMENT-RELATIVE — the same term's (B′)-shape σ (the λ's
codomain `arrow ACU unit`) is live, its (C)-shape σ (the fire's codomain)
is not. hmain loses the (C) conjunct; the (A)-app killer-side cases the
fn directly (the spine-walk) with the arg in scope. -/

/-- The folded (C) pin — REFUTED below (the falsity-map record). -/
def FoldedC : Prop :=
  ∀ (fuel : Nat) {Γ₁ ΓL ΓR₁ : List Ty} {fn : Term} {X σ : Ty}
    (h : Typed Γ₁ fn (Ty.arrow X σ)),
    MarchCtx' ΓL → MarchCtx' ΓR₁ → Γ₁ = ΓL ++ Ty.content :: ΓR₁ →
    EndsInUnit σ → ¬ ContainsLive σ → size h ≤ fuel → False

/-- The refuting witness: the lete that spends the token in the scrutinee
and returns the killer type. -/
def cWitness : Term := .lete (.pair (.var 0) .unit) killerBinder

def cWitnessTyped : Typed [Ty.content] cWitness (Ty.arrow ACU Ty.unit) :=
  Typed.lete
    (Γ₁ := [Ty.content]) (Γ₂ := [])
    (Typed.pair (Γ := [Ty.content]) (Δ := []) Typed.var Typed.unit rfl)
    (Typed.weak (k := Ty.unit) rfl killerBinderTyped)
    (by rw [List.append_nil])

/-- THE FOLDED (C) IS FALSE (w13 p21): every hypothesis is supplied at the
witness — including `¬ContainsLive unit`. -/
theorem foldedC_refuted (h : FoldedC) : False :=
  h (fuel := size cWitnessTyped) (Γ₁ := [Ty.content]) (ΓL := []) (ΓR₁ := [])
    (fn := cWitness) (X := ACU) (σ := Ty.unit)
    cWitnessTyped
    marchCtx'_nil marchCtx'_nil rfl
    (by unfold EndsInUnit; trivial)
    not_containsLive_unit
    (Nat.le_refl _)

/-- The content-trace spine-head's body frame is NOT primed: the trace
position fails MarchOK′, so the (A)-rec is unavailable there (the shape
routes to the trace chase / the named base B1). -/
theorem not_marchCtx'_trace_cons {Γ : List Ty} : ¬ MarchCtx' (Ty.trace :: Γ) := by
  intro h
  have hOK : MarchOK' Ty.trace := h 0 _ List.get?_zero_cons'
  exact not_marchOK'_trace hOK

/-! ## The routing table (w13 p22) + the break-route hypothesis (w14 round 3) -/

/-- `¬ContainsLive (arrow X σ)` decomposes EXACTLY — the routing table's
foundation: the (B′)-route at an inner killer `g : arrow W (arrow X σ)` is
available exactly when both the domain and the codomain are non-live. -/
theorem not_containsLive_arrow_iff {X σ : Ty} :
    ¬ ContainsLive (Ty.arrow X σ) ↔ (¬ ContainsLive X ∧ ¬ ContainsLive σ) := by
  constructor
  · intro h
    exact ⟨not_containsLive_arrow_dom h, not_containsLive_arrow_cod h⟩
  · rintro ⟨hX, hσ⟩ hc
    rcases containsLive_arrow.mp hc with h | h
    · exact hX h
    · exact hσ h

/-- The (B′)-route's thread: given the statement's own `¬ContainsLive σ`,
the route at the widened type is available exactly when `X` is non-live. -/
theorem bprime_route_thread {X σ : Ty} (hσ : ¬ ContainsLive σ) :
    ¬ ContainsLive (Ty.arrow X σ) ↔ ¬ ContainsLive X := by
  rw [not_containsLive_arrow_iff]
  constructor
  · exact fun h => h.1
  · intro hX
    exact ⟨hX, hσ⟩

/-- The break route's `dSupply` landing: at a primed piece the
`NeedsK`/`NeedsS` disjuncts are dead by the discipline (the `ContainsLive`
disjunct SURVIVES — see `marchOK'_codLive` below). -/
theorem supply_at_primed_is_live {Γ : List Ty} {b : Ty}
    (hΓ : MarchCtx' Γ) (hpos : ∃ (i : Nat), Γ[i]? = some b) :
    ¬ NeedsK b ∧ ¬ NeedsS b := by
  obtain ⟨i, hi⟩ := hpos
  exact ⟨marchOK'_notNeedsK (hΓ i b hi), marchOK'_notNeedsS (hΓ i b hi)⟩

/-- w14 round 3's SHOULD-FIX witness: a CODOMAIN-live arrow with inert
domain and nonpositive weights PASSES MarchOK′ — so a MarchCtx′ position
can carry `ContainsLive` via its codomain, and dSupply's ContainsLive
disjunct does NOT die at a MarchCtx′ piece. The break site names the
CONTAINSLIVE-FREE-PIECE hypothesis; the live-dSupply sub-case routes to
the corner machinery. -/
theorem codLive_CL : ContainsLive (Ty.arrow Ty.unit (Ty.arrow Ty.trace Ty.unit)) := by
  rw [containsLive_arrow]
  exact Or.inr containsLive_ATU

theorem marchOK'_codLive : MarchOK' (Ty.arrow Ty.unit (Ty.arrow Ty.trace Ty.unit)) := by
  refine ⟨⟨Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simp [binderOK, allInert]
  · intro h; exact Ty.noConfusion h
  · simp [DeepConsume, NeedsC]
  · simp [HasTokenDomain, CarriesContent, NeedsC]
  · simp [NeedsC]
  · simp [NeedsK]
  · simp [NeedsS]
  · simp [NeedsT]
  · simp only [tnet]; omega
  · simp only [snet]; omega
  · intro h
    obtain ⟨d, c, he, hl⟩ := h
    injection he with hd _
    subst hd
    exact not_containsLive_unit hl

/-! ## HScrut''' — the restated hscrut residual (the install's target shape)

The reroute's split: the unit-body case routes to the (A)-rec at the body
frame (the frame equation is rfl at the comp-carrying shape); the
arrow-body case stays residual WITH `¬ContainsLive σ′` — the known
witness's codomain `arrow ACU unit` is live, so the restated residual
excludes it. -/
def HScrut''' : Prop :=
  ∀ {Γa Γb ΓL ΓR₁ : List Ty} {a' b' σ' : Ty} {t body : Term},
    MarchCtx' ΓL → MarchCtx' ΓR₁ → MarchCtx' (b' :: a' :: Γb) →
    Typed Γa t (Ty.tensor a' b') → Typed (b' :: a' :: Γb) body σ' →
    Γa ++ Γb = ΓL ++ Ty.content :: ΓR₁ → ΓL.length < Γa.length →
    ¬ ContainsLive σ' → EndsInUnit σ' → False

/-- T3: the known hscrut witness's codomain is LIVE, so the restated
residual cannot be refuted through it. -/
theorem hscrut_witness_excluded :
    ¬ (MarchCtx' [] ∧ ¬ ContainsLive (Ty.arrow ACU Ty.unit)) :=
  fun ⟨_, h⟩ => h containsLive_killerOfKiller_cod

/-! ## The deleted-(C) spine-walk's engine set (w13 p23 — round 4)

(C) is DELETED (foldedC_refuted above); the (A)-app killer-side becomes the
spine-walk with the fire's arg in scope. The walk's pin, the break site's
LiveFree engine (w14's round-3 should-fix made precise: dSupply's
ContainsLive disjunct SURVIVES at primed pieces — marchOK'_codLive — so the
break site names the LiveFree hypothesis), and the lete arm's install shape. -/

/-- The spine-walk's pin: the (A)-app killer-side with the arg in scope —
the surgery's main piece (typed into march_block at increment B). -/
def SpineWalk : Prop :=
  ∀ (fuel : Nat) {Γ₁ Δ ΓL ΓR : List Ty} {fn arg : Term} {X : Ty}
    (hf : Typed Γ₁ fn (Ty.arrow X Ty.unit)) (ha : Typed Δ arg X),
    MarchCtx' ΓL → MarchCtx' ΓR →
    Γ₁ ++ Δ = ΓL ++ Ty.content :: ΓR → ΓL.length < Γ₁.length →
    size hf ≤ fuel → False

/-- T3: the hscrut witness's fn-shape needs an `ACU`-val at the primed `Δ`,
and `ACU` is not a primed position. -/
theorem acu_not_primed : ¬ MarchOK' ACU :=
  not_marchOK'_arrowContent Ty.unit

/-- T3: the same for `killerBinder`'s type (the codomain is live). -/
theorem killerBinder_type_not_primed : ¬ MarchOK' (Ty.arrow ACU Ty.unit) := by
  intro h
  exact h.2 ⟨ACU, Ty.unit, rfl, containsLive_ACU⟩

/-- A piece is ContainsLive-free: no position carries a live type. The
break site's hypothesis (w14's round-4: NOT derivable from MarchCtx′ —
marchOK'_codLive — so it is named, and the walk's typing carries it at the
arrow-body live-X bottom). -/
def LiveFree (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (b : Ty), Γ[i]? = some b → ¬ ContainsLive b

/-- THE BREAK SITE'S ENGINE: at a `LiveFree` primed piece, `dSupply` is
IMPOSSIBLE — the `ContainsLive` disjunct dies by freeness, the
`NeedsK`/`NeedsS` disjuncts by the discipline. So `dRoute` gives `dEscape`
or `dInert`, and the walk consumes those. -/
theorem no_dSupply_of_free {Δ : List Ty}
    (hΓ : MarchCtx' Δ) (hfree : LiveFree Δ) :
    ∀ (i : Nat) (b : Ty) (hpos : Δ[i]? = some b), ¬ Demand b := by
  intro i b hpos hd
  rcases hd with hl | hk | hs
  · exact hfree i b hpos hl
  · exact marchOK'_notNeedsK (hΓ i b hpos) hk
  · exact marchOK'_notNeedsS (hΓ i b hpos) hs

/-- The routing corollary: at a `LiveFree` primed piece, every value is
`dEscape` or `dInert` — the walk's two consumable routes. -/
theorem dRoute_escape_or_inert {Δ : List Ty} {u : Term} {X : Ty}
    (hu : Typed Δ u X) (hΓ : MarchCtx' Δ) (hfree : LiveFree Δ) :
    (LiveEscape hu ∨ FixNeedS hu) ∨ (¬ ContainsLive X ∧ ¬ NeedsK X ∧ ¬ NeedsS X) := by
  cases hd : dRoute hu with
  | dSupply i b hpos hsup huses =>
      exact absurd hsup (no_dSupply_of_free hΓ hfree i b hpos)
  | dEscape e => exact Or.inl e
  | dInert h => exact Or.inr h

/-- The `LiveFree` piece lemma: freeness is inherited by split pieces (the
walk's recursion needs it). -/
theorem liveFree_of_append_left {Γ Δ : List Ty} (h : LiveFree (Γ ++ Δ)) :
    LiveFree Γ := by
  intro i b hpos
  exact h i b (by rw [List.get?_append_lt (by
    have := List.get?_some_lt hpos; omega)]; exact hpos)

/-- The lete arm's install shape: at the (A)-app's lete arm with the token
in the scrutinee's piece, HScrut''' applies with `σ′ = unit` (both
`¬ContainsLive unit` and `EndsInUnit unit` hold). -/
theorem hscrut_install_shape {Γa Γb ΓL ΓR₁ : List Ty} {a' b' : Ty}
    {t body : Term}
    (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR₁)
    (hΓb : MarchCtx' (b' :: a' :: Γb))
    (ht : Typed Γa t (Ty.tensor a' b'))
    (hb : Typed (b' :: a' :: Γb) body Ty.unit)
    (heq : Γa ++ Γb = ΓL ++ Ty.content :: ΓR₁)
    (htok : ΓL.length < Γa.length)
    (h : HScrut''') : False :=
  h hL hR hΓb ht hb heq htok not_containsLive_unit
    (by unfold EndsInUnit; trivial)

/-! ## The round-5 crop: the walk's inner statement + the regime split
(w13 p24, w14 round 5 — the increment-B consult converged)

THE INNER STATEMENT IS σ-GENERALIZED and NOT (C)-shaped — because it
carries the ARG. (C)'s refutation (foldedC_refuted) does not apply: (C)
is a statement about a killer ALONE, and a killer alone can be a closed
value at a vacuously-disciplined frame. The walk's statement carries
`hu : Typed Γu u W`, so the killer is FIRED — and its arg would need an
ACU-val at a primed piece (blocked). The telescope's σ is a VARIABLE,
never a hypothesis; no predicate is preserved under widening, so p17's
impossibility cannot bite.

THE REGIME SPLIT (w14 round 5): a token-carrying piece is NOT LiveFree
(the token position is live) — the two break regimes are DISJOINT.
Token-carrying pieces route dSupply-on-the-token into the march's own
arg-side spend analysis (hdeepArg's shape); the LiveFree engine applies
only at token-free pieces (the killer-side break). No cycle is possible:
every walk descent is a direct premise (size strictly drops,
equation-compiler-enforced). -/

/-- The walk's inner statement: the σ-generalized spine head WITH THE ARG.
`σ` is a variable (the telescope's carriage), never a hypothesis. The
walk's proof takes the residual layer as hypotheses (the dEscape routes
per w14's P4/P5: the spine head can stall into the (D)-machinery). -/
def SpineWalkGen : Prop :=
  ∀ (fuel : Nat) {Γg Γu ΓL ΓR : List Ty} {g u : Term} {W σ : Ty}
    (hg : Typed Γg g (Ty.arrow W σ)) (hu : Typed Γu u W),
    MarchCtx' ΓL → MarchCtx' ΓR →
    Γg ++ Γu = ΓL ++ Ty.content :: ΓR → ΓL.length < Γg.length →
    size hg ≤ fuel → False

/-- The (A)-root's call: the root's `hf : Γ₁ ⊢ arrow X unit` and `ha` are
exactly the inner statement at `σ := unit`. -/
theorem spineWalkGen_at_unit {fuel : Nat} {Γ₁ Δ ΓL ΓR : List Ty}
    {fn arg : Term} {X : Ty}
    (hf : Typed Γ₁ fn (Ty.arrow X Ty.unit)) (ha : Typed Δ arg X)
    (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR)
    (heq : Γ₁ ++ Δ = ΓL ++ Ty.content :: ΓR) (htok : ΓL.length < Γ₁.length)
    (hsz : size hf ≤ fuel) (h : SpineWalkGen) : False :=
  h fuel hf ha hL hR heq htok hsz

/-- The spine recursion's call: at `fn = app g u` the walk continues at
`(g, u, W, arrow X unit)` — the SAME statement, the telescope widened. -/
theorem spineWalkGen_spine_step {fuel : Nat} {Γg Γu ΓL ΓR : List Ty}
    {g u : Term} {W X : Ty}
    (hg : Typed Γg g (Ty.arrow W (Ty.arrow X Ty.unit))) (hu : Typed Γu u W)
    (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR)
    (heq : Γg ++ Γu = ΓL ++ Ty.content :: ΓR) (htok : ΓL.length < Γg.length)
    (hsz : size hg ≤ fuel) (h : SpineWalkGen) : False :=
  h fuel hg hu hL hR heq htok hsz

/-- T3: the hscrut fn-shape at a spine node needs an `ACU`-val at the
primed `Δ` — and `ACU` is not a primed position. -/
theorem hscrut_spine_node_blocked : ¬ MarchOK' ACU :=
  not_marchOK'_arrowContent Ty.unit

/-- T3: the killerBinder spine: same type, same block (the codomain is
live). -/
theorem killerBinder_spine_blocked : ¬ MarchOK' (Ty.arrow ACU Ty.unit) := by
  intro h
  exact h.2 ⟨ACU, Ty.unit, rfl, containsLive_ACU⟩

/-- THE REGIME SPLIT (w14 round 5, kernel): a mid-token piece is NOT
LiveFree — the token position is live. The LiveFree engine is never
invoked at a token-carrying piece; there, dSupply fires ON the token and
routes into the march's own arg-side spend analysis. -/
theorem midToken_not_liveFree {Γ : List Ty} (h : MidToken Γ) : ¬ LiveFree Γ := by
  obtain ⟨ΓL, ΓR, heq⟩ := h
  intro hfree
  have hpos : Γ[ΓL.length]? = some Ty.content := by rw [heq]; exact frame_token
  exact hfree ΓL.length Ty.content hpos containsLive_content

/-- The token-side form of the same fact (w13 p24): the frame's own
concatenation is not LiveFree. -/
theorem not_liveFree_of_token {ΓL ΓR : List Ty} :
    ¬ LiveFree (ΓL ++ Ty.content :: ΓR) := by
  intro h
  have hpos : (ΓL ++ Ty.content :: ΓR)[ΓL.length]? = some Ty.content := by
    rw [List.get?_append_ge (Nat.le_refl _), Nat.sub_self]
    rfl
  exact h ΓL.length Ty.content hpos containsLive_content

/-- The LiveFree engine's home is satisfiable (the empty piece). -/
theorem liveFree_nil : LiveFree [] := by
  intro i b hpos
  rw [List.get?_nil'] at hpos
  contradiction

/-- w14 round 5's P5: at a LiveFree primed piece, an ACU-val is
dEscape-ONLY (dInert impossible — ACU is live; dSupply dead by the
engine). The killerBinder spine stalls only into the (D)-machinery's
dEscape route at the OUTER arg — a named residual route, not a cycle. -/
theorem acu_val_escape_only {Δ : List Ty} {u : Term} (hu : Typed Δ u ACU)
    (hΓ : MarchCtx' Δ) (hfree : LiveFree Δ) :
    LiveEscape hu ∨ FixNeedS hu := by
  rcases dRoute_escape_or_inert hu hΓ hfree with h | h
  · exact h
  · exact absurd containsLive_ACU h.1

/-! ### The arg-side three-way W-split (w13 p24) -/

/-- (i) `W = content`: the (B′)-route's guard is satisfied. -/
theorem wsplit_content_guard :
    (Ty.content = Ty.content ∨ ∃ a', Ty.content = Ty.later a') :=
  Or.inl rfl

/-- (i) `W = content`: `DeepConsume (arrow content σ)` holds by the domain. -/
theorem wsplit_content_deepConsume (σ : Ty) :
    DeepConsume (Ty.arrow Ty.content σ) :=
  Or.inl (Or.inl rfl)

/-- (ii) `W = later a`: `DeepConsume (arrow (later a) σ)` is EXACTLY
`DeepConsume σ` — `later` is predicate-opaque (`NeedsC (later a) = False`,
`DeepConsume (later a) = False`). -/
theorem wsplit_later_deepConsume {a σ : Ty} :
    DeepConsume (Ty.arrow (Ty.later a) σ) ↔ DeepConsume σ := by
  constructor
  · intro h
    unfold DeepConsume at h
    rcases h with h | h
    · rcases h with h | h | h
      · exact absurd h (by intro hc; cases hc)
      · cases h
      · cases h
    · exact h
  · intro h
    exact Or.inr h

/-- (ii) The later arm is SELF-DEAD at the (B′)-route: `DeepConsume σ`
plus the caller's `¬ContainsLive σ` is a contradiction (`laterDom_dead`). -/
theorem wsplit_later_dead {a σ : Ty}
    (h : DeepConsume (Ty.arrow (Ty.later a) σ)) (hnl : ¬ ContainsLive σ) : False :=
  laterDom_dead h hnl

/-- (iii) The thread: the (B′)-route at `g` is available exactly when
`¬ContainsLive X` (the landed `bprime_route_thread` at `σ := unit`). -/
theorem wsplit_thread {X : Ty} (hX : ¬ ContainsLive X) :
    ¬ ContainsLive (Ty.arrow X Ty.unit) :=
  (bprime_route_thread not_containsLive_unit).mpr hX

/-! ## w13's post-install verification (p26) — the T3 records

(A) hLamArrow's token-side exclusion of the killerBinder spine —
CONFIRMED at the kernel: consumerFire's spine decomposition puts Γg = []
and Γu = [content], so the token is ARG-side and hLamArrow's
`ΓL.length < Γg.length` is `|ΓL| < 0` — FALSE. The one legal spine head
cannot instantiate the eleventh residual.

(B) The restated hcompK is SAFE, with a mechanism correction recorded
for the pricing sweep: the CONTENT-comp arm is the multi-token base (a
content comp forces a CSupply position in the scrutinee's piece, and at
a primed position CSupply implies the position IS content); the
NON-content-comps arm is NOT the multi-token base — it is the (A)-shape
at the body's frame (`(X :: b' :: a' :: Γb) ⊢ unit` with the token in
Γb), priced by the march (A) in the sweep, not by the multi-token
machinery. No in-tree witness reaches either arm at a one-content frame
(the natural bodies fail: the inner frames have no arrow-typed position
and killerBinder's ACU cannot be lifted past the linear content). -/

/-- The token-side condition at consumerFire's shape is unsatisfiable
(Γg = [] — the token is arg-side). -/
theorem consumerFire_not_fn_side {ΓL : List Ty} :
    ¬ (ΓL.length < ([] : List Ty).length) := by
  rw [List.length_nil]
  omega

/-- At a PRIMED position, `CSupply` implies the position IS `content`:
`NeedsK`/`NeedsS` are banned by the discipline, and `NeedsC` only holds
for `content` (`marchOK_notNeedsC`). The exact content of the
two-content claim: a content COMP needs a content position in the
scrutinee's piece. -/
theorem primed_csupply_is_content {b : Ty} (h : MarchOK' b) (hcs : CSupply b) :
    b = Ty.content := by
  have hK : ¬ NeedsK b := marchOK'_notNeedsK h
  rcases hcs with hC | hK'
  · by_cases hb : b = Ty.content
    · exact hb
    · exact absurd hC (marchOK_notNeedsC h.1 hb)
  · exact absurd hK' hK

/-! ## The lam-arrow case's routing table (w13 p25 — increment B's last pin)

At the walk's node with `g = λ(W).body'`, `body' : (W :: Γg) ⊢ arrow X' σ'`
(the walk's arg `u : Γu ⊢ W` in scope, the token in Γg): the walk carries
NO σ-predicate, so the (B′)-route at the λ is unavailable here; the move
is `dRoute` at `u`. THE by_cases: token fn-side → dRoute at hu (dSupply =
the LIVE-SUPPLY RESIDUAL below; dEscape = the (D)-machinery's named
routes; dInert = the body-entry); token arg-side → hdeepArg.

THE KEY FACT: every primed position has tnet ≤ 0, while corner_piece
needs tnet b > 0 — the corner machinery can NEVER take a primed piece's
position. dSupply-live at a primed Γu is therefore NOT corner territory:
it is a NAMED RESIDUAL (LiveSupplyAtArg), whose content instance IS the
multi-token base and whose trace/stream instances are the standing
position bases. THE UNIQUE-CONTENT RESTRICTION (obs 183-α) WOULD NOT
PRICE IT: the march's own λ(content)-body recursion creates two-content
frames ((content :: ΓL) ++ content :: ΓR₁), so the restriction would
break the internal recursion — naming is forced. -/

/-- EVERY primed position has `tnet ≤ 0` — so `corner_piece`'s `tnet b > 0`
hypothesis can never be met at a primed piece. This is why dSupply-live at a
primed piece is NOT corner-machinery territory. -/
theorem primed_tnet_nonpos {b : Ty} (h : MarchOK' b) : tnet b ≤ 0 :=
  h.1.2.1

/-- And the same for snet. -/
theorem primed_snet_nonpos {b : Ty} (h : MarchOK' b) : snet b ≤ 0 :=
  h.1.2.2

/-- The content case: `ContainsLive content` with `tnet content = 0` — the
live-supply residual's simplest instance, and the multi-token base's shape. -/
theorem content_live_tnet_zero : ContainsLive Ty.content ∧ tnet Ty.content = 0 :=
  ⟨containsLive_content, rfl⟩

/-- THE ELEVENTH NAMED RESIDUAL: no live position at the arg piece is spent
by the arg, at a token-fn-side primed frame. At `b = content` this is the
multi-token base; at `b = trace`/`stream` (or any live position with
`tnet ≤ 0` — the `marchOK'_codLive` family) the standing position bases.
Unfalsified (the simplest instance needs a killer at a two-content frame —
no construction from the in-tree witnesses reaches it) and unpriced (the
unique-content restriction would break the march's internal recursion). -/
def LiveSupplyAtArg : Prop :=
  ∀ {Γg Γu ΓL ΓR : List Ty} {g u : Term} {W σ : Ty}
    (hg : Typed Γg g (Ty.arrow W σ)) (hu : Typed Γu u W),
    MarchCtx' ΓL → MarchCtx' ΓR →
    Γg ++ Γu = ΓL ++ Ty.content :: ΓR → ΓL.length < Γg.length →
    (∃ (i : Nat) (b : Ty), Γu[i]? = some b ∧ ContainsLive b ∧ uses hu i ≥ 1) →
    False

/-- The residual's content instance is the multi-token shape: a second
`content` position in the arg piece. -/
theorem liveSupply_content_shape {Γu : List Ty} {i : Nat}
    (hpos : Γu[i]? = some Ty.content) : ContainsLive Ty.content :=
  containsLive_content

/-! ## The (β)-dead witnesses + the weight-free peel pin (w13 p14)

EndsInUnit is a SHAPE class; the weights are unbounded inside it
in both directions — the two double-domain witnesses. The relaxed
peel (KillerPeelNoWeights) drops the weight hypotheses at the cost of
exactly ONE structural residual (HFixPayload: the fix-arm positive-
weight payload, where the modality discipline genuinely has nothing
to say). -/


/-! ## (β)'s death, kernel -/

theorem endsInUnit_doubleDomain_trace : EndsInUnit (Ty.arrow (Ty.arrow Ty.trace Ty.unit) Ty.unit) := by
  unfold EndsInUnit
  trivial

theorem tnet_unbounded_in_endsInUnit :
    tnet (Ty.arrow (Ty.arrow Ty.trace Ty.unit) Ty.unit) = 1 := by
  simp only [tnet]; omega

theorem snet_unbounded_in_endsInUnit :
    snet (Ty.arrow (Ty.arrow Ty.stream Ty.unit) Ty.unit) = 1 := by
  simp only [snet]; omega

theorem endsInUnit_doubleDomain_stream : EndsInUnit (Ty.arrow (Ty.arrow Ty.stream Ty.unit) Ty.unit) := by
  unfold EndsInUnit
  trivial

/-- The two facts that (β) would need and cannot have: an EndsInUnit type
whose weights violate the (B′)-hypotheses. -/
theorem beta_dead :
    EndsInUnit (Ty.arrow (Ty.arrow Ty.trace Ty.unit) Ty.unit)
      ∧ ¬ (tnet (Ty.arrow (Ty.arrow Ty.trace Ty.unit) Ty.unit) ≤ 0) := by
  refine ⟨endsInUnit_doubleDomain_trace, ?_⟩
  rw [tnet_unbounded_in_endsInUnit]
  omega

/-! ## The residual (α) needs, pinned

A fix node whose payload carries a positive weight: the `▷a` binder is not
`MarchOK'`-able, so `marchOK_later′` cannot be called and the frame inside
the fix body is not re-established. NOT proven false — named. -/

/-- The (B′)-relaxed shape: no weight hypotheses on the codomain, and the
fix-at-positive-weight case as a named residual. This is the shape the
(C)-app arg-side needs (its codomain `arrow X σ` carries only
`EndsInUnit σ`). -/
def KillerPeelNoWeights (hfix : Prop) : Prop :=
  ∀ (fuel : Nat) (Γ : List Ty), MarchCtx' Γ →
    ∀ (X σ : Ty), DeepConsume (Ty.arrow X σ) →
    (X = Ty.content ∨ ∃ a', X = Ty.later a') → MarchOK' X →
    EndsInUnit σ →
    ∀ (fn : Term) (h : Typed Γ fn (Ty.arrow X σ)), size h ≤ fuel → False

/-- The residual's pin (a shape, not a proof): the fix-arm's frame is
unreconstructable when the payload's weights are positive. -/
def HFixPayload : Prop :=
  ∀ {Γ : List Ty} {a : Ty} {body : Term} (hΓ : AllNonLinear Γ)
    (h : Typed Γ body (Ty.arrow (Ty.later a) a)),
    MarchCtx' Γ → (0 < tnet a ∨ 0 < snet a) →
    ¬ MarchOK' (Ty.later a) → False

/-! ## The origin-arg threading (interval 18)

The walk's spine recursion DROPS the entry arg — it carries only the
current spine level's arg, so at spine depth ≥ 1 the refuter (W1/W2/W3
generalized: the produce chain grows one λ-level per spine step, the ACU
at the innermost level, FRESH unit args at each) can supply every
walk-site datum that does not reach the ORIGIN's arg. The threading: the
walk's statement carries the ENTRY ARG as fixed data (`horg`, at the
entry fire's arg piece — primed, token-free) plus the TELESCOPE
INVARIANT (`BottomsAt (arrow W σ) Xo`: the walked node's type is an
arrow-chain whose innermost arrow is `arrow Xo unit` — INVARIANT across
the spine recursion, each step adding one OUTER domain; contr/weak
preserve the walked node's type outright).

The refuter's obligation the invariant surfaces (the T3 sweep,
`/tmp/probe/fp16_att.lean`): an Xo-VAL at a primed token-free piece —
Xo := ACU (the W1/W2 family) is the (B′)-regress (the peel kills the
ACU-val at any primed piece); Xo := unit (the INERT-LIFT family the
record's hunts missed: the closed unit and AUU-reading vars weak-lift
past the non-linear `AUU = arrow unit unit`, which is MarchOK') dies at
the SCRUTINEE/BODY comps-frames — the token is LINEAR, lifts cross
non-linear positions only, vars are singleton-only. Both obligations are
documented dead steps, not proven impossibilities: the residuals stay
named. -/

/-- The walked node's type is an arrow-chain whose innermost arrow is
`arrow Xo unit`. At the walk's entry the walked node IS `arrow X unit`,
so `Xo := X`; each spine step wraps the telescope in one outer domain. -/
def BottomsAt : Ty → Ty → Prop
  | .arrow a b, Xo => (a = Xo ∧ b = Ty.unit) ∨ BottomsAt b Xo
  | _, _ => False

/-- The entry supply: the walked node `arrow X unit` bottoms at `X`. -/
theorem bottomsAt_entry (X : Ty) : BottomsAt (Ty.arrow X Ty.unit) X :=
  Or.inl ⟨rfl, rfl⟩

/-- The spine-step preservation: one outer domain preserves the bottom.
contr/weak preserve the walked node's type outright, so the invariant
threads those arms verbatim. -/
theorem bottomsAt_spine {W W₂ σ Xo : Ty} (h : BottomsAt (Ty.arrow W σ) Xo) :
    BottomsAt (Ty.arrow W₂ (Ty.arrow W σ)) Xo :=
  Or.inr h

/-! ## The pricing sweep (interval 18, unit 2)

The thirteen residuals against the chases' twenty: NO direct matches
(the march's configs are genuinely fix-full-grain — shape-by-shape
compared against both chase statements), so the pricing is BY MAP: every
residual routes to one of FIVE named bases or a proven sub-route, and
the layer's obligations REDUCE rather than list. THE FIVE BASES:
BASE-1 MULTI-TOKEN (`[content, content] ⊢ unit` and its C⊗C twin — the
produce-frame pair; UNDERIVED; the fallback is the unique-content
restriction); BASE-2 the ▷trace-killer/trace-stuckness regress; BASE-3
the (▷stream)-with-token restatement; BASE-4 the INERT-LIFT base
(unit-vals at token-carrying comps-frames — the interval-18 find);
BASE-5 the COMPONENT-GRAIN WALK (the token inside a pair/lete
component; the comp-is-token sub-case prices to the (A)-rec but the
deep case remains). THE MAP: hlamDom → dRoute-at-hu (dSupply-live →
BASE-1-family; dEscape-mints → BASE-2/3; dEscape-gen → DEAD below;
dEscape-fix → hfix; dEscape-binders → the peel regress; dInert → the
body-entry); hspine → the killer-of-killer regress at primed; hscrutA/
hscrutW → BASE-5 (+BASE-4 at Xo := unit); hcompK → BASE-1 (content-comp)
/ the (A)-shape at the body's frame; hdeepArgA/hdeepArgW → the X-class
bases (unit → BASE-4; trace/stream → BASE-2/3; live → BASE-1-family);
hLamArrow → dRoute-at-u (the same dEscape table — the lam-arrow case is
genuinely residual: the λ's body is the NEXT killer, whose arg is not
in scope); hcomp → the (A)-shape at the body's frame plus the
strengthening gap (unread non-MarchOK' comps); hcontrHead → BASE-2 (the
knower-frame terminate-mint→snoc→trace-stuck route); hpeelLam/
hpeelLete → the closed-killer regress (the (B')-claim itself at the
failing hrec); hfix → the ▷-stack live-payload regress. NO SIGNATURE
SHRINKS: every residual bottoms at a named base; the interval-17/18 T3
rounds stand (none is refutable at the repaired shapes). -/

/-- The sweep's one kernel-new PROVEN route: a knower-val at a primed
piece is impossible (kprop forces a NeedsK-supplying position; the
discipline bans it). This kills the dEscape-genHere route at primed
pieces — `gen` is a CLOSED constant at `[]` (Typing.lean), so the node
is legal everywhere but its FIRE needs a knower-arg, which is dead at
primed pieces. -/
theorem knower_arg_dead_at_primed {Δ : List Ty} {u : Term}
    (hΓ : MarchCtx' Δ) (h : Typed Δ u Ty.knower) : False := by
  obtain ⟨i, b, hpos, hK⟩ := kprop h (by simp [NeedsK])
  exact marchOK'_notNeedsK (hΓ i b hpos) hK

/-- The X-class generalization: any NeedsK-carrying X-val at a primed
piece is dead (the same kprop route — this is the C⊗C-producer's
knower-domain fire-kill and the hcontrHead heads' supplier-kill). -/
theorem needsK_val_dead_at_primed {Δ : List Ty} {X : Ty} {u : Term}
    (hΓ : MarchCtx' Δ) (hK : NeedsK X) (h : Typed Δ u X) : False := by
  obtain ⟨i, b, hpos, hKb⟩ := kprop h hK
  exact marchOK'_notNeedsK (hΓ i b hpos) hKb

/-! ### The C⊗C march's T3 facts (S7's ground, kernel-checked)

The first draft's key fact — "a C⊗C-producer arrow is never a primed
position" — was FALSIFIED at the kernel: `arrow knower (C⊗C)` PASSES
`MarchOK'` (the coalgebra family, ledger #70). The CORRECTED fact: a
primed-legal C⊗C-producer's domain is (NeedsC ∨ NeedsK)-CARRYING
(`marchOK'_cxC_dom` — via D2's `¬NeedsC` conjunct: `NeedsC (arrow X
σ) = NeedsC σ ∧ ¬NeedsC X ∧ ¬NeedsK X` with `NeedsC (C⊗C) = True`, so
D2-survival requires the disjunction on the domain). BOTH disjuncts die
at the produce's FIRE (the arg is an X-val at a primed token-free
piece): `NeedsK X` → `needsK_val_dead_at_primed` (DEAD); `NeedsC X` →
cprop → a CSupply position → primed ⇒ the position IS content
(`primed_csupply_is_content`) → the piece carries a SECOND content —
BASE-1 exactly (the produce-frame multi-token demand, witnessed by
`multiTokenPair` at the two-content frame). Every C⊗C-producer is
therefore CONSTRUCTED (var-supplied producers are dead or based), and
its body is PAIR-HEADED (pair is the only tensor intro), whose split
puts the non-token component at a token-free primed piece — the same
BASE-1/`no_closed_content` pair-analysis. -/

/-- The corrected key fact. -/
theorem marchOK'_cxC_dom {X : Ty}
    (h : MarchOK' (Ty.arrow X (.tensor Ty.content Ty.content))) :
    NeedsC X ∨ NeedsK X := by
  rcases h.1.1 with hb | hD2
  · exfalso
    unfold binderOK at hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with hc | hi
    · exact Ty.noConfusion hc
    · simp only [allInert, Bool.false_and, Bool.and_false] at hi
      cases hi
  · refine Classical.byContradiction fun hnk => ?_
    have hnc : ¬ NeedsC X := fun hc => hnk (Or.inl hc)
    have hnK : ¬ NeedsK X := fun hk => hnk (Or.inr hk)
    have hNC : NeedsC (Ty.arrow X (.tensor Ty.content Ty.content)) :=
      ⟨(Or.inl trivial), hnc, hnK⟩
    exact hD2.2.2.2.2.1 hNC

/-- The produce's knower-domain FIRE is dead at primed pieces. -/
theorem cxC_fire_needsK_dead {Δ : List Ty} {X : Ty} {u : Term}
    (hΓ : MarchCtx' Δ) (hK : NeedsK X) (h : Typed Δ u X) : False :=
  needsK_val_dead_at_primed hΓ hK h

/-- BASE-1's C⊗C witness at the two-content frame: the produce-frame
pair is legal exactly when the frame carries a second content. -/
def multiTokenPair : Typed [Ty.content, Ty.content]
    (.pair (.var 0) (.var 0)) (.tensor Ty.content Ty.content) :=
  Typed.pair (Γ := [Ty.content]) (Δ := [Ty.content])
    Typed.var Typed.var rfl


theorem march_block
    (hlamDom : ∀ {Γg Γu ΓL ΓR₃ : List Ty} {W : Ty} {body u : Term},
        MarchCtx' ΓL → MarchCtx' ΓR₃ → MarchCtx' Γu →
        ¬ MarchOK' W →
        Typed (W :: Γg) body Ty.unit → Typed Γu u W →
        Γg = ΓL ++ Ty.content :: ΓR₃ → False)
    (hspine : ∀ {Γ Γg Γu : List Ty} {W X σ : Ty} {g u : Term},
        MarchCtx' Γ → DeepConsume (Ty.arrow X σ) → (X = Ty.content ∨ ∃ a', X = Ty.later a') →
        MarchOK' X →
        EndsInUnit σ → ¬ ContainsLive σ →
        Typed Γg g (Ty.arrow W (Ty.arrow X σ)) → Typed Γu u W → False)
    (hscrutA : ∀ {Γa Γb ΓL ΓR₁ : List Ty} {a' b' σ' : Ty} {t body : Term},
        MarchCtx' ΓL → MarchCtx' ΓR₁ →
        Typed Γa t (Ty.tensor a' b') → Typed (b' :: a' :: Γb) body σ' →
        Γa ++ Γb = ΓL ++ Ty.content :: ΓR₁ → ΓL.length < Γa.length →
        EndsInUnit σ' → ¬ ContainsLive σ' → False)
    (hscrutW : ∀ {Γa Γb ΓL ΓR₁ Γo : List Ty} {a' b' σ' Xo : Ty} {t body uo : Term},
        MarchCtx' ΓL → MarchCtx' ΓR₁ → MarchCtx' Γo →
        Typed Γa t (Ty.tensor a' b') → Typed (b' :: a' :: Γb) body σ' →
        Γa ++ Γb = ΓL ++ Ty.content :: ΓR₁ → ΓL.length < Γa.length →
        BottomsAt σ' Xo → Typed Γo uo Xo → False)
    (hcompK : ∀ {Γb ΓL'' ΓR₁ : List Ty} {b' a' X σ : Ty} {body : Term},
        MarchCtx' ΓL'' → MarchCtx' ΓR₁ →
        Typed (b' :: a' :: Γb) body (Ty.arrow X σ) →
        Γb = ΓL'' ++ Ty.content :: ΓR₁ →
        EndsInUnit σ → False)
    (hdeepArgA : ∀ {Γ₁ ΓL'' ΓR : List Ty} {X : Ty} {fn arg : Term},
        MarchCtx' Γ₁ → X ≠ Ty.content →
        Typed Γ₁ fn (Ty.arrow X Ty.unit) →
        Typed (ΓL'' ++ Ty.content :: ΓR) arg X → False)
    (hdeepArgW : ∀ {Γ₁ ΓL'' ΓR Γo : List Ty} {W₂ σ Xo : Ty} {fn arg uo : Term},
        MarchCtx' Γ₁ → MarchCtx' Γo →
        Typed Γ₁ fn (Ty.arrow W₂ σ) →
        BottomsAt (Ty.arrow W₂ σ) Xo → Typed Γo uo Xo →
        Typed (ΓL'' ++ Ty.content :: ΓR) arg W₂ → False)
    (hLamArrow : ∀ {Γg Γu ΓL ΓR : List Ty} {body u : Term} {W X' σ' : Ty},
        MarchCtx' ΓL → MarchCtx' ΓR →
        Γg ++ Γu = ΓL ++ Ty.content :: ΓR → ΓL.length < Γg.length →
        Typed (W :: Γg) body (Ty.arrow X' σ') →
        EndsInUnit σ' →
        Typed Γu u W → False)
    (hcomp : ∀ {Γ₁ Γ₂ ΓL ΓR : List Ty} {a b : Ty} {t body : Term},
        MarchCtx' ΓL → MarchCtx' ΓR →
        Typed Γ₁ t (Ty.tensor a b) → Typed (b :: a :: Γ₂) body Ty.unit →
        Γ₁ ++ Γ₂ = ΓL ++ Ty.content :: ΓR → ¬(MarchOK' b ∧ MarchOK' a) → False)
    (hcontrHead : ∀ {a : Ty} {ΓL' ΓR : List Ty} {t : Term} {Γf : List Ty},
        a.isLinear = false → ¬MarchOK' a →
        Typed (a :: a :: Γf) t Ty.unit → Γf = ΓL' ++ Ty.content :: ΓR → False)
    (hpeelLam : ∀ {Γ : List Ty} {X σ : Ty} {body : Term},
        MarchCtx' Γ → DeepConsume (Ty.arrow X σ) → (X = Ty.content ∨ ∃ a', X = Ty.later a') →
        MarchOK' X →
        EndsInUnit σ → ¬ ContainsLive σ → Typed (X :: Γ) body σ → False)
    (hpeelLete : ∀ {Γ Γb : List Ty} {X σ y x : Ty} {fn : Term},
        MarchCtx' Γ → DeepConsume (Ty.arrow X σ) → (X = Ty.content ∨ ∃ a', X = Ty.later a') →
        MarchOK' X →
        EndsInUnit σ → ¬ ContainsLive σ →
        Typed (y :: x :: Γb) fn (Ty.arrow X σ) → ¬(MarchOK' y ∧ MarchOK' x) → False)
    (hfix : ∀ {Γ : List Ty} {a : Ty} {body : Term},
        MarchCtx' Γ → DeepConsume (Ty.arrow (Ty.later a) a) →
        EndsInUnit a → Typed Γ body (Ty.arrow (Ty.later a) a) →
        (0 < tnet a ∨ 0 < snet a ∨ ¬ MarchOK' a) → False) :
    (∀ fuel (Γ ΓL ΓR : List Ty), MarchCtx' ΓL → MarchCtx' ΓR →
      Γ = ΓL ++ Ty.content :: ΓR →
      ∀ {t : Term} (h : Typed Γ t Ty.unit), size h ≤ fuel → False)
    ∧
    (∀ fuel (Γ : List Ty), MarchCtx' Γ →
      ∀ (X σ : Ty), DeepConsume (Ty.arrow X σ) → (X = Ty.content ∨ ∃ a', X = Ty.later a') →
      MarchOK' X →
      EndsInUnit σ → ¬ ContainsLive σ →
      ∀ (fn : Term) (h : Typed Γ fn (Ty.arrow X σ)), size h ≤ fuel → False) := by
  have hmain : ∀ fuel,
      (∀ (Γ ΓL ΓR : List Ty), MarchCtx' ΓL → MarchCtx' ΓR →
        Γ = ΓL ++ Ty.content :: ΓR →
        ∀ {t : Term} (h : Typed Γ t Ty.unit), size h ≤ fuel → False)
      ∧
      (∀ (Γ : List Ty), MarchCtx' Γ →
        ∀ (X σ : Ty), DeepConsume (Ty.arrow X σ) → (X = Ty.content ∨ ∃ a', X = Ty.later a') →
        MarchOK' X →
        EndsInUnit σ → ¬ ContainsLive σ →
        ∀ (fn : Term) (h : Typed Γ fn (Ty.arrow X σ)), size h ≤ fuel → False)
      ∧
      (∀ (Γg Γu ΓL ΓR Γo : List Ty), MarchCtx' ΓL → MarchCtx' ΓR →
        Γg ++ Γu = ΓL ++ Ty.content :: ΓR → ΓL.length < Γg.length →
        MarchCtx' Γo →
        ∀ (uo : Term) (Xo : Ty), Typed Γo uo Xo →
        ∀ (g u : Term) (W σ : Ty) (hg : Typed Γg g (Ty.arrow W σ))
          (hu : Typed Γu u W),
        BottomsAt (Ty.arrow W σ) Xo → EndsInUnit σ → size hg ≤ fuel → False) := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
        constructor
        · -- (A) the march at fuel
          intro Γ ΓL ΓR hL hR heq t h hsz
          cases h with
          | @app E Γ₁ Δ X b fn arg hf ha hs =>
              by_cases htok : ΓL.length < Γ₁.length
              · -- the killer-side: the killer carries the token — the
                -- SPINE WALK (the deleted-(C) replacement) at the fire's
                -- whole context, the arg in scope; the ENTRY ARG threads
                -- (Γo := Δ, Xo := X, hbot := the entry telescope)
                have hlt : size hf < fuel := by rw [size_app] at hsz; omega
                obtain ⟨ΓR₃, hΓ₁e, hrestΔ⟩ :=
                  append_cancel_left ΓL Γ₁ Δ Ty.content ΓR (hs.trans heq) htok
                have hΓΔ : MarchCtx' Δ := by
                  have := hR; rw [hrestΔ] at this; exact marchCtx'_piece_right this
                exact (ih (size hf) hlt).2.2 Γ₁ Δ ΓL ΓR Δ hL hR (hs.trans heq) htok
                  hΓΔ arg X ha fn arg X Ty.unit hf ha (bottomsAt_entry X)
                  (by unfold EndsInUnit; trivial)
                  (by rw [size_app] at hsz; omega)
              · -- the arg-side: the token is in Δ
                obtain ⟨ΓL'', hrest, hΓL'⟩ :=
                  append_cancel_right ΓL Γ₁ Δ Ty.content ΓR (hs.trans heq) (Nat.not_lt.mp htok)
                have hL' : MarchCtx' (Γ₁ ++ ΓL'') := by rw [← hΓL']; exact hL
                have hΓ₁ : MarchCtx' Γ₁ := marchCtx'_piece_left hL'
                by_cases hXc : X = Ty.content
                · -- the killer's domain is content — the (B')-peel applies
                  -- UNCONDITIONALLY (w14-certified: the ΓL''=[] conjunct was
                  -- vestigial; (B')'s statement never mentions the token's
                  -- position in the arg's frame)
                  subst hXc
                  have hlt : size hf < fuel := by rw [size_app] at hsz; omega
                  exact (ih (size hf) hlt).2.1 Γ₁ hΓ₁ Ty.content Ty.unit
                    (by unfold DeepConsume; exact Or.inl (Or.inl rfl))
                    (Or.inl rfl) marchOK'_content
                    (by unfold EndsInUnit; trivial) not_containsLive_unit fn hf
                    (by rw [size_app] at hsz; omega)
                · -- the token rides deeper in the argument, the killer's
                  -- domain is NOT content — the deep-arg config, at the
                  -- UNIT-CODOMAIN specialization (the (A)-conclusion
                  -- forces `fn : arrow X unit`, which W1/W3 — chain
                  -- codomains — cannot instantiate)
                  exact hdeepArgA hΓ₁ hXc hf (by simpa only [hrest] using ha)
          | @lete E Γ₁ Γ₂ a b c t' body ht hb hs =>
              by_cases htok : ΓL.length < Γ₁.length
              · obtain ⟨ΓR₁, hΓ₁, hrest⟩ :=
                  append_cancel_left ΓL Γ₁ Γ₂ Ty.content ΓR (hs.trans heq) htok
                -- the (A)-conclusion forces the body's type `unit`, which
                -- is not live — the LIVENESS shape excludes W2
                exact hscrutA hL hR ht hb (hs.trans heq) htok
                  (by unfold EndsInUnit; trivial) not_containsLive_unit
              · obtain ⟨ΓL'', hrest, hΓL'⟩ :=
                  append_cancel_right ΓL Γ₁ Γ₂ Ty.content ΓR (hs.trans heq) (Nat.not_lt.mp htok)
                by_cases hba : MarchOK' b ∧ MarchOK' a
                · have hlt : size hb < fuel := by rw [size_lete] at hsz; omega
                  have hΓL'' : MarchCtx' ΓL'' := marchCtx'_piece_right (by rw [← hΓL']; exact hL)
                  have heq' : b :: a :: Γ₂ = (b :: a :: ΓL'') ++ Ty.content :: ΓR := by
                    rw [hrest]; rfl
                  exact (ih (size hb) hlt).1 (b :: a :: Γ₂)
                    (b :: a :: ΓL'') ΓR (marchCtx'_cons hba.1 (marchCtx'_cons hba.2 hΓL'')) hR
                    heq' hb (by rw [size_lete] at hsz; omega)
                · exact hcomp hL hR ht hb (hs.trans heq) hba
          | @fix Γ' a' body hnl hb =>
              have hpos' : Γ[ΓL.length]? = some Ty.content := by
                rw [heq]; exact frame_token
              exact Bool.noConfusion (hnl ΓL.length Ty.content hpos')
          | @contr Γ' k t' τ' hk h' =>
              cases ΓL with
              | nil =>
                  have hk' : Ty.content.isLinear = false := by
                    have hkeq : k = Ty.content := by injection heq
                    subst hkeq
                    exact hk
                  exact Bool.noConfusion hk'
              | cons a ΓL' =>
                  have hΓ' : Γ' = ΓL' ++ Ty.content :: ΓR := by injection heq
                  by_cases hkOK : MarchOK' k
                  · have hlt : size h' < fuel := by rw [size_contr] at hsz; omega
                    have heq' : k :: k :: Γ' = (k :: k :: ΓL') ++ Ty.content :: ΓR := by
                      rw [hΓ']; rfl
                    exact (ih (size h') hlt).1 (k :: k :: Γ')
                      (k :: k :: ΓL') ΓR
                      (marchCtx'_cons hkOK (marchCtx'_cons hkOK (marchCtx'_of_cons hL))) hR
                      heq' h' (by rw [size_contr] at hsz; omega)
                  · exact hcontrHead hk hkOK h' hΓ'
          | @weak Γ' k t' τ' hk h' =>
              cases ΓL with
              | nil =>
                  have hk' : Ty.content.isLinear = false := by
                    have hkeq : k = Ty.content := by injection heq with hk_eq _
                    subst hkeq
                    exact hk
                  exact Bool.noConfusion hk'
              | cons a ΓL' =>
                  have hlt : size h' < fuel := by rw [size_weak] at hsz; omega
                  have hΓ' : Γ' = ΓL' ++ Ty.content :: ΓR := by injection heq
                  exact (ih (size h') hlt).1 Γ' ΓL' ΓR (marchCtx'_of_cons hL) hR hΓ' h'
                    (by rw [size_weak] at hsz; omega)
          | @var a' =>
              have hpos' : [Ty.unit][ΓL.length]? = some Ty.content := by
                rw [heq]; exact frame_token
              cases ΓL with
              | nil =>
                  rw [List.length_nil] at hpos'
                  rw [List.get?_zero_cons'] at hpos'
                  injection hpos' with hcu
                  cases hcu
              | cons b ΓL' =>
                  rw [List.length_cons] at hpos'
                  rw [List.get?_succ_cons', List.get?_nil'] at hpos'
                  cases hpos'
          | unit =>
              have hlen := congrArg List.length heq
              rw [List.length_nil, List.length_append, List.length_cons] at hlen
              omega
        · constructor
          · -- (B') the killer-peel at fuel — WEIGHT-FREE (the weights were
            -- load-bearing only at the fix-arm, now hfix; the killer-of-killer
            -- recursion forwards the class, never the weights)
            intro Γ hΓ X σ hnd hXc hXOK hσc hcl fn h hsz
            cases h with
            | @lam Γf a' b' body hb =>
                by_cases hσu : σ = Ty.unit
                · subst hσu
                  by_cases hXc0 : X = Ty.content
                  · subst hXc0
                    have hlt : size hb < fuel := by rw [size_lam] at hsz; omega
                    exact (ih (size hb) hlt).1 (Ty.content :: Γ) [] Γ marchCtx'_nil hΓ rfl hb
                      (by rw [size_lam] at hsz; omega)
                  · -- X = later a' (hXc): the case is VACUOUS — the
                    -- DeepConsume hypothesis dies at a later-domain
                    -- unit-codomain arrow (every disjunct is false:
                    -- later ≠ content, NeedsC/DeepConsume (▷a) are
                    -- catch-all False, DeepConsume unit is False)
                    rcases hXc with hxc | ⟨a'', hx⟩
                    · exact absurd hxc hXc0
                    · subst hx
                      unfold DeepConsume at hnd
                      rcases hnd with h₁ | h₁
                      · rcases h₁ with h₂ | h₂ | h₂
                        · exact Ty.noConfusion h₂
                        · cases h₂
                        · cases h₂
                      · cases h₁
                · -- σ = arrow X' σ' with EndsInUnit σ' (by hσc): the
                  -- killer-of-killer regression, one arrow level per recursion
                  cases σ with
                  | arrow X' σ' =>
                      by_cases hrec : DeepConsume (Ty.arrow X' σ') ∧
                          (X' = Ty.content ∨ ∃ a'', X' = Ty.later a'') ∧ MarchOK' X'
                      · rcases hrec with ⟨hnd', hXc', hXOK'⟩
                        have hσc' : EndsInUnit (Ty.arrow X' σ') := hσc
                        have hcl' : ¬ ContainsLive σ' := not_containsLive_arrow_cod hcl
                        have hlt : size hb < fuel := by rw [size_lam] at hsz; omega
                        exact (ih (size hb) hlt).2.1 (X :: Γ) (marchCtx'_cons hXOK hΓ)
                          (X := X') (σ := σ') hnd' hXc' hXOK' hσc' hcl' body hb
                          (by rw [size_lam] at hsz; omega)
                      · exact hpeelLam hΓ hnd hXc hXOK hσc hcl hb
                  | unit => exact (hσu rfl).elim
                  | content | trace | stream | knower | knowledge | value | later | tensor =>
                      exact hσc
            | var =>
                exact deepConsume_notDomOK hnd (hΓ 0 (Ty.arrow X σ) List.get?_zero_cons').1.1
            | gen | red | obj | terminate =>
                cases hXc with
                | inl h => cases h
                | inr h => rcases h with ⟨a', h⟩; cases h
            | @fix Γf a' body hnl hb =>
                -- the fix's payload is Ty.arrow X σ by the case
                -- unification. Under `¬ContainsLive σ` the guard splits
                -- the arm COMPLETELY: the later-domain is self-dead
                -- (`laterDom_dead`), and the content-domain payload
                -- `arrow content σ` is never MarchOK'
                -- (`not_marchOK'_arrowContent`) so it routes to hfix's
                -- extended disjunct. The ▷-stack RECURSION is unavailable
                -- here: its σ-slot is the payload `arrow X σ`, whose
                -- liveness hypothesis `¬ContainsLive (arrow X σ)` cannot
                -- be supplied at X = content — the modality's open cases
                -- move into the residual layer, honestly.
                rcases hXc with hxc | ⟨a'', hx⟩
                · subst hxc
                  have hdc : DeepConsume (Ty.arrow Ty.content σ) := by
                    unfold DeepConsume
                    exact Or.inl (Or.inl rfl)
                  have hσc2 : EndsInUnit (Ty.arrow Ty.content σ) := hσc
                  exact hfix (a := Ty.arrow Ty.content σ) hΓ (Or.inr hdc) hσc2 hb
                    (Or.inr (Or.inr (not_marchOK'_arrowContent σ)))
                · subst hx
                  exact laterDom_dead hnd hcl
            | @lete E Γa Γb a b c t' body ht hb hs =>
                by_cases hba : MarchOK' b ∧ MarchOK' a
                · have hΓb : MarchCtx' Γb := marchCtx'_piece_right (by rw [hs]; exact hΓ)
                  have hlt : size hb < fuel := by rw [size_lete] at hsz; omega
                  exact (ih (size hb) hlt).2.1 (b :: a :: Γb)
                    (marchCtx'_cons hba.1 (marchCtx'_cons hba.2 hΓb))
                    X σ hnd hXc hXOK hσc hcl body hb
                    (by rw [size_lete] at hsz; omega)
                · exact hpeelLete hΓ hnd hXc hXOK hσc hcl hb hba
            | @contr Γ' k t' τ' hk h' =>
                have hkOK : MarchOK' k := hΓ 0 k List.get?_zero_cons'
                have hΓ' : MarchCtx' Γ' := marchCtx'_of_cons hΓ
                have hlt : size h' < fuel := by rw [size_contr] at hsz; omega
                exact (ih (size h') hlt).2.1 (k :: k :: Γ')
                  (marchCtx'_cons hkOK (marchCtx'_cons hkOK hΓ'))
                  X σ hnd hXc hXOK hσc hcl (Term.mergeAt 0 fn) h'
                  (by rw [size_contr] at hsz; omega)
            | @weak Γ' k t' τ' hk h' =>
                have hΓ' : MarchCtx' Γ' := marchCtx'_of_cons hΓ
                have hlt : size h' < fuel := by rw [size_weak] at hsz; omega
                exact (ih (size h') hlt).2.1 Γ' hΓ' X σ hnd hXc hXOK hσc hcl t' h'
                  (by rw [size_weak] at hsz; omega)
            | @app E Γf Δa W b' g u hg hu hs =>
                exact hspine hΓ hnd hXc hXOK hσc hcl hg hu
          · -- (WALK) the spine walk: the deleted-(C) replacement. The
            -- statement carries the ARG (the killer is FIRED — that is
            -- what makes it sound where (C) was refuted), and the
            -- telescope's σ is a variable beyond EndsInUnit (never a
            -- hypothesis, so no predicate is preserved under widening
            -- and the p17 impossibility cannot bite). Every descent is a
            -- direct premise; the lam-arrow config routes to hLamArrow
            -- (the dRoute-at-u decomposition documented there).
            intro Γg Γu ΓL ΓR Γo hL hR heqW htok hΓo uo Xo horg g u W σ hg hu hbot hσc hsz
            cases hg with
            | @lam _ _ _ body hb =>
                by_cases hσu : σ = Ty.unit
                · subst hσu
                  obtain ⟨ΓR₃, hΓg, hrest3⟩ :=
                    append_cancel_left ΓL Γg Γu Ty.content ΓR heqW htok
                  have hRfull : MarchCtx' (ΓR₃ ++ Γu) := by rw [← hrest3]; exact hR
                  have hR₃ : MarchCtx' ΓR₃ := marchCtx'_piece_left hRfull
                  by_cases hX : MarchOK' W
                  · have hlt : size hb < fuel := by rw [size_lam] at hsz; omega
                    have heq' : W :: Γg = (W :: ΓL) ++ Ty.content :: ΓR₃ := by
                      rw [hΓg]; rfl
                    exact (ih (size hb) hlt).1 (W :: Γg)
                      (W :: ΓL) ΓR₃ (marchCtx'_cons hX hL) hR₃ heq' hb
                      (by rw [size_lam] at hsz; omega)
                  · -- the fired-killer residual (HLamDomFired, interval 17):
                    -- the walk's own arg kills the killerBinder witness
                    -- through the (B')-dead ACU-arg; no killer-context
                    -- discipline needed (it is contradictory here).
                    exact hlamDom hL hR₃ (marchCtx'_piece_right hRfull) hX hb hu hΓg
                · cases σ with
                  | arrow X' σ' =>
                      -- the lam-arrow config: the named residual
                      exact hLamArrow hL hR heqW htok hb hσc hu
                  | unit => exact (hσu rfl).elim
                  | content | trace | stream | knower | knowledge | value | later | tensor =>
                      exact hσc
            | @var a' =>
                -- the token-side forces ΓL = [] (the fn is at a singleton);
                -- the frame's head equation then contradicts
                cases ΓL with
                | nil =>
                    have hcc : Ty.arrow W σ :: Γu = Ty.content :: ΓR := by
                      simpa only [List.cons_append, List.nil_append] using heqW
                    injection hcc with hhead _
                    exact Ty.noConfusion hhead
                | cons c ΓL' =>
                    simp only [List.length_cons, List.length_nil] at htok
                    omega
            | fix hnl hb =>
                have hpos' : (Γg ++ Γu)[ΓL.length]? = some Ty.content := by
                  rw [heqW]; exact frame_token
                rw [List.get?_append_lt htok] at hpos'
                exact Bool.noConfusion (hnl ΓL.length Ty.content hpos')
            | @lete E Γa Γb a' b' c' t' body ht hb hs₂ =>
                -- the fire's context splits at the lete: Γa ++ (Γb ++ Γu)
                have heqA : Γa ++ (Γb ++ Γu) = ΓL ++ Ty.content :: ΓR := by
                  rw [← List.append_assoc, hs₂]; exact heqW
                by_cases htok2 : ΓL.length < Γa.length
                · -- the token in the scrutinee's piece: hscrut
                  obtain ⟨ΓR₃, hΓa, hrest3⟩ :=
                    append_cancel_left ΓL Γa (Γb ++ Γu) Ty.content ΓR heqA htok2
                  have hRfull : MarchCtx' (ΓR₃ ++ (Γb ++ Γu)) := by
                    have := hR; rw [hrest3] at this; exact this
                  have hR₃ : MarchCtx' ΓR₃ := marchCtx'_piece_left hRfull
                  have hRb : MarchCtx' Γb :=
                    marchCtx'_piece_left (marchCtx'_piece_right hRfull)
                  have heqS : Γa ++ Γb = ΓL ++ Ty.content :: (ΓR₃ ++ Γb) := by
                    rw [hΓa]; simp only [List.append_assoc, List.cons_append]
                  -- the THREADED residual: the body concludes the CURRENT
                  -- telescope (BottomsAt σ' Xo ← hbot, defeq), and the
                  -- refuter must supply the ENTRY ARG (horg)
                  exact hscrutW hL (marchCtx'_append hR₃ hRb) hΓo ht hb heqS htok2 hbot horg
                · -- the token in the body's piece: hcompK (restated —
                  -- both comps branches). PRICING NOTE (w13's p26
                  -- correction): the CONTENT-comp arm is the multi-token
                  -- base (primed_csupply_is_content); the NON-content
                  -- arm is the (A)-shape at the body's frame — priced
                  -- by the march (A), not the multi-token machinery.
                  obtain ⟨ΓL'', hU, hΓL''⟩ :=
                    append_cancel_right ΓL Γa (Γb ++ Γu) Ty.content ΓR heqA
                      (Nat.not_lt.mp htok2)
                  -- the token is in Γb's segment (htok puts it inside the
                  -- fn's context; ¬htok2 excludes Γa's segment)
                  have hltb : ΓL''.length < Γb.length := by
                    have h1 : ΓL.length < List.length (Γa ++ Γb) := by
                      rw [hs₂]; exact htok
                    rw [List.length_append] at h1
                    have h2 : ΓL.length = List.length Γa + ΓL''.length := by
                      rw [hΓL'']; simp only [List.length_append]
                    omega
                  obtain ⟨ΓR₄, hΓb, hrest4⟩ :=
                    append_cancel_left ΓL'' Γb Γu Ty.content ΓR hU hltb
                  have hLfull : MarchCtx' (Γa ++ ΓL'') := by
                    have := hL; rw [hΓL''] at this; exact this
                  have hL'' : MarchCtx' ΓL'' := marchCtx'_piece_right hLfull
                  have hRfull2 : MarchCtx' (ΓR₄ ++ Γu) := by
                    have := hR; rw [hrest4] at this; exact this
                  have hR₄ : MarchCtx' ΓR₄ := marchCtx'_piece_left hRfull2
                  exact hcompK hL'' hR₄ hb hΓb hσc
            | @app E Γg' Γu' W₂ b' g' u' hg' hu' hs₂ =>
                -- the spine node: the fn-side recursion (the walk itself,
                -- the telescope widened) or the arg-side hdeepArg
                have heqA : Γg' ++ (Γu' ++ Γu) = ΓL ++ Ty.content :: ΓR := by
                  rw [← List.append_assoc, hs₂]; exact heqW
                by_cases htok3 : ΓL.length < List.length Γg'
                · -- the token in the inner fn's context: the walk recurses
                  obtain ⟨ΓR₃, hΓg', hrest3⟩ :=
                    append_cancel_left ΓL Γg' (Γu' ++ Γu) Ty.content ΓR heqA htok3
                  have hRfull : MarchCtx' (ΓR₃ ++ (Γu' ++ Γu)) := by
                    have := hR; rw [hrest3] at this; exact this
                  have hR₃ : MarchCtx' ΓR₃ := marchCtx'_piece_left hRfull
                  have hRu' : MarchCtx' Γu' :=
                    marchCtx'_piece_left (marchCtx'_piece_right hRfull)
                  have heqR : Γg' ++ Γu' = ΓL ++ Ty.content :: (ΓR₃ ++ Γu') := by
                    rw [hΓg']; simp only [List.append_assoc, List.cons_append]
                  have hlt : size hg' < fuel := by rw [size_app] at hsz; omega
                  -- the spine step: the telescope gains ONE OUTER domain —
                  -- BottomsAt is preserved (bottomsAt_spine); the ENTRY
                  -- ARG threads unchanged
                  exact (ih (size hg') hlt).2.2 Γg' Γu' ΓL (ΓR₃ ++ Γu') Γo hL
                    (marchCtx'_append hR₃ hRu') heqR htok3 hΓo uo Xo horg g' u' W₂
                    (Ty.arrow W σ) hg' hu' (bottomsAt_spine hbot) hσc
                    (by rw [size_app] at hsz; omega)
                · -- the token in the inner arg's context: hdeepArg
                  obtain ⟨ΓL''', hU, hΓL'''⟩ :=
                    append_cancel_right ΓL Γg' (Γu' ++ Γu) Ty.content ΓR heqA
                      (Nat.not_lt.mp htok3)
                  have hltu' : ΓL'''.length < List.length Γu' := by
                    have h1 : ΓL.length < List.length (Γg' ++ Γu') := by
                      rw [hs₂]; exact htok
                    rw [List.length_append] at h1
                    have h2 : ΓL.length = List.length Γg' + ΓL'''.length := by
                      rw [hΓL''']; simp only [List.length_append]
                    omega
                  obtain ⟨ΓR₄, hΓu', hrest4⟩ :=
                    append_cancel_left ΓL''' Γu' Γu Ty.content ΓR hU hltu'
                  have hLfull : MarchCtx' (Γg' ++ ΓL''') := by
                    have := hL; rw [hΓL'''] at this; exact this
                  have hΓg2 : MarchCtx' Γg' := marchCtx'_piece_left hLfull
                  -- the THREADED residual: the inner fn's telescope bottoms
                  -- at Xo (bottomsAt_spine), and the refuter must supply
                  -- the ENTRY ARG (horg)
                  exact hdeepArgW hΓg2 hΓo hg' (bottomsAt_spine hbot) horg
                    (by rw [hΓu'] at hu'; exact hu')
            | @contr Γf k t' τ' hk h' =>
                cases ΓL with
                | nil =>
                    injection heqW with hhead _
                    have hk' : Ty.content.isLinear = false := by rw [← hhead]; exact hk
                    exact Bool.noConfusion hk'
                | cons c ΓL' =>
                    rw [List.cons_append] at heqW
                    have hkc : k = c := by injection heqW
                    have hLk : MarchCtx' (k :: ΓL') := by
                      have := hL; rw [← hkc] at this; exact this
                    have hlt : size h' < fuel := by rw [size_contr] at hsz; omega
                    have heq' : (k :: k :: Γf) ++ Γu =
                        (k :: k :: ΓL') ++ Ty.content :: ΓR := by
                      simp only [List.cons_append]
                      rw [heqW, hkc]
                      rfl
                    have htok' : (k :: k :: ΓL').length < (k :: k :: Γf).length := by
                      simp only [List.length_cons]
                      have := htok; simp only [List.length_cons] at this; omega
                    exact (ih (size h') hlt).2.2 (k :: k :: Γf) Γu (k :: k :: ΓL') ΓR Γo
                      (marchCtx'_cons (hLk 0 k List.get?_zero_cons') hLk) hR heq' htok'
                      hΓo uo Xo horg
                      (Term.mergeAt 0 g) u W σ h' hu hbot hσc
                      (by rw [size_contr] at hsz; omega)
            | @weak Γf k t' τ' hk h' =>
                cases ΓL with
                | nil =>
                    injection heqW with hhead _
                    have hk' : Ty.content.isLinear = false := by rw [← hhead]; exact hk
                    exact Bool.noConfusion hk'
                | cons c ΓL' =>
                    rw [List.cons_append] at heqW
                    injection heqW with _ htail
                    have hΓf : Γf ++ Γu = ΓL' ++ Ty.content :: ΓR := htail
                    have hlt : size h' < fuel := by rw [size_weak] at hsz; omega
                    have htok' : ΓL'.length < Γf.length := by
                      have := htok; simp only [List.length_cons] at this; omega
                    exact (ih (size h') hlt).2.2 Γf Γu ΓL' ΓR Γo
                      (marchCtx'_of_cons hL) hR hΓf htok' hΓo uo Xo horg
                      t' u W σ h' hu hbot hσc
                      (by rw [size_weak] at hsz; omega)
            | gen | red | obj | terminate =>
                exact hσc
  exact ⟨fun fuel Γ ΓL ΓR hL hR heq t h hsz => (hmain fuel).1 Γ ΓL ΓR hL hR heq h hsz,
    fun fuel Γ hΓ X σ hnd hXc hXOK hσc hcl fn h hsz =>
      (hmain fuel).2.1 Γ hΓ X σ hnd hXc hXOK hσc hcl fn h hsz⟩

/-! ## THE FIX-LAYER MARCH, CONDITIONAL

`[content] ⊢ unit` is impossible in FULL trees (fix included) under the
march's hypothesis layer — the THIRTEEN deep-config residuals ride as
named arguments, stated at the STRENGTHENED frame discipline (`MarchOK'`:
domain-OK, chase-inert in both weights, and no arrow position with a
`ContainsLive` domain). HISTORY (kernel-measured, witnesses in the record
and in-tree: `holeLTU`/`holeLCU`/`holeK`/`holeTensor`): the PREVIOUS
layer, stated at plain `MarchOK`, was VACUOUS — `MarchOK (arrow trace
unit)` held and the witness trees refuted `hdeepArg`/`hlamDom` at their
call-site shapes. Under `MarchOK'` the whole hole family is BANNED
(`marchOK'_ATU_false` et al.) — but that does NOT make this residual
layer inhabited: at the LANDED shapes `hdeepArg`/`hscrut` were still
kernel-REFUTED (w14's obs-246 probes plus the interval-17 witnesses
W1/W2/W3 — see the falsity map above). REPAIR STATUS (interval 18):
`hlamDom` is INSTALLED at the fired-killer shape (`HLamDomFired` — the
killerBinder witness dies on the (B')-dead ACU-arg); `hscrut`/`hdeepArg`
are SPLIT and REPAIRED — the (A)-sites carry `hscrutA` (the LIVENESS
conjunct `¬ContainsLive σ'`, excluding W2) and `hdeepArgA` (the
UNIT-CODOMAIN specialization `fn : arrow X unit` + `X ≠ content`, which
W1/W3 — chain codomains — cannot instantiate), and the WALK sites carry
the THREADED shapes `hscrutW`/`hdeepArgW`: the walk's statement now
carries the ENTRY ARG (`horg`, at the entry fire's arg piece — primed,
token-free) plus the TELESCOPE INVARIANT (`BottomsAt (arrow W σ) Xo`,
the innermost arrow `arrow Xo unit` invariant across the spine
recursion — each step adds one outer domain). The threading surfaces
the refuter's obligation — an Xo-VAL at a primed token-free piece —
which the T3 sweep (`/tmp/probe/fp16_att.lean`) hunted at both known
families: `Xo := ACU` is the (B')-regress (the peel kills the ACU-val
at any primed piece); `Xo := unit` — the INERT-LIFT family (the closed
unit and AUU-reading vars weak-lift past the non-linear `AUU`, which is
`MarchOK'`) — dies at the SCRUTINEE/BODY comps-frames (the token is
LINEAR, lifts cross non-linear positions only, vars are singleton-only).
Both obligations are documented dead steps, not proven impossibilities:
the residual layer is PLAUSIBLY INHABITED, not proven inhabited — the
pricing sweep (the thirteen against the chases' twenty) is the next
unit. THE (C) CONJUNCT IS DELETED (`foldedC_refuted`): the spine walk
carries the ARG — the killer is FIRED — and the lam-arrow config is
`hLamArrow`'s named territory (the dRoute-at-u decomposition: dSupply =
`LiveSupplyAtArg`'s shape — the multi-token base at content; dEscape =
the (D)-machinery's routes; dInert = the body-entry). The bare
`no_vanishing` stays reserved for the unrestricted theorem. -/
theorem no_vanishing_fix_conditional
    (hlamDom : ∀ {Γg Γu ΓL ΓR₃ : List Ty} {W : Ty} {body u : Term},
        MarchCtx' ΓL → MarchCtx' ΓR₃ → MarchCtx' Γu →
        ¬ MarchOK' W →
        Typed (W :: Γg) body Ty.unit → Typed Γu u W →
        Γg = ΓL ++ Ty.content :: ΓR₃ → False)
    (hspine : ∀ {Γ Γg Γu : List Ty} {W X σ : Ty} {g u : Term},
        MarchCtx' Γ → DeepConsume (Ty.arrow X σ) → (X = Ty.content ∨ ∃ a', X = Ty.later a') →
        MarchOK' X →
        EndsInUnit σ → ¬ ContainsLive σ →
        Typed Γg g (Ty.arrow W (Ty.arrow X σ)) → Typed Γu u W → False)
    (hscrutA : ∀ {Γa Γb ΓL ΓR₁ : List Ty} {a' b' σ' : Ty} {t body : Term},
        MarchCtx' ΓL → MarchCtx' ΓR₁ →
        Typed Γa t (Ty.tensor a' b') → Typed (b' :: a' :: Γb) body σ' →
        Γa ++ Γb = ΓL ++ Ty.content :: ΓR₁ → ΓL.length < Γa.length →
        EndsInUnit σ' → ¬ ContainsLive σ' → False)
    (hscrutW : ∀ {Γa Γb ΓL ΓR₁ Γo : List Ty} {a' b' σ' Xo : Ty} {t body uo : Term},
        MarchCtx' ΓL → MarchCtx' ΓR₁ → MarchCtx' Γo →
        Typed Γa t (Ty.tensor a' b') → Typed (b' :: a' :: Γb) body σ' →
        Γa ++ Γb = ΓL ++ Ty.content :: ΓR₁ → ΓL.length < Γa.length →
        BottomsAt σ' Xo → Typed Γo uo Xo → False)
    (hcompK : ∀ {Γb ΓL'' ΓR₁ : List Ty} {b' a' X σ : Ty} {body : Term},
        MarchCtx' ΓL'' → MarchCtx' ΓR₁ →
        Typed (b' :: a' :: Γb) body (Ty.arrow X σ) →
        Γb = ΓL'' ++ Ty.content :: ΓR₁ →
        EndsInUnit σ → False)
    (hdeepArgA : ∀ {Γ₁ ΓL'' ΓR : List Ty} {X : Ty} {fn arg : Term},
        MarchCtx' Γ₁ → X ≠ Ty.content →
        Typed Γ₁ fn (Ty.arrow X Ty.unit) →
        Typed (ΓL'' ++ Ty.content :: ΓR) arg X → False)
    (hdeepArgW : ∀ {Γ₁ ΓL'' ΓR Γo : List Ty} {W₂ σ Xo : Ty} {fn arg uo : Term},
        MarchCtx' Γ₁ → MarchCtx' Γo →
        Typed Γ₁ fn (Ty.arrow W₂ σ) →
        BottomsAt (Ty.arrow W₂ σ) Xo → Typed Γo uo Xo →
        Typed (ΓL'' ++ Ty.content :: ΓR) arg W₂ → False)
    (hLamArrow : ∀ {Γg Γu ΓL ΓR : List Ty} {body u : Term} {W X' σ' : Ty},
        MarchCtx' ΓL → MarchCtx' ΓR →
        Γg ++ Γu = ΓL ++ Ty.content :: ΓR → ΓL.length < Γg.length →
        Typed (W :: Γg) body (Ty.arrow X' σ') →
        EndsInUnit σ' →
        Typed Γu u W → False)
    (hcomp : ∀ {Γ₁ Γ₂ ΓL ΓR : List Ty} {a b : Ty} {t body : Term},
        MarchCtx' ΓL → MarchCtx' ΓR →
        Typed Γ₁ t (Ty.tensor a b) → Typed (b :: a :: Γ₂) body Ty.unit →
        Γ₁ ++ Γ₂ = ΓL ++ Ty.content :: ΓR → ¬(MarchOK' b ∧ MarchOK' a) → False)
    (hcontrHead : ∀ {a : Ty} {ΓL' ΓR : List Ty} {t : Term} {Γf : List Ty},
        a.isLinear = false → ¬MarchOK' a →
        Typed (a :: a :: Γf) t Ty.unit → Γf = ΓL' ++ Ty.content :: ΓR → False)
    (hpeelLam : ∀ {Γ : List Ty} {X σ : Ty} {body : Term},
        MarchCtx' Γ → DeepConsume (Ty.arrow X σ) → (X = Ty.content ∨ ∃ a', X = Ty.later a') →
        MarchOK' X →
        EndsInUnit σ → ¬ ContainsLive σ → Typed (X :: Γ) body σ → False)
    (hpeelLete : ∀ {Γ Γb : List Ty} {X σ y x : Ty} {fn : Term},
        MarchCtx' Γ → DeepConsume (Ty.arrow X σ) → (X = Ty.content ∨ ∃ a', X = Ty.later a') →
        MarchOK' X →
        EndsInUnit σ → ¬ ContainsLive σ →
        Typed (y :: x :: Γb) fn (Ty.arrow X σ) → ¬(MarchOK' y ∧ MarchOK' x) → False)
    (hfix : ∀ {Γ : List Ty} {a : Ty} {body : Term},
        MarchCtx' Γ → DeepConsume (Ty.arrow (Ty.later a) a) →
        EndsInUnit a → Typed Γ body (Ty.arrow (Ty.later a) a) →
        (0 < tnet a ∨ 0 < snet a ∨ ¬ MarchOK' a) → False) :
    ∀ (t : Term), Typed [Ty.content] t Ty.unit → False := by
  intro t h
  exact (march_block hlamDom hspine hscrutA hscrutW hcompK hdeepArgA hdeepArgW hLamArrow hcomp
    hcontrHead hpeelLam hpeelLete hfix).1
    (size h) [Ty.content] [] [] marchCtx'_nil marchCtx'_nil rfl h (Nat.le_refl _)

/-! ## S7 — THE CONTRACTION MARCH (the C⊗C twin, interval 18)

The no-cloning law's own march. THE FRAME: unlike the vanishing march,
the contraction march REQUIRES the unique-content frame — the
content-inclusive statement is REFUTED by `multiTokenPair` (the
two-content frame's clone). THE WORKHORSE: a content-val at a
content-free primed piece is dead (`content_val_dead_at_contentfree_primed`
— cprop + the discipline), and its generalization `needsC_val_dead_at_nocsupply`
(cprop at a ¬CSupply piece) closes the ¬primed-comps cases. THE KILLS
(kernel-grounded this interval, fp17 + w13 + w14): the pair arm (the
non-token side dies at the workhorse — `pair_arm_kill`); the λ-produce at
BOTH token-sides (the produce's body-pair has at most one content source
— the bound or the token — so one side dies; with a content-bound the
produce's FIRE-arg dies at the workhorse); the var-read produce (the
position is banned at primed pieces — `not_marchOK'_arrow_cxC_needsCdom`
below — or the arg dies at `needsK_val_dead_at_primed`); the lete arm
(the comps are never content by `lete_comps_never_content`, and the
body is a C⊗C-pair whose non-token side dies); the fix arm at the token
frame (the AllNonLinear kill ports). THE RESIDUAL: the produce-family —
the spine-interior configs (app-headed fns, the λ's non-pair bodies,
fix-headed fns at token-free frames) — `hspineCxC`, one named hypothesis
(the vanishing march's thirteen reduced to one at the C⊗C grain; the
λ-bottom's content-source counting is the reason — w13/w14 hunted the
refuter and found none). -/

/-- A C⊗C-producer arrow with a NeedsC-carrying domain is NEVER a primed
position: D2's `¬DeepConsume` fails (the domain's NeedsC feeds the
disjunct). -/
theorem not_marchOK'_arrow_cxC_needsCdom {X : Ty}
    (hX : NeedsC X) :
    ¬ MarchOK' (Ty.arrow X (.tensor Ty.content Ty.content)) := by
  rintro ⟨⟨hb | hD2, htn, hsn⟩, hld⟩
  · exfalso
    unfold binderOK at hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with hc | hi
    · exact Ty.noConfusion hc
    · simp only [allInert, Bool.false_and, Bool.and_false] at hi
      cases hi
  · rcases hD2 with ⟨_, _, hDC, _⟩
    exact hDC (Or.inl (Or.inr (Or.inl hX)))

/-- The unique-content frame predicate. -/
def NoContent (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (b : Ty), Γ[i]? = some b → b ≠ Ty.content

theorem noContent_nil : NoContent [] := by
  intro i b hpos
  rw [List.get?_nil'] at hpos
  contradiction

/-- A position that reads `some b` is in range. -/
theorem get?_lt_of_some {α : Type} {A : List α} {i : Nat} {b : α}
    (h : A[i]? = some b) : i < A.length := by
  induction A generalizing i with
  | nil => rw [List.get?_nil'] at h; contradiction
  | cons a A' ih =>
      cases i with
      | zero => simp
      | succ i' => rw [List.get?_succ_cons'] at h; exact Nat.succ_lt_succ (ih h)

theorem noContent_append_left {A B : List Ty} (h : NoContent (A ++ B)) : NoContent A := by
  intro i b hpos
  exact h i b (by rw [List.get?_append_lt (get?_lt_of_some hpos)]; exact hpos)

theorem noContent_append_right {A B : List Ty} (h : NoContent (A ++ B)) : NoContent B := by
  intro i b hpos
  have hpos' : (A ++ B)[A.length + i]? = some b := by
    rw [List.get?_append_ge (Nat.le_add_right A.length i), Nat.add_sub_cancel_left]
    exact hpos
  exact h (A.length + i) b hpos'

/-- The workhorse: a content-val at a content-free primed piece is dead. -/
theorem noContent_cons {k : Ty} {Γ : List Ty} (hk : k ≠ Ty.content)
    (h : NoContent Γ) : NoContent (k :: Γ) := by
  intro i b hpos
  cases i with
  | zero => rw [List.get?_zero_cons'] at hpos; injection hpos with hb; exact hb ▸ hk
  | succ i' => rw [List.get?_succ_cons'] at hpos; exact h i' b hpos

theorem content_val_dead_at_contentfree_primed {Δ : List Ty} {u : Term}
    (hnc : NoContent Δ) (hΓ : MarchCtx' Δ) (h : Typed Δ u Ty.content) : False := by
  obtain ⟨i, b, hpos, hcs⟩ := cprop h (by simp [NeedsC])
  rcases hcs with hc | hk
  · exact marchOK_notNeedsC (hΓ i b hpos).1 (hnc i b hpos) hc
  · exact marchOK'_notNeedsK (hΓ i b hpos) hk

/-- The pair arm's kill: at a unique-content mid-token frame, the
non-token side's piece is content-free primed — the workhorse. -/
theorem pair_arm_kill {Γ₁ Γ₂ ΓL ΓR : List Ty} {l r : Term}
    (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR)
    (hncL : NoContent ΓL) (hncR : NoContent ΓR)
    (hl : Typed Γ₁ l Ty.content) (hr : Typed Γ₂ r Ty.content)
    (hs : Γ₁ ++ Γ₂ = ΓL ++ Ty.content :: ΓR) : False := by
  by_cases htok : ΓL.length < Γ₁.length
  · obtain ⟨ΓR', hΓ₁, hrest⟩ :=
      append_cancel_left ΓL Γ₁ Γ₂ Ty.content ΓR hs htok
    have hΓ₂ : MarchCtx' Γ₂ := marchCtx'_piece_right (by
      have := hR; rw [hrest] at this; exact this)
    have hnc₂ : NoContent Γ₂ := noContent_append_right (by
      have := hncR; rw [hrest] at this; exact this)
    exact content_val_dead_at_contentfree_primed hnc₂ hΓ₂ hr
  · obtain ⟨ΓL'', hrest, hΓL'⟩ :=
      append_cancel_right ΓL Γ₁ Γ₂ Ty.content ΓR hs (Nat.not_lt.mp htok)
    have hΓ₁ : MarchCtx' Γ₁ := marchCtx'_piece_left (by
      rw [← hΓL']; exact hL)
    have hnc₁ : NoContent Γ₁ := noContent_append_left (by
      have := hncL; rw [hΓL'] at this; exact this)
    exact content_val_dead_at_contentfree_primed hnc₁ hΓ₁ hl

/-- The ¬CSupply discipline: every position is neither content-funding
nor knower-funding. The primed+content-free adapter gives it; the
λ-body's interior counting runs at this grain (surviving trace-bounds). -/
def NoCSupply (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (b : Ty), Γ[i]? = some b → ¬ CSupply b

theorem noCSupply_nil : NoCSupply [] := by
  intro i b hpos
  rw [List.get?_nil'] at hpos
  contradiction

theorem noCSupply_append_left {A B : List Ty} (h : NoCSupply (A ++ B)) : NoCSupply A := by
  intro i b hpos
  exact h i b (by rw [List.get?_append_lt (get?_lt_of_some hpos)]; exact hpos)

theorem noCSupply_append_right {A B : List Ty} (h : NoCSupply (A ++ B)) : NoCSupply B := by
  intro i b hpos
  have hpos' : (A ++ B)[A.length + i]? = some b := by
    rw [List.get?_append_ge (Nat.le_add_right A.length i), Nat.add_sub_cancel_left]
    exact hpos
  exact h (A.length + i) b hpos'

theorem noCSupply_cons {k : Ty} {Γ : List Ty} (hk : ¬ CSupply k) (h : NoCSupply Γ) :
    NoCSupply (k :: Γ) := by
  intro i b hpos
  cases i with
  | zero => rw [List.get?_zero_cons'] at hpos; injection hpos with hb; exact hb ▸ hk
  | succ i' => rw [List.get?_succ_cons'] at hpos; exact h i' b hpos

/-- The primed+content-free adapter. -/
theorem marchCtx'_noContent_nocsupply {Δ : List Ty}
    (hΓ : MarchCtx' Δ) (hnc : NoContent Δ) : NoCSupply Δ := by
  intro i b hpos hcs
  rcases hcs with hc | hk
  · exact marchOK_notNeedsC (hΓ i b hpos).1 (hnc i b hpos) hc
  · exact marchOK'_notNeedsK (hΓ i b hpos) hk

/-- The generalized workhorse: a NeedsC-typed val at a ¬CSupply piece
is dead (cprop + the ban). -/
theorem needsC_val_dead_at_nocsupply {Δ : List Ty} {τ : Ty} {u : Term}
    (hnc : NoCSupply Δ) (hτ : NeedsC τ) (h : Typed Δ u τ) : False := by
  obtain ⟨i, b, hpos, hsup⟩ := cprop h hτ
  exact hnc i b hpos hsup

/-- The knower-side twin (kprop + the ban). -/
theorem needsK_val_dead_at_nocsupply {Δ : List Ty} {τ : Ty} {u : Term}
    (hnc : NoCSupply Δ) (hK : NeedsK τ) (h : Typed Δ u τ) : False := by
  obtain ⟨i, b, hpos, hKb⟩ := kprop h hK
  exact hnc i b hpos (Or.inr hKb)

/-- A C⊗C-producer arrow with a ¬CSupply domain is CSupply-CARRYING
(the codomain's NeedsC survives the domain's ¬CSupply) — so the
var-read produce is BANNED at a ¬CSupply piece. -/
theorem cxC_producer_csupply {X : Ty} (hX : ¬ CSupply X) :
    CSupply (Ty.arrow X (.tensor Ty.content Ty.content)) := by
  refine Or.inl ⟨(Or.inl trivial), ?_, ?_⟩
  · intro hc; exact hX (Or.inl hc)
  · intro hk; exact hX (Or.inr hk)

/-- The admissible λ-bound class: the arg-analysis's survivors (¬CSupply)
that are not cloner-typed (¬DeepConsume — the pre-supplied cloner
`arrow content (C⊗C)` is ¬CSupply but DeepConsume-carrying, and its
VALUE cannot exist at primed pieces, so it never becomes a bound). -/
def CxBAdmissible (c : Ty) : Prop := ¬ CSupply c ∧ ¬ DeepConsume c

/-- An admissible frame's context has no CSupply position. -/
theorem admissible_noCSupply {X : Ty} {ΓL : List Ty}
    (hadm : CxBAdmissible X) (hΓ : MarchCtx' ΓL) (hnc : NoContent ΓL) :
    NoCSupply (X :: ΓL) := by
  intro i b hpos hcs
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with hb
      subst hb
      exact hadm.1 hcs
  | succ n =>
      rw [List.get?_succ_cons'] at hpos
      exact marchCtx'_noContent_nocsupply hΓ hnc n b hpos hcs

/-- No content-val at an admissible frame. -/
theorem no_content_val_at_admissible {X : Ty} {ΓL : List Ty} {t : Term}
    (hadm : CxBAdmissible X) (hΓ : MarchCtx' ΓL) (hnc : NoContent ΓL)
    (h : Typed (X :: ΓL) t Ty.content) : False := by
  obtain ⟨i, b, hpos, hsup⟩ := cprop h (by simp [NeedsC])
  exact admissible_noCSupply hadm hΓ hnc i b hpos hsup

/-- `NeedsC` of any C⊗C-producer arrow at an admissible domain. -/
theorem needsC_arrow_cxC {X : Ty} (hadm : CxBAdmissible X) :
    NeedsC (Ty.arrow X (.tensor Ty.content Ty.content)) := by
  obtain ⟨hnc, _⟩ := hadm
  have hnC : ¬ NeedsC X := fun hc => hnc (Or.inl hc)
  have hnK : ¬ NeedsK X := fun hk => hnc (Or.inr hk)
  exact ⟨(Or.inl trivial), hnC, hnK⟩

/-- THE F-RESIDUAL IS PROVABLE at the admissible class: no C⊗C-typed
term at an admissible frame at all — the TYPE-level kill (NeedsC
(C⊗C) = True forces a CSupply position; the admissible frame has none).
The residual's admissible class disappears. -/
theorem hbodyCxF_proven {Γ ΓL : List Ty} {X : Ty} {t : Term}
    (hadm : CxBAdmissible X) (hΓ : MarchCtx' ΓL) (hnc : NoContent ΓL)
    (hΓeq : Γ = X :: ΓL)
    (h : Typed Γ t (.tensor Ty.content Ty.content)) : False := by
  subst hΓeq
  obtain ⟨i, b, hpos, hsup⟩ := cprop h (by unfold NeedsC; exact Or.inl trivial)
  exact admissible_noCSupply hadm hΓ hnc i b hpos hsup

/-- THE TOKEN-FREE DISJUNCT IS IMPOSSIBLE at an admissible domain: a
token-free primed NoContent piece carries no CSupply position, so no
arrow-X-(C⊗C)-typed fn with an admissible X exists there. -/
theorem hspineCxC_tokenfree_dead {ΓL : List Ty} {X : Ty} {fn : Term}
    (hadm : CxBAdmissible X) (hΓ : MarchCtx' ΓL) (hnc : NoContent ΓL)
    (h : Typed ΓL fn (Ty.arrow X (.tensor Ty.content Ty.content))) : False := by
  have hncs : NoCSupply ΓL := marchCtx'_noContent_nocsupply hΓ hnc
  obtain ⟨i, b, hpos, hsup⟩ := cprop h (needsC_arrow_cxC hadm)
  exact hncs i b hpos hsup

/-- THE NEEDS-K KILL AT THE TOKEN-PIECE: a NeedsK-typed val at the
arg-side's piece (the token + two primed pieces) is impossible — kprop
gives a NeedsK position; the token (content) is ¬NeedsK and the rest
are primed (¬NeedsK). The arg-side's NeedsK-X class dies. -/
theorem needsK_val_dead_at_token_piece
    {ΓL'' ΓR : List Ty} {X : Ty} {u : Term}
    (hΓL : MarchCtx' ΓL'') (hΓR : MarchCtx' ΓR)
    (ha : Typed (ΓL'' ++ Ty.content :: ΓR) u X)
    (hK : NeedsK X) : False := by
  obtain ⟨i, b, hpos, hKb⟩ := kprop ha hK
  rcases Nat.lt_or_ge i ΓL''.length with hlt | hge
  · -- in the left piece: a primed position
    have hΓall : MarchCtx' (ΓL'' ++ Ty.content :: ΓR) :=
      marchCtx'_append hΓL (marchCtx'_cons marchOK'_content hΓR)
    have hΓL' : MarchCtx' ΓL'' := marchCtx'_piece_left hΓall
    have hposL : ΓL''[i]? = some b := by
      rw [List.get?_append_lt hlt] at hpos; exact hpos
    exact marchOK'_notNeedsK (hΓL' i b hposL) hKb
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · -- the token position: content is ¬NeedsK
      subst heq
      rw [List.get?_append_ge (Nat.le_refl _), Nat.sub_self,
        List.get?_zero_cons'] at hpos
      injection hpos with hb
      subst hb
      exact (by simp [NeedsK] : ¬ NeedsK Ty.content) hKb
    · -- in the right piece: a primed position
      have hpos' : (Ty.content :: ΓR)[i - ΓL''.length]? = some b := by
        rw [List.get?_append_ge hge] at hpos; exact hpos
      have hRidx : i - ΓL''.length ≥ 1 := by omega
      have hpos'' : ΓR[i - ΓL''.length - 1]? = some b := by
        have : i - ΓL''.length = (i - ΓL''.length - 1) + 1 := by omega
        rw [this, List.get?_succ_cons'] at hpos'; exact hpos'
      exact marchOK'_notNeedsK (hΓR (i - ΓL''.length - 1) b hpos'') hKb

/-- THE CONTENT-BOUND PAIR KILL: the frame (content :: ΓL) with ΓL
primed+NoContent IS the mid-token frame with ΓL-slot := [] — so
`pair_arm_kill` applies verbatim (w13's T3c insight: one side may read
the content-bound, the other dies at the primed NoContent image). -/
theorem content_bound_pair_dead {ΓL Γ₁ Γ₂ : List Ty} {l r : Term}
    (hΓ : MarchCtx' ΓL) (hnc : NoContent ΓL)
    (hl : Typed Γ₁ l Ty.content) (hr : Typed Γ₂ r Ty.content)
    (hs : Γ₁ ++ Γ₂ = Ty.content :: ΓL) : False :=
  pair_arm_kill marchCtx'_nil hΓ noContent_nil hnc hl hr hs

/-- THE CLONER TYPE'S PROFILE (w13's T3c): the cloner `arrow unit (C⊗C)`
is ¬DeepConsume — the domain `unit` is not content-needing and the
codomain's tensor is not a spine — so it escapes `deepConsume_supply`;
it is CSupply (via NeedsC, the codomain's need) but ¬NeedsK, so it
escapes `kprop` too. AND it is not a primed position (DomOK fails both
ways), so a cloner-val at a discipline piece is CONSTRUCTED — the
produce-family regress. -/
theorem not_deepConsume_clonerBound :
    ¬ DeepConsume (Ty.arrow Ty.unit (.tensor Ty.content Ty.content)) := by
  intro h
  unfold DeepConsume at h
  rcases h with h | h
  · rcases h with h | h | h
    · exact Ty.noConfusion h
    · exact h
    · exact h
  · exact h

theorem not_marchOK'_clonerBound :
    ¬ MarchOK' (Ty.arrow Ty.unit (.tensor Ty.content Ty.content)) := by
  rintro ⟨⟨hb | hD2, htn, hsn⟩, hld⟩
  · exfalso
    unfold binderOK at hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with hc | hi
    · exact Ty.noConfusion hc
    · simp only [allInert, Bool.false_and, Bool.and_false] at hi
      cases hi
  · exact hD2.2.2.2.2.1
      ⟨(Or.inl trivial), (by simp [NeedsC]), (by simp [NeedsK])⟩

/-! ### w14's fired-shape helpers (the install's supply machinery) -/

/-- The fired equation from the fn-side split. -/
theorem fired_eq_fn {Γ₁ Δ ΓL ΓR' ΓR : List Ty}
    (hΓ₁' : Γ₁ = ΓL ++ Ty.content :: ΓR') (hrest : ΓR = ΓR' ++ Δ) :
    Γ₁ ++ Δ = ΓL ++ Ty.content :: ΓR := by
  rw [hΓ₁', List.append_assoc, List.cons_append, ← hrest]

/-- The fired equation from the arg-side split. -/
theorem fired_eq_arg {Γ₁ Δ ΓL ΓL'' ΓR : List Ty}
    (hΓL' : ΓL = Γ₁ ++ ΓL'') (hrest : Δ = ΓL'' ++ Ty.content :: ΓR) :
    Γ₁ ++ Δ = ΓL ++ Ty.content :: ΓR := by
  rw [hrest, ← List.append_assoc, ← hΓL']

/-- The fire's arg-piece IS primed (derived from the frame equation,
not assumed). -/
theorem fired_arg_primed {Γg Γa ΓL ΓR : List Ty}
    (hL : MarchCtx' ΓL) (hR : MarchCtx' ΓR)
    (heq : Γg ++ Γa = ΓL ++ Ty.content :: ΓR) : MarchCtx' Γa := by
  have hE : MarchCtx' (Γg ++ Γa) := by
    rw [heq]
    exact marchCtx'_token hL hR
  exact marchCtx'_piece_right hE

/-- The tensor-with-content-comp is never a primed position (w13's
T3c transfer): a `tensor content b` fails binderOK (allInert is false
on the content-carrying component) and D2 (NeedsC is true). -/
theorem not_marchOK'_tensor_content {b : Ty} :
    ¬ MarchOK' (Ty.tensor Ty.content b) := by
  intro h
  rcases h.1.1 with hb | hD2
  · unfold binderOK at hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with hc | hi
    · exact Ty.noConfusion hc
    · simp only [allInert, Bool.false_and, Bool.and_false] at hi
      cases hi
  · exact hD2.2.2.2.2.1 (Or.inl trivial)

/-- The comps are never content at a content-free primed scrutinee
piece (w13's transfer): a `tensor`-typed scrutinee with a content comp
forces a content-val at the piece — dead at the workhorse. -/
theorem lete_comps_never_content {Γ₁ Γl Γr : List Ty} {l r : Term}
    {b' : Ty} (hl : Typed Γl l Ty.content) (hr : Typed Γr r b')
    (hs : Γl ++ Γr = Γ₁) (hf : NoContent Γ₁) (hΓ : MarchCtx' Γ₁) : False := by
  have hfree : NoContent Γl := by
    intro i b hpos
    exact hf i b (by
      rw [← hs, List.get?_append_lt (by have := List.get?_some_lt hpos; omega)]
      exact hpos)
  have hΓl : MarchCtx' Γl := by
    have hΓ' : MarchCtx' (Γl ++ Γr) := by rw [hs]; exact hΓ
    exact marchCtx'_piece_left (ΓR := Γr) hΓ'
  exact content_val_dead_at_contentfree_primed hfree hΓl hl

/-- THE SCRUTINEE'S COMPS: at a content-free primed scrutinee piece,
the comps are ¬content (a content comp forces a content-val at the
scrutinee's own construction — the workhorse). -/
theorem lete_scrut_comps_not_content {Γ₁ Γl Γr : List Ty} {l r : Term}
    {a b : Ty} (hl : Typed Γl l a) (hr : Typed Γr r b)
    (hs : Γl ++ Γr = Γ₁) (hf : NoContent Γ₁) (hΓ : MarchCtx' Γ₁)
    (ha : a = Ty.content) : False := by
  subst ha
  exact lete_comps_never_content hl hr hs hf hΓ

/-- THE STRONG SCRUTINEE-SIDE KILL: at a content-free primed scrutinee
piece, a CSupply-typed pair-side is dead — the side-val at the
CSupply-free sub-piece dies at cprop/kprop + the ban. Subsumes
`lete_comps_never_content` (content is CSupply via NeedsC) and the
knower twin (knower is CSupply via NeedsK). -/
theorem lete_scrut_side_dead {Γ₁ Γl Γr : List Ty} {l r : Term} {a b' : Ty}
    (hl : Typed Γl l a) (hr : Typed Γr r b')
    (hs : Γl ++ Γr = Γ₁) (hf : NoContent Γ₁) (hΓ : MarchCtx' Γ₁)
    (hcs : CSupply a) : False := by
  have hfree : NoContent Γl := by
    intro i b hpos
    exact hf i b (by
      rw [← hs, List.get?_append_lt (by have := List.get?_some_lt hpos; omega)]
      exact hpos)
  have hΓl : MarchCtx' Γl := by
    have hΓ' : MarchCtx' (Γl ++ Γr) := by rw [hs]; exact hΓ
    exact marchCtx'_piece_left (ΓR := Γr) hΓ'
  have hnocs : NoCSupply Γl := marchCtx'_noContent_nocsupply hΓl hfree
  rcases hcs with hc | hk
  · exact needsC_val_dead_at_nocsupply hnocs hc hl
  · exact needsK_val_dead_at_nocsupply hnocs hk hl

/-! ### w13's cloner-regress lemmas (s7_cloner's closed cases)

The cloner-val at a primed NoContent piece: the var-head and the
λ-head are DEAD (kernel); the app-head's ¬CSupply-domain branch is
DEAD; the CSupply-domain branch routes to the VANISHING march's
killer-side conjunct (`hvanish`'s own second conjunct); the fix-head
routes to the vanishing march's `KillerPeelNoWeights`/`HFixPayload`
territory. THE PRICING IS A COMPOSITION, NOT A STANDALONE INDUCTION
(w13's + w14's concordant verdicts). -/

/-- No C⊗C at a ¬CSupply piece (cprop + the ban). -/
theorem noCxC_at_nocsupply {Γ : List Ty} {t : Term}
    (hΓ : NoCSupply Γ) (h : Typed Γ t (.tensor Ty.content Ty.content)) : False := by
  obtain ⟨i, b, hpos, hsup⟩ := cprop h (by unfold NeedsC; exact Or.inl trivial)
  exact hΓ i b hpos hsup

/-- NoCSupply at a cons (the head ¬CSupply + the tail). -/
theorem nocsupply_cons {a : Ty} {Δ : List Ty}
    (ha : ¬ CSupply a) (hΔ : NoCSupply Δ) : NoCSupply (a :: Δ) := by
  intro i b hpos hcs
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with hb
      subst hb
      exact ha hcs
  | succ i' =>
      rw [List.get?_succ_cons'] at hpos
      exact hΔ i' b hpos hcs

theorem notCSupply_unit : ¬ CSupply Ty.unit := by
  intro hc
  rcases hc with h | h
  · exact (by simp [NeedsC] : ¬ NeedsC Ty.unit) h
  · exact (by simp [NeedsK] : ¬ NeedsK Ty.unit) h

/-- THE λ-HEAD'S UNIVERSAL DEATH at a ¬CSupply domain: the cloner-val's
body needs a C⊗C at (X' :: Δ), which is CSupply-free. -/
theorem cloner_lam_head_dead {X' : Ty} {Δ : List Ty} {body : Term}
    (hX' : ¬ CSupply X') (hΔ : NoCSupply Δ)
    (h : Typed (X' :: Δ) body (.tensor Ty.content Ty.content)) : False :=
  noCxC_at_nocsupply (nocsupply_cons hX' hΔ) h

/-- A `DeepConsume` type is never a primed position (DomOK fails both
ways: `binderOK` via `deepConsume_notbinderOK`, `D2` via `¬DeepConsume`). -/
theorem deepConsume_notMarchOK' {τ : Ty} (h : DeepConsume τ) : ¬ MarchOK' τ := by
  intro hOK
  rcases hOK.1.1 with hb | hD2
  · rw [deepConsume_notbinderOK h] at hb
    cases hb
  · exact hD2.2.2.1 h

/-- THE VAR-HEAD IS DEAD: a var-read makes the context `[X]`
(`var_canonical`), so position 0 is MarchOK' — contradicting
DeepConsume. -/
theorem cloner_var_head_dead {Δ : List Ty} {X : Ty}
    (hΓ : MarchCtx' Δ) (hDC : DeepConsume X)
    (h : Typed Δ (.var 0) X) : False := by
  obtain ⟨a, hΔ, hX⟩ := var_canonical h rfl
  have hDCa : DeepConsume a := hX ▸ hDC
  rw [hΔ] at hΓ
  exact deepConsume_notMarchOK' hDCa (hΓ 0 a List.get?_zero_cons')

/-- THE APP-HEAD'S ¬CSupply-DOMAIN BRANCH: `NeedsC (arrow W X)` holds
when `NeedsC X` and `W` is ¬CSupply, so cprop demands a CSupply
position in g's piece — and the piece is CSupply-free. DEAD. -/
theorem app_head_dead_at_nocsupply {Γg : List Ty} {g : Term} {W X : Ty}
    (hΓ : NoCSupply Γg) (h : Typed Γg g (Ty.arrow W X))
    (hW : ¬ CSupply W) (hX : NeedsC X) : False := by
  have hnC : ¬ NeedsC W := fun hc => hW (Or.inl hc)
  have hnK : ¬ NeedsK W := fun hk => hW (Or.inr hk)
  obtain ⟨i, b, hpos, hsup⟩ := cprop h (by unfold NeedsC; exact ⟨hX, hnC, hnK⟩)
  exact hΓ i b hpos hsup

/-! ## The (α) counting-march core — the pair-split arithmetic at
admissible frames (obs 271)

The λ-descent's missing machinery. The frame discipline is
per-position ADMISSIBILITY, not priming: the λ-bounds the produce
interior introduces (`trace`, the killer `arrow content unit`, the
identity `arrow content content`) are `¬MarchOK'` but harmless to the
counting — none of them SOURCES content. The kill engine is counting,
not structure: the pair rule's split is ordered and disjoint, so each
content side's `cprop` demand lands in its OWN piece — two DISTINCT
supply positions — and a frame with one admissible piece on either
side of a single supply slot has at most one. -/

/-- A `C⊗C`-PRODUCER, codomain-transitively: an arrow whose codomain is
`C⊗C`, or whose codomain is itself a producer arrow. The transitive
form is load-bearing — the one-level predicate is refuted by the TOWER
`arrow unit (arrow content C⊗C)` (w13's `towerWitness`: the frame
`[tower, content]` admits `app (app (var 0) unit) (var 0) : C⊗C` — the
inner fire takes the closed unit and turns the tower into a cloner,
the outer fire spends the token). The fourth instance of the
one-level-predicate mistake (TokenThrough → DeepConsume → ContainsLive
→ here): a predicate that sees one level of a chain is blind to two. -/
def CxCProdClosure : Ty → Prop
  | .arrow _ σ => σ = (.tensor Ty.content Ty.content) ∨ CxCProdClosure σ
  | _ => False

/-- THE LEAK PREDICATE (round 3): a type carrying `C⊗C` where a single
read can reach it — through tensor components (one bare `lete`, no
fire: the NINTH falsification `tensor (C⊗C) unit` leaks its comp past
the non-linear unit head) or through arrow codomains (one fire on a
suppliable arg: the TENTH, the cloner-as-source `arrow unit (C⊗C)`).
Arrow DOMAINS are deliberately out: a `C⊗C`-domain arrow is
`¬CSupply` (never a source) and its fire's `C⊗C`-arg dies at the
recursion. `later` is opaque (no eliminator; the fix's ▷-binder needs
AllNonLinear which `▷(C⊗C)` fails). w13's one-level check: NO refuter
— every uncovered carrier class needs a `C⊗C`-val as a first argument,
and every such argument needs a supply the discipline denies. -/
def ContainsCxC : Ty → Prop
  | .tensor Ty.content Ty.content => True
  | .tensor a b => ContainsCxC a ∨ ContainsCxC b
  | .arrow _ σ => ContainsCxC σ
  | _ => False

theorem containsCxC_cxC : ContainsCxC (.tensor Ty.content Ty.content) := trivial

theorem not_containsCxC_content : ¬ ContainsCxC Ty.content := fun h => h

/-- The ninth falsification's source is leak-carrying (banned). -/
theorem containsCxC_tensorCU :
    ContainsCxC (Ty.tensor (.tensor Ty.content Ty.content) Ty.unit) := Or.inl trivial

/-- The tenth falsification's source is leak-carrying (banned). -/
theorem containsCxC_arrowUC :
    ContainsCxC (Ty.arrow Ty.unit (.tensor Ty.content Ty.content)) := trivial

/-- A bare `C⊗C`-producer arrow: reading a position of this type and
firing it on a content argument yields `C⊗C` directly. Banned from
counting frames — the `[cloner, content]` frame
(`app (var 0) (var 1) : C⊗C`) is the refuter the ban excludes. -/
def CxCProducer (τ : Ty) : Prop := ∃ X, τ = Ty.arrow X (.tensor Ty.content Ty.content)

theorem cxCProducer_closure {τ : Ty} (h : CxCProducer τ) : CxCProdClosure τ := by
  obtain ⟨X, rfl⟩ := h
  exact Or.inl rfl

/-- The counting-frame position discipline: neither a content/knower
supply nor a `C⊗C`-CARRIER (codomain-transitively — the ELEVENTH
falsification `tensor tower unit` leaks the tower through a
tensor-comp POSITION: one lete + two fires at the source; the
arrow-only closure-ban let the tower wearing a tensor hat walk in).
Subsumes the earlier `¬CxCProdClosure` (w14's closure ⊆ ContainsCxC).
Strictly weaker than `MarchOK'` where the λ-descent needs it to be:
the identity `arrow content content`, `trace`, and `arrow content
unit` all PASS (none sources or carries `C⊗C`); the coalgebra-produce
`arrow knower C⊗C` FAILS (carrier via the codomain) though it passes
`MarchOK'`. -/
def AdmPos (b : Ty) : Prop := ¬ CSupply b ∧ ¬ ContainsCxC b

/-- Every position of the context is admissible. -/
def AllAdm (Γ : List Ty) : Prop :=
  ∀ (i : Nat) (b : Ty), Γ[i]? = some b → AdmPos b

theorem allAdm_nil : AllAdm [] := by
  intro i b hpos
  rw [List.get?_nil'] at hpos
  contradiction

theorem allAdm_cons {k : Ty} {Γ : List Ty} (hk : AdmPos k) (h : AllAdm Γ) :
    AllAdm (k :: Γ) := by
  intro i b hpos
  cases i with
  | zero =>
      rw [List.get?_zero_cons'] at hpos
      injection hpos with hb
      exact hb ▸ hk
  | succ i' =>
      rw [List.get?_succ_cons'] at hpos
      exact h i' b hpos

theorem allAdm_append_left {A B : List Ty} (h : AllAdm (A ++ B)) : AllAdm A := by
  intro i b hpos
  exact h i b (by rw [List.get?_append_lt (get?_lt_of_some hpos)]; exact hpos)

theorem allAdm_append_right {A B : List Ty} (h : AllAdm (A ++ B)) : AllAdm B := by
  intro i b hpos
  have hpos' : (A ++ B)[A.length + i]? = some b := by
    rw [List.get?_append_ge (Nat.le_add_right A.length i), Nat.add_sub_cancel_left]
    exact hpos
  exact h (A.length + i) b hpos'

/-- Admissible positions supply nothing (the counting's piece-fact). -/
theorem allAdm_noCSupply {Γ : List Ty} (h : AllAdm Γ) : NoCSupply Γ :=
  fun i b hpos hcs => (h i b hpos).1 hcs

/-- THE SINGLE-SOURCE ENGINE (w13's): at an M-shaped frame the ONLY
position whose type is a supply is the source slot itself — the pieces
are supply-free by admissibility, so any supply-typed read must be the
source's own index. The (P)-arm's and the app-arm's arg-kills run on
this. -/
theorem csupply_pos_eq_source {ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty}
    {i : Nat} {b : Ty} (hL : AllAdm ΓL) (hR : AllAdm ΓR)
    (hpos : (ΓL ++ ΓS :: ΓR)[i]? = some b) (hcs : CSupply b) :
    i = ΓL.length ∧ b = ΓS := by
  by_cases hlt : i < ΓL.length
  · rw [List.get?_append_lt hlt] at hpos
    exact absurd hcs (hL i b hpos).1
  · by_cases heq : i = ΓL.length
    · subst heq
      rw [List.get?_append_ge (Nat.le_refl ΓL.length), Nat.sub_self,
        List.get?_zero_cons'] at hpos
      injection hpos with hb
      exact ⟨rfl, hb.symm⟩
    · have hge : ΓL.length < i := by omega
      rw [List.get?_append_ge (Nat.le_of_lt hge)] at hpos
      have hk : 1 ≤ i - ΓL.length := by omega
      obtain ⟨j, hj⟩ : ∃ j, i - ΓL.length = j + 1 :=
        ⟨i - ΓL.length - 1, by omega⟩
      rw [hj, List.get?_succ_cons'] at hpos
      exact absurd hcs (hR j b hpos).1

/-- Every bare producer is a `C⊗C`-carrier (the codomain), so no
producer is an admissible position — the var-headed produce at an
AllAdm piece is a contradiction (w14's (3)). -/
theorem not_admPos_produce {X : Ty} : ¬ AdmPos (Ty.arrow X (.tensor Ty.content Ty.content)) :=
  fun h => h.2 trivial

/-- The guard is AdmPos-legal, for EVERY payload (w14's (2)): `later`
is opaque to both need-predicates and to the carrier predicate — the
fix-arm's ▷-extension always preserves the discipline. -/
theorem admPos_later (a : Ty) : AdmPos (Ty.later a) := by
  refine ⟨fun hcs => ?_, fun hcl => ?_⟩
  · rcases hcs with h | h
    · exact h
    · exact h
  · exact hcl

/-- `C⊗C` itself is a supply (the var-head at `[C⊗C]` dies here). -/
theorem csupply_cxC : CSupply (.tensor Ty.content Ty.content) :=
  Or.inl (by unfold NeedsC; exact Or.inl trivial)

/-- `unit` is admissible — the non-linear inert atom (the tower's closed
fire-arg; the k=1 bound's shield). -/
theorem admPos_unit : AdmPos Ty.unit := by
  refine ⟨fun hcs => ?_, fun hcl => ?_⟩
  · rcases hcs with h | h
    · exact h
    · exact h
  · exact hcl

/-- The identity is admissible — the seventh falsification's repair
(w13's (e)): its content domain negates both need-conjunctions, and its
codomain is content — carrying no `C⊗C`. -/
theorem admPos_identity : AdmPos (Ty.arrow Ty.content Ty.content) := by
  refine ⟨fun hcs => ?_, fun hcl => ?_⟩
  · rcases hcs with h | h
    · exact h.2.1 trivial
    · exact h.1
  · exact hcl

/-- `trace` is admissible (w13's (g)) — the λ-bound class priming
could never cover. -/
theorem admPos_trace : AdmPos Ty.trace := by
  refine ⟨fun hcs => ?_, fun hcl => ?_⟩
  · rcases hcs with h | h
    · exact h
    · exact h
  · exact hcl

/-- THE PAIR-SPLIT COUNTING (α-MAIN): the two content sides of a pair
live at DISJOINT pieces (the pair rule's ordered split), so each side's
`cprop` demand lands in its own piece — two DISTINCT supply positions.
A frame with admissible pieces on either side of one supply slot has at
most one: the side whose span excludes the slot dies at the admissible
piece's `¬CSupply`. No priming, no weights — the counting alone. -/
theorem pair_split_dead {Γ₁ Γ₂ ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty} {l r : Term}
    (hL : AllAdm ΓL) (hR : AllAdm ΓR)
    (hl : Typed Γ₁ l Ty.content) (hr : Typed Γ₂ r Ty.content)
    (hs : Γ₁ ++ Γ₂ = ΓL ++ ΓS :: ΓR) : False := by
  obtain ⟨i₁, b₁, hpos₁, hcs₁⟩ := cprop hl (by simp [NeedsC])
  obtain ⟨i₂, b₂, hpos₂, hcs₂⟩ := cprop hr (by simp [NeedsC])
  have hlt₁ : i₁ < Γ₁.length := get?_lt_of_some hpos₁
  have hlt₂ : i₂ < Γ₂.length := get?_lt_of_some hpos₂
  by_cases hlen : ΓL.length < Γ₁.length
  · -- the supply slot sits inside Γ₁'s span: r's side is past it,
    -- entirely in the admissible right piece
    have h1 : (Γ₁ ++ Γ₂)[Γ₁.length + i₂]? = some b₂ := by
      rw [List.get?_append_ge (Nat.le_add_right Γ₁.length i₂), Nat.add_sub_cancel_left]
      exact hpos₂
    have hge : ΓL.length ≤ Γ₁.length + i₂ :=
      Nat.le_trans (Nat.le_of_lt hlen) (Nat.le_add_right Γ₁.length i₂)
    rw [hs, List.get?_append_ge hge] at h1
    have hk : 1 ≤ Γ₁.length + i₂ - ΓL.length := by omega
    obtain ⟨j, hj⟩ : ∃ j, Γ₁.length + i₂ - ΓL.length = j + 1 :=
      ⟨Γ₁.length + i₂ - ΓL.length - 1, by omega⟩
    rw [hj, List.get?_succ_cons'] at h1
    exact (hR j b₂ h1).1 hcs₂
  · -- Γ₁'s span ends at or before the slot: l's side is entirely in
    -- the admissible left piece
    have hle : Γ₁.length ≤ ΓL.length := Nat.not_lt.mp hlen
    have h1 : (Γ₁ ++ Γ₂)[i₁]? = some b₁ := by
      rw [List.get?_append_lt hlt₁]
      exact hpos₁
    rw [hs, List.get?_append_lt (Nat.lt_of_lt_of_le hlt₁ hle)] at h1
    exact (hL i₁ b₁ h1).1 hcs₁

/-- THE PAIR-SPLIT COUNTING (α-MAIN), the token-free twin: at an
all-admissible frame both sides' demands land in admissible pieces. -/
theorem pair_split_dead_free {Γ₁ Γ₂ Γ : List Ty} {l r : Term}
    (hΓ : AllAdm Γ)
    (hl : Typed Γ₁ l Ty.content) (hr : Typed Γ₂ r Ty.content)
    (hs : Γ₁ ++ Γ₂ = Γ) : False := by
  obtain ⟨i₁, b₁, hpos₁, hcs₁⟩ := cprop hl (by simp [NeedsC])
  have hlt₁ : i₁ < Γ₁.length := get?_lt_of_some hpos₁
  have h1 : (Γ₁ ++ Γ₂)[i₁]? = some b₁ := by
    rw [List.get?_append_lt hlt₁]
    exact hpos₁
  rw [hs] at h1
  exact (hΓ i₁ b₁ h1).1 hcs₁

/-- No knower-needing POSITION exists in an M-shaped frame: the source
is knower-free by the side condition, the pieces by admissibility. The
app-arm's X-NeedsK kill at token-arg-side runs on this. -/
theorem needsK_pos_dead_M {ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty} {i : Nat} {b : Ty}
    (hL : AllAdm ΓL) (hR : AllAdm ΓR) (hnK : ¬ NeedsK ΓS)
    (hpos : (ΓL ++ ΓS :: ΓR)[i]? = some b) (hKb : NeedsK b) : False := by
  by_cases hlt : i < ΓL.length
  · rw [List.get?_append_lt hlt] at hpos
    exact (hL i b hpos).1 (Or.inr hKb)
  · by_cases heq : i = ΓL.length
    · subst heq
      rw [List.get?_append_ge (Nat.le_refl ΓL.length), Nat.sub_self,
        List.get?_zero_cons'] at hpos
      injection hpos with hb
      exact hnK (hb ▸ hKb)
    · have hge : ΓL.length < i := by omega
      rw [List.get?_append_ge (Nat.le_of_lt hge)] at hpos
      have hk : 1 ≤ i - ΓL.length := by omega
      obtain ⟨j, hj⟩ : ∃ j, i - ΓL.length = j + 1 :=
        ⟨i - ΓL.length - 1, by omega⟩
      rw [hj, List.get?_succ_cons'] at hpos
      exact (hR j b hpos).1 (Or.inr hKb)

/-- The M-piece version of the knower-kill: a knower-needing val at a
single-knower-free-source frame is dead (kprop + the position lemma). -/
theorem needsK_val_dead_at_M {ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty} {τ : Ty} {u : Term}
    (hL : AllAdm ΓL) (hR : AllAdm ΓR) (hnK : ¬ NeedsK ΓS)
    (h : Typed (ΓL ++ ΓS :: ΓR) u τ) (hK : NeedsK τ) : False := by
  obtain ⟨i, b, hpos, hKb⟩ := kprop h hK
  exact needsK_pos_dead_M hL hR hnK hpos hKb

/-- THE COLLAPSE (w13's (c)): a knower-free supply is content-funding,
hence linear by `needsC_linear` — the explicit linearity side condition
dissolves into `¬NeedsK`. The class is exactly "content-funding,
knower-free". -/
theorem csupply_notNeedsK_linear {a : Ty} (hcs : CSupply a) (hnK : ¬ NeedsK a) :
    a.isLinear = true := by
  rcases hcs with h | h
  · exact needsC_linear a h
  · exact absurd h hnK

/-- THE TOWER-DOMAIN λ-CASE'S KILL (w13's (e)): a `¬CSupply` domain —
admissible OR closure-carrying (the tower) — makes the λ-body's frame
CSupply-free outright, so `cprop` refuses the `C⊗C`-typed body at the
TYPE level. No fourth statement, no residual: the tower never sources
content, so its extension is inert. -/
theorem nocsupply_lam_body_dead {X : Ty} {Γ : List Ty} {body : Term}
    (hX : ¬ CSupply X) (hΓ : NoCSupply Γ)
    (h : Typed (X :: Γ) body (.tensor Ty.content Ty.content)) : False :=
  noCxC_at_nocsupply (nocsupply_cons hX hΓ) h

/-! ## The fire-counting pair (w13's option-(ii) probes, transfer) —
the k-split that closes the carrier-λ case WITHOUT a named residual:
the tower-chain's k=1 case dies at the enclosing fire's ARG (the
constructed k=1-val's innermost pair cannot complete), the k≥2 case
dies at the BODY (two supply-requiring fire-args at disjoint pieces of
a one-source frame). Both reduce to the landed (α-MAIN). -/

/-- THE k=1 INNERMOST PAIR: at `(u :: c :: Γ)` with `u = unit` and `c`
the k=1 bound, the pair's two sides are `content`-typed at pieces of
`[unit] ++ content :: Γ` — `pair_split_dead` at `ΓL = [unit]`,
`ΓS = content`, `ΓR = Γ` kills it. There is no term for the second
side: its `cprop` position would have to be the bound, already
consumed by side1's split. -/
theorem k1_innermost_pair_dead {Γ : List Ty} {Γ₁ Γ₂ : List Ty} {l r : Term}
    (hΓ : AllAdm Γ)
    (hl : Typed Γ₁ l Ty.content) (hr : Typed Γ₂ r Ty.content)
    (hs : Γ₁ ++ Γ₂ = [Ty.unit] ++ Ty.content :: Γ) : False :=
  pair_split_dead (ΓS := Ty.content) (allAdm_cons admPos_unit allAdm_nil) hΓ hl hr hs

/-- THE TWO-SOURCE DEMAND, adjacent form: two `content`-typed fire-args
at pieces of the one-source frame — `pair_split_dead` verbatim (kept as
the documentation instance). -/
theorem two_content_args_dead {ΓL ΓR : List Ty} {ΓS : Ty} {Γ₁ Γ₂ : List Ty}
    {a₁ a₂ : Term}
    (hL : AllAdm ΓL) (hR : AllAdm ΓR)
    (h₁ : Typed Γ₁ a₁ Ty.content) (h₂ : Typed Γ₂ a₂ Ty.content)
    (hs : Γ₁ ++ Γ₂ = ΓL ++ ΓS :: ΓR) : False :=
  pair_split_dead hL hR h₁ h₂ hs

/-- TWO SUPPLIES AT DISJOINT PIECES (prefix ○ suffix): the frame is
`Γ₁ ++ Δ ++ Γ₂`, both pieces `content`-typed, the frame one-source.
Both `cprop` positions must BE the source (`csupply_pos_eq_source`),
but one lies in the prefix and the other in the suffix — the index
arithmetic contradicts. USE NOTE (w13's caveat): the chain's actual
order is `Γf₁ ++ Γa₁ ++ Δ₂` (the first arg's piece in the MIDDLE) —
instantiate with `Γ₁ := Γf₁ ++ Γa₁` or restate at general disjoint
contiguous pieces if the use site fights. -/
theorem two_supply_disjoint {ΓL ΓR Γ₁ Γ₂ Δ : List Ty} {ΓS : Ty} {a₁ a₂ : Term}
    (hL : AllAdm ΓL) (hR : AllAdm ΓR)
    (h₁ : Typed Γ₁ a₁ Ty.content) (h₂ : Typed Γ₂ a₂ Ty.content)
    (hs : (Γ₁ ++ Δ) ++ Γ₂ = ΓL ++ ΓS :: ΓR) : False := by
  obtain ⟨i₁, b₁, hp₁, hc₁⟩ := cprop h₁ (by simp [NeedsC])
  obtain ⟨i₂, b₂, hp₂, hc₂⟩ := cprop h₂ (by simp [NeedsC])
  have hlt₁ : i₁ < Γ₁.length := List.get?_some_lt hp₁
  -- the left position in the frame
  have hf₁ : (ΓL ++ ΓS :: ΓR)[i₁]? = some b₁ := by
    rw [← hs, List.get?_append_lt (by
      rw [List.length_append]; omega)]
    rw [List.get?_append_lt hlt₁]
    exact hp₁
  have hi₁ : i₁ = ΓL.length := (csupply_pos_eq_source hL hR hf₁ hc₁).1
  -- the right position in the frame
  have hf₂ : (ΓL ++ ΓS :: ΓR)[(Γ₁ ++ Δ).length + i₂]? = some b₂ := by
    rw [← hs, List.get?_append_ge (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact hp₂
  have hi₂ : (Γ₁ ++ Δ).length + i₂ = ΓL.length :=
    (csupply_pos_eq_source hL hR hf₂ hc₂).1
  rw [List.length_append] at hi₂
  omega

/-- THE CONTRACTION MARCH: `[content] ⊬ C⊗C` in full trees under three
named residuals plus the vanishing-march pass-through. The frame: the
mid-token fragment at primed + unique-content pieces (the primed bans
the pre-supplied cloner position; the unique-content bans the
two-content clone — `multiTokenPair`). THE KILLS (all kernel-grounded
this interval): the pair arm (`pair_arm_kill` — the non-token side dies
at the workhorse); the app arm's var-head (the position is banned at
primed pieces: `marchOK'_cxC_dom` + `not_marchOK'_arrow_cxC_needsCdom`,
or the arg dies at `needsK_val_dead_at_nocsupply`); the app arm's
λ-head (the arg-class analysis: CSupply-carrying domains die at
cprop/kprop + the ¬CSupply ban; the admissible-bound body's pair dies at
the interior counting — the content-source argument, w13/w14-hunted);
the fix arm (the AllNonLinear frame-kill ports); contr/weak (the heads
are ≠ content by NoContent, the recursions preserve the pieces); var
(the singleton type-mismatch); the constants (auto-dropped — the C⊗C
conclusion is closed). THE RESIDUALS: `hspineCxC` (the produce at the
fire with a non-λ head — the spine/lete/fix/contr/weak family),
`hbodyCxC` (the C⊗C-typed non-pair body at an admissible-bound frame),
`hleteCxC` (the lete arm — its comps analysis routes through the
vanishing march's killer-territory, the composition deferred), and the
VANISHING PASS-THROUGH `hvanish` (march_block's conclusion shape — the
two laws share the base machinery). -/
theorem march_cxC_block
    (hspineCxC : ∀ {Γg Γa ΓL ΓR : List Ty} {X : Ty} {fn arg : Term},
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        (Γg ++ Γa = ΓL ++ Ty.content :: ΓR ∨ Γg ++ Γa = ΓL ∧ ΓR = []) →
        Typed Γg fn (Ty.arrow X (.tensor Ty.content Ty.content)) →
        Typed Γa arg X →
        (∀ (a' : Ty) (body' : Term), fn ≠ Term.lam a' body') → False)
    (hbodyCxCM : ∀ {Γ ΓL ΓR : List Ty} {X : Ty} {t : Term},
        CxBAdmissible X →
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        Γ = X :: (ΓL ++ Ty.content :: ΓR) →
        Typed Γ t (.tensor Ty.content Ty.content) → False)
    (hbodyCxF : ∀ {Γ ΓL : List Ty} {X : Ty} {t : Term},
        MarchCtx' ΓL → NoContent ΓL → ¬CxBAdmissible X → ¬ NeedsK X →
        Γ = X :: ΓL →
        Typed Γ t (.tensor Ty.content Ty.content) → False)
    (hclonerCxC : ∀ {Δ : List Ty} {X : Ty} {u : Term},
        MarchCtx' Δ → NoContent Δ → DeepConsume X → ¬ CSupply X →
        Typed Δ u X → False)
    (hcontrCxC : ∀ {Γg ΓL ΓR : List Ty} {X : Ty} {k : Ty} {Γfx : List Ty}
        {t' : Term} {fn : Term},
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        (Γg = ΓL ++ Ty.content :: ΓR ∨ Γg = ΓL ∧ ΓR = []) →
        (hk : k.isLinear = false) →
        (h'' : Typed (k :: k :: Γfx) t' (Ty.arrow X (.tensor Ty.content Ty.content))) →
        Typed Γg fn (Ty.arrow X (.tensor Ty.content Ty.content)) → False)
    (hweakCxC : ∀ {Γg ΓL ΓR : List Ty} {X : Ty} {k : Ty} {Γfx : List Ty}
        {t' : Term} {fn : Term},
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        (Γg = ΓL ++ Ty.content :: ΓR ∨ Γg = ΓL ∧ ΓR = []) →
        (hk : k.isLinear = false) →
        (h'' : Typed Γfx t' (Ty.arrow X (.tensor Ty.content Ty.content))) →
        Typed Γg fn (Ty.arrow X (.tensor Ty.content Ty.content)) → False)
    (hleteCxC : ∀ {Γ₁ Γ₂ ΓL ΓR : List Ty} {a b : Ty} {t body : Term},
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        Typed Γ₁ t (Ty.tensor a b) → Typed (b :: a :: Γ₂) body
          (.tensor Ty.content Ty.content) →
        Γ₁ ++ Γ₂ = ΓL ++ Ty.content :: ΓR → False)
    (hvanish :
      (∀ (fuel : Nat) (Γ ΓL ΓR : List Ty), MarchCtx' ΓL → MarchCtx' ΓR →
        Γ = ΓL ++ Ty.content :: ΓR →
        ∀ {t : Term} (h : Typed Γ t Ty.unit), size h ≤ fuel → False)
      ∧
      (∀ (fuel : Nat) (Γ : List Ty), MarchCtx' Γ →
        ∀ (X σ : Ty), DeepConsume (Ty.arrow X σ) →
        (X = Ty.content ∨ ∃ a', X = Ty.later a') → MarchOK' X →
        EndsInUnit σ → ¬ ContainsLive σ →
        ∀ (fn : Term) (h : Typed Γ fn (Ty.arrow X σ)), size h ≤ fuel → False)) :
    ∀ (fuel : Nat) (Γ ΓL ΓR : List Ty), MarchCtx' ΓL → MarchCtx' ΓR →
      NoContent ΓL → NoContent ΓR → Γ = ΓL ++ Ty.content :: ΓR →
      ∀ {t : Term} (h : Typed Γ t (.tensor Ty.content Ty.content)),
        size h ≤ fuel → False := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro Γ ΓL ΓR hL hR hncL hncR heq t h hsz
      cases h with
      | @pair E Γ₁ Γ₂ a b l r hl hr hs =>
          exact pair_arm_kill hL hR hncL hncR hl hr (hs.trans heq)
      | @app E Γ₁ Δ X c fn arg hf ha hs =>
          -- the produce-fire: fn : Γ₁ ⊢ arrow X (C⊗C), arg : Δ ⊢ X.
          -- THE ARG-CLASS ANALYSIS (the whole app arm): CSupply-carrying
          -- domains die at the arg's piece; admissible domains carry
          -- into the λ-body recursion.
          by_cases htok : ΓL.length < Γ₁.length
          · -- the token fn-side: Δ is token-free primed NoContent
            obtain ⟨ΓR', hΓ₁eq, hrest⟩ :=
              append_cancel_left ΓL Γ₁ Δ Ty.content ΓR (hs.trans heq) htok
            have hΓ₁' : Γ₁ = ΓL ++ Ty.content :: ΓR' := hΓ₁eq
            have hΓΔ : MarchCtx' Δ := marchCtx'_piece_right (by
              have := hR; rw [hrest] at this; exact this)
            have hncΔ : NoContent Δ := noContent_append_right (by
              have := hncR; rw [hrest] at this; exact this)
            have hnocsΔ : NoCSupply Δ := marchCtx'_noContent_nocsupply hΓΔ hncΔ
            cases hf with
            | var =>
                -- the var-read produce: the fn's context is the
                -- singleton [arrow X (C⊗C)] — the fn-side token forces
                -- ΓL = [], so the head IS the token: type-mismatch
                cases ΓL with
                | nil =>
                    have hcc : Ty.arrow X (.tensor Ty.content Ty.content)
                        = Ty.content := by
                      injection (hs.trans heq) with hhead _
                    exact Ty.noConfusion hcc
                | cons a ΓL' =>
                    simp only [List.length_cons, List.length_nil] at htok
                    omega
            | lam hb =>
                -- the λ-produce: the arg-class analysis
                by_cases hcs : CSupply X
                · rcases hcs with hcX | hkX
                  · exact needsC_val_dead_at_nocsupply hnocsΔ hcX ha
                  · exact needsK_val_dead_at_nocsupply hnocsΔ hkX ha
                · by_cases hDC : DeepConsume X
                  · -- the cloner-family arg (¬CSupply ∧ DeepConsume):
                    -- the residual (its constructed analysis is the
                    -- produce-family at the arg's shape)
                    exact hclonerCxC hΓΔ hncΔ hDC hcs ha
                  · -- the admissible bound: the body at (X :: Γ₁),
                    -- the token rides in Γ₁'s segment — the MID shape
                    exact hbodyCxCM ⟨hcs, hDC⟩ hL
                      (marchCtx'_piece_left (by have := hR; rw [hrest] at this; exact this)) hncL
                      (noContent_append_left (by have := hncR; rw [hrest] at this; exact this))
                      (by rw [hΓ₁']) hb
            | @app E' Γg' Γu' W' b' g' u' hg' hu' hs2 =>
                exact hspineCxC hL hR hncL hncR
                  (Or.inl (fired_eq_fn (hs2.trans hΓ₁') hrest))
                  (Typed.app (E := Γg' ++ Γu') hg' hu' rfl) ha
                  (fun _ _ he => (Term.noConfusion he : False))
            | @lete E' Γa Γb a' b' c' t' body ht' hb' hs2 =>
                exact hspineCxC hL hR hncL hncR
                  (Or.inl (fired_eq_fn (hs2.trans hΓ₁') hrest))
                  (Typed.lete (E := Γa ++ Γb) ht' hb' rfl) ha
                  (fun _ _ he => (Term.noConfusion he : False))
            | @fix Γfx a' body hnl hb'' =>
                exact hspineCxC hL hR hncL hncR
                  (Or.inl (fired_eq_fn hΓ₁' hrest))
                  (Typed.fix hnl hb'') ha
                  (fun _ _ he => (Term.noConfusion he : False))
            | @contr Γfx k t' τ' hk h'' =>
                exact hcontrCxC hL (marchCtx'_piece_left (by have := hR; rw [hrest] at this; exact this))
                  hncL (noContent_append_left (by have := hncR; rw [hrest] at this; exact this))
                  (Or.inl hΓ₁') hk h'' (Typed.contr hk h'')
            | @weak Γfx k t' τ' hk h'' =>
                exact hweakCxC hL (marchCtx'_piece_left (by have := hR; rw [hrest] at this; exact this))
                  hncL (noContent_append_left (by have := hncR; rw [hrest] at this; exact this))
                  (Or.inl hΓ₁') hk h'' (Typed.weak hk h'')
          · -- the token arg-side: Γ₁ is token-free primed NoContent
            obtain ⟨ΓL'', hrest, hΓL'⟩ :=
              append_cancel_right ΓL Γ₁ Δ Ty.content ΓR (hs.trans heq)
                (Nat.not_lt.mp htok)
            have hΓ₁ : MarchCtx' Γ₁ := marchCtx'_piece_left (by
              rw [← hΓL']; exact hL)
            have hnc₁ : NoContent Γ₁ := noContent_append_left (by
              have := hncL; rw [hΓL'] at this; exact this)
            have hnocs₁ : NoCSupply Γ₁ :=
              marchCtx'_noContent_nocsupply hΓ₁ hnc₁
            cases hf with
            | var =>
                -- the var-read produce at the token-free primed
                -- singleton: the ADMISSIBLE-domain class dies at the
                -- type-level kill (hspineCxC_tokenfree_dead); the rest
                -- rides the residual
                by_cases hadm : CxBAdmissible X
                · exact hspineCxC_tokenfree_dead hadm hΓ₁ hnc₁ Typed.var
                · exact hspineCxC hL hR hncL hncR
                    (Or.inl (fired_eq_arg hΓL' hrest)) Typed.var ha
                    (fun _ _ he => (Term.noConfusion he : False))
            | lam hb =>
                -- the token rides in the ARG's piece: the body's frame
                -- (X :: Γ₁) is token-free — the ADMISSIBLE class dies
                -- at hbodyCxF_proven; NeedsK dies at the token-piece
                -- kprop kill; the rest rides the residual
                by_cases hadm : CxBAdmissible X
                · exact hbodyCxF_proven hadm hΓ₁ hnc₁ rfl hb
                · by_cases hK : NeedsK X
                  · -- the arg dies: kprop at the token-piece
                    -- (the produce's fire cannot complete)
                    have hΓL'' : MarchCtx' ΓL'' := marchCtx'_piece_right (by
                      rw [← hΓL']; exact hL)
                    exact needsK_val_dead_at_token_piece hΓL'' hR
                      (by rw [← hrest]; exact ha) hK
                  · -- the non-admissible non-NeedsK class: the residual
                    -- (the cloner, the content-ish, the tensor-ish)
                    exact hbodyCxF hΓ₁ hnc₁ hadm hK rfl hb
            | @app E' Γg' Γu' W' b' g' u' hg' hu' hs2 =>
                by_cases hadm : CxBAdmissible X
                · exact hspineCxC_tokenfree_dead hadm hΓ₁ hnc₁
                    (Typed.app hg' hu' hs2)
                · exact hspineCxC hL hR hncL hncR
                    (Or.inl (fired_eq_arg hΓL' hrest))
                    (Typed.app hg' hu' hs2) ha
                    (fun _ _ he => (Term.noConfusion he : False))
            | @lete E' Γa Γb a' b' c' t' body ht' hb' hs2 =>
                by_cases hadm : CxBAdmissible X
                · exact hspineCxC_tokenfree_dead hadm hΓ₁ hnc₁
                    (Typed.lete ht' hb' hs2)
                · exact hspineCxC hL hR hncL hncR
                    (Or.inl (fired_eq_arg hΓL' hrest))
                    (Typed.lete ht' hb' hs2) ha
                    (fun _ _ he => (Term.noConfusion he : False))
            | @fix Γfx a' body hnl hb'' =>
                by_cases hadm : CxBAdmissible X
                · exact hspineCxC_tokenfree_dead hadm hΓ₁ hnc₁ (Typed.fix hnl hb'')
                · exact hspineCxC hL hR hncL hncR
                    (Or.inl (fired_eq_arg hΓL' hrest))
                    (Typed.fix hnl hb'') ha
                    (fun _ _ he => (Term.noConfusion he : False))
            | @contr Γfx k t' τ' hk h'' =>
                exact hcontrCxC hΓ₁ marchCtx'_nil hnc₁ noContent_nil
                  (Or.inr ⟨rfl, rfl⟩) hk h'' (Typed.contr hk h'')
            | @weak Γfx k t' τ' hk h'' =>
                exact hweakCxC hΓ₁ marchCtx'_nil hnc₁ noContent_nil
                  (Or.inr ⟨rfl, rfl⟩) hk h'' (Typed.weak hk h'')
      | @lete E Γ₁ Γ₂ a b c t' body ht hb hs =>
          exact hleteCxC hL hR hncL hncR ht hb (hs.trans heq)
      | @fix Γ' a' body hnl hb =>
          -- the fix's context IS the frame: the token is a linear
          -- member — the AllNonLinear side condition contradicts
          have hpos' : Γ[ΓL.length]? = some Ty.content := by
            rw [heq]; exact frame_token
          exact Bool.noConfusion (hnl ΓL.length Ty.content hpos')
      | @contr Γ' k t' τ' hk h' =>
          cases ΓL with
          | nil =>
              have hk' : Ty.content.isLinear = false := by
                have hkeq : k = Ty.content := by injection heq
                subst hkeq
                exact hk
              exact Bool.noConfusion hk'
          | cons a ΓL' =>
              have hΓ' : Γ' = ΓL' ++ Ty.content :: ΓR := by injection heq
              have hka : k = a := by injection heq
              have hknc : k ≠ Ty.content := fun h =>
                hncL 0 a List.get?_zero_cons' (hka ▸ h)
              have hncL' : NoContent ΓL' := by
                intro i b hpos
                exact hncL (i + 1) b (by rw [List.get?_succ_cons']; exact hpos)
              have hlt : size h' < fuel := by rw [size_contr] at hsz; omega
              exact ih (size h') hlt (k :: k :: Γ') (k :: k :: ΓL') ΓR
                (marchCtx'_cons (hka ▸ (hL 0 a List.get?_zero_cons'))
                  (marchCtx'_cons (hka ▸ (hL 0 a List.get?_zero_cons'))
                    (marchCtx'_of_cons hL))) hR
                (noContent_cons hknc (noContent_cons hknc hncL')) hncR
                (by rw [hΓ']; rfl) h' (by rw [size_contr] at hsz; omega)
      | @weak Γ' k t' τ' hk h' =>
          cases ΓL with
          | nil =>
              have hk' : Ty.content.isLinear = false := by
                have hkeq : k = Ty.content := by injection heq with hk_eq _
                subst hkeq
                exact hk
              exact Bool.noConfusion hk'
          | cons a ΓL' =>
              have hΓ' : Γ' = ΓL' ++ Ty.content :: ΓR := by injection heq
              have hncL' : NoContent ΓL' := by
                intro i b hpos
                exact hncL (i + 1) b (by rw [List.get?_succ_cons']; exact hpos)
              have hlt : size h' < fuel := by rw [size_weak] at hsz; omega
              exact ih (size h') hlt Γ' ΓL' ΓR (marchCtx'_of_cons hL) hR
                hncL' hncR hΓ' h' (by rw [size_weak] at hsz; omega)
      | @var a' =>
          cases ΓL with
          | nil =>
              have hcc : Ty.tensor Ty.content Ty.content = Ty.content := by
                injection heq with hhead _
              exact Ty.noConfusion hcc
          | cons a ΓL' =>
              have hlen := congrArg List.length heq
              simp only [List.length_cons, List.length_nil, List.length_append,
                List.length_cons] at hlen
              omega

/-- The contraction law's conditional full-fragment theorem:
`[content] ⊬ C⊗C` in ALL trees (fixpoints included) under seven named
residuals plus the vanishing-march pass-through (the two laws share the
base machinery — the lete arm's killer-comps route through the vanishing
march's territory). The bare `no_contraction_content` stays reserved for
the unrestricted theorem. HONESTY STATUS (kernel-measured, the
interval-18 falsity map below): TWO of the seven residuals are REFUTED
at their landed shapes (`hbodyCxF` — the knower and cloner-bound routes;
`hclonerCxC` — the IDENTITY route, the seventh falsification), and a
THIRD was refuted in its ORIGINAL unfired shape (`hspineCxC` — the
partial-application and var-read routes, kept as `HspineCxCLanded` +
`hspineCxC_refuted`); its INSTALLED shape is the FIRED repair, which has
resisted every witness hunt so far but is not proven. So
THIS THEOREM IS NOT INSTANTIABLE AS STATED; the repairs (the fired-
shape, CxBAdmissible-F, and the codomain restriction) are derived and
recorded in the falsity map section. The four other residuals resisted
all witness attempts; the march's own frame discipline is sound (the
order arithmetic protects it — see the falsity map's note). -/
theorem no_contraction_fix_conditional
    (hspineCxC : ∀ {Γg Γa ΓL ΓR : List Ty} {X : Ty} {fn arg : Term},
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        (Γg ++ Γa = ΓL ++ Ty.content :: ΓR ∨ Γg ++ Γa = ΓL ∧ ΓR = []) →
        Typed Γg fn (Ty.arrow X (.tensor Ty.content Ty.content)) →
        Typed Γa arg X →
        (∀ (a' : Ty) (body' : Term), fn ≠ Term.lam a' body') → False)
    (hbodyCxCM : ∀ {Γ ΓL ΓR : List Ty} {X : Ty} {t : Term},
        CxBAdmissible X →
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        Γ = X :: (ΓL ++ Ty.content :: ΓR) →
        Typed Γ t (.tensor Ty.content Ty.content) → False)
    (hbodyCxF : ∀ {Γ ΓL : List Ty} {X : Ty} {t : Term},
        MarchCtx' ΓL → NoContent ΓL → ¬CxBAdmissible X → ¬ NeedsK X →
        Γ = X :: ΓL →
        Typed Γ t (.tensor Ty.content Ty.content) → False)
    (hclonerCxC : ∀ {Δ : List Ty} {X : Ty} {u : Term},
        MarchCtx' Δ → NoContent Δ → DeepConsume X → ¬ CSupply X →
        Typed Δ u X → False)
    (hcontrCxC : ∀ {Γg ΓL ΓR : List Ty} {X : Ty} {k : Ty} {Γfx : List Ty}
        {t' : Term} {fn : Term},
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        (Γg = ΓL ++ Ty.content :: ΓR ∨ Γg = ΓL ∧ ΓR = []) →
        (hk : k.isLinear = false) →
        (h'' : Typed (k :: k :: Γfx) t' (Ty.arrow X (.tensor Ty.content Ty.content))) →
        Typed Γg fn (Ty.arrow X (.tensor Ty.content Ty.content)) → False)
    (hweakCxC : ∀ {Γg ΓL ΓR : List Ty} {X : Ty} {k : Ty} {Γfx : List Ty}
        {t' : Term} {fn : Term},
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        (Γg = ΓL ++ Ty.content :: ΓR ∨ Γg = ΓL ∧ ΓR = []) →
        (hk : k.isLinear = false) →
        (h'' : Typed Γfx t' (Ty.arrow X (.tensor Ty.content Ty.content))) →
        Typed Γg fn (Ty.arrow X (.tensor Ty.content Ty.content)) → False)
    (hleteCxC : ∀ {Γ₁ Γ₂ ΓL ΓR : List Ty} {a b : Ty} {t body : Term},
        MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
        Typed Γ₁ t (Ty.tensor a b) → Typed (b :: a :: Γ₂) body
          (.tensor Ty.content Ty.content) →
        Γ₁ ++ Γ₂ = ΓL ++ Ty.content :: ΓR → False)
    (hvanish :
      (∀ (fuel : Nat) (Γ ΓL ΓR : List Ty), MarchCtx' ΓL → MarchCtx' ΓR →
        Γ = ΓL ++ Ty.content :: ΓR →
        ∀ {t : Term} (h : Typed Γ t Ty.unit), size h ≤ fuel → False)
      ∧
      (∀ (fuel : Nat) (Γ : List Ty), MarchCtx' Γ →
        ∀ (X σ : Ty), DeepConsume (Ty.arrow X σ) →
        (X = Ty.content ∨ ∃ a', X = Ty.later a') → MarchOK' X →
        EndsInUnit σ → ¬ ContainsLive σ →
        ∀ (fn : Term) (h : Typed Γ fn (Ty.arrow X σ)), size h ≤ fuel → False)) :
    ∀ (t : Term), Typed [Ty.content] t (.tensor Ty.content Ty.content) → False := by
  intro t h
  exact march_cxC_block hspineCxC hbodyCxCM hbodyCxF hclonerCxC hcontrCxC hweakCxC
    hleteCxC hvanish
    (size h) [Ty.content] [] [] marchCtx'_nil marchCtx'_nil noContent_nil noContent_nil
    rfl h (Nat.le_refl _)

/-! ## The interval-18 contraction falsity map (kernel-checked, the
workers' + fp17's hunts)

THREE of the seven residuals are REFUTED at their landed shapes:

(1) `hspineCxC` — REFUTED twice, both by the VALUE-vs-FIRE lesson (the
record's obs-236: a statement whose subject is a VALUE is refutable by
a closed/partial value; a statement about a FIRE is not): (a) w13's
partial-application route — the produce `λ(content).λ(knower).pair(gen-
minted, token)` at `[]`, partially applied at `[content]`, is a NON-λ
fn at the mid-token frame whose codomain is `arrow knower (C⊗C)` — the
knower funds a SECOND content via the coalgebra (`gen`), so the pair
lives; (b) w14's var-route — `MarchOK' (arrow knower C⊗C)` HOLDS (the
coalgebra family, ledger #70), so the var-read fn at the singleton
`[arrow knower C⊗C]` satisfies every antecedent. THE REPAIR: the
fired-shape (carry the produce's arg — the knower-arg dies at `kprop`,
the content-arg at the workhorse).

(2) `hbodyCxF` — REFUTED: (a) w13's route at `X := knower` — the frame
`[knower]` admits `C⊗C` (duplicate the knower with `contr`, mint
content on each copy — the coalgebra licenses both); (b) w14's route at
the cloner-bound `X := arrow unit (C⊗C)` — `app (var 0) (var 0)` at
`[arrow unit C⊗C, unit]` typechecks (the cloner-position IS the bound).
THE REPAIR: `CxBAdmissible X` (¬CSupply kills the knower and the
cloner-as-bound alike) + the arg-side call-site's class-split.

NOTE the ORDER DISCIPLINE (fp17's own correction — the frame-hole
claim was over-derived): the march's own frames are NOT refuted — a
λ-body frame puts the bound FIRST, and the cloner-fire inside needs the
arg's piece as a SUFFIX, which the no-exchange arithmetic forbids. The
third protection the order discipline has bought (after the spine-bug
and the killer-order findings). The five other residuals resisted all
witness attempts (w14's obs-255/256); the march mechanics read clean.
-/

/-- The coalgebra content-val at `[knower]` — gen fired on the knower,
its content half extracted. The second content-source the F-residual
missed. -/
def knowerContent : Typed [Ty.knower]
    (.lete (.app .gen (.var 0)) (.liftAt 0 (.var 0))) Ty.content :=
  Typed.lete
    (Γ₁ := [Ty.knower]) (Γ₂ := [])
    (Typed.app (Γ := []) (Δ := [Ty.knower]) Typed.gen Typed.var rfl)
    (Typed.weak (k := Ty.knower) rfl Typed.var)
    (by rw [List.append_nil])

/-- The pair at `[knower, content]`: the knower's minted content and
the token — the cloner-witness's body. -/
def knowerTokenPair : Typed [Ty.knower, Ty.content]
    (.pair (.lete (.app .gen (.var 0)) (.liftAt 0 (.var 0))) (.var 0))
    (.tensor Ty.content Ty.content) :=
  Typed.pair (Γ := [Ty.knower]) (Δ := [Ty.content]) knowerContent Typed.var rfl

/-- `hspineCxC` IS FALSE (route (a)): the partial application at
`[content]` is a non-λ fn with codomain `arrow knower (C⊗C)`. -/
def HspineCxCLanded : Prop :=
  ∀ {Γg ΓL ΓR : List Ty} {X : Ty} {fn : Term},
    MarchCtx' ΓL → MarchCtx' ΓR → NoContent ΓL → NoContent ΓR →
    (Γg = ΓL ++ Ty.content :: ΓR ∨ Γg = ΓL ∧ ΓR = []) →
    Typed Γg fn (Ty.arrow X (.tensor Ty.content Ty.content)) →
    (∀ (a' : Ty) (body' : Term), fn ≠ Term.lam a' body') → False

theorem hspineCxC_refuted (h : HspineCxCLanded) : False :=
  h (Γg := [Ty.content]) (ΓL := []) (ΓR := []) (X := Ty.knower)
    (fn := .app (.lam Ty.content (.lam Ty.knower
      (.pair (.lete (.app .gen (.var 0)) (.liftAt 0 (.var 0))) (.var 0))))
      (.var 0))
    marchCtx'_nil marchCtx'_nil noContent_nil noContent_nil
    (Or.inl rfl)
    (Typed.app (Γ := []) (Δ := [Ty.content])
      (Typed.lam (Typed.lam knowerTokenPair)) Typed.var rfl)
    (by intro a' body' hlam; exact Term.noConfusion hlam)

/-- `hbodyCxF` IS FALSE (route (a)): the doubled knower's two minted
contents, paired — `C⊗C` at `[knower]` via `contr`. -/
def knowerPair : Typed [Ty.knower]
    (.pair (.lete (.app .gen (.var 0)) (.liftAt 0 (.var 0)))
           (.lete (.app .gen (.var 0)) (.liftAt 0 (.var 0))))
    (.tensor Ty.content Ty.content) :=
  Typed.contr (k := Ty.knower) rfl
    (Typed.pair (Γ := [Ty.knower]) (Δ := [Ty.knower])
      knowerContent knowerContent rfl)

theorem hbodyCxF_refuted
    (h : ∀ {Γ ΓL : List Ty} {X : Ty} {t : Term},
        MarchCtx' ΓL → NoContent ΓL →
        Γ = X :: ΓL →
        Typed Γ t (.tensor Ty.content Ty.content) → False) : False :=
  h (Γ := [Ty.knower]) (ΓL := []) (X := Ty.knower)
    marchCtx'_nil noContent_nil rfl knowerPair

/-- The knower frame is NEVER a march frame (w13's T3b fact): the
discipline bans it — the residual X-slots were the only place the
knower config could hide. -/
theorem marchOK'_knower_false : ¬ MarchOK' Ty.knower := by
  intro h
  exact marchOK'_notNeedsK h (by simp [NeedsK])

/-- The cloner-bound's type is ¬NeedsK — the ¬NeedsK-only repair's
blind spot (w14's decisive catch). -/
theorem notNeedsK_clonerBound :
    ¬ NeedsK (Ty.arrow Ty.unit (.tensor Ty.content Ty.content)) := by
  rintro ⟨h, _⟩
  rcases h with h | h
  · simp only [NeedsK] at h
  · simp only [NeedsK] at h

/-- But it IS content-supplying — the CxBAdmissible repair's kill. -/
theorem cSupply_clonerBound :
    CSupply (Ty.arrow Ty.unit (.tensor Ty.content Ty.content)) :=
  Or.inl ⟨(Or.inl trivial), by simp [NeedsC], by simp [NeedsK]⟩

/-- w14's second witness: the cloner-bound body. -/
def clonerBoundBody : Typed [Ty.arrow Ty.unit (.tensor Ty.content Ty.content), Ty.unit]
    (.app (.var 0) (.var 0)) (.tensor Ty.content Ty.content) :=
  Typed.app (Γ := [Ty.arrow Ty.unit (.tensor Ty.content Ty.content)])
    (Δ := [Ty.unit]) Typed.var Typed.var rfl

/-- The F-residual is refuted at a SECOND X — the cloner bound, which
¬NeedsK X does not exclude. -/
theorem hbodyCxF_refuted_second
    (h : ∀ {Γ ΓL : List Ty} {X : Ty} {t : Term},
        MarchCtx' ΓL → NoContent ΓL →
        Γ = X :: ΓL →
        Typed Γ t (.tensor Ty.content Ty.content) → False) : False :=
  h (Γ := [Ty.arrow Ty.unit (.tensor Ty.content Ty.content), Ty.unit])
    (ΓL := [Ty.unit]) (X := Ty.arrow Ty.unit (.tensor Ty.content Ty.content))
    (marchCtx'_cons marchOK'_unit marchCtx'_nil)
    (noContent_cons (by intro hc; cases hc) noContent_nil)
    rfl clonerBoundBody

/-- The knower route is not admissible. -/
theorem not_admissible_knower : ¬ CxBAdmissible Ty.knower :=
  fun ⟨hnc, _⟩ => hnc (Or.inr trivial)

/-- The cloner-bound route is not admissible either. -/
theorem not_admissible_clonerBound :
    ¬ CxBAdmissible (Ty.arrow Ty.unit (.tensor Ty.content Ty.content)) :=
  fun ⟨hnc, _⟩ => hnc cSupply_clonerBound


/-! ## THE SEVENTH FALSIFICATION (interval 18, the (α) design's T3)

`hclonerCxC` AS STATED IS FALSE: the IDENTITY function refutes it.
`X = arrow content content` is DeepConsume (the domain disjunct) ∧
¬CSupply (the content domain negates both need-conjunctions) — and
`λ(content).var 0 : [] ⊢ arrow content content` EXISTS. The residual's
every hypothesis holds at the identity.

THE REPAIR DIRECTION (derived, not yet landed): the codomain
restriction `EndsInUnit X` excludes the identity (EndsInUnit (arrow
content content) = EndsInUnit content = False) — but OPENS the
λ-descent at NON-PRIMED extended frames (MarchOK′ ACU = false), so
the (α) induction must handle the extended frames themselves: the
pair-split arithmetic at the identity-extended frame (the
identity-bound is ¬CSupply — NOT a content source; the token supplies
one side; the other dies at the content-free piece). The march's own
STATEMENT survives (the identity-arg fire cannot produce a C⊗C at a
unique-content frame — all pair-splits die), but the residual layer
needs the repair before the march's proof closes. -/

/-- THE IDENTITY: `λ(content).var 0 : [] ⊢ arrow content content`. -/
def identityCxC : Typed []
    (.lam Ty.content (.var 0)) (Ty.arrow Ty.content Ty.content) :=
  Typed.lam Typed.var

/-- The identity's type is DeepConsume (the domain-content disjunct). -/
theorem deepConsume_arrowContentContent :
    DeepConsume (Ty.arrow Ty.content Ty.content) := by
  unfold DeepConsume
  exact Or.inl (Or.inl rfl)

/-- And ¬CSupply (the content domain negates both need-conjunctions). -/
theorem notCSupply_arrowContentContent :
    ¬ CSupply (Ty.arrow Ty.content Ty.content) := by
  intro hcs
  rcases hcs with hc | hk
  · exact (by simp [NeedsC] : ¬ NeedsC (Ty.arrow Ty.content Ty.content)) hc
  · exact (by simp [NeedsK] : ¬ NeedsK (Ty.arrow Ty.content Ty.content)) hk

/-- `hclonerCxC` AS STATED IS FALSE — the identity instantiates every
hypothesis. -/
theorem hclonerCxC_refuted
    (h : ∀ {Δ : List Ty} {X : Ty} {u : Term},
        MarchCtx' Δ → NoContent Δ → DeepConsume X → ¬ CSupply X →
        Typed Δ u X → False) : False :=
  h marchCtx'_nil noContent_nil deepConsume_arrowContentContent
    notCSupply_arrowContentContent identityCxC

/-! ## THE CARRIER-DOMAIN FIRE — w24's k-split, the engines (fp19)

Transferred from /tmp/probe/pt_carrier2.lean (the k-split draft). THE
CONFIG (the (M)-app's fn-side carrier case, after the refutation round):
`t = app fn arg : C⊗C` at the one-source M-frame `ΓL ++ ΓS :: ΓR`,
`fn : Γ₁ ⊢ arrow X C⊗C` (the source fn-side), `arg : Δ ⊢ X` at an
all-admissible piece, `X` a CARRIER domain (`¬CSupply X`, `¬NeedsK X`,
`ContainsCxC X`).

`towerDepth X` = the number of `CSupply` domains along the arrow chain
(each `CSupply` domain's fire needs a supply-funded arg). The k-split:
`k ≤ 1` → the ARG is dead (availability: no value of a k≤1 carrier
inhabits an admissible piece); `k ≥ 2` → the arg may be CLOSED
(`closedTowerVal` — availability fails), and the kill is at the
PRODUCE: the fn's body fires the X-read on ≥2 supply-args at disjoint
pieces of a one-source frame.

THIS SECTION carries the placeholder-free part: the depth measure, the
engines at the ¬CSupply grain (the carrier-headed frames are not
`AllAdm` — the head is a carrier — so the in-tree counting engines are
restated with `NoCSupply` pieces, which is all their proofs ever
used), the cheap arg heads, the k=2 closed val, and the two measured
refutations. The two arms (`carrier_arg_arm_k1`, `carrier_body_arm_k2`)
and the dispatch (`carrier_fire_k_split`) are march-grain statements
(their proofs are the Λ-descent / the spine counting with the march's
shims) — they land with the counting-march assembly, not here.

MEASURED FINDING (the unguarded-source refutation): the fire-level
config WITHOUT `¬ContainsCxC ΓS` is FALSE — the producer-as-source
witness `ΓS := arrow X C⊗C` with `app (var 0) closedTowerVal` derives
`C⊗C` at `[arrow X C⊗C]` with no content spent. The M-frame's source
slot needs `CSupply ∧ ¬NeedsK ∧ ¬ContainsCxC`. -/

section CarrierFireEngines
open Classical

/-- The `CSupply`-domain count of the arrow chain. `later` is opaque. -/
noncomputable def towerDepth : Ty → Nat
  | .arrow a σ => if CSupply a then 1 + towerDepth σ else towerDepth σ
  | _ => 0

theorem towerDepth_arrow {a σ : Ty} :
    towerDepth (.arrow a σ) = (if CSupply a then 1 + towerDepth σ else towerDepth σ) :=
  rfl

/-- The additive normal form (the one the march's arithmetic wants). -/
theorem towerDepth_arrow' {a σ : Ty} :
    towerDepth (.arrow a σ) = (if CSupply a then 1 else 0) + towerDepth σ := by
  rw [towerDepth_arrow]
  split <;> omega

theorem towerDepth_later {a : Ty} : towerDepth (.later a) = 0 := rfl

theorem cSupply_content : CSupply Ty.content := Or.inl trivial

/-- The tower (one `CSupply` domain, `content`) has depth 1. -/
theorem towerDepth_tower :
    towerDepth (Ty.arrow Ty.unit (Ty.arrow Ty.content (.tensor Ty.content Ty.content))) = 1 := by
  rw [towerDepth_arrow, ite_eq_right notCSupply_unit,
    towerDepth_arrow, ite_eq_left cSupply_content]
  rfl

/-- The closed tower (two `content` domains, then a `unit`) has depth 2. -/
theorem towerDepth_closedTower :
    towerDepth (Ty.arrow Ty.content (Ty.arrow Ty.content
      (Ty.arrow Ty.unit (.tensor Ty.content Ty.content)))) = 2 := by
  rw [towerDepth_arrow, ite_eq_left cSupply_content,
    towerDepth_arrow, ite_eq_left cSupply_content,
    towerDepth_arrow, ite_eq_right notCSupply_unit]
  rfl

/-- The k = 0 case is real: the CLONER's type (`arrow unit C⊗C`) has no
`CSupply` domain. -/
theorem towerDepth_cloner : towerDepth (Ty.arrow Ty.unit (.tensor Ty.content Ty.content)) = 0 := by
  rw [towerDepth_arrow, ite_eq_right notCSupply_unit]
  rfl

/-- Depth positivity, the classification the march reasons with. -/
theorem towerDepth_pos_arrow {a σ : Ty} :
    0 < towerDepth (.arrow a σ) ↔ CSupply a ∨ 0 < towerDepth σ := by
  rw [towerDepth_arrow]
  split <;> simp_all <;> omega

/-! ### The engines at the ¬CSupply grain

The carrier-extended frames (`X :: ΓL ++ ΓS :: ΓR`, `X` a carrier) are
`NoCSupply` but NOT `AllAdm`. The in-tree counting engines demand
`AllAdm` pieces; their proofs use only the `¬CSupply` half of it, so
the restated versions below are the ones the march's carrier cases can
actually call. -/

/-- E1 — the single-source engine at the ¬CSupply grain. -/
theorem csupply_pos_eq_source_ns {ΓL : List Ty} {ΓS : Ty} {ΓR : List Ty}
    {i : Nat} {b : Ty} (hL : NoCSupply ΓL) (hR : NoCSupply ΓR)
    (hpos : (ΓL ++ ΓS :: ΓR)[i]? = some b) (hcs : CSupply b) :
    i = ΓL.length ∧ b = ΓS := by
  by_cases hlt : i < ΓL.length
  · rw [List.get?_append_lt hlt] at hpos
    exact absurd hcs (hL i b hpos)
  · by_cases heq : i = ΓL.length
    · subst heq
      rw [List.get?_append_ge (Nat.le_refl ΓL.length), Nat.sub_self,
        List.get?_zero_cons'] at hpos
      injection hpos with hb
      exact ⟨rfl, hb.symm⟩
    · have hge : ΓL.length < i := by omega
      rw [List.get?_append_ge (Nat.le_of_lt hge)] at hpos
      have hk : 1 ≤ i - ΓL.length := by omega
      obtain ⟨j, hj⟩ : ∃ j, i - ΓL.length = j + 1 :=
        ⟨i - ΓL.length - 1, by omega⟩
      rw [hj, List.get?_succ_cons'] at hpos
      exact absurd hcs (hR j b hpos)

/-- E2 — THE ONE-SOURCE PAIR KILL, the generalized bound-structure form of
`k1_innermost_pair_dead`: the tower's λ-bounds need only be `¬CSupply`
(they may themselves be carriers); admissibility is not needed. `_hcs`
is carried for fidelity to the config; the counting never uses it. -/
theorem pair_dead_at_one_source {Γ₁ Γ₂ ΓA : List Ty} {ΓS : Ty} {ΓR : List Ty}
    {l r : Term}
    (hA : NoCSupply ΓA) (hR : NoCSupply ΓR) (_hcs : CSupply ΓS)
    (hl : Typed Γ₁ l Ty.content) (hr : Typed Γ₂ r Ty.content)
    (hs : Γ₁ ++ Γ₂ = ΓA ++ ΓS :: ΓR) : False := by
  obtain ⟨i₁, b₁, hpos₁, hcs₁⟩ := cprop hl (by simp [NeedsC])
  obtain ⟨i₂, b₂, hpos₂, hcs₂⟩ := cprop hr (by simp [NeedsC])
  have hlt₁ : i₁ < Γ₁.length := get?_lt_of_some hpos₁
  have hlt₂ : i₂ < Γ₂.length := get?_lt_of_some hpos₂
  by_cases hlen : ΓA.length < Γ₁.length
  · have h1 : (Γ₁ ++ Γ₂)[Γ₁.length + i₂]? = some b₂ := by
      rw [List.get?_append_ge (Nat.le_add_right Γ₁.length i₂),
        Nat.add_sub_cancel_left]
      exact hpos₂
    have hge : ΓA.length ≤ Γ₁.length + i₂ :=
      Nat.le_trans (Nat.le_of_lt hlen) (Nat.le_add_right Γ₁.length i₂)
    rw [hs, List.get?_append_ge hge] at h1
    have hk : 1 ≤ Γ₁.length + i₂ - ΓA.length := by omega
    obtain ⟨j, hj⟩ : ∃ j, Γ₁.length + i₂ - ΓA.length = j + 1 :=
      ⟨Γ₁.length + i₂ - ΓA.length - 1, by omega⟩
    rw [hj, List.get?_succ_cons'] at h1
    exact hR j b₂ h1 hcs₂
  · have hle : Γ₁.length ≤ ΓA.length := Nat.not_lt.mp hlen
    have h1 : (Γ₁ ++ Γ₂)[i₁]? = some b₁ := by
      rw [List.get?_append_lt hlt₁]
      exact hpos₁
    rw [hs, List.get?_append_lt (Nat.lt_of_lt_of_le hlt₁ hle)] at h1
    exact hA i₁ b₁ h1 hcs₁

/-- E3 — the SUPPLY-FREE pair kill: at a frame with no supply position at
all (the k = 0 carrier's peeled frame), the pair dies outright. -/
theorem pair_dead_at_nocsupply_frame {Γ₁ Γ₂ Γ : List Ty} {l r : Term}
    (hΓ : NoCSupply Γ)
    (hl : Typed Γ₁ l Ty.content) (_hr : Typed Γ₂ r Ty.content)
    (hs : Γ₁ ++ Γ₂ = Γ) : False := by
  obtain ⟨i₁, b₁, hpos₁, hcs₁⟩ := cprop hl (by simp [NeedsC])
  have hlt₁ : i₁ < Γ₁.length := get?_lt_of_some hpos₁
  have h1 : (Γ₁ ++ Γ₂)[i₁]? = some b₁ := by
    rw [List.get?_append_lt hlt₁]
    exact hpos₁
  rw [hs] at h1
  exact hΓ i₁ b₁ h1 hcs₁

/-- E4 — THE k ≥ 2 ENGINE at the ¬CSupply grain: two content-funding args
at disjoint ORDERED pieces (prefix ○ suffix) of a one-source frame. This
is the in-tree `two_supply_disjoint` with the `AllAdm` pieces weakened to
`NoCSupply`. -/
theorem two_supply_disjoint_ns {ΓL ΓR Γ₁ Γ₂ Δ : List Ty} {ΓS : Ty}
    {a₁ a₂ : Term}
    (hL : NoCSupply ΓL) (hR : NoCSupply ΓR) (_hcs : CSupply ΓS)
    (h₁ : Typed Γ₁ a₁ Ty.content) (h₂ : Typed Γ₂ a₂ Ty.content)
    (hs : (Γ₁ ++ Δ) ++ Γ₂ = ΓL ++ ΓS :: ΓR) : False := by
  obtain ⟨i₁, b₁, hp₁, hc₁⟩ := cprop h₁ (by simp [NeedsC])
  obtain ⟨i₂, b₂, hp₂, hc₂⟩ := cprop h₂ (by simp [NeedsC])
  have hlt₁ : i₁ < Γ₁.length := get?_lt_of_some hp₁
  have hf₁ : (ΓL ++ ΓS :: ΓR)[i₁]? = some b₁ := by
    rw [← hs, List.get?_append_lt (by rw [List.length_append]; omega)]
    rw [List.get?_append_lt hlt₁]
    exact hp₁
  have hi₁ : i₁ = ΓL.length := (csupply_pos_eq_source_ns hL hR hf₁ hc₁).1
  have hf₂ : (ΓL ++ ΓS :: ΓR)[(Γ₁ ++ Δ).length + i₂]? = some b₂ := by
    rw [← hs, List.get?_append_ge (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    exact hp₂
  have hi₂ : (Γ₁ ++ Δ).length + i₂ = ΓL.length :=
    (csupply_pos_eq_source_ns hL hR hf₂ hc₂).1
  rw [List.length_append] at hi₂
  omega

/-- The fn's type is content-needing whenever its domain is a carrier
(`NeedsC C⊗C = True`, and the domain's two negations come from the
carrier's `¬CSupply`/`¬NeedsK`). (The ¬CSupply-grain twin of the
in-tree `needsC_arrow_cxC`, which needs the stronger `CxBAdmissible`.) -/
theorem needsC_arrow_cxC_ns {X : Ty} (hX : ¬ CSupply X) (hXK : ¬ NeedsK X) :
    NeedsC (Ty.arrow X (.tensor Ty.content Ty.content)) := by
  refine ⟨?_, ?_, hXK⟩
  · exact Or.inl trivial
  · exact fun hc => hX (Or.inl hc)

/-! ### The arg arm's cheap heads (CLOSED) -/

/-- A carrier at an admissible piece is never a var-read: the singleton
frame would be `[X]`, and admissibility forbids a carrier position
(`AdmPos = ¬CSupply ∧ ¬ContainsCxC`). -/
theorem carrier_arg_not_var {Δ : List Ty} {X : Ty} {arg : Term}
    (hΔ : AllAdm Δ) (hcx : ContainsCxC X)
    (harg : Typed Δ arg X) (hvar : arg = Term.var 0) : False := by
  obtain ⟨a, hΓ, hτ⟩ := var_canonical harg hvar
  subst hτ
  subst hΓ
  exact (hΔ 0 X (List.get?_zero_cons')).2 hcx

/-- A content-needing carrier dies at the cprop demand (the piece is
supply-free). Covers the TENSOR carriers and the `CSupply` carriers. -/
theorem carrier_arg_dead_of_needsC {Δ : List Ty} {X : Ty} {arg : Term}
    (hΔ : AllAdm Δ) (hn : NeedsC X) (harg : Typed Δ arg X) : False :=
  needsC_val_dead_at_nocsupply (allAdm_noCSupply hΔ) hn harg

/-- The knower-side twin. -/
theorem carrier_arg_dead_of_needsK {Δ : List Ty} {X : Ty} {arg : Term}
    (hΔ : AllAdm Δ) (hn : NeedsK X) (harg : Typed Δ arg X) : False :=
  needsK_val_dead_at_nocsupply (allAdm_noCSupply hΔ) hn harg

/-! ### The k ≥ 2 closed val (availability fails at k ≥ 2)

`closedTowerVal` is typed at `[]` — an ALL-ADMISSIBLE piece — so the arg
arm cannot be a blanket availability claim: the k ≥ 2 kill must be at the
produce. (The k = 1 closed val does NOT exist: its pair needs a second
content and the tower has one.) -/

def towerTy : Ty := Ty.arrow Ty.content (Ty.arrow Ty.content (Ty.arrow Ty.unit
  (.tensor Ty.content Ty.content)))

/-- `λc₁.λc₂.λu. pair (weak-past-u c₁) c₂ : [] ⊢ arrow content (arrow
content (arrow unit C⊗C))`. The side1 read is weak-lifted past the
NON-LINEAR `unit` head; both contents are λ-bounds. -/
def closedTowerTerm : Term :=
  .lam Ty.content (.lam Ty.content (.lam Ty.unit
    (.pair (.liftAt 0 (.var 0)) (.var 0))))

def closedTowerVal : Typed [] closedTowerTerm towerTy :=
  Typed.lam
    (Typed.lam
      (Typed.lam
        (Typed.pair
          (Typed.weak (k := Ty.unit) rfl (Typed.var (a := Ty.content)))
          (Typed.var (a := Ty.content))
          rfl)))

theorem notCSupply_towerTy : ¬ CSupply towerTy := by
  intro h
  rcases h with h | h <;> simp [towerTy, NeedsC, NeedsK] at h

theorem notNeedsK_towerTy : ¬ NeedsK towerTy := by
  simp [towerTy, NeedsK]

theorem containsCxC_towerTy : ContainsCxC towerTy := by
  simp [towerTy, ContainsCxC]

theorem cSupply_arrow_towerTy : CSupply (Ty.arrow towerTy (.tensor Ty.content Ty.content)) := by
  refine Or.inl ⟨Or.inl trivial, ?_, notNeedsK_towerTy⟩
  exact fun hc => notCSupply_towerTy (Or.inl hc)

theorem notNeedsK_arrow_towerTy : ¬ NeedsK (Ty.arrow towerTy (.tensor Ty.content Ty.content)) := by
  simp [NeedsK]

/-- MEASURED FINDING: the fire-level config WITHOUT `¬ContainsCxC ΓS` is
FALSE. The witness: the source slot holds the PRODUCER TYPE
`arrow X C⊗C` itself (`CSupply` by the codomain's `C⊗C` need,
`¬NeedsK` likewise), and the fire `app (var 0) closedTowerVal` derives
`C⊗C` at `[arrow X C⊗C]` — one position, no content spent. -/
theorem carrier_fire_unguarded_refuted :
    ¬ (∀ (ΓL ΓR Γ₁ Δ : List Ty) (ΓS X : Ty) (fn arg : Term),
        AllAdm ΓL → AllAdm ΓR → CSupply ΓS → ¬ NeedsK ΓS →
        ¬ CSupply X → ¬ NeedsK X → ContainsCxC X → AllAdm Δ →
        Typed Γ₁ fn (Ty.arrow X (.tensor Ty.content Ty.content)) →
        Typed Δ arg X →
        Γ₁ ++ Δ = ΓL ++ ΓS :: ΓR → False) := by
  intro h
  exact h [] [] [Ty.arrow towerTy (.tensor Ty.content Ty.content)] []
    (Ty.arrow towerTy (.tensor Ty.content Ty.content)) towerTy
    (.var 0) closedTowerTerm
    allAdm_nil allAdm_nil
    (cSupply_arrow_towerTy) (notNeedsK_arrow_towerTy)
    notCSupply_towerTy notNeedsK_towerTy containsCxC_towerTy
    allAdm_nil
    (Typed.var (a := Ty.arrow towerTy (.tensor Ty.content Ty.content)))
    closedTowerVal
    rfl

/-- The arm-2 var-head kill: a `var 0` producer forces `ΓS` to BE the
producer type (a carrier), contradicting `¬ContainsCxC ΓS`. -/
theorem producer_var_head_dead {ΓL ΓR : List Ty} {ΓS X : Ty}
    (hcsrc : ¬ ContainsCxC ΓS)
    (hs : [Ty.arrow X (.tensor Ty.content Ty.content)] = ΓL ++ ΓS :: ΓR) : False := by
  cases ΓL with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at hs
      exact hcsrc (by rw [← hs.1]; simp [ContainsCxC])
  | cons k ΓL' =>
      simp only [List.cons_append, List.cons.injEq] at hs
      have hlen := congrArg List.length hs.2
      simp only [List.length_nil, List.length_append, List.length_cons] at hlen
      omega

end CarrierFireEngines

/-! ## THE ELEVENTH FALSIFICATION (interval 19 — the tower leaks
through a TENSOR-COMP POSITION; the `AdmPos` repair)
`
`tensor tower unit` (tower = `arrow unit (arrow content C⊗C)`) passes
the position discipline `¬CSupply ∧ ¬closure` — the closure is
arrow-only, so the tower wearing a tensor hat walks in — and the frame
`[tensor tower unit, content]` admits a `C⊗C` in one lete + two fires
(the tower at position 1, read past the non-linear unit head; the
inner fire on the CLOSED unit at the empty piece; the outer fire on
the source-read). The repair: `AdmPos := ¬CSupply ∧ ¬ContainsCxC` —
the carrier predicate bans `C⊗C`-carriers from POSITIONS, subsuming
the closure (w14's inclusion) and surviving both of w13's round-4
attacks (the ordinary lete comps stay legal; no fifth leak route). -/

/-- The eleventh witness: the tower leaked through a tensor-comp. -/
def eleventhTower : Typed
    [Ty.tensor (Ty.arrow Ty.unit (Ty.arrow Ty.content (.tensor Ty.content Ty.content))) Ty.unit,
     Ty.content]
    (Term.lete (Term.var 0)
      (Term.app (Term.app (Term.liftAt 0 (Term.var 0)) Term.unit) (Term.var 0)))
    (.tensor Ty.content Ty.content) :=
  Typed.lete (Γ₂ := [Ty.content])
    Typed.var
    (Typed.app
      (Typed.app (Typed.weak (by rfl) Typed.var) Typed.unit rfl)
      Typed.var rfl)
    rfl

/-- The eleventh's frame-position carries the tower (banned by the
repaired discipline). -/
theorem containsCxC_tensorTowerUnit :
    ContainsCxC (Ty.tensor (Ty.arrow Ty.unit (Ty.arrow Ty.content (.tensor Ty.content Ty.content)))
      Ty.unit) := by
  simp only [ContainsCxC]
  exact Or.inl trivial

/-! ## THE CARRIER/YIELD ENGINE LAYER (fp19 intervals 19-20, the
counting-march's clean foundation — w25..w43's parallel rounds)

The counting-march's engine inventory, transferred from the assembly
probe: the yield layers (frame-relative `yieldIn`, universal `yieldAll`,
closed-only `yieldC` with all inclusions), the liveness/funding
plumbing, the provenance layer (a `NeedsC` type always has universal
yield ≥ 1 — the source's own comps cannot both be supplies), the
carrier bridge (`ContainsCxC τ → 2 ≤ yieldAll τ` — so `¬ContainsCxC`
on sources is a THEOREM of the yield bound), the ns-grain pair kills,
the deep-type engine, and the produce-head kills. The march itself
(the six-conjunct mutual induction at these engines) remains a /tmp
working artifact at 56 named residuals — the record's seven-architecture
falsification map (obs 282-312) is the boundary. -/
open Classical
section CarrierYieldEngines


open Dcare
open Classical

/-- The supply-kill at an AllAdm piece (the splice-level helper). -/
theorem supply_val_dead_at_allAdmS {Γ : List Ty} (hA : AllAdm Γ) {τ : Ty}
    (hcs : CSupply τ) {t : Term} (h : Typed Γ t τ) : False := by
  rcases hcs with hc | hk
  · exact needsC_val_dead_at_nocsupply (allAdm_noCSupply hA) hc h
  · exact needsK_val_dead_at_nocsupply (allAdm_noCSupply hA) hk h

/-- (F) standalone: no C⊗C value at any AllAdm frame (cprop + the ban). -/
theorem noCxC_at_allAdm {Γ : List Ty} (hA : AllAdm Γ) {t : Term}
    (h : Typed Γ t (Ty.tensor Ty.content Ty.content)) : False :=
  needsC_val_dead_at_nocsupply (allAdm_noCSupply hA) (by simp [NeedsC]) h

/-- The λ-headed produce with an ADMISSIBLE domain X is dead at an AllAdm
frame: the body's frame `X :: Γ` is AllAdm, so (F) refuses the C⊗C body. -/
theorem produce_lam_head_dead {Γ : List Ty} {X : Ty} {body : Term}
    (hA : AllAdm Γ) (hX : AdmPos X)
    (hb : Typed (X :: Γ) body (Ty.tensor Ty.content Ty.content)) : False :=
  noCxC_at_allAdm (allAdm_cons hX hA) hb

/-- The app-headed produce with a ¬CSupply domain X is dead at an AllAdm
frame: either the inner arg dies (W CSupply at the AllAdm piece), or the
inner fn's own type is content-needing and cprop refuses it. -/
theorem produce_app_head_dead {Γ₁ Γa Δv : List Ty} {W X : Ty} {g v : Term}
    (hA : AllAdm Γ₁) (hX : ¬ CSupply X)
    (hg : Typed Γa g (Ty.arrow W (Ty.arrow X (Ty.tensor Ty.content Ty.content))))
    (hv : Typed Δv v W) (hs : Γa ++ Δv = Γ₁) : False := by
  have hAΓa : AllAdm Γa := allAdm_append_left (hs ▸ hA)
  have hAΔv : AllAdm Δv := allAdm_append_right (hs ▸ hA)
  by_cases hW : CSupply W
  · rcases hW with hc | hk
    · exact needsC_val_dead_at_nocsupply (allAdm_noCSupply hAΔv) hc hv
    · exact needsK_val_dead_at_nocsupply (allAdm_noCSupply hAΔv) hk hv
  · have hneeds : NeedsC (Ty.arrow W (Ty.arrow X (Ty.tensor Ty.content Ty.content))) :=
      ⟨⟨Or.inl trivial, fun hc => hX (Or.inl hc), fun hk => hX (Or.inr hk)⟩,
       fun hc => hW (Or.inl hc), fun hk => hW (Or.inr hk)⟩
    exact needsC_val_dead_at_nocsupply (allAdm_noCSupply hAΓa) hneeds hg

/-- A bare producer arrow is a `C⊗C`-carrier (the codomain recursion). -/
theorem containsCxC_arrow_cxC (X : Ty) :
    ContainsCxC (Ty.arrow X (Ty.tensor Ty.content Ty.content)) := trivial

/-- A `C⊗C`-carrier is linear: every path to the embedded `C⊗C` runs
through `tensor`/`arrow`, whose linearity is the join — the linear leaf
wins. (The weak/contr heads cons the carrier into the frame, and their
gates demand `isLinear = false`.) -/
theorem containsCxC_linear {X : Ty} (h : ContainsCxC X) : X.isLinear = true := by
  induction X with
  | content => exact absurd h not_containsCxC_content
  | knower => exact False.elim h
  | knowledge => exact False.elim h
  | value => exact False.elim h
  | stream => exact False.elim h
  | trace => exact False.elim h
  | unit => exact False.elim h
  | later _ => exact False.elim h
  | tensor a b iha ihb =>
      cases a with
      | content =>
          cases b with
          | content => rfl
          | _ =>
              rcases h with h | h
              · rfl
              · simp [Ty.isLinear]
      | _ =>
          rcases h with h | h
          · show (Ty.isLinear _ || Ty.isLinear b) = true
            rw [iha h]
            exact Bool.true_or _
          · show (Ty.isLinear _ || Ty.isLinear b) = true
            rw [ihb h]
            exact Bool.or_true _
  | arrow a b _ ihb =>
      show (Ty.isLinear a || Ty.isLinear b) = true
      rw [ihb h]
      exact Bool.or_true _

/-- Fuelling fact for the (PF) λ-arm. -/
theorem size_lam_lt {Γ a b body} (hb : Typed (a :: Γ) body b) {fuel : Nat}
    (h : size (Typed.lam hb) ≤ fuel) : size hb < fuel := by
  rw [size_lam] at h; omega

/-! ### The yield layer (w28's repair — the compound-source falsifications)

The M-frame source class counts POSITIONS; a compound source hides two
supplies behind one position (the tensor source `tensor (arrow unit
content) content` and the arrow sources `arrow unit (tensor …)` /
`arrow stream (tensor …)` refute (M)/(PF)/(PT)/(P) as stated).
`yieldIn Γ τ` counts the content a value of type τ can mint with its
arrow-domains funded at Γ or closed; the source class gains
`yieldIn (ΓL ++ ΓR) ΓS ≤ 1` and (P) gains `yieldIn Γ X ≤ 1`. -/

noncomputable def ClosedFundable (a : Ty) : Prop := ∃ t : Term, Nonempty (Typed [] t a)

noncomputable def FundableAt (Γ : List Ty) (a : Ty) : Prop :=
  (∃ t : Term, Nonempty (Typed Γ t a)) ∨ ClosedFundable a

noncomputable def yieldIn (Γ : List Ty) : Ty → Nat
  | .content => 1
  | .tensor a b => yieldIn Γ a + yieldIn Γ b
  | .arrow a b => if FundableAt Γ a then yieldIn Γ b else 0
  | _ => 0

theorem yieldIn_content (Γ : List Ty) : yieldIn Γ Ty.content = 1 := rfl
theorem yieldIn_tensor (Γ : List Ty) {a b : Ty} :
    yieldIn Γ (.tensor a b) = yieldIn Γ a + yieldIn Γ b := rfl
theorem yieldIn_arrow (Γ : List Ty) {a b : Ty} :
    yieldIn Γ (.arrow a b) = (if FundableAt Γ a then yieldIn Γ b else 0) := rfl

theorem closedFundable_unit : ClosedFundable Ty.unit := ⟨.unit, ⟨Typed.unit⟩⟩
theorem closedFundable_trace : ClosedFundable Ty.trace := ⟨.nil, ⟨Typed.nil⟩⟩
theorem not_closedFundable_stream : ¬ ClosedFundable Ty.stream := by
  intro ⟨t, ht⟩; obtain ⟨ht⟩ := ht; exact no_closed_stream ht

/-- A closed-fundable domain cannot need anything (cprop/kprop at `[]`). -/
theorem closedFundable_not_needs {a : Ty} (h : ClosedFundable a) : ¬ NeedsC a ∧ ¬ NeedsK a := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨ht⟩ := ht
  constructor
  · intro hc
    obtain ⟨i, b, hpos, -⟩ := cprop ht hc
    rw [List.get?_nil'] at hpos; contradiction
  · intro hk
    obtain ⟨i, b, hpos, -⟩ := kprop ht hk
    rw [List.get?_nil'] at hpos; contradiction

/-- A value of a needing type cannot live at an admissible piece. -/
theorem fundableAt_adm_not_needs {Γ : List Ty} (hA : AllAdm Γ) {a : Ty}
    (h : FundableAt Γ a) : ¬ NeedsC a ∧ ¬ NeedsK a := by
  rcases h with ⟨t, ht⟩ | hcf
  · obtain ⟨ht⟩ := ht
    have hnocs := allAdm_noCSupply hA
    constructor
    · intro hc
      obtain ⟨i, b, hpos, hsup⟩ := cprop ht hc
      exact hnocs i b hpos hsup
    · intro hk
      obtain ⟨i, b, hpos, hK⟩ := kprop ht hk
      exact hnocs i b hpos (Or.inr hK)
  · exact closedFundable_not_needs hcf

theorem yieldIn_pos_needsC {Γ : List Ty} (hA : AllAdm Γ) (a : Ty) (h : 1 ≤ yieldIn Γ a) :
    NeedsC a := by
  induction a with
  | content => trivial
  | knower => simp [yieldIn] at h
  | knowledge => simp [yieldIn] at h
  | value => simp [yieldIn] at h
  | stream => simp [yieldIn] at h
  | trace => simp [yieldIn] at h
  | unit => simp [yieldIn] at h
  | later a iha => simp [yieldIn] at h
  | tensor a b iha ihb =>
      rw [yieldIn_tensor] at h
      by_cases h1 : 1 ≤ yieldIn Γ a
      · exact Or.inl (iha h1)
      · exact Or.inr (ihb (by omega))
  | arrow a b iha ihb =>
      rw [yieldIn_arrow] at h
      split at h
      · next hf =>
          obtain ⟨hca, hka⟩ := fundableAt_adm_not_needs hA hf
          exact ⟨ihb h, hca, hka⟩
      · omega

/-- ¬CSupply ⇒ yield 0 (at admissible pieces): the app-arm's produce calls
can always supply the bound. -/
theorem yieldIn_zero_of_notCSupply {Γ : List Ty} (hA : AllAdm Γ) {a : Ty} (h : ¬ CSupply a) :
    yieldIn Γ a ≤ 1 := by
  by_cases h1 : 1 ≤ yieldIn Γ a
  · exact absurd (Or.inl (yieldIn_pos_needsC hA a h1)) h
  · omega

theorem yieldIn_tensor_ge (Γ : List Ty) {a b : Ty} : yieldIn Γ a ≤ yieldIn Γ (.tensor a b) := by
  rw [yieldIn_tensor]; omega


/-- THE UNIVERSAL YIELD: the maximal content a type can mint with every
arrow-domain funded. Frame-independent (`yieldIn Γ a ≤ yieldAll a` for
every Γ) — the source class uses THIS, so the hypothesis threads through
every frame shift verbatim (the weak/contr/comps/bound extensions need no
per-frame bounds). -/
noncomputable def yieldAll : Ty → Nat
  | .content => 1
  | .tensor a b => yieldAll a + yieldAll b
  | .arrow _ b => yieldAll b
  | _ => 0

theorem yieldAll_content : yieldAll Ty.content = 1 := rfl
theorem yieldAll_tensor {a b : Ty} : yieldAll (.tensor a b) = yieldAll a + yieldAll b := rfl
theorem yieldAll_arrow {a b : Ty} : yieldAll (.arrow a b) = yieldAll b := rfl

/-- The frame-relative yield is bounded by the universal yield (funding
only enables, the codomain recursion is the cap). -/
theorem yieldIn_le_yieldAll (Γ : List Ty) (a : Ty) : yieldIn Γ a ≤ yieldAll a := by
  induction a with
  | content => simp [yieldIn, yieldAll]
  | knower => simp [yieldIn, yieldAll]
  | knowledge => simp [yieldIn, yieldAll]
  | value => simp [yieldIn, yieldAll]
  | stream => simp [yieldIn, yieldAll]
  | trace => simp [yieldIn, yieldAll]
  | unit => simp [yieldIn, yieldAll]
  | later a iha => simp [yieldIn, yieldAll]
  | tensor a b iha ihb =>
      rw [yieldIn_tensor, yieldAll_tensor]
      omega
  | arrow a b iha ihb =>
      rw [yieldIn_arrow, yieldAll_arrow]
      by_cases h : FundableAt Γ a
      · rw [if_pos h]
        exact ihb
      · rw [if_neg h]
        omega

/-! ### The closed-only yield (w35) — the M-restricted counting chain

`yieldC` counts content through CLOSED-funded arrow-domains only. The
general frame-budget is FALSE for both measures (w34/w35's kernel
witnesses: position-funding is free in `FundableAt` but firing consumes
the position — the cost lands on the arg's piece at the app), but at
M-frames the closed-only chain HOLDS and is ≤ 1 — the compound sites'
counting engine. -/

noncomputable def yieldC : Ty → Nat
  | .content => 1
  | .tensor a b => yieldC a + yieldC b
  | .arrow a b => if ClosedFundable a then yieldC b else 0
  | _ => 0

noncomputable def frameYieldC (Γ : List Ty) : Nat := (Γ.map yieldC).sum

theorem yieldC_content : yieldC .content = 1 := rfl
theorem yieldC_tensor {a b : Ty} : yieldC (.tensor a b) = yieldC a + yieldC b := rfl
theorem yieldC_arrow {a b : Ty} :
    yieldC (.arrow a b) = (if ClosedFundable a then yieldC b else 0) := rfl

theorem yieldC_pos_needsC (x : Ty) (h : 1 ≤ yieldC x) : NeedsC x := by
  induction x with
  | content => trivial
  | knower => simp [yieldC] at h
  | knowledge => simp [yieldC] at h
  | value => simp [yieldC] at h
  | stream => simp [yieldC] at h
  | trace => simp [yieldC] at h
  | unit => simp [yieldC] at h
  | later a => simp [yieldC] at h
  | tensor a b iha ihb =>
      rw [yieldC_tensor] at h
      by_cases h1 : 1 ≤ yieldC a
      · exact Or.inl (iha h1)
      · exact Or.inr (ihb (by omega))
  | arrow a b iha ihb =>
      rw [yieldC_arrow] at h
      by_cases hcf : ClosedFundable a
      · rw [if_pos hcf] at h
        obtain ⟨hna, hka⟩ := closedFundable_not_needs hcf
        exact ⟨ihb h, hna, hka⟩
      · rw [if_neg hcf] at h
        omega

theorem yieldC_zero_of_notCSupply {x : Ty} (h : ¬ CSupply x) : yieldC x = 0 := by
  by_cases h1 : 1 ≤ yieldC x
  · exact absurd (Or.inl (yieldC_pos_needsC x h1)) h
  · omega

theorem yieldC_le_yieldAll (x : Ty) : yieldC x ≤ yieldAll x := by
  induction x with
  | content => rw [yieldC_content, yieldAll_content]; omega
  | knower => exact Nat.zero_le _
  | knowledge => exact Nat.zero_le _
  | value => exact Nat.zero_le _
  | stream => exact Nat.zero_le _
  | trace => exact Nat.zero_le _
  | unit => exact Nat.zero_le _
  | later a _iha => exact Nat.zero_le _
  | tensor a b iha ihb => rw [yieldC_tensor, yieldAll_tensor]; omega
  | arrow a b _iha ihb =>
      rw [yieldC_arrow, yieldAll_arrow]
      by_cases h : ClosedFundable a
      · rw [if_pos h]; exact ihb
      · rw [if_neg h]; omega

theorem frameYieldC_zero_of_allAdm {Γ : List Ty} (hA : AllAdm Γ) : frameYieldC Γ = 0 := by
  induction Γ with
  | nil => rfl
  | cons k Γ ih =>
      have hk : AdmPos k := hA 0 k List.get?_zero_cons'
      have hΓ : AllAdm Γ := fun i b hpos => hA (i + 1) b (by rw [List.get?_succ_cons']; exact hpos)
      show (List.map yieldC (k :: Γ)).sum = 0
      rw [List.map_cons, List.sum_cons, yieldC_zero_of_notCSupply hk.1, Nat.zero_add]
      exact ih hΓ

/-- THE CONFIRMED CHAIN: at a one-source M-frame the closed-only frame
measure is the source's own yield, hence ≤ 1. -/
theorem frameYieldC_of_M {ΓL ΓR : List Ty} {ΓS : Ty} (hL : AllAdm ΓL) (hR : AllAdm ΓR) :
    frameYieldC (ΓL ++ ΓS :: ΓR) = yieldC ΓS := by
  have h0 : (List.map yieldC ΓL).sum = 0 := frameYieldC_zero_of_allAdm hL
  have h1 : (List.map yieldC ΓR).sum = 0 := frameYieldC_zero_of_allAdm hR
  show (List.map yieldC (ΓL ++ ΓS :: ΓR)).sum = yieldC ΓS
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  rw [h0, h1]
  omega

theorem frameYieldC_M_le_one {ΓL ΓR : List Ty} {ΓS : Ty} (hL : AllAdm ΓL) (hR : AllAdm ΓR)
    (hy : yieldAll ΓS ≤ 1) : frameYieldC (ΓL ++ ΓS :: ΓR) ≤ 1 := by
  rw [frameYieldC_of_M hL hR]
  have hyc := yieldC_le_yieldAll ΓS
  omega

/-- Two `NeedsC` components at disjoint pieces of a one-source frame both
cprop-read the UNIQUE source index — contradiction (the tensor-compound
kill: a pair of content-needing sides cannot split one source). -/
theorem no_twoNeedsC_split_at_M {ΓL ΓR : List Ty} {ΓS : Ty} {a b : Ty} {l r : Term}
    {Δ₁ Δ₂ : List Ty}
    (hL : AllAdm ΓL) (hR : AllAdm ΓR) (hcs : CSupply ΓS) (hnK : ¬ NeedsK ΓS)
    (hnc : ¬ ContainsCxC ΓS) (hy : yieldAll ΓS ≤ 1)
    (hs : Δ₁ ++ Δ₂ = ΓL ++ ΓS :: ΓR)
    (hl : Typed Δ₁ l a) (hr : Typed Δ₂ r b) (hca : NeedsC a) (hcb : NeedsC b) : False := by
  obtain ⟨i, b', hpos, hcs'⟩ := cprop hl hca
  have hilt : i < Δ₁.length := List.get?_some_lt hpos
  have hpos' : (ΓL ++ ΓS :: ΓR)[i]? = some b' := by
    rw [← hs, List.get?_append_lt hilt]; exact hpos
  obtain ⟨hi, -⟩ := csupply_pos_eq_source hL hR hpos' hcs'
  obtain ⟨j, b'', hpos2, hcs''⟩ := cprop hr hcb
  have hpos2' : (ΓL ++ ΓS :: ΓR)[Δ₁.length + j]? = some b'' := by
    rw [← hs, List.get?_append_ge (Nat.le_add_right Δ₁.length j), Nat.add_sub_cancel_left]
    exact hpos2
  obtain ⟨hj, -⟩ := csupply_pos_eq_source hL hR hpos2' hcs''
  omega

/-- THE DEEP-TYPE ENGINE (w36): the deep produce type is content-needing
whenever both domains supply nothing — cprop kills any such value at a
NoCSupply frame with NO head dispatch. Fails exactly when the value sits
at a frame hosting the source (the cprop read pins to the source slot,
legal) — there the pair-counting needs the deep descent. -/
theorem deep_produce_needsC {W X : Ty} (hW : ¬ CSupply W) (hX : ¬ CSupply X) :
    NeedsC (Ty.arrow W (Ty.arrow X (Ty.tensor Ty.content Ty.content))) :=
  ⟨⟨Or.inl trivial, fun hc => hX (Or.inl hc), fun hk => hX (Or.inr hk)⟩,
   fun hc => hW (Or.inl hc), fun hk => hW (Or.inr hk)⟩

/-- Funding lifts across a NON-LINEAR cons (the weak rule's crossing). -/
theorem fundableAt_weakCons {Γ : List Ty} {k a : Ty} (hk : k.isLinear = false)    (h : FundableAt Γ a) : FundableAt (k :: Γ) a := by
  rcases h with ⟨t, ht⟩ | hcf
  · obtain ⟨ht⟩ := ht
    exact Or.inl ⟨Term.liftAt 0 t, ⟨Typed.weak hk ht⟩⟩
  · exact Or.inr hcf

/-- `yieldIn` is monotone across NON-LINEAR consing (the weak/contr arms'
frames shrink only by dropped non-linear heads). -/
theorem yieldIn_mono_weakCons {Γ : List Ty} {k a : Ty} (hk : k.isLinear = false) :
    yieldIn Γ a ≤ yieldIn (k :: Γ) a := by
  induction a with
  | content => simp [yieldIn]
  | knower => simp [yieldIn]
  | knowledge => simp [yieldIn]
  | value => simp [yieldIn]
  | stream => simp [yieldIn]
  | trace => simp [yieldIn]
  | unit => simp [yieldIn]
  | later a iha => simp [yieldIn]
  | tensor a b iha ihb =>
      rw [yieldIn_tensor, yieldIn_tensor]
      omega
  | arrow a b iha ihb =>
      rw [yieldIn_arrow, yieldIn_arrow]
      by_cases h : FundableAt Γ a
      · rw [if_pos h, if_pos (fundableAt_weakCons hk h)]
        exact ihb
      · rw [if_neg h]
        by_cases h' : FundableAt (k :: Γ) a
        · rw [if_pos h']
          omega
        · rw [if_neg h']
          omega

/-! ### The two-source provenance layer (w39/wI)

A `NeedsC` type always has universal yield ≥ 1, so the SOURCE's own
comps cannot both be content-needing under `yieldAll ΓS ≤ 1`. The
two-source body-frames therefore never come from a source read — their
provenance is a construction, and the var/pair heads die (the var head
by this lemma; the pair head by no_twoNeedsC_split_at_M). -/

theorem needsC_yieldAll_ge_one (a : Ty) (h : NeedsC a) : 1 ≤ yieldAll a := by
  induction a with
  | content => exact Nat.le_refl 1
  | knower => exact absurd h id
  | knowledge => exact absurd h id
  | value => exact absurd h id
  | stream => exact absurd h id
  | trace => exact absurd h id
  | unit => exact absurd h id
  | later a iha => exact absurd h id
  | tensor a b iha ihb =>
      rw [yieldAll_tensor]
      rcases h with h | h
      · have := iha h; omega
      · have := ihb h; omega
  | arrow a b iha ihb =>
      rw [yieldAll_arrow]
      exact ihb h.1

theorem two_needsC_yieldAll_ge_two (a b : Ty) (ha : NeedsC a) (hb : NeedsC b) :
    2 ≤ yieldAll (Ty.tensor a b) := by
  rw [yieldAll_tensor]
  have h1 := needsC_yieldAll_ge_one a ha
  have h2 := needsC_yieldAll_ge_one b hb
  omega

theorem source_comps_not_both_needsC {ΓS a b : Ty} (hy : yieldAll ΓS ≤ 1)
    (he : ΓS = Ty.tensor a b) (ha : NeedsC a) (hb : NeedsC b) : False := by
  subst he
  have := two_needsC_yieldAll_ge_two a b ha hb
  omega

/-! ### THE CARRIER-YIELD BRIDGE AND THE ¬CSupply-GRAIN PAIR KILL

The carrier layer's foundation lemmas (fp19 brief, tasks 1-2). Both relate
the position-discipline predicate to the counting grain:

* `containsCxC_yieldAll_ge_two` — a `C⊗C`-carrier always has universal
  yield ≥ 2, so in the SOURCE class (`yieldAll ΓS ≤ 1`) the source can
  never itself be or contain a carrier-comp: `¬ContainsCxC ΓS` is a
  THEOREM of the yield bound (it stays load-bearing only for `AdmPos`
  frame positions, whose `yieldAll` is unbounded).
* `no_twoNeedsC_split_ns` — the two-source pair kill at the `NoCSupply`
  grain. The CARRIER-EXTENDED frames (`X :: ΓL ++ ΓS :: ΓR` with `X` a
  carrier) are `NoCSupply` but NOT `AllAdm`; a carrier is `¬CSupply`, so
  it extends the ns-grain frame but never supplies a cprop demand, and
  the single-source index arithmetic survives it verbatim. -/

/-- THE BRIDGE (task 1): a carrier has universal yield ≥ 2. `ContainsCxC`
embeds at least one `content ⊗ content` under tensors and codomains;
`yieldAll` counts exactly those. Boundary: `ContainsCxC (C⊗C) = True`,
`yieldAll (C⊗C) = 2`. -/
theorem containsCxC_yieldAll_ge_two (τ : Ty) (h : ContainsCxC τ) : 2 ≤ yieldAll τ := by
  induction τ with
  | tensor a b iha ihb =>
      rw [yieldAll_tensor]
      by_cases ha : a = Ty.content
      · subst ha
        by_cases hb : b = Ty.content
        · subst hb
          have hT : ContainsCxC (Ty.tensor Ty.content Ty.content) = True := rfl
          rw [hT] at h
          simp [yieldAll]
        · have hEq : ContainsCxC (Ty.tensor Ty.content b) = (False ∨ ContainsCxC b) := by
            cases b
            · exact absurd rfl hb
            all_goals rfl
          rw [hEq] at h
          rcases h with h | h
          · exact h.elim
          · have := ihb h; omega
      · have hEq : ContainsCxC (Ty.tensor a b) = (ContainsCxC a ∨ ContainsCxC b) := by
          cases a
          · exact absurd rfl ha
          all_goals (cases b <;> rfl)
        rw [hEq] at h
        rcases h with h | h
        · have := iha h; omega
        · have := ihb h; omega
  | arrow a b iha ihb =>
      rw [yieldAll_arrow]
      have hEq : ContainsCxC (Ty.arrow a b) = ContainsCxC b := rfl
      rw [hEq] at h
      exact ihb h
  | content => exact absurd h id
  | knower => exact absurd h id
  | knowledge => exact absurd h id
  | value => exact absurd h id
  | stream => exact absurd h id
  | trace => exact absurd h id
  | unit => exact absurd h id
  | later a iha => exact absurd h id

/-- The source-class collapse (the brief's consequence): under
`yieldAll ΓS ≤ 1` the source can never be or contain a carrier-comp, so
the march's `¬ContainsCxC` conjuncts are DERIVABLE from the yield bound. -/
theorem not_containsCxC_of_yield_le_one {τ : Ty} (h : yieldAll τ ≤ 1) :
    ¬ ContainsCxC τ :=
  fun hc => absurd (containsCxC_yieldAll_ge_two τ hc) (by omega)

/-- The carrier-source boundary: a source that IS a tensor with a carrier
comp already has yield ≥ 2 — the `var`-head case of a carrier-source read
dies on `yieldAll ΓS ≤ 1` alone. -/
theorem carrier_comp_source_dead {ΓS a b : Ty} (hy : yieldAll ΓS ≤ 1)
    (he : ΓS = Ty.tensor a b) (hc : ContainsCxC a) : False := by
  subst he
  rw [yieldAll_tensor] at hy
  have := containsCxC_yieldAll_ge_two a hc
  omega

/-- THE ¬CSupply-GRAIN PAIR KILL (task 2): the twin of
`no_twoNeedsC_split_at_M` with `NoCSupply` pieces. The proof is the AllAdm
proof verbatim with `csupply_pos_eq_source_ns` replacing
`csupply_pos_eq_source`; the source-class hypotheses are carried for
config fidelity (the counting never uses them — only the pieces' grain
matters). This is the engine the CARRIER-EXTENDED frames need: they are
`NoCSupply` (`nocsupply_cons` of a carrier and an AllAdm piece) but never
`AllAdm`. -/
theorem no_twoNeedsC_split_ns {ΓL ΓR : List Ty} {ΓS : Ty} {a b : Ty}
    {l r : Term} {Δ₁ Δ₂ : List Ty}
    (hL : NoCSupply ΓL) (hR : NoCSupply ΓR) (_hcs : CSupply ΓS)
    (_hnK : ¬ NeedsK ΓS) (_hnc : ¬ ContainsCxC ΓS) (_hy : yieldAll ΓS ≤ 1)
    (hs : Δ₁ ++ Δ₂ = ΓL ++ ΓS :: ΓR)
    (hl : Typed Δ₁ l a) (hr : Typed Δ₂ r b) (hca : NeedsC a) (hcb : NeedsC b) : False := by
  obtain ⟨i, b', hpos, hcs'⟩ := cprop hl hca
  have hilt : i < Δ₁.length := List.get?_some_lt hpos
  have hpos' : (ΓL ++ ΓS :: ΓR)[i]? = some b' := by
    rw [← hs, List.get?_append_lt hilt]; exact hpos
  obtain ⟨hi, -⟩ := csupply_pos_eq_source_ns hL hR hpos' hcs'
  obtain ⟨j, b'', hpos2, hcs''⟩ := cprop hr hcb
  have hpos2' : (ΓL ++ ΓS :: ΓR)[Δ₁.length + j]? = some b'' := by
    rw [← hs, List.get?_append_ge (Nat.le_add_right Δ₁.length j), Nat.add_sub_cancel_left]
    exact hpos2
  obtain ⟨hj, -⟩ := csupply_pos_eq_source_ns hL hR hpos2' hcs''
  omega

/-- The AllAdm-grain twin is an INSTANCE of the ns-grain one
(`allAdm_noCSupply`): the carrier-extended generalization strictly
contains the original engine — the pair kill now works at carrier frames. -/
theorem no_twoNeedsC_split_at_M_of_ns {ΓL ΓR : List Ty} {ΓS : Ty} {a b : Ty}
    {l r : Term} {Δ₁ Δ₂ : List Ty}
    (hL : AllAdm ΓL) (hR : AllAdm ΓR) (hcs : CSupply ΓS)
    (hnK : ¬ NeedsK ΓS) (hnc : ¬ ContainsCxC ΓS) (hy : yieldAll ΓS ≤ 1)
    (hs : Δ₁ ++ Δ₂ = ΓL ++ ΓS :: ΓR)
    (hl : Typed Δ₁ l a) (hr : Typed Δ₂ r b) (hca : NeedsC a) (hcb : NeedsC b) : False :=
  no_twoNeedsC_split_ns (allAdm_noCSupply hL) (allAdm_noCSupply hR)
    hcs hnK hnc hy hs hl hr hca hcb

/-- The boundary check the brief names: the embedded `C⊗C` is a carrier
with yield exactly 2 (so `yieldAll ΓS ≤ 1` really does exclude it). -/
theorem cxC_boundary :
    ContainsCxC (Ty.tensor Ty.content Ty.content)
      ∧ yieldAll (Ty.tensor Ty.content Ty.content) = 2 :=
  ⟨containsCxC_cxC, rfl⟩

/-- THE ROOT INSTANCE IS INHABITED — the layer's non-vacuity check (the
record's recurring failure mode: an uninstantiable residual layer). At the
singleton frame `[content]` every `(M)`/`(PF)`/`(PT)`/`(P)` hypothesis
holds, and `¬ContainsCxC content` is DERIVED from `yieldAll ≤ 1` (task 1's
collapse) rather than assumed — so the yield bound alone already fixes the
source class, and the twelfths' carrier-source refuters cannot ride in. -/
theorem root_source_class_inhabited :
    AllAdm [] ∧ CSupply Ty.content ∧ ¬ NeedsK Ty.content
      ∧ ¬ ContainsCxC Ty.content ∧ yieldAll Ty.content ≤ 1 :=
  ⟨allAdm_nil, Or.inl trivial, fun hk => hk,
   not_containsCxC_of_yield_le_one (by rw [yieldAll_content]; omega),
   by rw [yieldAll_content]; omega⟩

end CarrierYieldEngines
end Dcare
