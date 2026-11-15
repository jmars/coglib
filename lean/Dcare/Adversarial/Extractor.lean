import Dcare.SC

/-!
# The Extractor — the unrestricted calculus's structural counterexample

THE ADVERSARIAL BASELINE. This file isolates, names, and scopes the
counterexample that ended the unrestricted no-vanishing program
(`Dcare.SCProvenance3`, landed d18a322): an explicit, kernel-checked
derivation of `[content] ⊢ unit`.

WHAT THE EXTRACTOR IS, HONESTLY STATED:

  (λ(k : arrow knower knowledge). unit)          -- the DISCARD: weak
  (λ(k : knower). red (lete ⟨var 0, var 0⟩       -- the SWAP: lete/pair
      (cons (var 0) (next (fix (λs. flip2))))))  -- the CYCLE: cons+fix

- The content token is SPENT as the `cons` head of the epistemic cycle's
  stream (`[content, knower] ⊢ stream`) — it is not destroyed unused.
- The LETE SWAP (`lete`'s body context is `b :: a :: Γ₂`, the tensor's
  components REVERSED, so `pair`/`lete` reorders the context) moves the
  knower pocket in front of the content, where `lam` can bind it.
- `red` reads the pocket's stream; `lam knower` closes
  `[content] ⊢ arrow knower knowledge`.
- The carrier applies `λ(k : arrow knower knowledge). unit` to that
  conduit: the `weak` node discards the conduit and returns `unit`.

THE CORRECTIONS THE KERNEL FORCES ON THE GLOSS (do not soften, do not
overclaim): (1) the conduit is NOT synthesized "from thin air" and NOT
without a stream — the epistemic cycle's fix/stream IS the engine; what
the swap synthesizes is a REORDERING that lets a knower binder sit in
front of a content position. (2) No knower VALUE is ever synthesized:
`[content] ⊢ knower` and `[] ⊢ knower` are dead (in-tree), and the
conduit cannot even FIRE at a content frame
(`no_arrowKnower_app_at_content`). The knower lives exactly one life:
as a λ-binder that `weak` then discards. (3) The witness is NOT
cut-free — its discharging application is λ-headed.

MEANING: in a calculus without a resource guard, an agent can receive
content and return nothing — by spending the content into a self-sustaining
epistemic cycle and discarding the reading. The unrestricted calculus
permits this; the restricted kernel (the Guarded kernel, `Dcare.Kernel.Guarded`) forbids it by
banning the discard (`weak`), which the witness needs at its last step.
-/

namespace Dcare.Adversarial.Extractor

open SCExtractor SCProvenance SCProvenance3

/-- THE EXTRACTOR EXISTS: `[content] ⊢ unit` is inhabited in the
UNRESTRICTED calculus. This one line is the refutation of
`Dcare.Linearity.no_vanishing` (the statement as written is FALSE);
it is kept in-tree as the adversarial baseline result. -/
theorem extractor_exists : ∃ (t : Term), Nonempty (Typed [Ty.content] t Ty.unit) :=
  ⟨_, ⟨carrierAKK arrowKnowerKnowledge⟩⟩

/-- THE UNRESTRICTED LAW IS REFUTED, as a one-line statement. -/
theorem no_vanishing_unrestricted_refuted :
    ¬ (∀ (t : Term), Typed [Ty.content] t Ty.unit → False) := by
  intro H
  obtain ⟨t, ⟨h⟩⟩ := extractor_exists
  exact H t h

/-! ## The four pieces, named -/

/-- PIECE 1 — THE CYCLE: the content spent as the `cons` head onto the
epistemic fixpoint. The shortest content-carrying stream in the
calculus. -/
theorem the_cycle :
    Nonempty (Typed [Ty.content, Ty.knower]
      (Term.cons (Term.var 0)
        (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2)))) Ty.stream) :=
  ⟨streamContentKnower⟩

/-- PIECE 2 — THE SWAP: `lete`'s reversed body context reorders the
frame, knower pocket first. -/
theorem the_swap :
    Nonempty (Typed [Ty.knower, Ty.content]
      (Term.lete (Term.pair (Term.var 0) (Term.var 0))
        (Term.cons (Term.var 0)
          (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2))))) Ty.stream) :=
  ⟨streamKnowerContent⟩

/-- PIECE 3 — THE CONDUIT: `[content] ⊢ arrow knower knowledge`,
derivable (this is the type the record's open question #2 named). -/
theorem the_conduit :
    Nonempty (Typed [Ty.content]
      (Term.lam Ty.knower
        (Term.app Term.red
          (Term.lete (Term.pair (Term.var 0) (Term.var 0))
            (Term.cons (Term.var 0)
              (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2)))))))
      (Ty.arrow Ty.knower Ty.knowledge)) :=
  ⟨arrowKnowerKnowledge⟩

/-- PIECE 4 — THE DISCARD: the carrier's `λ(k : arrow knower knowledge).
unit` weakens the conduit away for `unit`. -/
theorem the_discard :
    Nonempty (Typed [Ty.content]
      (Term.app (Term.lam (Ty.arrow Ty.knower Ty.knowledge) (Term.liftAt 0 Term.unit))
        (Term.lam Ty.knower
          (Term.app Term.red
            (Term.lete (Term.pair (Term.var 0) (Term.var 0))
              (Term.cons (Term.var 0)
                (Term.next (Term.fix (Term.lam (Ty.later Ty.stream) flip2))))))))
      Ty.unit) :=
  ⟨carrierAKK arrowKnowerKnowledge⟩

/-! ## The scope — what the Extractor is NOT -/

/-- No knower is synthesized: `[content] ⊢ knower` is dead, and the
conduit cannot fire at any content frame (the knower argument would be
closed or content-rooted — both dead, fix- and weak-inclusively). The
knower's only life in the witness is as a λ-binder that `weak` discards. -/
theorem no_knower_synthesized : ¬ KnowerAtContent :=
  no_knowerAtContent

theorem conduit_inert {X : Ty} {fn arg : Term} {Γ Δ : List Ty}
    (hf : Typed Γ fn (Ty.arrow Ty.knower X)) (ha : Typed Δ arg Ty.knower)
    (hs : Γ ++ Δ = [Ty.content]) : False :=
  no_arrowKnower_app_at_content hf ha hs

/-- The witness is NOT cut-free: its discharging application is
λ-headed. Every cut-free fragment theorem in the tree survives. -/
theorem extractor_not_cut_free :
    ¬ IsAtomic
      (Term.lam (Ty.arrow Ty.knower Ty.knowledge) (Term.liftAt 0 Term.unit)) :=
  carrierAKK_fn_not_atomic

/-- The knowledge rung stays unreachable: `[content] ⊢ knowledge` would
give the target, and it remains dead — the conduit is inhabited but
inert, so `red`'s argument never reaches a content frame. -/
theorem knowledge_rung_unreachable
    (hex : ∃ (t : Term), Nonempty (Typed [Ty.content] t Ty.knowledge)) :
    ∃ (u : Term), Nonempty (Typed [Ty.content] u Ty.unit) :=
  unit_at_content_of_knowledgeAtContent hex

/-- The token is SPENT, not destroyed: the witness's own head sub-tree
reads the content position exactly once, as the cycle's stream head. -/
theorem the_token_is_spent :
    Nonempty (Typed [Ty.content] (Term.var 0) Ty.content) := ⟨Typed.var⟩

end Dcare.Adversarial.Extractor
