import Dcare.T1
import Dcare.T3
import Dcare.T2
import Dcare.Diagnostic
import Dcare.Stream
import Dcare.Policy
import Dcare.Linearity
import Dcare.Flow
import Dcare.Adversaries
import Dcare.Constructive
import Dcare.SelfApp
import Dcare.Path

/-!
# Axiom audit (run by scripts/lean-check.sh, NOT part of the library)

Rules:
- public theorems may depend only on the standard three axioms
  (propext, Classical.choice, Quot.sound) — sorryAx only for the three
  statements on the scheduled allowlist;
- `T2_postulate` must NEVER appear in a public theorem's axiom list:
  "the paper does not depend on the collaboration landing" as a check.
-/

#print axioms Dcare.T1_semantic
#print axioms Dcare.T3_main
#print axioms Dcare.Diagnostic_main
#print axioms Dcare.diagnostic_premise
#print axioms Dcare.needsK_mentions
#print axioms Dcare.protective_needsK
#print axioms Dcare.no_closed_protective_guard
#print axioms Dcare.no_trace_to_stream
#print axioms Dcare.knower_sustains_stream
#print axioms Dcare.always_continue_infinite
#print axioms Dcare.run_not_infinite_is_finite
#print axioms Dcare.no_contraction_content
#print axioms Dcare.no_weakening_content
#print axioms Dcare.knower_contractible
#print axioms Dcare.adversary_spin_diverges
#print axioms Dcare.adversary_blind_transfer
#print axioms Dcare.constructive_main
#print axioms Dcare.T2_main
#print axioms Dcare.no_closed_content
#print axioms Dcare.no_closed_knower
#print axioms Dcare.sound
#print axioms Dcare.single_linear_use
#print axioms Dcare.no_vanishing
#print axioms Dcare.archival_witness
#print axioms Dcare.past_cannot_teach
#print axioms Dcare.past_cannot_value
#print axioms Dcare.conservation
#print axioms Dcare.soundL
#print axioms Dcare.no_knower_at_knowerfree
#print axioms Dcare.selfapp_price
#print axioms Dcare.nonlinear_leaves
#print axioms Dcare.leaves_bound
#print axioms Dcare.kprop
#print axioms Dcare.netprop_core
#print axioms Dcare.no_contraction_core
#print axioms Dcare.nonlinear_net
#print axioms Dcare.netprop_nofix
#print axioms Dcare.no_contraction_nogen
#print axioms Dcare.netEq
#print axioms Dcare.no_vanishing_eq
#print axioms Dcare.no_contraction_eq
#print axioms Dcare.flowEq
#print axioms Dcare.fix_unfold_closed
#print axioms Dcare.fix_unfold_at_knower
#print axioms Dcare.looped_only_spins
#print axioms Dcare.spin_pays_forever_buys_nothing
#print axioms Dcare.extractor_never_consults
#print axioms Dcare.extractor_step_integrates
#print axioms Dcare.no_stream_without_supply
#print axioms Dcare.no_closed_later_stream
#print axioms Dcare.cprop
#print axioms Dcare.sprop
#print axioms Dcare.tprop
#print axioms Dcare.extract_produce
#print axioms Dcare.no_trace_at_clean
#print axioms Dcare.no_d2_producer
#print axioms Dcare.kill_clean
#print axioms Dcare.no_vanishing_clean
#print axioms Dcare.mintCount_zero_at_unit_root
#print axioms Dcare.extract_produce'
#print axioms Dcare.no_trace_at_oblig
#print axioms Dcare.deepConsume_notDomOK
#print axioms Dcare.no_deep_consumer
#print axioms Dcare.fixMint_eq_zero
#print axioms Dcare.oblctx_noSSupply
#print axioms Dcare.sinks_extract
#print axioms Dcare.no_vanishing_parkfree
