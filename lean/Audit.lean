import Dcare.Chase
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
import Dcare.Subst
import Dcare.Cut

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
#print axioms Dcare.sinks_extract'
#print axioms Dcare.Prem_size
#print axioms Dcare.Prem_clean
#print axioms Dcare.no_vanishing_parkfree
#print axioms Dcare.Sub_size
#print axioms Dcare.wSpendFrom_nonpos
#print axioms Dcare.trace_origin
#print axioms Dcare.origin_lemma
#print axioms Dcare.sinks_extract'
#print axioms Dcare.wSpendFrom_nonpos_all
#print axioms Dcare.lam_no_producer
#print axioms Dcare.read_locate
#print axioms Dcare.Sub_trans
#print axioms Dcare.Introduces
#print axioms Dcare.pos_introduced
#print axioms Dcare.Path_clean
#print axioms Dcare.parent_locate
#print axioms Dcare.substG_tsize
#print axioms Dcare.linear_redex_shrink
#print axioms Dcare.substP_tsize
#print axioms Dcare.linear_redex_shrinkP
#print axioms Dcare.append_cancel_left
#print axioms Dcare.append_cancel_right
#print axioms Dcare.sFlowEq
#print axioms Dcare.sMint_nonpos
#print axioms Dcare.stream_origin
#print axioms Dcare.nonlinear_snet
#print axioms Dcare.binder_sexact
#print axioms Dcare.mergeAt_unmergeAt
#print axioms Dcare.unmergeAt_tsize
#print axioms Dcare.term_transport
#print axioms Dcare.linear_cut
#print axioms Dcare.linear_beta_splice
#print axioms Dcare.rebuild_along
#print axioms Dcare.reduce_at
#print axioms Dcare.spendNet_singleton
#print axioms Dcare.no_vanishing_fixfree_of_chase
#print axioms Dcare.Path_append
#print axioms Dcare.sub_path
#print axioms Dcare.get?_zero_of_singleton
#print axioms Dcare.prem_position
#print axioms Dcare.liftAt0_ne_var0
#print axioms Dcare.var_canonical
#print axioms Dcare.chase_step
#print axioms Dcare.root_content_nonpos
#print axioms Dcare.introducer_of_positive
#print axioms Dcare.config_fn_positive_arg
#print axioms Dcare.config_arg_lam_killer
#print axioms Dcare.killer_step
#print axioms Dcare.config_lete_elim
#print axioms Dcare.uses_sub_ge_or_binder
#print axioms Dcare.uses_zero_of_ge_length
#print axioms Dcare.Sub_irrefl
#print axioms Dcare.uses_sub_le
#print axioms Dcare.sub_of_prem
#print axioms Dcare.root_unit_prem
#print axioms Dcare.ConsumingPrem
#print axioms Dcare.RidePrem
#print axioms Dcare.RootReach
#print axioms Dcare.value_climb
#print axioms Dcare.no_root_reach
#print axioms Dcare.Slot
#print axioms Dcare.SlotsOf
#print axioms Dcare.path_slots
#print axioms Dcare.slots_of_append
#print axioms Dcare.SubLen
#print axioms Dcare.sub_len_exists
#print axioms Dcare.sub_len_trans
#print axioms Dcare.path_append_assoc
#print axioms Dcare.sub_path_trans
