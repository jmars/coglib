-- Root of the `Dcare` library: the derivation-of-care formalization.
--
-- STATEMENT SPIKE (S1): definitions and theorem STATEMENTS only. Every
-- `sorry` is a placeholder for a proof scheduled by the plan (S2–S9);
-- none is load-bearing. `scripts/lean-check.sh` audits axioms and sorries.
import Dcare.ListAux
import Dcare.Count
import Dcare.Flow
import Dcare.SelfApp
import Dcare.Path
import Dcare.Syntax
import Dcare.Typing
import Dcare.Linearity
import Dcare.Model
import Dcare.Semantics
import Dcare.Stream
import Dcare.Policy
import Dcare.T1
import Dcare.Parametricity
import Dcare.T3
import Dcare.Diagnostic
import Dcare.T2
import Dcare.Constructive
import Dcare.Adversaries
