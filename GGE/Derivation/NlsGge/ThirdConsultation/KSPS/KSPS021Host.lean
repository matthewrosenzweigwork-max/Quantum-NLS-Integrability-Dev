import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS016Host
import NlsGge.ThirdConsultation.KSPS.KSPS019Host

/- KSPS-021 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS021Host.lean.
   Bodies VERBATIM from Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md Cluster 1 = followup12 DEFINITIONS/KSPS.lean.md
   "Round-14 replacement bodies"): KSPSWKB.normingLog, KSPSWKB.normingError, KSPS.DirichletBoundaryWeightedL2.
   grep of NlsGge/ and Work/isolated_20261027 (2026-11-01) found none of these names in these namespaces
   (NlsGge.Atomic.G1.G1088 has an unrelated `normingError` over PotPair in another namespace; Pro: "No L2-vector
   GKDefinitionDesign.normingError is reused or renamed"). Header opens = Pro's block.
   LEXICAL REPAIR (as in KSPS012Host/KSPS014Host/KSPS016Host): Lean-3 `local attribute [instance] Classical.propDecidable`
   -> `attribute [local instance] Classical.propDecidable`. Uses KSPS016Host (antitrace), KSPS015Host (discriminant,
   WeightedL2Error) and KSPS019Host (mu). -/

set_option autoImplicit false
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
attribute [local instance] Classical.propDecidable

-- Principal log gives the source's high-frequency branch near 1. This
-- definition makes no assertion that it equals the globally continued κ_n
-- at the finitely many low modes.
def normingLog (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℂ :=
  2 * Complex.log ((-1 : ℂ) ^ n *
    (discriminant φ (mu φ n) + antitrace φ (mu φ n)) / 2)

def normingError (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℂ :=
  normingLog N φ n - Complex.I *
    (physicalFourier (toPotPair φ).1 (-n) -
     physicalFourier (toPotPair φ).2 n)

end
end NlsGge.ThirdConsultation.KSPSWKB

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def DirichletBoundaryWeightedL2 (N : ℕ) (φ : SobolevC N) : Prop :=
  WeightedL2Error ((N + 1 : ℕ) : ℝ)
    (fun n : ℤ => discriminant φ (mu φ n) - 2 * (-1 : ℂ) ^ n) ∧
  WeightedL2Error ((N + 1 : ℕ) : ℝ) (KSPSWKB.normingError N φ)

end
end NlsGge.ThirdConsultation.KSPS
