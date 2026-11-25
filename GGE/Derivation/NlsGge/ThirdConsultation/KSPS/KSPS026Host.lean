import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS014Host
import NlsGge.ThirdConsultation.KSPS.KSPS015Host
import NlsGge.ThirdConsultation.KSPS.KSPS020Host

/- KSPS-026 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS026Host.lean.
   Bodies VERBATIM from Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md Cluster 1 = followup12
   DEFINITIONS/KSPS.lean.md "Round-14 replacement bodies"): KSPSWKB.scaledEndpointCorrection, endpointQuadraticABC,
   endpointQuadraticAt, endpointQuadraticFormula, endpointEntryError; KSPS.EndpointQuadraticWKB.
   grep of NlsGge/ and all Work/isolated_20261027 author folders (2026-11-01) found none of these names declared.
   Header opens = Pro's block. Uses KSPS014Host (alpha, beta), KSPS015Host (WeightedL2Error, wkbPhase; under review,
   kit proof development), KSPS020Host (periodicPlus/Minus), KSPS011Host (sourceRemainderVector), KSPSInversePhaseHost
   (integralRiccatiLeft).
   LEXICAL REPAIR (as in KSPS012Host/KSPS014Host/KSPS016Host): Lean-3 `local attribute [instance] Classical.propDecidable`
   -> `attribute [local instance] Classical.propDecidable`. -/

set_option autoImplicit false
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
attribute [local instance] Classical.propDecidable

-- Corrections after multiplying the column difference by (-1)^n.
def scaledEndpointCorrection (N : ℕ) (φ : SobolevC N) (n : ℤ)
    (lam : {z : ℂ // z ≠ 0}) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (-1 : ℂ) ^ n * ((2 * Complex.I * lam.1) ^ N)⁻¹ *
    (if j = 0 then sourceRemainderVector φ false lam 1 i
     else sourceRemainderVector φ true lam 1 i)

def endpointQuadraticABC (N : ℕ) (φ : SobolevC N) (n : ℤ)
    (lam : {z : ℂ // z ≠ 0}) : Fin 3 → ℂ :=
  let r := scaledEndpointCorrection N φ n lam
  let al := alpha φ lam.1 0
  let be := beta φ lam.1 0
  ![-1 + al * be + r 0 0 - be * r 1 0,
    1 + (1 - r 0 0) * (1 - r 1 1) - al * be -
      (al - r 1 0) * (be - r 0 1),
    -1 + al * be + r 1 1 - al * r 0 1]

def endpointQuadraticAt (N : ℕ) (φ : SobolevC N) (n : ℤ)
    (lam : {z : ℂ // z ≠ 0}) (h : ℂ) : Prop :=
  let q := endpointQuadraticABC N φ n lam
  let eta := (-1 : ℂ) ^ n * Complex.exp (Complex.I * wkbPhase φ lam.1)
  q 0 ≠ 0 ∧ q 0 * eta ^ 2 + q 1 * eta + q 2 = 0 ∧
    (q 1) ^ 2 - 4 * q 0 * q 2 =
      -4 * physicalFourier (toPotPair φ).1 (-n) *
        physicalFourier (toPotPair φ).2 n + h

def endpointQuadraticFormula (N : ℕ) (φ : SobolevC N) (n : ℤ)
    (hplus hminus : ℤ → ℂ) : Prop :=
  ∃ (hp : periodicPlus φ n ≠ 0) (hm : periodicMinus φ n ≠ 0),
    endpointQuadraticAt N φ n ⟨periodicPlus φ n, hp⟩ (hplus n) ∧
    endpointQuadraticAt N φ n ⟨periodicMinus φ n, hm⟩ (hminus n)

def endpointEntryError (N : ℕ) (φ : SobolevC N) (upper : Bool)
    (i j : Fin 2) (n : ℤ) : ℂ :=
  let lam := if upper then periodicPlus φ n else periodicMinus φ n
  if hz : lam = 0 then 0 else
    let lead : Matrix (Fin 2) (Fin 2) ℂ :=
      !![integralRiccatiLeft φ (N + 1) /
            (2 * Complex.I * lam) ^ (N + 1),
         Complex.I * physicalFourier (toPotPair φ).1 (-n);
         -Complex.I * physicalFourier (toPotPair φ).2 n,
         -integralRiccatiLeft φ (N + 1) /
            (2 * Complex.I * lam) ^ (N + 1)]
    scaledEndpointCorrection N φ n ⟨lam, hz⟩ i j - lead i j

end
end NlsGge.ThirdConsultation.KSPSWKB

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

-- Radicand error is ℓ¹ at order 2N+1. The entry errors are separately ℓ²
-- at order N+1, for all four entries and both endpoints.
def EndpointQuadraticWKB (N : ℕ) (φ : SobolevC N) : Prop :=
  (∀ (upper : Bool) (i j : Fin 2),
    WeightedL2Error ((N + 1 : ℕ) : ℝ)
      (KSPSWKB.endpointEntryError N φ upper i j)) ∧
  ∃ hplus hminus : ℤ → ℂ,
    Summable (fun n : ℤ => indexWeight n ^ (2 * N + 1) * ‖hplus n‖) ∧
    Summable (fun n : ℤ => indexWeight n ^ (2 * N + 1) * ‖hminus n‖) ∧
    ∀ᶠ n : ℤ in Filter.cocompact ℤ,
      KSPSWKB.endpointQuadraticFormula N φ n hplus hminus

end
end NlsGge.ThirdConsultation.KSPS
