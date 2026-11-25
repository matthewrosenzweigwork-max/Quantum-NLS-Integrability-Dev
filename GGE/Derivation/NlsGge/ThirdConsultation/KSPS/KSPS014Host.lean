import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Host
import NlsGge.ThirdConsultation.KSPS.KSPS003Host

/- KSPS-014 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS014Host.lean.
   Bodies VERBATIM from Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md Cluster 1 = followup12 DEFINITIONS/KSPS.lean.md
   "Round-14 replacement bodies"): KSPSWKB.coefficientTraceZero, coefficientTrace, alpha, beta, initialColumns,
   wkbColumn, wkbColumns, explicitWKBMonodromy; KSPSVolterra.endpointCoefficientBound, threshold; KSPS.WKBThreshold.
   grep of NlsGge/ and Work/ found none of these names defined. Header opens = Pro's block.
   LEXICAL REPAIR: Lean-3 `local attribute [instance] Classical.propDecidable` -> `attribute [local instance] ...`
   (as in the KSPS-012 host). The other round-14 bodies (endpointDiagonal*, integralRiccatiRight: KSPS012Host;
   antitrace.., normingLog.., endpointQuadratic.., halfNode/primitive, AntiTraceDirichletWKB..) are NOT installed here. -/

set_option autoImplicit false
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
attribute [local instance] Classical.propDecidable

-- Reconstruct the continuous H¹ trace, rather than evaluate an arbitrary
-- L² representative at a point. Used as an H¹ trace only after that regularity
-- has been proved for 1 ≤ k ≤ N.
def coefficientTraceZero {N : ℕ} (φ : SobolevC N) (b : Bool)
    (k : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k) t -
      ((1 - t : ℝ) : ℂ) *
        coverRep38 (weakDerivative
          (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k)) t

def coefficientTrace {N : ℕ} (φ : SobolevC N) (b : Bool)
    (k : ℕ) (x : ℝ) : ℂ :=
  coefficientTraceZero φ b k +
    ∫ t in (0 : ℝ)..x,
      coverRep38 (weakDerivative
        (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k)) t

def alpha {N : ℕ} (φ : SobolevC N) (lam : ℂ) (x : ℝ) : ℂ :=
  -Complex.I * ∑ k ∈ Finset.Icc 1 N,
    ((2 * Complex.I * lam) ^ k)⁻¹ * coefficientTrace φ false k x

def beta {N : ℕ} (φ : SobolevC N) (lam : ℂ) (x : ℝ) : ℂ :=
  -Complex.I * ∑ k ∈ Finset.Icc 1 N,
    ((2 * Complex.I * lam) ^ k)⁻¹ * coefficientTrace φ true k x

def initialColumns {N : ℕ} (φ : SobolevC N) (lam : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, beta φ lam 0; alpha φ lam 0, 1]

def wkbColumn {N : ℕ} (φ : SobolevC N) (b : Bool)
    (lam : {z : ℂ // z ≠ 0}) (x : ℝ) : Fin 2 → ℂ :=
  (if b then
    (Complex.exp (Complex.I * lam.1 * (x : ℂ)) *
      NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ true lam.1 x) •
        ![beta φ lam.1 x, 1]
   else
    (Complex.exp (-(Complex.I * lam.1 * (x : ℂ))) *
      NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ false lam.1 x) •
        ![1, alpha φ lam.1 x]) +
  ((2 * Complex.I * lam.1) ^ N)⁻¹ •
    sourceRemainderVector φ b lam x

def wkbColumns {N : ℕ} (φ : SobolevC N)
    (lam : {z : ℂ // z ≠ 0}) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if j = 0 then wkbColumn φ false lam x i
    else wkbColumn φ true lam x i

-- The spectral parameter has its genuine nonzero domain. No value is
-- invented at lam=0 for the WKB inverse/columns.
def explicitWKBMonodromy (N : ℕ) (φ : SobolevC N)
    (lam : {z : ℂ // z ≠ 0}) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Matrix.det (initialColumns φ lam.1))⁻¹ •
    (wkbColumns φ lam 1 *
      NlsGge.ThirdConsultation.KSPSVolterra.adjugate2
        (initialColumns φ lam.1))

end
end NlsGge.ThirdConsultation.KSPSWKB

namespace NlsGge.ThirdConsultation.KSPSVolterra
noncomputable section

-- Numerical construction from finite Riccati endpoint coefficients only.
-- It does not select a number by assuming a monodromy theorem.
def endpointCoefficientBound (N : ℕ) (B : ℝ) (k : ℕ) : ℝ :=
  sSup ({0} ∪ {r : ℝ | ∃ (φ : KSPS.SobolevC N) (b : Bool),
    KSPS.sobolevNorm N φ ≤ max B 0 ∧
    r = ‖KSPSWKB.coefficientTraceZero φ b k‖})

def threshold (N : ℕ) (B : ℝ) : ℝ :=
  1 + ∑ k ∈ Finset.Icc 1 N, endpointCoefficientBound N B k

end
end NlsGge.ThirdConsultation.KSPSVolterra

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def WKBThreshold (N : ℕ) (B : ℝ) (lam : ℂ) : Prop :=
  0 < ‖lam‖ ∧ KSPSVolterra.threshold N B ≤ ‖lam‖

end
end NlsGge.ThirdConsultation.KSPS
