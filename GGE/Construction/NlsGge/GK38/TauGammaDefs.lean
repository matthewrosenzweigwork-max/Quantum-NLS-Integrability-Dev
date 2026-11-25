import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.ProductRepr

/-! Weighted spectral moments on the actual isolating circles (GK I.12). -/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory SummationFilter
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def AdmissibleSelectors38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ) : Prop :=
  ∀ φ : PotPair, φ ∈ gkW → IsolatingFamily38 φ (C φ) (R φ)

def momentIntegrand38 (φ : PotPair) (k : ℕ) (z : ℂ) : ℂ :=
  z ^ k * deriv (perChar φ) z / perChar φ z

def fixedMoment38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (n : ℤ) (k : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * circleIntegral (momentIntegrand38 φ k) (C n) (R n)

def tauN38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ) (φ : PotPair) (n : ℤ) : ℂ :=
  (2 * (2 * (Real.pi : ℂ) * Complex.I))⁻¹ *
    circleIntegral (momentIntegrand38 φ 1) (C φ n) (R φ n)

def q2N38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ) (φ : PotPair) (n : ℤ) : ℂ :=
  fixedMoment38 φ (C φ) (R φ) n 2

def gamma2N38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ) (φ : PotPair) (n : ℤ) : ℂ :=
  2 * q2N38 C R φ n - 4 * (tauN38 C R φ n) ^ 2

def gapMagnitude38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ) (φ : PotPair) (n : ℤ) : ℝ :=
  Real.sqrt ‖gamma2N38 C R φ n‖

def excludedPairedFactors38 (φ : PotPair) (n : ℤ) (z : ℂ) (m : ℤ) : ℂ :=
  if m = n then 1 else pairedFactors38 φ z m

def exteriorFactor38 (φ : PotPair) (n : ℤ) (z : ℂ) : ℂ :=
  (πn n : ℂ)⁻¹ ^ 2 * ∏'[symmetricIcc ℤ] m : ℤ, excludedPairedFactors38 φ n z m

def criticalDenominator38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (φ : PotPair) (n : ℤ) : ℂ :=
  2 * exteriorFactor38 φ n (lamDot φ n) + (lamDot φ n - tauN38 C R φ n) *
    deriv (exteriorFactor38 φ n) (lamDot φ n)

def criticalCoefficient38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (φ : PotPair) (n : ℤ) : ℂ :=
  deriv (exteriorFactor38 φ n) (lamDot φ n) / (4 * criticalDenominator38 C R φ n)

def tauN (φ : PotPair) (n : ℤ) : ℂ := tauN38 discC discR φ n

def q2 (φ : PotPair) (n : ℤ) : ℂ := q2N38 discC discR φ n

def gamma2 (φ : PotPair) (n : ℤ) : ℂ := gamma2N38 discC discR φ n

end
end NlsGge.GK38
