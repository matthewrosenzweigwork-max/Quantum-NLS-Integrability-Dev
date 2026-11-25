import Mathlib
import NlsGge.Atomic.KSN.KSN002
import NlsGge.Atomic.KSN.KSN003
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.Atomic.G4.G4036Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

                                                                                                                  
                                                                                                                  
                                                                                                                                 
                                                                                                  
                                                                                                                      
                                           
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.KSN
noncomputable section
open NlsGge.GKDefinitionDesign

def eta (n : ℤ) (a : ℤ) (φ : PotPair) : ℂ :=
  Complex.exp (-(a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))

def gapEndpoint (n : ℤ) (φ : PotPair) (e : Bool) : ℂ :=
  if e then lamPlus φ n else lamMinus φ n

/-- A path on the actual quadratic surface, with the terminal sheet fixed.
The endpoint roots may vanish; interior roots must not vanish. -/
def CorrectionPath (n : ℤ) (φ : PotPair) (e : Bool)
    (c r : ℝ → ℂ) : Prop :=
  NlsGge.Atomic.KSN003Design.PiecewiseC1On c 0 1 ∧
  ContinuousOn r (Icc 0 1) ∧
  c 0 = gapEndpoint n φ e ∧ c 1 = muSeq φ n ∧
  r 0 = 0 ∧ r 1 = terminalRoot n φ ∧
  (∀ t ∈ Icc 0 1, c t ∈ Metric.ball (discC φ n) (discR φ n) ∧
    (r t)^2 = (lamPlus φ n - c t) * (lamMinus φ n - c t)) ∧
  ∀ t ∈ Ioo 0 1, r t ≠ 0

def correctionIntegrand (n : ℤ) (φ : PotPair) (c r : ℝ → ℂ) (t : ℝ) : ℂ :=
  deriv c t * (normalizedZeta n φ (c t) - 1) / r t

/-- Improper integral at both endpoints; all truncated integrals are real
Bochner interval integrals. No nonexistent improper integral is totalized. -/
def HasCorrectionIntegral (n : ℤ) (φ : PotPair) (c r : ℝ → ℂ) (I : ℂ) : Prop :=
  (∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    IntervalIntegrable (correctionIntegrand n φ c r) volume δ (1 - δ)) ∧
  Tendsto (fun δ : ℝ => ∫ t in δ..(1 - δ), correctionIntegrand n φ c r t)
    (𝓝[>] 0) (𝓝 I)

end
end NlsGge.ThirdConsultation.KSN
