import Mathlib
import NlsGge.ThirdConsultation.KSPSRiccatiHost

                                                                   
                                                             
                                                                                           
                                                                                               
                                                                                                             
                                                                                       
                                                                                                         
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.ThirdConsultation.KSPSRiccati
open NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
open MeasureTheory

def riccatiLeft {N : ℕ} (φ : SobolevC N) : ℕ → PhysicalL2 :=
  NlsGge.ThirdConsultation.KSPSRiccati.left φ

def integralRiccatiLeft {N : ℕ} (φ : SobolevC N) (k : ℕ) : ℂ :=
  ∫ x in (0:ℝ)..1, (toPotPair φ).1 x * riccatiLeft φ k x

end
end NlsGge.ThirdConsultation.KSPS

open Filter MeasureTheory
open scoped Topology BigOperators

namespace NlsGge.ThirdConsultation.KSPSRiccati
noncomputable section

def phasePolynomial
    {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (K : ℕ) (z : ℂ) : ℂ :=
  Complex.I * ∑ k ∈ Finset.Icc 1 K,
    ((2 * Complex.I) ^ k)⁻¹ *
      NlsGge.ThirdConsultation.KSPS.integralRiccatiLeft φ k * z ^ k

def inversePhaseIterate
    {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) :
    ℕ → ℂ → ℂ
  | 0 => fun _ : ℂ => 0
  | j + 1 => fun z : ℂ =>
      -phasePolynomial φ (j + 1)
        (z / ((Real.pi : ℂ) + z * inversePhaseIterate φ j z))

def spectralCoefficient
    {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (k : ℕ) : ℂ :=
  iteratedDeriv k (inversePhaseIterate φ k) 0 /
    (Nat.factorial k : ℂ)

def momentumIntegral
    {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    NlsGge.GK38.coverRep38
      (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
    NlsGge.GK38.coverRep38
      (NlsGge.GKDefinitionDesign.weakDerivative
        (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2) x

def inversePhaseTaylor
    {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (K : ℕ) (c : ℕ → ℂ) : Prop :=
  ∃ ζ : ℂ → ℂ,
    AnalyticAt ℂ ζ 0 ∧ ζ 0 = 0 ∧
    (∀ᶠ z : ℂ in 𝓝 0,
      (Real.pi : ℂ) + z * ζ z ≠ 0 ∧
      ζ z + phasePolynomial φ K
        (z / ((Real.pi : ℂ) + z * ζ z)) = 0) ∧
    ∀ k : ℕ, k ≤ K →
      c k = iteratedDeriv k ζ 0 / (Nat.factorial k : ℂ)

end
end NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section
open NlsGge.ThirdConsultation.KSPSRiccati
open NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
open MeasureTheory

def massCoefficient {N : ℕ} (φ : SobolevC N) : ℂ :=
  -(2*Real.pi:ℂ)⁻¹ * integralRiccatiLeft φ 1

def momentumCoefficient {N : ℕ} (φ : SobolevC N) : ℂ :=
  Complex.I*(4*Real.pi^2:ℂ)⁻¹ *
    NlsGge.ThirdConsultation.KSPSRiccati.momentumIntegral φ

def ConsistentRiccatiSpectralCoefficients
    {N : ℕ} (φ : SobolevC N) (c : ℕ → ℂ) : Prop :=
  ∀ K, K ≤ N+1 →
    NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseTaylor φ K c

end
end NlsGge.ThirdConsultation.KSPS
