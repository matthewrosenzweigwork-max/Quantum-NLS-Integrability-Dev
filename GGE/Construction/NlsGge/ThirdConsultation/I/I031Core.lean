import Mathlib
import NlsGge.ThirdConsultation.I.FiniteGapFlow
import NlsGge.Birkhoff.S04FiniteGapInvariance38

                                                                                                                       
                                                                                                                        
                                                                                                                            
                                                                                                             
                                                                                                      
                                                                                                                 
                                                                                                     
                                                                                                                     
                                                                         
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I
namespace I031Aux

theorem i031_of (BB : BirkhoffTop38) (Ω : ℤ → (ℤ → ℝ) → ℝ) (hΩ : ∀ n, Measurable (Ω n))
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) (Λ : Finset ℤ)
    (hPhi : ∀ (u : PhysicalL2) (n : ℤ), BB.Φ u n = physicalBirkhoff u n)
    (hF : ∀ w : Λ → ℂ, BB.finiteGapField38 Λ w = finiteGapField Λ w)
    (hrot : ∀ (w : Λ → ℂ) (t : ℝ), NlsGge.NLS38.nlsFlowL2 t (BB.finiteGapField38 Λ w) =
      BB.finiteGapField38 Λ (NlsGge.NLS38.twist (kappaΛ38 Ω Λ t) w))
    (hdens : ∀ (t : ℝ) (w : Λ → ℂ),
      BB.densΛ38 c.val Λ (NlsGge.NLS38.twist (kappaΛ38 Ω Λ t) w) = BB.densΛ38 c.val Λ w)
    (hnuInv : ∀ t : ℝ, Measure.map (NlsGge.NLS38.nlsFlowL2 t) (BB.nu38 c.val Λ) = BB.nu38 c.val Λ)
    (hnuHat : BB.nuHat38 c.val Λ = finiteGapCoordinateLaw (weight c.val) Λ)
    (hnu : BB.nu38 c.val Λ = finiteGapLaw (weight c.val) Λ)
    (hmeasρ : Measurable (fun w : Λ → ℂ =>
      ENNReal.ofReal (BB.densΛ38 c.val Λ w / BB.ZcalΛ38 c.val Λ)))
    (hact : ∀ (u : PhysicalL2) (n : ℤ), actualGapActionAllE02_38 u n = ‖physicalBirkhoff u n‖ ^ 2) :
    ∃ ω : (Λ → ℝ) → Λ → ℝ, ∀ t : ℝ,
      (∀ (w : Λ → ℂ) (n : Λ),
        finiteGapFlow Λ t w n =
          Complex.exp (-Complex.I * ((t * ω (fun k => ‖w k‖ ^ 2) n : ℝ) : ℂ)) * w n) ∧
      (∀ w : Λ → ℂ,
        NlsGge.NLS38.nlsFlowL2 t (finiteGapField Λ w) =
          finiteGapField Λ (finiteGapFlow Λ t w) ∧
        (∀ n : ℤ, actualGapActionAllE02_38
          (NlsGge.NLS38.nlsFlowL2 t (finiteGapField Λ w)) n =
            actualGapActionAllE02_38 (finiteGapField Λ w) n) ∧
        spectralEnergy (weight c.val) (NlsGge.NLS38.nlsFlowL2 t (finiteGapField Λ w)) =
          spectralEnergy (weight c.val) (finiteGapField Λ w)) ∧
      MeasurePreserving (finiteGapFlow Λ t) (finiteComplexVolume Λ) (finiteComplexVolume Λ) ∧
      (finiteGapCoordinateLaw (weight c.val) Λ).map (finiteGapFlow Λ t) =
        finiteGapCoordinateLaw (weight c.val) Λ ∧
      (finiteGapLaw (weight c.val) Λ).map (NlsGge.NLS38.nlsFlowL2 t) =
        finiteGapLaw (weight c.val) Λ := by
  have hB : ∀ (v : Λ → ℂ) (i : Λ), physicalBirkhoff (finiteGapField Λ v) i = v i := by
    intro v i
    rw [← hF, ← hPhi, BB.Φ_finiteGapField38, extZero38_apply_of_mem _ i.2]
  have hflow : ∀ t : ℝ, finiteGapFlow Λ t = NlsGge.NLS38.twist (kappaΛ38 Ω Λ t) := by
    intro t
    funext w i
    show physicalBirkhoff (NlsGge.NLS38.nlsFlowL2 t (finiteGapField Λ w)) i = _
    rw [← hF, hrot, hF, hB]
  have hω : ∀ w : Λ → ℂ, (fun k : ℤ => if h : k ∈ Λ then ‖w ⟨k, h⟩‖ ^ 2 else 0) =
      fun k => ‖extZero38 Λ w k‖ ^ 2 := by
    intro w
    funext k
    by_cases h : k ∈ Λ <;> simp [extZero38, h]
  have hen : ∀ u : PhysicalL2, spectralEnergy (weight c.val) u = energyW38 c.val u := fun u => rfl
  refine ⟨fun (a : Λ → ℝ) (i : Λ) => Ω i.1 (fun k => if h : k ∈ Λ then a ⟨k, h⟩ else 0),
    fun t => ⟨?_, fun w => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · intro w i
    rw [hflow]
    simp only [NlsGge.NLS38.twist, kappaΛ38]
    rw [hω w]
    congr 2
    push_cast
    ring
  · rw [hflow, ← hF, hrot, hF]
  · intro n
    rw [hact, hact, ← hF, hrot, ← hPhi, ← hPhi, BB.Φ_finiteGapField38, BB.Φ_finiteGapField38]
    exact congrArg (· ^ 2) (norm_extZero38_rotate Λ w (kappaΛ38 Ω Λ t w) n)
  · have h := hdens t w
    unfold BirkhoffTop38.densΛ38 at h
    have h2 := Real.exp_injective h
    rw [hen, hen, ← hF, hrot]
    linarith
  · rw [hflow]
    exact NlsGge.NLS38.measurePreserving_twist (kappaΛ38 Ω Λ t) (measurable_kappaΛ38 Ω hΩ Λ t)
      (kappaΛ38_rotate Ω Λ t)
  · rw [hflow, ← hnuHat]
    unfold BirkhoffTop38.nuHat38
    exact NlsGge.NLS38.map_withDensity_twist (kappaΛ38 Ω Λ t) (measurable_kappaΛ38 Ω hΩ Λ t)
      (kappaΛ38_rotate Ω Λ t) _ hmeasρ (fun w => by simp only [hdens])
  · rw [← hnu]
    exact hnuInv t

end I031Aux
end NlsGge.ThirdConsultation.I
