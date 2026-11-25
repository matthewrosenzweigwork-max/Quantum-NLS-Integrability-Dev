import Mathlib
import NlsGge.Weights.UniformSymbolBound38
import NlsGge.Birkhoff.H03Diagonal38b
import NlsGge.Birkhoff.F05Identity38j
import NlsGge.Measure.FourierGaussian
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.SourceWeighted

                                                                                                                   
                                                                                                                             
                                                                                                                           
                                                                                                                                                  
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Measure NlsGge.Weights NlsGge.SpectralFoundations NlsGge.Sobolev38

namespace NlsGge.ThirdConsultation.I

theorem i020_norm_eq (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖physicalSobolevL2 1 u hu‖ = ‖physFS38 1 u‖ := by
  have hu' : SobolevSquareSummable ((1 : ℕ) : ℝ) (physicalFourier u) := by simpa using hu
  have h := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) (toCarrier38 _ (physFS38 1 u))
  have hc : ∀ n : ℤ, carrierCoe38 ((1 : ℕ) : ℝ) (toCarrier38 _ (physFS38 1 u)) n =
      physicalFourier u n := fun n => coeffSeq_physFS38 1 u hu' n
  have h2 := h.tsum_eq
  have h3 := physicalSobolevL2_norm_sq 1 u hu
  have hsq : ‖physicalSobolevL2 1 u hu‖ ^ 2 = ‖physFS38 1 u‖ ^ 2 := by
    rw [h3]
    have : ‖toCarrier38 ((1 : ℕ) : ℝ) (physFS38 1 u)‖ = ‖physFS38 1 u‖ := rfl
    rw [← this, ← h2]
    refine tsum_congr fun n => ?_
    rw [hc n]
    simp [sobolevModeWeight]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

theorem i020 (lower upper : ℝ) (hlower : 0 < lower) (hle : lower ≤ upper)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : BoundedCoefficients lower upper,
      ∀ u : PhysicalL2, SobolevSquareSummable 1 (physicalFourier u) →
        ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        ∀ «λ» ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
          |weight c.val (2 * «λ») - fullWeightRate c.val n| ≤
            C * fullWeightRate c.val n * japaneseBracket n ^ (-3 / 2 : ℝ) ∧
          ∀ m : ℕ, |partialWeight c.val m (2 * «λ») - hierRate38 c.val m n| ≤
            C * hierRate38 c.val m n * japaneseBracket n ^ (-3 / 2 : ℝ) := by
  obtain ⟨CB, hCB, hsym⟩ := uniformSymbolGap38 lower upper hlower hle (max 1 B) (le_max_left _ _)
  refine ⟨CB, hCB.le, fun c u hu hnorm n l hl => ?_⟩
  have hn : ‖physicalSobolevL2 1 u hu‖ ≤ max 1 B := by
    rw [i020_norm_eq u hu]; exact hnorm.trans (le_max_right _ _)
  obtain ⟨hpart, hfull⟩ := hsym c.val (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2)
    u hu hn n l hl
  have e : (-3 / 2 : ℝ) = -(3 / 2) := by norm_num
  rw [e]
  exact ⟨hfull, hpart⟩

end NlsGge.ThirdConsultation.I
