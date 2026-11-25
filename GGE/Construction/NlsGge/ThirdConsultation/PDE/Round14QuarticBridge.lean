import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Field
import NlsGge.ThirdConsultation.G6.Energy031C
import NlsGge.NLS38.PhysicalBridge38a

                                                                                                                        
                                                                                                                       
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

namespace NlsGge.ThirdConsultation.PDE

theorem integral_spatial_eq_interval (g : PhysicalCircle → ℝ) :
    ∫ x, g x ∂spatialMeasure = ∫ θ in (0 : ℝ)..1, g (θ : PhysicalCircle) := by
  have h := AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))
  have h2 := AddCircle.intervalIntegral_preimage (1 : ℝ) 0 g
  rw [h] at h2
  simpa [spatialMeasure] using h2.symm

theorem quart_neg_reflect (c : ℤ → ℂ) :
    quart (fun n : ℤ => -c (-n)) = quart c := by
  have h : ∀ n : ℤ, conv (fun m : ℤ => -c (-m)) (fun m : ℤ => -c (-m)) n = conv c c (-n) := by
    intro n
    unfold conv
    rw [← (Equiv.neg ℤ).tsum_eq (fun a : ℤ => c a * c (-n - a))]
    refine tsum_congr fun a => ?_
    simp only [Equiv.neg_apply, neg_mul_neg]
    congr 2
    ring
  unfold quart
  simp_rw [h]
  exact (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ‖conv c c n‖ ^ 2)

theorem quartic_circle_eq (q : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    ∫ x : PhysicalCircle, ‖physicalSobolevEmbed 1 q x‖ ^ 4 ∂spatialMeasure =
      quart (fourierSeq38 (physicalSobolevEmbed 1 q)) := by
  set c := fourierSeq38 (physicalSobolevEmbed 1 q) with hc
  have hcmem : c ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
    have : c = carrierCoe38 ((1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) q) :=
      funext (physicalSobolevEmbed_fourier 1 q)
    rw [this]; exact carrierCoe38_mem _ _
  have hL1c : IsL1 c := (isL1_of_hn_one c hcmem).1
  set f := iotaCLM q with hf
  have hfL : ContinuousMap.toLp 2 spatialMeasure ℂ f = physicalSobolevEmbed 1 q := by
    rw [hf, iotaCLM_apply, physicalSobolevContinuous38_toLp]
  -- coefficients of f
  set d : ℤ → ℂ := fun n => fourierCoeff (⇑f) n with hd
  have hdc : ∀ n : ℤ, d n = -c (-n) := by
    intro n
    have h1 : c (-n) = reflectedFourier (physicalSobolevEmbed 1 q) (-n) :=
      reflectedFourierL2_apply _ _
    have h2 : reflectedFourier (physicalSobolevEmbed 1 q) (-n) =
        -physicalFourier (physicalSobolevEmbed 1 q) (- -n) := rfl
    rw [h1, h2, neg_neg, neg_neg]
    unfold physicalFourier
    rw [← hfL, hd]
    exact (fourierCoeff_toLp f n).symm
  have hdfun : d = fun n : ℤ => -c (-n) := funext hdc
  have hL1d : IsL1 d := by
    rw [hdfun]
    unfold IsL1
    simp only [norm_neg]
    exact ((Equiv.neg ℤ).summable_iff).2 hL1c
  have hsum : Summable (fourierCoeff (⇑f)) := by
    have : Summable (fun n : ℤ => ‖d n‖) := hL1d
    exact Summable.of_norm this
  have hpt : ∀ θ : ℝ, f (θ : PhysicalCircle) = serU d θ := by
    intro θ
    have h := has_pointwise_sum_fourier_series_of_summable hsum (θ : PhysicalCircle)
    rw [serU]
    refine (h.tsum_eq).symm.trans ?_
    refine tsum_congr fun n => ?_
    rw [smul_eq_mul, fourier_coe_apply]
    simp [hd]
  have hae : ∫ x : PhysicalCircle, ‖physicalSobolevEmbed 1 q x‖ ^ 4 ∂spatialMeasure =
      ∫ x : PhysicalCircle, ‖f x‖ ^ 4 ∂spatialMeasure := energy_quartic_eq q
  rw [hae, integral_spatial_eq_interval]
  have : (fun θ : ℝ => ‖f (θ : PhysicalCircle)‖ ^ 4) = fun θ => ‖serU d θ‖ ^ 4 := by
    funext θ; rw [hpt]
  rw [this, integral_norm_pow_four_serU hL1d, ← quart_neg_reflect c, hdfun]
  rfl

end NlsGge.ThirdConsultation.PDE
end
