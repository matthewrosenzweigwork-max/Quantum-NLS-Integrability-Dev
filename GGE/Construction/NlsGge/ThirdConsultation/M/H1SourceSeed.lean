import Mathlib
import NlsGge.ThirdConsultation.M.M033Host
import NlsGge.ThirdConsultation.M.M031Energy
import NlsGge.ThirdConsultation.M.Round5b
import NlsGge.ThirdConsultation.M.M053Host
import NlsGge.ThirdConsultation.KSPS.KSPS032Support
import NlsGge.ThirdConsultation.Sobolev.Round5

                                                                                                                          
                                                                                                                       
                                                                                                                  
                                                                                                                        
                                                                                                               
                                                                                                                   
                                                                                                                      
                                                                                                                        
                                                       
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Birkhoff
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.MH1Seed

/-- `r_p = |û_p|²` in reflected form. -/
abbrev rcoef (v : PhysicalL2) (p : ℤ) : ℝ := ‖reflectedFourierL2 v p‖ ^ 2

/-- The source weight squared at the doubled-cover index `-2p`. -/
abbrev srcW (p : ℤ) : ℝ := (1 + |2 * Real.pi * (p : ℝ)|) ^ 2

theorem cover_weighted_tsum (v : PhysicalL2) :
    ∑' k : ℤ, M.sourceH1Weight k ^ 2 *
        ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 v) k‖ ^ 2 =
      ∑' p : ℤ, srcW p * rcoef v p := by
  set F : ℤ → ℝ := fun k => M.sourceH1Weight k ^ 2 *
        ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 v) k‖ ^ 2 with hF
  have hg : Function.Injective (fun p : ℤ => -2 * p) := by
    intro a b h
    simp only at h
    omega
  have hsupp : Function.support F ⊆ Set.range (fun p : ℤ => -2 * p) := by
    intro k hk
    by_contra hkr
    apply hk
    have hodd : k % 2 ≠ 0 := by
      intro h0
      exact hkr ⟨-(k / 2), by simp only; omega⟩
    simp only [hF]
    rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd v k hodd, norm_zero]
    ring
  rw [← hg.tsum_eq hsupp]
  refine tsum_congr (fun p => ?_)
  simp only [hF]
  have heven : (-2 * p) % 2 = 0 := by omega
  have hdiv : (-2 * p) / 2 = -p := by omega
  rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_even_index v _ heven, hdiv]
  have hn : ‖physicalFourier (v : PhysicalCircle → ℂ) (-p)‖ = ‖reflectedFourierL2 v p‖ := by
    rw [reflectedFourierL2_apply]
    unfold reflectedFourier
    rw [norm_neg]
  rw [hn]
  have hw : M.sourceH1Weight (-2 * p) = 1 + |2 * Real.pi * (p : ℝ)| := by
    unfold M.sourceH1Weight
    push_cast
    rw [show Real.pi * (-2 * (p : ℝ)) = -(2 * Real.pi * (p : ℝ)) by ring, abs_neg]
  rw [hw]

theorem star_weighted_tsum (v : PhysicalL2) :
    ∑' p : ℤ, srcW p * rcoef (star v) p = ∑' p : ℤ, srcW p * rcoef v p := by
  have he : (fun p : ℤ => srcW p * rcoef (star v) p) =
      (fun p : ℤ => srcW p * rcoef v p) ∘ (Equiv.neg ℤ) := by
    funext p
    simp only [Function.comp_apply, Equiv.neg_apply, rcoef, srcW,
      NlsGge.ThirdConsultation.KSPS032S.norm_reflected_star, Int.cast_neg, mul_neg, abs_neg]
  rw [he]
  exact (Equiv.neg ℤ).tsum_eq (fun p : ℤ => srcW p * rcoef v p)

/-- Exported Fourier formula for the source (Molnar pair) H1 norm. -/
theorem H1Norm_sq_eq (u : M.SobolevR 1) :
    MTwoMode.H1Norm u ^ 2 = 2 * ∑' p : ℤ, srcW p * rcoef (M.physicalOfSobolev u) p := by
  have hwe : NlsGge.GKDefinitionDesign.physicalSobolevEmbed 1 u = M.physicalOfSobolev u :=
    NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M 1 u
  have hs1 := M.sobolevEmbed_one_summable u
  rw [hwe] at hs1
  obtain ⟨hs2, -⟩ := NlsGge.ThirdConsultation.KSPS032S.star_summable (M.physicalOfSobolev u) hs1
  have sum1 := M.sourceH1_component_summable (M.physicalOfSobolev u) hs1
  have sum2 := M.sourceH1_component_summable (star (M.physicalOfSobolev u)) hs2
  have hsum : Summable (fun k : ℤ => M.sourceH1Weight k ^ 2 *
      (‖MTwoMode.potentialCoefficientPair (realSlice (M.physicalOfSobolev u)) true k‖ ^ 2 +
        ‖MTwoMode.potentialCoefficientPair (realSlice (M.physicalOfSobolev u)) false k‖ ^ 2)) := by
    refine (sum1.add sum2).congr (fun k => ?_)
    simp only [MTwoMode.potentialCoefficientPair, realSlice_apply, ite_true, Bool.false_eq_true,
      ite_false]
    ring
  have hE : (MTwoMode.potentialCoefficientEnergy M.sourceH1Weight
        (realSlice (M.physicalOfSobolev u))).toReal =
      ∑' k : ℤ, M.sourceH1Weight k ^ 2 *
          ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 (M.physicalOfSobolev u)) k‖ ^ 2 +
        ∑' k : ℤ, M.sourceH1Weight k ^ 2 *
          ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2
            (star (M.physicalOfSobolev u))) k‖ ^ 2 := by
    unfold MTwoMode.potentialCoefficientEnergy
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum,
      ENNReal.toReal_ofReal (tsum_nonneg (fun k => by positivity)), ← sum1.tsum_add sum2]
    refine tsum_congr (fun k => ?_)
    simp only [MTwoMode.potentialCoefficientPair, realSlice_apply, ite_true, Bool.false_eq_true,
      ite_false]
    ring
  show (Real.sqrt (MTwoMode.potentialCoefficientEnergy M.sourceH1Weight
      (realSlice (M.physicalOfSobolev u))).toReal) ^ 2 = _
  rw [Real.sq_sqrt ENNReal.toReal_nonneg, hE, cover_weighted_tsum, cover_weighted_tsum,
    star_weighted_tsum]
  ring

/-- Exported Fourier formula for the top derivative at order one. -/
theorem topDerivativeNorm_sq_eq (u : M.SobolevR 1) :
    M.topDerivativeNorm 1 u ^ 2 =
      ∑' p : ℤ, (2 * Real.pi * (p : ℝ)) ^ 2 * rcoef (M.physicalOfSobolev u) p := by
  have h0 : M.topDerivativeNorm 1 u =
      ‖NlsGge.Atomic.Common.physicalSobolevDerivative38 1 u‖ := rfl
  rw [h0, norm_sq_eq_tsum_fourierSeq38]
  refine tsum_congr (fun p => ?_)
  rw [NlsGge.GKDefinitionDesign.physicalSobolevDerivative38_reflected, pow_one, norm_mul, mul_pow]
  have hc : ‖carrierCoe38 ((1 : ℕ) : ℝ)
      (NlsGge.Atomic.Common.physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u) p‖ =
      ‖reflectedFourierL2 (M.physicalOfSobolev u) p‖ := by
    rw [← NlsGge.GKDefinitionDesign.physicalSobolevEmbed_fourier,
      NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M]
    rfl
  rw [hc]
  congr 1
  rw [show (-2 * (Real.pi : ℂ) * Complex.I * (p : ℂ)) =
      ((-2 * Real.pi * (p : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem massCharge_eq_tsum (u : M.SobolevR 1) :
    M.massCharge (M.physicalOfSobolev u) = ∑' p : ℤ, rcoef (M.physicalOfSobolev u) p := by
  unfold M.massCharge
  rw [norm_sq_eq_tsum_fourierSeq38]
  rfl

theorem weight_ineq (p : ℤ) :
    2 / 3 * (1 + |2 * Real.pi * (p : ℝ)|) ^ 2 ≤ (2 * Real.pi * (p : ℝ)) ^ 2 + 1 := by
  by_cases hp : p = 0
  · subst hp; norm_num
  · have h1 : (1 : ℝ) ≤ |(p : ℝ)| := by
      have := Int.one_le_abs hp
      exact_mod_cast this
    have ht : 6 ≤ |2 * Real.pi * (p : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_gt_three]
    rw [← sq_abs (2 * Real.pi * (p : ℝ))]
    nlinarith [ht]

theorem summable_rcoef_weights (u : M.SobolevR 1) :
    Summable (fun p : ℤ => rcoef (M.physicalOfSobolev u) p) ∧
    Summable (fun p : ℤ => (2 * Real.pi * (p : ℝ)) ^ 2 * rcoef (M.physicalOfSobolev u) p) ∧
    Summable (fun p : ℤ => srcW p * rcoef (M.physicalOfSobolev u) p) := by
  have hwe : NlsGge.GKDefinitionDesign.physicalSobolevEmbed 1 u = M.physicalOfSobolev u :=
    NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M 1 u
  have hs1 := M.sobolevEmbed_one_summable u
  rw [hwe] at hs1
  have hr0 : ∀ p : ℤ, 0 ≤ rcoef (M.physicalOfSobolev u) p := fun p => sq_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le hr0 (fun p => ?_) hs1
    have := hr0 p
    nlinarith [sq_nonneg (p : ℝ)]
  · refine Summable.of_nonneg_of_le (fun p => mul_nonneg (sq_nonneg _) (hr0 p)) (fun p => ?_)
      (hs1.mul_left (4 * Real.pi ^ 2))
    have := hr0 p
    have hp2 : (2 * Real.pi * (p : ℝ)) ^ 2 ≤ 4 * Real.pi ^ 2 * (1 + (p : ℝ) ^ 2) := by
      nlinarith [sq_nonneg Real.pi]
    calc (2 * Real.pi * (p : ℝ)) ^ 2 * rcoef (M.physicalOfSobolev u) p
        ≤ (4 * Real.pi ^ 2 * (1 + (p : ℝ) ^ 2)) * rcoef (M.physicalOfSobolev u) p :=
          mul_le_mul_of_nonneg_right hp2 this
      _ = 4 * Real.pi ^ 2 * ((1 + (p : ℝ) ^ 2) * rcoef (M.physicalOfSobolev u) p) := by ring
  · refine Summable.of_nonneg_of_le (fun p => mul_nonneg (sq_nonneg _) (hr0 p)) (fun p => ?_)
      (hs1.mul_left (2 * (1 + 4 * Real.pi ^ 2)))
    have := hr0 p
    have hw : srcW p ≤ 2 * (1 + 4 * Real.pi ^ 2) * (1 + (p : ℝ) ^ 2) := by
      have e : srcW p = M.sourceH1Weight (-2 * p) ^ 2 := by
        unfold srcW M.sourceH1Weight
        push_cast
        rw [show Real.pi * (-2 * (p : ℝ)) = -(2 * Real.pi * (p : ℝ)) by ring, abs_neg]
      rw [e]
      exact M.sourceH1Weight_sq_le p
    calc srcW p * rcoef (M.physicalOfSobolev u) p
        ≤ (2 * (1 + 4 * Real.pi ^ 2) * (1 + (p : ℝ) ^ 2)) * rcoef (M.physicalOfSobolev u) p :=
          mul_le_mul_of_nonneg_right hw this
      _ = 2 * (1 + 4 * Real.pi ^ 2) * ((1 + (p : ℝ) ^ 2) * rcoef (M.physicalOfSobolev u) p) := by ring

end NlsGge.ThirdConsultation.MH1Seed

namespace NlsGge.ThirdConsultation.M

open NlsGge.ThirdConsultation.MH1Seed in
theorem source_H1_norm_energy_bound (u : SobolevR 1) :
    (1 / 3 : ℝ) * MTwoMode.H1Norm u ^ 2 ≤
      topDerivativeNorm 1 u ^ 2 + massCharge (physicalOfSobolev u) := by
  obtain ⟨hs0, hs1, hs⟩ := summable_rcoef_weights u
  rw [H1Norm_sq_eq, topDerivativeNorm_sq_eq, massCharge_eq_tsum, ← hs1.tsum_add hs0]
  calc (1 / 3 : ℝ) * (2 * ∑' p : ℤ, srcW p * rcoef (physicalOfSobolev u) p)
      = ∑' p : ℤ, 2 / 3 * (srcW p * rcoef (physicalOfSobolev u) p) := by
        rw [tsum_mul_left]; ring
    _ ≤ ∑' p : ℤ, ((2 * Real.pi * (p : ℝ)) ^ 2 * rcoef (physicalOfSobolev u) p +
          rcoef (physicalOfSobolev u) p) := by
        refine Summable.tsum_le_tsum (fun p => ?_) (hs.mul_left _) (hs1.add hs0)
        have hr := sq_nonneg ‖reflectedFourierL2 (physicalOfSobolev u) p‖
        have hw := weight_ineq p
        calc 2 / 3 * (srcW p * rcoef (physicalOfSobolev u) p)
            = (2 / 3 * (1 + |2 * Real.pi * (p : ℝ)|) ^ 2) * rcoef (physicalOfSobolev u) p := by
              simp only [srcW]; ring
          _ ≤ ((2 * Real.pi * (p : ℝ)) ^ 2 + 1) * rcoef (physicalOfSobolev u) p :=
              mul_le_mul_of_nonneg_right hw hr
          _ = _ := by ring

end NlsGge.ThirdConsultation.M
