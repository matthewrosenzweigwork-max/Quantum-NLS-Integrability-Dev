import Mathlib
import NlsGge.Atomic.R.R018
import NlsGge.ThirdConsultation.R.CylCore06

                                                                                                           
                                                                                                    
                                                                                                   
                                                                    
                                                                                                            
                                                                                                                
                                                                                       
set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- Square of an `L²` norm as the integral of the squared norm (totalized; `MemLp` supplied). -/
theorem r019_eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ ^ 2 = ENNReal.ofReal (∫ a, ‖f a‖ ^ 2 ∂μ) := by
  have hI : 0 ≤ ∫ a, ‖f a‖ ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hI ((2 : ℝ)⁻¹))]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
  norm_num

/-- Pointwise: the HS norm is the square of `hsDeriv`. -/
theorem hsDeriv_sq
    (d : ℕ) (F : GaussianFiniteCarrier d → GaussianFiniteCarrier d)
    (x : GaussianFiniteCarrier d) :
    (hsDeriv d F x) ^ 2 =
      NlsGge.Ramer.hsNormSq (fderiv ℝ F x) :=
  Real.sq_sqrt (NlsGge.Ramer.hsNormSq_nonneg _)

/-- Continuity of `hsDeriv` for a `C²` field. -/
theorem r019_continuous_hsDeriv
    {d : ℕ} {F : GaussianFiniteCarrier d → GaussianFiniteCarrier d} (hF2 : ContDiff ℝ 2 F) :
    Continuous (hsDeriv d F) :=
  Real.continuous_sqrt.comp (NlsGge.Ramer.continuous_hsNormSq_fderiv hF2)

/-- Integrability of the HS norm of the derivative under the exponential growth bound. -/
theorem r019_integrable_hsNormSq
    {d : ℕ} {F : GaussianFiniteCarrier d → GaussianFiniteCarrier d} {C : ℝ}
    (hF2 : ContDiff ℝ 2 F) (hC : 0 ≤ C)
    (hDg : ∀ x, ‖fderiv ℝ F x‖ ≤ C * Real.exp (C * ‖x‖)) :
    Integrable (fun x => NlsGge.Ramer.hsNormSq (fderiv ℝ F x))
      (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) := by
  refine integrable_of_norm_le_pow_mul_exp_finiteStd
    (NlsGge.Ramer.continuous_hsNormSq_fderiv hF2).aestronglyMeasurable
    (((Module.finrank ℝ (GaussianFiniteCarrier d) : ℝ)) ^ 2 * C ^ 2) (2 * C) 0 (fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (NlsGge.Ramer.hsNormSq_nonneg _), pow_zero, one_mul]
  calc NlsGge.Ramer.hsNormSq (fderiv ℝ F x)
      ≤ (Module.finrank ℝ (GaussianFiniteCarrier d) : ℝ) ^ 2 * ‖fderiv ℝ F x‖ ^ 2 :=
        NlsGge.Ramer.hsNormSq_le_finrank_sq_mul _
    _ ≤ (Module.finrank ℝ (GaussianFiniteCarrier d) : ℝ) ^ 2 * (C * Real.exp (C * ‖x‖)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hDg x) 2) (sq_nonneg _)
    _ = (Module.finrank ℝ (GaussianFiniteCarrier d) : ℝ) ^ 2 * C ^ 2 * Real.exp ((2 * C) * ‖x‖) := by
        rw [mul_pow, sq_mul_exp_eq]
        ring

/-- **L² divergence inequality with constant one** (Pro round 6, R-019, verbatim head). -/
theorem finite_div_L2_le
    (d : ℕ) (F : GaussianFiniteCarrier d → GaussianFiniteCarrier d)
    (hF : GaussianC2AdmissibleField F) :
    eLpNorm (NlsGge.Ramer.finiteGaussianDivergence F) 2
        (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) ^ 2 ≤
      eLpNorm F 2
        (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) ^ 2 +
      eLpNorm (hsDeriv d F) 2
        (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) ^ 2 := by
  obtain ⟨hF2, C, hC, hbd⟩ := hF
  have hFg : ∀ x, ‖F x‖ ≤ C * Real.exp (C * ‖x‖) := fun x => by
    have h1 := hbd x
    have h2 := norm_nonneg (fderiv ℝ F x)
    have h3 := norm_nonneg (fderiv ℝ (fun y : GaussianFiniteCarrier d => fderiv ℝ F y) x)
    linarith
  have hDg : ∀ x, ‖fderiv ℝ F x‖ ≤ C * Real.exp (C * ‖x‖) := fun x => by
    have h1 := hbd x
    have h2 := norm_nonneg (F x)
    have h3 := norm_nonneg (fderiv ℝ (fun y : GaussianFiniteCarrier d => fderiv ℝ F y) x)
    linarith
  obtain ⟨hI1, hI2, hI3, -⟩ := integral_sq_finiteGaussianDivergence_expGrowth hF2 hC hFg hDg
  have hid := (integral_sq_finiteGaussianDivergence_expGrowth hF2 hC hFg hDg).2.2.2
  have hsI := r019_integrable_hsNormSq hF2 hC.le hDg
  have hF1 : ContDiff ℝ 1 F := hF2.of_le (by norm_num)
  have hle : ∫ x, (NlsGge.Ramer.finiteGaussianDivergence F x) ^ 2
        ∂(NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) ≤
      ∫ x, ‖F x‖ ^ 2 ∂(NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) +
        ∫ x, NlsGge.Ramer.hsNormSq (fderiv ℝ F x)
          ∂(NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) := by
    have hmono := integral_mono hI3 hsI
      (fun x => NlsGge.Ramer.traceCLM_comp_self_le (fderiv ℝ F x))
    rw [hid]
    linarith
  have hmem1 : MemLp (NlsGge.Ramer.finiteGaussianDivergence F) 2
      (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) :=
    (memLp_two_iff_integrable_sq
      (NlsGge.Ramer.continuous_finiteGaussianDivergence hF1).aestronglyMeasurable).2 hI1
  have hmem2 : MemLp F 2 (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) :=
    (memLp_two_iff_integrable_sq_norm hF2.continuous.aestronglyMeasurable).2 hI2
  have hmem3 : MemLp (hsDeriv d F) 2 (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) :=
    (memLp_two_iff_integrable_sq_norm (r019_continuous_hsDeriv hF2).aestronglyMeasurable).2
      (hsI.congr (ae_of_all _ fun x => by
        dsimp only
        rw [Real.norm_eq_abs, sq_abs, hsDeriv_sq]))
  have e1 : ∫ x, ‖NlsGge.Ramer.finiteGaussianDivergence F x‖ ^ 2
        ∂(NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) =
      ∫ x, (NlsGge.Ramer.finiteGaussianDivergence F x) ^ 2
        ∂(NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) :=
    integral_congr_ae (ae_of_all _ fun x => by dsimp only; rw [Real.norm_eq_abs, sq_abs])
  have e3 : ∫ x, ‖hsDeriv d F x‖ ^ 2
        ∂(NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) =
      ∫ x, NlsGge.Ramer.hsNormSq (fderiv ℝ F x)
        ∂(NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) :=
    integral_congr_ae (ae_of_all _ fun x => by
      dsimp only
      rw [Real.norm_eq_abs, sq_abs, hsDeriv_sq])
  have hA : 0 ≤ ∫ x, ‖F x‖ ^ 2 ∂(NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) :=
    integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, NlsGge.Ramer.hsNormSq (fderiv ℝ F x)
      ∂(NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) :=
    integral_nonneg fun x => NlsGge.Ramer.hsNormSq_nonneg _
  rw [r019_eLpNorm_two_sq hmem1, r019_eLpNorm_two_sq hmem2, r019_eLpNorm_two_sq hmem3, e1, e3,
    ← ENNReal.ofReal_add hA hB]
  exact ENNReal.ofReal_le_ofReal hle

/-- Difference of two finite Gaussian divergences (both fields differentiable). -/
theorem r019_finiteGaussianDivergence_sub
    {d : ℕ} (F G : GaussianFiniteCarrier d → GaussianFiniteCarrier d)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : GaussianFiniteCarrier d) :
    NlsGge.Ramer.finiteGaussianDivergence (fun y => F y - G y) x =
      NlsGge.Ramer.finiteGaussianDivergence F x -
        NlsGge.Ramer.finiteGaussianDivergence G x := by
  unfold NlsGge.Ramer.finiteGaussianDivergence
  simp only [fderiv_fun_sub (hF x) (hG x), ContinuousLinearMap.toLinearMap_sub, inner_sub_right,
    map_sub]
  ring

/-- Admissibility of a difference of two admissible fields (constant `C_F + C_G`). -/
theorem r019_admissible_sub
    {d : ℕ} {F G : GaussianFiniteCarrier d → GaussianFiniteCarrier d}
    (hF : GaussianC2AdmissibleField F) (hG : GaussianC2AdmissibleField G) :
    GaussianC2AdmissibleField (fun x => F x - G x) := by
  obtain ⟨hF2, CF, hCF, hbF⟩ := hF
  obtain ⟨hG2, CG, hCG, hbG⟩ := hG
  have hFd : Differentiable ℝ F := hF2.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG2.differentiable (by norm_num)
  have hFD : ContDiff ℝ 1 (fderiv ℝ F) := hF2.fderiv_right (m := 1) (by norm_num)
  have hGD : ContDiff ℝ 1 (fderiv ℝ G) := hG2.fderiv_right (m := 1) (by norm_num)
  have hFDd : Differentiable ℝ (fderiv ℝ F) := hFD.differentiable (by norm_num)
  have hGDd : Differentiable ℝ (fderiv ℝ G) := hGD.differentiable (by norm_num)
  have hfd : (fun y => fderiv ℝ (fun z => F z - G z) y) =
      fun y => fderiv ℝ F y - fderiv ℝ G y :=
    funext fun y => fderiv_fun_sub (hFd y) (hGd y)
  refine ⟨hF2.sub hG2, CF + CG, by linarith, fun x => ?_⟩
  have h1 : ‖F x - G x‖ ≤ ‖F x‖ + ‖G x‖ := norm_sub_le _ _
  have h2 : ‖fderiv ℝ (fun z => F z - G z) x‖ ≤ ‖fderiv ℝ F x‖ + ‖fderiv ℝ G x‖ := by
    rw [fderiv_fun_sub (hFd x) (hGd x)]
    exact norm_sub_le _ _
  have h3 : ‖fderiv ℝ (fun y => fderiv ℝ (fun z => F z - G z) y) x‖ ≤
      ‖fderiv ℝ (fun y => fderiv ℝ F y) x‖ + ‖fderiv ℝ (fun y => fderiv ℝ G y) x‖ := by
    rw [hfd, fderiv_fun_sub (hFDd x) (hGDd x)]
    exact norm_sub_le (fderiv ℝ (fun y => fderiv ℝ F y) x) (fderiv ℝ (fun y => fderiv ℝ G y) x)
  have hF' := hbF x
  have hG' := hbG x
  have ht : 0 ≤ ‖x‖ := norm_nonneg x
  have hKF : Real.exp (CF * ‖x‖) ≤ Real.exp ((CF + CG) * ‖x‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) ht)
  have hKG : Real.exp (CG * ‖x‖) ≤ Real.exp ((CF + CG) * ‖x‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) ht)
  have hA : CF * Real.exp (CF * ‖x‖) ≤ CF * Real.exp ((CF + CG) * ‖x‖) :=
    mul_le_mul_of_nonneg_left hKF hCF.le
  have hB : CG * Real.exp (CG * ‖x‖) ≤ CG * Real.exp ((CF + CG) * ‖x‖) :=
    mul_le_mul_of_nonneg_left hKG hCG.le
  calc ‖F x - G x‖ + ‖fderiv ℝ (fun z => F z - G z) x‖ +
        ‖fderiv ℝ (fun y => fderiv ℝ (fun z => F z - G z) y) x‖
      ≤ (‖F x‖ + ‖fderiv ℝ F x‖ + ‖fderiv ℝ (fun y => fderiv ℝ F y) x‖) +
          (‖G x‖ + ‖fderiv ℝ G x‖ + ‖fderiv ℝ (fun y => fderiv ℝ G y) x‖) := by
        linarith [h1, h2, h3]
    _ ≤ CF * Real.exp (CF * ‖x‖) + CG * Real.exp (CG * ‖x‖) := add_le_add hF' hG'
    _ ≤ CF * Real.exp ((CF + CG) * ‖x‖) + CG * Real.exp ((CF + CG) * ‖x‖) :=
        add_le_add hA hB
    _ = (CF + CG) * Real.exp ((CF + CG) * ‖x‖) := by ring

/-- **Difference form of the L² divergence inequality** (Pro round 6, R-019, verbatim head). -/
theorem finite_div_L2_sub_le
    (d : ℕ)
    (F G : GaussianFiniteCarrier d → GaussianFiniteCarrier d)
    (hF : GaussianC2AdmissibleField F)
    (hG : GaussianC2AdmissibleField G) :
    eLpNorm
        (fun x : GaussianFiniteCarrier d =>
          NlsGge.Ramer.finiteGaussianDivergence F x -
            NlsGge.Ramer.finiteGaussianDivergence G x)
        2 (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) ^ 2 ≤
      eLpNorm (fun x : GaussianFiniteCarrier d => F x - G x)
        2 (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) ^ 2 +
      eLpNorm (hsDeriv d (fun x : GaussianFiniteCarrier d => F x - G x))
        2 (NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) ^ 2 := by
  have hFd : Differentiable ℝ F := hF.1.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.1.differentiable (by norm_num)
  have e : (fun x : GaussianFiniteCarrier d =>
        NlsGge.Ramer.finiteGaussianDivergence F x - NlsGge.Ramer.finiteGaussianDivergence G x) =
      NlsGge.Ramer.finiteGaussianDivergence (fun x => F x - G x) :=
    funext fun x => (r019_finiteGaussianDivergence_sub F G hFd hGd x).symm
  rw [e]
  exact finite_div_L2_le d (fun x => F x - G x) (r019_admissible_sub hF hG)

end
end NlsGge.ThirdConsultation.R
