import NlsGge.GK38.GradTauGammaKernelMap
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Uniqueness of the continuous bilinear L2 gradient representative. Testing
against its conjugate L2 class earns a zero squared-mass integral, then genuine
continuous a.e. uniqueness restores every closed-unit time, including endpoints. -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open scoped ComplexConjugate
namespace NlsGge.GK38
noncomputable section

theorem k4aKernelPairingMap_zero38 (g : PairKernelCont38)
    (hg : k4aKernelPairingMap38 g = 0) : g = 0 := by
  let gs : PairKernelCont38 :=
    ⟨fun t i => conj (g t i), by
      apply continuous_pi
      intro i
      exact Complex.continuous_conj.comp ((continuous_apply i).comp g.continuous)⟩
  let h : PotPair := pairKernelL2Class38 gs
  let F : ℝ → ℝ := fun s => ‖pairKernelExt38 g s 0‖ ^ 2 + ‖pairKernelExt38 g s 1‖ ^ 2
  have h0 : Continuous (fun s => pairKernelExt38 g s 0) :=
    (continuous_apply 0).comp (continuous_pairKernelExt38 g)
  have h1 : Continuous (fun s => pairKernelExt38 g s 1) :=
    (continuous_apply 1).comp (continuous_pairKernelExt38 g)
  have hF : Continuous F := (h0.norm.pow 2).add (h1.norm.pow 2)
  have hFi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable _ _
  have he : pairIntegral38 g ⟨1, zero_le_one, le_rfl⟩ h =
      ((∫ s in (0 : ℝ)..1, F s : ℝ) : ℂ) := by
    unfold pairIntegral38
    change (∫ s in (0 : ℝ)..1,
      pairKernelExt38 g s 0 * potRepFst38 h s + pairKernelExt38 g s 1 * potRepSnd38 h s) =
        ((∫ s in (0 : ℝ)..1, F s : ℝ) : ℂ)
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc]
    filter_upwards [pairKernelL2Class38_rep gs, ae_restrict_mem measurableSet_Icc] with s hs hm
    change pairKernelExt38 g s 0 * potRepFst38 (pairKernelL2Class38 gs) s +
      pairKernelExt38 g s 1 * potRepSnd38 (pairKernelL2Class38 gs) s = _
    rw [hs.1, hs.2, pairKernelExt38_of_mem gs hm, pairKernelExt38_of_mem g hm]
    dsimp only [gs, F]
    rw [pairKernelExt38_of_mem g hm]
    change g ⟨s, hm⟩ 0 * conj (g ⟨s, hm⟩ 0) +
      g ⟨s, hm⟩ 1 * conj (g ⟨s, hm⟩ 1) =
        ((‖g ⟨s, hm⟩ 0‖ ^ 2 + ‖g ⟨s, hm⟩ 1‖ ^ 2 : ℝ) : ℂ)
    simp only [Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow]
  have hz : pairIntegral38 g ⟨1, zero_le_one, le_rfl⟩ h = 0 := by
    change k4aKernelPairingMap38 g h = 0
    rw [hg]
    rfl
  have hreal : (∫ s in (0 : ℝ)..1, F s) = 0 :=
    Complex.ofReal_eq_zero.mp (by rw [← he, hz])
  have hae : F =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
      (Filter.Eventually.of_forall (fun s => add_nonneg (sq_nonneg _) (sq_nonneg _))) hFi).mp hreal
  rw [restrict_Ioc_eq_restrict_Icc] at hae
  have hp : EqOn F 0 (Icc (0 : ℝ) 1) :=
    Measure.eqOn_Icc_of_ae_eq volume (by norm_num) hae hF.continuousOn continuous_const.continuousOn
  ext t i
  have ht := hp t.2
  change ‖pairKernelExt38 g t 0‖ ^ 2 + ‖pairKernelExt38 g t 1‖ ^ 2 = 0 at ht
  rw [pairKernelExt38_of_mem g t.2] at ht
  change ‖g t 0‖ ^ 2 + ‖g t 1‖ ^ 2 = 0 at ht
  apply norm_eq_zero.mp
  fin_cases i
  · change ‖g t 0‖ = 0
    nlinarith [norm_nonneg (g t 0), sq_nonneg ‖g t 1‖]
  · change ‖g t 1‖ = 0
    nlinarith [norm_nonneg (g t 1), sq_nonneg ‖g t 0‖]

theorem k4aKernelPairingMap_injective38 : Function.Injective k4aKernelPairingMap38 := by
  intro g k h
  have hz : k4aKernelPairingMap38 (g - k) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (k4aKernelPairingMap_zero38 (g - k) hz)

end
end NlsGge.GK38
