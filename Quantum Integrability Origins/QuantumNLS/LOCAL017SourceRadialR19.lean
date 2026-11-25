import QuantumNLS.LOCAL017SourceOperatorsR19

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.LOCAL017SourceR19
open Ext025A4BanachComplexification Ext025A4BanachSeries

def radialValue (G : CH → CForm) (z : CH) (t : ℝ) : CCov :=
  (t : ℂ) • G ((t : ℂ) • z) z

def radialDeriv (G : CH → CForm) (z : CH) (t : ℝ) : CH →L[ℂ] CCov :=
  (t : ℂ) • G ((t : ℂ) • z) + (t : ℂ)^2 •
    ((ContinuousLinearMap.apply ℂ CCov z).comp (fderiv ℂ G ((t : ℂ) • z)))

def radialBeta (G : CH → CForm) (z : CH) : CCov :=
  ∫ t in Icc (0 : ℝ) 1, radialValue G z t

theorem scale_mem {R : ℝ} {z : CH} (hz : z ∈ ball 0 R) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (t : ℂ) • z ∈ ball (0 : CH) R := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz

theorem radial_cont {G : CH → CForm} {R : ℝ} (hg : ContinuousOn G (ball 0 R))
    {z : CH} (hz : z ∈ ball 0 R) :
    ContinuousOn (radialValue G z) (Icc (0 : ℝ) 1) := by
  have hs : ContinuousOn (fun t : ℝ => (t : ℂ) • z) (Icc (0 : ℝ) 1) :=
    (Complex.continuous_ofReal.smul continuous_const).continuousOn
  exact Complex.continuous_ofReal.continuousOn.smul
    ((hg.comp hs (fun _ ht => scale_mem hz ht)).clm_apply continuousOn_const)

theorem radial_dcont {G : CH → CForm} {R : ℝ}
    (hg : AnalyticOnNhd ℂ G (ball 0 R)) {z : CH} (hz : z ∈ ball 0 R) :
    ContinuousOn (radialDeriv G z) (Icc (0 : ℝ) 1) := by
  have hs : ContinuousOn (fun t : ℝ => (t : ℂ) • z) (Icc (0 : ℝ) 1) :=
    (Complex.continuous_ofReal.smul continuous_const).continuousOn
  have hgd : ContDiffOn ℂ 1 G (ball 0 R) := hg.contDiffOn_of_completeSpace
  have hd := hgd.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hd' := hd.comp hs (fun _ ht => scale_mem hz ht)
  have hc : Continuous (fun A : CH →L[ℂ] CForm =>
      (ContinuousLinearMap.apply ℂ CCov z).comp A) :=
    ((ContinuousLinearMap.compL ℂ CH CForm CCov) (ContinuousLinearMap.apply ℂ CCov z)).continuous
  exact (Complex.continuous_ofReal.continuousOn.smul
    (hg.continuousOn.comp hs (fun _ ht => scale_mem hz ht))).add
    ((Complex.continuous_ofReal.continuousOn.pow 2).smul (hc.comp_continuousOn hd'))

theorem radial_hasFDerivAt {G : CH → CForm} {R : ℝ}
    (hg : DifferentiableOn ℂ G (ball 0 R)) {z : CH} (hz : z ∈ ball 0 R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt (fun z => radialValue G z t) (radialDeriv G z t) z := by
  have hh := ((hg.differentiableAt (isOpen_ball.mem_nhds (scale_mem hz ht))).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul (t : ℂ))).clm_apply (hasFDerivAt_id z)
  apply (hh.const_smul (t : ℂ)).congr_fderiv
  ext a h
  simp [radialDeriv, smul_smul, pow_two]

/-- A uniform operator bound for the derivative of the radial integrand. -/
theorem radial_derivative_bound {G : CH → CForm} {R C K : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ z ∈ ball (0 : CH) R, ‖G z‖ ≤ C * ‖z‖^2)
    (hd : ∀ z ∈ ball (0 : CH) R, ‖fderiv ℂ G z‖ ≤ K)
    {z : CH} (hz : z ∈ ball 0 R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖radialDeriv G z t‖ ≤ C*R^2 + K*R := by
  have htz := scale_mem hz ht
  have hn : ‖(t : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hnz : ‖z‖ ≤ R := (mem_ball_zero_iff.mp hz).le
  have hntz : ‖(t : ℂ) • z‖ ≤ R := (mem_ball_zero_iff.mp htz).le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  simp only [radialDeriv, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  have hg0 : ‖G ((t : ℂ) • z)‖ ≤ C*R^2 := (hb _ htz).trans (by gcongr)
  calc
    _ ≤ ‖(t : ℂ) • G ((t : ℂ) • z) a‖ +
      ‖(t : ℂ)^2 • (fderiv ℂ G ((t : ℂ) • z) a) z‖ := norm_add_le _ _
    _ ≤ (C*R^2)*‖a‖ + (K*‖a‖)*R := by
      apply add_le_add
      · rw [norm_smul]
        exact (mul_le_mul hn ((G _).le_opNorm a) (norm_nonneg _) zero_le_one).trans
          (by simpa using mul_le_mul_of_nonneg_right hg0 (norm_nonneg a))
      · rw [norm_smul, norm_pow]
        have h1 := (fderiv ℂ G ((t : ℂ) • z) a).le_opNorm z
        have h2 := (fderiv ℂ G ((t : ℂ) • z)).le_opNorm a
        calc
          _ ≤ 1 * ((K*‖a‖)*R) := mul_le_mul (by nlinarith [norm_nonneg (t : ℂ)])
            (h1.trans (mul_le_mul (h2.trans (mul_le_mul_of_nonneg_right (hd _ htz) (norm_nonneg a))) hnz (norm_nonneg _) (by positivity)))
            (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
    _ = _ := by ring

/-- Bochner integration preserves the common holomorphic covector extension. -/
theorem radial_holomorphic {G : CH → CForm} {R C K : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hg : AnalyticOnNhd ℂ G (ball 0 R))
    (hb : ∀ z ∈ ball (0 : CH) R, ‖G z‖ ≤ C * ‖z‖^2)
    (hd : ∀ z ∈ ball (0 : CH) R, ‖fderiv ℂ G z‖ ≤ K) :
    DifferentiableOn ℂ (radialBeta G) (ball 0 R) := by
  intro z hz
  have hmeas (y : CH) (hy : y ∈ ball 0 R) :
      AEStronglyMeasurable (radialValue G y) (volume.restrict (Icc (0 : ℝ) 1)) :=
    (radial_cont hg.continuousOn hy).aestronglyMeasurable_of_subset_isCompact
      isCompact_Icc measurableSet_Icc (Subset.refl _)
  have hi := ((radial_cont hg.continuousOn hz).intervalIntegrable_of_Icc (μ := volume) zero_le_one)
  have hi' : Integrable (radialValue G z) (volume.restrict (Icc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (F := radialValue G) (F' := radialDeriv G) (bound := fun _ => C*R^2+K*R)
    (isOpen_ball.mem_nhds hz)
    (by filter_upwards [isOpen_ball.mem_nhds hz] with y hy using hmeas y hy) hi'
    ((radial_dcont hg hz).aestronglyMeasurable_of_subset_isCompact
      isCompact_Icc measurableSet_Icc (Subset.refl _))
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht y hy
        exact radial_derivative_bound hR hC hK hb hd hy ht)
    (integrable_const _)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht y hy
        exact radial_hasFDerivAt hg.differentiableOn hy ht)
  exact hh.differentiableAt.differentiableWithinAt

end QuantumNLS.LOCAL017SourceR19
