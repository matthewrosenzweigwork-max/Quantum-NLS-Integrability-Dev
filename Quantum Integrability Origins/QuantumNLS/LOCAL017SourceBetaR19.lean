import QuantumNLS.LOCAL017SourceRadialR19

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.LOCAL017SourceR19
open Ext025A4BanachComplexification Ext025A4BanachSeries

/-- The common cubic bound follows before any scalar Haar averaging. -/
theorem radial_cubic {G : CH → CForm} {R C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z ∈ ball (0 : CH) R, ‖G z‖ ≤ C * ‖z‖^2)
    {z : CH} (hz : z ∈ ball 0 R) : ‖radialBeta G z‖ ≤ C * ‖z‖^3 := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have hh : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖radialValue G z t‖ ≤ C * ‖z‖^3 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hn : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    have htz : ‖(t : ℂ) • z‖ ≤ ‖z‖ := by
      rw [norm_smul]
      simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg z)
    have hg : ‖G ((t : ℂ) • z)‖ ≤ C * ‖z‖^2 :=
      (hb _ (scale_mem hz ht)).trans (by gcongr)
    calc
      ‖radialValue G z t‖ = ‖(t : ℂ)‖ * ‖G ((t : ℂ) • z) z‖ := norm_smul _ _
      _ ≤ 1 * ((C * ‖z‖^2) * ‖z‖) :=
        mul_le_mul hn (((G _).le_opNorm z).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg z)))
          (norm_nonneg _) zero_le_one
      _ = _ := by ring
  simpa only [radialBeta, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hh

/-- The complex radial integral agrees with the frozen native beta, including
its interval convention and the real covector evaluation. -/
theorem radial_real (S : ResetMoser.Hyp) {R M : ℝ} (hL : ResetMoser.Loc S R M)
    {G : CH → CForm} (hg : ContinuousOn G (ball 0 R))
    (he : ∀ x ∈ ball (0 : H) R, ∀ v w,
      G (Cx.ι x) (Cx.ι v) (Cx.ι w) = (ResetMoser.Dl S x v w : ℂ))
    {z : H} (hz : z ∈ ball 0 R) (h : H) :
    radialBeta G (Cx.ι z) (Cx.ι h) = (ResetMoser.betaR S z h : ℂ) := by
  have hzi : Cx.ι z ∈ ball (0 : CH) R := by simpa [mem_ball_zero_iff, Cx.norm_ι] using hz
  have hi : Integrable (radialValue G (Cx.ι z)) (volume.restrict (Icc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      ((radial_cont hg hzi).intervalIntegrable_of_Icc (μ := volume) zero_le_one)
  have hiR := (ResetMoser.radial_cont S hL hz).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  rw [radialBeta, ContinuousLinearMap.integral_apply hi]
  have he' : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      radialValue G (Cx.ι z) t (Cx.ι h) = ((t • ResetMoser.Dl S (t • z) z) h : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [radialValue, _root_.smul_apply]
    rw [← Cx.ι_smul, he _ (ResetMoser.scale_mem' hz ht)]
    simp
  rw [integral_congr_ae he', integral_complex_ofReal]
  congr 1
  rw [ResetMoser.betaR, ContinuousLinearMap.intervalIntegral_apply hiR,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]

/-- Shrink a native Loc bundle without changing its source or constants. -/
theorem loc_mono {S : ResetMoser.Hyp} {R M r : ℝ} (hL : ResetMoser.Loc S R M)
    (hr : 0 < r) (hrR : r ≤ R) : ResetMoser.Loc S r M :=
  ⟨hr, hrR.trans hL.ρR, hL.M0,
    fun z hz => hL.b2 z (ball_subset_ball hrR hz),
    fun z hz => hL.b1 z (ball_subset_ball hrR hz),
    fun z hz => hL.b0 z (ball_subset_ball hrR hz)⟩

/-- All common complexification inputs are now derived from native S. -/
theorem source_beta_extension (S : ResetMoser.Hyp) :
    ∃ R M C : ℝ, ResetMoser.Loc S R M ∧ 0 ≤ C ∧ ∃ G : CH → CForm,
      DifferentiableOn ℂ (radialBeta G) (ball 0 R) ∧
      (∀ z ∈ ball (0 : CH) R, ‖radialBeta G z‖ ≤ C * ‖z‖^3) ∧
      (∀ x ∈ ball (0 : H) R, ∀ h,
        radialBeta G (Cx.ι x) (Cx.ι h) = (ResetMoser.betaR S x h : ℂ)) := by
  obtain ⟨R0, hR0, _, C, hC, G, hg, hb, he⟩ := source_complex_form S
  obtain ⟨r, M, hL⟩ := S.exists_loc
  have hdc : ContinuousAt (fderiv ℂ G) 0 :=
    ((hg 0 (mem_ball_self hR0)).contDiffAt (n := 1)).continuousAt_fderiv (by norm_num)
  obtain ⟨d, hd, hdb⟩ := Metric.continuousAt_iff.mp hdc 1 one_pos
  let R := min (r/2) (min R0 d)
  have hR : 0 < R := lt_min (half_pos hL.ρpos) (lt_min hR0 hd)
  have hRR0 : R ≤ R0 := (min_le_right _ _).trans (min_le_left _ _)
  have hRd : R ≤ d := (min_le_right _ _).trans (min_le_right _ _)
  have hL' := loc_mono hL hR
    ((min_le_left _ _).trans (half_le_self hL.ρpos.le))
  have hg' := hg.mono (ball_subset_ball hRR0)
  have hb' : ∀ z ∈ ball (0 : CH) R, ‖G z‖ ≤ C * ‖z‖^2 :=
    fun z hz => hb z (ball_subset_ball hRR0 hz)
  let K := ‖fderiv ℂ G 0‖ + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : ∀ z ∈ ball (0 : CH) R, ‖fderiv ℂ G z‖ ≤ K := by
    intro z hz
    have hh := hdb ((ball_subset_ball hRd) hz)
    rw [dist_eq_norm] at hh
    have hh' := norm_sub_norm_le (fderiv ℂ G z) (fderiv ℂ G 0)
    dsimp [K]
    linarith
  exact ⟨R, M, C, hL', hC, G,
    radial_holomorphic hR hC hK hg' hb' hD,
    fun _ hz => radial_cubic hC hb' hz,
    fun _ hz h => radial_real S hL' hg'.continuousOn
      (fun x hx => he x (ball_subset_ball hRR0 hx)) hz h⟩

end QuantumNLS.LOCAL017SourceR19
