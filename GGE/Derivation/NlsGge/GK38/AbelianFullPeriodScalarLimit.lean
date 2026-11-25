import NlsGge.GK38.AbelianFullPeriodScalarAnalytic
import NlsGge.GK38.AbelianScaledOmittedRatio

/-! UNCOMPILED actual scalar full-period limit on each FIXED actual contour.
Integrability, denominator nonzero and norm domination are earned before
the integral difference estimate. No operator-norm limit is asserted here. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6FullPeriodCoordinate_limit38 (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) (m : ℤ) :
    Tendsto (fun k : ℕ => ((((k : ℤ)-m : ℤ) : ℂ)) *
      abelianPeriod38 m φ (p2FullNumerator38 (k : ℤ) s)) atTop
      (𝓝 (p6FullPeriodCoordinate38 (φ,s) m)) := by
  let C : ℂ := discC φ m
  let R : ℝ := discR φ m
  let G : ℂ → ℂ := fun z => P6FullNumeratorVariation.fullNumerator s z/canonRoot38 φ z
  have hr : 0 < R := isolating_radius_pos38 (isolating_family38 φ hφ) m
  have hsphere : sphere C R ⊆ actionCutDomain38 φ :=
    fixed_sphere_subset φ (discC φ) (discR φ) (isolating_family38 φ hφ) m
  have hG : ContinuousOn G (sphere C R) :=
    ((p2Quotient_analytic38 φ hφ (P6FullNumeratorVariation.fullNumerator s)
      (p6FullNumerator_entire38 s)).mono hsphere).continuousOn
  obtain ⟨M₀,hM₀⟩ := (isCompact_sphere C R).exists_bound_of_continuousOn hG
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hGM : ∀ z ∈ sphere C R, ‖G z‖ ≤ M :=
    fun z hz => (hM₀ z hz).trans (le_max_left _ _)
  let D : ℝ := ‖C‖+R
  have hD : 0 ≤ D := add_nonneg (norm_nonneg _) hr.le
  have hzD (z : ℂ) (hz : z ∈ sphere C R) : ‖z‖ ≤ D := by
    have hd : ‖z-C‖=R := by simpa only [mem_sphere_iff_norm] using hz
    have ht := norm_le_norm_sub_add z C
    rw [hd] at ht
    dsimp [D]
    linarith
  have hfull : CircleIntegrable G C R := p6FullPeriod_integrable38 m φ hφ s
  rw [Metric.tendsto_nhds]
  intro ε hε
  let A : ℝ := 2*Real.pi*R*(M+1)+1
  have hA : 0 < A := by dsimp [A]; positivity
  let η : ℝ := ε/A
  have hη : 0 < η := div_pos hε hA
  obtain ⟨N,hN⟩ := p6ScaleRatio_uniform_bounded_set38 m s D hD η hη
  filter_upwards [eventually_ge_atTop N] with k hk
  let a : ℂ := ((((k : ℤ)-m : ℤ) : ℂ))
  let F : ℂ → ℂ := fun z => a*(p2FullNumerator38 (k : ℤ) s z/canonRoot38 φ z)
  have hbase := p2Period_integrable38 m (k : ℤ) φ hφ s
  have hscaled : CircleIntegrable F C R := by
    simpa only [F,Pi.smul_apply,smul_eq_mul] using! hbase.const_smul (a := a)
  have hpoint (z : ℂ) (hz : z ∈ sphere C R) : ‖F z-G z‖ ≤ η*M := by
    obtain ⟨hden,herror⟩ := hN k hk z (hzD z hz)
    have hroot : canonRoot38 φ z ≠ 0 := canonRoot_ne_zero38 φ hφ z (hsphere hz)
    have he : F z-G z=(p6ScaleRatio38 k m s z-1)*G z := by
      dsimp [F,G,a]
      rw [P6FullNumeratorVariation.fullNumerator_factor (k : ℤ) s z]
      unfold p6ScaleRatio38
      field_simp [hden,hroot,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
      push_cast
      ring
    rw [he,norm_mul]
    exact mul_le_mul herror.le (hGM z hz) (norm_nonneg _) hη.le
  have heq : a*abelianPeriod38 m φ (p2FullNumerator38 (k : ℤ) s)-
      p6FullPeriodCoordinate38 (φ,s) m = circleIntegral (fun z => F z-G z) C R := by
    unfold p6FullPeriodCoordinate38 abelianPeriod38
    rw [← circleIntegral.integral_const_mul,
      ← circleIntegral.integral_sub hscaled hfull]
  have hb : ‖a*abelianPeriod38 m φ (p2FullNumerator38 (k : ℤ) s)-
      p6FullPeriodCoordinate38 (φ,s) m‖ ≤ 2*Real.pi*R*(η*M) := by
    rw [heq]
    exact circleIntegral.norm_integral_le_of_norm_le_const hr.le hpoint
  have hfinal : 2*Real.pi*R*(η*M) < ε := by
    have hcoef : 0 ≤ 2*Real.pi*R := by positivity
    have hsmall : 2*Real.pi*R*M < A := by dsimp [A]; nlinarith
    have he : η*A=ε := div_mul_cancel₀ ε hA.ne'
    have hh := mul_lt_mul_of_pos_left hsmall hη
    rw [he] at hh
    nlinarith
  simpa only [dist_eq_norm,a] using hb.trans_lt hfinal

end
end NlsGge.GK38
