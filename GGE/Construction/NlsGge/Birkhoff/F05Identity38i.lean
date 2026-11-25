import NlsGge.Birkhoff.F05Identity38h
import NlsGge.Birkhoff.S01Equivariance38b
import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Spectral.ActualTraceFormulaQ024E02_38
import NlsGge.Hierarchy.RiccatiQ4FiniteProjectionSourceEnergyIdentityAfterSmoothDensityAndMatchingFifth

/-! # F05, file i: `V_2 = alV2` on `H¹` (L06.08(b)(2))

For `m = 2` the local remainder `V_2` of F03/F04 (`localRemainderSobolev38 2 β`) equals the explicit
`C:eq:V2positive` functional `alV2_38 β₁ β₂` of the AL chain.  Route: both are continuous on `H¹`;
on a finite Fourier projection `u = planeReal N z` (smooth, period one) the trig-polynomial local
formulas for `Q₀, Q₂, Q₄` (E02.06) and Parseval give
`V₂(u) = β₁ ∫|u|⁴ + β₂ ∫ [2|u|⁶ + 8|u|²|u'|² + 2Re(u² ū'²)]`, which is the explicit formula of
`alV2_eq_integral38` (pointwise `q4_integrand_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik Filter Topology
open NlsGge.HierarchyRiccati
open scoped ContDiff

/-- The coordinate identity `H¹ → H^{(2-1:ℕ)}`. -/
def castDown38 : SobolevHilbert 1 →L[ℝ] SobolevHilbert ((2 - 1 : ℕ) : ℝ) :=
  weightedRealComparisonContinuous (sobolevModeWeight 1) (sobolevModeWeight ((2 - 1 : ℕ) : ℝ)) 1
    (by norm_num) (fun n => by
      have : ((2 - 1 : ℕ) : ℝ) = 1 := by norm_num
      rw [this]; simp)

theorem castDown38_apply (x : SobolevHilbert 1) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight ((2 - 1 : ℕ) : ℝ)) from castDown38 x) n =
      (show WeightedHilbert (sobolevModeWeight 1) from x) n := rfl

theorem lift_planeReal38 (N : ℕ) (z : FourierPlane N) :
    riccatiSmoothPeriodicLiftContinuousMapRecovery30First (planeReal N z)
      (contDiff_planeReal N z).continuous (planeReal_periodic N z) = planeContinuous N z := by
  ext y
  obtain ⟨t, ht, rfl⟩ := exists_Ioc_rep38 y
  have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa using ht
  simp only [riccatiSmoothPeriodicLiftContinuousMapRecovery30First, ContinuousMap.coe_mk]
  rw [AddCircle.liftIoc_coe_apply ht']
  rfl


theorem smoothFourier_plane38 (N : ℕ) (z : FourierPlane N) (hu : ContDiff ℝ ∞ (planeReal N z))
    (n : ℤ) :
    smoothFourier38 (planeReal N z) hu (planeReal_periodic N z) n =
      physicalFourier (planeField N z) n := by
  unfold smoothFourier38
  have h := lift_planeReal38 N z
  have e : riccatiSmoothPeriodicLiftContinuousMapRecovery30First (planeReal N z) hu.continuous
      (planeReal_periodic N z) = planeContinuous N z := h
  rw [e]
  exact physicalFourier_planeL2 N z n

theorem coords_proj38 (N : ℕ) (y : SobolevHilbert 1) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight 1) from physicalH1FiniteProjection N y) n =
      physicalFourier (planeField N (physicalH1FiniteProjectionPlane N y)) n := by
  have h1 := physicalH1CarrierToL2AfterAcceptedCoordinate_fourier (physicalH1FiniteProjection N y) n
  have h2 := physicalH1FiniteProjection_fourier N y n
  have h3 : (show WeightedHilbert (sobolevModeWeight 1) from physicalH1FiniteProjection N y) n =
      physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate (physicalH1FiniteProjection N y)) n :=
    h1.symm
  rw [h3, h2]
  by_cases hn : n ∈ symmetricModes N
  · have hn' : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by
      simpa only [symmetricModes, Finset.mem_Icc] using hn
    obtain ⟨i, hi⟩ := modeIndex_covers N n hn'.1 hn'.2
    rw [if_pos hn, ← hi, physicalFourier_planeField]
    rfl
  · have hout : n < -(N : ℤ) ∨ (N : ℤ) < n := by
      simp only [symmetricModes, Finset.mem_Icc] at hn
      omega
    rw [if_neg hn, physicalFourier_planeField_outside N _ n hout]


theorem tsum_rate_smoothFourier38 (M : ℕ) (β : ℕ → ℝ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    ∑' n : ℤ, finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2 =
      ∑ j ∈ Finset.range (M + 1), β j * ∫ x in (0 : ℝ)..1, ‖iteratedDeriv j u x‖ ^ 2 := by
  have hP := fun j => smoothDerivative_parseval38 j u hu hper
  set c : ℕ → ℤ → ℝ := fun j n =>
    β j * ((2 * Real.pi * |(n : ℝ)|) ^ (2 * j) * ‖smoothFourier38 u hu hper n‖ ^ 2) with hc
  have hcs : ∀ j ∈ Finset.range (M + 1), Summable (c j) :=
    fun j _ => (hP j).1.mul_left (β j)
  have hfun : (fun n : ℤ => finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2) =
      fun n => ∑ j ∈ Finset.range (M + 1), c j n := by
    funext n
    simp only [finiteHierarchyRate38, finiteHierarchyW38, Finset.sum_mul, hc,
      two_pi_abs_pow_even38]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun, Summable.tsum_finsetSum hcs]
  apply Finset.sum_congr rfl
  intro j _
  rw [(hP j).2, hc]
  simp only
  rw [tsum_mul_left]
  rfl

/-- **T1.** On the finite Fourier projection `u = planeReal N z` of `y ∈ H¹`:
`V₂(u) = β₁ ∫|u|⁴ + β₂ ∫ [2|u|⁶ + 8|u|²|u'|² + 2Re(u² ū'²)]`. -/
theorem V2_trig38 (β : ℕ → ℝ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert ((2 - 1 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((2 - 1 : ℕ) : ℝ)) from x) n =
        smoothFourier38 u hu hper n) :
    localRemainderSobolev38 2 β (toCarrier38 _ x) =
      β 1 * (∫ t in (0 : ℝ)..1, ‖u t‖ ^ 4) +
      β 2 * (∫ t in (0 : ℝ)..1, (2 * ‖u t‖ ^ 6 + 8 * ‖u t‖ ^ 2 * ‖deriv u t‖ ^ 2 +
        2 * (u t ^ 2 * star (deriv u t) ^ 2).re)) := by
  obtain ⟨-, hV⟩ := localRemainderSobolev38_smooth_paperForm 2 le_rfl β u hu hper x hsource
  rw [hV, tsum_rate_smoothFourier38 2 β u hu hper, localEnergy38]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [complexQ0_local_formula_Q024, complexQ2_local_formula_Q024 u hu hper,
    complexQ4_local_formula_Q024 u hu hper]
  have hc0 : Continuous u := hu.continuous
  have hd1 : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hd2 : Continuous (iteratedDeriv 2 u) := hu.continuous_iteratedDeriv 2 (by simp)
  have hint : ∀ {f : ℝ → ℝ}, Continuous f → IntervalIntegrable f volume 0 1 :=
    fun hf => hf.intervalIntegrable 0 1
  simp only [iteratedDeriv_zero, iteratedDeriv_one]
  have i1 : IntervalIntegrable (fun t => ‖deriv u t‖ ^ 2) volume 0 1 :=
    hint (hd1.norm.pow 2)
  have i2 : IntervalIntegrable (fun t => ‖u t‖ ^ 4) volume 0 1 := hint (hc0.norm.pow 4)
  have i3 : IntervalIntegrable (fun t => ‖iteratedDeriv 2 u t‖ ^ 2) volume 0 1 :=
    hint (hd2.norm.pow 2)
  have i4 : IntervalIntegrable (fun t => 2 * ‖u t‖ ^ 6 + 8 * ‖u t‖ ^ 2 * ‖deriv u t‖ ^ 2 +
      2 * (u t ^ 2 * star (deriv u t) ^ 2).re) volume 0 1 := by
    refine hint ?_
    have : Continuous (fun t => (u t ^ 2 * star (deriv u t) ^ 2).re) :=
      Complex.continuous_re.comp ((hc0.pow 2).mul (hd1.star.pow 2))
    fun_prop
  have e2 : ∫ t in (0 : ℝ)..1, (‖deriv u t‖ ^ 2 + ‖u t‖ ^ 4) =
      (∫ t in (0 : ℝ)..1, ‖deriv u t‖ ^ 2) + ∫ t in (0 : ℝ)..1, ‖u t‖ ^ 4 :=
    intervalIntegral.integral_add i1 i2
  have e4 : ∫ t in (0 : ℝ)..1, (‖iteratedDeriv 2 u t‖ ^ 2 + 2 * ‖u t‖ ^ 6 +
      8 * ‖u t‖ ^ 2 * ‖deriv u t‖ ^ 2 + 2 * (u t ^ 2 * star (deriv u t) ^ 2).re) =
      (∫ t in (0 : ℝ)..1, ‖iteratedDeriv 2 u t‖ ^ 2) + ∫ t in (0 : ℝ)..1,
        (2 * ‖u t‖ ^ 6 + 8 * ‖u t‖ ^ 2 * ‖deriv u t‖ ^ 2 + 2 * (u t ^ 2 * star (deriv u t) ^ 2).re) := by
    rw [← intervalIntegral.integral_add i3 i4]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    ring
  rw [e2, e4]
  ring


/-- For `x ∈ F_N`, the weak derivative class of `x` is a.e. the classical derivative of
`u = planeReal N z` (`z` the plane of `x`). -/
theorem alDeriv_plane38 {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      alDeriv38 x t = deriv (planeReal N (physicalH1FiniteProjectionPlane N x)) t := by
  set z := physicalH1FiniteProjectionPlane N x with hz
  have h1 : physicalH1DerivativeL2CLM x =
      planeL2 N (derivativePlane N z) := by
    have := physicalH1FiniteProjection_derivative_isPlane N x
    rwa [alProj_eq38 hx] at this
  have h2 := planeL2_ae N (derivativePlane N z)
  have hv : (volume : Measure PhysicalCircle) = spatialMeasure := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp [spatialMeasure]
  have hm : MeasurePreserving (QuotientAddGroup.mk : ℝ → PhysicalCircle)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  have h2' : ∀ᵐ y ∂(volume : Measure PhysicalCircle),
      (planeL2 N (derivativePlane N z) : PhysicalCircle → ℂ) y = planeField N (derivativePlane N z) y := by
    rw [hv]; exact h2
  have h3 := hm.quasiMeasurePreserving.ae h2'
  filter_upwards [h3] with t ht
  have e1 : alDeriv38 x t = (planeL2 N (derivativePlane N z) : PhysicalCircle → ℂ) (t : PhysicalCircle) := by
    unfold alDeriv38; rw [h1]
  rw [e1, ht, (hasDerivAt_planeReal N z t).deriv]
  rfl

/-- **T2.** For `x ∈ F_N`, with `u = planeReal N z` the trigonometric polynomial of `x`:
`alV2 β₁ β₂ x = β₁ ∫|u|⁴ + β₂ ∫ [2|u|⁶ + 8|u|²|u'|² + 2Re(u² ū'²)]`. -/
theorem alV2_trig38 (β₁ β₂ : ℝ) {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    alV2_38 β₁ β₂ x =
      β₁ * (∫ t in (0 : ℝ)..1, ‖planeReal N (physicalH1FiniteProjectionPlane N x) t‖ ^ 4) +
      β₂ * (∫ t in (0 : ℝ)..1, (2 * ‖planeReal N (physicalH1FiniteProjectionPlane N x) t‖ ^ 6 +
        8 * ‖planeReal N (physicalH1FiniteProjectionPlane N x) t‖ ^ 2 *
          ‖deriv (planeReal N (physicalH1FiniteProjectionPlane N x)) t‖ ^ 2 +
        2 * (planeReal N (physicalH1FiniteProjectionPlane N x) t ^ 2 *
          star (deriv (planeReal N (physicalH1FiniteProjectionPlane N x)) t) ^ 2).re)) := by
  set z := physicalH1FiniteProjectionPlane N x with hz
  obtain ⟨-, -, hV⟩ := alV2_eq_integral38 β₁ β₂ x
  rw [hV]
  have hc : ∀ t, alCanon38 x t = planeReal N z t := fun t => alCanon_plane38 hx t
  simp only [hc]
  congr 2
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [alDeriv_plane38 hx] with t ht
  have ht' : alDeriv38 x t = deriv (planeReal N z) t := ht
  rw [ht']
  have := NlsGge.HierarchyRiccati.Core.q4_integrand_eq (planeReal N z t)
    (deriv (planeReal N z) t) 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
  have hs : star (deriv (planeReal N z) t) = (starRingEnd ℂ) (deriv (planeReal N z) t) := rfl
  rw [hs]
  linarith


theorem Vm2_eq_alV2_F38 (β₀ β₁ β₂ : ℝ) {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    Vm38 2 (alQ4Beta38 β₀ β₁ β₂) (castDown38 x) = alV2_38 β₁ β₂ x := by
  set z := physicalH1FiniteProjectionPlane N x with hz
  have hu : ContDiff ℝ ∞ (planeReal N z) := (contDiff_planeReal N z).of_le (by simp)
  have hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((2 - 1 : ℕ) : ℝ)) from castDown38 x) n =
        smoothFourier38 (planeReal N z) hu (planeReal_periodic N z) n := by
    intro n
    rw [castDown38_apply, smoothFourier_plane38 N z hu n]
    have := coords_proj38 N x n
    rw [alProj_eq38 hx] at this
    exact this
  have h1 := V2_trig38 (alQ4Beta38 β₀ β₁ β₂) (planeReal N z) hu (planeReal_periodic N z)
    (castDown38 x) hsource
  have h2 := alV2_trig38 β₁ β₂ hx
  have hb1 : alQ4Beta38 β₀ β₁ β₂ 1 = β₁ := by simp [alQ4Beta38]
  have hb2 : alQ4Beta38 β₀ β₁ β₂ 2 = β₂ := by simp [alQ4Beta38]
  unfold Vm38
  rw [h1, h2, hb1, hb2]

/-- **L06.08(b)(2).** `V₂ = alV2_38 β₁ β₂` on `H¹`, for every `y`. -/
theorem Vm2_eq_alV2 (β₀ β₁ β₂ : ℝ) (y : SobolevHilbert 1) :
    Vm38 2 (alQ4Beta38 β₀ β₁ β₂) (castDown38 y) = alV2_38 β₁ β₂ y := by
  have hc1 : Continuous (fun y : SobolevHilbert 1 => Vm38 2 (alQ4Beta38 β₀ β₁ β₂) (castDown38 y)) :=
    ((continuous_localRemainderSobolev38 2 (alQ4Beta38 β₀ β₁ β₂)).comp
      (continuous_toCarrier38 _)).comp castDown38.continuous
  have hc2 := continuous_alV2_38 β₁ β₂
  have ht := physicalH1FiniteProjection_tendsto y
  have h1 := (hc1.tendsto y).comp ht
  have h2 := (hc2.tendsto y).comp ht
  refine tendsto_nhds_unique h1 (h2.congr' (Filter.Eventually.of_forall fun N => ?_))
  exact (Vm2_eq_alV2_F38 β₀ β₁ β₂ (alProj_inF38 N y)).symm

end NlsGge.Birkhoff
