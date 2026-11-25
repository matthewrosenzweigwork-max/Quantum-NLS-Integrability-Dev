import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UniformSpace.Ascoli
import QuantumNLS.DEF014Continuity
import QuantumNLS.DEF014DiscriminantAnalytic
import QuantumNLS.DEF014PhaseAnalytic
import QuantumNLS.DEF014SeparatorAnalytic


/-! The exact Cauchy-contour formula for interval masses. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace QuantumNLS.DEF014Contour

/-- A pole outside the closed disk contributes zero. -/
theorem integral_kernel_outside {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hw : R < ‖w-c‖) : (∮ z in C(c,R), (z-w)⁻¹) = 0 := by
  have hn : ∀ z ∈ Metric.closedBall c R, z-w ≠ 0 := by
    intro z hz he
    have heq : z = w := sub_eq_zero.mp he
    subst z
    exact (not_le.mpr hw) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
  apply DiffContOnCl.circleIntegral_eq_zero hR.le
  constructor
  · intro z hz
    exact ((differentiableAt_id.sub_const w).inv (hn z (Metric.ball_subset_closedBall hz))).differentiableWithinAt
  · apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    exact hn z (by simpa [closure_ball c hR.ne'] using hz)

/-- Fubini on a circle separated uniformly from the measure's support. -/
theorem integral_cauchy (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℝ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ᵐ (t : ℝ) ∂μ, δ ≤ |‖(t : ℂ) - (c : ℂ)‖ - R|) :
    (∮ z in C((c : ℂ),R), EmpiricalRapidity.cauchyTransform μ z) =
      (2 * (Real.pi : ℂ) * I) * (μ {t : ℝ | ‖(t : ℂ)-(c : ℂ)‖ < R}).toReal := by
  let F : ℝ → ℝ → ℂ := fun θ t =>
    deriv (circleMap (c : ℂ) R) θ * (circleMap (c : ℂ) R θ - (t : ℂ))⁻¹
  have hdist (θ t : ℝ) (ht : δ ≤ |‖(t : ℂ)-(c : ℂ)‖-R|) :
      δ ≤ ‖circleMap (c : ℂ) R θ - (t : ℂ)‖ := by
    have h := abs_norm_sub_norm_le ((t : ℂ)-(c : ℂ)) (circleMap (c : ℂ) R θ-(c : ℂ))
    have hc : ‖circleMap (c : ℂ) R θ-(c : ℂ)‖ = R := by
      simp [circleMap, abs_of_pos hR]
    rw [hc] at h
    have he : (t : ℂ)-(c : ℂ) - (circleMap (c : ℂ) R θ-(c : ℂ)) =
        - (circleMap (c : ℂ) R θ-(t : ℂ)) := by ring
    rw [he, norm_neg] at h
    exact ht.trans h
  have hmeas : Measurable (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    simp_rw [deriv_circleMap]
    fun_prop
  let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    rw [uIoc_of_le Real.two_pi_pos.le]
    infer_instance
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))).prod μ) := by
    apply (integrable_const (R * δ⁻¹)).mono' hmeas.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hmeas.norm measurable_const)).mpr
    exact Eventually.of_forall fun θ => hgap.mono fun t ht => by
      dsimp [Function.uncurry, F]
      rw [norm_mul, norm_inv]
      have hd : ‖deriv (circleMap (c : ℂ) R) θ‖ = R := by
        simp [deriv_circleMap, norm_circleMap_zero, abs_of_pos hR]
      rw [hd]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hδ (hdist θ t ht)) hR.le
  have hswap := intervalIntegral_integral_swap hi
  have hformula : ∀ᵐ (t : ℝ) ∂μ, (∮ z in C((c : ℂ),R), (z-(t : ℂ))⁻¹) =
      {s : ℝ | ‖(s : ℂ)-(c : ℂ)‖ < R}.indicator
        (fun _ => (2 * (Real.pi : ℂ) * I)) t := by
    filter_upwards [hgap] with t ht
    by_cases hin : ‖(t : ℂ)-(c : ℂ)‖ < R
    · simp only [Set.indicator, mem_ofPred, hin, ↓reduceIte]
      exact circleIntegral.integral_sub_inv_of_mem_ball (by simpa [Metric.mem_ball, dist_eq_norm] using hin)
    · simp only [Set.indicator, mem_ofPred, hin, ↓reduceIte]
      have hout : R < ‖(t : ℂ)-(c : ℂ)‖ := by
        have he : ‖(t : ℂ)-(c : ℂ)‖ ≠ R := by intro he; rw [he, sub_self, abs_zero] at ht; linarith
        exact lt_of_le_of_ne (le_of_not_gt hin) he.symm
      exact integral_kernel_outside hR hout
  calc
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ t, F θ t ∂μ := by
      unfold circleIntegral EmpiricalRapidity.cauchyTransform
      congr 1
      funext θ
      exact (integral_const_mul _ _).symm
    _ = ∫ (t : ℝ), (∮ z in C((c : ℂ),R), (z-(t : ℂ))⁻¹) ∂μ := hswap
    _ = ∫ (t : ℝ), {s : ℝ | ‖(s : ℂ)-(c : ℂ)‖ < R}.indicator
        (fun _ => (2 * (Real.pi : ℂ) * I)) t ∂μ := integral_congr_ae hformula
    _ = _ := by
      rw [integral_indicator (isOpen_lt (by fun_prop) continuous_const).measurableSet,
        integral_const]
      simp [measureReal_def, Complex.real_smul, mul_comm]

/-- The normalization is exactly 1/(2*pi*i). -/
theorem normalized_integral_cauchy (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℝ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ᵐ (t : ℝ) ∂μ, δ ≤ |‖(t : ℂ)-(c : ℂ)‖-R|) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ z in C((c : ℂ),R), EmpiricalRapidity.cauchyTransform μ z) =
      ((μ {t : ℝ | ‖(t : ℂ)-(c : ℂ)‖ < R}).toReal : ℂ) := by
  rw [integral_cauchy μ c hR hδ hgap, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]

/-- The Cauchy kernel is integrable at any point with an almost-everywhere
positive distance from the support, including real points in open bands. -/
theorem integrable_kernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : ∀ᵐ (t : ℝ) ∂μ, δ ≤ ‖z-(t : ℂ)‖) :
    Integrable (fun t : ℝ => (z-(t : ℂ))⁻¹) μ := by
  refine (integrable_const δ⁻¹).mono'
    ((measurable_const.sub Complex.measurable_ofReal).inv.aestronglyMeasurable) ?_
  filter_upwards [hz] with t ht
  rw [norm_inv]
  exact inv_anti₀ hδ ht

/-- A common support distance supplies a uniform spectral Lipschitz bound. -/
theorem norm_cauchy_sub_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {z w : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : ∀ᵐ (t : ℝ) ∂μ, δ ≤ ‖z-(t : ℂ)‖)
    (hw : ∀ᵐ (t : ℝ) ∂μ, δ ≤ ‖w-(t : ℂ)‖) :
    ‖EmpiricalRapidity.cauchyTransform μ z-EmpiricalRapidity.cauchyTransform μ w‖ ≤
      (μ univ).toReal * δ⁻¹ ^ 2 * ‖z-w‖ := by
  rw [EmpiricalRapidity.cauchyTransform,EmpiricalRapidity.cauchyTransform,
    ← integral_sub (integrable_kernel μ hδ hz) (integrable_kernel μ hδ hw)]
  have hb : ∀ᵐ (t : ℝ) ∂μ,
      ‖(z-(t : ℂ))⁻¹-(w-(t : ℂ))⁻¹‖ ≤ δ⁻¹ ^ 2 * ‖z-w‖ := by
    filter_upwards [hz,hw] with t hzt hwt
    have hzne : z-(t : ℂ) ≠ 0 := norm_pos_iff.mp (hδ.trans_le hzt)
    have hwne : w-(t : ℂ) ≠ 0 := norm_pos_iff.mp (hδ.trans_le hwt)
    have he : (z-(t : ℂ))⁻¹-(w-(t : ℂ))⁻¹ =
        (z-(t : ℂ))⁻¹ * (w-(t : ℂ))⁻¹ * (w-z) := by
      field_simp
      ring
    rw [he,norm_mul,norm_mul,norm_inv,norm_inv,norm_sub_rev w z]
    have hm : ‖z-(t : ℂ)‖⁻¹ * ‖w-(t : ℂ)‖⁻¹ ≤ δ⁻¹ * δ⁻¹ :=
      mul_le_mul (inv_anti₀ hδ hzt) (inv_anti₀ hδ hwt)
        (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr hδ.le)
    exact mul_le_mul_of_nonneg_right (by simpa only [pow_two] using hm) (norm_nonneg _)

  calc
    _ ≤ ∫ t, ‖(z-(t : ℂ))⁻¹-(w-(t : ℂ))⁻¹‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : ℝ, δ⁻¹ ^ 2 * ‖z-w‖ ∂μ := integral_mono_ae
      ((integrable_kernel μ hδ hz).sub (integrable_kernel μ hδ hw)).norm (integrable_const _) hb
    _ = _ := by simp [measureReal_def,smul_eq_mul]; ring

/-- A real-centered disk cuts the real axis in precisely its diameter. -/
theorem diameter_set (a b : ℝ) :
    {t : ℝ | ‖(t : ℂ)-(((a+b)/2 : ℝ) : ℂ)‖ < (b-a)/2} = Ioo a b := by
  ext t
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, mem_ofPred, mem_Ioo, abs_lt]
  constructor
  · rintro ⟨h1,h2⟩; constructor <;> linarith
  · rintro ⟨h1,h2⟩; constructor <;> linarith

/-- Two mass-free endpoint neighborhoods separate the circle from the support. -/
theorem radial_gap {μ : Measure ℝ} {a b δa δb : ℝ}
    (_ha : 0 < δa) (_hb : 0 < δb)
    (hza : μ (Metric.ball a δa) = 0) (hzb : μ (Metric.ball b δb) = 0) :
    ∀ᵐ (t : ℝ) ∂μ, min δa δb ≤
      |‖(t : ℂ)-(((a+b)/2 : ℝ) : ℂ)‖-(b-a)/2| := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hza,
    measure_eq_zero_iff_ae_notMem.mp hzb] with t hta htb
  have hta' : δa ≤ |t-a| := by simpa [Metric.mem_ball, Real.dist_eq, not_lt] using hta
  have htb' : δb ≤ |t-b| := by simpa [Metric.mem_ball, Real.dist_eq, not_lt] using htb
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  by_cases ht : t ≤ (a+b)/2
  · rw [abs_of_nonpos (by linarith : t-(a+b)/2 ≤ 0)]
    have he : - (t-(a+b)/2)-(b-a)/2 = -(t-a) := by ring
    rw [he, abs_neg]
    exact (min_le_left _ _).trans hta'
  · rw [abs_of_nonneg (by linarith : 0 ≤ t-(a+b)/2)]
    have he : t-(a+b)/2-(b-a)/2 = t-b := by ring
    rw [he]
    exact (min_le_right _ _).trans htb'

variable {L : ℝ} [Fact (0 < L)]

/-- One uniform support gap works for the whole fixed circle and all nearby
physical inputs. This is a support statement, with no analyticity premise. -/
theorem common_contour_gap (p : DEF014Phase.Param L) (n : ℤ) :
    let a := DEF014Phase.separator p (n-1)
    let b := DEF014Phase.separator p n
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ q : DEF014Phase.Param L in 𝓝 p,
      ∀ᵐ (t : ℝ) ∂(DEF014Phase.measure q), δ ≤
        |‖(t : ℂ)-(((a+b)/2 : ℝ) : ℂ)‖-(b-a)/2| := by
  dsimp only
  let a := DEF014Phase.separator p (n-1)
  let b := DEF014Phase.separator p n
  obtain ⟨δa,hδa,hba⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band (n-1))
  obtain ⟨δb,hδb,hbb⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band n)
  refine ⟨min δa δb,lt_min hδa hδb,?_⟩
  filter_upwards [hba,hbb] with q hqa hqb
  have hza : DEF014Phase.measure q (Metric.ball a δa) = 0 :=
    DEF014Phase.measure_band_zero q Metric.isOpen_ball.measurableSet (fun t ht =>
      (hqa t (by simpa [a, DEF014Phase.separator, Metric.mem_ball, Real.dist_eq] using ht)).le)
  have hzb : DEF014Phase.measure q (Metric.ball b δb) = 0 :=
    DEF014Phase.measure_band_zero q Metric.isOpen_ball.measurableSet (fun t ht =>
      (hqb t (by simpa [b, DEF014Phase.separator, Metric.mem_ball, Real.dist_eq] using ht)).le)
  exact radial_gap hδa hδb hza hzb

/-- The literal fixed-contour identity for the actual physical mass, on a
neighborhood of every physical input. The circle crosses the real axis at
its two base separators, and works also for vacuum and collapsed masses. -/
theorem eventually_physical_mass_contour (p : DEF014Phase.Param L) (n : ℤ) :
    let a := DEF014Phase.separator p (n-1)
    let b := DEF014Phase.separator p n
    ∀ᶠ q : DEF014Phase.Param L in 𝓝 p,
      (((DEF014Continuity.masses q).1 n : ℝ) : ℂ) =
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          (∮ z in C((((a+b)/2 : ℝ) : ℂ),(b-a)/2),
            EmpiricalRapidity.cauchyTransform (DEF014Phase.measure q) z) := by
  dsimp only
  let a := DEF014Phase.separator p (n-1)
  let b := DEF014Phase.separator p n
  have hab : a < b := (DEF014Phase.facts p).phase.separator_strictMono (by omega)
  obtain ⟨δa,hδa,hba⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band (n-1))
  obtain ⟨δb,hδb,hbb⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band n)
  filter_upwards [hba,hbb,DEF014Continuity.eventually_mass_fixed_interval p n] with q hqa hqb hmass
  have hza : DEF014Phase.measure q (Metric.ball a δa) = 0 :=
    DEF014Phase.measure_band_zero q Metric.isOpen_ball.measurableSet (fun t ht =>
      (hqa t (by simpa [a, DEF014Phase.separator, Metric.mem_ball, Real.dist_eq] using ht)).le)
  have hzb : DEF014Phase.measure q (Metric.ball b δb) = 0 :=
    DEF014Phase.measure_band_zero q Metric.isOpen_ball.measurableSet (fun t ht =>
      (hqb t (by simpa [b, DEF014Phase.separator, Metric.mem_ball, Real.dist_eq] using ht)).le)
  have h := normalized_integral_cauchy (DEF014Phase.measure q) ((a+b)/2)
    (by linarith : 0 < (b-a)/2) (lt_min hδa hδb) (radial_gap hδa hδb hza hzb)
  rw [diameter_set] at h
  exact (congrArg (fun x : ℝ => (x : ℂ)) hmass).trans h.symm

end QuantumNLS.DEF014Contour

#print axioms QuantumNLS.DEF014Contour.integral_kernel_outside
#print axioms QuantumNLS.DEF014Contour.integral_cauchy
#print axioms QuantumNLS.DEF014Contour.normalized_integral_cauchy
#print axioms QuantumNLS.DEF014Contour.radial_gap
#print axioms QuantumNLS.DEF014Contour.eventually_physical_mass_contour

end



/-! Integration of a common analytic germ in the uniform norm. The uniform
hypothesis is explicit; pointwise analyticity is not substituted for it. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.DEF014AnalyticIntegration

abbrev UnitInterval := Icc (0 : ℝ) 1

def extend (f : C(UnitInterval, ℂ)) (t : ℝ) : ℂ :=
  f (projIcc 0 1 (by norm_num) t)

theorem continuous_extend (f : C(UnitInterval, ℂ)) : Continuous (extend f) :=
  f.continuous.comp continuous_projIcc

theorem integrable_extend (f : C(UnitInterval, ℂ)) :
    IntervalIntegrable (extend f) volume 0 1 :=
  (continuous_extend f).intervalIntegrable 0 1

/-- Integration on the unit interval is a bounded real-linear functional. -/
def integrateCLM : C(UnitInterval, ℂ) →L[ℝ] ℂ :=
  ({ toFun := fun f => ∫ t in (0 : ℝ)..1, extend f t
     map_add' := by
       intro f g
       exact intervalIntegral.integral_add (integrable_extend f) (integrable_extend g)
     map_smul' := by
       intro c f
       exact intervalIntegral.integral_smul c (extend f)
    } : C(UnitInterval, ℂ) →ₗ[ℝ] ℂ).mkContinuous 1 (by
      intro f
      change ‖∫ t in (0 : ℝ)..1, extend f t‖ ≤ 1 * ‖f‖
      simpa [extend] using intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := ‖f‖)
        (fun t _ => ContinuousMap.norm_coe_le_norm f _))

/-- A common norm-convergent analytic series can be integrated termwise by
applying a bounded linear functional. No separate coefficient domination
assumption is needed once the uniform-norm series has been proved. -/
theorem hasFPowerSeriesAt_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → C(UnitInterval, ℂ)} {p : FormalMultilinearSeries ℝ E C(UnitInterval, ℂ)}
    {u : E} (hF : HasFPowerSeriesAt F p u) :
    HasFPowerSeriesAt (fun v => ∫ t in (0 : ℝ)..1, extend (F v) t)
      (integrateCLM.compFormalMultilinearSeries p) u := by
  obtain ⟨r,hr⟩ := hF
  exact ⟨r,integrateCLM.comp_hasFPowerSeriesOnBall hr⟩

/-- Uniform real analyticity passes through parameter integration. -/
theorem analyticAt_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → C(UnitInterval, ℂ)} {u : E}
    (hF : AnalyticAt ℝ F u) :
    AnalyticAt ℝ (fun v => ∫ t in (0 : ℝ)..1, extend (F v) t) u :=
  (integrateCLM.analyticAt (F u)).comp hF

/-- Analytic moving endpoints multiply the analytic reparameterized unit
integral. F is the actual integrand pulled back along the moving segment. -/
theorem analyticAt_moving_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℂ} {F : E → C(UnitInterval, ℂ)} {u : E}
    (ha : AnalyticAt ℝ a u) (hb : AnalyticAt ℝ b u)
    (hF : AnalyticAt ℝ F u) :
    AnalyticAt ℝ (fun v => (b v-a v) *
      ∫ t in (0 : ℝ)..1, extend (F v) t) u :=
  (hb.sub ha).mul (analyticAt_integral hF)

/-- A literal moving-endpoint integral, with the reparameterized integrand
identified pointwise. The endpoints may coincide or reverse order. -/
theorem analyticAt_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {f : E → ℝ → ℂ} {F : E → C(UnitInterval, ℂ)} {u : E}
    (ha : AnalyticAt ℝ a u) (hb : AnalyticAt ℝ b u)
    (hF : AnalyticAt ℝ F u)
    (heq : ∀ᶠ v in 𝓝 u, ∀ t : UnitInterval,
      F v t = f v ((b v-a v)*t.1+a v)) :
    AnalyticAt ℝ (fun v => ∫ t in a v..b v, f v t) u := by
  have haC := (Complex.ofRealCLM.analyticAt (a u)).comp ha
  have hbC := (Complex.ofRealCLM.analyticAt (b u)).comp hb
  apply (analyticAt_moving_segment haC hbC hF).congr
  filter_upwards [heq] with v hv
  have he : (∫ t in (0 : ℝ)..1, extend (F v) t) =
      ∫ t in (0 : ℝ)..1, f v ((b v-a v)*t+a v) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    change F v (projIcc 0 1 (by norm_num) t) = _
    rw [projIcc_of_mem (by norm_num) ht]
    exact hv ⟨t,ht⟩
  rw [he]
  simpa only [Function.comp_def,Complex.ofRealCLM_apply, ← Complex.ofReal_sub, ← Complex.real_smul,
    mul_zero, zero_add, mul_one, sub_add_cancel] using
    intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1) (f v) (b v-a v) (a v)

end QuantumNLS.DEF014AnalyticIntegration

#print axioms QuantumNLS.DEF014AnalyticIntegration.integrateCLM
#print axioms QuantumNLS.DEF014AnalyticIntegration.hasFPowerSeriesAt_integral
#print axioms QuantumNLS.DEF014AnalyticIntegration.analyticAt_integral
#print axioms QuantumNLS.DEF014AnalyticIntegration.analyticAt_moving_segment
#print axioms QuantumNLS.DEF014AnalyticIntegration.analyticAt_intervalIntegral

end



/-! Uniform-norm analyticity of the physical discriminant on every compact
spectral parameter space. This is a Banach-valued conclusion. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.DEF014UniformDiscriminant
open SpatialTransfer L2SpatialTransfer DEF014VolterraOperator
open PhysicalTensor (L2T)
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : UniformSpace Mat2 :=
  (inferInstance : NormedAddCommGroup Mat2).toUniformSpace
local instance : TopologicalSpace Mat2 :=
  (inferInstance : UniformSpace Mat2).toTopologicalSpace
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {K : Type*} [PseudoMetricSpace K] [CompactSpace K]
variable {L : ℝ} [Fact (0 < L)]
local instance : NormedRing C(K,Mat2) := ContinuousMap.instNormedRing
local instance : ENormedAddMonoid C(K,Mat2) := NormedAddGroup.toENormedAddMonoid
local instance : NormedAlgebra ℝ C(K,Mat2) := { ContinuousMap.normedSpace, ContinuousMap.algebra with }
local instance : CompleteSpace C(K,Mat2) := ContinuousMap.instCompleteSpaceOfCompactlyCoherentSpace

def spectral (κ : ℝ) (Z : C(K,ℂ)) : C(K,Mat2) where
  toFun k := balCoef κ (fun _ => 0) (Z k) 0
  continuous_toFun := by
    dsimp [balCoef, coef]
    fun_prop

def contourCoef (κ : ℝ) (Z : C(K,ℂ)) (p : L2T L × ℝ) (t : ℝ) : C(K,Mat2) :=
  ContinuousMap.const K (balCoef κ (L2SpatialTransfer.profile p.1) 0 t) +
    p.2 • spectral κ Z

theorem contourCoef_apply (κ : ℝ) (Z : C(K,ℂ)) (p : L2T L × ℝ) (t : ℝ) (k : K) :
    contourCoef κ Z p t k = balCoef κ (L2SpatialTransfer.profile p.1) (p.2 • Z k) t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [contourCoef, spectral, balCoef, coef, Complex.real_smul] <;> ring

theorem integrable_coef (κ : ℝ) (Z : C(K,ℂ)) (p : L2T L × ℝ) :
    IntervalIntegrable (contourCoef κ Z p) volume 0 L := by
  have hi : IntervalIntegrable (balCoef κ (L2SpatialTransfer.profile p.1) 0) volume 0 L :=
    intervalIntegrable_coef (intervalIntegrable_profile p.1) _ _ _
  let hc := (ContinuousLinearMap.const ℝ K : Mat2 →L[ℝ] C(K,Mat2))
  have hh : IntervalIntegrable
      (fun t => hc (balCoef κ (L2SpatialTransfer.profile p.1) 0 t)) volume 0 L :=
    ⟨ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (𝕜' := ℝ) hc hi.1,
      ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (𝕜' := ℝ) hc hi.2⟩
  change IntervalIntegrable (fun t => hc (balCoef κ (L2SpatialTransfer.profile p.1) 0 t) + p.2 • spectral κ Z) volume 0 L
  exact hh.add intervalIntegrable_const

def family (κ : ℝ) (Z : C(K,ℂ)) : Family (L2T L × ℝ) C(K,Mat2) L where
  coef := contourCoef κ Z
  integrable := integrable_coef κ Z
  add_ae p q := by
    filter_upwards [DEF014DiscriminantAnalytic.profile_add p.1 q.1] with t ht
    apply ContinuousMap.ext
    intro k
    change contourCoef κ Z (p+q) t k = contourCoef κ Z p t k + contourCoef κ Z q t k
    simp only [contourCoef_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [balCoef,coef,ht,Complex.real_smul,mul_add] <;> ring
  smul_ae c p := by
    filter_upwards [DEF014DiscriminantAnalytic.profile_smul c p.1] with t ht
    apply ContinuousMap.ext
    intro k
    change contourCoef κ Z (c • p) t k = c • contourCoef κ Z p t k
    simp only [contourCoef_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [balCoef,coef,ht,Complex.real_smul] <;> ring
  bound := (DEF014DiscriminantAnalytic.physicalFamily (L := L) κ).bound + L * ‖spectral κ Z‖
  bound_nonneg := by
    have hL : 0 < L := Fact.out
    exact add_nonneg (DEF014DiscriminantAnalytic.physicalFamily κ).bound_nonneg (by positivity)
  norm_integral_le p := by
    have hL : 0 < L := Fact.out
    have hi : IntervalIntegrable (balCoef κ (L2SpatialTransfer.profile p.1) 0) volume 0 L :=
      intervalIntegrable_coef (intervalIntegrable_profile p.1) _ _ _
    have hn : (∫ t in (0 : ℝ)..L, ‖contourCoef κ Z p t‖) ≤
        (∫ t in (0 : ℝ)..L, ‖balCoef κ (L2SpatialTransfer.profile p.1) 0 t‖) +
          L * (‖p.2‖ * ‖spectral κ Z‖) := by
      calc
        _ ≤ ∫ t in (0 : ℝ)..L,
            ‖balCoef κ (L2SpatialTransfer.profile p.1) 0 t‖ + ‖p.2‖ * ‖spectral κ Z‖ := by
          apply intervalIntegral.integral_mono_on hL.le (integrable_coef κ Z p).norm
            (hi.norm.add intervalIntegrable_const)
          intro t _
          exact (norm_add_le _ _).trans (add_le_add ((ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun _ => le_rfl)) (by rw [norm_smul]))
        _ = _ := by rw [intervalIntegral.integral_add hi.norm intervalIntegrable_const,
          intervalIntegral.integral_const]; simp [smul_eq_mul]
    have hp := (DEF014DiscriminantAnalytic.physicalFamily (L := L) κ).norm_integral_le (p.1,0)
    have hp' : (∫ t in (0 : ℝ)..L, ‖balCoef κ (L2SpatialTransfer.profile p.1) 0 t‖) ≤
        (DEF014DiscriminantAnalytic.physicalFamily (L := L) κ).bound * ‖p.1‖ := by
      simpa only [DEF014DiscriminantAnalytic.physicalFamily, Prod.norm_def, norm_zero,
        max_eq_left (norm_nonneg p.1)] using hp
    refine hn.trans (le_trans (add_le_add hp' le_rfl) ?_)
    have h1 := norm_fst_le p
    have h2 := norm_snd_le p
    have hB := (DEF014DiscriminantAnalytic.physicalFamily (L := L) κ).bound_nonneg
    nlinarith [mul_le_mul_of_nonneg_left h1 hB,
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hL.le (norm_nonneg (spectral κ Z)))]

/-- Evaluation commutes with the actual Dyson iterates, hence with the transfer. -/
theorem eval_dyson (κ : ℝ) (Z : C(K,ℂ)) (p : L2T L × ℝ) (k : K) (n : ℕ)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) L) :
    LinearFundamental.dyson (contourCoef κ Z p) n x k =
      LinearFundamental.dyson (balCoef κ (L2SpatialTransfer.profile p.1) (p.2 • Z k)) n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [LinearFundamental.dyson,LinearFundamental.dyson]
    let ev := ContinuousMap.evalCLM ℝ k (M := Mat2)
    have hi := (L1SpatialTransfer.integrable_dyson_product (integrable_coef κ Z p) n).mono_set
      (show uIcc (0 : ℝ) x ⊆ uIcc 0 L by
        rw [uIcc_of_le hx.1,uIcc_of_le (Fact.out : 0 < L).le]
        exact Icc_subset_Icc_right hx.2)
    change ev (∫ t in (0 : ℝ)..x, contourCoef κ Z p t * LinearFundamental.dyson (contourCoef κ Z p) n t) = _
    rw [← ev.intervalIntegral_comp_comm hi]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    change contourCoef κ Z p t k * LinearFundamental.dyson (contourCoef κ Z p) n t k = _
    rw [contourCoef_apply,ih t ⟨ht.1,ht.2.trans hx.2⟩]

theorem eval_transfer (κ : ℝ) (Z : C(K,ℂ)) (p : L2T L × ℝ) (k : K) :
    L1SpatialTransfer.transfer (contourCoef κ Z p) L k =
      L1SpatialTransfer.transfer (balCoef κ (L2SpatialTransfer.profile p.1) (p.2 • Z k)) L := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hb := L1SpatialTransfer.uniform_dyson_bound hL (integrable_coef κ Z p)
  have hs := Summable.of_norm_bounded hb.1 (fun n => hb.2 n L ⟨hL,le_rfl⟩)
  change (∑' n, LinearFundamental.dyson (contourCoef κ Z p) n L) k = _
  rw [← ContinuousMap.tsum_apply hs k]
  simp_rw [eval_dyson κ Z p k _ L ⟨hL,le_rfl⟩]
  rfl

/-- Every continuous compact spectral path has a uniformly analytic physical
trace. The theorem is at arbitrary L2 base points and does not omit vacuum. -/
theorem analyticAt_discriminant_contour (κ : ℝ) (Z : C(K,ℂ)) (u : L2T L) :
    ∃ D : L2T L → C(K,ℂ), AnalyticAt ℝ D u ∧
      ∀ v k, D v k = L2SpatialTransfer.discriminant κ v (Z k) := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  let tr : Mat2 →L[ℝ] ℂ := DEF014DiscriminantAnalytic.entryCLM 0 0 +
    DEF014DiscriminantAnalytic.entryCLM 1 1
  let trK := ContinuousLinearMap.compLeftContinuous ℝ K tr
  let path := DEF014VolterraAnalytic.transferPath hL (family κ Z)
  let evL : Path L C(K,Mat2) →L[ℝ] C(K,Mat2) :=
    ContinuousMap.evalCLM ℝ (⟨L,hL,le_rfl⟩ : Icc (0 : ℝ) L)
  let D : L2T L → C(K,ℂ) := fun v =>
    trK (evL (path (v,1)))
  refine ⟨D,?_,?_⟩
  · have ha : AnalyticAt ℝ (fun v : L2T L => path (v,1)) u :=
      (DEF014VolterraAnalytic.analyticAt_transferPath hL (family κ Z) (u,1)).comp
        (f := fun v : L2T L => (v,(1 : ℝ))) (analyticAt_id.prod analyticAt_const)
    have he : AnalyticAt ℝ (fun v : L2T L => evL (path (v,1))) u :=
      (evL.analyticAt _).comp ha
    exact (trK.analyticAt _).comp he
  · intro v k
    change (L1SpatialTransfer.transfer (contourCoef κ Z (v,1)) L k) 0 0 +
      (L1SpatialTransfer.transfer (contourCoef κ Z (v,1)) L k) 1 1 = _
    simp only [eval_transfer,one_smul,L2SpatialTransfer.discriminant,
      L2SpatialTransfer.spatialTransfer,Matrix.trace_fin_two]

end QuantumNLS.DEF014UniformDiscriminant

#print axioms QuantumNLS.DEF014UniformDiscriminant.contourCoef_apply
#print axioms QuantumNLS.DEF014UniformDiscriminant.integrable_coef
#print axioms QuantumNLS.DEF014UniformDiscriminant.family
#print axioms QuantumNLS.DEF014UniformDiscriminant.eval_dyson
#print axioms QuantumNLS.DEF014UniformDiscriminant.eval_transfer
#print axioms QuantumNLS.DEF014UniformDiscriminant.analyticAt_discriminant_contour

end



/-! Analytic selection of the cosine branch in the uniform norm on a compact
parameter space. This is an actual Banach inverse argument. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Topology
namespace QuantumNLS.DEF014UniformPhase
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def cosine (g : C(K,ℂ)) : C(K,ℂ) :=
  NormedSpace.exp (Complex.I • g) + NormedSpace.exp ((-Complex.I) • g)

theorem exp_apply (g : C(K,ℂ)) (k : K) :
    NormedSpace.exp g k = Complex.exp (g k) := by
  simpa only [← Complex.exp_eq_exp_ℂ,ContinuousMap.evalAlgHom_apply] using NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ k)
    ((ContinuousMap.evalCLM ℂ k : C(K,ℂ) →L[ℂ] ℂ).continuous) g

theorem cosine_apply (g : C(K,ℂ)) (k : K) :
    cosine g k = 2 * Complex.cos (g k) := by
  simp only [cosine, ContinuousMap.add_apply, exp_apply, ContinuousMap.smul_apply,
    smul_eq_mul, Complex.cos]
  have he1 : Complex.I * g k = g k * Complex.I := by ring
  have he2 : -Complex.I * g k = -(g k * Complex.I) := by ring
  rw [he1,he2]
  ring

def slope (g : C(K,ℂ)) : C(K,ℂ) :=
  Complex.I • (NormedSpace.exp (Complex.I • g) - NormedSpace.exp ((-Complex.I) • g))

theorem slope_apply (g : C(K,ℂ)) (k : K) :
    slope g k = -2 * Complex.sin (g k) := by
  simp only [slope, ContinuousMap.smul_apply, ContinuousMap.sub_apply, exp_apply,
    smul_eq_mul, Complex.sin]
  have he : -Complex.I * g k = -(g k * Complex.I) := by ring
  rw [he,mul_comm Complex.I (g k)]
  field_simp
  ring

theorem analyticAt_cosine (g : C(K,ℂ)) : AnalyticAt ℂ (cosine (K := K)) g := by
  exact ((NormedSpace.exp_analytic _).comp (analyticAt_id.const_smul (c := Complex.I))).add
    ((NormedSpace.exp_analytic _).comp (analyticAt_id.const_smul (c := -Complex.I)))

theorem hasFDerivAt_cosine (g : C(K,ℂ)) :
    HasFDerivAt (cosine (K := K))
      (slope g • (1 : C(K,ℂ) →L[ℂ] C(K,ℂ))) g := by
  have hpos := (hasFDerivAt_exp (𝕂 := ℂ) (x := Complex.I • g)).comp g
    ((hasFDerivAt_id g).const_smul Complex.I)
  have hneg := (hasFDerivAt_exp (𝕂 := ℂ) (x := (-Complex.I) • g)).comp g
    ((hasFDerivAt_id g).const_smul (-Complex.I))
  apply (hpos.add hneg).congr_fderiv
  ext h k
  change NormedSpace.exp (Complex.I • g) k * (Complex.I * h k) +
    NormedSpace.exp ((-Complex.I) • g) k * ((-Complex.I) * h k) =
      (Complex.I * (NormedSpace.exp (Complex.I • g) k -
        NormedSpace.exp ((-Complex.I) • g) k)) * h k
  ring

/-- Continuous selected cosine solutions inherit a common analytic germ in
C(K,C), once the right-hand side is analytic in that same Banach norm. -/
theorem analytic_selected_cosine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G D : E → C(K,ℂ)} {u : E}
    (hD : AnalyticAt ℝ D u) (hG : ContinuousAt G u)
    (he : ∀ᶠ v in 𝓝 u, ∀ k, 2 * Complex.cos (G v k) = D v k)
    (hs : ∀ k, Complex.sin (G u k) ≠ 0) : AnalyticAt ℝ G u := by
  have hd : IsUnit (slope (G u)) := (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    (fun k => by rw [slope_apply]; exact mul_ne_zero (by norm_num) (hs k))
  obtain ⟨d,hd⟩ := hd
  let A : C(K,ℂ) ≃L[ℂ] C(K,ℂ) :=
    (ContinuousLinearEquiv.unitsEquivAut C(K,ℂ) d).restrictScalars ℂ
  have hder : HasFDerivAt (cosine (K := K)) A.toContinuousLinearMap (G u) := by
    convert hasFDerivAt_cosine (G u) using 1
    ext h k
    change h k * (d : C(K,ℂ)) k = slope (G u) k * h k
    rw [hd]
    ring
  obtain ⟨inv,hinv,_,hleft,_⟩ := Ext025A.gp03_analytic_inverse A
    (analyticAt_cosine (G u)) hder
  have hDu : D u = cosine (G u) := by
    ext k
    rw [cosine_apply]
    exact (Filter.Eventually.self_of_nhds he k).symm
  have hc : AnalyticAt ℝ (fun v => inv (D v)) u := by
    rw [← hDu] at hinv
    exact hinv.restrictScalars.comp hD
  apply hc.congr
  filter_upwards [he,hG.tendsto.eventually hleft] with v hv hl
  have hh : D v = cosine (G v) := by
    ext k
    rw [cosine_apply]
    exact (hv k).symm
  rw [hh]
  exact hl

end QuantumNLS.DEF014UniformPhase

#print axioms QuantumNLS.DEF014UniformPhase.cosine_apply
#print axioms QuantumNLS.DEF014UniformPhase.slope_apply
#print axioms QuantumNLS.DEF014UniformPhase.analyticAt_cosine
#print axioms QuantumNLS.DEF014UniformPhase.hasFDerivAt_cosine
#print axioms QuantumNLS.DEF014UniformPhase.analytic_selected_cosine

end



/-! A common support distance upgrades pointwise field continuity to
continuity in the compact-path sup norm. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped NNReal
open Set Filter Topology MeasureTheory
namespace QuantumNLS.DEF014UniformCauchy

/-- Quantitative compact-path lifting of an actual finite-measure Cauchy
transform. Only support separation, mass control and pointwise continuity
are inputs; no uniform continuity or analyticity conclusion is assumed. -/
theorem exists_continuousAt_path
    {E K : Type*} [TopologicalSpace E] [PseudoMetricSpace K] [CompactSpace K]
    (μ : E → Measure ℝ) [∀ v, IsFiniteMeasure (μ v)]
    (Z : K → ℂ) {B : ℝ≥0} (hZ : LipschitzWith B Z) {u : E}
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hgap : ∀ᶠ v in 𝓝 u, ∀ᵐ (t : ℝ) ∂(μ v), ∀ k, δ ≤ ‖Z k-(t : ℂ)‖)
    (hmass : ∀ᶠ v in 𝓝 u, (μ v univ).toReal ≤ M)
    (hpoint : ∀ k, ContinuousAt (fun v => EmpiricalRapidity.cauchyTransform (μ v) (Z k)) u) :
    ∃ G : E → C(K,ℂ), ContinuousAt G u ∧
      ∀ᶠ v in 𝓝 u, ∀ k, G v k = EmpiricalRapidity.cauchyTransform (μ v) (Z k) := by
  classical
  let S : Set E := {v | (∀ᵐ (t : ℝ) ∂(μ v), ∀ k, δ ≤ ‖Z k-(t : ℂ)‖) ∧
    (μ v univ).toReal ≤ M}
  have hS : S ∈ 𝓝 u := hgap.and hmass
  have hu : u ∈ S := Filter.Eventually.self_of_nhds hS
  let C : ℝ≥0 := ⟨M * δ⁻¹ ^ 2 * B,by positivity⟩
  have hlip : ∀ v ∈ S, LipschitzWith C
      (fun k => EmpiricalRapidity.cauchyTransform (μ v) (Z k)) := by
    intro v hv
    apply LipschitzWith.of_dist_le_mul
    intro k l
    rw [dist_eq_norm]
    have h := DEF014Contour.norm_cauchy_sub_le (μ v) hδ
      (hv.1.mono fun t ht => ht k) (hv.1.mono fun t ht => ht l)
    have hZ' := hZ.dist_le_mul k l
    rw [dist_eq_norm] at hZ'
    exact h.trans (by
      change (μ v univ).toReal * δ⁻¹ ^ 2 * ‖Z k-Z l‖ ≤
        (M * δ⁻¹ ^ 2 * B) * dist k l
      calc
        _ ≤ M * δ⁻¹ ^ 2 * ‖Z k-Z l‖ := by gcongr; exact hv.2
        _ ≤ M * δ⁻¹ ^ 2 * (B * dist k l) := by gcongr
        _ = _ := by ring)
  let base : C(K,ℂ) := ⟨_,(hlip u hu).continuous⟩
  let G : E → C(K,ℂ) := fun v => if hv : v ∈ S then
    ⟨_,(hlip v hv).continuous⟩ else base
  have heq : ∀ᶠ v in 𝓝 u, ∀ k,
      G v k = EmpiricalRapidity.cauchyTransform (μ v) (Z k) := by
    filter_upwards [hS] with v hv k
    simp only [G,dite_eq_left hv,ContinuousMap.coe_mk]
  have hequ : ∀ k, G u k = EmpiricalRapidity.cauchyTransform (μ u) (Z k) :=
    Filter.Eventually.self_of_nhds heq
  have hGLip : ∀ v, LipschitzWith C (G v) := by
    intro v
    dsimp only [G]
    split_ifs with hv
    · exact hlip v hv
    · exact hlip u hu
  have hequi : Equicontinuous (fun v k => G v k) :=
    (LipschitzWith.uniformEquicontinuous (fun v k => G v k) C hGLip).equicontinuous
  have hp : Tendsto (fun v k => G v k) (𝓝 u) (𝓝 fun k => G u k) := by
    apply tendsto_pi_nhds.mpr
    intro k
    rw [hequ k]
    exact (hpoint k).tendsto.congr' (heq.mono fun v hv => (hv k).symm)
  have ht : TendstoUniformly (fun v k => G v k) (fun k => G u k) (𝓝 u) := by
    exact UniformFun.tendsto_iff_tendstoUniformly.mp
      ((hequi.tendsto_uniformFun_iff_pi (𝓝 u) (fun k => G u k)).mpr hp)
  refine ⟨G,?_,heq⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp ht) (ε/2) (by positivity)] with v hv
  rw [dist_eq_norm]
  have hn : ‖G v-G u‖ ≤ ε/2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro k
    simpa only [ContinuousMap.sub_apply,← dist_eq_norm,dist_comm] using (hv k).le
  exact hn.trans_lt (by linarith)

end QuantumNLS.DEF014UniformCauchy
end



/-! Identification of the uniformly analytic branch with the physical
Cauchy transform on compact upper paths with mass-free real crossings. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped NNReal
open Set Filter Topology MeasureTheory
namespace QuantumNLS.DEF014UpperAnalytic
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)

theorem selected_real_eq (u : L2T L) {x : ℝ}
    (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    DEF014PhaseAnalytic.selected hκ u (x : ℂ) =
      (DEF014Phase.phase (⟨κ,hκ⟩,u) x : ℂ) := by
  by_cases hu : u = 0
  · subst u
    simp [DEF014PhaseAnalytic.selected,SpatialTransfer.boundaryPhase,
      PhysicalQuantumMeasure.measure,EmpiricalRapidity.cauchyTransform,
      DEF014Phase.phase,PhysicalContinuousBoundary.boundary_zero]
  · rw [DEF014PhaseAnalytic.selected,← PhysicalContinuousBoundary.band_eq hκ hu hx]
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      rw [PhysicalContinuousBoundary.boundary_im]
      simp [RootDensity.hfun,not_lt.mpr hx.le]

theorem continuousAt_cauchy_band (u : L2T L) {x : ℝ}
    (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    ContinuousAt (fun v : L2T L =>
      EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ v) (x : ℂ)) u := by
  have hc : Continuous (fun v : L2T L => |(L2SpatialTransfer.discriminant κ v (x : ℂ)).re|) :=
    (Complex.continuous_re.comp ((DiscParamContinuity.continuous_discriminant_param (L := L) (x : ℂ)).comp
      ((continuous_const (y := κ)).prodMk continuous_id))).abs
  have hb : ∀ᶠ v : L2T L in 𝓝 u,
      |(L2SpatialTransfer.discriminant κ v (x : ℂ)).re| < 2 :=
    (isOpen_lt hc continuous_const).mem_nhds hx
  have hs : ContinuousAt (fun v : L2T L => DEF014PhaseAnalytic.selected hκ v (x : ℂ)) u := by
    have hh := Complex.continuous_ofReal.continuousAt.comp
      ((DEF014Phase.continuous_phase_at_band (⟨κ,hκ⟩,u) hx).comp
        (continuous_const.prodMk continuous_id).continuousAt)
    apply hh.congr_of_eventuallyEq
    filter_upwards [hb] with v hv
    exact selected_real_eq hκ v hv
  have hh : ContinuousAt (fun v : L2T L =>
      ((L : ℂ)*(x : ℂ)/2-DEF014PhaseAnalytic.selected hκ v (x : ℂ))/(κ : ℂ)) u :=
    (continuousAt_const.sub hs).div_const (κ : ℂ)
  convert hh using 1
  funext v
  dsimp [DEF014PhaseAnalytic.selected,SpatialTransfer.boundaryPhase]
  field_simp [Complex.ofReal_ne_zero.mpr hκ.ne']
  ring

/-- A uniformly analytic physical Cauchy germ on a compact upper path. The
hypotheses are explicit geometric support/band conditions, rather than any
analyticity or branch-identification conclusion. -/
theorem exists_analytic_cauchy_path
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K]
    (Z : C(K,ℂ)) {B : ℝ≥0} (hZ : LipschitzWith B Z) (u : L2T L)
    (hupper : ∀ k, 0 ≤ (Z k).im)
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hgap : ∀ᶠ v : L2T L in 𝓝 u,
      ∀ᵐ (t : ℝ) ∂(PhysicalQuantumMeasure.measure hκ v), ∀ k, δ ≤ ‖Z k-(t : ℂ)‖)
    (hmass : ∀ᶠ v : L2T L in 𝓝 u,
      (PhysicalQuantumMeasure.measure hκ v univ).toReal ≤ M)
    (hband : ∀ᶠ v : L2T L in 𝓝 u, ∀ k, (Z k).im = 0 →
      |(L2SpatialTransfer.discriminant κ v ((Z k).re : ℂ)).re| < 2) :
    ∃ H : L2T L → C(K,ℂ), AnalyticAt ℝ H u ∧
      ∀ᶠ v : L2T L in 𝓝 u, ∀ k,
        H v k = EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ v) (Z k) := by
  have hpoint : ∀ k, ContinuousAt (fun v : L2T L =>
      EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ v) (Z k)) u := by
    intro k
    by_cases hz : (Z k).im = 0
    · have he : Z k = ((Z k).re : ℂ) := by apply Complex.ext <;> simp [hz]
      rw [he]
      exact continuousAt_cauchy_band hκ u (Filter.Eventually.self_of_nhds hband k hz)
    · exact (DEF014PhaseAnalytic.analyticAt_cauchy_upper hκ u
        (lt_of_le_of_ne (hupper k) (Ne.symm hz))).continuousAt
  obtain ⟨C,hC,hCe⟩ := DEF014UniformCauchy.exists_continuousAt_path
    (fun v : L2T L => PhysicalQuantumMeasure.measure hκ v) Z hZ hδ hM hgap hmass hpoint
  obtain ⟨D,hD,hDe⟩ := DEF014UniformDiscriminant.analyticAt_discriminant_contour κ Z u
  let lin : C(K,ℂ) := ((L : ℂ)/2) • Z
  let G : L2T L → C(K,ℂ) := fun v => lin-(κ : ℂ) • C v
  have hG : ContinuousAt G u := continuousAt_const.sub (hC.const_smul (κ : ℂ))
  have hGe : ∀ᶠ v : L2T L in 𝓝 u, ∀ k,
      G v k = DEF014PhaseAnalytic.selected hκ v (Z k) := by
    filter_upwards [hCe] with v hv k
    change ((L : ℂ)/2) * Z k-(κ : ℂ)*C v k = _
    rw [hv k]
    dsimp [DEF014PhaseAnalytic.selected,SpatialTransfer.boundaryPhase]
    ring
  have he : ∀ᶠ v : L2T L in 𝓝 u, ∀ k, 2 * Complex.cos (G v k) = D v k := by
    filter_upwards [hGe,hband] with v hv hb k
    rw [hv k,hDe v k]
    by_cases hz : (Z k).im = 0
    · have hez : Z k = ((Z k).re : ℂ) := by apply Complex.ext <;> simp [hz]
      rw [hez,selected_real_eq hκ v (hb k hz)]
      have hcos := PhysicalContinuousBoundary.boundary_cosine hκ v (Z k).re
      have hreal : PhysicalContinuousBoundary.boundary hκ v (Z k).re =
          (DEF014Phase.phase (⟨κ,hκ⟩,v) (Z k).re : ℂ) := by
        apply Complex.ext
        · rfl
        · simp only [Complex.ofReal_im]
          rw [PhysicalContinuousBoundary.boundary_im]
          simp [RootDensity.hfun,not_lt.mpr (hb k hz).le]
      rwa [hreal] at hcos
    · exact PhysicalUnconditionalTrace.upper_cosine hκ v
        (lt_of_le_of_ne (hupper k) (Ne.symm hz))
  have hs : ∀ k, Complex.sin (G u k) ≠ 0 := by
    intro k hzero
    have hg := Filter.Eventually.self_of_nhds hGe k
    rw [hg] at hzero
    by_cases hz : (Z k).im = 0
    · have hc := congrArg Complex.re (Filter.Eventually.self_of_nhds he k)
      have hb := Filter.Eventually.self_of_nhds hband k hz
      have hez : Z k = ((Z k).re : ℂ) := by apply Complex.ext <;> simp [hz]
      rw [hDe,hez] at hc
      rw [← hg] at hzero
      rcases Complex.sin_eq_zero_iff_cos_eq.mp hzero with hh | hh
      all_goals
        rw [hh] at hc
        norm_num at hc
        rw [← hc] at hb
        norm_num at hb
    · have hp := PhysicalQuantumMeasure.im_phase_pos hκ u
        (lt_of_le_of_ne (hupper k) (Ne.symm hz))
      obtain ⟨m,hm⟩ := Complex.sin_eq_zero_iff.mp hzero
      have hh := congrArg Complex.im hm
      simp at hh
      change 0 < (DEF014PhaseAnalytic.selected hκ u (Z k)).im at hp
      linarith
  have ha : AnalyticAt ℝ G u := DEF014UniformPhase.analytic_selected_cosine hD hG he hs
  let H : L2T L → C(K,ℂ) := fun v => ((κ : ℂ)⁻¹) • (lin-G v)
  refine ⟨H,(analyticAt_const.sub ha).const_smul (c := (κ : ℂ)⁻¹),?_⟩
  filter_upwards [hCe] with v hv k
  change (κ : ℂ)⁻¹ * (lin k-(lin k-(κ : ℂ)*C v k)) = _
  rw [sub_sub_cancel,inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr hκ.ne')]
  exact hv k

end QuantumNLS.DEF014UpperAnalytic
end



/-! Real-measure reflection reduces the full Cauchy contour to its upper arc. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Topology MeasureTheory Complex ComplexConjugate
namespace QuantumNLS.DEF014ContourReflection

theorem cauchy_conj (μ : Measure ℝ) (z : ℂ) :
    EmpiricalRapidity.cauchyTransform μ (conj z) =
      conj (EmpiricalRapidity.cauchyTransform μ z) := by
  simp only [EmpiricalRapidity.cauchyTransform,← integral_conj]
  congr 1
  funext t
  simp

theorem circle_support_distance (c : ℝ) {R δ t : ℝ} (hR : 0 < R)
    (ht : δ ≤ |‖(t : ℂ)-(c : ℂ)‖-R|) (θ : ℝ) :
    δ ≤ ‖circleMap (c : ℂ) R θ-(t : ℂ)‖ := by
  have h := abs_norm_sub_norm_le ((t : ℂ)-(c : ℂ)) (circleMap (c : ℂ) R θ-(c : ℂ))
  have hc : ‖circleMap (c : ℂ) R θ-(c : ℂ)‖ = R := by simp [abs_of_pos hR]
  rw [hc] at h
  have he : (t : ℂ)-(c : ℂ)-(circleMap (c : ℂ) R θ-(c : ℂ)) =
      -(circleMap (c : ℂ) R θ-(t : ℂ)) := by ring
  rw [he,norm_neg] at h
  exact ht.trans h

theorem continuous_cauchy_circle (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℝ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ᵐ (t : ℝ) ∂μ, δ ≤ |‖(t : ℂ)-(c : ℂ)‖-R|) :
    Continuous (fun θ => EmpiricalRapidity.cauchyTransform μ (circleMap (c : ℂ) R θ)) := by
  apply LipschitzWith.continuous (K := Real.toNNReal ((μ univ).toReal * δ⁻¹ ^ 2 * |R|))
  apply LipschitzWith.of_dist_le'
  intro θ φ
  rw [dist_eq_norm]
  have h := DEF014Contour.norm_cauchy_sub_le μ hδ
    (hgap.mono fun t ht => circle_support_distance c hR ht θ)
    (hgap.mono fun t ht => circle_support_distance c hR ht φ)
  have hz := (lipschitzWith_circleMap (c : ℂ) R).dist_le_mul θ φ
  rw [dist_eq_norm,Real.coe_nnabs] at hz
  exact h.trans (by
    change (μ univ).toReal * δ⁻¹ ^ 2 * ‖circleMap (c : ℂ) R θ-circleMap (c : ℂ) R φ‖ ≤ _
    calc
      _ ≤ (μ univ).toReal * δ⁻¹ ^ 2 * (|R| * dist θ φ) := by gcongr
      _ = _ := by ring)

def arcIntegrand (μ : Measure ℝ) (c R : ℝ) (θ : ℝ) : ℂ :=
  deriv (circleMap (c : ℂ) R) θ * EmpiricalRapidity.cauchyTransform μ (circleMap (c : ℂ) R θ)

theorem arcIntegrand_neg (μ : Measure ℝ) (c R θ : ℝ) :
    arcIntegrand μ c R (-θ) = -conj (arcIntegrand μ c R θ) := by
  have hz : circleMap (c : ℂ) R (-θ) = conj (circleMap (c : ℂ) R θ) := by
    simpa using (conj_circleMap (c : ℂ) R θ).symm
  have h0 : circleMap 0 R (-θ) = conj (circleMap 0 R θ) :=
    (conj_circleMap_zero R θ).symm
  simp only [arcIntegrand,deriv_circleMap,hz,h0,cauchy_conj,map_mul,Complex.conj_I]
  ring

theorem periodic_arcIntegrand (μ : Measure ℝ) (c R : ℝ) :
    Function.Periodic (arcIntegrand μ c R) (2 * Real.pi) := by
  intro θ
  simp only [arcIntegrand,deriv_circleMap,periodic_circleMap _ _ θ]

theorem integral_eq_upper_sub_conj (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℝ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ᵐ (t : ℝ) ∂μ, δ ≤ |‖(t : ℂ)-(c : ℂ)‖-R|) :
    (∮ z in C((c : ℂ),R), EmpiricalRapidity.cauchyTransform μ z) =
      (∫ θ in (0 : ℝ)..Real.pi,arcIntegrand μ c R θ) -
        conj (∫ θ in (0 : ℝ)..Real.pi,arcIntegrand μ c R θ) := by
  have hc : Continuous (arcIntegrand μ c R) := by
    change Continuous (fun θ => deriv (circleMap (c : ℂ) R) θ *
      EmpiricalRapidity.cauchyTransform μ (circleMap (c : ℂ) R θ))
    have hd : Continuous (fun θ => deriv (circleMap (c : ℂ) R) θ) := by
      simp only [deriv_circleMap]; fun_prop
    exact hd.mul (continuous_cauchy_circle μ c hR hδ hgap)
  have hp := (periodic_arcIntegrand μ c R).intervalIntegral_add_eq 0 (-Real.pi)
  simp only [zero_add] at hp
  have hend : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hend] at hp
  change (∫ θ in (0 : ℝ)..2 * Real.pi,arcIntegrand μ c R θ) = _
  rw [hp,← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-Real.pi) 0) (hc.intervalIntegrable 0 Real.pi)]
  have hn : (∫ θ in -Real.pi..0,arcIntegrand μ c R θ) =
      -conj (∫ θ in (0 : ℝ)..Real.pi,arcIntegrand μ c R θ) := by
    rw [← show -(0 : ℝ) = 0 by simp]
    rw [← intervalIntegral.integral_comp_neg]
    simp_rw [arcIntegrand_neg]
    rw [intervalIntegral.integral_neg,intervalIntegral.intervalIntegral_conj]
    simp only [neg_zero]
  rw [hn]
  ring

/-- The real normalization of the reflected upper arc. -/
theorem normalized_sub_conj (w : ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * (w-conj w) = ((w.im/Real.pi : ℝ) : ℂ) := by
  have he : w-conj w = (2*(w.im : ℂ))*I := by
    apply Complex.ext <;> simp [two_mul]
  have hp : (2 * (Real.pi : ℂ) * I)⁻¹ * (2*I) = (Real.pi : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [he]
  calc
    _ = ((2 * (Real.pi : ℂ) * I)⁻¹ * (2*I)) * (w.im : ℂ) := by ring
    _ = _ := by rw [hp]; push_cast; ring

end QuantumNLS.DEF014ContourReflection
end



/-! Individual real analyticity of the actual canonical indexed masses. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open scoped NNReal
open Set Filter Topology MeasureTheory Complex
namespace QuantumNLS.DEF014MassAnalytic
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)

abbrev UpperInterval := Icc (0 : ℝ) Real.pi

def upperPath (c R : ℝ) : C(UpperInterval,ℂ) where
  toFun θ := circleMap (c : ℂ) R θ.1
  continuous_toFun := (continuous_circleMap _ _).comp continuous_subtype_val

theorem analyticAt_physical_coordinate (n : ℤ) (u : L2T L) :
    AnalyticAt ℝ (fun v : L2T L =>
      ((PhysicalSourceFinal.sourceFacts hκ v).masses).1 n) u := by
  let p : DEF014Phase.Param L := (⟨κ,hκ⟩,u)
  let j : L2T L → DEF014Phase.Param L := fun v => (⟨κ,hκ⟩,v)
  have hj : Continuous j := continuous_const.prodMk continuous_id
  let a := DEF014Phase.separator p (n-1)
  let b := DEF014Phase.separator p n
  let c := (a+b)/2
  let R := (b-a)/2
  have hab : a < b := (DEF014Phase.facts p).phase.separator_strictMono (by omega)
  have hR : 0 < R := by dsimp [R]; linarith
  let Z := upperPath c R
  have hZ : LipschitzWith (Real.nnabs R) Z := by
    apply LipschitzWith.of_dist_le_mul
    intro θ φ
    change dist (circleMap (c : ℂ) R θ.1) (circleMap (c : ℂ) R φ.1) ≤
      (Real.nnabs R : ℝ) * dist θ.1 φ.1
    exact (lipschitzWith_circleMap (c : ℂ) R).dist_le_mul θ.1 φ.1
  have hupper : ∀ θ, 0 ≤ (Z θ).im := by
    intro θ
    change 0 ≤ (circleMap (c : ℂ) R θ.1).im
    simpa [circleMap,Complex.exp_mul_I,Complex.mul_im,Complex.sin_ofReal_re] using
      mul_nonneg hR.le (Real.sin_nonneg_of_mem_Icc θ.2)
  have hreal : ∀ θ : UpperInterval, (Z θ).im = 0 → (Z θ).re = a ∨ (Z θ).re = b := by
    intro θ hθ
    have him : (Z θ).im = R * Real.sin θ.1 := by
      simp [Z,upperPath,circleMap,Complex.exp_mul_I,Complex.mul_im,Complex.sin_ofReal_re]
    have hs : Real.sin θ.1 = 0 := (mul_eq_zero.mp (him.symm.trans hθ)).resolve_left hR.ne'
    by_cases h0 : θ.1 = 0
    · right
      simp [Z,upperPath,h0,circleMap,c,R]; ring
    · by_cases hπ : θ.1 = Real.pi
      · left
        simp [Z,upperPath,hπ,circleMap,c,R]; ring
      · have hp := Real.sin_pos_of_pos_of_lt_pi
          (lt_of_le_of_ne θ.2.1 (Ne.symm h0)) (lt_of_le_of_ne θ.2.2 hπ)
        exact (hp.ne' hs).elim
  obtain ⟨δ,hδ,hgapP⟩ := DEF014Contour.common_contour_gap p n
  have hgap : ∀ᶠ v : L2T L in 𝓝 u,
      ∀ᵐ (t : ℝ) ∂(PhysicalQuantumMeasure.measure hκ v), ∀ θ : UpperInterval,
        δ ≤ ‖Z θ-(t : ℂ)‖ := by
    filter_upwards [hj.continuousAt.tendsto.eventually hgapP] with v hv
    filter_upwards [hv] with t ht θ
    exact DEF014ContourReflection.circle_support_distance c hR ht θ.1
  let M := (‖u‖+1)^2
  have hM : 0 ≤ M := sq_nonneg _
  have hmass : ∀ᶠ v : L2T L in 𝓝 u,
      (PhysicalQuantumMeasure.measure hκ v univ).toReal ≤ M := by
    have hn : ∀ᶠ v : L2T L in 𝓝 u, ‖v‖ < ‖u‖+1 :=
      continuous_norm.continuousAt.tendsto.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hn] with v hv
    rw [PhysicalQuantumMeasure.measure_univ,ENNReal.toReal_ofReal (sq_nonneg _)]
    dsimp [M]
    nlinarith [norm_nonneg v,norm_nonneg u]
  obtain ⟨δa,hδa,hba⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band (n-1))
  obtain ⟨δb,hδb,hbb⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band n)
  have hband : ∀ᶠ v : L2T L in 𝓝 u, ∀ θ : UpperInterval, (Z θ).im = 0 →
      |(L2SpatialTransfer.discriminant κ v ((Z θ).re : ℂ)).re| < 2 := by
    filter_upwards [hj.continuousAt.tendsto.eventually hba,
      hj.continuousAt.tendsto.eventually hbb] with v hva hvb θ hθ
    rcases hreal θ hθ with he | he
    · rw [he]
      exact hva a (by simpa [a,DEF014Phase.separator] using hδa)
    · rw [he]
      exact hvb b (by simpa [b,DEF014Phase.separator] using hδb)
  obtain ⟨H,hH,hHe⟩ := DEF014UpperAnalytic.exists_analytic_cauchy_path hκ Z hZ u
    hupper hδ hM hgap hmass hband
  let τ : C(DEF014AnalyticIntegration.UnitInterval,UpperInterval) :=
    ⟨fun s => ⟨Real.pi*s.1,by constructor <;> nlinarith [s.2.1,s.2.2,Real.pi_pos]⟩,
      by fun_prop⟩
  let d : C(DEF014AnalyticIntegration.UnitInterval,ℂ) :=
    ⟨fun s => deriv (circleMap (c : ℂ) R) (Real.pi*s.1),by
      simp only [deriv_circleMap]; fun_prop⟩
  let F : L2T L → C(DEF014AnalyticIntegration.UnitInterval,ℂ) :=
    fun v => d * (H v).comp τ
  have hF : AnalyticAt ℝ F u := by
    exact analyticAt_const.mul
      (((ContinuousMap.compCLM (M := ℂ) (R := ℝ) τ).analyticAt _).comp hH)
  have hJ : AnalyticAt ℝ (fun v : L2T L =>
      ∫ θ in (0 : ℝ)..Real.pi,
        DEF014ContourReflection.arcIntegrand (PhysicalQuantumMeasure.measure hκ v) c R θ) u := by
    apply DEF014AnalyticIntegration.analyticAt_intervalIntegral
      (F := F) analyticAt_const analyticAt_const hF
    filter_upwards [hHe] with v hv s
    change deriv (circleMap (c : ℂ) R) (Real.pi*s.1) * H v (τ s) = _
    rw [hv]
    simp [τ,Z,upperPath,DEF014ContourReflection.arcIntegrand]
  have hscalar : AnalyticAt ℝ (fun v : L2T L =>
      (∫ θ in (0 : ℝ)..Real.pi,
        DEF014ContourReflection.arcIntegrand (PhysicalQuantumMeasure.measure hκ v) c R θ).im / Real.pi) u :=
    (((Complex.imCLM.analyticAt _).comp hJ).div_const (c := Real.pi))
  apply hscalar.congr
  have hcontour := hj.continuousAt.tendsto.eventually (DEF014Contour.eventually_physical_mass_contour p n)
  filter_upwards [hcontour,hj.continuousAt.tendsto.eventually hgapP] with v hv hvg
  have hr := DEF014ContourReflection.integral_eq_upper_sub_conj
    (PhysicalQuantumMeasure.measure hκ v) c hR hδ hvg
  change (((PhysicalSourceFinal.sourceFacts hκ v).masses).1 n : ℂ) =
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ z in C((c : ℂ),R),EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ v) z) at hv
  rw [hr] at hv
  rw [DEF014ContourReflection.normalized_sub_conj] at hv
  have hh := congrArg Complex.re hv
  simpa only [Complex.ofReal_re] using hh.symm

end QuantumNLS.DEF014MassAnalytic
end



/-! The complete DEF-014 realization on the actual physical L2 carrier. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.DEF014Realization
variable {L κ : ℝ} [Fact (0 < L)]

/-- Full DEF-014: the canonical quantum measure supplies the unique ordered
separators and nonnegative summable masses, with norm-continuous ell1 mass
map and real-analytic individual mass and separator functions. -/
theorem «DEF-014-realization» (hκ : 0 < κ) (u : PhysicalTensor.L2T L) :
    let D := PhysicalSourceFinal.sourceFacts hκ u
    (∀ n : ℤ, ∃! b : ℝ, (PhysicalContinuousBoundary.boundary hκ u b).re =
      MonotoneIndexedMasses.level n) ∧
    StrictMono D.phase.separator ∧
    (∀ n, D.masses.1 n =
      (PhysicalQuantumMeasure.measure hκ u
        (Ioo (D.phase.separator (n-1)) (D.phase.separator n))).toReal) ∧
    (∀ n, 0 ≤ D.masses.1 n) ∧ Summable (fun n => D.masses.1 n) ∧
    (∑' n,D.masses.1 n) = ‖u‖ ^ 2 ∧
    Continuous (fun v : PhysicalTensor.L2T L => (PhysicalSourceFinal.sourceFacts hκ v).masses) ∧
    (∀ n : ℤ, AnalyticAt ℝ (fun v : PhysicalTensor.L2T L =>
      ((PhysicalSourceFinal.sourceFacts hκ v).masses).1 n) u) ∧
    (∀ n : ℤ, AnalyticAt ℝ (fun v : PhysicalTensor.L2T L =>
      (PhysicalSourceFinal.sourceFacts hκ v).phase.separator n) u) := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := PhysicalSourceFinal.«DEF-014» hκ u
  exact ⟨h1,h2,h3,h4,h5,h6,DEF014Continuity.continuous_physical_masses hκ,
    (fun n => DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u),
    (fun n => DEF014SeparatorAnalytic.analyticAt_separator hκ n u)⟩

end QuantumNLS.DEF014Realization
end


#print axioms QuantumNLS.DEF014Realization.«DEF-014-realization»
#print axioms QuantumNLS.DEF014UniformCauchy.exists_continuousAt_path
#print axioms QuantumNLS.DEF014UpperAnalytic.exists_analytic_cauchy_path
#print axioms QuantumNLS.DEF014ContourReflection.integral_eq_upper_sub_conj
#print axioms QuantumNLS.DEF014MassAnalytic.analyticAt_physical_coordinate
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let prefixes : Array String := #["QuantumNLS.DEF014Contour.","QuantumNLS.DEF014AnalyticIntegration.","QuantumNLS.DEF014UniformDiscriminant.","QuantumNLS.DEF014UniformPhase.","QuantumNLS.DEF014UniformCauchy.","QuantumNLS.DEF014UpperAnalytic.","QuantumNLS.DEF014ContourReflection.","QuantumNLS.DEF014MassAnalytic.","QuantumNLS.DEF014Realization."]
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if prefixes.any (fun p => n.toString.startsWith p) ||
        n.toString.startsWith "_private.QuantumNLS.DEF014Round5." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"DEF014Round5 audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
