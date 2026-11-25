import Mathlib
import QuantumNLS.DEF014Round5
import QuantumNLS.RootIndexedMasses

/-!
# REF88EnergyContour: the weighted contour energy of one fixed cell is real analytic
(R-EF8C2837, "Bounded contour energies near arbitrary mass")

Source: `source-text/chapters/global/physical_cubic.tex`, proof, paragraph "Bounded contour energies
near arbitrary mass" (printed lines 38 to 77): "... choose a fixed rectangle whose vertical crossings are
inside the two neighboring open bands at `u_*` ... Let `G_u` be the actual quantum-selected Cauchy
transform and set locally `E_F(u) = ∑_{j∈F} (2πi)⁻¹ ∮_{Γ_j} z² G_u(z) dz`.  This is a real-analytic scalar
function on the full Hilbert neighborhood."

The fixed contour `Γ_j` of the accepted `DEF014MassAnalytic.analyticAt_physical_coordinate` is the circle
whose diameter is the cell `(a,b) = (σ(j-1), σ(j))` of the base point `u_*` (`σ` = actual selected separators).
This module proves the same statement with the weight `z²`:

* `integral_cauchy_sq`: the weighted Fubini/residue identity
  `(2πi)⁻¹ ∮_{C(c,R)} z² G_μ(z) dz = ∫_{(c-R,c+R)} t² dμ(t)` for a finite measure with a uniform gap to the circle;
* `integral_sq_eq_upper_sub_conj`: the real-measure reflection reducing it to the upper arc;
* `analyticAt_cellEnergy`: `v ↦ ∫_{(σ_u(n-1),σ_u(n))} t² dM_{κ,v}(t)` is real analytic at `u`
  (the weighted copy of the accepted `analyticAt_physical_coordinate`, with the fixed continuous
  weight `z(θ)²` inserted into the reparameterized arc integrand).

Only accepted modules are imported, read-only.  No held contract is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section

open Set Filter Topology MeasureTheory Complex ComplexConjugate
open scoped NNReal

namespace QuantumNLS.REF88EnergyContour

open PhysicalTensor (L2T)
open DEF014MassAnalytic (UpperInterval upperPath)

/-- The `z²`-weighted circle kernel: `∮_{C(c,R)} z² (z-t)⁻¹ dz = 2πi t²` for `t` inside, `0` outside. -/
theorem circle_integral_sq_kernel (c : ℝ) {R : ℝ} (hR : 0 < R) {t : ℝ}
    (ht : ‖(t : ℂ) - (c : ℂ)‖ ≠ R) :
    (∮ z in C((c : ℂ), R), z ^ 2 * (z - (t : ℂ))⁻¹) =
      {s : ℝ | ‖(s : ℂ) - (c : ℂ)‖ < R}.indicator
        (fun s : ℝ => 2 * (Real.pi : ℂ) * I * (s : ℂ) ^ 2) t := by
  by_cases hin : ‖(t : ℂ) - (c : ℂ)‖ < R
  · simp only [Set.indicator, mem_ofPred, hin, ↓reduceIte]
    have hw : (t : ℂ) ∈ Metric.ball (c : ℂ) R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hin
    have hf : DiffContOnCl ℂ (fun z : ℂ => z ^ 2) (Metric.ball (c : ℂ) R) :=
      (differentiable_id.pow 2).diffContOnCl
    have h := hf.circleIntegral_sub_inv_smul hw
    simp only [smul_eq_mul] at h
    have e : (fun z : ℂ => z ^ 2 * (z - (t : ℂ))⁻¹) = fun z : ℂ => (z - (t : ℂ))⁻¹ * z ^ 2 := by
      funext z; ring
    rw [e, h]
  · simp only [Set.indicator, mem_ofPred, hin, ↓reduceIte]
    have hout : R < ‖(t : ℂ) - (c : ℂ)‖ := lt_of_le_of_ne (le_of_not_gt hin) (Ne.symm ht)
    have hn : ∀ z ∈ Metric.closedBall (c : ℂ) R, z - (t : ℂ) ≠ 0 := by
      intro z hz he
      have heq : z = (t : ℂ) := sub_eq_zero.mp he
      subst z
      exact (not_le.mpr hout) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
    apply DiffContOnCl.circleIntegral_eq_zero hR.le
    constructor
    · intro z hz
      exact ((differentiableAt_id.pow 2).mul
        ((differentiableAt_id.sub_const (t : ℂ)).inv
          (hn z (Metric.ball_subset_closedBall hz)))).differentiableWithinAt
    · apply (continuousOn_id.pow 2).mul
      apply (continuousOn_id.sub continuousOn_const).inv₀
      intro z hz
      exact hn z (by simpa [closure_ball (c : ℂ) hR.ne'] using hz)

/-- Fubini on a circle separated from the support, with weight `z²`. -/
theorem integral_cauchy_sq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℝ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ᵐ (t : ℝ) ∂μ, δ ≤ |‖(t : ℂ) - (c : ℂ)‖ - R|) :
    (∮ z in C((c : ℂ), R), z ^ 2 * EmpiricalRapidity.cauchyTransform μ z) =
      (2 * (Real.pi : ℂ) * I) *
        ((∫ t in {s : ℝ | ‖(s : ℂ) - (c : ℂ)‖ < R}, t ^ 2 ∂μ : ℝ) : ℂ) := by
  let F : ℝ → ℝ → ℂ := fun θ t =>
    deriv (circleMap (c : ℂ) R) θ * (circleMap (c : ℂ) R θ) ^ 2 *
      (circleMap (c : ℂ) R θ - (t : ℂ))⁻¹
  have hdist (θ t : ℝ) (ht : δ ≤ |‖(t : ℂ) - (c : ℂ)‖ - R|) :
      δ ≤ ‖circleMap (c : ℂ) R θ - (t : ℂ)‖ :=
    DEF014ContourReflection.circle_support_distance c hR ht θ
  have hmeas : Measurable (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    simp_rw [deriv_circleMap]
    fun_prop
  let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    rw [uIoc_of_le Real.two_pi_pos.le]
    infer_instance
  have hcb : ∀ θ : ℝ, ‖circleMap (c : ℂ) R θ‖ ≤ |c| + R := by
    intro θ
    have h1 : ‖circleMap (c : ℂ) R θ - (c : ℂ)‖ = R := by simp [abs_of_pos hR]
    have h2 := norm_le_insert' (circleMap (c : ℂ) R θ) (c : ℂ)
    rw [h1, Complex.norm_real, Real.norm_eq_abs] at h2
    linarith
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))).prod μ) := by
    apply (integrable_const (R * (|c| + R) ^ 2 * δ⁻¹)).mono' hmeas.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hmeas.norm measurable_const)).mpr
    exact Eventually.of_forall fun θ => hgap.mono fun t ht => by
      dsimp [Function.uncurry, F]
      rw [norm_mul, norm_mul, norm_inv, norm_pow]
      have hd : ‖deriv (circleMap (c : ℂ) R) θ‖ = R := by
        simp [deriv_circleMap, norm_circleMap_zero, abs_of_pos hR]
      rw [hd]
      have h1 : ‖circleMap (c : ℂ) R θ‖ ^ 2 ≤ (|c| + R) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hcb θ) 2
      have h2 : ‖circleMap (c : ℂ) R θ - (t : ℂ)‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (hdist θ t ht)
      gcongr
  have hswap := intervalIntegral_integral_swap hi
  have hformula : ∀ᵐ (t : ℝ) ∂μ, (∮ z in C((c : ℂ), R), z ^ 2 * (z - (t : ℂ))⁻¹) =
      {s : ℝ | ‖(s : ℂ) - (c : ℂ)‖ < R}.indicator
        (fun s : ℝ => 2 * (Real.pi : ℂ) * I * (s : ℂ) ^ 2) t := by
    filter_upwards [hgap] with t ht
    refine circle_integral_sq_kernel c hR ?_
    intro he
    rw [he, sub_self, abs_zero] at ht
    linarith
  have hmeasS : MeasurableSet {s : ℝ | ‖(s : ℂ) - (c : ℂ)‖ < R} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  calc
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ t, F θ t ∂μ := by
      unfold circleIntegral EmpiricalRapidity.cauchyTransform
      congr 1
      funext θ
      simp only [F]
      rw [← integral_const_mul]
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      congr 1
      funext t
      ring
    _ = ∫ (t : ℝ), (∮ z in C((c : ℂ), R), z ^ 2 * (z - (t : ℂ))⁻¹) ∂μ := by
      rw [hswap]
      congr 1
      funext t
      unfold circleIntegral
      congr 1
      funext θ
      simp only [F, smul_eq_mul]
      ring
    _ = ∫ (t : ℝ), {s : ℝ | ‖(s : ℂ) - (c : ℂ)‖ < R}.indicator
        (fun s : ℝ => 2 * (Real.pi : ℂ) * I * (s : ℂ) ^ 2) t ∂μ := integral_congr_ae hformula
    _ = _ := by
      rw [integral_indicator hmeasS, integral_const_mul]
      congr 1
      rw [← integral_complex_ofReal]
      congr 1
      funext t
      push_cast
      ring

/-- Normalized weighted contour identity. -/
theorem normalized_integral_cauchy_sq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℝ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ᵐ (t : ℝ) ∂μ, δ ≤ |‖(t : ℂ) - (c : ℂ)‖ - R|) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ z in C((c : ℂ), R), z ^ 2 * EmpiricalRapidity.cauchyTransform μ z) =
      ((∫ t in {s : ℝ | ‖(s : ℂ) - (c : ℂ)‖ < R}, t ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [integral_cauchy_sq μ c hR hδ hgap, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]

/-- The weighted upper-arc integrand. -/
def arcIntegrandSq (μ : Measure ℝ) (c R : ℝ) (θ : ℝ) : ℂ :=
  deriv (circleMap (c : ℂ) R) θ * (circleMap (c : ℂ) R θ) ^ 2 *
    EmpiricalRapidity.cauchyTransform μ (circleMap (c : ℂ) R θ)

theorem arcIntegrandSq_neg (μ : Measure ℝ) (c R θ : ℝ) :
    arcIntegrandSq μ c R (-θ) = -conj (arcIntegrandSq μ c R θ) := by
  have hz : circleMap (c : ℂ) R (-θ) = conj (circleMap (c : ℂ) R θ) := by
    simpa using (conj_circleMap (c : ℂ) R θ).symm
  have h0 : circleMap 0 R (-θ) = conj (circleMap 0 R θ) :=
    (conj_circleMap_zero R θ).symm
  simp only [arcIntegrandSq, deriv_circleMap, hz, h0, DEF014ContourReflection.cauchy_conj, map_mul,
    map_pow, Complex.conj_I]
  ring

theorem periodic_arcIntegrandSq (μ : Measure ℝ) (c R : ℝ) :
    Function.Periodic (arcIntegrandSq μ c R) (2 * Real.pi) := by
  intro θ
  simp only [arcIntegrandSq, deriv_circleMap, periodic_circleMap _ _ θ]

theorem integral_sq_eq_upper_sub_conj (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℝ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ᵐ (t : ℝ) ∂μ, δ ≤ |‖(t : ℂ) - (c : ℂ)‖ - R|) :
    (∮ z in C((c : ℂ), R), z ^ 2 * EmpiricalRapidity.cauchyTransform μ z) =
      (∫ θ in (0 : ℝ)..Real.pi, arcIntegrandSq μ c R θ) -
        conj (∫ θ in (0 : ℝ)..Real.pi, arcIntegrandSq μ c R θ) := by
  have hc : Continuous (arcIntegrandSq μ c R) := by
    change Continuous (fun θ => deriv (circleMap (c : ℂ) R) θ * (circleMap (c : ℂ) R θ) ^ 2 *
      EmpiricalRapidity.cauchyTransform μ (circleMap (c : ℂ) R θ))
    have hd : Continuous (fun θ => deriv (circleMap (c : ℂ) R) θ) := by
      simp only [deriv_circleMap]; fun_prop
    exact (hd.mul ((continuous_circleMap _ _).pow 2)).mul
      (DEF014ContourReflection.continuous_cauchy_circle μ c hR hδ hgap)
  have hp := (periodic_arcIntegrandSq μ c R).intervalIntegral_add_eq 0 (-Real.pi)
  simp only [zero_add] at hp
  have hend : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hend] at hp
  have hcirc : (∮ z in C((c : ℂ), R), z ^ 2 * EmpiricalRapidity.cauchyTransform μ z) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, arcIntegrandSq μ c R θ := by
    unfold circleIntegral
    congr 1
    funext θ
    simp only [arcIntegrandSq, smul_eq_mul]
    ring
  rw [hcirc, hp, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-Real.pi) 0) (hc.intervalIntegrable 0 Real.pi)]
  have hn : (∫ θ in -Real.pi..0, arcIntegrandSq μ c R θ) =
      -conj (∫ θ in (0 : ℝ)..Real.pi, arcIntegrandSq μ c R θ) := by
    rw [← show -(0 : ℝ) = 0 by simp]
    rw [← intervalIntegral.integral_comp_neg]
    simp_rw [arcIntegrandSq_neg]
    rw [intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]
    simp only [neg_zero]
  rw [hn]
  ring

/-- The fixed-cell weighted contour energy `∫_{(a,b)} t² dM_{κ,v}`. -/
def cellEnergy {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (a b : ℝ) (v : L2T L) : ℝ :=
  ∫ t in Ioo a b, t ^ 2 ∂(PhysicalQuantumMeasure.measure hκ v)

/-- The actual selected separator, as a function of the base field. -/
def sep {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L) (n : ℤ) : ℝ :=
  DEF014Phase.separator ((⟨κ, hκ⟩ : {κ : ℝ // 0 < κ}), u) n

variable {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)

/-- **Weighted copy of `DEF014MassAnalytic.analyticAt_physical_coordinate`**: the contour energy of the
fixed cell of `u` is real analytic on a full `L²` neighborhood of `u`. -/
theorem analyticAt_cellEnergy (n : ℤ) (u : L2T L) :
    AnalyticAt ℝ (fun v : L2T L => cellEnergy hκ (sep hκ u (n - 1)) (sep hκ u n) v) u := by
  let p : DEF014Phase.Param L := (⟨κ, hκ⟩, u)
  let j : L2T L → DEF014Phase.Param L := fun v => (⟨κ, hκ⟩, v)
  have hj : Continuous j := continuous_const.prodMk continuous_id
  let a := DEF014Phase.separator p (n - 1)
  let b := DEF014Phase.separator p n
  let c := (a + b) / 2
  let R := (b - a) / 2
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
    simpa [circleMap, Complex.exp_mul_I, Complex.mul_im, Complex.sin_ofReal_re] using
      mul_nonneg hR.le (Real.sin_nonneg_of_mem_Icc θ.2)
  have hreal : ∀ θ : UpperInterval, (Z θ).im = 0 → (Z θ).re = a ∨ (Z θ).re = b := by
    intro θ hθ
    have him : (Z θ).im = R * Real.sin θ.1 := by
      simp [Z, upperPath, circleMap, Complex.exp_mul_I, Complex.mul_im, Complex.sin_ofReal_re]
    have hs : Real.sin θ.1 = 0 := (mul_eq_zero.mp (him.symm.trans hθ)).resolve_left hR.ne'
    by_cases h0 : θ.1 = 0
    · right
      simp [Z, upperPath, h0, circleMap, c, R]; ring
    · by_cases hπ : θ.1 = Real.pi
      · left
        simp [Z, upperPath, hπ, circleMap, c, R]; ring
      · have hp := Real.sin_pos_of_pos_of_lt_pi
          (lt_of_le_of_ne θ.2.1 (Ne.symm h0)) (lt_of_le_of_ne θ.2.2 hπ)
        exact (hp.ne' hs).elim
  obtain ⟨δ, hδ, hgapP⟩ := DEF014Contour.common_contour_gap p n
  have hgap : ∀ᶠ v : L2T L in 𝓝 u,
      ∀ᵐ (t : ℝ) ∂(PhysicalQuantumMeasure.measure hκ v), ∀ θ : UpperInterval,
        δ ≤ ‖Z θ - (t : ℂ)‖ := by
    filter_upwards [hj.continuousAt.tendsto.eventually hgapP] with v hv
    filter_upwards [hv] with t ht θ
    exact DEF014ContourReflection.circle_support_distance c hR ht θ.1
  let M := (‖u‖ + 1) ^ 2
  have hM : 0 ≤ M := sq_nonneg _
  have hmass : ∀ᶠ v : L2T L in 𝓝 u,
      (PhysicalQuantumMeasure.measure hκ v univ).toReal ≤ M := by
    have hn : ∀ᶠ v : L2T L in 𝓝 u, ‖v‖ < ‖u‖ + 1 :=
      continuous_norm.continuousAt.tendsto.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hn] with v hv
    rw [PhysicalQuantumMeasure.measure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
    dsimp [M]
    nlinarith [norm_nonneg v, norm_nonneg u]
  obtain ⟨δa, hδa, hba⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band (n - 1))
  obtain ⟨δb, hδb, hbb⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band n)
  have hband : ∀ᶠ v : L2T L in 𝓝 u, ∀ θ : UpperInterval, (Z θ).im = 0 →
      |(L2SpatialTransfer.discriminant κ v ((Z θ).re : ℂ)).re| < 2 := by
    filter_upwards [hj.continuousAt.tendsto.eventually hba,
      hj.continuousAt.tendsto.eventually hbb] with v hva hvb θ hθ
    rcases hreal θ hθ with he | he
    · rw [he]
      exact hva a (by simpa [a, DEF014Phase.separator] using hδa)
    · rw [he]
      exact hvb b (by simpa [b, DEF014Phase.separator] using hδb)
  obtain ⟨H, hH, hHe⟩ := DEF014UpperAnalytic.exists_analytic_cauchy_path hκ Z hZ u
    hupper hδ hM hgap hmass hband
  let τ : C(DEF014AnalyticIntegration.UnitInterval, UpperInterval) :=
    ⟨fun s => ⟨Real.pi * s.1, by constructor <;> nlinarith [s.2.1, s.2.2, Real.pi_pos]⟩,
      by fun_prop⟩
  -- the fixed continuous weight `z'(θ) z(θ)²`
  let d : C(DEF014AnalyticIntegration.UnitInterval, ℂ) :=
    ⟨fun s => deriv (circleMap (c : ℂ) R) (Real.pi * s.1) * (circleMap (c : ℂ) R (Real.pi * s.1)) ^ 2, by
      simp only [deriv_circleMap]; fun_prop⟩
  let F : L2T L → C(DEF014AnalyticIntegration.UnitInterval, ℂ) :=
    fun v => d * (H v).comp τ
  have hF : AnalyticAt ℝ F u := by
    exact analyticAt_const.mul
      (((ContinuousMap.compCLM (M := ℂ) (R := ℝ) τ).analyticAt _).comp hH)
  have hJ : AnalyticAt ℝ (fun v : L2T L =>
      ∫ θ in (0 : ℝ)..Real.pi,
        arcIntegrandSq (PhysicalQuantumMeasure.measure hκ v) c R θ) u := by
    apply DEF014AnalyticIntegration.analyticAt_intervalIntegral
      (F := F) analyticAt_const analyticAt_const hF
    filter_upwards [hHe] with v hv s
    change deriv (circleMap (c : ℂ) R) (Real.pi * s.1) * (circleMap (c : ℂ) R (Real.pi * s.1)) ^ 2 *
      H v (τ s) = _
    rw [hv]
    simp [τ, Z, upperPath, arcIntegrandSq]
  have hscalar : AnalyticAt ℝ (fun v : L2T L =>
      (∫ θ in (0 : ℝ)..Real.pi,
        arcIntegrandSq (PhysicalQuantumMeasure.measure hκ v) c R θ).im / Real.pi) u :=
    (((Complex.imCLM.analyticAt _).comp hJ).div_const (c := Real.pi))
  have hlc : Real.pi = 0 → False := fun h => Real.pi_ne_zero h
  have hce : ∀ᶠ v : L2T L in 𝓝 u,
      cellEnergy hκ (sep hκ u (n - 1)) (sep hκ u n) v =
        (∫ θ in (0 : ℝ)..Real.pi,
          arcIntegrandSq (PhysicalQuantumMeasure.measure hκ v) c R θ).im / Real.pi := by
    filter_upwards [hj.continuousAt.tendsto.eventually hgapP] with v hvg
    have hr := integral_sq_eq_upper_sub_conj
      (PhysicalQuantumMeasure.measure hκ v) c hR hδ hvg
    have hnorm := normalized_integral_cauchy_sq
      (PhysicalQuantumMeasure.measure hκ v) c hR hδ hvg
    have hdia : {s : ℝ | ‖(s : ℂ) - (c : ℂ)‖ < R} = Ioo a b := DEF014Contour.diameter_set a b
    rw [hdia, hr, DEF014ContourReflection.normalized_sub_conj] at hnorm
    have hh := congrArg Complex.re hnorm
    simp only [Complex.ofReal_re] at hh
    unfold cellEnergy
    exact hh.symm
  exact hscalar.congr (by
    filter_upwards [hce] with v hv
    exact hv.symm)

#print axioms circle_integral_sq_kernel
#print axioms integral_cauchy_sq
#print axioms integral_sq_eq_upper_sub_conj
#print axioms analyticAt_cellEnergy

end QuantumNLS.REF88EnergyContour
