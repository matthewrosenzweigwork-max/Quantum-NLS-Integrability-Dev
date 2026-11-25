import QuantumNLS.GP05ComplexAverageR14
import QuantumNLS.Ext025BHaar

/-! GP-05, literal scalar Haar averaging of a covector field. Coefficients are
normalized derivatives of the source integrand, followed by weak integration.
All measurability and geometric bounds are derived from the original family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal
namespace QuantumNLS.GP05SourceHaarR14
open GP05CauchyMajorantsR14 GP05ComplexAverageR14
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure X) [IsProbabilityMeasure μ]

/-- Source scalar coefficients, including the final tangent argument. -/
def scalarCoefficients (F : X → E → E →L[ℂ] ℂ) (a : E) (n : ℕ) (x : X) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (n+1) => E) ℂ :=
  (coefficients (F x) a n).uncurryRight

lemma scalarCoefficients_measurable {F : X → E → E →L[ℂ] ℂ} {a : E} {U : Set E}
    (hU : IsOpen U) (ha : a ∈ U) (hf : ∀ x, AnalyticOnNhd ℂ (F x) U)
    (hm : ∀ z ∈ U, ∀ w, Measurable (fun x => F x z w)) (n : ℕ) (v : Fin (n+1) → E) :
    Measurable (fun x => scalarCoefficients F a n x v) := by
  have h := GP05WeakMeasR14.iterated_measurable
    (ContinuousLinearMap.apply ℂ ℂ (v (Fin.last n))) hU hf
    (fun z hz => hm z hz _) n a ha (Fin.init v)
  simpa [scalarCoefficients, coefficients] using h.const_mul ((n.factorial : ℂ)⁻¹)

omit [MeasurableSpace X] in
lemma scalarCoefficients_bound {F : X → E → E →L[ℂ] ℂ} {a : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hf : ∀ x, AnalyticOnNhd ℂ (F x) (ball a R))
    (hb : ∀ x z, z ∈ ball a R → ‖F x z‖ ≤ M) (n : ℕ) (x : X) :
    ‖scalarCoefficients F a n x‖ ≤ (Real.exp 1*M)*(2*Real.exp 1/R)^n := by
  rw [scalarCoefficients, ContinuousMultilinearMap.uncurryRight_norm]
  exact coefficient_bound hR hM (hf x) (hb x) n

/-- The original weak covector average on its stated open domain. Outside the
domain it is set to zero, with no claim of regularity across that boundary. -/
def weakAverageOn (F : X → E → E →L[ℂ] ℂ) (U : Set E) (M : ℝ)
    (hm : ∀ z ∈ U, ∀ w, Measurable (fun x => F x z w))
    (hb : ∀ x z, z ∈ U → ‖F x z‖ ≤ M) : E → E →L[ℂ] ℂ := by
  classical
  exact fun z => if hz : z ∈ U then
    QuantumNLS.Ext025A2.gp05_weak_average (μ := μ) (fun x => F x z)
      (fun w => Integrable.of_bound (hm z hz w).aestronglyMeasurable (M*‖w‖)
        (.of_forall (fun x => (F x z).le_opNorm w |>.trans
          (mul_le_mul_of_nonneg_right (hb x z hz) (norm_nonneg w)))))
      (.of_forall (fun x => hb x z hz))
    else 0

@[simp] lemma weakAverageOn_apply (F : X → E → E →L[ℂ] ℂ) (U : Set E) (M : ℝ)
    (hm : ∀ z ∈ U, ∀ w, Measurable (fun x => F x z w))
    (hb : ∀ x z, z ∈ U → ‖F x z‖ ≤ M) (z : E) (hz : z ∈ U) (w : E) :
    weakAverageOn μ F U M hm hb z w = ∫ x, F x z w ∂μ := by
  simp only [weakAverageOn, dite_eq_left hz]
  rfl

/-- Application form: the original weak average has actual bounded multilinear
coefficients, a common geometric majorant and a full dual-norm convergent
expansion. The only bridge premise is holomorphic implies analytic. -/
theorem covector_average_of_analytic
    (F : X → E → E →L[ℂ] ℂ) (a : E) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hfa : ∀ x, AnalyticOnNhd ℂ (F x) (ball a R))
    (hm : ∀ z ∈ ball a R, ∀ w, Measurable (fun x => F x z w))
    (hb : ∀ x z, z ∈ ball a R → ‖F x z‖ ≤ M) :
    ∃ p : FormalMultilinearSeries ℂ E (E →L[ℂ] ℂ),
      (∀ n v w, p n v w = ∫ x, coefficients (F x) a n v w ∂μ) ∧
      (∀ n, ‖p n‖ ≤ (Real.exp 1*M)*(2*Real.exp 1/R)^n) ∧
      HasFPowerSeriesOnBall (weakAverageOn μ F (ball a R) M hm hb) p a
        (ENNReal.ofReal (commonRadius R)) ∧
      AnalyticOnNhd ℂ (weakAverageOn μ F (ball a R) M hm hb)
        (ball a (commonRadius R)) := by
  let r : ℝ≥0 := NNReal.mk (commonRadius R) (commonRadius_pos hR).le
  let D : ℕ → ℝ := fun n => (Real.exp 1*M)*(2*Real.exp 1/R)^n
  have hD : ∀ n, 0 ≤ D n := fun n => by dsimp [D]; positivity
  have hmeas := scalarCoefficients_measurable isOpen_ball (mem_ball_self hR) hfa hm
  have hbound := scalarCoefficients_bound hR hM hfa hb
  let p := averagedCoefficients μ (scalarCoefficients F a) D hmeas hbound
  have hgeo : ∀ n, D n*(r : ℝ)^n ≤ Real.exp 1*M := by
    intro n
    dsimp [D, r]
    rw [mul_assoc, ← mul_pow]
    have hrw : (2*Real.exp 1/R)*commonRadius R = 1 := by
      unfold commonRadius
      field_simp
    rw [hrw, one_pow, mul_one]
  have hTaylor : ∀ x z, ‖z‖ < r → ∀ w,
      HasSum (fun n => scalarCoefficients F a n x (Fin.snoc (fun _ => z) w))
        (F x (a+z) w) := by
    intro x z hz w
    have hz' : z ∈ eball (0 : E) r := by
      rw [mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
      exact ENNReal.coe_lt_coe.mpr (by exact_mod_cast hz)
    have hc : HasFPowerSeriesOnBall (F x) (coefficients (F x) a) a r := by
      simpa only [ENNReal.ofReal_eq_coe_nnreal (commonRadius_pos hR).le] using
        canonical_expansion hR hM (hfa x) (hb x)
    have hs := hc.hasSum hz'
    have hsw := (ContinuousLinearMap.apply ℂ ℂ w).hasSum hs
    simpa [scalarCoefficients] using hsw
  have havg := analytic_average μ (scalarCoefficients F a) D hD hmeas hbound r
    (commonRadius_pos hR) (Real.exp 1*M) hgeo (fun x z w => F x (a+z) w) hTaylor
  have hradius := (coefficient_analyticity μ (scalarCoefficients F a) D hD hmeas hbound r
    (Real.exp 1*M) hgeo).1
  have hpower : HasFPowerSeriesOnBall (weakAverageOn μ F (ball a R) M hm hb) p a r := by
    refine ⟨hradius, by exact_mod_cast commonRadius_pos hR, ?_⟩
    intro z hz
    have hzR : a+z ∈ ball a R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      have hzr : ‖z‖ < r := by
        have : ‖z‖₊ < r := by simpa only [mem_eball, edist_eq_enorm_sub, sub_zero,
          enorm_eq_nnnorm, ENNReal.coe_lt_coe] using hz
        exact_mod_cast this
      exact hzr.trans_le (commonRadius_le hR.le)
    have he : p.sum z = weakAverageOn μ F (ball a R) M hm hb (a+z) := by
      ext w
      rw [weakAverageOn_apply μ F (ball a R) M hm hb _ hzR]
      apply havg.2 z _ w
      have : ‖z‖₊ < r := by simpa only [mem_eball, edist_eq_enorm_sub, sub_zero,
        enorm_eq_nnnorm, ENNReal.coe_lt_coe] using hz
      exact_mod_cast this
    rw [← he]
    exact p.hasSum (lt_of_lt_of_le hz hradius)
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · intro n v w
    simp [p, scalarCoefficients]
  · intro n
    dsimp [p, averagedCoefficients]
    rw [ContinuousMultilinearMap.curryRight_norm]
    exact norm_scalarAverage_le μ _ (D n) (hD n) (hmeas n) (hbound n)
  · simpa only [ENNReal.ofReal_eq_coe_nnreal (commonRadius_pos hR).le] using hpower
  · exact hpower.analyticOnNhd.mono (by
      intro z hz
      rw [mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm]
      exact ENNReal.coe_lt_coe.mpr (by
        exact_mod_cast (show ‖z-a‖ < (r : ℝ) from mem_ball_iff_norm.mp hz)))

theorem covector_average (bridge : BanachHolomorphicBridge E (E →L[ℂ] ℂ))
    (F : X → E → E →L[ℂ] ℂ) (a : E) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hf : ∀ x, DifferentiableOn ℂ (F x) (ball a R))
    (hm : ∀ z ∈ ball a R, ∀ w, Measurable (fun x => F x z w))
    (hb : ∀ x z, z ∈ ball a R → ‖F x z‖ ≤ M) :
    ∃ p : FormalMultilinearSeries ℂ E (E →L[ℂ] ℂ),
      (∀ n v w, p n v w = ∫ x, coefficients (F x) a n v w ∂μ) ∧
      (∀ n, ‖p n‖ ≤ (Real.exp 1*M)*(2*Real.exp 1/R)^n) ∧
      HasFPowerSeriesOnBall (weakAverageOn μ F (ball a R) M hm hb) p a
        (ENNReal.ofReal (commonRadius R)) ∧
      AnalyticOnNhd ℂ (weakAverageOn μ F (ball a R) M hm hb)
        (ball a (commonRadius R)) := by
  exact covector_average_of_analytic μ F a hR hM
    (fun x => bridge _ _ isOpen_ball (hf x)) hm hb

end QuantumNLS.GP05SourceHaarR14
