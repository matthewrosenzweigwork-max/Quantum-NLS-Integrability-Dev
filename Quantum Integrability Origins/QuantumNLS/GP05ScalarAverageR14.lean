import QuantumNLS.GP05SourceHaarR14

/-! Scalar integration form used by LOCAL-017's radial/angular primitive.
The coefficients, their measurability and their summable geometric bounds are
constructed from the original holomorphic scalar family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal
namespace QuantumNLS.GP05ScalarAverageR14
open GP05CauchyMajorantsR14 GP05ComplexAverageR14
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure X) [IsProbabilityMeasure μ]

/-- Scalar integration with an explicit Banach holomorphy bridge. -/
theorem scalar_average_of_analytic
    (F : X → E → ℂ) (a : E) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hfa : ∀ x, AnalyticOnNhd ℂ (F x) (ball a R))
    (hm : ∀ z ∈ ball a R, Measurable (fun x => F x z))
    (hb : ∀ x z, z ∈ ball a R → ‖F x z‖ ≤ M) :
    ∃ p : FormalMultilinearSeries ℂ E ℂ,
      (∀ n v, p n v = ∫ x, coefficients (F x) a n v ∂μ) ∧
      (∀ n, ‖p n‖ ≤ (Real.exp 1*M)*(2*Real.exp 1/R)^n) ∧
      HasFPowerSeriesOnBall (fun z => ∫ x, F x z ∂μ) p a
        (ENNReal.ofReal (commonRadius R)) ∧
      AnalyticOnNhd ℂ (fun z => ∫ x, F x z ∂μ) (ball a (commonRadius R)) := by
  let r : ℝ≥0 := NNReal.mk (commonRadius R) (commonRadius_pos hR).le
  let D : ℕ → ℝ := fun n => (Real.exp 1*M)*(2*Real.exp 1/R)^n
  have hD : ∀ n, 0 ≤ D n := fun n => by dsimp [D]; positivity
  have hmeas : ∀ n v, Measurable (fun x => coefficients (F x) a n v) := by
    intro n v
    have h := GP05WeakMeasR14.iterated_measurable (ContinuousLinearMap.id ℂ ℂ)
      isOpen_ball hfa hm n a (mem_ball_self hR) v
    simpa [coefficients] using h.const_mul ((n.factorial : ℂ)⁻¹)
  have hbound : ∀ n x, ‖coefficients (F x) a n‖ ≤ D n :=
    fun n x => coefficient_bound hR hM (hfa x) (hb x) n
  let p : FormalMultilinearSeries ℂ E ℂ := fun n =>
    scalarAverage μ (fun x => coefficients (F x) a n) (D n) (hmeas n) (hbound n)
  have hpbound : ∀ n, ‖p n‖ ≤ D n := fun n =>
    norm_scalarAverage_le μ _ _ (hD n) (hmeas n) (hbound n)
  have hgeo : ∀ n, D n*(r : ℝ)^n ≤ Real.exp 1*M := by
    intro n
    dsimp [D, r]
    rw [mul_assoc, ← mul_pow]
    have he : (2*Real.exp 1/R)*commonRadius R = 1 := by
      unfold commonRadius
      field_simp
    rw [he, one_pow, mul_one]
  have hrad : (r : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_bound (Real.exp 1*M)
    intro n
    exact (mul_le_mul_of_nonneg_right (hpbound n) (by positivity)).trans (hgeo n)
  have hpower : HasFPowerSeriesOnBall (fun z => ∫ x, F x z ∂μ) p a r := by
    refine ⟨hrad, by exact_mod_cast commonRadius_pos hR, ?_⟩
    intro z hz
    have hz' : ‖z‖ < r := by
      have : ‖z‖₊ < r := by simpa only [mem_eball, edist_eq_enorm_sub, sub_zero,
        enorm_eq_nnnorm, ENNReal.coe_lt_coe] using hz
      exact_mod_cast this
    let q : ℝ := ‖z‖/r
    have hq : |q| < 1 := by
      rw [abs_of_nonneg (by dsimp [q]; positivity)]
      exact (div_lt_one (commonRadius_pos hR)).mpr hz'
    have hs : Summable (fun n : ℕ => (Real.exp 1*M)*q^n) :=
      (summable_geometric_of_abs_lt_one hq).mul_left _
    have hterm : ∀ n x, ‖coefficients (F x) a n (fun _ => z)‖ ≤ (Real.exp 1*M)*q^n := by
      intro n x
      have hprod : (∏ _ : Fin n, ‖z‖) = ‖z‖^n := by simp
      calc
        _ ≤ ‖coefficients (F x) a n‖*(∏ _ : Fin n, ‖z‖) :=
          (coefficients (F x) a n).le_opNorm _
        _ ≤ D n*‖z‖^n := by rw [hprod]; gcongr; exact hbound n x
        _ = (D n*(r : ℝ)^n)*q^n := by
          dsimp [q]
          rw [div_pow]
          have hrne : (r : ℝ) ≠ 0 := ne_of_gt (show 0 < (r : ℝ) from commonRadius_pos hR)
          field_simp [hrne]
        _ ≤ (Real.exp 1*M)*q^n :=
          mul_le_mul_of_nonneg_right (hgeo n) (by dsimp [q]; positivity)
    have hi : HasSum (fun n => ∫ x, coefficients (F x) a n (fun _ => z) ∂μ)
        (∫ x, F x (a+z) ∂μ) := by
      apply hasSum_integral_of_dominated_convergence (fun n _ => (Real.exp 1*M)*q^n)
      · intro n
        exact (hmeas n _).aestronglyMeasurable
      · intro n
        exact .of_forall (hterm n)
      · exact .of_forall (fun _ => hs)
      · exact integrable_const _
      · apply Filter.Eventually.of_forall
        intro x
        have hc : HasFPowerSeriesOnBall (F x) (coefficients (F x) a) a r := by
          simpa only [ENNReal.ofReal_eq_coe_nnreal (commonRadius_pos hR).le] using
            canonical_expansion hR hM (hfa x) (hb x)
        exact hc.hasSum hz
    exact hi
  refine ⟨p, fun _ _ => rfl, hpbound, ?_, ?_⟩
  · simpa only [ENNReal.ofReal_eq_coe_nnreal (commonRadius_pos hR).le] using hpower
  · exact hpower.analyticOnNhd.mono (by
      intro z hz
      rw [mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm]
      exact ENNReal.coe_lt_coe.mpr (by exact_mod_cast (mem_ball_iff_norm.mp hz)))

theorem scalar_average (bridge : BanachHolomorphicBridge E ℂ)
    (F : X → E → ℂ) (a : E) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hf : ∀ x, DifferentiableOn ℂ (F x) (ball a R))
    (hm : ∀ z ∈ ball a R, Measurable (fun x => F x z))
    (hb : ∀ x z, z ∈ ball a R → ‖F x z‖ ≤ M) :
    ∃ p : FormalMultilinearSeries ℂ E ℂ,
      (∀ n v, p n v = ∫ x, coefficients (F x) a n v ∂μ) ∧
      (∀ n, ‖p n‖ ≤ (Real.exp 1*M)*(2*Real.exp 1/R)^n) ∧
      HasFPowerSeriesOnBall (fun z => ∫ x, F x z ∂μ) p a
        (ENNReal.ofReal (commonRadius R)) ∧
      AnalyticOnNhd ℂ (fun z => ∫ x, F x z ∂μ) (ball a (commonRadius R)) := by
  exact scalar_average_of_analytic μ F a hR hM (fun x => bridge _ _ isOpen_ball (hf x)) hm hb

/-- The literal scalar angular/path integrand; its final sign is retained. -/
def correctingIntegrand (β : E → E →L[ℂ] ℂ)
    (rotation velocity : X → E →L[ℂ] E) (x : X) (z : E) : ℂ :=
  -(β (rotation x z) (velocity x (rotation x z)))

omit [MeasurableSpace X] in
/-- The source cubic covector and bounded rotations/velocities give a uniform
fourth-order scalar value bound before Cauchy estimates are applied. -/
theorem correctingIntegrand_bound (β : E → E →L[ℂ] ℂ)
    (rotation velocity : X → E →L[ℂ] E) {R C K : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hrot : ∀ x z, ‖rotation x z‖ ≤ ‖z‖)
    (hvel : ∀ x z, ‖velocity x z‖ ≤ K*‖z‖)
    (hβ : ∀ z ∈ ball (0 : E) R, ‖β z‖ ≤ C*‖z‖^3) :
    ∀ x z, z ∈ ball (0 : E) R → ‖correctingIntegrand β rotation velocity x z‖ ≤ C*K*R^4 := by
  intro x z hz
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  have hrotR : ‖rotation x z‖ < R := (hrot x z).trans_lt hzR
  have hmem : rotation x z ∈ ball (0 : E) R := mem_ball_zero_iff.mpr hrotR
  rw [correctingIntegrand, norm_neg]
  calc
    _ ≤ ‖β (rotation x z)‖*‖velocity x (rotation x z)‖ :=
      (β (rotation x z)).le_opNorm _
    _ ≤ (C*R^3)*(K*R) := by
      apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
      · exact (hβ _ hmem).trans (by gcongr)
      · exact (hvel _ _).trans (by gcongr)
    _ = C*K*R^4 := by ring

omit [MeasurableSpace X] in
/-- Holomorphy of the literal scalar expression follows from that of beta
and bounded complex-linear rotations and velocities. -/
lemma correctingIntegrand_analytic
    (bridgeCovector : BanachHolomorphicBridge E (E →L[ℂ] ℂ))
    (β : E → E →L[ℂ] ℂ) (rotation velocity : X → E →L[ℂ] E) {R : ℝ}
    (hrot : ∀ x z, ‖rotation x z‖ ≤ ‖z‖)
    (hf : DifferentiableOn ℂ β (ball (0 : E) R)) :
    ∀ x, AnalyticOnNhd ℂ (correctingIntegrand β rotation velocity x) (ball 0 R) := by
  intro x z hz
  have hr := (rotation x).analyticAt z
  have hmem : rotation x z ∈ ball (0 : E) R := by
    exact mem_ball_zero_iff.mpr ((hrot x z).trans_lt (mem_ball_zero_iff.mp hz))
  have hβa := (bridgeCovector _ _ isOpen_ball hf _ hmem).comp hr
  have hva := ((velocity x).analyticAt (rotation x z)).comp hr
  have he := ((ContinuousLinearMap.id ℂ (E →L[ℂ] ℂ)).analyticAt_bilinear
    (β (rotation x z), velocity x (rotation x z))).comp₂
      (f := fun y : E => β (rotation x y))
      (g := fun y : E => velocity x (rotation x y)) (x := z) hβa hva
  convert he.neg using 1
  funext y
  rfl

/-- LOCAL-017 application form for any normalized parameter measure, including
Haar times the unit interval. The source rotations and iTheta are bounded
complex-linear operators on the real Hilbert complexification. -/
theorem local017_scalar_primitive (bridgeCovector : BanachHolomorphicBridge E (E →L[ℂ] ℂ))
    (β : E → E →L[ℂ] ℂ) (rotation velocity : X → E →L[ℂ] E)
    {R C K : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hrot : ∀ x z, ‖rotation x z‖ ≤ ‖z‖)
    (hvel : ∀ x z, ‖velocity x z‖ ≤ K*‖z‖)
    (hβ : ∀ z ∈ ball (0 : E) R, ‖β z‖ ≤ C*‖z‖^3)
    (hf : DifferentiableOn ℂ β (ball (0 : E) R))
    (hm : ∀ z ∈ ball (0 : E) R,
      Measurable (fun x => correctingIntegrand β rotation velocity x z)) :
    ∃ p : FormalMultilinearSeries ℂ E ℂ,
      (∀ n v, p n v = ∫ x, coefficients (correctingIntegrand β rotation velocity x) 0 n v ∂μ) ∧
      (∀ n, ‖p n‖ ≤ (Real.exp 1*(C*K*R^4))*(2*Real.exp 1/R)^n) ∧
      HasFPowerSeriesOnBall
        (fun z => ∫ x, correctingIntegrand β rotation velocity x z ∂μ) p 0
        (ENNReal.ofReal (commonRadius R)) ∧
      AnalyticOnNhd ℂ (fun z => ∫ x, correctingIntegrand β rotation velocity x z ∂μ)
        (ball 0 (commonRadius R)) :=
  scalar_average_of_analytic μ _ 0 hR (by positivity)
    (correctingIntegrand_analytic bridgeCovector β rotation velocity hrot hf) hm
    (correctingIntegrand_bound β rotation velocity hR hC hK hrot hvel hβ)

end QuantumNLS.GP05ScalarAverageR14
