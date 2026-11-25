import QuantumNLS.HolomorphicCauchyC1
import QuantumNLS.Ext025A2Covectors

/-! GP-05 application estimates. The missing Banach holomorphy bridge is an
explicit hypothesis. All coefficient bounds below are proved from value bounds,
in the full multilinear norm, without a quantitative bridge premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.GP05CauchyMajorantsR14
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Interface to the native holomorphic-to-analytic construction. -/
def BanachHolomorphicBridge (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] : Prop :=
  ∀ (U : Set E) (f : E → F), IsOpen U → DifferentiableOn ℂ f U → AnalyticOnNhd ℂ f U

/-- Repeated Cauchy bounds on nested balls, with a fixed positive step. -/
theorem norm_iterated_steps (n : ℕ) {f : E → F} {a : E} {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (ball a ((n+1 : ℕ)*δ)))
    (hb : ∀ x ∈ ball a ((n+1 : ℕ)*δ), ‖f x‖ ≤ M) :
    ‖iteratedFDeriv ℂ n f a‖ ≤ (2/δ)^n * M := by
  induction n generalizing a with
  | zero => simpa using hb a (mem_ball_self (by simpa using hδ))
  | succ n ih =>
    have hsub : ball a δ ⊆ ball a ((n+1+1 : ℕ)*δ) := by
      apply ball_subset_ball
      have hn : (1 : ℝ) ≤ (n+1+1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n+1+1)
      nlinarith
    have hg : DifferentiableOn ℂ (iteratedFDeriv ℂ n f) (ball a δ) :=
      (hf.iteratedFDeriv n).differentiableOn.mono hsub
    have hgB : ∀ x ∈ ball a δ, ‖iteratedFDeriv ℂ n f x‖ ≤ (2/δ)^n*M := by
      intro x hx
      have hs : ball x ((n+1 : ℕ)*δ) ⊆ ball a ((n+1+1 : ℕ)*δ) := by
        intro y hy
        have hxy : dist x a < δ := hx
        have hyx : dist y x < (n+1 : ℕ)*δ := hy
        change dist y a < _
        have ht := dist_triangle y x a
        push_cast
        push_cast at hyx
        nlinarith
      exact ih (hf.mono hs) (fun y hy => hb y (hs hy))
    have hnorm : ‖fderiv ℂ (iteratedFDeriv ℂ n f) a‖ ≤ 2*((2/δ)^n*M)/δ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      exact QuantumNLS.HolomorphicCauchyC1.norm_fderiv_apply_le hg hδ
        (Subset.refl _) hgB v
    rw [← norm_fderiv_iteratedFDeriv]
    calc
      _ ≤ 2*((2/δ)^n*M)/δ := hnorm
      _ = (2/δ)^(n+1)*M := by rw [pow_succ]; ring

/-- Actual normalized derivative coefficients of the original function. -/
def coefficients (f : E → F) (a : E) : FormalMultilinearSeries ℂ E F :=
  fun n => (n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n f a

/-- A single common value bound gives a common geometric coefficient majorant.
The factor exp(1) is independent of the function and the derivative order. -/
theorem coefficient_bound {f : E → F} {a : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hf : AnalyticOnNhd ℂ f (ball a R))
    (hb : ∀ x ∈ ball a R, ‖f x‖ ≤ M) (n : ℕ) :
    ‖coefficients f a n‖ ≤ (Real.exp 1 * M) * (2*Real.exp 1/R)^n := by
  have hn : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hδ : 0 < R/(n+1 : ℕ) := div_pos hR hn
  have hrad : (n+1 : ℕ)*(R/(n+1 : ℕ)) = R := by field_simp
  have hd := norm_iterated_steps n hδ hM (hrad.symm ▸ hf) (hrad.symm ▸ hb)
  have hfact : (0 : ℝ) < n.factorial := by positivity
  have hpow : ((n+1 : ℕ) : ℝ)^n / n.factorial ≤ Real.exp ((n+1 : ℕ) : ℝ) :=
    Real.pow_div_factorial_le_exp _ hn.le n
  have he : Real.exp ((n+1 : ℕ) : ℝ) = Real.exp 1 * (Real.exp 1)^n := by
    push_cast
    rw [Real.exp_add, show (n : ℝ) = n*1 by ring, Real.exp_nat_mul]
    ring
  rw [he] at hpow
  have hnorm : ‖coefficients f a n‖ = ‖iteratedFDeriv ℂ n f a‖ / n.factorial := by
    simp [coefficients, norm_smul, norm_inv, div_eq_mul_inv, mul_comm]
  rw [hnorm]
  calc
    _ ≤ (2/(R/(n+1 : ℕ)))^n*M/n.factorial :=
      div_le_div_of_nonneg_right hd hfact.le
    _ = (M*(2/R)^n)*(((n+1 : ℕ) : ℝ)^n/n.factorial) := by
      rw [div_div_eq_mul_div, div_pow, mul_pow]
      ring
    _ ≤ (M*(2/R)^n)*(Real.exp 1*(Real.exp 1)^n) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (Real.exp 1*M)*(2*Real.exp 1/R)^n := by simp only [div_pow, mul_pow]; ring

/-- A fixed positive radius, shared by the whole bounded family. -/
def commonRadius (R : ℝ) : ℝ := R/(2*Real.exp 1)

lemma commonRadius_pos {R : ℝ} (hR : 0 < R) : 0 < commonRadius R := by
  unfold commonRadius
  positivity

lemma commonRadius_le {R : ℝ} (hR : 0 ≤ R) : commonRadius R ≤ R := by
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  unfold commonRadius
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

lemma coefficient_radius {f : E → F} {a : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hf : AnalyticOnNhd ℂ f (ball a R))
    (hb : ∀ x ∈ ball a R, ‖f x‖ ≤ M) :
    ENNReal.ofReal (commonRadius R) ≤
      (coefficients f a).radius := by
  rw [ENNReal.ofReal_eq_coe_nnreal (commonRadius_pos hR).le]
  apply FormalMultilinearSeries.le_radius_of_bound _ (Real.exp 1*M)
  intro n
  change ‖coefficients f a n‖ * commonRadius R^n ≤ Real.exp 1*M
  calc
    ‖coefficients f a n‖ * commonRadius R^n ≤
        ((Real.exp 1*M)*(2*Real.exp 1/R)^n)*commonRadius R^n :=
      mul_le_mul_of_nonneg_right (coefficient_bound hR hM hf hb n) (pow_nonneg (commonRadius_pos hR).le n)
    _ = Real.exp 1*M := by
      rw [mul_assoc, ← mul_pow]
      have hr : (2*Real.exp 1/R)*commonRadius R = 1 := by
        unfold commonRadius
        field_simp
      rw [hr, one_pow, mul_one]

/-- The canonical coefficients represent the original function throughout the
common smaller ball. Analytic continuation supplies the common radius, rather
than a separate family of pointwise radii. -/
theorem canonical_expansion {f : E → F} {a : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hf : AnalyticOnNhd ℂ f (ball a R))
    (hb : ∀ x ∈ ball a R, ‖f x‖ ≤ M) :
    HasFPowerSeriesOnBall f (coefficients f a) a
      (ENNReal.ofReal (commonRadius R)) := by
  rw [ENNReal.ofReal_eq_coe_nnreal (commonRadius_pos hR).le]
  let r : ℝ≥0 := NNReal.mk (commonRadius R) (commonRadius_pos hR).le
  let p := coefficients f a
  have hr : (r : ℝ≥0∞) ≤ p.radius := by
    simpa only [r, p, ENNReal.ofReal_eq_coe_nnreal (commonRadius_pos hR).le] using coefficient_radius hR hM hf hb
  have hsum : AnalyticOnNhd ℂ p.sum (ball (0 : E) r) :=
    p.analyticOnNhd.mono (by
      intro z hz
      apply lt_of_lt_of_le _ hr
      simpa only [mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
        using (ENNReal.coe_lt_coe.mpr (show ‖z‖₊ < r from by exact_mod_cast (mem_ball_zero_iff.mp hz))))
  have hfa : AnalyticOnNhd ℂ (fun z => f (a+z)) (ball (0 : E) r) := by
    intro z hz
    have hzR : a+z ∈ ball a R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (mem_ball_zero_iff.mp hz).trans_le (commonRadius_le hR.le)
    exact (hf _ hzR).comp (analyticAt_const.add analyticAt_id)
  obtain ⟨q,t,hq⟩ := hf a (mem_ball_self hR)
  have heq : p.sum =ᶠ[𝓝 (0 : E)] (fun z => f (a+z)) := by
    filter_upwards [Metric.eball_mem_nhds (0 : E) hq.r_pos,
      Metric.eball_mem_nhds (0 : E) (lt_of_lt_of_le (by exact_mod_cast commonRadius_pos hR) hr)]
      with z hzt hzp
    exact (p.hasSum hzp).unique (hq.hasSum_iteratedFDeriv hzt)
  have heqBall := hsum.eqOn_of_preconnected_of_eventuallyEq hfa
    (convex_ball (0 : E) (r : ℝ)).isPreconnected (mem_ball_self (commonRadius_pos hR)) heq
  change HasFPowerSeriesOnBall f p a (r : ℝ≥0∞)
  refine ⟨hr, by exact_mod_cast commonRadius_pos hR, ?_⟩
  intro z hz
  have hzball : z ∈ ball (0 : E) r := by
    apply mem_ball_zero_iff.mpr
    have hzNN : ‖z‖₊ < r := by
      simpa only [mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm,
        ENNReal.coe_lt_coe] using hz
    exact_mod_cast hzNN
  rw [show f (a+z) = p.sum z from (heqBall hzball).symm]
  exact p.hasSum (lt_of_lt_of_le hz hr)

end QuantumNLS.GP05CauchyMajorantsR14
