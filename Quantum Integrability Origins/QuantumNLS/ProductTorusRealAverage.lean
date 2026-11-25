import QuantumNLS.ProductTorusSymmetry
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# R-4C2E4AC7, stage T9a: real weak averaging of covector families with uniform Taylor majorants

Source: `chapters/global/product_torus.tex`, "Averaging the primitive": "Its Taylor coefficients can be integrated
against Haar measure after evaluation on fixed tangent vectors. The Cauchy coefficient bounds are uniform in `θ` and
in unit tangent vectors, so these integrals define bounded multilinear coefficients with a norm-convergent Taylor
series on a smaller ball. ... This proves full dual-norm analyticity of `ᾱ` ... No Bochner integral with values in
the nonseparable space of bounded operators is needed."

This is the REAL route (integrator assignment after T8): it is a real-scalar port of the sol_ext_b GP-05 package
(`GP05WeakMeasR14.iterated_measurable`, `GP05ComplexAverageR14.analytic_average`,
`GP05CauchyMajorantsR14.canonical_expansion`, `GP05SourceHaarR14.covector_average_of_analytic`), with the complex
Cauchy coefficient bound replaced by an assumed uniform real Taylor majorant of the canonical coefficients. No
complexification and no holomorphic-to-analytic bridge is used. Only scalar evaluations are integrated.

Proved, for a probability space `X`, a real Banach space `E` and a family `F : X → E → (E →L[ℝ] ℝ)`:
* `rcoeff f a n = (n!)⁻¹ • D^n f(a)` (canonical coefficients), `norm_iteratedFDeriv_le_of_series`
  (`‖D^n f(a)‖ ≤ n! ‖p n‖` for any power series `p` of `f` at `a`);
* `iterated_measurable` (fixed-vector measurability of all derivatives, from countable difference quotients);
* `canonical_expansion` (an analytic `f` on `B(a,r)` whose canonical coefficients satisfy `‖c_n‖ rⁿ ≤ K` is the sum
  of its canonical series on `B(a,r)`; identity theorem);
* `scalarAverage`, `averagedCoefficients` (bounded multilinear dual-valued coefficients by scalar integration),
  **`real_covector_average`**: if every `F x` is analytic on `B(a,r)`, the canonical coefficients satisfy
  `‖c_n(F x)‖ rⁿ ≤ K` uniformly in `x`, and `x ↦ F x z w` is measurable, then any `Φ` with
  `Φ z w = ∫ F x z w` on `B(a,r)` has a power series at `a` of radius `r`, in the full dual norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

noncomputable section

namespace QuantumNLS.ProductTorusRealAverage

/-! ## 1. Canonical coefficients -/

section Coeff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical (normalized derivative) coefficients. -/
def rcoeff (f : E → F) (a : E) : FormalMultilinearSeries ℝ E F :=
  fun n => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f a

/-- `‖D^n f(a)‖ ≤ n! ‖p n‖` for any power series of `f` at `a`. -/
theorem norm_iteratedFDeriv_le_of_series [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries ℝ E F}
    {a : E} {ρ : ℝ≥0∞} (hp : HasFPowerSeriesOnBall f p a ρ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f a‖ ≤ n.factorial * ‖p n‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [hp.iteratedFDeriv_eq_sum_of_completeSpace v]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ σ : Equiv.Perm (Fin n), ‖p n (fun i => v (σ i))‖ ≤ ∑ _σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ :=
        Finset.sum_le_sum fun σ _ => ((p n).le_opNorm _).trans
          (le_of_eq (by rw [Equiv.prod_comp σ (fun i => ‖v i‖)]))
    _ = n.factorial * ‖p n‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem norm_rcoeff_le_of_series [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries ℝ E F}
    {a : E} {ρ : ℝ≥0∞} (hp : HasFPowerSeriesOnBall f p a ρ) (n : ℕ) : ‖rcoeff f a n‖ ≤ ‖p n‖ := by
  rw [rcoeff, norm_smul, norm_inv, RCLike.norm_natCast]
  have h := norm_iteratedFDeriv_le_of_series hp n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [inv_mul_le_iff₀ hf]
  exact h

/-- **Canonical expansion**: an analytic function on `B(a,r)` whose canonical coefficients have the majorant
`‖c_n‖ rⁿ ≤ K` is the sum of its canonical series on `B(a,r)`. -/
theorem canonical_expansion [CompleteSpace F] {f : E → F} {a : E} {r K : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℝ f (ball a r)) (hK : ∀ n, ‖rcoeff f a n‖ * r ^ n ≤ K) :
    HasFPowerSeriesOnBall f (rcoeff f a) a (ENNReal.ofReal r) := by
  rw [ENNReal.ofReal_eq_coe_nnreal hr.le]
  let r' : ℝ≥0 := NNReal.mk r hr.le
  let p := rcoeff f a
  have hrad : (r' : ℝ≥0∞) ≤ p.radius := FormalMultilinearSeries.le_radius_of_bound _ K fun n => hK n
  have hsum : AnalyticOnNhd ℝ p.sum (ball (0 : E) r') :=
    p.analyticOnNhd.mono (by
      intro z hz
      apply lt_of_lt_of_le _ hrad
      simpa only [mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
        using (ENNReal.coe_lt_coe.mpr (show ‖z‖₊ < r' from by exact_mod_cast (mem_ball_zero_iff.mp hz))))
  have hfa : AnalyticOnNhd ℝ (fun z => f (a + z)) (ball (0 : E) r') := by
    intro z hz
    have hzR : a + z ∈ ball a r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact mem_ball_zero_iff.mp hz
    exact (hf _ hzR).comp (analyticAt_const.add analyticAt_id)
  obtain ⟨q, t, hq⟩ := hf a (mem_ball_self hr)
  have heq : p.sum =ᶠ[𝓝 (0 : E)] (fun z => f (a + z)) := by
    filter_upwards [Metric.eball_mem_nhds (0 : E) hq.r_pos,
      Metric.eball_mem_nhds (0 : E) (lt_of_lt_of_le (by exact_mod_cast hr) hrad)] with z hzt hzp
    exact (p.hasSum hzp).unique (hq.hasSum_iteratedFDeriv hzt)
  have heqBall := hsum.eqOn_of_preconnected_of_eventuallyEq hfa
    (convex_ball (0 : E) (r' : ℝ)).isPreconnected (mem_ball_self hr) heq
  change HasFPowerSeriesOnBall f p a (r' : ℝ≥0∞)
  refine ⟨hrad, by exact_mod_cast hr, ?_⟩
  intro z hz
  have hzball : z ∈ ball (0 : E) r' := by
    apply mem_ball_zero_iff.mpr
    have hzNN : ‖z‖₊ < r' := by
      simpa only [mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ENNReal.coe_lt_coe] using hz
    exact_mod_cast hzNN
  rw [show f (a + z) = p.sum z from (heqBall hzball).symm]
  exact p.hasSum (lt_of_lt_of_le hz hrad)

end Coeff

/-! ## 2. Fixed-vector measurability of all derivatives -/

section Meas

variable {X E G : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem hasDerivAt_line {g : E → ℝ} {y : E} (hg : DifferentiableAt ℝ g y) (v : E) :
    HasDerivAt (fun s : ℝ => g (y + s • v)) (fderiv ℝ g y v) 0 := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hg' : HasFDerivAt g (fderiv ℝ g y) (y + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact hg.hasFDerivAt
  exact hg'.comp_hasDerivAt (0 : ℝ) hl

/-- Weak measurability of the family propagates to every fixed finite list of derivatives. -/
theorem iterated_measurable {F : X → E → G} {U : Set E}
    (L : G →L[ℝ] ℝ) (hU : IsOpen U) (hf : ∀ x, AnalyticOnNhd ℝ (F x) U)
    (hm : ∀ z ∈ U, Measurable (fun x => L (F x z)))
    (n : ℕ) (a : E) (ha : a ∈ U) (v : Fin n → E) :
    Measurable (fun x => L (iteratedFDeriv ℝ n (F x) a v)) := by
  classical
  induction n generalizing a with
  | zero => simpa using hm a ha
  | succ n ih =>
    let t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have ht0 : Tendsto t atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have htne : ∀ k, t k ≠ 0 := fun k => by
      dsimp [t]
      positivity
    have ht : Tendsto t atTop (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨ht0, .of_forall htne⟩
    have hloc : ∀ᶠ k in atTop, a + t k • v 0 ∈ U := by
      have hl := (tendsto_const_nhds (x := a)).add (ht0.smul_const (v 0))
      have hl' : Tendsto (fun k => a + t k • v 0) atTop (𝓝 a) := by simpa using hl
      exact hl'.eventually (hU.mem_nhds ha)
    let q : ℕ → X → ℝ := fun k x =>
      if a + t k • v 0 ∈ U then
        (t k)⁻¹ * (L (iteratedFDeriv ℝ n (F x) (a + t k • v 0) (Fin.tail v)) -
          L (iteratedFDeriv ℝ n (F x) a (Fin.tail v)))
      else 0
    have hq : ∀ k, Measurable (q k) := by
      intro k
      dsimp [q]
      split_ifs with hmem
      · exact measurable_const.mul ((ih _ hmem (Fin.tail v)).sub (ih a ha (Fin.tail v)))
      · exact measurable_const
    apply measurable_of_tendsto_metrizable hq
    apply tendsto_pi_nhds.mpr
    intro x
    have hdn : DifferentiableAt ℝ (iteratedFDeriv ℝ n (F x)) a :=
      ((hf x).iteratedFDeriv n a ha).differentiableAt
    have hd := hdn.hasFDerivAt.continuousMultilinear_apply_const (Fin.tail v)
    have hde := L.hasFDerivAt.comp a hd
    have hline := hasDerivAt_line hde.differentiableAt (v 0)
    have hline' : HasDerivAt
        (fun s : ℝ => L (iteratedFDeriv ℝ n (F x) (a + s • v 0) (Fin.tail v)))
        (L (iteratedFDeriv ℝ (n + 1) (F x) a v)) 0 := by
      convert hline using 1 <;> try rfl
      rw [hde.fderiv]
      rfl
    have hlim := hline'.tendsto_slope_zero.comp ht
    have hlim' : Tendsto (fun k => (t k)⁻¹ *
        (L (iteratedFDeriv ℝ n (F x) (a + t k • v 0) (Fin.tail v)) -
          L (iteratedFDeriv ℝ n (F x) a (Fin.tail v))))
        atTop (𝓝 (L (iteratedFDeriv ℝ (n + 1) (F x) a v))) := by
      simpa only [Function.comp_def, zero_add, zero_smul, add_zero, smul_eq_mul] using hlim
    apply hlim'.congr'
    filter_upwards [hloc] with k hk
    simp [q, hk]

end Meas

/-! ## 3. Weak multilinear averaging and the dual-norm series -/

section Average

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [hμ : IsProbabilityMeasure μ]

lemma scalar_integrable {n : ℕ} (a : X → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (D : ℝ) (hm : ∀ v, Measurable (fun x => a x v)) (hb : ∀ x, ‖a x‖ ≤ D) (v : Fin n → E) :
    Integrable (fun x => a x v) μ := by
  apply Integrable.of_bound (hm v).aestronglyMeasurable (D * ∏ i, ‖v i‖)
  apply Eventually.of_forall
  intro x
  exact (a x).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right (hb x) (Finset.prod_nonneg (fun i _ => norm_nonneg (v i))))

/-- Scalar multilinear average, from weak scalar measurability. -/
def scalarAverage {n : ℕ} (a : X → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (D : ℝ) (hm : ∀ v, Measurable (fun x => a x v)) (hb : ∀ x, ‖a x‖ ≤ D) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  MultilinearMap.mkContinuous
    { toFun := fun v => ∫ x, a x v ∂μ
      map_update_add' := fun v i z w => by
        simp_rw [ContinuousMultilinearMap.map_update_add]
        exact integral_add (scalar_integrable μ a D hm hb _) (scalar_integrable μ a D hm hb _)
      map_update_smul' := fun v i c z => by
        simp_rw [ContinuousMultilinearMap.map_update_smul]
        exact integral_smul c _ }
    D (fun v => by
      simpa using norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall (fun x =>
        (a x).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hb x)
          (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))))))

theorem norm_scalarAverage_le {n : ℕ} (a : X → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hm : ∀ v, Measurable (fun x => a x v)) (hb : ∀ x, ‖a x‖ ≤ D) :
    ‖scalarAverage μ a D hm hb‖ ≤ D :=
  MultilinearMap.mkContinuous_norm_le _ hD _

/-- The dual-valued averaged coefficients. -/
def averagedCoefficients (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ)
    (D : ℕ → ℝ) (hm : ∀ n v, Measurable (fun x => a n x v)) (hb : ∀ n x, ‖a n x‖ ≤ D n) :
    FormalMultilinearSeries ℝ E (E →L[ℝ] ℝ) :=
  fun n => (scalarAverage μ (a n) (D n) (hm n) (hb n)).curryRight

@[simp] theorem averagedCoefficients_apply
    (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ)
    (D : ℕ → ℝ) (hm : ∀ n v, Measurable (fun x => a n x v)) (hb : ∀ n x, ‖a n x‖ ≤ D n)
    (n : ℕ) (v : Fin n → E) (w : E) :
    averagedCoefficients μ a D hm hb n v w = ∫ x, a n x (Fin.snoc v w) ∂μ := by
  rw [averagedCoefficients, ContinuousMultilinearMap.curryRight_apply]
  rfl

theorem coefficient_radius (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ)
    (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n) (hm : ∀ n v, Measurable (fun x => a n x v))
    (hb : ∀ n x, ‖a n x‖ ≤ D n) (r : ℝ≥0) (C : ℝ) (hbound : ∀ n, D n * (r : ℝ) ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ (averagedCoefficients μ a D hm hb).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound _ C
  intro n
  have hn : ‖averagedCoefficients μ a D hm hb n‖ ≤ D n := by
    rw [averagedCoefficients, ContinuousMultilinearMap.curryRight_norm]
    exact norm_scalarAverage_le μ (a n) (D n) (hD n) (hm n) (hb n)
  exact (mul_le_mul_of_nonneg_right hn (by positivity)).trans (hbound n)

/-- Scalar Taylor representations identify the dual-valued series with the weak scalar average. -/
theorem average_sum_eq (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ)
    (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n) (hm : ∀ n v, Measurable (fun x => a n x v))
    (hb : ∀ n x, ‖a n x‖ ≤ D n) (r : ℝ≥0) (hr : 0 < r) (C : ℝ) (hbound : ∀ n, D n * (r : ℝ) ^ n ≤ C)
    (F : X → E → E → ℝ)
    (hTaylor : ∀ x z, ‖z‖ < r → ∀ w, HasSum (fun n => a n x (Fin.snoc (fun _ => z) w)) (F x z w)) :
    ∀ z : E, ‖z‖ < r → ∀ w : E, (averagedCoefficients μ a D hm hb).sum z w = ∫ x, F x z w ∂μ := by
  intro z hz w
  have hr' : 0 < (r : ℝ) := hr
  have hC : 0 ≤ C := le_trans (by simpa using hD 0) (hbound 0)
  let q : ℝ := ‖z‖ / r
  have hq : |q| < 1 := by
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) r.coe_nonneg)]
    exact (div_lt_one hr').mpr hz
  have hs : Summable (fun n : ℕ => C * q ^ n * ‖w‖) :=
    ((summable_geometric_of_abs_lt_one hq).mul_left C).mul_right ‖w‖
  have hterm : ∀ n x, ‖a n x (Fin.snoc (fun _ => z) w)‖ ≤ C * q ^ n * ‖w‖ := by
    intro n x
    have hcoeff : D n * ‖z‖ ^ n ≤ C * q ^ n := by
      calc D n * ‖z‖ ^ n = (D n * (r : ℝ) ^ n) * q ^ n := by
            dsimp [q]
            rw [div_pow]
            field_simp [ne_of_gt hr']
        _ ≤ C * q ^ n := mul_le_mul_of_nonneg_right (hbound n) (by positivity)
    let v : Fin (n + 1) → E := Fin.snoc (fun _ : Fin n => z) w
    have hprod : (∏ i, ‖v i‖) = ‖z‖ ^ n * ‖w‖ := by
      dsimp [v]
      rw [Fin.prod_univ_castSucc]
      simp
    change ‖a n x v‖ ≤ C * q ^ n * ‖w‖
    calc ‖a n x v‖ ≤ ‖a n x‖ * ∏ i, ‖v i‖ := (a n x).le_opNorm v
      _ ≤ D n * ∏ i, ‖v i‖ :=
          mul_le_mul_of_nonneg_right (hb n x) (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))
      _ = (D n * ‖z‖ ^ n) * ‖w‖ := by rw [hprod]; ring
      _ ≤ C * q ^ n * ‖w‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
  have hi : HasSum (fun n => ∫ x, a n x (Fin.snoc (fun _ => z) w) ∂μ) (∫ x, F x z w ∂μ) := by
    apply hasSum_integral_of_dominated_convergence (fun n _ => C * q ^ n * ‖w‖)
    · intro n
      exact (hm n _).aestronglyMeasurable
    · intro n
      exact Eventually.of_forall (hterm n)
    · exact Eventually.of_forall (fun _ => hs)
    · exact integrable_const _
    · exact Eventually.of_forall (fun x => hTaylor x z hz w)
  let p := averagedCoefficients μ a D hm hb
  have hrad : (r : ℝ≥0∞) ≤ p.radius := coefficient_radius μ a D hD hm hb r C hbound
  have hzrad : z ∈ Metric.eball (0 : E) p.radius := by
    apply lt_of_lt_of_le _ hrad
    have hzNN : ‖z‖₊ < r := by exact_mod_cast hz
    simpa only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm] using
      (ENNReal.coe_lt_coe.mpr hzNN)
  have hp := p.hasSum hzrad
  have hpw : HasSum (fun n => p n (fun _ => z) w) (p.sum z w) := (ContinuousLinearMap.apply ℝ ℝ w).hasSum hp
  simp only [p, averagedCoefficients_apply] at hpw
  exact hpw.unique hi

/-- Scalar coefficients of a covector family, including the final tangent argument. -/
def scalarCoefficients (F : X → E → E →L[ℝ] ℝ) (a : E) (n : ℕ) (x : X) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ :=
  (rcoeff (F x) a n).uncurryRight

/-- **Real weak covector averaging.** A covector family with a uniform canonical Taylor majorant on `B(a,r)` and
weakly measurable values has a weak average with a power series at `a` of radius `r`, in the full dual norm. -/
theorem real_covector_average [CompleteSpace E] (F : X → E → E →L[ℝ] ℝ) (Φ : E → E →L[ℝ] ℝ) (a : E)
    {r K : ℝ} (hr : 0 < r) (hK0 : 0 ≤ K) (hfa : ∀ x, AnalyticOnNhd ℝ (F x) (ball a r))
    (hm : ∀ z ∈ ball a r, ∀ w, Measurable (fun x => F x z w))
    (hK : ∀ x n, ‖rcoeff (F x) a n‖ * r ^ n ≤ K)
    (hΦ : ∀ z ∈ ball a r, ∀ w, Φ z w = ∫ x, F x z w ∂μ) :
    ∃ p : FormalMultilinearSeries ℝ E (E →L[ℝ] ℝ), HasFPowerSeriesOnBall Φ p a (ENNReal.ofReal r) := by
  let r' : ℝ≥0 := NNReal.mk r hr.le
  let D : ℕ → ℝ := fun n => K / r ^ n
  have hD : ∀ n, 0 ≤ D n := fun n => by dsimp [D]; positivity
  have hmeas : ∀ n v, Measurable (fun x => scalarCoefficients F a n x v) := by
    intro n v
    have h := iterated_measurable (ContinuousLinearMap.apply ℝ ℝ (v (Fin.last n))) isOpen_ball hfa
      (fun z hz => hm z hz _) n a (mem_ball_self hr) (Fin.init v)
    simpa [scalarCoefficients, rcoeff] using h.const_mul ((n.factorial : ℝ)⁻¹)
  have hbound : ∀ n x, ‖scalarCoefficients F a n x‖ ≤ D n := by
    intro n x
    rw [scalarCoefficients, ContinuousMultilinearMap.uncurryRight_norm]
    dsimp [D]
    rw [le_div_iff₀ (by positivity)]
    exact hK x n
  let p := averagedCoefficients μ (scalarCoefficients F a) D hmeas hbound
  have hgeo : ∀ n, D n * (r' : ℝ) ^ n ≤ K := by
    intro n
    dsimp [D, r']
    rw [div_mul_cancel₀ _ (by positivity)]
  have hTaylor : ∀ x z, ‖z‖ < r' → ∀ w,
      HasSum (fun n => scalarCoefficients F a n x (Fin.snoc (fun _ => z) w)) (F x (a + z) w) := by
    intro x z hz w
    have hz' : z ∈ eball (0 : E) r' := by
      rw [mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
      exact ENNReal.coe_lt_coe.mpr (by exact_mod_cast hz)
    have hc : HasFPowerSeriesOnBall (F x) (rcoeff (F x) a) a r' := by
      simpa only [ENNReal.ofReal_eq_coe_nnreal hr.le] using canonical_expansion hr (hfa x) (hK x)
    have hs := hc.hasSum hz'
    have hsw := (ContinuousLinearMap.apply ℝ ℝ w).hasSum hs
    simpa [scalarCoefficients] using hsw
  have havg := average_sum_eq μ (scalarCoefficients F a) D hD hmeas hbound r' hr K hgeo
    (fun x z w => F x (a + z) w) hTaylor
  have hradius := coefficient_radius μ (scalarCoefficients F a) D hD hmeas hbound r' K hgeo
  refine ⟨p, ?_⟩
  rw [ENNReal.ofReal_eq_coe_nnreal hr.le]
  refine ⟨hradius, by exact_mod_cast hr, ?_⟩
  intro z hz
  have hzr : ‖z‖ < r := by
    have : ‖z‖₊ < r' := by
      simpa only [mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ENNReal.coe_lt_coe] using hz
    exact_mod_cast this
  have hzR : a + z ∈ ball a r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hzr
  have he : p.sum z = Φ (a + z) := by
    ext w
    rw [hΦ _ hzR w]
    exact havg z hzr w
  rw [← he]
  exact p.hasSum (lt_of_lt_of_le hz hradius)

end Average

end QuantumNLS.ProductTorusRealAverage

#print axioms QuantumNLS.ProductTorusRealAverage.norm_iteratedFDeriv_le_of_series
#print axioms QuantumNLS.ProductTorusRealAverage.canonical_expansion
#print axioms QuantumNLS.ProductTorusRealAverage.iterated_measurable
#print axioms QuantumNLS.ProductTorusRealAverage.average_sum_eq
#print axioms QuantumNLS.ProductTorusRealAverage.real_covector_average
