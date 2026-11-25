import Mathlib
import Armstrong.Frozen.RawBeta.HasGKImproperPathIntegral38
import Armstrong.Work.RawBetaCompactIntegrability
import Armstrong.Frozen.RawBeta.GKArcSheet38
import NlsGge.GK38.IsolatingCounting
import NlsGge.GK38.PeriodicLabellingRoots
import NlsGge.GK38.AngleEndpointVariety
import NlsGge.GK38.AbelianPsiNumerator
import NlsGge.GK38.StdRootBranchesOrders
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.TauGamma
import NlsGge.GK38.TauGammaExteriorAnalytic
import NlsGge.GK38.TauGammaExterior
import NlsGge.GK38.StdRootBranchesConvergence
import NlsGge.Atomic.G2.G2046

/- G3-001 SUPPORT (assembled by proof development with build_kit.py; not semantically reviewed by its author).
   Concatenation of the compiled pieces, each in its own section, imports hoisted, #print axioms removed.
   Pieces: L1 (proof development); L4 (proof development); SHEET (proof development); L3 branch (proof development); L3 regular and full (proof development); L6 (proof development); L2 native (proof development); L5b tube (proof development); L5a localization (proof development); L5 uniform (proof development); L7 segment (proof development); assembly general (proof development). -/

section Piece00
/- G3-001 SUPPORT L1 (proof development, AUTHOR; not self-reviewed). Scalar local simple-branch coefficient
   (Pro round 9, sec. 8, local primitive). Imports Mathlib only; no hypothesis beyond the statement.
   Construction: E = dslope D a (simple factor, D = (z-a) E), q analytic nonvanishing with q^2 = E near a,
   h = f/q, H(u) = 2 * integral_0^1 h(u x^2) dx, which solves u H' + H/2 = h (proved by FTC in x),
   and R = H(z-a)/q. Then D R' + (D'/2) R = q (u H' + H/2) = f. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Parametric integral `H(u) = 2 * ∫_0^1 h(u x^2) dx`. -/
def g3001EulerH (h : ℂ → ℂ) (u : ℂ) : ℂ :=
  2 * ∫ x in (0:ℝ)..1, h (u * (x:ℂ)^2)

/-- Its formal derivative in `u`. -/
def g3001EulerD (h : ℂ → ℂ) (u : ℂ) : ℂ :=
  2 * ∫ x in (0:ℝ)..1, deriv h (u * (x:ℂ)^2) * (x:ℂ)^2

lemma g3001_norm_sq_le {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : ‖(x:ℂ)^2‖ ≤ 1 := by
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.1]
  nlinarith [hx.1, hx.2]

lemma g3001_uIoc_sub : Set.uIoc (0:ℝ) 1 ⊆ Icc (0:ℝ) 1 := by
  rw [Set.uIoc_of_le zero_le_one]
  exact Ioc_subset_Icc_self

lemma g3001_mem_ball_of_sq {r : ℝ} {u : ℂ} (hu : ‖u‖ < r) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    u * (x:ℂ)^2 ∈ ball (0:ℂ) r := by
  rw [mem_ball_zero_iff]
  have h1 : ‖(x:ℂ)^2‖ ≤ 1 := g3001_norm_sq_le hx
  calc ‖u * (x:ℂ)^2‖ = ‖u‖ * ‖(x:ℂ)^2‖ := norm_mul _ _
    _ ≤ ‖u‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ < r := by linarith

lemma g3001_contOn_comp (k : ℂ → ℂ) {r : ℝ} (hk : ContinuousOn k (ball (0:ℂ) r)) {u : ℂ}
    (hu : ‖u‖ < r) :
    ContinuousOn (fun x : ℝ => k (u * (x:ℂ)^2)) (Icc (0:ℝ) 1) := by
  refine hk.comp (Continuous.continuousOn (by fun_prop)) (fun x hx => g3001_mem_ball_of_sq hu hx)

lemma g3001_cont_pieces (h : ℂ → ℂ) {r : ℝ} (hh : DifferentiableOn ℂ h (ball (0:ℂ) r)) {u : ℂ}
    (hu : ‖u‖ < r) :
    ContinuousOn (fun x : ℝ => h (u * (x:ℂ)^2)) (Icc (0:ℝ) 1) ∧
    ContinuousOn (fun x : ℝ => deriv h (u * (x:ℂ)^2) * (x:ℂ)^2) (Icc (0:ℝ) 1) := by
  have hdh : ContinuousOn (deriv h) (ball (0:ℂ) r) :=
    (hh.analyticOnNhd isOpen_ball).deriv.continuousOn
  exact ⟨g3001_contOn_comp h hh.continuousOn hu,
    (g3001_contOn_comp (deriv h) hdh hu).mul (Continuous.continuousOn (by fun_prop))⟩

lemma g3001_hasDerivAt_integrand {h : ℂ → ℂ} {r : ℝ} (hh : DifferentiableOn ℂ h (ball (0:ℂ) r))
    {u : ℂ} (hu : ‖u‖ < r) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun v : ℂ => h (v * (t:ℂ)^2)) (deriv h (u * (t:ℂ)^2) * (t:ℂ)^2) u := by
  have hmem := g3001_mem_ball_of_sq hu ht
  have hd : HasDerivAt h (deriv h (u * (t:ℂ)^2)) (u * (t:ℂ)^2) :=
    (hh.differentiableAt (isOpen_ball.mem_nhds hmem)).hasDerivAt
  have hin : HasDerivAt (fun v : ℂ => v * (t:ℂ)^2) ((t:ℂ)^2) u := by
    simpa using (hasDerivAt_id' u).mul_const ((t:ℂ)^2)
  exact hd.comp u hin

lemma g3001_hasDerivAt_H {h : ℂ → ℂ} {r : ℝ} (hh : DifferentiableOn ℂ h (ball (0:ℂ) r))
    {u : ℂ} (hu : ‖u‖ < r) :
    HasDerivAt (g3001EulerH h) (g3001EulerD h u) u := by
  obtain ⟨ρ, huρ, hρr⟩ := exists_between hu
  have hdh : ContinuousOn (deriv h) (ball (0:ℂ) r) :=
    (hh.analyticOnNhd isOpen_ball).deriv.continuousOn
  have hdhb : ContinuousOn (deriv h) (closedBall (0:ℂ) ρ) :=
    hdh.mono (closedBall_subset_ball hρr)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) ρ).exists_bound_of_continuousOn hdhb
  have hs : ball (0:ℂ) ρ ∈ 𝓝 u :=
    isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; exact huρ)
  have hmeas : ∀ᶠ v in 𝓝 u,
      AEStronglyMeasurable (fun t : ℝ => h (v * (t:ℂ)^2)) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    filter_upwards [hs] with v hv
    have hvr : ‖v‖ < r := by
      have := mem_ball_zero_iff.mp hv
      linarith
    exact ContinuousOn.aestronglyMeasurable
      ((g3001_contOn_comp h hh.continuousOn hvr).mono g3001_uIoc_sub) measurableSet_uIoc
  have hint : IntervalIntegrable (fun t : ℝ => h (u * (t:ℂ)^2)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one (g3001_cont_pieces h hh hu).1
  have hF'meas : AEStronglyMeasurable (fun t : ℝ => deriv h (u * (t:ℂ)^2) * (t:ℂ)^2)
      (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    ContinuousOn.aestronglyMeasurable
      ((g3001_cont_pieces h hh hu).2.mono g3001_uIoc_sub) measurableSet_uIoc
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 →
      ∀ v ∈ ball (0:ℂ) ρ, ‖deriv h (v * (t:ℂ)^2) * (t:ℂ)^2‖ ≤ (fun _ : ℝ => M) t := by
    refine ae_of_all _ (fun t ht v hv => ?_)
    have htI : t ∈ Icc (0:ℝ) 1 := g3001_uIoc_sub ht
    have hv' : ‖v‖ < ρ := mem_ball_zero_iff.mp hv
    have hvt : v * (t:ℂ)^2 ∈ closedBall (0:ℂ) ρ := by
      rw [mem_closedBall_zero_iff]
      calc ‖v * (t:ℂ)^2‖ = ‖v‖ * ‖(t:ℂ)^2‖ := norm_mul _ _
        _ ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left (g3001_norm_sq_le htI) (norm_nonneg _)
        _ ≤ ρ := by linarith
    have hd := hM _ hvt
    have ht2 := g3001_norm_sq_le htI
    calc ‖deriv h (v * (t:ℂ)^2) * (t:ℂ)^2‖ = ‖deriv h (v * (t:ℂ)^2)‖ * ‖(t:ℂ)^2‖ := norm_mul _ _
      _ ≤ M * 1 := mul_le_mul hd ht2 (norm_nonneg _) (le_trans (norm_nonneg _) hd)
      _ = M := mul_one M
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 →
      ∀ v ∈ ball (0:ℂ) ρ,
        HasDerivAt (fun v : ℂ => h (v * (t:ℂ)^2)) (deriv h (v * (t:ℂ)^2) * (t:ℂ)^2) v := by
    refine ae_of_all _ (fun t ht v hv => ?_)
    have hv' : ‖v‖ < r := by
      have := mem_ball_zero_iff.mp hv
      linarith
    exact g3001_hasDerivAt_integrand hh hv' (g3001_uIoc_sub ht)
  obtain ⟨_, hD⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun v t => h (v * (t:ℂ)^2))
    (F' := fun v t => deriv h (v * (t:ℂ)^2) * (t:ℂ)^2) (x₀ := u) (s := ball (0:ℂ) ρ)
    (bound := fun _ : ℝ => M) (a := 0) (b := 1) hs hmeas hint hF'meas hbound
    intervalIntegrable_const hdiff
  unfold g3001EulerH g3001EulerD
  exact hD.const_mul 2

lemma g3001_ftc (h : ℂ → ℂ) {r : ℝ} (hh : DifferentiableOn ℂ h (ball (0:ℂ) r)) {u : ℂ}
    (hu : ‖u‖ < r) :
    ∫ x in (0:ℝ)..1, (h (u * (x:ℂ)^2) + 2 * u * (deriv h (u * (x:ℂ)^2) * (x:ℂ)^2)) = h u := by
  have hpieces := g3001_cont_pieces h hh hu
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun y : ℝ => (y:ℂ) * h (u * (y:ℂ)^2))
      (h (u * (x:ℂ)^2) + 2 * u * (deriv h (u * (x:ℂ)^2) * (x:ℂ)^2)) x := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    have hin : HasDerivAt (fun w : ℂ => u * w^2) (2 * u * (x:ℂ)) (x:ℂ) := by
      have := (hasDerivAt_pow 2 (x:ℂ)).const_mul u
      convert this using 1
      simp
      ring
    have hd : HasDerivAt h (deriv h (u * (x:ℂ)^2)) (u * (x:ℂ)^2) :=
      (hh.differentiableAt (isOpen_ball.mem_nhds (g3001_mem_ball_of_sq hu hx))).hasDerivAt
    have hk : HasDerivAt (fun w : ℂ => h (u * w^2)) (deriv h (u * (x:ℂ)^2) * (2 * u * (x:ℂ)))
        (x:ℂ) := hd.comp (x:ℂ) hin
    have hw : HasDerivAt (fun w : ℂ => w * h (u * w^2))
        (h (u * (x:ℂ)^2) + 2 * u * (deriv h (u * (x:ℂ)^2) * (x:ℂ)^2)) (x:ℂ) :=
      ((hasDerivAt_id' (x:ℂ)).mul hk).congr_deriv (by ring)
    exact hw.comp_ofReal
  have hint : IntervalIntegrable
      (fun x : ℝ => h (u * (x:ℂ)^2) + 2 * u * (deriv h (u * (x:ℂ)^2) * (x:ℂ)^2)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one
      (hpieces.1.add (continuousOn_const.mul hpieces.2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

lemma g3001_ode (h : ℂ → ℂ) {r : ℝ} (hh : DifferentiableOn ℂ h (ball (0:ℂ) r)) {u : ℂ}
    (hu : ‖u‖ < r) :
    u * g3001EulerD h u + g3001EulerH h u / 2 = h u := by
  have hpieces := g3001_cont_pieces h hh hu
  have hF := g3001_ftc h hh hu
  have i1 : IntervalIntegrable (fun x : ℝ => h (u * (x:ℂ)^2)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one hpieces.1
  have i2 : IntervalIntegrable (fun x : ℝ => 2 * u * (deriv h (u * (x:ℂ)^2) * (x:ℂ)^2)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_const.mul hpieces.2)
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul] at hF
  unfold g3001EulerD g3001EulerH
  linear_combination hF

lemma g3001_alg (u q q' H H' F f : ℂ) (hq : q ≠ 0) (hode : u * H' + H / 2 = F) (hF : F * q = f) :
    u * (q * q) * ((H' * q - H * q') / q ^ 2) +
      ((1 * (q * q) + u * (q' * q + q * q')) / 2) * (H / q) = f := by
  rw [← hF, ← hode]
  field_simp
  ring

lemma g3001_sqrt_factor (E : ℂ → ℂ) (a : ℂ) (hE : AnalyticAt ℂ E a) (hEa : E a ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q a ∧ (∀ z, q z ≠ 0) ∧ ∀ᶠ z in 𝓝 a, q z ^ 2 = E z := by
  have hq1 : E a / E a ∈ Complex.slitPlane := by
    rw [div_self hEa]
    exact Complex.one_mem_slitPlane
  have hw : AnalyticAt ℂ (fun z => E z / E a) a := hE.div analyticAt_const hEa
  have hL : AnalyticAt ℂ (fun z => Complex.log (E z / E a)) a := hw.clog hq1
  refine ⟨fun z => Complex.exp (Complex.log (E a) * (1/2)) *
      Complex.exp (Complex.log (E z / E a) * (1/2)), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul ((hL.mul analyticAt_const).cexp')
  · intro z
    exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  · have hev : ∀ᶠ z in 𝓝 a, E z / E a ∈ Complex.slitPlane :=
      hw.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hq1)
    filter_upwards [hev] with z hz
    have hz0 : E z / E a ≠ 0 := Complex.slitPlane_ne_zero hz
    have hc2 : Complex.exp (Complex.log (E a) * (1/2)) ^ 2 = E a := by
      rw [← Complex.exp_nat_mul]
      rw [show ((2:ℕ):ℂ) * (Complex.log (E a) * (1/2)) = Complex.log (E a) by push_cast; ring]
      exact Complex.exp_log hEa
    have hz2 : Complex.exp (Complex.log (E z / E a) * (1/2)) ^ 2 = E z / E a := by
      rw [← Complex.exp_nat_mul]
      rw [show ((2:ℕ):ℂ) * (Complex.log (E z / E a) * (1/2)) = Complex.log (E z / E a) by
        push_cast; ring]
      exact Complex.exp_log hz0
    calc (Complex.exp (Complex.log (E a) * (1/2)) * Complex.exp (Complex.log (E z / E a) * (1/2))) ^ 2
        = Complex.exp (Complex.log (E a) * (1/2)) ^ 2 *
          Complex.exp (Complex.log (E z / E a) * (1/2)) ^ 2 := by ring
      _ = E a * (E z / E a) := by rw [hc2, hz2]
      _ = E z := by field_simp

lemma g3001_core (D E f q : ℂ → ℂ) (a : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hDE : ∀ z, D z = (z - a) * E z) (hq0 : ∀ z, q z ≠ 0)
    (hmem : ∀ z ∈ ball a ρ, AnalyticAt ℂ f z ∧ AnalyticAt ℂ q z ∧ q z ^ 2 = E z) :
    ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (ball a ρ) ∧
      ∀ z ∈ ball a ρ, D z * deriv R z + (deriv D z / 2) * R z = f z := by
  obtain ⟨hh, hhdef⟩ : ∃ hh : ℂ → ℂ, hh = fun u => f (a + u) / q (a + u) := ⟨_, rfl⟩
  have hdist : ∀ u : ℂ, ‖u‖ < ρ → a + u ∈ ball a ρ := by
    intro u hu
    rw [mem_ball, show dist (a + u) a = ‖u‖ by rw [dist_eq_norm]; congr 1; ring]
    exact hu
  have hdiffh : DifferentiableOn ℂ hh (ball (0:ℂ) ρ) := by
    intro u hu
    have hu' := hdist u (mem_ball_zero_iff.mp hu)
    obtain ⟨hfa, hqa, -⟩ := hmem _ hu'
    have hg : DifferentiableAt ℂ (fun z => f z / q z) (a + u) :=
      hfa.differentiableAt.div hqa.differentiableAt (hq0 _)
    have hcomp := hg.comp u (((hasDerivAt_id' u).const_add a).differentiableAt)
    rw [hhdef]
    exact hcomp.differentiableWithinAt
  have hode : ∀ u ∈ ball (0:ℂ) ρ,
      u * g3001EulerD hh u + g3001EulerH hh u / 2 = hh u :=
    fun u hu => g3001_ode hh hdiffh (mem_ball_zero_iff.mp hu)
  have hRd : ∀ z ∈ ball a ρ, HasDerivAt (fun z => g3001EulerH hh (z - a) / q z)
      ((g3001EulerD hh (z - a) * q z - g3001EulerH hh (z - a) * deriv q z) / q z ^ 2) z := by
    intro z hz
    obtain ⟨-, hqa, -⟩ := hmem z hz
    have hu : ‖z - a‖ < ρ := by
      rw [← dist_eq_norm]
      exact mem_ball.mp hz
    have hH : HasDerivAt (g3001EulerH hh) (g3001EulerD hh (z - a)) (z - a) :=
      g3001_hasDerivAt_H hdiffh hu
    have hH' : HasDerivAt (fun w => g3001EulerH hh (w - a)) (g3001EulerD hh (z - a)) z :=
      HasDerivAt.comp_sub_const z a hH
    have hq' : HasDerivAt q (deriv q z) z := hqa.differentiableAt.hasDerivAt
    exact hH'.div hq' (hq0 z)
  have hRan : AnalyticOnNhd ℂ (fun z => g3001EulerH hh (z - a) / q z) (ball a ρ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (hRd z hz).differentiableAt.differentiableWithinAt) isOpen_ball
  refine ⟨fun z => g3001EulerH hh (z - a) / q z, hRan, ?_⟩
  intro z hz
  obtain ⟨-, hqz, hq2⟩ := hmem z hz
  have hDeq : D =ᶠ[𝓝 z] (fun w => (w - a) * (q w * q w)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    obtain ⟨-, -, hq2w⟩ := hmem w hw
    rw [hDE w, ← hq2w]
    ring
  have hdD : HasDerivAt (fun w => (w - a) * (q w * q w))
      (1 * (q z * q z) + (z - a) * (deriv q z * q z + q z * deriv q z)) z := by
    have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id' z).sub_const a
    have hq' : HasDerivAt q (deriv q z) z := hqz.differentiableAt.hasDerivAt
    exact h1.mul (hq'.mul hq')
  have hderivD : deriv D z = 1 * (q z * q z) + (z - a) * (deriv q z * q z + q z * deriv q z) := by
    rw [hDeq.deriv_eq, hdD.deriv]
  have hDz : D z = (z - a) * (q z * q z) := by
    rw [hDE z, ← hq2]
    ring
  have hza : a + (z - a) = z := by ring
  have hhz : hh (z - a) = f z / q z := by
    rw [hhdef]
    show f (a + (z - a)) / q (a + (z - a)) = f z / q z
    rw [hza]
  have hu : z - a ∈ ball (0:ℂ) ρ := by
    rw [mem_ball_zero_iff, ← dist_eq_norm]
    exact mem_ball.mp hz
  have hode_z := hode (z - a) hu
  have hF : hh (z - a) * q z = f z := by
    rw [hhz]
    exact div_mul_cancel₀ (f z) (hq0 z)
  rw [(hRd z hz).deriv, hderivD, hDz]
  exact g3001_alg (z - a) (q z) (deriv q z) (g3001EulerH hh (z - a)) (g3001EulerD hh (z - a))
    (hh (z - a)) (f z) (hq0 z) hode_z hF

theorem g3001_local_simple_branch_coefficient
    (D f : ℂ → ℂ) (a : ℂ)
    (hD : AnalyticAt ℂ D a) (hf : AnalyticAt ℂ f a)
    (hzero : D a = 0) (hsimple : deriv D a ≠ 0) :
  ∃ r : ℝ, 0 < r ∧ ∃ R : ℂ → ℂ,
    AnalyticOnNhd ℂ R (Metric.ball a r) ∧
    (∀ z ∈ Metric.ball a r,
      D z * deriv R z + (deriv D z / 2) * R z = f z) := by
  obtain ⟨p, hp⟩ := hD
  have hE : AnalyticAt ℂ (dslope D a) a :=
    (HasFPowerSeriesAt.has_fpower_series_dslope_fslope hp).analyticAt
  have hEa : dslope D a a ≠ 0 := by
    rw [dslope_same]
    exact hsimple
  have hDE : ∀ z, D z = (z - a) * dslope D a z := by
    intro z
    by_cases hz : z = a
    · subst hz
      simp [hzero]
    · rw [dslope_of_ne D hz, slope_def_field, hzero, sub_zero]
      field_simp [sub_ne_zero.mpr hz]
  obtain ⟨q, hqa, hq0, hqev⟩ := g3001_sqrt_factor (dslope D a) a hE hEa
  have hev : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ f z ∧ AnalyticAt ℂ q z ∧
      q z ^ 2 = dslope D a z :=
    hf.eventually_analyticAt.and (hqa.eventually_analyticAt.and hqev)
  obtain ⟨ρ, hρ0, hρ⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨R, hR, hODE⟩ := g3001_core D (dslope D a) f q a ρ hρ0 hDE hq0
    (fun z hz => hρ (Metric.mem_ball.mp hz))
  exact ⟨ρ, hρ0, R, hR, hODE⟩

end
end NlsGge.GKDefinitionDesign
end Piece00

section Piece01
/- G3-001 SUPPORT L4 (proof development, AUTHOR; not self-reviewed). Joint two-endpoint assembly for one rooted path.
   Given the one-sided limits of the first-arc integral (eps -> 0+, upper limit 1) and of the last-arc integral
   (eta -> 0+, lower limit 1 - eta), the sum with the constant middle integral has the joint improper limit on
   the filter nhdsWithin (0,0) {0 < eps, 0 < eta, eps + eta < 1}. Compact integrability is the unconditional
   theorem rawBetaPathCompactIntegrable38. No hypothesis beyond the two one-sided limits. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral

namespace NlsGge.GK38
noncomputable section

theorem g3001_joint_assembly (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (p : GKRootedPiecewisePath38 φ m) (L1 L2 : ℂ)
    (h1 : Tendsto (fun ε : ℝ => ∫ t in ε..(1:ℝ), GKRootedArcIntegrand38 n m F φ (GKPathFirst38 p) t)
      (𝓝[>] (0:ℝ)) (𝓝 L1))
    (h2 : Tendsto (fun η : ℝ =>
      ∫ t in (0:ℝ)..((1:ℝ) - η), GKRootedArcIntegrand38 n m F φ (GKPathLast38 p) t)
      (𝓝[>] (0:ℝ)) (𝓝 L2)) :
    HasGKImproperPathIntegral38 n m F φ p
      (L1 + GKPathMiddleIntegral38 n m F φ (GKPathMiddle38 p) + L2) := by
  refine ⟨rawBetaPathCompactIntegrable38 n m F φ p, ?_⟩
  let S : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}
  have hS : S ∈ 𝓝[S] ((0:ℝ), (0:ℝ)) := self_mem_nhdsWithin
  have hfst : Tendsto (fun q : ℝ × ℝ => q.1) (𝓝[S] ((0:ℝ), (0:ℝ))) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_fst.tendsto ((0:ℝ), (0:ℝ))).mono_left nhdsWithin_le_nhds
    · filter_upwards [hS] with q hq
      exact hq.1
  have hsnd : Tendsto (fun q : ℝ × ℝ => q.2) (𝓝[S] ((0:ℝ), (0:ℝ))) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_snd.tendsto ((0:ℝ), (0:ℝ))).mono_left nhdsWithin_le_nhds
    · filter_upwards [hS] with q hq
      exact hq.2.1
  have hA : Tendsto (fun q : ℝ × ℝ =>
      ∫ t in q.1..(1:ℝ), GKRootedArcIntegrand38 n m F φ (GKPathFirst38 p) t)
      (𝓝[S] ((0:ℝ), (0:ℝ))) (𝓝 L1) := h1.comp hfst
  have hB : Tendsto (fun q : ℝ × ℝ =>
      ∫ t in (0:ℝ)..((1:ℝ) - q.2), GKRootedArcIntegrand38 n m F φ (GKPathLast38 p) t)
      (𝓝[S] ((0:ℝ), (0:ℝ))) (𝓝 L2) := h2.comp hsnd
  have hsum := (hA.add_const (GKPathMiddleIntegral38 n m F φ (GKPathMiddle38 p))).add hB
  exact hsum

end
end NlsGge.GK38
end Piece01

section Piece02
/- G3-001 native sheet primitive (proof development, AUTHOR; not semantically reviewed by its author).
   Native replacement for Armstrong.Work.RawBetaRootDerivative.rawBetaSheetPrimitiveHasDerivAt38
   (REVIEW_ONLY, outside the approved closure). Same binders and conclusion; Mathlib only.
   Route: s is differentiable at t with derivative P'γ'/(2 s t), by the slope identity
   (s u - s t) = (s u^2 - s t^2)/(s u + s t) near t, where s u + s t -> 2 s t != 0. Then product rule
   and the ODE P R' + (P'/2) R = Ψ with s^2 = P∘γ. -/
set_option autoImplicit false

open Set Filter Topology

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3001_sheet_hasDerivAt {P : ℂ → ℂ} {γ s : ℝ → ℂ} {t : ℝ} {P' γ' : ℂ}
    (hγ : HasDerivAt γ γ' t) (hP : HasDerivAt P P' (γ t))
    (hsc : ContinuousAt s t) (hsn : s t ≠ 0)
    (he : (fun u => s u ^ 2) =ᶠ[𝓝 t] P ∘ γ) :
    HasDerivAt s (P' * γ' / (2 * s t)) t := by
  have hPγ : HasDerivAt (fun u => P (γ u)) (P' * γ') t := hP.comp t hγ
  have h2 : (2 * s t) ≠ 0 := mul_ne_zero two_ne_zero hsn
  have hsq0 : s t ^ 2 = P (γ t) := he.self_of_nhds
  have hsum : Tendsto (fun u => s u + s t) (𝓝 t) (𝓝 (2 * s t)) := by
    have h := hsc.tendsto.add_const (s t)
    rwa [show s t + s t = 2 * s t by ring] at h
  have hsev : ∀ᶠ u in 𝓝 t, s u + s t ≠ 0 := hsum.eventually_ne h2
  have he' : ∀ᶠ u in 𝓝 t, s u ^ 2 = P (γ u) := he
  have hall : ∀ᶠ u in 𝓝[≠] t, s u + s t ≠ 0 ∧ s u ^ 2 = P (γ u) :=
    ((hsev.and he').filter_mono nhdsWithin_le_nhds)
  have hden : Tendsto (fun u => s u + s t) (𝓝[≠] t) (𝓝 (2 * s t)) :=
    hsum.mono_left nhdsWithin_le_nhds
  have hcomb : Tendsto (fun u => slope (fun v => P (γ v)) t u / (s u + s t)) (𝓝[≠] t)
      (𝓝 (P' * γ' / (2 * s t))) :=
    (hasDerivAt_iff_tendsto_slope.mp hPγ).div hden h2
  rw [hasDerivAt_iff_tendsto_slope]
  refine hcomb.congr' ?_
  filter_upwards [hall] with u hu
  obtain ⟨hne, hsq⟩ := hu
  rw [slope_def_module, slope_def_module, Complex.real_smul, Complex.real_smul,
    ← hsq, ← hsq0, div_eq_iff hne]
  ring

theorem g3001_sheet_primitive_hasDerivAt {P Ψ R : ℂ → ℂ} {γ s : ℝ → ℂ} {t : ℝ} {P' R' γ' : ℂ}
    (hγ : HasDerivAt γ γ' t) (hP : HasDerivAt P P' (γ t))
    (hR : HasDerivAt R R' (γ t))
    (hsc : ContinuousAt s t) (hsn : s t ≠ 0)
    (he : (fun u => s u ^ 2) =ᶠ[𝓝 t] P ∘ γ)
    (hODE : P (γ t) * R' + (P' / 2) * R (γ t) = Ψ (γ t)) :
    HasDerivAt (fun u => s u * R (γ u))
      ((Ψ (γ t) / s t) * γ') t := by
  have hs := g3001_sheet_hasDerivAt hγ hP hsc hsn he
  have hsq : s t ^ 2 = P (γ t) := he.self_of_nhds
  apply (hs.mul (hR.comp t hγ)).congr_deriv
  simp only [Function.comp_apply]
  rw [← hODE, ← hsq]
  field_simp
  ring

end
end NlsGge.GKDefinitionDesign
end Piece02

section Piece03
/- G3-001 L3 BRANCH (proof development, AUTHOR; not semantically reviewed by its author).
   Last-arc endpoint limit at mu = GKArcCurve38 a 1 when perChar mu = 0 (branch case).
   Versus proof development G3001_L3_BRANCH02 (which kept the extra hypothesis hmuseg and hprim):
   (a) hmuseg is DISCHARGED from angleEndpointDetector_zero_iff38 (wiring lemmas below);
   (b) hprim is DISCHARGED: simple zero at mu (perChar_simple_endpoint_orders38, needs lamPlus != lamMinus)
       and the local primitive G3001_L1 (owner proof development, compiled module G3001_L1_RUN02).
   (c) the sheet primitive is the native G3001_SHEET02_RUN01 (no Armstrong.Work import).
   Still an explicit hypothesis: hint (integrability of the arc integrand on [0,1-eta]). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory intervalIntegral
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3001_L3_arc_props {φ : GKPotential38} {m : ℤ} (a : GKRootedC1Arc38 φ m) :
    ContinuousOn (GKArcCurve38 a) (Icc (0:ℝ) 1) ∧
    ContDiffOn ℝ 1 (GKArcCurve38 a) (Icc (0:ℝ) 1) ∧
    ContinuousOn (GKArcSheet38 a) (Icc (0:ℝ) 1) ∧
    (∀ t ∈ Icc (0:ℝ) 1, GKArcSheet38 a t ^ 2 = perChar φ.1 (GKArcCurve38 a t)) ∧
    (∀ t ∈ Ioo (0:ℝ) 1, GKArcCurve38 a t ∉ segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m)) := by
  obtain ⟨h1, h2, h3, h4, _, h6⟩ := a.2
  exact ⟨h1, h2, h3, h4, fun t ht => (h6 t ht).2⟩

theorem g3001_L3_perChar_order_ne_top (φ : PotPair) (z : ℂ) :
    analyticOrderAt (perChar φ) z ≠ ⊤ := by
  obtain ⟨U, hU, N, _, hcount⟩ := prescribed_common_counting38 φ 0
  exact counting_order_ne_top38 (hcount φ (mem_of_mem_nhds hU)).1 z

theorem g3001_L3_perChar_eventually_ne (φ : PotPair) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, perChar φ w ≠ 0 := by
  have hA : AnalyticAt ℂ (perChar φ) z := analyticOnNhd_perChar_z φ z (mem_univ _)
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (analyticOrderAt_eq_top.mpr h) (g3001_L3_perChar_order_ne_top φ z)
  · exact h

/-- A zero of order one has nonzero derivative (Mathlib: analyticOrderAt_deriv_add_one). -/
theorem g3001_L3_deriv_ne_of_order_one (f : ℂ → ℂ) (x : ℂ) (hf : AnalyticAt ℂ f x)
    (hx : f x = 0) (hord : analyticOrderAt f x = 1) : deriv f x ≠ 0 := by
  have hid := hf.analyticOrderAt_deriv_add_one
  simp only [hx, sub_zero] at hid
  rw [hord] at hid
  have hd0 : analyticOrderAt (deriv f) x = 0 := by simpa using hid
  exact (hf.deriv.analyticOrderAt_eq_zero).mp hd0

/-- Wiring (a): the head's last-arc endpoint mu = muSeq is a zero of perChar only at lamMinus or lamPlus. -/
theorem g3001_L3_mu_is_endpoint {φ : GKPotential38} {m : ℤ} (a : GKRootedC1Arc38 φ m)
    (hμ : GKArcCurve38 a 1 = muSeq φ.1 m) (hz : perChar φ.1 (GKArcCurve38 a 1) = 0) :
    GKArcCurve38 a 1 = lamMinus φ.1 m ∨ GKArcCurve38 a 1 = lamPlus φ.1 m := by
  have h0 : angleEndpointDetector38 m φ.1 = 0 := by
    unfold angleEndpointDetector38
    rw [← hμ]
    exact hz
  rw [hμ]
  exact (angleEndpointDetector_zero_iff38 φ.1 φ.2 m).mp h0

theorem g3001_L3_mu_segment {φ : GKPotential38} {m : ℤ} (a : GKRootedC1Arc38 φ m)
    (hμ : GKArcCurve38 a 1 = muSeq φ.1 m) (hz : perChar φ.1 (GKArcCurve38 a 1) = 0) :
    GKArcCurve38 a 1 ∈ segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m) := by
  rcases g3001_L3_mu_is_endpoint a hμ hz with h | h
  · rw [h]; exact left_mem_segment ℝ _ _
  · rw [h]; exact right_mem_segment ℝ _ _

/-- Discharge (b) of hprim at a branch point mu in {lamMinus, lamPlus}: local primitive via L1. -/
theorem g3001_L3_branch_prim (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (hgap : lamPlus φ.1 m ≠ lamMinus φ.1 m) (μ : ℂ) (hz : perChar φ.1 μ = 0)
    (hμ : μ = lamMinus φ.1 m ∨ μ = lamPlus φ.1 m) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (ball μ r) ∧
      ∀ z ∈ ball μ r,
        perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
          p6PsiNumerator38 n (F n) φ.1 z := by
  have hord : analyticOrderAt (perChar φ.1) μ = 1 := by
    rcases hμ with h | h
    · rw [h]; exact (perChar_simple_endpoint_orders38 φ.1 φ.2 m (Ne.symm hgap)).1
    · rw [h]; exact (perChar_simple_endpoint_orders38 φ.1 φ.2 m (Ne.symm hgap)).2
  have hD : AnalyticAt ℂ (perChar φ.1) μ := analyticOnNhd_perChar_z φ.1 μ (mem_univ _)
  have hder : deriv (perChar φ.1) μ ≠ 0 := g3001_L3_deriv_ne_of_order_one _ μ hD hz hord
  have hf : AnalyticAt ℂ (fun z => p6PsiNumerator38 n (F n) φ.1 z) μ :=
    p6PsiNumerator_entire38 n (F n) φ.1 μ (mem_univ _)
  exact g3001_local_simple_branch_coefficient (perChar φ.1) (fun z => p6PsiNumerator38 n (F n) φ.1 z)
    μ hD hf hz hder

theorem g3001_L3_branch_limit
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (a : GKRootedC1Arc38 φ m) (μ : ℂ)
    (hμ : GKArcCurve38 a 1 = μ)
    (hμseg : μ ∈ segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m))
    (hint : ∀ η : ℝ, 0 < η → η < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 (1 - η))
    (hprim : ∃ r : ℝ, 0 < r ∧ ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (ball μ r) ∧
      ∀ z ∈ ball μ r,
        perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
          p6PsiNumerator38 n (F n) φ.1 z) :
    ∃ L : ℂ, Tendsto (fun η : ℝ => ∫ t in (0:ℝ)..((1:ℝ) - η), GKRootedArcIntegrand38 n m F φ a t)
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  obtain ⟨hγc, hγd, hsc, hsq, hslit⟩ := g3001_L3_arc_props a
  obtain ⟨r, hr, R, hRan, hODE⟩ := hprim
  have hnv : ∀ᶠ z in 𝓝[≠] μ, perChar φ.1 z ≠ 0 := g3001_L3_perChar_eventually_ne φ.1 μ
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hnv)
  have hδ : 0 < min ρ r := lt_min hρ hr
  have hc : Tendsto (GKArcCurve38 a) (𝓝[Icc (0:ℝ) 1] 1) (𝓝 μ) := by
    rw [← hμ]
    exact (hγc 1 ⟨zero_le_one, le_rfl⟩).tendsto
  have hev : ∀ᶠ t in 𝓝[Icc (0:ℝ) 1] (1:ℝ), GKArcCurve38 a t ∈ ball μ (min ρ r) :=
    hc.eventually (ball_mem_nhds μ hδ)
  obtain ⟨θ, hθ, hθev⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  obtain ⟨t1, ht1pos, ht1θ, ht1one⟩ : ∃ t1 : ℝ, 0 < t1 ∧ 1 - t1 < θ ∧ t1 < 1 :=
    ⟨1 - min (θ / 2) (1 / 2), by linarith [min_le_right (θ / 2) (1 / 2)],
      by linarith [min_le_left (θ / 2) (1 / 2)],
      by linarith [lt_min (show 0 < θ / 2 by linarith) (show (0:ℝ) < 1 / 2 by norm_num)]⟩
  have hball : ∀ t ∈ Icc t1 (1:ℝ), GKArcCurve38 a t ∈ ball μ (min ρ r) := by
    intro t ht
    have hd : dist t 1 < θ := by
      rw [Real.dist_eq, abs_of_nonpos (show t - 1 ≤ 0 by linarith [ht.2])]
      linarith [ht.1]
    exact hθev hd ⟨by linarith [ht.1, ht1pos], ht.2⟩
  -- the sheet does not vanish on (t1,1)
  have hsn : ∀ t ∈ Ioo t1 (1:ℝ), GKArcSheet38 a t ≠ 0 := by
    intro t ht
    have ht01 : t ∈ Ioo (0:ℝ) 1 := ⟨lt_trans ht1pos ht.1, ht.2⟩
    have hmem := hball t ⟨ht.1.le, ht.2.le⟩
    have hne : GKArcCurve38 a t ≠ μ := by
      intro h
      apply hslit t ht01
      rw [h]
      exact hμseg
    have hdist : dist (GKArcCurve38 a t) μ < ρ :=
      lt_of_lt_of_le (mem_ball.mp hmem) (min_le_left _ _)
    have hpc : perChar φ.1 (GKArcCurve38 a t) ≠ 0 :=
      hρball hdist (Set.mem_compl_singleton_iff.mpr hne)
    intro h0
    have hs2 := hsq t ⟨ht01.1.le, ht01.2.le⟩
    rw [h0] at hs2
    exact hpc (by simpa using hs2.symm)
  have hderiv : ∀ t ∈ Ioo t1 (1:ℝ),
      HasDerivAt (fun u => GKArcSheet38 a u * R (GKArcCurve38 a u))
        (GKRootedArcIntegrand38 n m F φ a t) t := by
    intro t ht
    have ht01 : t ∈ Ioo (0:ℝ) 1 := ⟨lt_trans ht1pos ht.1, ht.2⟩
    have hIcc : Icc (0:ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht01.1 ht01.2
    have hγ : HasDerivAt (GKArcCurve38 a) (deriv (GKArcCurve38 a) t) t :=
      ((hγd.differentiableOn (by norm_num)).differentiableAt hIcc).hasDerivAt
    have hmem := hball t ⟨ht.1.le, ht.2.le⟩
    have hRball : GKArcCurve38 a t ∈ ball μ r := ball_subset_ball (min_le_right _ _) hmem
    have hP : HasDerivAt (perChar φ.1) (deriv (perChar φ.1) (GKArcCurve38 a t))
        (GKArcCurve38 a t) :=
      ((analyticOnNhd_perChar_z φ.1 (GKArcCurve38 a t) (mem_univ _)).differentiableAt).hasDerivAt
    have hR : HasDerivAt R (deriv R (GKArcCurve38 a t)) (GKArcCurve38 a t) :=
      ((hRan _ hRball).differentiableAt).hasDerivAt
    have hsc' : ContinuousAt (GKArcSheet38 a) t := hsc.continuousAt hIcc
    have he : (fun u => GKArcSheet38 a u ^ 2) =ᶠ[𝓝 t] (perChar φ.1 ∘ GKArcCurve38 a) := by
      filter_upwards [hIcc] with u hu
      exact hsq u hu
    have hODE' := hODE (GKArcCurve38 a t) hRball
    have key := g3001_sheet_primitive_hasDerivAt (P := perChar φ.1)
      (Ψ := fun z => p6PsiNumerator38 n (F n) φ.1 z) (R := R) hγ hP hR hsc'
      (hsn t ht) he hODE'
    unfold GKRootedArcIntegrand38
    exact key
  set G : ℝ → ℂ := fun u => GKArcSheet38 a u * R (GKArcCurve38 a u) with hGdef
  have hGc : ContinuousOn G (Icc t1 1) := by
    have hRc : ContinuousOn R (ball μ r) := fun x hx =>
      ((hRan x hx).continuousAt).continuousWithinAt
    have hγ' : ContinuousOn (GKArcCurve38 a) (Icc t1 1) :=
      hγc.mono (Icc_subset_Icc (le_of_lt ht1pos) le_rfl)
    have hmaps : MapsTo (GKArcCurve38 a) (Icc t1 1) (ball μ r) := fun u hu =>
      ball_subset_ball (min_le_right _ _) (hball u hu)
    exact (hsc.mono (Icc_subset_Icc (le_of_lt ht1pos) le_rfl)).mul (hRc.comp hγ' hmaps)
  -- the piece on [0,t1] is a fixed constant
  have hC0 : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 t1 := by
    have := hint (1 - t1) (by linarith) (by linarith)
    rwa [sub_sub_cancel] at this
  have hftc : ∀ η ∈ Ioo (0:ℝ) (1 - t1),
      ∫ t in (0:ℝ)..((1:ℝ) - η), GKRootedArcIntegrand38 n m F φ a t =
        (∫ t in (0:ℝ)..t1, GKRootedArcIntegrand38 n m F φ a t) + (G (1 - η) - G t1) := by
    intro η hη
    have hη1 : η < 1 := by linarith [hη.2]
    have hCη : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume t1 (1 - η) := by
      refine (hint η hη.1 hη1).mono_set (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc)
      exact Set.mem_uIcc.2 (Or.inl ⟨by linarith [ht1pos], by linarith [hη.2]⟩)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hC0 hCη
    have hcont : ContinuousOn G (Icc t1 (1 - η)) :=
      hGc.mono (Icc_subset_Icc le_rfl (by linarith [hη.1]))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith [hη.2]) hcont
      (f' := GKRootedArcIntegrand38 n m F φ a)
      (fun x hx => hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith [hη.1])⟩) hCη
    rw [← hsplit, hFTC]
  -- G is continuous at 1 from the left, along 1 - eta
  have hG1 : Tendsto (fun η : ℝ => G (1 - η)) (𝓝[>] (0:ℝ)) (𝓝 (G 1)) := by
    have h1 : Tendsto (fun η : ℝ => (1:ℝ) - η) (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have hc0 : Tendsto (fun η : ℝ => (1:ℝ) - η) (𝓝 0) (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at hc0
      exact hc0.mono_left nhdsWithin_le_nhds
    have hmaps : Tendsto (fun η : ℝ => (1:ℝ) - η) (𝓝[>] (0:ℝ)) (𝓝[Icc t1 1] 1) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨h1, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 - t1 by linarith)] with η hη
      exact ⟨by linarith [hη.2], by linarith [hη.1]⟩
    exact (hGc 1 ⟨le_of_lt ht1one, le_rfl⟩).tendsto.comp hmaps
  refine ⟨(∫ t in (0:ℝ)..t1, GKRootedArcIntegrand38 n m F φ a t) + (G 1 - G t1), ?_⟩
  refine Tendsto.congr' ?_ ((hG1.sub_const (G t1)).const_add _)
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 - t1 by linarith)] with η hη
  exact (hftc η hη).symm

end
end NlsGge.GKDefinitionDesign
end Piece03

section Piece04
/- G3-001 L3 REGULAR and FULL (proof development, AUTHOR; not semantically reviewed by its author).
   (b) Regular case perChar mu != 0: the integrand is continuous on [t1,1] (sheet nonzero there, arc C1,
       psi entire in z), hence integrable on [0,1]; the primitive is continuous at 1, so the limit exists.
       No analyticity hypothesis on F is needed (p6PsiNumerator_entire38 holds for every F).
   Final theorem g3001_last_arc_full: combines the branch case (G3001_L3BR_RUN01) and this regular case.
   Hypotheses left explicit: hgap (lamPlus != lamMinus, used only in the branch case), hμ (arc ends at muSeq),
   and hint (integrability of the arc integrand on [0,1-eta]). The head supplies hint from path compact
   integrability; that plumbing is NOT done here. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory intervalIntegral
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3001_L3_regular_limit (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (a : GKRootedC1Arc38 φ m) (hz : perChar φ.1 (GKArcCurve38 a 1) ≠ 0)
    (hint : ∀ η : ℝ, 0 < η → η < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 (1 - η)) :
    ∃ L : ℂ, Tendsto (fun η : ℝ => ∫ t in (0:ℝ)..((1:ℝ) - η), GKRootedArcIntegrand38 n m F φ a t)
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  obtain ⟨hγc, hγd, hsc, hsq, _⟩ := g3001_L3_arc_props a
  have hc : Tendsto (GKArcCurve38 a) (𝓝[Icc (0:ℝ) 1] 1) (𝓝 (GKArcCurve38 a 1)) :=
    (hγc 1 ⟨zero_le_one, le_rfl⟩).tendsto
  have hnv : ∀ᶠ t in 𝓝[Icc (0:ℝ) 1] (1:ℝ), perChar φ.1 (GKArcCurve38 a t) ≠ 0 :=
    hc.eventually ((analyticOnNhd_perChar_z φ.1 (GKArcCurve38 a 1) (mem_univ _)).continuousAt.eventually_ne hz)
  obtain ⟨θ, hθ, hθev⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hnv)
  obtain ⟨t1, ht1pos, ht1θ, ht1one⟩ : ∃ t1 : ℝ, 0 < t1 ∧ 1 - t1 < θ ∧ t1 < 1 :=
    ⟨1 - min (θ / 2) (1 / 2), by linarith [min_le_right (θ / 2) (1 / 2)],
      by linarith [min_le_left (θ / 2) (1 / 2)],
      by linarith [lt_min (show 0 < θ / 2 by linarith) (show (0:ℝ) < 1 / 2 by norm_num)]⟩
  have hgood : ∀ t ∈ Icc t1 (1:ℝ), perChar φ.1 (GKArcCurve38 a t) ≠ 0 := by
    intro t ht
    have hd : dist t 1 < θ := by
      rw [Real.dist_eq, abs_of_nonpos (show t - 1 ≤ 0 by linarith [ht.2])]
      linarith [ht.1]
    exact hθev hd ⟨by linarith [ht.1, ht1pos], ht.2⟩
  have hsn : ∀ t ∈ Icc t1 (1:ℝ), GKArcSheet38 a t ≠ 0 := by
    intro t ht h0
    have hs2 := hsq t ⟨by linarith [ht.1, ht1pos], ht.2⟩
    rw [h0] at hs2
    exact hgood t ht (by simpa using hs2.symm)
  have hpsiC : ContinuousOn (fun t => p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t)) (Icc t1 1) :=
    ((p6PsiNumerator_entire38 n (F n) φ.1).continuousOn).comp
      (hγc.mono (Icc_subset_Icc ht1pos.le le_rfl)) (mapsTo_univ _ _)
  have hsC : ContinuousOn (GKArcSheet38 a) (Icc t1 1) := hsc.mono (Icc_subset_Icc ht1pos.le le_rfl)
  have hdC : ContinuousOn (derivWithin (GKArcCurve38 a) (Icc (0:ℝ) 1)) (Icc t1 1) :=
    (hγd.continuousOn_derivWithin (uniqueDiffOn_Icc one_pos) (by norm_num)).mono
      (Icc_subset_Icc ht1pos.le le_rfl)
  have hgC : ContinuousOn (fun t => (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
      GKArcSheet38 a t) * derivWithin (GKArcCurve38 a) (Icc (0:ℝ) 1) t) (Icc t1 1) :=
    (hpsiC.div hsC hsn).mul hdC
  have hIoo : IntegrableOn (GKRootedArcIntegrand38 n m F φ a) (Ioo t1 1) := by
    refine (hgC.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro t ht
    have hIcc : Icc (0:ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds (by linarith [ht.1, ht1pos]) ht.2
    dsimp only
    unfold GKRootedArcIntegrand38
    rw [derivWithin_of_mem_nhds hIcc]
  have hIcc1 : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume t1 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt ht1one)).mpr hIoo
  have hC0 : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 t1 := by
    have := hint (1 - t1) (by linarith) (by linarith)
    rwa [sub_sub_cancel] at this
  have hI01 : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 1 :=
    hC0.trans hIcc1
  have hI01' : IntegrableOn (GKRootedArcIntegrand38 n m F φ a) (uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hI01
  have hPc : ContinuousOn (fun x : ℝ => ∫ t in (0:ℝ)..x, GKRootedArcIntegrand38 n m F φ a t)
      (uIcc (0:ℝ) 1) :=
    continuousOn_primitive_interval hI01'
  have hlim1 : Tendsto (fun η : ℝ => (1:ℝ) - η) (𝓝[>] (0:ℝ)) (𝓝[uIcc (0:ℝ) 1] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc0 : Tendsto (fun η : ℝ => (1:ℝ) - η) (𝓝 0) (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at hc0
      exact hc0.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with η hη
      rw [Set.uIcc_of_le zero_le_one]
      exact ⟨by linarith [hη.2], by linarith [hη.1]⟩
  exact ⟨_, (hPc 1 Set.right_mem_uIcc).tendsto.comp hlim1⟩

theorem g3001_last_arc_full (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (hgap : lamPlus φ.1 m ≠ lamMinus φ.1 m) (a : GKRootedC1Arc38 φ m)
    (hμ : GKArcCurve38 a 1 = muSeq φ.1 m)
    (hint : ∀ η : ℝ, 0 < η → η < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 (1 - η)) :
    ∃ L : ℂ, Tendsto (fun η : ℝ => ∫ t in (0:ℝ)..((1:ℝ) - η), GKRootedArcIntegrand38 n m F φ a t)
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  by_cases hz : perChar φ.1 (GKArcCurve38 a 1) = 0
  · exact g3001_L3_branch_limit n m F φ a (GKArcCurve38 a 1) rfl
      (g3001_L3_mu_segment a hμ hz) hint
      (g3001_L3_branch_prim n m F φ hgap (GKArcCurve38 a 1) hz (g3001_L3_mu_is_endpoint a hμ hz))
  · exact g3001_L3_regular_limit n m F φ a hz hint

end
end NlsGge.GKDefinitionDesign
end Piece04

section Piece05
/- G3-001 L6 (proof development, AUTHOR; not semantically reviewed by its author).
   CONDITIONAL lemma: from the per-endpoint factorization data of L5 (for ONE endpoint a, on the closed disc
   of radius r: perChar phi z = (z-a) H z with ||H z|| >= c0, and ||psi|| <= P), deduce the head's
   root-bound clause ||psi/canonRoot38|| <= C / sqrt||z-a|| with C = P / sqrt c0.
   Uses canonRoot_sq38 (canonRoot38^2 = perChar off the gap segments). L5 itself is NOT proved here. -/
set_option autoImplicit false

open Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3001_L6_root_bound (n : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair) (hφ : φ ∈ gkW)
    (a : ℂ) (r c0 P : ℝ) (hc0 : 0 < c0) (H : ℂ → ℂ)
    (hfac : ∀ z ∈ closedBall a r, perChar φ z = (z - a) * H z ∧ c0 ≤ ‖H z‖)
    (hψ : ∀ z ∈ closedBall a r, ‖p6PsiNumerator38 n F φ z‖ ≤ P) :
    ∀ z ∈ ball a r, (φ, z) ∈ rootDomain38 → z ≠ a →
      ‖p6PsiNumerator38 n F φ z / canonRoot38 φ z‖ ≤ (P / Real.sqrt c0) / Real.sqrt ‖z - a‖ := by
  intro z hz hrd hza
  have hz' : z ∈ closedBall a r := ball_subset_closedBall hz
  obtain ⟨hfz, hHb⟩ := hfac z hz'
  have hsq : canonRoot38 φ z ^ 2 = perChar φ z := canonRoot_sq38 φ hφ z hrd.2
  have hpos : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  have hnorm2 : ‖canonRoot38 φ z‖ ^ 2 = ‖z - a‖ * ‖H z‖ := by
    rw [← norm_pow, hsq, hfz, norm_mul]
  have hlow : c0 * ‖z - a‖ ≤ ‖canonRoot38 φ z‖ ^ 2 := by
    rw [hnorm2]
    nlinarith [hHb, hpos]
  have hsqpos2 : 0 < ‖canonRoot38 φ z‖ ^ 2 :=
    lt_of_lt_of_le (mul_pos hc0 hpos) hlow
  have hsqpos : 0 < ‖canonRoot38 φ z‖ := by
    rcases (norm_nonneg (canonRoot38 φ z)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hsqpos2
      norm_num at hsqpos2
  have hsrt : Real.sqrt c0 * Real.sqrt ‖z - a‖ ≤ ‖canonRoot38 φ z‖ := by
    rw [← Real.sqrt_mul hc0.le]
    calc Real.sqrt (c0 * ‖z - a‖) ≤ Real.sqrt (‖canonRoot38 φ z‖ ^ 2) := Real.sqrt_le_sqrt hlow
      _ = ‖canonRoot38 φ z‖ := Real.sqrt_sq (norm_nonneg _)
  have hden : 0 < Real.sqrt c0 * Real.sqrt ‖z - a‖ :=
    mul_pos (Real.sqrt_pos.mpr hc0) (Real.sqrt_pos.mpr hpos)
  have hψb := hψ z hz'
  rw [norm_div]
  calc ‖p6PsiNumerator38 n F φ z‖ / ‖canonRoot38 φ z‖ ≤ P / (Real.sqrt c0 * Real.sqrt ‖z - a‖) :=
        div_le_div₀ (le_trans (norm_nonneg _) hψb) hψb hden hsrt
    _ = (P / Real.sqrt c0) / Real.sqrt ‖z - a‖ := by rw [div_div]

end
end NlsGge.GKDefinitionDesign
end Piece05

section Piece06
/- G3-001 L2 (proof development, AUTHOR; native redo of proof development L2; not semantically reviewed by its author).
   First-arc endpoint limit at lamMinus.
   Hypotheses: arc starts at lamMinus, integrability on [eps,1] (supplied), local primitive R at lamMinus (supplied).
   v02: no gap hypothesis; the nonvanishing of perChar near a point uses the finite-order theorem
   counting_order_ne_top38 (PeriodicLabellingRoots), via prescribed_common_counting38.
   Conclusion: int_eps^1 of the arc integrand has a limit as eps -> 0+.
   Route: G(t) = sheet(t) * R(arc t) has derivative equal to the integrand on (0,t0]
   (rawBetaSheetPrimitiveHasDerivAt38), FTC on [eps,t0], G continuous at 0. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory intervalIntegral
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Arc regularity facts used by L2 (projections of the GKRootedC1Arc38 subtype). -/
theorem g3001_arc_props261 {φ : GKPotential38} {m : ℤ} (a : GKRootedC1Arc38 φ m) :
    ContinuousOn (GKArcCurve38 a) (Icc (0:ℝ) 1) ∧
    ContDiffOn ℝ 1 (GKArcCurve38 a) (Icc (0:ℝ) 1) ∧
    ContinuousOn (GKArcSheet38 a) (Icc (0:ℝ) 1) ∧
    (∀ t ∈ Icc (0:ℝ) 1, GKArcSheet38 a t ^ 2 = perChar φ.1 (GKArcCurve38 a t)) ∧
    (∀ t ∈ Ioo (0:ℝ) 1, GKArcCurve38 a t ∉ segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m)) := by
  obtain ⟨h1, h2, h3, h4, _, h6⟩ := a.2
  exact ⟨h1, h2, h3, h4, fun t ht => (h6 t ht).2⟩

/-- perChar is not identically zero near any point: its analytic order is finite. -/
theorem g3001_L2n_perChar_order_ne_top (φ : PotPair) (z : ℂ) :
    analyticOrderAt (perChar φ) z ≠ ⊤ := by
  obtain ⟨U, hU, N, _, hcount⟩ := prescribed_common_counting38 φ 0
  exact counting_order_ne_top38 (hcount φ (mem_of_mem_nhds hU)).1 z

/-- Punctured neighbourhoods of any point carry no zero of perChar. -/
theorem g3001_L2n_perChar_eventually_ne (φ : PotPair) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, perChar φ w ≠ 0 := by
  have hA : AnalyticAt ℂ (perChar φ) z := analyticOnNhd_perChar_z φ z (mem_univ _)
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (analyticOrderAt_eq_top.mpr h) (g3001_L2n_perChar_order_ne_top φ z)
  · exact h

theorem g3001_first_arc_endpoint_limit_native
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (a : GKRootedC1Arc38 φ m)
    (ha0 : GKArcCurve38 a 0 = lamMinus φ.1 m)
    (hint : ∀ ε : ℝ, 0 < ε → ε < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume ε 1)
    (hprim : ∃ r : ℝ, 0 < r ∧ ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (ball (lamMinus φ.1 m) r) ∧
      ∀ z ∈ ball (lamMinus φ.1 m) r,
        perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
          p6PsiNumerator38 n (F n) φ.1 z) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ => ∫ t in ε..(1:ℝ), GKRootedArcIntegrand38 n m F φ a t)
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  obtain ⟨hγc, hγd, hsc, hsq, hslit⟩ := g3001_arc_props261 a
  obtain ⟨r, hr, R, hRan, hODE⟩ := hprim
  set a0 := lamMinus φ.1 m with ha0def
  -- perChar has no zero in a punctured neighbourhood of a0
  have hnv : ∀ᶠ z in 𝓝[≠] a0, perChar φ.1 z ≠ 0 := g3001_L2n_perChar_eventually_ne φ.1 a0
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hnv)
  have hδ : 0 < min ρ r := lt_min hρ hr
  have hc : Tendsto (GKArcCurve38 a) (𝓝[Icc (0:ℝ) 1] 0) (𝓝 a0) := by
    rw [← ha0]
    exact (hγc 0 ⟨le_rfl, zero_le_one⟩).tendsto
  have hev : ∀ᶠ t in 𝓝[Icc (0:ℝ) 1] (0:ℝ), GKArcCurve38 a t ∈ ball a0 (min ρ r) :=
    hc.eventually (ball_mem_nhds a0 hδ)
  obtain ⟨θ, hθ, hθev⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  obtain ⟨t0, ht0, ht0θ, ht01⟩ : ∃ t0 : ℝ, 0 < t0 ∧ t0 < θ ∧ t0 < 1 :=
    ⟨min (θ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      by linarith [min_le_left (θ / 2) (1 / 2)], by linarith [min_le_right (θ / 2) (1 / 2)]⟩
  have hball : ∀ t ∈ Icc (0:ℝ) t0, GKArcCurve38 a t ∈ ball a0 (min ρ r) := by
    intro t ht
    have hd : dist t 0 < θ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2]
    exact hθev hd ⟨ht.1, ht.2.trans ht01.le⟩
  -- the sheet does not vanish on (0,t0]
  have hsn : ∀ t ∈ Ioo (0:ℝ) t0, GKArcSheet38 a t ≠ 0 := by
    intro t ht
    have ht1 : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1, lt_trans ht.2 ht01⟩
    have hmem := hball t ⟨ht.1.le, ht.2.le⟩
    have hne : GKArcCurve38 a t ≠ a0 := by
      intro h
      apply hslit t ht1
      rw [h]
      exact left_mem_segment ℝ _ _
    have hdist : dist (GKArcCurve38 a t) a0 < ρ :=
      lt_of_lt_of_le (mem_ball.mp hmem) (min_le_left _ _)
    have hpc : perChar φ.1 (GKArcCurve38 a t) ≠ 0 :=
      hρball hdist (Set.mem_compl_singleton_iff.mpr hne)
    intro h0
    have hs2 := hsq t ⟨ht1.1.le, ht1.2.le⟩
    rw [h0] at hs2
    exact hpc (by simpa using hs2.symm)
  -- derivative of G(t) = sheet(t) * R(arc t) is the integrand on (0,t0)
  have hderiv : ∀ t ∈ Ioo (0:ℝ) t0,
      HasDerivAt (fun u => GKArcSheet38 a u * R (GKArcCurve38 a u))
        (GKRootedArcIntegrand38 n m F φ a t) t := by
    intro t ht
    have ht1 : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1, lt_trans ht.2 ht01⟩
    have hIcc : Icc (0:ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht1.1 ht1.2
    have hγ : HasDerivAt (GKArcCurve38 a) (deriv (GKArcCurve38 a) t) t :=
      ((hγd.differentiableOn (by norm_num)).differentiableAt hIcc).hasDerivAt
    have hmem := hball t ⟨ht.1.le, ht.2.le⟩
    have hRball : GKArcCurve38 a t ∈ ball a0 r := ball_subset_ball (min_le_right _ _) hmem
    have hP : HasDerivAt (perChar φ.1) (deriv (perChar φ.1) (GKArcCurve38 a t))
        (GKArcCurve38 a t) :=
      ((analyticOnNhd_perChar_z φ.1 (GKArcCurve38 a t) (mem_univ _)).differentiableAt).hasDerivAt
    have hR : HasDerivAt R (deriv R (GKArcCurve38 a t)) (GKArcCurve38 a t) :=
      ((hRan _ hRball).differentiableAt).hasDerivAt
    have hsc' : ContinuousAt (GKArcSheet38 a) t := hsc.continuousAt hIcc
    have he : (fun u => GKArcSheet38 a u ^ 2) =ᶠ[𝓝 t] (perChar φ.1 ∘ GKArcCurve38 a) := by
      filter_upwards [hIcc] with u hu
      exact hsq u hu
    have hODE' := hODE (GKArcCurve38 a t) hRball
    have key := g3001_sheet_primitive_hasDerivAt (P := perChar φ.1)
      (Ψ := fun z => p6PsiNumerator38 n (F n) φ.1 z) (R := R) hγ hP hR hsc'
      (hsn t ht) he hODE'
    unfold GKRootedArcIntegrand38
    exact key
  -- G is continuous on [0,t0]
  have hGc : ContinuousOn (fun u => GKArcSheet38 a u * R (GKArcCurve38 a u)) (Icc 0 t0) := by
    have hRc : ContinuousOn R (ball a0 r) := fun x hx =>
      ((hRan x hx).continuousAt).continuousWithinAt
    have hγ' : ContinuousOn (GKArcCurve38 a) (Icc 0 t0) :=
      hγc.mono (Icc_subset_Icc le_rfl ht01.le)
    have hmaps : MapsTo (GKArcCurve38 a) (Icc 0 t0) (ball a0 r) := fun u hu =>
      ball_subset_ball (min_le_right _ _) (hball u hu)
    exact (hsc.mono (Icc_subset_Icc le_rfl ht01.le)).mul (hRc.comp hγ' hmaps)
  set G : ℝ → ℂ := fun u => GKArcSheet38 a u * R (GKArcCurve38 a u) with hGdef
  -- FTC on [eps,t0] and splitting at t0
  have hftc : ∀ ε ∈ Ioo (0:ℝ) t0,
      ∫ t in ε..(1:ℝ), GKRootedArcIntegrand38 n m F φ a t =
        (G t0 - G ε) + ∫ t in t0..(1:ℝ), GKRootedArcIntegrand38 n m F φ a t := by
    intro ε hε
    have hint_ε : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume ε t0 :=
      (hint ε hε.1 (lt_trans hε.2 ht01)).mono_set
        (Set.uIcc_subset_uIcc Set.left_mem_uIcc
          (Set.mem_uIcc.2 (Or.inl ⟨hε.2.le, ht01.le⟩)))
    have hC : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume t0 1 :=
      hint t0 ht0 ht01
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint_ε hC
    have hcont : ContinuousOn G (Icc ε t0) := hGc.mono (Icc_subset_Icc hε.1.le le_rfl)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hε.2.le hcont
      (f' := GKRootedArcIntegrand38 n m F φ a)
      (fun x hx => hderiv x ⟨lt_trans hε.1 hx.1, hx.2⟩) hint_ε
    rw [← hsplit, hFTC]
  -- limit of G at 0 from the right
  have hGlim : Tendsto G (𝓝[>] (0:ℝ)) (𝓝 (G 0)) := by
    have h0 : ContinuousWithinAt G (Icc 0 t0) 0 := hGc 0 ⟨le_rfl, ht0.le⟩
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝[Icc (0:ℝ) t0] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · exact (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT ht0] with ε hε
        exact ⟨hε.1.le, hε.2.le⟩
    exact h0.tendsto.comp hid
  refine ⟨G t0 - G 0 + ∫ t in t0..(1:ℝ), GKRootedArcIntegrand38 n m F φ a t, ?_⟩
  refine Tendsto.congr' ?_ ((tendsto_const_nhds.sub hGlim).add tendsto_const_nhds)
  filter_upwards [Ioo_mem_nhdsGT ht0] with ε hε
  exact (hftc ε hε).symm

end
end NlsGge.GKDefinitionDesign
end Piece06

section Piece07
/- G3-001 L5b generic tube lemmas (proof development, AUTHOR; not semantically reviewed by its author).
   For f continuous on an open S inside X x Y, K compact in Y and {x0} x K inside S: f is bounded above,
   resp. (f nonvanishing, K nonempty) bounded below in norm by a positive constant, on u x K for an open u
   around x0. Mathlib only (generalized_tube_lemma). -/
set_option autoImplicit false

open Set Filter Topology

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3001_tube_upper {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set (X × Y)} (hS : IsOpen S) {f : X × Y → ℂ} (hf : ContinuousOn f S)
    {x0 : X} {K : Set Y} (hK : IsCompact K) (hsub : ({x0} : Set X) ×ˢ K ⊆ S) :
    ∃ u : Set X, IsOpen u ∧ x0 ∈ u ∧ ∃ P : ℝ, ∀ x ∈ u, ∀ y ∈ K,
      (x, y) ∈ S ∧ ‖f (x, y)‖ ≤ P := by
  have hc : ContinuousOn (fun y : Y => f (x0, y)) K := by
    refine hf.comp (Continuous.continuousOn (by fun_prop)) (fun y hy => ?_)
    exact hsub ⟨rfl, hy⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  have hO : IsOpen (S ∩ (fun p => ‖f p‖) ⁻¹' Iio (C + 1)) :=
    hf.norm.isOpen_inter_preimage hS isOpen_Iio
  have hsub' : ({x0} : Set X) ×ˢ K ⊆ S ∩ (fun p => ‖f p‖) ⁻¹' Iio (C + 1) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [mem_singleton_iff] at hx
    subst hx
    exact ⟨hsub ⟨rfl, hy⟩, by simpa using lt_of_le_of_lt (hC y hy) (by linarith)⟩
  obtain ⟨u, v, hu, _, hx0u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hO hsub'
  refine ⟨u, hu, hx0u (mem_singleton x0), C + 1, fun x hx y hy => ?_⟩
  obtain ⟨h1, h2⟩ := huv (⟨hx, hKv hy⟩ : (x, y) ∈ u ×ˢ v)
  exact ⟨h1, le_of_lt h2⟩

theorem g3001_tube_lower {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set (X × Y)} (hS : IsOpen S) {f : X × Y → ℂ} (hf : ContinuousOn f S)
    (hnz : ∀ p ∈ S, f p ≠ 0)
    {x0 : X} {K : Set Y} (hK : IsCompact K) (hKne : K.Nonempty)
    (hsub : ({x0} : Set X) ×ˢ K ⊆ S) :
    ∃ u : Set X, IsOpen u ∧ x0 ∈ u ∧ ∃ e : ℝ, 0 < e ∧ ∀ x ∈ u, ∀ y ∈ K,
      (x, y) ∈ S ∧ e ≤ ‖f (x, y)‖ := by
  have hc : ContinuousOn (fun y : Y => ‖f (x0, y)‖) K := by
    refine (hf.comp (Continuous.continuousOn (by fun_prop)) (fun y hy => ?_)).norm
    exact hsub ⟨rfl, hy⟩
  obtain ⟨y0, hy0, hmin⟩ := hK.exists_isMinOn hKne hc
  have he1 : 0 < ‖f (x0, y0)‖ := norm_pos_iff.mpr (hnz _ (hsub ⟨rfl, hy0⟩))
  have hO : IsOpen (S ∩ (fun p => ‖f p‖) ⁻¹' Ioi (‖f (x0, y0)‖ / 2)) :=
    hf.norm.isOpen_inter_preimage hS isOpen_Ioi
  have hsub' : ({x0} : Set X) ×ˢ K ⊆ S ∩ (fun p => ‖f p‖) ⁻¹' Ioi (‖f (x0, y0)‖ / 2) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [mem_singleton_iff] at hx
    subst hx
    refine ⟨hsub ⟨rfl, hy⟩, ?_⟩
    have := hmin hy
    simp only [mem_setOf_eq] at this
    show ‖f (x, y0)‖ / 2 < ‖f (x, y)‖
    linarith
  obtain ⟨u, v, hu, _, hx0u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hO hsub'
  refine ⟨u, hu, hx0u (mem_singleton x0), ‖f (x0, y0)‖ / 2, by linarith, fun x hx y hy => ?_⟩
  obtain ⟨h1, h2⟩ := huv (⟨hx, hKv hy⟩ : (x, y) ∈ u ×ˢ v)
  exact ⟨h1, le_of_lt h2⟩

end
end NlsGge.GKDefinitionDesign
end Piece07

section Piece08
/- G3-001 L5a (proof development, AUTHOR; not semantically reviewed by its author).
   Local uniform separation and localization of the band edges lamMinus, lamPlus at a non-collapsed potential.
   No continuity of the individual labels is used: only the symmetric data tauN (mean) and gamma2 (squared gap),
   which are analytic on gkW (tauN_analytic, gamma2_analytic) and equal (lamPlus+lamMinus)/2 and
   (lamPlus-lamMinus)^2 there (tauN_value38, gamma2_value38).
   Conclusion: on an open neighbourhood U of phi0, |gap phi| >= |gap phi0|/2 and every endpoint of phi is
   within eps of an endpoint of phi0. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3001_L5a_pair_close (τ τ0 g g0 : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hτ : ‖τ - τ0‖ < ε / 2) (hγ : ‖g ^ 2 - g0 ^ 2‖ < ε ^ 2) :
    (‖(τ - g / 2) - (τ0 - g0 / 2)‖ < ε ∧ ‖(τ + g / 2) - (τ0 + g0 / 2)‖ < ε) ∨
    (‖(τ - g / 2) - (τ0 + g0 / 2)‖ < ε ∧ ‖(τ + g / 2) - (τ0 - g0 / 2)‖ < ε) := by
  have hprod : ‖g - g0‖ * ‖g + g0‖ < ε ^ 2 := by
    rw [← norm_mul]
    have : (g - g0) * (g + g0) = g ^ 2 - g0 ^ 2 := by ring
    rw [this]; exact hγ
  have hcase : ‖g - g0‖ < ε ∨ ‖g + g0‖ < ε := by
    by_contra h
    push_neg at h
    nlinarith [h.1, h.2, norm_nonneg (g - g0), norm_nonneg (g + g0)]
  have n1 : ∀ x y : ℂ, ‖x - y / 2‖ ≤ ‖x‖ + ‖y‖ / 2 := fun x y => by
    calc ‖x - y / 2‖ ≤ ‖x‖ + ‖y / 2‖ := norm_sub_le _ _
      _ = ‖x‖ + ‖y‖ / 2 := by rw [norm_div]; norm_num
  have n2 : ∀ x y : ℂ, ‖x + y / 2‖ ≤ ‖x‖ + ‖y‖ / 2 := fun x y => by
    calc ‖x + y / 2‖ ≤ ‖x‖ + ‖y / 2‖ := norm_add_le _ _
      _ = ‖x‖ + ‖y‖ / 2 := by rw [norm_div]; norm_num
  rcases hcase with h | h
  · left
    constructor
    · have e : (τ - g / 2) - (τ0 - g0 / 2) = (τ - τ0) - (g - g0) / 2 := by ring
      rw [e]; linarith [n1 (τ - τ0) (g - g0)]
    · have e : (τ + g / 2) - (τ0 + g0 / 2) = (τ - τ0) + (g - g0) / 2 := by ring
      rw [e]; linarith [n2 (τ - τ0) (g - g0)]
  · right
    constructor
    · have e : (τ - g / 2) - (τ0 + g0 / 2) = (τ - τ0) - (g + g0) / 2 := by ring
      rw [e]; linarith [n1 (τ - τ0) (g + g0)]
    · have e : (τ + g / 2) - (τ0 - g0 / 2) = (τ - τ0) + (g + g0) / 2 := by ring
      rw [e]; linarith [n2 (τ - τ0) (g + g0)]

theorem g3001_L5a_endpoint_localization (m : ℤ) (φ0 : PotPair) (hφ0 : φ0 ∈ gkW)
    (hgap : lamPlus φ0 m - lamMinus φ0 m ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PotPair, IsOpen U ∧ φ0 ∈ U ∧ U ⊆ gkW ∧
      ∀ φ ∈ U, ‖lamPlus φ0 m - lamMinus φ0 m‖ / 2 ≤ ‖lamPlus φ m - lamMinus φ m‖ ∧
        ∀ a ∈ ({lamMinus φ m, lamPlus φ m} : Set ℂ),
          ∃ a0 ∈ ({lamMinus φ0 m, lamPlus φ0 m} : Set ℂ), ‖a - a0‖ < ε := by
  have hτc : ContinuousAt (fun φ => tauN φ m) φ0 := (tauN_analytic m φ0 hφ0).continuousAt
  have hγc : ContinuousAt (fun φ => gamma2 φ m) φ0 := (gamma2_analytic m φ0 hφ0).continuousAt
  set g0 : ℂ := lamPlus φ0 m - lamMinus φ0 m with hg0def
  have hg0 : 0 < ‖g0‖ := norm_pos_iff.mpr hgap
  have hγ0 : gamma2 φ0 m = g0 ^ 2 := gamma2_value38 φ0 hφ0 m
  have hτe : ∀ᶠ φ in 𝓝 φ0, ‖tauN φ m - tauN φ0 m‖ < ε / 2 := by
    filter_upwards [hτc.eventually (Metric.ball_mem_nhds _ (half_pos hε))] with φ hφ
    rwa [dist_eq_norm] at hφ
  have hγe : ∀ᶠ φ in 𝓝 φ0, ‖gamma2 φ m - gamma2 φ0 m‖ < min (ε ^ 2) (3 / 4 * ‖g0‖ ^ 2) := by
    have hpos : 0 < min (ε ^ 2) (3 / 4 * ‖g0‖ ^ 2) :=
      lt_min (by positivity) (by positivity)
    filter_upwards [hγc.eventually (Metric.ball_mem_nhds _ hpos)] with φ hφ
    rwa [dist_eq_norm] at hφ
  have hgk : ∀ᶠ φ in 𝓝 φ0, φ ∈ gkW := isOpen_gkW.mem_nhds hφ0
  obtain ⟨U, hU, hUo, hφ0U⟩ := _root_.eventually_nhds_iff.mp (hτe.and (hγe.and hgk))
  refine ⟨U, hUo, hφ0U, fun φ hφ => (hU φ hφ).2.2, fun φ hφ => ?_⟩
  obtain ⟨hτ, hγ, hgkφ⟩ := hU φ hφ
  set g : ℂ := lamPlus φ m - lamMinus φ m with hgdef
  have hγφ : gamma2 φ m = g ^ 2 := gamma2_value38 φ hgkφ m
  have hτφ : tauN φ m = (lamPlus φ m + lamMinus φ m) / 2 := tauN_value38 φ hgkφ m
  have hτ0 : tauN φ0 m = (lamPlus φ0 m + lamMinus φ0 m) / 2 := tauN_value38 φ0 hφ0 m
  have hdiff : ‖g ^ 2 - g0 ^ 2‖ < min (ε ^ 2) (3 / 4 * ‖g0‖ ^ 2) := by
    rw [← hγφ, ← hγ0]; exact hγ
  constructor
  · have h1 : ‖g ^ 2 - g0 ^ 2‖ < 3 / 4 * ‖g0‖ ^ 2 := lt_of_lt_of_le hdiff (min_le_right _ _)
    have h2 : ‖g0 ^ 2‖ ≤ ‖g ^ 2‖ + ‖g ^ 2 - g0 ^ 2‖ := by
      have := norm_sub_norm_le (g0 ^ 2) (g ^ 2)
      rw [norm_sub_rev] at this
      linarith
    rw [norm_pow, norm_pow] at h2
    by_contra hcon
    push_neg at hcon
    nlinarith [norm_nonneg g]
  · have hclose := g3001_L5a_pair_close (tauN φ m) (tauN φ0 m) g g0 ε hε hτ
      (lt_of_lt_of_le hdiff (min_le_left _ _))
    have eM : tauN φ m - g / 2 = lamMinus φ m := by rw [hτφ, hgdef]; ring
    have eP : tauN φ m + g / 2 = lamPlus φ m := by rw [hτφ, hgdef]; ring
    have eM0 : tauN φ0 m - g0 / 2 = lamMinus φ0 m := by rw [hτ0, hg0def]; ring
    have eP0 : tauN φ0 m + g0 / 2 = lamPlus φ0 m := by rw [hτ0, hg0def]; ring
    rw [eM, eP, eM0, eP0] at hclose
    intro a ha
    rcases ha with rfl | ha
    · rcases hclose with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact ⟨_, Or.inl rfl, h1⟩
      · exact ⟨_, Or.inr rfl, h1⟩
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      rcases hclose with ⟨_, h1⟩ | ⟨_, h1⟩
      · exact ⟨_, Or.inr rfl, h1⟩
      · exact ⟨_, Or.inl rfl, h1⟩

end
end NlsGge.GKDefinitionDesign
end Piece08

section Piece09
/- G3-001 L5 (proof development, AUTHOR; not semantically reviewed by its author).
   Uniform endpoint factorization on a neighbourhood V of phi0 (head conjunct 2, data for L6).
   Route: perChar phi z = (z-a) * (-4 (z-b) E phi z) with E = exteriorFactor38 phi m jointly analytic and
   nonvanishing on V1 x ball (C m) (R m) (local isolating family); band edges stay within eps of those of phi0
   (L5a, via tauN/gamma2 only); tube lemmas give uniform lower bound of |E| and upper bound of |psi| on
   V x K, K = cthickening of the two edges of phi0 inside the isolating disc. F analytic on the open W, W in gkW. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3001_L5_pair_factor (m : ℤ) (φ : PotPair) (a b : ℂ)
    (hab : (a = lamMinus φ m ∧ b = lamPlus φ m) ∨ (a = lamPlus φ m ∧ b = lamMinus φ m)) (z : ℂ) :
    perChar φ z = (z - a) * (-4 * (z - b) * exteriorFactor38 φ m z) := by
  rw [exterior_perChar_factor38 φ m z]
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring

theorem g3001_L5_uniform (n m : ℤ) (W : Set PotPair) (hWo : IsOpen W) (hWg : W ⊆ gkW)
    (F : PotPair → P2Space38 n) (hF : AnalyticOnNhd ℂ F W)
    (φ0 : PotPair) (hφ0 : φ0 ∈ W) (hgap : lamPlus φ0 m - lamMinus φ0 m ≠ 0) :
    ∃ V : Set PotPair, IsOpen V ∧ φ0 ∈ V ∧ V ⊆ W ∧ ∃ r c0 P : ℝ, 0 < r ∧ 0 < c0 ∧ 0 < P ∧
      ∀ φ ∈ V, lamPlus φ m - lamMinus φ m ≠ 0 ∧
        ∀ a ∈ ({lamMinus φ m, lamPlus φ m} : Set ℂ),
          (∃ H : ℂ → ℂ, ∀ z ∈ closedBall a r, perChar φ z = (z - a) * H z ∧ c0 ≤ ‖H z‖) ∧
          ∀ z ∈ closedBall a r, ‖p6PsiNumerator38 n F φ z‖ ≤ P := by
  have hφ0g : φ0 ∈ gkW := hWg hφ0
  -- local isolating family
  obtain ⟨V1, hV1n, hV1g, hV1o, _, C, R, hf⟩ := local_isolatingFamily φ0 hφ0g
  have hφ0V1 : φ0 ∈ V1 := mem_of_mem_nhds hV1n
  obtain ⟨c, N, _, hs⟩ := hf φ0 hφ0V1
  have hseg := (hs.1 m).1
  set Z0 : Set ℂ := {lamMinus φ0 m, lamPlus φ0 m} with hZ0
  have hZD : Z0 ⊆ ball (C m) (R m) := by
    intro z hz
    rcases hz with rfl | hz
    · exact hseg (left_mem_segment ℝ _ _)
    · rw [mem_singleton_iff] at hz; subst hz; exact hseg (right_mem_segment ℝ _ _)
  have hZc : IsCompact Z0 := (Set.toFinite Z0).isCompact
  obtain ⟨ε0, hε0, hKD⟩ := hZc.exists_cthickening_subset_open isOpen_ball hZD
  set K : Set ℂ := cthickening ε0 Z0 with hKdef
  have hKc : IsCompact K := hZc.cthickening
  have hKne : K.Nonempty := ⟨lamMinus φ0 m, self_subset_cthickening _ (Or.inl rfl)⟩
  -- lower bound for the exterior factor
  have hEan := exterior_joint_analytic38 V1 C R hV1o hV1g (fun φ hφ => hf φ hφ) m
  have hsubE : ({φ0} : Set PotPair) ×ˢ K ⊆ V1 ×ˢ ball (C m) (R m) := fun p hp =>
    ⟨by rw [mem_singleton_iff.mp hp.1]; exact hφ0V1, hKD hp.2⟩
  obtain ⟨uE, huEo, hφ0uE, eE, heE, huE⟩ := g3001_tube_lower
    (f := fun p : PotPair × ℂ => exteriorFactor38 p.1 m p.2)
    (hV1o.prod isOpen_ball) hEan.continuousOn
    (fun p hp => exterior_nonzero_in_disc38 p.1 C R (hf p.1 hp.1) m p.2 hp.2)
    hKc hKne hsubE
  -- upper bound for psi
  have hψan := p6PsiNumerator_joint_analytic38 n W F hF
  have hsubP : ({φ0} : Set PotPair) ×ˢ K ⊆ W ×ˢ (univ : Set ℂ) := fun p hp =>
    ⟨by rw [mem_singleton_iff.mp hp.1]; exact hφ0, mem_univ _⟩
  obtain ⟨uP, huPo, hφ0uP, P0, huP⟩ := g3001_tube_upper
    (f := fun p : PotPair × ℂ => p6PsiNumerator38 n F p.1 p.2)
    (hWo.prod isOpen_univ) hψan.continuousOn hKc hsubP
  -- localization of the band edges
  have hg0pos : 0 < ‖lamPlus φ0 m - lamMinus φ0 m‖ := norm_pos_iff.mpr hgap
  obtain ⟨U, hUo, hφ0U, _, hU⟩ :=
    g3001_L5a_endpoint_localization m φ0 hφ0g hgap (ε0 / 2) (half_pos hε0)
  set g0 : ℝ := ‖lamPlus φ0 m - lamMinus φ0 m‖ with hg0def
  refine ⟨U ∩ uE ∩ uP ∩ W, (((hUo.inter huEo).inter huPo).inter hWo),
    ⟨⟨⟨hφ0U, hφ0uE⟩, hφ0uP⟩, hφ0⟩, fun φ hφ => hφ.2, min (ε0 / 2) (g0 / 4), g0 * eE, max P0 1,
    lt_min (half_pos hε0) (by linarith), mul_pos hg0pos heE, lt_max_of_lt_right one_pos, ?_⟩
  intro φ hφ
  obtain ⟨⟨⟨hφU, hφE⟩, hφP⟩, hφW⟩ := hφ
  obtain ⟨hgapφ, hends⟩ := hU φ hφU
  have hgapne : lamPlus φ m - lamMinus φ m ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hgapφ)
  refine ⟨hgapne, fun a ha => ?_⟩
  obtain ⟨a0, ha0, hdist⟩ := hends a ha
  have hball : ∀ z ∈ closedBall a (min (ε0 / 2) (g0 / 4)), z ∈ K := by
    intro z hz
    have h1 : dist z a ≤ min (ε0 / 2) (g0 / 4) := mem_closedBall.mp hz
    have h2 : dist z a ≤ ε0 / 2 := h1.trans (min_le_left _ _)
    have h3 : dist a a0 < ε0 / 2 := by rwa [dist_eq_norm]
    exact mem_cthickening_of_dist_le z a0 ε0 Z0 ha0 (by
      have := dist_triangle z a a0
      linarith)
  obtain ⟨b, hab, hnab⟩ : ∃ b : ℂ, ((a = lamMinus φ m ∧ b = lamPlus φ m) ∨
      (a = lamPlus φ m ∧ b = lamMinus φ m)) ∧ ‖a - b‖ = ‖lamPlus φ m - lamMinus φ m‖ := by
    rcases ha with rfl | ha
    · exact ⟨lamPlus φ m, Or.inl ⟨rfl, rfl⟩, norm_sub_rev _ _⟩
    · rw [mem_singleton_iff] at ha
      subst ha
      exact ⟨lamMinus φ m, Or.inr ⟨rfl, rfl⟩, rfl⟩
  refine ⟨⟨fun z => -4 * (z - b) * exteriorFactor38 φ m z, fun z hz => ⟨?_, ?_⟩⟩, fun z hz => ?_⟩
  · exact g3001_L5_pair_factor m φ a b hab z
  · have hzK := hball z hz
    have hE := (huE φ hφE z hzK).2
    have hzr : ‖z - a‖ ≤ g0 / 4 :=
      (mem_closedBall_iff_norm.mp hz).trans (min_le_right _ _)
    have hzb : g0 / 4 ≤ ‖z - b‖ := by
      have h1 : ‖a - b‖ ≤ ‖a - z‖ + ‖z - b‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub a z b
      rw [norm_sub_rev a z] at h1
      linarith
    show g0 * eE ≤ ‖-4 * (z - b) * exteriorFactor38 φ m z‖
    rw [norm_mul, norm_mul]
    have h4 : ‖(-4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    have h5 : 0 ≤ ‖exteriorFactor38 φ m z‖ := norm_nonneg _
    nlinarith [mul_le_mul hzb hE heE.le (norm_nonneg _)]
  · exact (((huP φ hφP z (hball z hz)).2).trans (le_max_left _ _))

end
end NlsGge.GKDefinitionDesign
end Piece09

section Piece10
/- G3-001 L7 (proof development, AUTHOR; not semantically reviewed by its author).
   Straight-segment clause of the head: given the pointwise root bound (the L6 conclusion at the endpoint a)
   and that the open segment (a + t d), t in (0,1), lies in rootDomain38, the integrand
   d * Psi(a+td)/canonRoot38 phi (a+td) is integrable on Ioo 0 1 and bounded by C sqrt|d| / sqrt t.
   Measurability: t -> canonRoot38 phi (a+td) is continuous on Ioo 0 1 (canonRoot_analytic38 on rootDomain38);
   the denominator is nonzero off the gap segments (canonRoot_ne_zero38). Psi is an arbitrary continuous function
   (psi is entire: p6PsiNumerator_entire38). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3001_L7_segment (φ : PotPair) (hφ : φ ∈ gkW) (Ψ : ℂ → ℂ) (hΨ : Continuous Ψ)
    (a d : ℂ) (r C : ℝ) (hd : 0 < ‖d‖) (hdr : ‖d‖ < r)
    (hbound : ∀ z ∈ ball a r, (φ, z) ∈ rootDomain38 → z ≠ a →
      ‖Ψ z / canonRoot38 φ z‖ ≤ C / Real.sqrt ‖z - a‖)
    (hdom : ∀ t ∈ Ioo (0 : ℝ) 1, (φ, a + (t : ℂ) * d) ∈ rootDomain38) :
    IntegrableOn (fun t : ℝ => d * Ψ (a + (t : ℂ) * d) / canonRoot38 φ (a + (t : ℂ) * d))
      (Ioo (0 : ℝ) 1) ∧
    ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖d * Ψ (a + (t : ℂ) * d) / canonRoot38 φ (a + (t : ℂ) * d)‖ ≤
        C * Real.sqrt ‖d‖ / Real.sqrt t := by
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖d * Ψ (a + (t : ℂ) * d) / canonRoot38 φ (a + (t : ℂ) * d)‖ ≤
        C * Real.sqrt ‖d‖ / Real.sqrt t := by
    intro t ht
    have hnorm : ‖a + (t : ℂ) * d - a‖ = t * ‖d‖ := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
    have hzne : a + (t : ℂ) * d ≠ a := by
      intro h
      have : ‖a + (t : ℂ) * d - a‖ = 0 := by rw [h, sub_self, norm_zero]
      rw [hnorm] at this
      exact absurd this (mul_pos ht.1 hd).ne'
    have hzb : a + (t : ℂ) * d ∈ ball a r := by
      rw [mem_ball, dist_eq_norm, hnorm]
      nlinarith [ht.2, ht.1]
    have hb := hbound _ hzb (hdom t ht) hzne
    rw [hnorm, Real.sqrt_mul ht.1.le] at hb
    rw [mul_div_assoc, norm_mul]
    have hsd : 0 < Real.sqrt ‖d‖ := Real.sqrt_pos.mpr hd
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
    have hdd : ‖d‖ = Real.sqrt ‖d‖ * Real.sqrt ‖d‖ := (Real.mul_self_sqrt hd.le).symm
    calc ‖d‖ * ‖Ψ (a + (t : ℂ) * d) / canonRoot38 φ (a + (t : ℂ) * d)‖
        ≤ ‖d‖ * (C / (Real.sqrt t * Real.sqrt ‖d‖)) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = C * Real.sqrt ‖d‖ / Real.sqrt t := by
          have key : ∀ s t' : ℝ, 0 < s → 0 < t' → (s * s) * (C / (t' * s)) = C * s / t' := by
            intro s t' hs ht'
            field_simp
          rw [← key _ _ hsd hst, ← hdd]
  refine ⟨?_, hpt⟩
  -- the dominating function is integrable on (0,1)
  have hg : IntegrableOn (fun t : ℝ => C * Real.sqrt ‖d‖ * (t ^ (-(1 / 2 : ℝ)))) (Ioo (0 : ℝ) 1) := by
    have h1 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h2 := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h1
    exact h2.const_mul _
  have hge : ∀ t ∈ Ioo (0 : ℝ) 1,
      C * Real.sqrt ‖d‖ * (t ^ (-(1 / 2 : ℝ))) = C * Real.sqrt ‖d‖ / Real.sqrt t := by
    intro t ht
    have hh : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
      rw [Real.rpow_neg ht.1.le, Real.sqrt_eq_rpow]
    rw [hh, div_eq_mul_inv]
  have hg' : IntegrableOn (fun t : ℝ => C * Real.sqrt ‖d‖ / Real.sqrt t) (Ioo (0 : ℝ) 1) :=
    hg.congr_fun hge measurableSet_Ioo
  -- measurability
  have hcurve : ContinuousOn (fun t : ℝ => canonRoot38 φ (a + (t : ℂ) * d)) (Ioo (0 : ℝ) 1) := by
    have hc := canonRoot_analytic38.continuousOn.comp
      (f := fun t : ℝ => (φ, a + (t : ℂ) * d))
      (Continuous.continuousOn (by fun_prop)) (fun t ht => hdom t ht)
    exact hc
  have hnz : ∀ t ∈ Ioo (0 : ℝ) 1, canonRoot38 φ (a + (t : ℂ) * d) ≠ 0 :=
    fun t ht => canonRoot_ne_zero38 φ hφ _ (hdom t ht).2
  have hΨc : ContinuousOn (fun t : ℝ => Ψ (a + (t : ℂ) * d)) (Ioo (0 : ℝ) 1) :=
    (hΨ.comp (by fun_prop)).continuousOn
  have hfc : ContinuousOn (fun t : ℝ => d * Ψ (a + (t : ℂ) * d) / canonRoot38 φ (a + (t : ℂ) * d))
      (Ioo (0 : ℝ) 1) :=
    (continuousOn_const.mul hΨc).div hcurve hnz
  refine Integrable.mono' hg' (hfc.aestronglyMeasurable measurableSet_Ioo) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioo hpt

end
end NlsGge.GKDefinitionDesign
end Piece10

section Piece11
/- G3-001 ASSEMBLY, general form (proof development, AUTHOR; not semantically reviewed by its author).
   Pro round 9 sec. 8 head, with the source objects abstracted: W open in gkW (sourceW), F with F k analytic on W
   (sourceF; sourceFamily.W_open, W_gk, F_analytic), phi0 : GKPotential38 with phi0.1 in W (sourceGK phi0),
   psi n phi z written out as p6PsiNumerator38 n (F n) phi z (definitional unfolding of psi).
   Conjunct 1: L2 (first arc, native) + L3 (last arc) + L4 (joint), hints from compact integrability, hprim via L1.
   Conjunct 2: L5 (uniform factorization) -> L6 (root bound) -> L7 (segment integrability and bound). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory intervalIntegral
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3001_head_general (n m : ℤ) (W : Set PotPair) (hWo : IsOpen W) (hWg : W ⊆ gkW)
    (F : (k : ℤ) → PotPair → P2Space38 k) (hFan : ∀ k : ℤ, AnalyticOnNhd ℂ (F k) W)
    (φ0 : GKPotential38) (hφ0W : φ0.1 ∈ W) (hgap : gap φ0.1 m ≠ 0) :
    (∀ p : GKRootedPiecewisePath38 φ0 m, ∃ b : ℂ,
      HasGKImproperPathIntegral38 n m F φ0 p b) ∧
    ∃ V : Set PotPair, ∃ C r : ℝ,
      IsOpen V ∧ φ0.1 ∈ V ∧ V ⊆ W ∧ 0 < C ∧ 0 < r ∧
      ∀ φ ∈ V, gap φ m ≠ 0 ∧
        ∀ a ∈ ({lamMinus φ m, lamPlus φ m} : Set ℂ),
          (∀ z ∈ ball a r, (φ, z) ∈ rootDomain38 → z ≠ a →
            ‖p6PsiNumerator38 n (F n) φ z / canonRoot38 φ z‖ ≤ C / Real.sqrt ‖z - a‖) ∧
          (∀ d : ℂ, 0 < ‖d‖ → ‖d‖ < r →
            (∀ t ∈ Ioo (0 : ℝ) 1, (φ, a + (t : ℂ) * d) ∈ rootDomain38) →
            IntegrableOn (fun t : ℝ =>
              d * p6PsiNumerator38 n (F n) φ (a + (t : ℂ) * d) /
                canonRoot38 φ (a + (t : ℂ) * d)) (Ioo (0 : ℝ) 1) ∧
            ∀ t ∈ Ioo (0 : ℝ) 1,
              ‖d * p6PsiNumerator38 n (F n) φ (a + (t : ℂ) * d) /
                  canonRoot38 φ (a + (t : ℂ) * d)‖ ≤
                C * Real.sqrt ‖d‖ / Real.sqrt t) := by
  have hgap' : lamPlus φ0.1 m ≠ lamMinus φ0.1 m := fun h => hgap (sub_eq_zero.mpr h)
  have hgapd : lamPlus φ0.1 m - lamMinus φ0.1 m ≠ 0 := hgap
  refine ⟨?_, ?_⟩
  · intro p
    have hcompact := rawBetaPathCompactIntegrable38 n m F φ0 p
    have hint1 : ∀ ε : ℝ, 0 < ε → ε < 1 →
        IntervalIntegrable (GKRootedArcIntegrand38 n m F φ0 (GKPathFirst38 p)) volume ε 1 := by
      intro ε hε hε1
      exact (hcompact ε ((1 - ε) / 2) hε (by linarith) (by linarith)).1
    have hint3 : ∀ η : ℝ, 0 < η → η < 1 →
        IntervalIntegrable (GKRootedArcIntegrand38 n m F φ0 (GKPathLast38 p)) volume 0 (1 - η) := by
      intro η hη hη1
      exact (hcompact ((1 - η) / 2) η (by linarith) hη (by linarith)).2.2
    have hz0 : perChar φ0.1 (lamMinus φ0.1 m) = 0 :=
      ((lamSeq_enumeration38 φ0.1).2.1 _).mpr ⟨2 * m, rfl⟩
    have hprim := g3001_L3_branch_prim n m F φ0 hgap' (lamMinus φ0.1 m) hz0 (Or.inl rfl)
    obtain ⟨L1, hL1⟩ := g3001_first_arc_endpoint_limit_native n m F φ0 (GKPathFirst38 p)
      p.2.2.2.1 hint1 hprim
    obtain ⟨L2, hL2⟩ := g3001_last_arc_full n m F φ0 hgap' (GKPathLast38 p) p.2.2.2.2.1 hint3
    exact ⟨_, g3001_joint_assembly n m F φ0 p L1 L2 hL1 hL2⟩
  · obtain ⟨V, hVo, hφ0V, hVW, r, c0, P, hr, hc0, hP, hV⟩ :=
      g3001_L5_uniform n m W hWo hWg (F n) (hFan n) φ0.1 hφ0W hgapd
    refine ⟨V, P / Real.sqrt c0, r, hVo, hφ0V, hVW, div_pos hP (Real.sqrt_pos.mpr hc0), hr, ?_⟩
    intro φ hφ
    obtain ⟨hgapφ, hends⟩ := hV φ hφ
    refine ⟨hgapφ, fun a ha => ?_⟩
    obtain ⟨⟨H, hH⟩, hψ⟩ := hends a ha
    have hφg : φ ∈ gkW := hWg (hVW hφ)
    have hbound := g3001_L6_root_bound n (F n) φ hφg a r c0 P hc0 H hH hψ
    refine ⟨fun z hz hrd hza => hbound z hz hrd hza, fun d hd hdr hdom => ?_⟩
    exact g3001_L7_segment φ hφg (p6PsiNumerator38 n (F n) φ)
      (continuousOn_univ.mp (p6PsiNumerator_entire38 n (F n) φ).continuousOn)
      a d r (P / Real.sqrt c0) hd hdr hbound hdom

end
end NlsGge.GKDefinitionDesign
end Piece11

