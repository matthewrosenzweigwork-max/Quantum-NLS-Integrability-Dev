import Armstrong.Work.RawBetaCircleParameterCauchy
import NlsGge.GK38.StdRootBranchesSlit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Prospective source, awaiting root's compiler queue.

The zero period of the actual standard root produces an analytic solution of
the quadratic coefficient equation on the original filled ball.  The proof is
a compact Cauchy projection of a boundary primitive; it makes no assertion of
simple connectivity of a slit ball and no assertion of absolute endpoint
integrability.  Arbitrary complex and repeated endpoints are retained.

The first import is B's simultaneously prepared, Mathlib-only parameter Cauchy
derivative helper.  Root may set the final module path when integrating.
-/

set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Topology

namespace NlsGge.GK38
noncomputable section

/-- Literal compact boundary Cauchy projection. This total integral formula
is used analytically only after its displayed continuity hypotheses are proved. -/
def rawBetaBoundaryCauchy38 (B : ℝ → ℂ) (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (∫ θ in (0:ℝ)..2*Real.pi,
      B θ * deriv (circleMap c r) θ / (circleMap c r θ-z))

/-- Literal nested standard-root coefficient. Its branch is the existing
standard root, and its analytic/ODE properties require a positive circle
containing the full segment and the genuine zero period. -/
def rawBetaStdCauchyCoefficient38 (a b c : ℂ) (r : ℝ)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  rawBetaBoundaryCauchy38
    (fun θ => (∫ t in (0:ℝ)..θ,
      deriv (circleMap c r) t *
        (f (circleMap c r t) /
          stdRoot38 ((a+b)/2) ((b-a)^2) (circleMap c r t))) /
      stdRoot38 ((a+b)/2) ((b-a)^2) (circleMap c r θ)) c r z

/-- The compact Cauchy projection commutes with
`(z-a)*(z-b)*d/dz + (z-(a+b)/2)`.  Boundary data are parameter functions;
only their two displayed endpoint values, not an ambient circle extension,
are needed. -/
theorem rawBetaQuadraticODEOfBoundaryDataExplicit38
    (a b c : ℂ) (r : ℝ) (hr : 0 < r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (B B' : ℝ → ℂ) (hB : Continuous B)
    (hBd : ∀ θ : ℝ, HasDerivAt B (B' θ) θ)
    (hB0 : B 0 = 0) (hBend : B (2 * Real.pi) = 0)
    (hboundary : ∀ θ : ℝ,
      (circleMap c r θ - a) * (circleMap c r θ - b) * B' θ +
        (circleMap c r θ - (a+b)/2) * deriv (circleMap c r) θ * B θ =
          f (circleMap c r θ) * deriv (circleMap c r) θ) :
    let T : ℂ → ℂ := rawBetaBoundaryCauchy38 B c r
    AnalyticOnNhd ℂ T (ball c r) ∧
      ∀ z ∈ ball c r,
        (z-a) * (z-b) * deriv T z + (z-(a+b)/2) * T z = f z := by
  let γ : ℝ → ℂ := circleMap c r
  let τ : ℂ := (a+b)/2
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let T : ℂ → ℂ := fun z => C⁻¹ *
    (∫ θ in (0:ℝ)..2*Real.pi, B θ * deriv γ θ / (γ θ-z))
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hγc : Continuous γ := continuous_circleMap c r
  have hγd : ∀ θ : ℝ, HasDerivAt γ (deriv γ θ) θ :=
    fun θ => (differentiable_circleMap c r θ).hasDerivAt
  have hγ'c : Continuous (deriv γ) := by
    change Continuous (deriv (circleMap c r))
    rw [funext (deriv_circleMap c r)]
    exact (continuous_circleMap 0 r).mul_const Complex.I
  have hfc : Continuous (fun θ => f (γ θ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hf (γ θ) (sphere_subset_closedBall
      (circleMap_mem_sphere c hr.le θ))).continuousAt.comp hγc.continuousAt
  have hTd : ∀ z ∈ ball c r, HasDerivAt T
      (C⁻¹ * (∫ θ in (0:ℝ)..2*Real.pi,
        B θ * deriv γ θ / (γ θ-z)^2)) z := by
    intro z hz
    have hz' : z ∉ sphere c |r| := by
      rw [abs_of_pos hr]
      intro hs
      exact (not_lt.mpr (mem_sphere.mp hs).ge) (mem_ball.mp hz)
    exact (rawBetaCircleParameterCauchyHasDerivAt38 B hB c r z hz').const_mul C⁻¹
  refine ⟨(show DifferentiableOn ℂ T (ball c r) from
    fun z hz => (hTd z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
      isOpen_ball, ?_⟩
  intro z hz
  let I₁ : ℝ → ℂ := fun θ => B θ * deriv γ θ / (γ θ-z)
  let I₂ : ℝ → ℂ := fun θ => B θ * deriv γ θ / (γ θ-z)^2
  let F : ℝ → ℂ := fun θ => f (γ θ) * deriv γ θ / (γ θ-z)
  let J : ℝ → ℂ := fun θ => (γ θ-a) * (γ θ-b) * B θ / (γ θ-z)
  have hden : ∀ θ : ℝ, γ θ-z ≠ 0 :=
    fun θ => sub_ne_zero.mpr (circleMap_ne_mem_ball hz θ)
  have hI₁c : Continuous I₁ :=
    (hB.mul hγ'c).div (hγc.sub continuous_const) hden
  have hI₂c : Continuous I₂ :=
    (hB.mul hγ'c).div ((hγc.sub continuous_const).pow 2)
      (fun θ => pow_ne_zero 2 (hden θ))
  have hFc : Continuous F :=
    (hfc.mul hγ'c).div (hγc.sub continuous_const) hden
  have hI₁i : IntervalIntegrable I₁ volume (0:ℝ) (2*Real.pi) :=
    hI₁c.intervalIntegrable (0:ℝ) (2*Real.pi)
  have hI₂i : IntervalIntegrable I₂ volume (0:ℝ) (2*Real.pi) :=
    hI₂c.intervalIntegrable (0:ℝ) (2*Real.pi)
  have hFi : IntervalIntegrable F volume (0:ℝ) (2*Real.pi) :=
    hFc.intervalIntegrable (0:ℝ) (2*Real.pi)
  have hJd : ∀ θ : ℝ, HasDerivAt J
      (F θ - ((z-a)*(z-b))*I₂ θ - (z-τ)*I₁ θ) θ := by
    intro θ
    have hb : (γ θ-a) * (γ θ-b) * B' θ =
        f (γ θ) * deriv γ θ - (γ θ-τ) * deriv γ θ * B θ :=
      eq_sub_of_add_eq (hboundary θ)
    apply (((((hγd θ).sub_const a).mul ((hγd θ).sub_const b)).mul
      (hBd θ)).div ((hγd θ).sub_const z) (hden θ)).congr_deriv
    change
      (((deriv γ θ * (γ θ-b) + (γ θ-a) * deriv γ θ) * B θ +
        ((γ θ-a)*(γ θ-b)) * B' θ) * (γ θ-z) -
        ((γ θ-a)*(γ θ-b)) * B θ * deriv γ θ) / (γ θ-z)^2 =
      F θ - ((z-a)*(z-b))*I₂ θ - (z-τ)*I₁ θ
    rw [hb]
    dsimp [F, I₁, I₂, τ]
    field_simp [hden θ]
    ring
  have hJ0 : J 0 = 0 := by simp [J, hB0]
  have hJend : J (2*Real.pi) = 0 := by simp [J, hBend]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hJd θ)
    ((hFi.sub (hI₂i.const_mul ((z-a)*(z-b)))).sub (hI₁i.const_mul (z-τ)))
  rw [hJend, hJ0, sub_self,
    intervalIntegral.integral_sub
      (hFi.sub (hI₂i.const_mul ((z-a)*(z-b)))) (hI₁i.const_mul (z-τ)),
    intervalIntegral.integral_sub hFi (hI₂i.const_mul ((z-a)*(z-b))),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  have hCauchy : (∫ θ in (0:ℝ)..2*Real.pi, F θ) = C * f z := by
    simpa [F, γ, C, circleIntegral, smul_eq_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
      hf.differentiableOn.circleIntegral_sub_inv_smul hz
  rw [hCauchy] at hFTC
  have hEq : ((z-a)*(z-b)) * (∫ θ in (0:ℝ)..2*Real.pi, I₂ θ) +
      (z-τ) * (∫ θ in (0:ℝ)..2*Real.pi, I₁ θ) = C * f z := by
    linear_combination -hFTC
  change ((z-a)*(z-b)) * deriv T z + (z-τ) * T z = f z
  rw [(hTd z hz).deriv]
  change ((z-a)*(z-b)) *
      (C⁻¹ * (∫ θ in (0:ℝ)..2*Real.pi, I₂ θ)) +
    (z-τ) * (C⁻¹ * (∫ θ in (0:ℝ)..2*Real.pi, I₁ θ)) = f z
  calc
    _ = C⁻¹ * (((z-a)*(z-b)) * (∫ θ in (0:ℝ)..2*Real.pi, I₂ θ) +
        (z-τ) * (∫ θ in (0:ℝ)..2*Real.pi, I₁ θ)) := by ring
    _ = C⁻¹ * (C * f z) := by rw [hEq]
    _ = f z := by rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]

theorem rawBetaQuadraticODEOfBoundaryData38
    (a b c : ℂ) (r : ℝ) (hr : 0 < r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (B B' : ℝ → ℂ) (hB : Continuous B)
    (hBd : ∀ θ : ℝ, HasDerivAt B (B' θ) θ)
    (hB0 : B 0 = 0) (hBend : B (2 * Real.pi) = 0)
    (hboundary : ∀ θ : ℝ,
      (circleMap c r θ - a) * (circleMap c r θ - b) * B' θ +
        (circleMap c r θ - (a+b)/2) * deriv (circleMap c r) θ * B θ =
          f (circleMap c r θ) * deriv (circleMap c r) θ) :
    ∃ T : ℂ → ℂ, AnalyticOnNhd ℂ T (ball c r) ∧
      ∀ z ∈ ball c r,
        (z-a) * (z-b) * deriv T z + (z-(a+b)/2) * T z = f z := by
  obtain ⟨hT, hTode⟩ := rawBetaQuadraticODEOfBoundaryDataExplicit38
    a b c r hr f hf B B' hB hBd hB0 hBend hboundary
  exact ⟨rawBetaBoundaryCauchy38 B c r, hT, hTode⟩

/-- A zero period for the actual standard square-root branch yields an
analytic quadratic coefficient on the original filled ball.  The branch
square identity is used only on the circle, never on the removed segment. -/
theorem rawBetaQuadraticODEOfZeroStdRootPeriodExplicit38
    (a b c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcut : segment ℝ a b ⊆ ball c r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hperiod : circleIntegral
      (fun z => f z / stdRoot38 ((a+b)/2) ((b-a)^2) z) c r = 0) :
    let T : ℂ → ℂ := rawBetaStdCauchyCoefficient38 a b c r f
    AnalyticOnNhd ℂ T (ball c r) ∧
      ∀ z ∈ ball c r,
        (z-a) * (z-b) * deriv T z + (z-(a+b)/2) * T z = f z := by
  let γ : ℝ → ℂ := circleMap c r
  let τ : ℂ := (a+b)/2
  let S : ℝ → ℂ := fun θ => stdRoot38 τ ((b-a)^2) (γ θ)
  let U' : ℝ → ℂ := fun θ => deriv γ θ * (f (γ θ) / S θ)
  let U : ℝ → ℂ := fun θ => ∫ t in (0:ℝ)..θ, U' t
  let B : ℝ → ℂ := fun θ => U θ / S θ
  let B' : ℝ → ℂ := fun θ =>
    (U' θ * S θ - U θ * deriv S θ) / S θ^2
  have hγc : Continuous γ := continuous_circleMap c r
  have hγd : ∀ θ : ℝ, HasDerivAt γ (deriv γ θ) θ :=
    fun θ => (differentiable_circleMap c r θ).hasDerivAt
  have hγ'c : Continuous (deriv γ) := by
    change Continuous (deriv (circleMap c r))
    rw [funext (deriv_circleMap c r)]
    exact (continuous_circleMap 0 r).mul_const Complex.I
  have hoff : ∀ θ : ℝ, γ θ ∉ segment ℝ a b := by
    intro θ hθ
    have hs := circleMap_mem_sphere c hr.le θ
    exact (not_lt.mpr (mem_sphere.mp hs).ge) (mem_ball.mp (hcut hθ))
  have hSn : ∀ θ : ℝ, S θ ≠ 0 :=
    fun θ => stdRoot_ne_zero38 a b (γ θ) (hoff θ)
  have hSq : ∀ θ : ℝ, S θ^2 = (γ θ-a) * (γ θ-b) := by
    intro θ
    change stdRoot38 ((a+b)/2) ((b-a)^2) (γ θ)^2 = _
    rw [stdRoot_sq38 a b (γ θ) (hoff θ)]
    ring
  have hSd : Differentiable ℝ S := by
    intro θ
    have hs := stdRoot_slit38 a b (γ θ) (hoff θ)
    have ha : AnalyticAt ℂ (stdRoot38 τ ((b-a)^2)) (γ θ) :=
      stdRoot_analyticAt38 analyticAt_const analyticAt_const analyticAt_id hs.1 hs.2
    exact (ha.differentiableAt.hasDerivAt.comp θ (hγd θ)).differentiableAt
  have hSc : Continuous S := hSd.continuous
  have hfc : Continuous (fun θ => f (γ θ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hf (γ θ) (sphere_subset_closedBall
      (circleMap_mem_sphere c hr.le θ))).continuousAt.comp hγc.continuousAt
  have hU'c : Continuous U' := hγ'c.mul (hfc.div hSc hSn)
  have hUd : ∀ θ : ℝ, HasDerivAt U (U' θ) θ :=
    fun θ => (hU'c.integral_hasStrictDerivAt 0 θ).hasDerivAt
  have hUc : Continuous U :=
    (show Differentiable ℝ U from fun θ => (hUd θ).differentiableAt).continuous
  have hBc : Continuous B := hUc.div hSc hSn
  have hBd : ∀ θ : ℝ, HasDerivAt B (B' θ) θ :=
    fun θ => (hUd θ).div (hSd θ).hasDerivAt (hSn θ)
  have hB0 : B 0 = 0 := by simp [B, U]
  have hUend : U (2*Real.pi) = 0 := by
    simpa [U, U', S, γ, τ, circleIntegral, smul_eq_mul] using hperiod
  have hBend : B (2*Real.pi) = 0 := by simp [B, hUend]
  have hSrel : ∀ θ : ℝ, S θ * deriv S θ = (γ θ-τ) * deriv γ θ := by
    intro θ
    have hds : HasDerivAt (fun t => S t^2) (2*S θ*deriv S θ) θ := by
      simpa using! (hSd θ).hasDerivAt.pow 2
    have hdq : HasDerivAt (fun t => S t^2)
        (deriv γ θ * (γ θ-b) + (γ θ-a) * deriv γ θ) θ := by
      have he : (fun t => S t^2) = fun t => (γ t-a) * (γ t-b) := funext hSq
      rw [he]
      exact ((hγd θ).sub_const a).mul ((hγd θ).sub_const b)
    have hu := hds.unique hdq
    dsimp [τ]
    linear_combination (1/2:ℂ) * hu
  apply rawBetaQuadraticODEOfBoundaryDataExplicit38 a b c r hr f hf B B' hBc hBd hB0 hBend
  intro θ
  change (γ θ-a) * (γ θ-b) * B' θ +
    (γ θ-τ) * deriv γ θ * B θ = f (γ θ) * deriv γ θ
  rw [← hSq θ]
  calc
    S θ^2 * B' θ + (γ θ-τ) * deriv γ θ * B θ =
        U' θ * S θ - U θ * deriv S θ +
          (γ θ-τ) * deriv γ θ * U θ / S θ := by
      dsimp [B, B']
      field_simp [hSn θ]
    _ = U' θ * S θ := by
      rw [← hSrel θ]
      field_simp [hSn θ]
      ring
    _ = f (γ θ) * deriv γ θ := by
      dsimp [U']
      field_simp [hSn θ]

theorem rawBetaQuadraticODEOfZeroStdRootPeriod38
    (a b c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcut : segment ℝ a b ⊆ ball c r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hperiod : circleIntegral
      (fun z => f z / stdRoot38 ((a+b)/2) ((b-a)^2) z) c r = 0) :
    ∃ T : ℂ → ℂ, AnalyticOnNhd ℂ T (ball c r) ∧
      ∀ z ∈ ball c r,
        (z-a) * (z-b) * deriv T z + (z-(a+b)/2) * T z = f z := by
  obtain ⟨hT, hTode⟩ := rawBetaQuadraticODEOfZeroStdRootPeriodExplicit38
    a b c r hr hcut f hf hperiod
  exact ⟨rawBetaStdCauchyCoefficient38 a b c r f, hT, hTode⟩

#print axioms rawBetaQuadraticODEOfBoundaryData38
#print axioms rawBetaQuadraticODEOfZeroStdRootPeriod38

end
end NlsGge.GK38
