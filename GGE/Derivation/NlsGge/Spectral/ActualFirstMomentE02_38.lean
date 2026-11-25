import NlsGge.Spectral.ActualTraceMomentsE02_38
import NlsGge.Spectral.ActualConvexMomentE02_38
import NlsGge.Hierarchy.RiccatiLowOrderAlgebraAfterCore
import Mathlib.Analysis.Calculus.Deriv.Star
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # S01.01–.02 (campaign 38): the first spectral moment

(.01) For a finite-gap field, `(2/π)∫ 2λ v = Σ' 2πn I_n` (from A:lem:convex applied to `W = ±id`,
equivalently `∫(λ - p)v = 0`). (.02) For an H¹ field with smooth representative `U`,
`(2/π)∫ 2λ v = -P(U)` where `P(U) = Im ∫₀¹ ū ∂ₓu`. -/

/-- S01.01: first spectral moment of a finite-gap field equals `Σ 2πn I_n`. -/
theorem actualFirstMoment_eq_sum_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) :
    Integrable (fun l : ℝ => (2*l) * actualGapHeightE02_38 u l) ∧
    Summable (fun n : ℤ => 2*Real.pi*n * actualGapActionAllE02_38 u n) ∧
    (2/Real.pi) * ∫ l : ℝ, (2*l) * actualGapHeightE02_38 u l =
      ∑' n : ℤ, 2*Real.pi*n * actualGapActionAllE02_38 u n := by
  have hid : ContDiff ℝ 2 (fun x : ℝ => x) := contDiff_id
  have hneg : ContDiff ℝ 2 (fun x : ℝ => -x) := contDiff_id.neg
  obtain ⟨h1, h2, h3⟩ := actualConvexMoment_E02_38 u hu hfin (fun x => x) hid
    (convexOn_id convex_univ)
  obtain ⟨-, h2', h3'⟩ := actualConvexMoment_E02_38 u hu hfin (fun x => -x) hneg
    (concaveOn_id convex_univ).neg
  refine ⟨h1, h2, ?_⟩
  have e1 : ∑' n : ℤ, -(2*Real.pi*n) * actualGapActionAllE02_38 u n =
      -∑' n : ℤ, 2*Real.pi*n * actualGapActionAllE02_38 u n := by
    rw [← tsum_neg]; congr 1; funext n; ring
  have e2 : ∫ l : ℝ, -(2*l) * actualGapHeightE02_38 u l =
      -∫ l : ℝ, (2*l) * actualGapHeightE02_38 u l := by
    rw [← integral_neg]; congr 1; funext l; ring
  rw [e1, e2] at h3'
  linarith

/-- Momentum `P(U) = Im ∫₀¹ ū ∂ₓu`. -/
def momentumE02_38 (U : ℝ → ℂ) : ℝ := (∫ x in (0:ℝ)..1, star (U x) * deriv U x).im

/-- S01.02: the first spectral moment is `-P(U)` (H¹ class with smooth representative). -/
theorem actualFirstMoment_eq_neg_momentum_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (U : ℝ → ℂ) (hUs : ContDiff ℝ ∞ U) (hUp : Function.Periodic U 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] U) :
    Integrable (fun l : ℝ => (2*l) * actualGapHeightE02_38 u l) ∧
    (2/Real.pi) * ∫ l : ℝ, (2*l) * actualGapHeightE02_38 u l = -momentumE02_38 U := by
  obtain ⟨hint, hval⟩ := actualTraceMoments_E02_38 u hu U hUs hUp hae 1 1 (by norm_num)
  set v := actualGapHeightE02_38 u
  have hUd : Differentiable ℝ U := hUs.differentiable (by simp)
  -- the coefficient b₂
  have hp2 : ∀ x, riccatiJetEvaluation U x (MvPolynomial.X (false, 0) * p 2) =
      -(U x * star (deriv U x)) := by
    intro x
    rw [p_two]
    have hd : deriv (fun y => star (U y)) x = star (deriv U x) := ((hUd x).hasDerivAt.star).deriv
    simp [riccatiJetEvaluation, polynomialEvaluation, riccatiJetFunction]
    exact Or.inl hd
  set J := ∫ x in (0:ℝ)..1, star (U x) * deriv U x
  have hconjJ : (∫ x in (0:ℝ)..1, U x * star (deriv U x)) = star J := by
    simp only [J]
    rw [show star (∫ x in (0:ℝ)..1, star (U x) * deriv U x) =
      (starRingEnd ℂ) (∫ x in (0:ℝ)..1, star (U x) * deriv U x) from rfl,
      ← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr; intro x _
    simp [mul_comm]
  have hb2 : riccatiQuasiCoeff38 U 2 = -(Complex.I / 4) * star J := by
    unfold riccatiQuasiCoeff38
    simp_rw [hp2]
    rw [intervalIntegral.integral_neg, hconjJ]
    ring
  -- the moment
  have hmom : ((∫ t, t^1 * v t : ℝ) : ℂ) = Real.pi * riccatiQuasiCoeff38 U 2 := by
    have hI2 : Complex.I ^ (1+1) = -1 := by rw [show (1:ℕ)+1 = 2 from rfl, Complex.I_sq]
    rw [hI2] at hval
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    set X := ((∫ t, t^1 * v t : ℝ) : ℂ)
    calc X = Real.pi * ((1/Real.pi) * X) := by field_simp
      _ = Real.pi * riccatiQuasiCoeff38 U 2 := by
          rw [show (1/(Real.pi:ℂ)) * X = riccatiQuasiCoeff38 U 2 by linear_combination hval]
  have hval2 : (((2/Real.pi) * ∫ l : ℝ, (2*l) * v l : ℝ) : ℂ) = -Complex.I * star J := by
    have : ∫ l : ℝ, (2*l) * v l = 2 * ∫ t, t^1 * v t := by
      rw [← integral_const_mul]; congr 1; funext l; ring
    rw [this]; push_cast
    rw [hmom, hb2]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp; ring
  refine ⟨?_, ?_⟩
  · have := hint.const_mul 2
    exact this.congr (Eventually.of_forall fun l => by simp only [pow_one]; ring)
  · have hre := congrArg Complex.re hval2
    rw [Complex.ofReal_re] at hre
    rw [hre, momentumE02_38]
    simp [Complex.mul_re]
    rfl
