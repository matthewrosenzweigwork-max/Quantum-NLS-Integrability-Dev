import QuantumNLS.Ext025A5Triangular
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! GP-03 / LOCAL-009: the literal scalar exponential map. Quantitative
inverse disks will use the source derivative estimate; the map's joint
analyticity and its scalar derivative are constructed, never assumed. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open scoped NNReal
namespace QuantumNLS.Ext025A7

def spectralMap (κ L : ℝ) (z w : ℂ) : ℂ :=
  Complex.exp (Complex.I * κ * w) +
    Complex.exp (Complex.I * z * L) * Complex.exp (-Complex.I * κ * w)

def spectralDerivative (κ L : ℝ) (z w : ℂ) : ℂ :=
  (Complex.I * κ) * Complex.exp (Complex.I * κ * w) +
    Complex.exp (Complex.I * z * L) *
      ((-Complex.I * κ) * Complex.exp (-Complex.I * κ * w))

def spectralLinear (κ L : ℝ) (z : ℂ) : ℂ :=
  Complex.I * κ * (1 - Complex.exp (Complex.I * z * L))

theorem spectralMap_analyticAt (κ L : ℝ) (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => spectralMap κ L q.1 q.2) p := by
  unfold spectralMap
  exact (analyticAt_const.mul analyticAt_snd).cexp.add
    (((analyticAt_const.mul analyticAt_fst).mul analyticAt_const).cexp.mul
      (analyticAt_const.mul analyticAt_snd).cexp)

theorem spectralMap_hasDerivAt (κ L : ℝ) (z w : ℂ) :
    HasDerivAt (spectralMap κ L z) (spectralDerivative κ L z w) w := by
  unfold spectralMap spectralDerivative
  convert (((hasDerivAt_id w).const_mul (Complex.I * κ)).cexp).add
    ((((hasDerivAt_id w).const_mul (-Complex.I * κ)).cexp).const_mul
      (Complex.exp (Complex.I * z * L))) using 1
  · rfl
  · simp only [id_eq]; ring

theorem spectralDerivative_zero (κ L : ℝ) (z : ℂ) :
    spectralDerivative κ L z 0 = spectralLinear κ L z := by
  simp [spectralDerivative, spectralLinear]
  ring

def normalizedSpectral (κ L : ℝ) (z w : ℂ) : ℂ :=
  (spectralMap κ L z w - spectralMap κ L z 0) / spectralLinear κ L z

theorem normalizedSpectral_analyticAt (κ L : ℝ) {p : ℂ × ℂ}
    (hD : spectralLinear κ L p.1 ≠ 0) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => normalizedSpectral κ L q.1 q.2) p := by
  unfold normalizedSpectral spectralLinear at *
  exact ((spectralMap_analyticAt κ L p).sub
    ((spectralMap_analyticAt κ L (p.1, 0)).comp (f := fun q : ℂ × ℂ => (q.1, 0))
      (analyticAt_fst.prod analyticAt_const))).div
    (analyticAt_const.mul (analyticAt_const.sub
      ((analyticAt_const.mul analyticAt_fst).mul analyticAt_const).cexp)) hD

theorem normalizedSpectral_hasDerivAt (κ L : ℝ) (z w : ℂ) :
    HasDerivAt (normalizedSpectral κ L z)
      (spectralDerivative κ L z w / spectralLinear κ L z) w :=
  ((spectralMap_hasDerivAt κ L z w).sub_const _).div_const _

/-- The source's quarter-derivative estimate gives the exact normalized
quarter bound, with no assumption about any inverse or its regularity. -/
theorem normalizedSpectral_derivative_bound (κ L : ℝ) {z w : ℂ}
    (hD : spectralLinear κ L z ≠ 0)
    (hb : ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
      ‖spectralLinear κ L z‖ / 4) :
    ‖spectralDerivative κ L z w / spectralLinear κ L z - 1‖ ≤ 1 / 4 := by
  rw [← div_self hD, ← sub_div, norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hD)).2 (by linarith)

/-- Integrating the actual derivative on the convex disk yields the
quantitative linear approximation required for a constructive inverse. -/
theorem normalizedSpectral_approximates (κ L : ℝ) {z : ℂ} {R : ℝ}
    (hD : spectralLinear κ L z ≠ 0)
    (hb : ∀ w ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4) :
    ApproximatesLinearOn (normalizedSpectral κ L z)
      (ContinuousLinearMap.id ℂ ℂ) (closedBall (0 : ℂ) R) (1 / 4) := by
  intro x hx y hy
  exact (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun w _ => (normalizedSpectral_hasDerivAt κ L z w).hasFDerivAt.hasFDerivWithinAt)
    (fun w hw => by
      have hi : ContinuousLinearMap.toSpanSingleton ℂ
          (spectralDerivative κ L z w / spectralLinear κ L z) - ContinuousLinearMap.id ℂ ℂ =
          ContinuousLinearMap.toSpanSingleton ℂ
            (spectralDerivative κ L z w / spectralLinear κ L z - 1) := by
        apply ContinuousLinearMap.ext
        intro u
        simp [mul_sub]
      rw [hi, ContinuousLinearMap.norm_toSpanSingleton]
      norm_num
      exact normalizedSpectral_derivative_bound κ L hD (hb w hw)) hy hx

end QuantumNLS.Ext025A7
#print axioms QuantumNLS.Ext025A7.spectralMap_analyticAt
#print axioms QuantumNLS.Ext025A7.spectralMap_hasDerivAt
#print axioms QuantumNLS.Ext025A7.spectralDerivative_zero
#print axioms QuantumNLS.Ext025A7.normalizedSpectral_analyticAt
#print axioms QuantumNLS.Ext025A7.normalizedSpectral_hasDerivAt
#print axioms QuantumNLS.Ext025A7.normalizedSpectral_derivative_bound
#print axioms QuantumNLS.Ext025A7.normalizedSpectral_approximates
