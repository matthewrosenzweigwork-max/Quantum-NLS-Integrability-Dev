import NlsGge.GK38.GradTauGammaCircleTransfer
import NlsGge.GK38.TauGamma
import NlsGge.GK38.GradFundamentalFree

/-! Independent contour kernels for the actual symmetric periodic gap data.
The potential components are independent complex L2 classes. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

def tauGammaQuotientKernel38 (φ : PotPair) (t : ℝ) (z : ℂ) : PairVec38 :=
  (discrim φ z / perChar φ z) • gradDiscrim38 φ z t

def gradTau38 (φ : PotPair) (n : ℤ) (t : ℝ) : PairVec38 :=
  -((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    circleIntegral (tauGammaQuotientKernel38 φ t) (discC φ n) (discR φ n)

def gradGamma2_38 (φ : PotPair) (n : ℤ) (t : ℝ) : PairVec38 :=
  (-8 * (2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    circleIntegral (fun z => (z - tauN φ n) • tauGammaQuotientKernel38 φ t z)
      (discC φ n) (discR φ n)

def pairPointMass38 (v : PairVec38) : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2

theorem pairPointMass38_nonneg (v : PairVec38) : 0 ≤ pairPointMass38 v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem k4aGradDiscrim_zero38 (z : ℂ) (t : Icc (0 : ℝ) 1) :
    gradDiscrim38 0 z t = 0 := by
  exact (smul_eq_zero.mp (scaled_gradDiscrim38_zero z t)).resolve_left Complex.I_ne_zero

theorem tauGammaQuotientKernel38_zero (z : ℂ) (t : Icc (0 : ℝ) 1) :
    tauGammaQuotientKernel38 0 t z = 0 := by
  simp only [tauGammaQuotientKernel38, k4aGradDiscrim_zero38 z t, smul_zero]

theorem gradTau38_zero (n : ℤ) (t : Icc (0 : ℝ) 1) : gradTau38 0 n t = 0 := by
  have he : tauGammaQuotientKernel38 0 t = 0 := by
    funext z
    exact tauGammaQuotientKernel38_zero z t
  simp [gradTau38, he, circleIntegral]

theorem gradGamma2_38_zero (n : ℤ) (t : Icc (0 : ℝ) 1) :
    gradGamma2_38 0 n t = 0 := by
  have he : (fun z => (z - tauN 0 n) • tauGammaQuotientKernel38 0 t z) = 0 := by
    funext z
    simp only [tauGammaQuotientKernel38_zero z t, smul_zero, Pi.zero_apply]
  unfold gradGamma2_38
  rw [he]
  simp [circleIntegral]

end
end NlsGge.GK38
