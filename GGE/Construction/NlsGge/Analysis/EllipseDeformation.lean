import NlsGge.Analysis.AffineLoopDeformation
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.Analysis.EllipseDeformation
noncomputable section

def curve (c : ℂ) (r δ θ : ℝ) : ℂ :=
  c + (r : ℂ) * (Real.cos θ : ℂ) + Complex.I * (δ * r : ℝ) * (Real.sin θ : ℂ)

def velocity (r δ θ : ℝ) : ℂ :=
  -(r : ℂ) * (Real.sin θ : ℂ) + Complex.I * (δ * r : ℝ) * (Real.cos θ : ℂ)

def displacement (r δ θ : ℝ) : ℂ :=
  Complex.I * ((1 - δ) * r : ℝ) * (Real.sin θ : ℂ)

def displacementVelocity (r δ θ : ℝ) : ℂ :=
  Complex.I * ((1 - δ) * r : ℝ) * (Real.cos θ : ℂ)

theorem curve_derivative (c : ℂ) (r δ θ : ℝ) :
    HasDerivAt (curve c r δ) (velocity r δ θ) θ := by
  convert ((hasDerivAt_const θ c).add ((Real.hasDerivAt_cos θ).ofReal_comp.const_mul (r : ℂ))).add
    ((Real.hasDerivAt_sin θ).ofReal_comp.const_mul (Complex.I * (δ * r : ℝ))) using 1
  · rfl
  · simp only [velocity, Complex.ofReal_neg]
    ring

theorem displacement_derivative (r δ θ : ℝ) :
    HasDerivAt (displacement r δ) (displacementVelocity r δ θ) θ := by
  exact (Real.hasDerivAt_sin θ).ofReal_comp.const_mul _

theorem velocity_continuous (r δ : ℝ) : Continuous (velocity r δ) :=
  (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_sin)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_cos))

theorem displacementVelocity_continuous (r δ : ℝ) :
    Continuous (displacementVelocity r δ) :=
  continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_cos)

theorem homotopy_point (c : ℂ) (r δ t θ : ℝ) :
    NlsGge.Analysis.AffineLoopDeformation.point (curve c r δ) (displacement r δ) t θ =
      curve c r (δ + (1 - δ) * t) θ := by
  simp only [NlsGge.Analysis.AffineLoopDeformation.point, curve, displacement, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem homotopy_tangent (r δ t θ : ℝ) :
    NlsGge.Analysis.AffineLoopDeformation.tangent (velocity r δ) (displacementVelocity r δ) t θ =
      velocity r (δ + (1 - δ) * t) θ := by
  simp only [NlsGge.Analysis.AffineLoopDeformation.tangent, velocity, displacementVelocity, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem curve_one (c : ℂ) (r θ : ℝ) : curve c r 1 θ = circleMap c r θ := by
  simp only [curve, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, one_mul]
  ring

theorem velocity_one (c : ℂ) (r θ : ℝ) : velocity r 1 θ = deriv (circleMap c r) θ := by
  rw [deriv_circleMap]
  simp only [velocity, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, one_mul, zero_add]
  ring_nf
  simp [Complex.I_sq]

theorem ellipse_integral_eq_circle {Ω : Set ℂ} {f : ℂ → ℂ}
    (c : ℂ) (r δ : ℝ) (hΩ : IsOpen Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      curve c r (δ + (1 - δ) * t) θ ∈ Ω) :
    IntervalIntegrable (fun θ => velocity r δ θ * f (curve c r δ θ)) volume 0 (2 * Real.pi) ∧
      CircleIntegrable f c r ∧
      (∫ θ in (0 : ℝ)..2 * Real.pi, velocity r δ θ * f (curve c r δ θ)) =
        circleIntegral f c r := by
  have h := NlsGge.Analysis.AffineLoopDeformation.affine_closed_loop_integral_eq hΩ hf
    (curve_derivative c r δ) (displacement_derivative r δ)
    (velocity_continuous r δ) (displacementVelocity_continuous r δ)
    (by simp [curve]) (by simp [displacement])
    (by simpa only [homotopy_point] using hdom)
  have hzero : ∀ θ, NlsGge.Analysis.AffineLoopDeformation.pullback f (curve c r δ) (displacement r δ)
      (velocity r δ) (displacementVelocity r δ) 0 θ =
      velocity r δ θ * f (curve c r δ θ) := by
    intro θ
    simp [NlsGge.Analysis.AffineLoopDeformation.pullback, NlsGge.Analysis.AffineLoopDeformation.tangent, NlsGge.Analysis.AffineLoopDeformation.point]
  have hone : ∀ θ, NlsGge.Analysis.AffineLoopDeformation.pullback f (curve c r δ) (displacement r δ)
      (velocity r δ) (displacementVelocity r δ) 1 θ =
      deriv (circleMap c r) θ * f (circleMap c r θ) := by
    intro θ
    simp only [NlsGge.Analysis.AffineLoopDeformation.pullback, homotopy_point, homotopy_tangent,
      mul_one, add_sub_cancel, curve_one, velocity_one c]
  rw [funext hzero, funext hone] at h
  have hfc : ContinuousOn (fun θ => f (circleMap c r θ)) (Icc 0 (2 * Real.pi)) := by
    apply hf.continuousOn.comp (continuous_circleMap c r).continuousOn
    intro θ hθ
    have hd := hdom 1 (by simp) θ hθ
    simpa only [mul_one, add_sub_cancel, curve_one] using hd
  refine ⟨h.1, ?_, ?_⟩
  · exact hfc.intervalIntegrable_of_Icc (by positivity)
  · simpa only [circleIntegral, smul_eq_mul] using h.2.2

end
end NlsGge.Analysis.EllipseDeformation
