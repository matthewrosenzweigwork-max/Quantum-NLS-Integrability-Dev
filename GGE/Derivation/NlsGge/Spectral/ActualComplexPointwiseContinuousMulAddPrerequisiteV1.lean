import NlsGge.Spectral.ActualComplexZsCoefficientEntireInSpectralParameterV1
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

/-- A pointwise complex product has the same continuity as the corresponding
pointwise product of function-valued maps, including the pinned function
module dictionaries. -/
theorem continuousOn_complex_pointwise_mul
    (s : Set ℝ) (f g : ℝ → ℂ)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x : ℝ => f x * g x) s := by
  simpa only [Pi.mul_apply] using! (hf.mul hg)

/-- A sum of two pointwise products has the corresponding function-algebra
continuity, with no additional topological assumptions. -/
theorem continuousOn_complex_pointwise_mul_add
    (s : Set ℝ) (f g h k : ℝ → ℂ)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hh : ContinuousOn h s) (hk : ContinuousOn k s) :
    ContinuousOn (fun x : ℝ => f x * g x + h x * k x) s := by
  simpa only [Pi.add_apply, Pi.mul_apply] using!
    (hf.mul hg).add (hh.mul hk)

end NlsGge.SpectralFoundations
