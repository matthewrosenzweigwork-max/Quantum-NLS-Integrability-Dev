import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
namespace NlsGge.GK38.ActionGradient
noncomputable section

theorem scalar_const_mul_div_hasDeriv {f g : ℂ → ℂ} {x f' g' : ℂ} (c : ℂ)
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (hn : g x ≠ 0) :
    HasDerivAt (fun t : ℂ => c * f t / g t)
      ((c * f' * g x - c * f x * g') / g x ^ 2) x := by
  convert (hf.const_mul c).div hg hn using 1

theorem scalar_div_hasDeriv {f g : ℂ → ℂ} {x f' g' : ℂ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (hn : g x ≠ 0) :
    HasDerivAt (fun t : ℂ => f t / g t)
      ((f' * g x - f x * g') / g x ^ 2) x := by
  simpa only [one_mul] using scalar_const_mul_div_hasDeriv 1 hf hg hn

end
end NlsGge.GK38.ActionGradient
