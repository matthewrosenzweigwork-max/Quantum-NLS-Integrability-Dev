import Mathlib

                                                                                                                                             
                                                                                                                                           
                                                             
set_option autoImplicit false
noncomputable section
namespace NlsGge.ThirdConsultation.I

/-- Totalized diagonal value is zero; its actual integrability is I-012. -/
def symmetricKernel (f p v : ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  (deriv f (p x.1) - deriv f (p x.2)) / (x.1 - x.2) * v x.1 * v x.2

end NlsGge.ThirdConsultation.I
