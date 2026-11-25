                                                                                                                                                                                                                                                                                           
import Mathlib
import NlsGge.NLS38.TorusTwist38

set_option autoImplicit false
open NlsGge.NLS38

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

abbrev Torus (Λ : Finset ℤ) := Λ → AddCircle (2*Real.pi)

/-- statement-local `rotate` (forced by `twist_rotTorus`). -/
def rotate {Λ : Finset ℤ} (θ : Λ → ℝ) (z : Λ → ℂ) : Λ → ℂ :=
  fun i => Complex.exp (θ i * Complex.I) * z i

variable {Λ : Finset ℤ} {κ : (Λ → ℂ) → Λ → ℝ}

theorem twist_rotation_covariance (hκ : Measurable κ)
    (hinv : ∀ z θ, κ (rotate θ z) = κ z) :
    Measurable (twist κ) ∧
      ∀ (g : Torus Λ) z, twist κ (rotTorus g z) = rotTorus g (twist κ z) :=
  ⟨measurable_twist κ hκ, fun g z => twist_rotTorus κ (fun z θ => hinv z θ) g z⟩

end
end NlsGge.ThirdConsultation.PDE
