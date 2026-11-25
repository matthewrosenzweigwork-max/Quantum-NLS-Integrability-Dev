import QuantumNLS.Local018ModulusImageRound11
/-! integrator-authored trusted spec for LOCAL-018 lem:reset-modulus-image (Terra r158 FULL ACCEPT): headline statement(s) copied verbatim from Local018ModulusImageRound11 (QuantumNLS.Local018ModulusImage). -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.L018Spec
open QuantumNLS.Local018ModulusImage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

set_option maxHeartbeats 8000000 in
theorem reset_modulus_image_spec {f : E → E} {R ε : ℝ} (hR : 0 < R)
    (hf : ∀ x ∈ ball (0 : E) R, AnalyticAt ℝ f x)
    (hn : ∀ x ∈ ball (0 : E) R, ‖f x‖ = ‖x‖)
    (hε : ε < 1) (hD : ∀ x ∈ ball (0 : E) R, ‖fderiv ℝ f x - 1‖ ≤ ε) :
    f 0 = 0 ∧
    (∀ x ∈ ball (0 : E) R, ‖f x‖ = ‖x‖) ∧
    (∀ x ∈ ball (0 : E) R, ∀ y ∈ ball (0 : E) R,
      ‖f y - f x - (y - x)‖ ≤ ε * ‖y - x‖) ∧
    InjOn f (ball (0 : E) R) ∧
    IsClosed ((Subtype.val : ball (0 : E) R → E) ⁻¹' (f '' ball (0 : E) R)) ∧
    ∃ g : E → E, f '' ball (0 : E) R = ball (0 : E) R ∧
      (∀ x ∈ ball (0 : E) R, g (f x) = x) ∧
      (∀ y ∈ ball (0 : E) R, g y ∈ ball (0 : E) R ∧ f (g y) = y ∧
        AnalyticAt ℝ g y ∧ HasFDerivAt g (fderiv ℝ f (g y)).inverse y ∧
        ‖(fderiv ℝ f (g y)).inverse‖ ≤ (1 - ε)⁻¹) := by
  first
  | exact QuantumNLS.Local018ModulusImage.reset_modulus_image
  | (apply QuantumNLS.Local018ModulusImage.reset_modulus_image <;> assumption)

end QuantumNLS.L018Spec
#print axioms QuantumNLS.L018Spec.reset_modulus_image_spec
