import QuantumNLS.Ext025AFoundations

/-! GP-06's precise normalization wrapper: the action `I(u)=norm(u)^2`
has real gradient `2u`, and its normalized Hamiltonian flow is `exp(-it)u`.
The strong form-to-dual isomorphism is proved in Ext025AFoundations.
-/
set_option autoImplicit false
noncomputable section
open InnerProductSpace
open scoped InnerProductSpace
namespace QuantumNLS.Ext025A
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

theorem gp06_action_real_gradient (u : E) :
    (toDual ℝ E).symm (fderiv ℝ (fun v : E => ‖v‖ ^ 2) u) = (2 : ℝ) • u := by
  apply (toDual ℝ E).injective
  ext w
  simp [fderiv_norm_sq_apply]

theorem gp06_action_hamiltonian (u : E) :
    ((-Complex.I) / 2) •
      (toDual ℝ E).symm (fderiv ℝ (fun v : E => ‖v‖ ^ 2) u) = (-Complex.I) • u := by
  rw [gp06_action_real_gradient]
  rw [show (2 : ℝ) • u = (2 : ℂ) • u by simp [two_smul], smul_smul]
  congr 1
  norm_num

omit [CompleteSpace E] in
theorem gp06_action_rotation (u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) * Complex.I) • u)
      ((-Complex.I) • (Complex.exp (-(t : ℂ) * Complex.I) • u)) t := by
  have h : HasDerivAt (fun s : ℝ => -(s : ℂ) * Complex.I) (-Complex.I) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt).neg.mul_const Complex.I :
      HasDerivAt (fun s : ℝ => -(s : ℂ) * Complex.I) _ t)
  simpa only [smul_smul, mul_comm] using h.cexp.smul_const u

omit [CompleteSpace E] in
theorem gp06_action_rotation_initial (u : E) :
    Complex.exp (-(0 : ℂ) * Complex.I) • u = u := by simp

end QuantumNLS.Ext025A

#print axioms QuantumNLS.Ext025A.gp06_action_real_gradient
#print axioms QuantumNLS.Ext025A.gp06_action_hamiltonian
#print axioms QuantumNLS.Ext025A.gp06_action_rotation
#print axioms QuantumNLS.Ext025A.gp06_action_rotation_initial
