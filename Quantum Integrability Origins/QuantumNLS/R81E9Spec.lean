import QuantumNLS.D01LocalPrimitive
/-! integrator-authored trusted spec for R-81E9AAB6 lem:global-D01-local-primitive (Terra r157 ACCEPT, parametric over the printed hypotheses): headline statement(s) copied verbatim from D01LocalPrimitive (QuantumNLS.D01LocalPrimitive). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped ComplexConjugate Topology ENNReal
open Filter Set
namespace QuantumNLS.R81E9Spec
open QuantumNLS.D01LocalPrimitive
open QuantumNLS.SymplecticBracket QuantumNLS.StrongSymplectic QuantumNLS.RealAnalyticDef
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Hyp H)

set_option maxHeartbeats 8000000 in
theorem local_primitive_lemma_spec {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Hyp H) :
    (∀ u ∈ S.B, ‖S.phi u‖ = ‖u‖) ∧
    (∀ (n : ℤ) (z : K), hamField (q n) z = Xq n z) ∧
    (∀ u ∈ S.B, ∀ n : ℤ, fderiv ℝ S.phi u (hamField (fun v => S.act v n) u) = Xq n (S.phi u)) ∧
    (∀ u ∈ S.B, ∀ θ : Tor, S.phi (S.rho θ u) = Rot θ (S.phi u)) ∧
    (∀ u ∈ S.B, ∀ h : H, alphaF (S.phi u) (fderiv ℝ S.phi u h) = S.abar u h) ∧
    (∀ u ∈ S.B, ∀ h : H, omega (S.Y u) h = S.abar u h) ∧
    (∀ u ∈ S.B, fderiv ℝ S.phi u (S.Y u) = (2⁻¹ : ℂ) • S.phi u) := by
  first
  | exact QuantumNLS.D01LocalPrimitive.local_primitive_lemma
  | (apply QuantumNLS.D01LocalPrimitive.local_primitive_lemma <;> assumption)

end QuantumNLS.R81E9Spec
#print QuantumNLS.D01LocalPrimitive.Hyp
#print axioms QuantumNLS.R81E9Spec.local_primitive_lemma_spec
