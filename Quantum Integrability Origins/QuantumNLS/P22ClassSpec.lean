import QuantumNLS.Prop022BClass3
/-! integrator-authored trusted spec for PROP-022 Q7B:lem:pair (Prop022BClass3): headline statement(s) copied verbatim from Prop022BClass3 (QuantumNLS.Prop022BClass3). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.P22ClassSpec
open QuantumNLS.Prop022BClass3
open TensorCarrier PhysicalTensor Prop022GTensor Prop022AIsoTensor Prop022GAntiHS
open Prop022GClassical Prop022GLinear Prop022BIso Prop022BClass1 Prop022BClass2
open Prop022FactorialMajorantR115
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

include hM in
set_option maxHeartbeats 8000000 in
theorem PROP022_J_classical_spec (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    let F := symbolH K
    let grad := gradJ J K
    let Φ := flowJ J K M A hA.le hK hs
    let u := profJ J K M A hA.le hK hs u₀ hu₀
    let S := SJ J K M A hA.le hK hs u₀ hu₀
    let a := aJ J K M A hA.le hK hs u₀ hu₀
    let b := bJ J K M A hA.le hK hs u₀ hu₀
    let α := alphaJ J K M A hA.le hK hs u₀ hu₀
    let β := betaJ J K M A hA.le hK hs u₀ hu₀
    (∀ v, HasFDerivAt F (realDual (grad v)) v) ∧
    (∀ v, F v = Prop022ClassicalTimeR116.classicalSeries (BL (UI L) (kernelsI J K)) (J v)) ∧
    (∀ x, Φ 0 x = x ∧ ∀ t, HasDerivAt (fun r => Φ r x) ((-Complex.I) • grad (Φ t x)) t ∧
      ‖Φ t x‖ = ‖x‖) ∧
    (u 0 = u₀ ∧ ∀ t, ‖u t‖ = 1 ∧ HasDerivAt u ((-Complex.I) • grad (u t)) t) ∧
    (∀ γ : ℝ → H, γ 0 = u₀ → (∀ t, ‖γ t‖ = 1 ∧ HasDerivAt γ ((-Complex.I) • grad (γ t)) t) →
      γ = u) ∧
    (∀ s t, Φ (t - s) (u s) = u t) ∧
    (∀ t s, S t s = fderiv ℝ (Φ (t - s)) (u s)) ∧
    (∀ t, CLinear (a t) ∧ (∀ x y, ⟪x, a t y⟫_ℂ = ⟪a t x, y⟫_ℂ) ∧
      Antilinear (b t) ∧ (∀ x y, ⟪x, b t y⟫_ℂ = ⟪y, b t x⟫_ℂ) ∧
      antiHS e (b t) ≠ ⊤ ∧ Real.sqrt ((antiHS e (b t)).toReal) ≤ pairMajorant A * M ∧
      ‖a t‖ ≤ M * ∑' r : ℕ,
        (((r+1 : ℕ) : ℝ)^2 * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ))) ∧
    (∀ s t x, Complex.I • deriv (fun r => S r s x) t = a t (S t s x) + b t (S t s x)) ∧
    (∀ t s, S t s = α t s + β t s ∧ CLinear (α t s) ∧ Antilinear (β t s)) ∧
    ((∀ r q : ℝ, |r| ≤ T → |q| ≤ T → ‖S r q‖ ≤ P) → ∀ t, |t| ≤ T →
      antiHS e (β t 0) ≠ ⊤ ∧
        Real.sqrt ((antiHS e (β t 0)).toReal) ≤ |t| * pairMajorant A * M * P) ∧
    (∀ J' : H →ₗᵢ[ℂ] L2T L, gradJ J' K = grad ∧
      profJ J' K M A hA.le hK hs u₀ hu₀ = u ∧
      SJ J' K M A hA.le hK hs u₀ hu₀ = S ∧ aJ J' K M A hA.le hK hs u₀ hu₀ = a ∧
      bJ J' K M A hA.le hK hs u₀ hu₀ = b ∧ alphaJ J' K M A hA.le hK hs u₀ hu₀ = α ∧
      betaJ J' K M A hA.le hK hs u₀ hu₀ = β) := by
  first
  | exact QuantumNLS.Prop022BClass3.PROP022_J_classical J K M A hM hA hK hs u₀ hu₀ T P hP e
  | exact QuantumNLS.Prop022BClass3.PROP022_J_classical
  | (apply QuantumNLS.Prop022BClass3.PROP022_J_classical <;> assumption)

end QuantumNLS.P22ClassSpec
#print axioms QuantumNLS.P22ClassSpec.PROP022_J_classical_spec
