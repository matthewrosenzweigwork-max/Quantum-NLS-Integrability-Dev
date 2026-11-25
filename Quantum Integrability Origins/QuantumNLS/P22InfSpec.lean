import QuantumNLS.Prop022AExact
/-! integrator-authored trusted spec for PROP-022 Q7B:lem:pair (Prop022AExact): headline statement(s) copied verbatim from Prop022AExact (QuantumNLS.Prop022AExact). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.P22InfSpec
open QuantumNLS.Prop022AExact
open TensorCarrier PhysicalTensor Prop022GAntiHS Prop022GClassical Prop022GLinear Prop022FactorialMajorantR115
open Prop022AFock Prop022AIndep Ext025B3PhysicalSectors Prop022GTensor

set_option maxHeartbeats 8000000 in
theorem PROP022_general_infinite_exact_spec {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H)
    (L : ℝ) [Fact (0 < L)]
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    Nonempty (H ≃ₗᵢ[ℂ] L2T L) ∧
    ∀ U : H ≃ₗᵢ[ℂ] L2T L,
    (
      let F := symbolH K
      let grad := gradH U K
      let Φ := flowH U K M A hA.le hK hs
      let u := profH U K M A hA.le hK hs u₀ hu₀
      let S := SH U K M A hA.le hK hs u₀ hu₀
      let a := aH U K M A hA.le hK hs u₀ hu₀
      let b := bH U K M A hA.le hK hs u₀ hu₀
      let α := alphaH U K M A hA.le hK hs u₀ hu₀
      let β := betaH U K M A hA.le hK hs u₀ hu₀
      -- the classical data: F intrinsic on H, its gradient, F = F_L ∘ U
      (∀ v, HasFDerivAt F (realDual (grad v)) v) ∧
      (∀ v, F v = Prop022ClassicalTimeR116.classicalSeries (BL U K) (U v)) ∧
      -- the flow -i∇F, the trajectory (unique among unit solutions), S = DΦ_{t-s}(u_s)
      (∀ x, Φ 0 x = x ∧ ∀ t, HasDerivAt (fun r => Φ r x) ((-Complex.I) • grad (Φ t x)) t ∧
        ‖Φ t x‖ = ‖x‖) ∧
      (u 0 = u₀ ∧ ∀ t, ‖u t‖ = 1 ∧ HasDerivAt u ((-Complex.I) • grad (u t)) t) ∧
      (∀ γ : ℝ → H, γ 0 = u₀ → (∀ t, ‖γ t‖ = 1 ∧ HasDerivAt γ ((-Complex.I) • grad (γ t)) t) →
        γ = u) ∧
      (∀ s t, Φ (t - s) (u s) = u t) ∧
      (∀ t s, S t s = fderiv ℝ (Φ (t - s)) (u s)) ∧
      -- (1) b_t Hilbert--Schmidt (in the arbitrary basis e) and both printed bounds
      (∀ t, CLinear (a t) ∧ (∀ x y, ⟪x, a t y⟫_ℂ = ⟪a t x, y⟫_ℂ) ∧
        Antilinear (b t) ∧ (∀ x y, ⟪x, b t y⟫_ℂ = ⟪y, b t x⟫_ℂ) ∧
        antiHS e (b t) ≠ ⊤ ∧ Real.sqrt ((antiHS e (b t)).toReal) ≤ pairMajorant A * M ∧
        ‖a t‖ ≤ M * ∑' r : ℕ, (((r+1 : ℕ) : ℝ)^2 * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ))) ∧
      -- (2) the linearized equation and S = α + β with α complex-linear, β antilinear
      (∀ s t x, Complex.I • deriv (fun r => S r s x) t = a t (S t s x) + b t (S t s x)) ∧
      (∀ t s, S t s = α t s + β t s ∧ CLinear (α t s) ∧ Antilinear (β t s)) ∧
      -- (3) the β estimate under the printed P hypothesis, including negative time
      ((∀ r q : ℝ, |r| ≤ T → |q| ≤ T → ‖S r q‖ ≤ P) → ∀ t, |t| ≤ T →
        antiHS e (β t 0) ≠ ⊤ ∧ Real.sqrt ((antiHS e (β t 0)).toReal) ≤ |t| * pairMajorant A * M * P) ∧
      -- independence of the transporting unitary
      (∀ U' : H ≃ₗᵢ[ℂ] L2T L, gradH U' K = grad ∧ profH U' K M A hA.le hK hs u₀ hu₀ = u ∧
        SH U' K M A hA.le hK hs u₀ hu₀ = S ∧ aH U' K M A hA.le hK hs u₀ hu₀ = a ∧
        bH U' K M A hA.le hK hs u₀ hu₀ = b ∧ alphaH U' K M A hA.le hK hs u₀ hu₀ = α ∧
        betaH U' K M A hA.le hK hs u₀ hu₀ = β)
    ) ∧
    (
      let hM0 : 0 ≤ M := by linarith
      let V := VH U K M A hA.le hK hs u₀ hu₀ hM0
      (∀ s x, V s s x = x) ∧
      (∀ r s t x, V t s (V s r x) = V t r x) ∧
      (∀ s x, Continuous (fun t => V t s x)) ∧
      (∀ s t (x : FockSpace H), (∀ j : ℕ, x ∈ momentDomainH j) →
        HasDerivAt (fun r => V r s x)
          ((-Complex.I) • QH U (aSym U K M A hA.le hK hs u₀ hu₀ t) (bSym U K M A hA.le hK hs u₀ hu₀ t)
            (V t s x)) t) ∧
      (∀ s t (v : H) (x : FockSpace H),
        V t s (WH U v ((V t s).symm x)) =
          WH U (SH U K M A hA.le hK hs u₀ hu₀ t s v) x) ∧
      (∀ t, QFH U (V t 0 (vacH U)) ∧ ‖V t 0 (vacH U)‖ = 1 ∧
        numExpH (V t 0 (vacH U)) = antiHS e (betaH U K M A hA.le hK hs u₀ hu₀ t 0))
    ) ∧
    ((∀ (U' : H ≃ₗᵢ[ℂ] L2T L) (v : H), WH U' v = WH U v) ∧
      (∀ U' : H ≃ₗᵢ[ℂ] L2T L, vacH U' = vacH U) ∧
      (∀ (U' : H ≃ₗᵢ[ℂ] L2T L) (t : ℝ),
        QFH U' (VH U K M A hA.le hK hs u₀ hu₀ (by linarith) t 0 (vacH U))) ∧
      (∀ (U' : H ≃ₗᵢ[ℂ] L2T L) (t s : ℝ),
        VH U' K M A hA.le hK hs u₀ hu₀ (by linarith) t s =
          VH U K M A hA.le hK hs u₀ hu₀ (by linarith) t s) ∧
      (∀ (U' : H ≃ₗᵢ[ℂ] L2T L) (t : ℝ),
        aSym U' K M A hA.le hK hs u₀ hu₀ t = aSym U K M A hA.le hK hs u₀ hu₀ t ∧
        bSym U' K M A hA.le hK hs u₀ hu₀ t = bSym U K M A hA.le hK hs u₀ hu₀ t) ∧
      (∀ (U' : H ≃ₗᵢ[ℂ] L2T L) (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2)
        (y : FockSpace H), QH U' a b y = QH U a b y)) := by
  first
  | exact QuantumNLS.Prop022AExact.PROP022_general_infinite_exact
  | (apply QuantumNLS.Prop022AExact.PROP022_general_infinite_exact <;> assumption)

end QuantumNLS.P22InfSpec
#print axioms QuantumNLS.P22InfSpec.PROP022_general_infinite_exact_spec
