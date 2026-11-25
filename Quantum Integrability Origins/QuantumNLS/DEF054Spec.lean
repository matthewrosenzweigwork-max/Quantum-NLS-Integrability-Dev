import QuantumNLS.FullCharacterProjection
/-! integrator-authored trusted spec for DEF-054 "Full-character projection of a physical operator"
(DEFINITIONS_LEDGER.md; dynamic_full_torus.tex eq:dynft-Haar-seed), REALIZED parametric (Terra r132) for a supplied
complete physical basis b: for bounded T_N and fixed labels a, c, the component is the strong (vector) integral
∫ e^{i(θ_a−θ_c)} V_N(θ)^* T_N V_N(θ) x dθ against the full product Haar probability (V_N unitary, V_N^* = V_N⁻¹),
with every exterior occupation retained; it is a bounded operator with ‖·‖ ≤ ‖T‖. -/
namespace DEF054Spec
open QuantumNLS QuantumNLS.FullCharacterProjection QuantumNLS.CountRotations QuantumNLS.BetheLabels
  QuantumNLS.BetheCoefficientTransform MeasureTheory

theorem spec :
    (∀ (a c : ℤ) (θ : AngleTorus), character a c θ = ((θ a / θ c : Circle) : ℂ)) ∧
    IsProbabilityMeasure productHaar ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N) (a c : ℤ) (x : HN L N),
      component b T a c x =
        ∫ θ, ((θ a / θ c : Circle) : ℂ) • (quantumRotation b θ).symm (T (quantumRotation b θ x)) ∂productHaar ∧
      Integrable (fun θ => ((θ a / θ c : Circle) : ℂ) • (quantumRotation b θ).symm (T (quantumRotation b θ x)))
        productHaar ∧
      ‖component b T a c x‖ ≤ ‖T‖ * ‖x‖) :=
  ⟨fun _ _ _ => rfl, inferInstance,
    fun L _ N b T a c x => ⟨component_apply b T a c x, integrand_integrable b T a c x, componentVector_bound b T a c x⟩⟩

end DEF054Spec
#print axioms DEF054Spec.spec
