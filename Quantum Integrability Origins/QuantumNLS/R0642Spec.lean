import QuantumNLS.RootHilbertL2
/-! integrator-authored trusted spec for R-064239ED lem:root-Hilbert-truncations (ROOT_scalar_uniqueness.tex:11–67)
(Terra r132 ACCEPT). For ρ ≥ 0, ρ ∈ L¹ ∩ L^∞, locally Hölder: with H_ε ρ(x) = ∫_{|x−y|>ε} ρ(y)/(x−y) dy, the principal
value Hρ(x) = lim_{ε↓0} H_ε ρ(x) exists at every x, and H_ε ρ → Hρ in L²(dx) and in L²(ρ dx). -/
namespace R0642Spec
open QuantumNLS QuantumNLS.RootHilbert MeasureTheory Filter Topology
open scoped NNReal

theorem spec :
    (∀ (ρ : ℝ → ℝ) (ε x : ℝ), hilbertTrunc ρ ε x = ∫ y in {y : ℝ | ε < |x - y|}, ρ y / (x - y)) ∧
    (∀ (ρ : ℝ → ℝ), HilbertHyp ρ ↔ ((∀ x, 0 ≤ ρ x) ∧ Integrable ρ volume ∧ MemLp ρ ⊤ volume ∧
      ∀ x : ℝ, ∃ s ∈ 𝓝 x, ∃ C r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ HolderOnWith C r ρ s)) ∧
    (∀ (ρ : ℝ → ℝ), rhoMeasure ρ = (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (ρ x))) ∧
    (∀ {ρ : ℝ → ℝ}, HilbertHyp ρ →
      (∀ x, Tendsto (fun ε => hilbertTrunc ρ ε x) (𝓝[>] (0 : ℝ)) (𝓝 (hilbertPV ρ x))) ∧
      ((∀ ε : ℝ, 0 < ε → MemLp (hilbertTrunc ρ ε) 2 (volume : Measure ℝ)) ∧
        MemLp (hilbertPV ρ) 2 (volume : Measure ℝ) ∧
        Tendsto (fun ε => ∫ x, ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      ((∀ ε : ℝ, 0 < ε → MemLp (hilbertTrunc ρ ε) 2 (rhoMeasure ρ)) ∧
        MemLp (hilbertPV ρ) 2 (rhoMeasure ρ) ∧
        Tendsto (fun ε => ∫ x, ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ ^ 2 ∂(rhoMeasure ρ))
          (𝓝[>] (0 : ℝ)) (𝓝 0))) :=
  ⟨fun _ _ _ => rfl, fun _ => ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩,
    fun _ => rfl, fun hρ => root_Hilbert_truncations hρ⟩

end R0642Spec
#print axioms R0642Spec.spec
