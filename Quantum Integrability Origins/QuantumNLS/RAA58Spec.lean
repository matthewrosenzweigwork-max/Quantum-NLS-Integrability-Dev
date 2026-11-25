import QuantumNLS.ColumnFinalR02
/-! integrator-authored trusted spec for R-AA5864B7 cor:column (final): headline statement(s) copied verbatim from ColumnFinalR02 (QuantumNLS.ColumnFinalR02). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal
open Filter Topology
noncomputable section
namespace QuantumNLS.RAA58Spec
open QuantumNLS.ColumnFinalR02
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem column_final_spec (hκ : 0 < κ) :
    ColumnR01.ColumnAA5864B7Statement hκ (Def021ChartR41b.chart L κ hκ)
      (DynamicGaugeFinalR35m.gauge (L := L) hκ)
      (ActualModelTargetR53a.flowMap
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)))
      (ActualModelTargetR53a.flow_isHam
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))) := by
  first
  | exact QuantumNLS.ColumnFinalR02.column_final
  | (apply QuantumNLS.ColumnFinalR02.column_final <;> assumption)

set_option maxHeartbeats 8000000 in
theorem column_printed_spec (hκ : 0 < κ) :
    ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
    ∀ (ψ : ∀ n : ℕ, HN L (1 + n)), (∀ n, ‖ψ n‖ = 1) →
      Tendsto (fun n => ‖ψ n - ReconstructionR33m.product u n‖) atTop (𝓝 0) →
    ∀ b : ℤ, 0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖ →
      (∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ t ∈ K,
          (c : ℂ) ≤ ⟪oneBasis b, Gamma hκ R ψ n t (oneBasis b)⟫_ℂ) ∧
      Tendsto (fun n => ⨆ t : K, ENNReal.ofReal
          ‖(((Real.sqrt ((Gamma hκ R ψ n t (oneBasis b)) b).re : ℝ) : ℂ))⁻¹ •
              Gamma hκ R ψ n t (oneBasis b) -
            (conj (w hκ u R t b) / ((‖w hκ u R t b‖ : ℝ) : ℂ)) • w hκ u R t‖)
        atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, ∀ t ∈ K, Gamma hκ R ψ n t (oneBasis b) ≠ 0 ∧
          ‖(((‖Gamma hκ R ψ n t (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ R ψ n t (oneBasis b) -
              (conj (w hκ u R t b) / ((‖w hκ u R t b‖ : ℝ) : ℂ)) • w hκ u R t‖ ≤
            2 * (⨆ s : K, traceNorm (Gamma hκ R ψ n s -
              ReconstructionR33m.projector (w hκ u R s))).toReal /
              ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖) ∧
      Tendsto (fun n => ⨆ t : K, ENNReal.ofReal
          ‖(((‖Gamma hκ R ψ n t (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ R ψ n t (oneBasis b) -
            (conj (w hκ u R t b) / ((‖w hκ u R t b‖ : ℝ) : ℂ)) • w hκ u R t‖)
        atTop (𝓝 0) := by
  first
  | exact QuantumNLS.ColumnFinalR02.column_printed
  | (apply QuantumNLS.ColumnFinalR02.column_printed <;> assumption)

end QuantumNLS.RAA58Spec
#print axioms QuantumNLS.RAA58Spec.column_final_spec
#print axioms QuantumNLS.RAA58Spec.column_printed_spec
