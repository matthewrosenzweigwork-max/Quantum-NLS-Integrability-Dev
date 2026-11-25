import QuantumNLS.InverseFinalR02
/-! integrator-authored trusted spec for R-154AFD4C cor:inverse (final): headline statement(s) copied verbatim from InverseFinalR02 (QuantumNLS.InverseFinalR02). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal
open Filter Topology
noncomputable section
namespace QuantumNLS.R154Spec
open QuantumNLS.InverseFinalR02
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)
open QuantumNLS.ColumnFinalR02 (Gamma w hierarchyFlows)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem inverse_final_spec (hκ : 0 < κ) :
    InverseR01.InverseStatement154AFD4C hκ (Def021ChartR41b.chart L κ hκ)
      (DynamicGaugeFinalR35m.gauge (L := L) hκ)
      (ActualModelTargetR53a.flowMap
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)))
      (ActualModelTargetR53a.flow_isHam
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))) := by
  first
  | exact QuantumNLS.InverseFinalR02.inverse_final
  | (apply QuantumNLS.InverseFinalR02.inverse_final <;> assumption)

set_option maxHeartbeats 8000000 in
theorem inverse_printed_spec (hκ : 0 < κ) :
    ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
    ∀ (ψ : ∀ n : ℕ, HN L (1 + n)), (∀ n, ‖ψ n‖ = 1) →
      Tendsto (fun n => ‖ψ n - ReconstructionR33m.product u n‖) atTop (𝓝 0) →
    ∀ b : ℤ, 0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖ →
      Tendsto (fun n => ⨆ t : K, ENNReal.ofReal
          ‖(Def021ChartR41b.chart L κ hκ).Ψ
              ((((‖Gamma hκ R ψ n t (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ R ψ n t (oneBasis b)) -
            (conj (w hκ u R t b) / ((‖w hκ u R t b‖ : ℝ) : ℂ)) •
              physical (jointSmooth (ActualModelTargetR53a.hamFlows (hierarchyFlows (L := L) hκ) R) t u)‖)
        atTop (𝓝 0) := by
  first
  | exact QuantumNLS.InverseFinalR02.inverse_printed
  | (apply QuantumNLS.InverseFinalR02.inverse_printed <;> assumption)

end QuantumNLS.R154Spec
#print axioms QuantumNLS.R154Spec.inverse_final_spec
#print axioms QuantumNLS.R154Spec.inverse_printed_spec
