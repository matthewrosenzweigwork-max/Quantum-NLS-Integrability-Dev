import QuantumNLS.TerraMultiFinalR94
/-! integrator-authored trusted spec for R-B2E70586 / R-300B8640 / R-D51987CA finals (no named inputs): headline statement(s) copied verbatim from TerraMultiFinalR94 (QuantumNLS.TerraMultiFinalR94). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
noncomputable section
open Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.TerraMultiRound91Mixed QuantumNLS.TerraMultiRound91Comparison
open QuantumNLS.DynSeedInputR47b QuantumNLS.RetargetFinalProofR48b
namespace QuantumNLS.RB2EChainSpec
open QuantumNLS.TerraMultiFinalR94
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem full_torus_final_spec (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (k : ℕ) (T : ℕ → ℝ) (hT : ∀ r ∈ R, 0 ≤ T r) :
    Tendsto (fun N => if hk : k ≤ N+1 then fullError hκ u R T k N hk else 0)
      atTop (𝓝 0) := by
  first
  | exact QuantumNLS.TerraMultiFinalR94.full_torus_final
  | (apply QuantumNLS.TerraMultiFinalR94.full_torus_final <;> assumption)

set_option maxHeartbeats 8000000 in
theorem seed_final_spec (hκ : 0 < κ) (w : L2T L → REF88Chart.K)
    (hw : REF88PrintedChart.PrintedChart hκ w) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b) :
    DynSeedR47b.SeedStatement hκ (Bind7BR300B8640A01.hierFlow hκ w hw) u R lo hi a b := by
  first
  | exact QuantumNLS.TerraMultiFinalR94.seed_final
  | (apply QuantumNLS.TerraMultiFinalR94.seed_final <;> assumption)

set_option maxHeartbeats 8000000 in
theorem chain_named_final_spec (hκ : 0 < κ) (w : L2T L → REF88Chart.K)
    (hw : REF88PrintedChart.PrintedChart hκ w) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b) :
    DynSeedR47b.SeedStatement hκ (Bind7BR300B8640A01.hierFlow hκ w hw) u R lo hi a b ∧
    GaugeConclusion (L := L) hκ (RetargetSelectionR49b.sectorStage (L := L) hκ)
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) := by
  first
  | exact QuantumNLS.TerraMultiFinalR94.chain_named_final
  | (apply QuantumNLS.TerraMultiFinalR94.chain_named_final <;> assumption)

end QuantumNLS.RB2EChainSpec
#print axioms QuantumNLS.RB2EChainSpec.full_torus_final_spec
#print axioms QuantumNLS.RB2EChainSpec.seed_final_spec
#print axioms QuantumNLS.RB2EChainSpec.chain_named_final_spec
