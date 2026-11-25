import QuantumNLS.TerraMultiRound93Chain
import QuantumNLS.ActualModelCorollaryR60a
import QuantumNLS.FullWickO5

/-! Author binding of the three frozen intermediate statements. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
noncomputable section
open Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.TerraMultiRound91Mixed QuantumNLS.TerraMultiRound91Comparison
open QuantumNLS.DynSeedInputR47b QuantumNLS.RetargetFinalProofR48b
namespace QuantumNLS.TerraMultiFinalR94
variable {L κ : ℝ} [Fact (0 < L)]

/-- The final actual-model theorem inhabits the full frozen predecessor type. -/
theorem predecessor_type_comparison (hκ : 0 < κ) :
    TerraMultiRound88Input.RE679E41DInput hκ
      (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ) := by
  intro u hu I R k Θ T hΘ hT
  exact ActualModelCorollaryR60a.cor_MP_actual_model hκ u hu I R k Θ T hΘ hT

/-- Mixed finite-angle convergence is derived from the final actual-model estimate. -/
theorem mixed_final (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) : MixedFiniteInput hκ u R :=
  TerraMultiRound92Bridge.mixed_of_estimate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional hκ)
    (predecessor_type_comparison hκ) u hu R

/-- R-B2E70586, at the frozen R91 full-torus conclusion. -/
theorem full_torus_final (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (k : ℕ) (T : ℕ → ℝ) (hT : ∀ r ∈ R, 0 ≤ T r) :
    Tendsto (fun N => if hk : k ≤ N+1 then fullError hκ u R T k N hk else 0)
      atTop (𝓝 0) :=
  TerraMultiRound91Assembly.full_torus_intermediate hκ u hu R (mixed_final hκ u hu R) k T hT

/-- Type comparison and R92 adapter into the exact R47b predecessor. -/
theorem full_torus_r47 (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) : DynftFullTorusInput hκ (TerraMultiRound93Compose.selected hκ) u R :=
  TerraMultiRound92Bridge.full_torus_to_r47 hκ u R (full_torus_final hκ u hu R)

/-- R-300B8640, with both frozen input types discharged and flows transported on smooth data. -/
theorem seed_final (hκ : 0 < κ) (w : L2T L → REF88Chart.K)
    (hw : REF88PrintedChart.PrintedChart hκ w) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b) :
    DynSeedR47b.SeedStatement hκ (Bind7BR300B8640A01.hierFlow hκ w hw) u R lo hi a b := by
  let F := Bind7BR300B8640A01.hierFlow hκ w hw
  have hm : MixedFinite hκ F u R := TerraMultiRound93Compose.mixed_flow hκ _ _ u R
    (TerraMultiRound93Compose.mixed_to_r47 hκ u R (mixed_final hκ u hu R))
  have hf : DynftFullTorusInput hκ F u R := by
    intro _
    exact TerraMultiRound93Compose.full_flow hκ _ _ u R
      (full_torus_r47 hκ u hu R (TerraMultiRound93Compose.mixed_to_r47 hκ u R (mixed_final hκ u hu R)))
  exact Bind7BR300B8640A01.dynft_seed_hierarchy hκ w hw u hu R lo hi a b hab hm hf

/-- R93 chain with its gauge conjunct pinned to the specified named pair. -/
theorem chain_named_final (hκ : 0 < κ) (w : L2T L → REF88Chart.K)
    (hw : REF88PrintedChart.PrintedChart hκ w) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b) :
    DynSeedR47b.SeedStatement hκ (Bind7BR300B8640A01.hierFlow hκ w hw) u R lo hi a b ∧
    GaugeConclusion (L := L) hκ (RetargetSelectionR49b.sectorStage (L := L) hκ)
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) := by
  have hc := TerraMultiRound93Chain.chain_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional hκ) (predecessor_type_comparison hκ)
    w hw u hu R lo hi a b hab
  exact FullWickO5.pin_gauge_conjunct hκ ⟨seed_final hκ w hw u hu R lo hi a b hab, hc.2⟩

/-- Frozen R93 existential comparison follows from the named binding. -/
theorem chain_frozen_type_comparison (hκ : 0 < κ) (w : L2T L → REF88Chart.K)
    (hw : REF88PrintedChart.PrintedChart hκ w) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b) :
    DynSeedR47b.SeedStatement hκ (Bind7BR300B8640A01.hierFlow hκ w hw) u R lo hi a b ∧
    (∃ (s : ℕ → ℕ) (q : ∀ n, Occupation.Arr (n+1) → FullOccupationAffinity.Phase),
      GaugeConclusion (L := L) hκ s q) := by
  have h := chain_named_final hκ w hw u hu R lo hi a b hab
  exact ⟨h.1, _, _, h.2⟩

#print axioms predecessor_type_comparison
#print axioms mixed_final
#print axioms full_torus_final
#print axioms full_torus_r47
#print axioms seed_final
#print axioms chain_named_final
#print axioms chain_frozen_type_comparison
end QuantumNLS.TerraMultiFinalR94
