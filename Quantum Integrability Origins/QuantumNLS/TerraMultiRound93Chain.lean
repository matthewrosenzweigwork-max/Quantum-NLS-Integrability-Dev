import QuantumNLS.TerraMultiRound93Compose

/-! R-300B8640 and R-D51987CA composition, intermediate only. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open QuantumNLS.PhysicalTensor QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.DynSeedInputR47b QuantumNLS.DynSeedClassicalR47b
open QuantumNLS.RetargetFinalProofR48b
namespace QuantumNLS.TerraMultiRound93Chain
variable {L κ : ℝ} [Fact (0 < L)]

/-- The unchanged R-E679E41D printed estimate is the single provisional
predecessor input. The two conclusions are exactly the frozen seed and
R48b gauge-intermediate conclusion types at the hierarchy-selected flow. -/
theorem chain_intermediate (hκ : 0 < κ)
    (HierarchyInput : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (PredecessorInput : QuantumNLS.TerraMultiRound93Compose.RE679E41DInput hκ HierarchyInput)
    (w : L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b) :
    QuantumNLS.DynSeedR47b.SeedStatement hκ
      (QuantumNLS.Bind7BR300B8640A01.hierFlow hκ w hw) u R lo hi a b ∧
    (∃ (s : ℕ → ℕ) (q : ∀ n, QuantumNLS.Occupation.Arr (n+1) → QuantumNLS.FullOccupationAffinity.Phase),
      GaugeConclusion (L := L) hκ s q) := by
  let F := QuantumNLS.Bind7BR300B8640A01.hierFlow hκ w hw
  have hInputs := QuantumNLS.TerraMultiRound93Compose.inputs_intermediate hκ HierarchyInput PredecessorInput w hw u hu R
  have hs := QuantumNLS.Bind7BR300B8640A01.dynft_seed_hierarchy hκ w hw u hu R lo hi a b hab hInputs.1 hInputs.2
  have hg := QuantumNLS.RetargetPhysicalR48b.retarget_with_seed_intermediate hκ F u hu R lo hi a b hab
    (QuantumNLS.Bind7BR300B8640A01.flow_actions_of hκ F
      (QuantumNLS.Bind7BR300B8640A01.hierFlow_action hκ w hw) u R lo hi) hInputs.1 hInputs.2
  exact ⟨hs, hg.2⟩

/-- Author-built R58a supplies the exact unchanged input, under its recorded
remaining inputs and DEF-044 realization gates. This is not final acceptance. -/
theorem chain_r58_intermediate (hκ : 0 < κ)
    (Prop021Input : QuantumNLS.Prop025OInputs.Prop021Input (L := L))
    (WindowInput : QuantumNLS.Prop025OInputs.WindowInput (L := L) hκ)
    (HierarchyInput : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (w : L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b) :
    QuantumNLS.DynSeedR47b.SeedStatement hκ
      (QuantumNLS.Bind7BR300B8640A01.hierFlow hκ w hw) u R lo hi a b ∧
    (∃ (s : ℕ → ℕ) (q : ∀ n, QuantumNLS.Occupation.Arr (n+1) → QuantumNLS.FullOccupationAffinity.Phase),
      GaugeConclusion (L := L) hκ s q) :=
  chain_intermediate hκ HierarchyInput
    (QuantumNLS.TerraMultiRound92Bridge.r58_type_comparison hκ Prop021Input WindowInput HierarchyInput)
    w hw u hu R lo hi a b hab

/-- Type comparisons against the frozen intermediates' conclusion forms. -/
theorem seed_type_comparison (hκ : 0 < κ)
    (H : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (PredecessorInput : QuantumNLS.TerraMultiRound93Compose.RE679E41DInput hκ H)
    (w : L2T L → QuantumNLS.REF88Chart.K) (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ)
    (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b) :
    QuantumNLS.DynSeedR47b.SeedStatement hκ
      (QuantumNLS.Bind7BR300B8640A01.hierFlow hκ w hw) u R lo hi a b :=
  (chain_intermediate hκ H PredecessorInput w hw u hu R lo hi a b hab).1

theorem gauge_type_comparison (hκ : 0 < κ)
    (H : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (PredecessorInput : QuantumNLS.TerraMultiRound93Compose.RE679E41DInput hκ H)
    (w : L2T L → QuantumNLS.REF88Chart.K) (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ)
    (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b) :
    (∃ (s : ℕ → ℕ) (q : ∀ n, QuantumNLS.Occupation.Arr (n+1) → QuantumNLS.FullOccupationAffinity.Phase),
      GaugeConclusion (L := L) hκ s q) :=
  (chain_intermediate hκ H PredecessorInput w hw u hu R lo hi a b hab).2

#print axioms chain_intermediate
#print axioms chain_r58_intermediate
#print axioms seed_type_comparison
#print axioms gauge_type_comparison
end QuantumNLS.TerraMultiRound93Chain
