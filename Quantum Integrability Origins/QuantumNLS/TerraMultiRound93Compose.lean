import QuantumNLS.TerraMultiRound93Flow
import QuantumNLS.RetargetFinalProofR48b

/-! Conditional composition. The unaccepted R-E679E41D predecessor remains
an explicit, unchanged input; acceptance and final binding are separate. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
noncomputable section
open Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.HighAngleRotations QuantumNLS.CountRotations QuantumNLS.ActualModelQuantumR52a
open QuantumNLS.TerraMultiRound91Mixed QuantumNLS.TerraMultiRound91Comparison
open QuantumNLS.DynSeedInputR47b
namespace QuantumNLS.TerraMultiRound93Compose
variable {L κ : ℝ} [Fact (0 < L)]

def selected (hκ : 0 < κ) : HigherFlows L κ :=
  higher (QuantumNLS.ActualModelBindingR53a.hierarchy_intermediate hκ
    (QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional hκ))

/-- Exact complete frozen predecessor interface, unchanged. -/
abbrev RE679E41DInput (hκ : 0 < κ)
    (H : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) : Prop :=
  QuantumNLS.TerraMultiRound88Input.RE679E41DInput hκ H

/-- The R91 centered-box finite-angle input implies the R47b finite-angle
input for arbitrary two-sided boxes, with zero inactive times. -/
theorem mixed_to_r47 (hκ : 0 < κ) (u : Smooth L) (R : Finset ℕ)
    (h : MixedFiniteInput hκ u R) : MixedFinite hκ (selected hκ) u R := by
  intro I k lo hi
  let T : ℕ → ℝ := fun r => max |lo r| |hi r|
  have hT : ∀ r ∈ R, 0 ≤ T r := by
    intro r hr
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  have lim := h I k T hT
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds lim
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with N
    by_cases hk : k ≤ N+1
    · rw [dif_pos hk, dif_pos hk]
      apply iSup_le
      intro t
      apply iSup_le
      intro θ
      have ht : ∀ r ∈ R, |t.val r| ≤ T r := by
        intro r hr
        have hh := t.property r
        simp only [hr, ↓reduceIte, Set.mem_Icc] at hh
        dsimp [T]
        apply abs_le.mpr
        constructor
        · have ha := neg_abs_le (lo r)
          have hm := le_max_left |lo r| |hi r|
          linarith
        · exact hh.2.trans ((le_abs_self _).trans (le_max_right _ _))
      let t' : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r} := ⟨t.val, ht⟩
      have hθ : truncate I θ.val = θ.val := by
        funext i
        by_cases hi : i ∈ I
        · simp [truncate, hi]
        · simp [truncate, hi, θ.property i hi]
      unfold mixedError
      apply le_iSup_of_le t'
      apply le_iSup_of_le θ.val
      simp only [mixedTerm, marginalError, classicalOrbit, physicalAngle, selected, t', hθ]
      rfl
    · simp [hk]

/-- Transport the exact two R47b inputs across smooth joint-flow uniqueness. -/
theorem mixed_flow (hκ : 0 < κ) (F G : HigherFlows L κ) (u : Smooth L) (R : Finset ℕ)
    (h : MixedFinite hκ F u R) : MixedFinite hκ G u R := by
  have horbit (t : ℕ → ℝ) : classicalOrbit hκ F u R t = classicalOrbit hκ G u R t :=
    congrArg physical (QuantumNLS.TerraMultiRound93Flow.joint_eq F G R t u)
  simpa only [MixedFinite, horbit] using h

theorem full_flow (hκ : 0 < κ) (F G : HigherFlows L κ) (u : Smooth L) (R : Finset ℕ)
    (h : FullTorus hκ F u R) : FullTorus hκ G u R := by
  have horbit (t : ℕ → ℝ) : classicalOrbit hκ F u R t = classicalOrbit hκ G u R t :=
    congrArg physical (QuantumNLS.TerraMultiRound93Flow.joint_eq F G R t u)
  simpa only [FullTorus, horbit] using h

/-- The frozen R-B2E70586 adapter and the mixed input at the auxiliary construction's flow. -/
theorem inputs_intermediate (hκ : 0 < κ)
    (HierarchyInput : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (PredecessorInput : RE679E41DInput hκ HierarchyInput)
    (w : L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) :
    let F := QuantumNLS.Bind7BR300B8640A01.hierFlow hκ w hw
    MixedFinite hκ F u R ∧ DynftFullTorusInput hκ F u R := by
  have hm := QuantumNLS.TerraMultiRound92Bridge.mixed_of_estimate hκ HierarchyInput PredecessorInput u hu R
  have hm47 : MixedFinite hκ (selected hκ) u R := mixed_to_r47 hκ u R hm
  have hf : FullTorus hκ (selected hκ) u R :=
    QuantumNLS.TerraMultiRound92Bridge.full_torus_to_r47 hκ u R
      (QuantumNLS.TerraMultiRound91Assembly.full_torus_intermediate hκ u hu R hm) hm47
  exact ⟨mixed_flow hκ _ _ u R hm47, fun _ => full_flow hκ _ _ u R hf⟩

#print axioms mixed_to_r47
#print axioms mixed_flow
#print axioms full_flow
#print axioms inputs_intermediate
end QuantumNLS.TerraMultiRound93Compose
