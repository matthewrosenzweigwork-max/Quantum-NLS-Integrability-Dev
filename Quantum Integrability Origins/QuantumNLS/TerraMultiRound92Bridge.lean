import QuantumNLS.TerraMultiRound88Input
import QuantumNLS.TerraMultiRound91Assembly
import QuantumNLS.TerraMultiRound91FlowRotation
import QuantumNLS.ActualModelCorollaryR58a
import QuantumNLS.DynSeedR47b

/-! R-B2E70586: bind the conditional R58a estimate to the R91 intermediate.
The R58a predecessor inputs remain explicit; acceptance is not asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
noncomputable section
open Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.TraceClass
open QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.ActualModelCorollaryR53a QuantumNLS.ActualModelQuantumR52a
open QuantumNLS.HighAngleRotations QuantumNLS.CountRotations
open QuantumNLS.TerraMultiRound89FiniteAngle QuantumNLS.TerraMultiRound91Mixed
open QuantumNLS.TerraMultiRound91Comparison
namespace QuantumNLS.TerraMultiRound92Bridge
variable {L κ : ℝ} [Fact (0 < L)]

/-- The complete fixed-box estimate implies exactly the R91 finite input. -/
theorem mixed_of_estimate (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (estimate : TerraMultiRound88Input.RE679E41DInput hκ H)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (orders : Finset ℕ) :
    MixedFiniteInput hκ u orders := by
  intro I k T hT
  have lim := TerraMultiRound88Input.finite_box_product_intermediate hκ H estimate u hu
    I orders k (fun _ => Real.pi) T (by intro n hn; exact Real.pi_pos.le) hT
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds lim
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with N
    by_cases hk : k ≤ N + 1
    · rw [dif_pos hk, dif_pos hk]
      unfold mixedError
      apply iSup_le
      intro t
      apply iSup_le
      intro θ
      let a : {a : ℤ → ℝ // ∀ n ∈ I, |a n| ≤ (fun _ => Real.pi) n} :=
        ⟨representative θ, fun n _ => representative_bound θ n⟩
      change mixedTerm hκ u orders I k N hk t.val θ ≤ boxError hκ _ _ u I orders (fun _ => Real.pi) T k N hk _
      unfold boxError
      apply le_iSup_of_le t
      apply le_iSup_of_le a
      simp only [mixedTerm, a, count_unitary_eq_rotation,
        TerraMultiRound91FlowRotation.target_eq_rotation_after_flow, rotate,
        classical_angle_same_parameter, le_refl]
    · simp [hk]

/-- R58a directly inhabits the entire fixed-box estimate type consumed above. -/
theorem r58_type_comparison (hκ : 0 < κ)
    (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    TerraMultiRound88Input.RE679E41DInput hκ HierarchyInput := by
  intro u hu I R k Θ T hΘ hT
  exact ActualModelCorollaryR58a.cor_MP_actual_model_intermediate hκ Prop021Input
    WindowInput HierarchyInput u hu I R k Θ T hΘ hT

/-- R58a supplies R91's exact fixed-profile finite-angle input. -/
theorem mixed_of_r58 (hκ : 0 < κ)
    (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (orders : Finset ℕ) :
    MixedFiniteInput hκ u orders :=
  mixed_of_estimate hκ HierarchyInput
    (r58_type_comparison hκ Prop021Input WindowInput HierarchyInput) u hu orders

/-- Conditional full-torus convergence, with exactly the remaining R58a inputs. -/
theorem full_torus_r58 (hκ : 0 < κ)
    (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (orders : Finset ℕ)
    (k : ℕ) (T : ℕ → ℝ) (hT : ∀ r ∈ orders, 0 ≤ T r) :
    Tendsto (fun N => if hk : k ≤ N+1 then fullError hκ u orders T k N hk else 0)
      atTop (𝓝 0) :=
  TerraMultiRound91Assembly.full_torus_intermediate hκ u hu orders
    (mixed_of_r58 hκ Prop021Input WindowInput HierarchyInput u hu orders) k T hT

/-- R47b uses arbitrary compact boxes with inactive coordinates zero. Its
conclusion follows from R91's larger centered boxes on the same flow. -/
theorem full_torus_to_r47 (hκ : 0 < κ) (u : Smooth L) (orders : Finset ℕ)
    (H : ∀ (k : ℕ) (T : ℕ → ℝ), (∀ r ∈ orders, 0 ≤ T r) →
      Tendsto (fun N => if hk : k ≤ N+1 then fullError hκ u orders T k N hk else 0)
        atTop (𝓝 0)) :
    DynSeedInputR47b.DynftFullTorusInput hκ
      (higher (ActualModelBindingR53a.hierarchy_intermediate hκ
        (RB7BindFinal.hierarchyInputR25m_unconditional hκ))) u orders := by
  intro _ k lo hi
  let T : ℕ → ℝ := fun r => max |lo r| |hi r|
  have hT : ∀ r ∈ orders, 0 ≤ T r := by
    intro r hr
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  have lim := H k T hT
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds lim
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with N
    by_cases hk : k ≤ N + 1
    · rw [dif_pos hk, dif_pos hk]
      apply iSup_le
      intro t
      apply iSup_le
      intro θ
      have ht : ∀ r ∈ orders, |t.val r| ≤ T r := by
        intro r hr
        have h := t.property r
        simp only [hr, ↓reduceIte, Set.mem_Icc] at h
        dsimp [T]
        apply abs_le.mpr
        constructor
        · have hle : - max |lo r| |hi r| ≤ lo r := by
            have hh := neg_abs_le (lo r)
            have hm := le_max_left |lo r| |hi r|
            linarith
          linarith
        · exact h.2.trans ((le_abs_self _).trans (le_max_right _ _))
      let t' : {t : ℕ → ℝ // ∀ r ∈ orders, |t r| ≤ T r} := ⟨t.val, ht⟩
      unfold fullError
      apply le_iSup_of_le t'
      apply le_iSup_of_le θ
      simp only [DynSeedInputR47b.marginalError, DynSeedInputR47b.quantumOrbit,
        DynSeedInputR47b.physicalAngle, DynSeedInputR47b.classicalOrbit,
        fullTerm, coordinateRotation, t']
      rfl
    · simp [hk]

/-- The R58a-backed result inhabits the exact downstream R47b input. -/
theorem dynft_full_torus_r47 (hκ : 0 < κ)
    (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (orders : Finset ℕ) :
    DynSeedInputR47b.DynftFullTorusInput hκ
      (higher (ActualModelBindingR53a.hierarchy_intermediate hκ
        (RB7BindFinal.hierarchyInputR25m_unconditional hκ))) u orders :=
  full_torus_to_r47 hκ u orders
    (full_torus_r58 hκ Prop021Input WindowInput HierarchyInput u hu orders)

#print axioms full_torus_to_r47
#print axioms dynft_full_torus_r47
#print axioms mixed_of_estimate
#print axioms r58_type_comparison
#print axioms mixed_of_r58
#print axioms full_torus_r58
end QuantumNLS.TerraMultiRound92Bridge
