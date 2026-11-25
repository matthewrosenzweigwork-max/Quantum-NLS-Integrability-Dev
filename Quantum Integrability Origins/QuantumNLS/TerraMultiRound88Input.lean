import QuantumNLS.ActualModelCorollaryR53a
import QuantumNLS.TerraMultiRound87Classical

/-! R-B2E70586 pre-start work. The single input below states the full
R-E679E41D estimate, not merely the fixed-product consequence used here.
It is an explicit hypothesis, not an axiom or a completed predecessor.
The hierarchy argument is the shared predecessor binding; the final theorem
must replace this input by the accepted R-E679E41D result. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter Topology
namespace QuantumNLS.TerraMultiRound88Input
open PhysicalTensor Def033HierarchyR24m ActualModelTargetR53a ActualModelCorollaryR53a
variable {L κ : ℝ} [Fact (0 < L)]

/-- The full printed estimate, on the actual chart and the physical flows,
for every smooth unit profile, finite labels and orders (including 0 and 1),
rank, and compact time and angle boxes. `MainEstimate` retains the exact
error, uniform normalized preparations, empty-angle clause, and ζ limit. -/
def RE679E41DInput (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ),
      (∀ n ∈ I, 0 ≤ Θ n) → (∀ r ∈ R, 0 ≤ T r) →
      MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ)
        (higher (ActualModelBindingR53a.hierarchy_intermediate hκ H)) u I R k Θ T

/-- The corollary's uniform finite-box convergence for the actual product,
including rank zero. The complete predecessor remains the one input above. -/
theorem finite_box_product_intermediate (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (Input : RE679E41DInput hκ H)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    Tendsto (fun N => if hk : k ≤ N + 1 then
      boxError hκ (ActualModelBindingR53a.chart (L := L) hκ)
        (higher (ActualModelBindingR53a.hierarchy_intermediate hκ H)) u I R Θ T k N hk
        (HighMomentsOps.wvec (N + 1) (physical u)) else 0) atTop (𝓝 0) := by
  apply convergence hκ _ _ u I R k Θ T (Input u hu I R k Θ T hΘ hT)
    (fun N => HighMomentsOps.wvec (N + 1) (physical u))
  · intro N
    change ‖TensorCarrier.htpow (N + 1) (physical u)‖ = 1
    rw [TensorCarrier.norm_htpow, hu, one_pow]
  · simpa [preparationError] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- The uniform classical cutoff uses the inverse of the actual chart, with
no lower bound on any action coordinate. -/
theorem actual_chart_cutoff (hκ : 0 < κ) (u : L2T L) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ x : ResetNormalizationUniqueness.S2 ℤ,
      (∀ n, ‖x n‖ = ‖(ActualModelBindingR53a.chart (L := L) hκ).Φ u n‖) →
      ∀ θ φ : ℤ → Circle, (∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = φ n) →
      dist ((ActualModelBindingR53a.chart (L := L) hκ).Ψ (ActionTorus.rotate θ x))
        ((ActualModelBindingR53a.chart (L := L) hκ).Ψ (ActionTorus.rotate φ x)) < ε := by
  apply TerraMultiRound87Classical.physical_radial_cutoff_of_equal_moduli
  exact continuous_iff_continuousAt.mpr (fun z =>
    ((ActualModelBindingR53a.chart (L := L) hκ).inverse_analytic z).continuousAt)
  exact hε

#print axioms finite_box_product_intermediate
#print axioms actual_chart_cutoff
#print RE679E41DInput
end QuantumNLS.TerraMultiRound88Input
