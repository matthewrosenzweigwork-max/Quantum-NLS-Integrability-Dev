import QuantumNLS.HierarchyInputR25m
import QuantumNLS.Def033AdjacentR24m
import QuantumNLS.Def033SobolevR25m

/-! DEF-033 restatement with the SAME complete printed predecessor input as
R-115CAA16. Sobolev homeomorphisms are an explicit printed ambient antecedent,
not a new hierarchy conclusion. Accepted scalar prerequisites are discharged.
No hierarchy proof or source-final theorem is supplied here. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
namespace QuantumNLS.Def033BindingR25m
open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow
open QuantumNLS.Def033HierarchyR24m QuantumNLS.Def033CoreR24m
variable {L κ : ℝ} [Fact (0 < L)]

theorem DEF033_from_printed_antecedents_intermediate (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (hSobolev : QuantumNLS.HierarchyInputR25m.SobolevHomeomorphisms w)
    (HierarchyR7B122087Input : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input
      (L := L) hκ) :
    ∃ (Ψ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΨ : ∀ r, IsHamFlow L (hamiltonian L κ r) (Ψ r)),
      (∀ r s, ∀ u : Smooth L, ∀ t τ, Ψ r t (Ψ s τ u.val) = Ψ s τ (Ψ r t u.val)) ∧
      ∀ r (u : Smooth L) n, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
        ∃! freq : ℝ, ActiveFrequency
          (fun t => w (physical ⟨Ψ r t u.val, ((hΨ r u.val u.property).2.2 t).1⟩) n)
          (w (physical u) n) freq := by
  have hFull := HierarchyR7B122087Input w hw hSobolev
    (QuantumNLS.HierarchyInputR25m.scalar_uniqueness hκ)
    (QuantumNLS.HierarchyInputR25m.scalar_moments hκ)
  exact QuantumNLS.Def033HierarchyR24m.DEF033_intermediate hκ w hw
    (QuantumNLS.HierarchyInputR25m.conclusion_to_r24 w _ hFull)

/-- Same all-order DEF-033 conclusion, now with every printed scalar and Sobolev
antecedent discharged. The only missing-predecessor argument is precisely the
shared full printed hierarchy Input. REG-015 remains an inherited conditional
proof import, as in R-115CAA16; no acceptance is promoted. -/
theorem DEF033_intermediate (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (HierarchyR7B122087Input : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input
      (L := L) hκ) :
    ∃ (Ψ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΨ : ∀ r, IsHamFlow L (hamiltonian L κ r) (Ψ r)),
      (∀ r s, ∀ u : Smooth L, ∀ t τ, Ψ r t (Ψ s τ u.val) = Ψ s τ (Ψ r t u.val)) ∧
      ∀ r (u : Smooth L) n, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
        ∃! freq : ℝ, ActiveFrequency
          (fun t => w (physical ⟨Ψ r t u.val, ((hΨ r u.val u.property).2.2 t).1⟩) n)
          (w (physical u) n) freq := by
  exact DEF033_from_printed_antecedents_intermediate hκ w hw
    (QuantumNLS.Def033SobolevR25m.sobolev_homeomorphisms hκ w hw)
    HierarchyR7B122087Input

end QuantumNLS.Def033BindingR25m
#print QuantumNLS.Def033BindingR25m.DEF033_intermediate
#print axioms QuantumNLS.Def033BindingR25m.DEF033_intermediate
