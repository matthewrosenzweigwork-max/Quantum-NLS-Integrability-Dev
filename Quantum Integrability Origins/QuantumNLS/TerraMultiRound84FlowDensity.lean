import QuantumNLS.L2Flow

/-! The finite-Fourier density and continuity step for the accepted L² flow.
The conditional extension lemma is not a proof of the finite-profile identity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
open Filter QuantumNLS.Fourier QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.L2Flow
namespace QuantumNLS.TerraMultiRound84FlowDensity
variable {L : ℝ} [Fact (0 < L)]

/-- Finite linear combinations of periodic Fourier modes. -/
def finiteModes : Submodule ℂ (HL L) := Submodule.span ℂ (Set.range (modeLp L))

/-- Finite Fourier profiles are dense in the physical L² space. -/
theorem dense_finiteModes : Dense (finiteModes (L := L) : Set (HL L)) := by
  intro u
  apply mem_closure_of_tendsto (hasSum_coeff_smul_modeLp L u)
  exact Filter.Eventually.of_forall (fun F => by
    apply Submodule.sum_mem
    intro n hn
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩))

/-- Once an identity has been proved on finite Fourier profiles, continuity
of the actual Duhamel flow and of the two transformations extends it to L².
The finite-profile identity is an explicit premise of this support lemma. -/
theorem extend_from_finiteModes {κ κ' : ℝ} (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (A B : HL L → HL L) (hA : Continuous A) (hB : Continuous B) (t : ℝ)
    (hfinite : ∀ u ∈ finiteModes (L := L),
      flowMap hκ (A u) t = B (flowMap hκ' u t)) :
    ∀ u : HL L, flowMap hκ (A u) t = B (flowMap hκ' u t) := by
  have hleft : Continuous (fun u : HL L => flowMap hκ (A u) t) :=
    (continuous_flowMap hκ t).comp hA
  have hright : Continuous (fun u : HL L => B (flowMap hκ' u t)) :=
    hB.comp (continuous_flowMap hκ' t)
  have heq := Continuous.ext_on dense_finiteModes hleft hright hfinite
  exact fun u => congrFun heq u

#print axioms dense_finiteModes
#print axioms extend_from_finiteModes
end QuantumNLS.TerraMultiRound84FlowDensity
