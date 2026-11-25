import QuantumNLS.LinearTailFinal
/-! integrator-authored trusted spec for R-36C23346 QG:lem:haar-linear-tail (Terra r156 ACCEPT): headline statement(s) copied verbatim from LinearTailFinal. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Filter Topology
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.R36C2Spec
open QuantumNLS.LinearTailFinal
open TensorCarrier PhysicalTensor KernelDefinition ContactOperator
open LinearTailGenerator LinearTailHamiltonian LinearTailPhysicalEvolution
open PhysicalCutoffEvolutionBounds SourceGeneratorBound SourceMarginalEvolution
variable (L : ℝ) [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem R_36C23346_spec (κ : ℝ) (hκ : 0 < κ) :
    (∀ (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ),
      genSum L κ N a t =
        ∑ j : Fin N, (((1 / L) * κ ^ j.val * HighMomentsRank.fallR N (j.val + 1) : ℝ) : ℂ) •
          genericU_N_r N (j.val + 1) j.2 (finiteT L (j.val + 1) a t) ∧
      IsSelfAdjoint (genSum L κ N a t)) ∧
    (∀ (N : ℕ) (hN : 1 ≤ N) (a : Finset ℤ) (t : ℤ → ℝ),
      (∀ (ψ : SymL2 L N) (hψ : ψ ∈ (Hop (L := L) (N := N) (κ / (N : ℝ))
          (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le).domain),
        ∃ h : symGen L κ N a t ψ ∈ (Hop (L := L) (N := N) (κ / (N : ℝ))
            (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le).domain,
          Hop (L := L) (N := N) (κ / (N : ℝ))
              (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le ⟨symGen L κ N a t ψ, h⟩ =
            symGen L κ N a t (Hop (L := L) (N := N) (κ / (N : ℝ))
              (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le ⟨ψ, hψ⟩)) ∧
      (∀ (g : BetheOccupationGauge.Gauge) (j : ℤ),
        Commute (genSum L κ N a t)
          (CartesianOccupationTransfer.physical
            (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) g j j))) ∧
    (∀ (E : ℝ), 0 ≤ E → ∀ k : ℕ,
      ∃ ε : ℕ → ℝ, (∀ R, 0 ≤ ε R) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ (N : ℕ) (hk : k ≤ N), ∃ P : SymL2 L N →L[ℂ] SymL2 L N,
          EnergyCutoff L κ hκ N E P ∧ P * P = P ∧ P.adjoint = P ∧
          ∀ (ψ : SymL2 L N), P ψ = ψ → ‖ψ‖ = 1 →
          ∀ (R : ℕ) (a : Finset ℤ) (t : ℤ → ℝ),
            (∀ m ∈ a, |t m| ≤ 1) → (∀ m ∈ a, (R : ℤ) < |m|) →
          ∀ (s : ℝ), |s| ≤ 1 →
            TraceClass.traceNorm (reducedDensityN N k hk (tensorOrbit L κ N a t s ψ) -
              reducedDensityN N k hk ((BethePhysicalTransfer.symmetricPosition L N).symm ψ).val) ≤
                ENNReal.ofReal (ε R)) := by
  first
  | exact QuantumNLS.LinearTailFinal.«R-36C23346»
  | (apply QuantumNLS.LinearTailFinal.«R-36C23346» <;> assumption)

end QuantumNLS.R36C2Spec
#print axioms QuantumNLS.R36C2Spec.R_36C23346_spec
