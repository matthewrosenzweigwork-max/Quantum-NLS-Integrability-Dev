import QuantumNLS.ExactShiftResidual
/-! integrator-authored trusted spec for R-284267AA lem:full-affinity-identities (shift_affinity.tex:26–63): the frozen statements of ExactShiftResidual restated verbatim
(Terra r131 ACCEPT). -/
namespace ExactShiftResidualSpec
open scoped InnerProductSpace ComplexConjugate ENNReal
open QuantumNLS.Occupation QuantumNLS.OccupationHilbert QuantumNLS.FullOccupationAffinity
open QuantumNLS QuantumNLS.ExactShiftResidual

theorem residual_identity_spec {N : ℕ} (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase)
    (g : UnitCoefficients N) :
    ‖transfer a b α g.1 - ζ.1 • g.1‖ ^ 2 =
      2 - missing a g.1 - 2 * affinity a b g.1 + 2 * defect a b α ζ g.1  := by
  apply QuantumNLS.ExactShiftResidual.residual_identity <;> assumption

theorem adjoint_residual_identity_spec {N : ℕ} (a b : ℤ) (hab : a ≠ b)
    (α : Donor N a → Phase) (ζ : Phase) (g : UnitCoefficients N) :
    ‖(transfer a b α).adjoint g.1 - conj ζ.1 • g.1‖ ^ 2 =
      2 - missing b g.1 - 2 * affinity a b g.1 + 2 * defect a b α ζ g.1  := by
  apply QuantumNLS.ExactShiftResidual.adjoint_residual_identity <;> assumption

theorem empty_transfer_spec {N : ℕ} (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase) (g : H N) :
    emptyCoefficients b (transfer a b α g) = 0  := by
  apply QuantumNLS.ExactShiftResidual.empty_transfer <;> assumption

theorem empty_adjoint_spec {N : ℕ} (a b : ℤ) (α : Donor N a → Phase) (g : H N) :
    emptyCoefficients a ((transfer a b α).adjoint g) = 0  := by
  apply QuantumNLS.ExactShiftResidual.empty_adjoint <;> assumption

theorem missing_receiver_le_spec {N : ℕ} (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase)
    (ζ : Phase) (g : H N) :
    missing b g ≤ ‖transfer a b α g - ζ.1 • g‖ ^ 2  := by
  apply QuantumNLS.ExactShiftResidual.missing_receiver_le <;> assumption

theorem missing_donor_le_spec {N : ℕ} (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N) :
    missing a g ≤ ‖(transfer a b α).adjoint g - conj ζ.1 • g‖ ^ 2  := by
  apply QuantumNLS.ExactShiftResidual.missing_donor_le <;> assumption

theorem affinity_defect_bounds_spec {N : ℕ} (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase)
    (g : UnitCoefficients N) :
    (0 ≤ 1 - affinity a b g.1 ∧
      1 - affinity a b g.1 ≤ (missing a g.1 + ‖transfer a b α g.1 - ζ.1 • g.1‖ ^ 2) / 2) ∧
    (0 ≤ defect a b α ζ g.1 ∧
      defect a b α ζ g.1 ≤ (missing a g.1 + ‖transfer a b α g.1 - ζ.1 • g.1‖ ^ 2) / 2)  := by
  apply QuantumNLS.ExactShiftResidual.affinity_defect_bounds <;> assumption

theorem all_errors_le_spec {N : ℕ} (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase) (ζ : Phase)
    (g : UnitCoefficients N) (ε : ℝ)
    (hε : ‖transfer a b α g.1 - ζ.1 • g.1‖ ^ 2 +
      ‖(transfer a b α).adjoint g.1 - conj ζ.1 • g.1‖ ^ 2 ≤ ε) :
    missing a g.1 ≤ ε ∧ missing b g.1 ≤ ε ∧
      |affinity a b g.1 - 1| ≤ ε / 2 ∧ |defect a b α ζ g.1| ≤ ε / 2  := by
  apply QuantumNLS.ExactShiftResidual.all_errors_le <;> assumption

theorem residual_limits_spec {N : ℕ} {I : Type*} (l : Filter I) (n : I → ℕ)
    (a b : ℤ) (hab : a ≠ b) (α : ∀ i, Donor (n i) a → Phase)
    (ζ : I → Phase) (g : ∀ i, UnitCoefficients (n i))
    (hW : Filter.Tendsto (fun i => ‖transfer a b (α i) (g i).1 - (ζ i).1 • (g i).1‖) l (nhds 0))
    (hA : Filter.Tendsto (fun i => ‖(transfer a b (α i)).adjoint (g i).1 -
      conj (ζ i).1 • (g i).1‖) l (nhds 0)) :
    Filter.Tendsto (fun i => missing a (g i).1) l (nhds 0) ∧
    Filter.Tendsto (fun i => missing b (g i).1) l (nhds 0) ∧
    Filter.Tendsto (fun i => affinity a b (g i).1) l (nhds 1) ∧
    Filter.Tendsto (fun i => defect a b (α i) (ζ i) (g i).1) l (nhds 0)  := by
  apply QuantumNLS.ExactShiftResidual.residual_limits <;> assumption

theorem uniform_errors_spec {N : ℕ} {I : Type*} (S : Set I) (n : I → ℕ)
    (a b : ℤ) (hab : a ≠ b) (α : ∀ i, Donor (n i) a → Phase)
    (ζ : I → Phase) (g : ∀ i, UnitCoefficients (n i)) (ε : ℝ)
    (h : ∀ i ∈ S, ‖transfer a b (α i) (g i).1 - (ζ i).1 • (g i).1‖ ^ 2 +
      ‖(transfer a b (α i)).adjoint (g i).1 - conj (ζ i).1 • (g i).1‖ ^ 2 ≤ ε) :
    ∀ i ∈ S, missing a (g i).1 ≤ ε ∧ missing b (g i).1 ≤ ε ∧
      |affinity a b (g i).1 - 1| ≤ ε / 2 ∧ |defect a b (α i) (ζ i) (g i).1| ≤ ε / 2  := by
  apply QuantumNLS.ExactShiftResidual.uniform_errors <;> assumption

theorem unitPhase_identity_spec {N : ℕ} (a b : ℤ) (ζ : Phase) (g : UnitCoefficients N) :
    ‖UnitPhaseTransfer.auxiliary N a b g.1 - ζ.1 • g.1‖ ^ 2 =
      2 - missing a g.1 - 2 * affinity a b g.1 +
        2 * defect a b (fun _ => ⟨1, norm_one⟩) ζ g.1  := by
  apply QuantumNLS.ExactShiftResidual.unitPhase_identity <;> assumption

theorem unitPhase_adjoint_identity_spec {N : ℕ} (a b : ℤ) (hab : a ≠ b) (ζ : Phase) (g : UnitCoefficients N) :
    ‖(UnitPhaseTransfer.auxiliary N a b).adjoint g.1 - conj ζ.1 • g.1‖ ^ 2 =
      2 - missing b g.1 - 2 * affinity a b g.1 +
        2 * defect a b (fun _ => ⟨1, norm_one⟩) ζ g.1  := by
  apply QuantumNLS.ExactShiftResidual.unitPhase_adjoint_identity <;> assumption

end ExactShiftResidualSpec
#print axioms ExactShiftResidualSpec.residual_identity_spec
#print axioms ExactShiftResidualSpec.adjoint_residual_identity_spec
#print axioms ExactShiftResidualSpec.empty_transfer_spec
#print axioms ExactShiftResidualSpec.empty_adjoint_spec
#print axioms ExactShiftResidualSpec.missing_receiver_le_spec
#print axioms ExactShiftResidualSpec.missing_donor_le_spec
#print axioms ExactShiftResidualSpec.affinity_defect_bounds_spec
#print axioms ExactShiftResidualSpec.all_errors_le_spec
#print axioms ExactShiftResidualSpec.residual_limits_spec
#print axioms ExactShiftResidualSpec.uniform_errors_spec
#print axioms ExactShiftResidualSpec.unitPhase_identity_spec
#print axioms ExactShiftResidualSpec.unitPhase_adjoint_identity_spec
