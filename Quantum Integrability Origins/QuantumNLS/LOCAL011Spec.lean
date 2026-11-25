import QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011
/-! integrator-authored trusted spec for LOCAL-011 (quantum_periods.tex:15-100; Terra r148 ACCEPT):
source-ordered clauses copied verbatim from PlacementFiberPrefixProductExpansionLOCAL011 f726ae8f:
chosen product expansion with representation and radius bound for arbitrary kernel lists, fixed-degree
overlap product identity and bound, N-uniform commutator bound, represented commutator identity and the
commutator radius loss 2/(R-r). DEF-050 radius bound and represented operator (rfl) below. -/
set_option maxHeartbeats 5000000
open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberGrouping
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound42
  QuantumNLS.PlacementFiberPrefixAlignedTransport
  QuantumNLS.PlacementFiberBound QuantumNLS.PlacementGrouping
  QuantumNLS.RadiusBound QuantumNLS.LocalPlacement


noncomputable section
namespace LOCAL011Spec
open QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem local011_spec {N : ℕ} {r R : ℝ}
    (hr : 1 ≤ r) (hR : r < R) (A B : KernelList (H := H) N) :
    (∃ C : ChosenExpansion (H := H) N,
      C.operator = (represented A).comp (represented B) ∧
      QuantumNLS.LocalPlacement.radiusBound C R ≤
        QuantumNLS.RadiusBound.radiusBound R A *
          QuantumNLS.RadiusBound.radiusBound R B) ∧
    (∀ (n p q : ℕ) (hp : p ≤ n) (hq : q ≤ n)
      (K : BoundedSymmetricKernel H p) (L : BoundedSymmetricKernel H q),
      (genericU_N_r n p hp K).comp (genericU_N_r n q hq L) =
        ∑ s : FeasibleOverlapIndex n p q,
          (((overlapCoefficient n p q s.1.1 : ℝ) : ℂ) •
            genericU_N_r n (unionSize p q s.1.1) s.2
              (averagedOverlapKernel
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) K L))) ∧
    (∀ {n p q : ℕ} {ρ : ℝ} (hp : p ≤ n) (hq : q ≤ n) (_hρ : 1 ≤ ρ)
      (K : BoundedSymmetricKernel H p) (L : BoundedSymmetricKernel H q),
      ‖(genericU_N_r n p hp K).comp (genericU_N_r n q hq L)‖ ≤
        (ρ ^ p * ‖K‖) * (ρ ^ q * ‖L‖)) ∧
    (∀ (n p q : ℕ) (hp : p ≤ n) (hq : q ≤ n)
      (K : BoundedSymmetricKernel H p) (L : BoundedSymmetricKernel H q),
      (n : ℝ) *
          ‖(genericU_N_r n p hp K).comp (genericU_N_r n q hq L) -
            (genericU_N_r n q hq L).comp (genericU_N_r n p hp K)‖ ≤
        2 * (p * q : ℝ) * ‖K‖ * ‖L‖) ∧
    represented (positiveOverlapCommutatorList N A B) =
      ((Complex.I : ℂ) * (N : ℂ)) •
        ((represented A).comp (represented B) -
          (represented B).comp (represented A)) ∧
    QuantumNLS.RadiusBound.radiusBound r (positiveOverlapCommutatorList N A B) ≤
      (2 / (R - r)) *
        (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
        QuantumNLS.RadiusBound.radiusBound R B :=
  QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011.local011_full_source_ordered_clauses hr hR A B

theorem radiusBound_def {N : ℕ} (R : ℝ) (A : KernelList (H := H) N) :
    QuantumNLS.RadiusBound.radiusBound R A = ∑ p : Fin (N + 1), R ^ p.1 * ‖A p‖ := rfl
theorem local_radiusBound_def {N : ℕ} (A : ChosenExpansion (H := H) N) (R : ℝ) :
    QuantumNLS.LocalPlacement.radiusBound A R = Finset.univ.sum (fun p : Fin (N + 1) => R ^ p.1 * ‖A.kernels p‖) := rfl
theorem represented_def {N : ℕ} (A : KernelList (H := H) N) :
    QuantumNLS.RadiusBound.represented A = ∑ p : Fin (N + 1), Q N p.1 (Nat.lt_succ_iff.mp p.2) (A p) := rfl
end LOCAL011Spec
#print axioms LOCAL011Spec.local011_spec
