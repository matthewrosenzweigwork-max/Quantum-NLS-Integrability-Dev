import QuantumNLS.Prop024TransferR133
import QuantumNLS.Prop024WickTransportR133
import QuantumNLS.Prop024CanonicalWeylR133

/-! Q7B:lem:remainder on the original separable Hilbert space. All
operators in the statement are intrinsic to that space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop024GeneralR133
open PhysicalTensor Prop022GTensor Prop022GClassical Prop022GHilbert Prop022BExist Prop022BFock2
open Prop021ManyBodyTransportR132 Prop021MomentsR132
open Prop024CanonicalWeylR133 Prop024WickTransportR133
open Prop024FinalH1

/-- All source data and both inequalities of Q7B:eq:mgf, with the
printed bound and explicit constant of the remainder proof. -/
def PrintedRemainder : Prop :=
  ∀ (A : ℝ), 0 < A →
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
  ∀ (K : Kernels H) (M : ℝ), 1 ≤ M → KBound K M A → KSelfAdj K →
  ∀ (N : ℕ) (Q : ℝ), 1 ≤ Q → 256 * Real.exp 1 * A * Q ≤ N →
  ∀ (u : H), ‖u‖ = 1 → ∀ (x : FockSpace H), NumberMoments Q x →
    let W := weyl ((Real.sqrt N : ℂ) • u)
    ∃ (hd : HamiltonianDomain K N (W x)) (R : FockSpace H),
      W.symm (hamiltonian K N (W x) hd) = lowOrders K N u x + R ∧
      ‖R‖ ≤ printedConstant A * M * (N : ℝ) ^ (-(1/2 : ℝ)) * Q ^ (3/2 : ℝ)

/-- Full printed scope, with an arbitrary isometric realization used only
in the proof. The operator domain is the maximal Hilbert direct sum. -/
theorem printed_remainder : PrintedRemainder := by
  intro A hA H _ _ _ _ K M hM hK hs N Q hQ hNQ u hu x hx
  let _ : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨J⟩ : Nonempty (H →ₗᵢ[ℂ] L2T 1) := by
    by_cases hH : FiniteDimensional ℂ H
    · exact exists_isometry_fin hH 1
    · obtain ⟨U⟩ := exists_unitary_L2T 1 hH
      exact ⟨U.toLinearIsometry⟩
  have hN : 0 < N := by
    have hp : (0 : ℝ) < 256 * Real.exp 1 * A * Q :=
      mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) hA) (zero_lt_one.trans_le hQ)
    exact_mod_cast hp.trans_le hNQ
  obtain ⟨hd,R,hact,hbound⟩ := Prop024TransferR133.transfer J A hA K M hM hK hs N Q hQ hNQ u hu x hx
  rw [lowOrders_eq_compression J K N hN u hu x Q M A (zero_le_one.trans hM) hA hQ hK hs hx] at hact
  dsimp only
  rw [weyl_eq_compressed J]
  refine ⟨hd,R,?_,hbound⟩
  let W := WJ J ((Real.sqrt N : ℂ) • u)
  exact (congrArg W.symm hact).trans (W.symm_apply_apply _)

end QuantumNLS.Prop024GeneralR133
