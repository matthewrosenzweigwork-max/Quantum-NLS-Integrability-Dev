import QuantumNLS.Prop024GeneralR133
import QuantumNLS.Prop022CMain

/-! The shifted Hamiltonian on Fock(H), with the Weyl exponential
characterized by the closure of its finite-particle generator. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop024GeneralR134
open PhysicalTensor Prop022GTensor Prop022GClassical Prop022BExist Prop022GHilbert
open Prop022CWeyl Prop021ManyBodyTransportR132 Prop021MomentsR132
open Prop024CanonicalWeylR133 Prop024WickTransportR133 Prop024FinalH1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Every separable carrier admits a proof of the intrinsic Weyl convention
for the canonical coherent-vector displacement. -/
theorem weyl_isWeylOp (v : H) : IsWeylOp v (weyl v) := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨J⟩ : Nonempty (H →ₗᵢ[ℂ] L2T 1) := by
    by_cases hH : FiniteDimensional ℂ H
    · exact exists_isometry_fin hH 1
    · obtain ⟨U⟩ := exists_unitary_L2T 1 hH
      exact ⟨U.toLinearIsometry⟩
  rw [weyl_eq_compressed J]
  exact WJ_isWeylOp J v

/-- Q7B:lem:remainder with the Weyl exponential on the original Fock
space. The maximal Hamiltonian domain, both number-moment estimates,
threshold, and Hilbert-norm remainder have the printed conventions. -/
def PrintedRemainder : Prop :=
  ∀ (A : ℝ), 0 < A →
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
  ∀ (K : Kernels H) (M : ℝ), 1 ≤ M → KBound K M A → KSelfAdj K →
  ∀ (N : ℕ) (Q : ℝ), 1 ≤ Q → 256 * Real.exp 1 * A * Q ≤ N →
  ∀ (u : H), ‖u‖ = 1 → ∀ (x : FockSpace H), NumberMoments Q x →
  ∃ W : FockSpace H ≃ₗᵢ[ℂ] FockSpace H, IsWeylOp ((Real.sqrt N : ℂ) • u) W ∧
    ∀ W' : FockSpace H ≃ₗᵢ[ℂ] FockSpace H, IsWeylOp ((Real.sqrt N : ℂ) • u) W' →
    ∃ (hd : HamiltonianDomain K N (W' x)) (R : FockSpace H),
      W'.symm (hamiltonian K N (W' x) hd) = lowOrders K N u x + R ∧
      ‖R‖ ≤ printedConstant A * M * (N : ℝ) ^ (-(1/2 : ℝ)) * Q ^ (3/2 : ℝ)

theorem printed_remainder : PrintedRemainder := by
  intro A hA H _ _ _ _ K M hM hK hs N Q hQ hNQ u hu x hx
  let v := (Real.sqrt N : ℂ) • u
  refine ⟨weyl v, weyl_isWeylOp v, fun W hW => ?_⟩
  rw [weylOp_unique hW (weyl_isWeylOp v)]
  exact Prop024GeneralR133.printed_remainder A hA H K M hM hK hs N Q hQ hNQ u hu x hx

end QuantumNLS.Prop024GeneralR134

#print axioms QuantumNLS.Prop024GeneralR134.weyl_isWeylOp
#print axioms QuantumNLS.Prop024GeneralR134.printed_remainder
