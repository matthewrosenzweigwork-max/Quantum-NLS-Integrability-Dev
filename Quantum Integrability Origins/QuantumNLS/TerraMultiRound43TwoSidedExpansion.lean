import QuantumNLS.TerraMultiRound42SmoothPositive
import QuantumNLS.TerraMultiRound43NegativeExpansion

/-! The two smooth expansions use the same field representative and the
unique signed exact-ball branch. The independent L∞ identification is open. -/
set_option autoImplicit false
noncomputable section
open Complex Finset
namespace QuantumNLS.TerraMultiRound43TwoSidedExpansion
open QuantumNLS.ClassicalCharges QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiODEConverse QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound41Coefficients QuantumNLS.TerraMultiRound42SmoothPositive
open QuantumNLS.TerraMultiRound43NegativeExpansion

/-- One Fourier representative carries the unique signed fixed-point branch;
its positive and negative expansions have the literal printed coefficients
and all-order remainders. -/
theorem smooth_two_sided_expansion (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (κ : ℝ) (f : ℝ → ℂ) (hf : SmoothPeriodic L f) :
    ∃ x : Ell2, physRep L a x = f ∧
      (∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ |Y| →
        ∃ (hY : 0 < |Y|) (r : Ell2), ‖r‖ ≤ 2 * ‖x‖ / |Y| ∧
          physicalT hLf.out ha hY κ x r = r ∧
          ∀ r' : Ell2, ‖r'‖ ≤ 2 * ‖x‖ / |Y| →
            physicalT hLf.out ha hY κ x r' = r' → r' = r) ∧
      (∀ M : ℕ, 1 ≤ M → ∃ B C : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y →
        ∃ (hY : 0 < Y) (r p : Ell2), ‖r‖ ≤ 2 * ‖x‖ / Y ∧
          physicalT hLf.out ha (abs_pos.mpr hY.ne') κ x r = r ∧
          (∀ t : ℝ, physRep L a p t =
            ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * ((Y : ℂ)⁻¹) ^ n) ∧
          ‖r - p‖ ≤ C * (Y ^ (M + 1))⁻¹) ∧
      (∀ M : ℕ, 1 ≤ M → ∃ B C : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y →
        ∃ (hY : 0 < Y) (r p : Ell2), ‖r‖ ≤ 2 * ‖x‖ / Y ∧
          physicalT hLf.out ha (by simpa using (abs_pos.mpr hY.ne') : 0 < |-Y|) κ x r = r ∧
          (∀ t : ℝ, physRep L a p t =
            ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * (((-Y : ℝ) : ℂ)⁻¹) ^ n) ∧
          ‖r - p‖ ≤ C * (Y ^ (M + 1))⁻¹) := by
  obtain ⟨x, hx, hp⟩ := smooth_positive_expansion L ha κ f hf
  obtain ⟨y, hy, hn⟩ := smooth_negative_expansion L ha κ f hf
  have he : y = x := physRep_injective hLf.out ha (hy.trans hx.symm)
  subst y
  exact ⟨x, hx, physical_fixed_eventually hLf.out ha κ x, hp, hn⟩

#print axioms smooth_two_sided_expansion
end QuantumNLS.TerraMultiRound43TwoSidedExpansion
