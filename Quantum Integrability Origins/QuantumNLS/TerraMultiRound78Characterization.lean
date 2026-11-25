import QuantumNLS.TerraMultiRound78UpperBootstrap
import QuantumNLS.TerraMultiRound77ActionCriteria
import QuantumNLS.TerraMultiRound64AllMoments

/-! Full interval REG-010 finiteness characterization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RiccatiSobolevE1
open QuantumNLS.TerraMultiRound64BaseCriterion QuantumNLS.TerraMultiRound64AllMoments
open QuantumNLS.TerraMultiRound78UpperBootstrap QuantumNLS.TerraMultiRound77ActionCriteria
open QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound78Characterization

variable {L : ℝ} [Fact (0 < L)]

theorem integer_characterization (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun x : ℝ => |x| ^ (2*(n:ℝ))) (PhysicalQuantumMeasure.measure hκ u) ↔
      ∃ v : H02 L (n:ℝ), v.val = u := by
  have he : (fun x : ℝ => |x| ^ (2*(n:ℝ))) = (fun x : ℝ => x^(2*n)) := by
    funext x
    have hc : 2 * (n:ℝ) = ((2*n:ℕ):ℝ) := by push_cast; ring
    rw [hc, Real.rpow_natCast, ← abs_pow,
      abs_of_nonneg ((even_two_mul n).pow_nonneg x)]
  rw [he]
  have hp : Integrable (fun x : ℝ => x^(2*n)) (PhysicalQuantumMeasure.measure hκ u) ↔
      hsq L (n:ℝ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ := by
    by_cases h1 : n = 1
    · subst n
      simpa only [Nat.mul_one] using physical_second_iff_hsq L κ hκ u
    · exact (integer_moment_induction L κ hκ n (by omega)).1 u
  have hpos : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact hp.trans ((QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_hsq u n hpos).symm.trans
    (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_H02 u n hpos))

theorem full_interval_characterization (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs0 : 0 < s) (hs2 : s ≤ 2) :
    (Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      ∃ v : H02 L s, v.val = u) ∧
    (Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) := by
  refine ⟨?_, physical_power_iff_indexed_actions hκ u s hs0⟩
  by_cases hlow : s < 1
  · exact QuantumNLS.Reg010LowFinal.low_characterization κ hκ u s hs0 hlow
  · by_cases hone : s = 1
    · subst s
      have h := integer_characterization κ hκ u 1 (by omega)
      rw [show ((1:ℕ):ℝ) = (1:ℝ) by norm_num] at h
      exact h
    · by_cases htwo : s = 2
      · subst s
        have h := integer_characterization κ hκ u 2 (by omega)
        rw [show ((2:ℕ):ℝ) = (2:ℝ) by norm_num] at h
        exact h
      · exact upper_characterization κ hκ u s
          (lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hone)) (lt_of_le_of_ne hs2 htwo)

#print axioms integer_characterization
#print axioms full_interval_characterization
end QuantumNLS.TerraMultiRound78Characterization
