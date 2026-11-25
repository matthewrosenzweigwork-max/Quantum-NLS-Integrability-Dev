import NlsGge.Analysis.ComplexHilbertSchmidtFiniteBasis
import Mathlib.Analysis.Normed.Operator.NormedSpace
import NlsGge.Schur.FreeResolventRealRpowTwoIdentity

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProduct lp

namespace NlsGge.Schur
open NlsGge.Pilot

/-- Real image norms of a square-summable family form a complex ℓ² sequence. -/
theorem complex_real_norm_sequence_memLp_two
    {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    (T : ι → E) (hs : Summable (fun i => ‖T i‖ ^ 2)) :
    Memℓp (fun i => (‖T i‖ : ℂ)) (2 : ℝ≥0∞) := by
  apply (memℓp_gen_iff (p := (2 : ℝ≥0∞))
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  convert hs using 1
  ext i
  simp [Complex.norm_real]

/-- Exact norm-square identity for the pinned complex `ℓ²` space. -/
theorem complex_lp_two_norm_sq_eq_tsum
    {ι : Type*} (f : ℓ²(ι, ℂ)) :
    ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have hraw := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f
  have hreal : ‖f‖ ^ (2 : ℝ) = ∑' i, ‖f i‖ ^ (2 : ℝ) := by
    simpa only [ENNReal.toReal_ofNat] using hraw
  calc
    ‖f‖ ^ 2 = ‖f‖ ^ (2 : ℝ) := (real_rpow_two_eq_pow ‖f‖).symm
    _ = ∑' i, ‖f i‖ ^ (2 : ℝ) := hreal
    _ = ∑' i, ‖f i‖ ^ 2 := tsum_congr fun i => real_rpow_two_eq_pow ‖f i‖

/-- Pinned Cauchy--Schwarz for pointwise products of two complex `ℓ²`
sequences, with the actual ENNReal-to-real Holder indices made explicit. -/
theorem complex_lp_two_tsum_mul_le
    {ι : Type*} (f g : ℓ²(ι, ℂ)) :
    Summable (fun i => ‖f i‖ * ‖g i‖) ∧
      (∑' i, ‖f i‖ * ‖g i‖) ≤ ‖f‖ * ‖g‖ := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  exact lp.tsum_mul_le_mul_norm hpq f g

end NlsGge.Schur
