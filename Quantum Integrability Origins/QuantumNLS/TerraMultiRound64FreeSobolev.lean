import QuantumNLS.TerraMultiRound64BaseCoefficient

/-! The free even moment is finite exactly at the corresponding Fourier Sobolev order. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Fourier
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
namespace QuantumNLS.TerraMultiRound64FreeSobolev
variable {L : ℝ} [Fact (0 < L)]

theorem free_even_integrable_iff_summable (u : L2T L) (s : ℕ) :
    Integrable (fun t : ℝ => t^(2*s)) (freeMeasure L u) ↔
      Summable (fun n : ℤ => |QuantumNLS.Fourier.freq L n|^(2*s) * ‖fourierL2 L u n‖^2) := by
  change Integrable (fun t : ℝ => t^(2*s)) (Measure.sum (fun n : ℤ =>
    ENNReal.ofReal (‖coeff L (u : AddCircle L → ℂ) n‖^2) •
      Measure.dirac (2 * Real.pi * n / L))) ↔ _
  rw [integrable_sum_dirac_iff (fun n => by simp)]
  apply summable_congr
  intro n
  rw [ENNReal.toReal_ofReal (sq_nonneg _), Real.norm_eq_abs, abs_pow,
    ← QuantumNLS.Fourier.fourierL2_apply]
  simp only [QuantumNLS.Fourier.freq]
  ring

theorem free_even_integrable_iff_hsq (u : L2T L) (s : ℕ) :
    Integrable (fun t : ℝ => t^(2*s)) (freeMeasure L u) ↔
      hsq L (s : ℝ) (fun n => coeff L (u : AddCircle L → ℂ) n) ≠ ⊤ := by
  rw [free_even_integrable_iff_summable]
  let c : ℤ → ℂ := fun n => coeff L (u : AddCircle L → ℂ) n
  let p : ℤ → ℝ := fun n => |QuantumNLS.Fourier.freq L n|
  have hcast : (2 : ℝ) * (s : ℝ) = ((2*s : ℕ) : ℝ) := by push_cast; ring
  have hw (n : ℤ) : wt L (s : ℝ) n = (1 + p n)^(2*s) := by
    unfold wt p QuantumNLS.RiccatiSobolevE1.freq QuantumNLS.Fourier.freq
    rw [hcast, Real.rpow_natCast]
  have hcoeff : Summable (fun n : ℤ => ‖c n‖^2) := by
    simpa only [c, ← fourierL2_apply] using QuantumNLS.Energy.summable_sq (fourierL2 L u)
  constructor
  · intro hm
    have hm' : Summable (fun n : ℤ => p n^(2*s) * ‖c n‖^2) := by
      simpa only [p, c, ← fourierL2_apply] using hm
    have hmajor : Summable (fun n : ℤ => (2 : ℝ)^(2*s-1) *
        (‖c n‖^2 + p n^(2*s) * ‖c n‖^2)) := (hcoeff.add hm').mul_left _
    have hs : Summable (fun n : ℤ => wt L (s : ℝ) n * ‖c n‖^2) := by
      apply Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_nonneg L (s : ℝ) n) (sq_nonneg _)) _ hmajor
      intro n
      rw [hw]
      have hb := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg (QuantumNLS.Fourier.freq L n)) (2*s)
      dsimp only [p]
      simp only [one_pow] at hb
      calc
        _ ≤ ((2 : ℝ)^(2*s-1) * (1 + |QuantumNLS.Fourier.freq L n|^(2*s))) * ‖c n‖^2 :=
          mul_le_mul_of_nonneg_right hb (sq_nonneg _)
        _ = _ := by ring
    exact hs.tsum_ofReal_ne_top
  · intro h
    have hs := (hsq_summable_eq h).1
    have hm : Summable (fun n : ℤ => p n^(2*s) * ‖c n‖^2) := by
      apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
      intro n
      rw [hw]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (by dsimp [p]; linarith) _) (sq_nonneg _)
    simpa only [p, c, ← fourierL2_apply] using hm

#print axioms free_even_integrable_iff_summable
#print axioms free_even_integrable_iff_hsq
end QuantumNLS.TerraMultiRound64FreeSobolev
