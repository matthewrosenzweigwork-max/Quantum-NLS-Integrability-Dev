import QuantumNLS.Reg014Moments

/-! REG-014 support: the two terms of `D_{r,u}(Y)` are finite for every `u ∈ H^{r-1}` and
`Y > 0` (the printed remark preceding the lemma), so that the Bochner integral and the
`tsum` in the statement are genuine, not junk values. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace QuantumNLS.Reg014Finite
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61MomentRecurrence
open QuantumNLS.TerraMultiRound64FieldIdentity QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.Reg014Moments

variable {L : ℝ} [Fact (0 < L)]

theorem terms_finite (κ : ℝ) (hκ : 0 < κ) (r : ℕ) (hr : 2 ≤ r) (u : Hk L (r - 1)) {Y : ℝ}
    (hY : 0 < Y) :
    Integrable (fun t : ℝ => Y ^ 2 * t ^ (2 * r) / (Y ^ 2 + t ^ 2))
        (PhysicalQuantumMeasure.measure hκ u.val) ∧
      Summable (fun n : ℤ => Y ^ 2 * (momentum L n) ^ (2 * r) /
        (Y ^ 2 + (momentum L n) ^ 2) * ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hu := representative_hsq (L := L) (n + 1 - 1) u
  simp only [Nat.add_sub_cancel] at hu
  have hμn := physical_moment_integrable κ hκ n hn u.val hu
  refine ⟨kernel_integrable_succ _ n Y hY hμn, ?_⟩
  have hνn : Integrable (fun t : ℝ => t ^ (2 * n)) (freeMeasure L u.val) :=
    (free_even_integrable_iff_hsq u.val n).mpr hu
  have : IsFiniteMeasure (freeMeasure L u.val) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  have hi := kernel_integrable_succ (freeMeasure L u.val) n Y hY hνn
  change Integrable (kernel (n + 1) Y) (Measure.sum (fun m : ℤ =>
    ENNReal.ofReal (‖QuantumNLS.Fourier.coeff L (u.val : AddCircle L → ℂ) m‖ ^ 2) •
      Measure.dirac (2 * Real.pi * m / L))) at hi
  refine (hasSum_integral_measure hi).summable.congr (fun m => ?_)
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  simp only [kernel]
  unfold momentum
  ring

#print axioms terms_finite
end QuantumNLS.Reg014Finite
