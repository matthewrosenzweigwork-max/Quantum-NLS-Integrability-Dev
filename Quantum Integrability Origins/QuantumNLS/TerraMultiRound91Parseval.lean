import QuantumNLS.TerraMultiRound91ShiftBasis
import QuantumNLS.ExactShiftResidual

/-! Parseval for the contact-form Hilbert core. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm
open QuantumNLS.TerraMultiRound90Shifted QuantumNLS.TerraMultiRound91NormalizedCore
open QuantumNLS.TerraMultiRound91ShiftBasis
namespace QuantumNLS.TerraMultiRound91Parseval
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

theorem shifted_coeff_norm_sq {ι : Type*} (hc : 0 ≤ c)
    (b : HilbertBasis ι ℂ (SymL2 L N)) (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (y : ι → VSym L N) (hy : ∀ i, valSym (y i) = b i)
    (hpair : ∀ i (z : VSym L N), q c z.1 (y i).1 = (ev i : ℂ) * ⟪valSym z, b i⟫_ℂ)
    (a : HilbertBasis ι ℂ (VSym L N)) (ha : ∀ i, a i = normalizedCore hc ev y i)
    (z : VSym L N) (i : ι) :
    ‖a.repr (shiftRoot hc z) i‖ ^ 2 = (ev i + 1) * ‖b.repr (valSym z) i‖ ^ 2 := by
  have hp : 0 < ev i + 1 := by linarith [hev i]
  have hs : Real.sqrt (ev i + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hpair' : ⟪shiftRoot hc (y i), shiftRoot hc z⟫_ℂ =
      ((ev i + 1 : ℝ) : ℂ) * ⟪b i, valSym z⟫_ℂ := by
    rw [← inner_conj_symm, shifted_pairing hc (y i) z (b i) (ev i) (hy i) (hpair i)]
    rw [map_mul, Complex.conj_ofReal]
    exact congrArg (fun w : ℂ => ((ev i + 1 : ℝ) : ℂ) * w)
      (inner_conj_symm (𝕜 := ℂ) (b i) (valSym z))
  rw [HilbertBasis.repr_apply_apply, ha, normalizedCore, inner_smul_left, Complex.conj_ofReal, hpair',
    HilbertBasis.repr_apply_apply]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.le,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow]
  rw [← Real.sq_sqrt hp.le]
  field_simp
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Weighted Parseval for any form vector, with no operator-domain hypothesis. -/
theorem shifted_parseval {ι : Type*} (hc : 0 ≤ c)
    (b : HilbertBasis ι ℂ (SymL2 L N)) (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (y : ι → VSym L N) (hy : ∀ i, valSym (y i) = b i)
    (hpair : ∀ i (z : VSym L N), q c z.1 (y i).1 = (ev i : ℂ) * ⟪valSym z, b i⟫_ℂ)
    (hdense : Dense ((Submodule.span ℂ (Set.range y) : Submodule ℂ (VSym L N)) : Set (VSym L N)))
    (z : VSym L N) :
    Summable (fun i => (ev i + 1) * ‖b.repr (valSym z) i‖ ^ 2) ∧
    (Bform c z z).re = ∑' i, (ev i + 1) * ‖b.repr (valSym z) i‖ ^ 2 := by
  obtain ⟨a, ha⟩ := normalized_core_basis hc b ev hev y hy hpair hdense
  have heq (i : ι) := shifted_coeff_norm_sq hc b ev hev y hy hpair a ha z i
  constructor
  · simpa only [← heq] using ExactShiftResidual.summable_norm_sq (a.repr (shiftRoot hc z))
  · calc
      (Bform c z z).re = ‖shiftRoot hc z‖ ^ 2 := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_shiftRoot]
        rfl
      _ = ‖a.repr (shiftRoot hc z)‖ ^ 2 := (a.repr.norm_map _).symm ▸ rfl
      _ = ∑' i, ‖a.repr (shiftRoot hc z) i‖ ^ 2 := ExactShiftResidual.norm_sq_tsum _
      _ = ∑' i, (ev i + 1) * ‖b.repr (valSym z) i‖ ^ 2 := tsum_congr heq

#print axioms shifted_coeff_norm_sq
#print axioms shifted_parseval
end QuantumNLS.TerraMultiRound91Parseval
