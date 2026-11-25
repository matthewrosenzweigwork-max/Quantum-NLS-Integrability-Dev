import QuantumNLS.TerraMultiRound91ShiftedCore

/-! Normalize the shifted eigenvector core by the positive square root of
1 + energy. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm
open QuantumNLS.TerraMultiRound90Shifted QuantumNLS.TerraMultiRound91ShiftedCore
namespace QuantumNLS.TerraMultiRound91NormalizedCore
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

def normalizedCore {ι : Type*} (hc : 0 ≤ c) (ev : ι → ℝ) (y : ι → VSym L N) (i : ι) : VSym L N :=
  (((Real.sqrt (ev i + 1))⁻¹ : ℝ) : ℂ) • shiftRoot hc (y i)

/-- The form-normalized eigenvectors are orthonormal in the original
Hilbert structure on the form space. -/
theorem normalized_orthonormal {ι : Type*} (hc : 0 ≤ c)
    (b : HilbertBasis ι ℂ (SymL2 L N)) (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (y : ι → VSym L N) (hy : ∀ i, valSym (y i) = b i)
    (hpair : ∀ i (z : VSym L N), q c z.1 (y i).1 = (ev i : ℂ) * ⟪valSym z, b i⟫_ℂ) :
    Orthonormal ℂ (normalizedCore hc ev y) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp only [normalizedCore, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    shifted_core_pairing hc b ev y hy hpair]
  by_cases hij : i = j
  · subst j
    have hp : 0 < ev i + 1 := by linarith [hev i]
    have hs : (Real.sqrt (ev i + 1) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hp))
    have hs2 : (Real.sqrt (ev i + 1) : ℂ) ^ 2 = ((ev i + 1 : ℝ) : ℂ) := by
      exact_mod_cast Real.sq_sqrt hp.le
    simp only [orthonormal_iff_ite.mp b.orthonormal i i, if_true, mul_one]
    rw [Complex.ofReal_inv]
    field_simp
    rw [← hs2]
  · rw [b.orthonormal.inner_eq_zero hij]
    simp [hij]

#print axioms normalized_orthonormal
end QuantumNLS.TerraMultiRound91NormalizedCore
