/-
QuantumNLS.PhysicalProductExpectation — physical product-vector expectation
for the DEF-009 placement at a literal total particle number.

The proof factors the dependent `r + (N-r) = N` transport into a small
equality-elimination lemma, then uses the frozen physical/generic placement
consistency theorem and the generic product-pairing result.  This avoids
expanding the full placement definitions during cast normalization.
-/
import QuantumNLS.PlacementConsistency

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor

noncomputable section

namespace QuantumNLS.PhysicalProductExpectation

open QuantumNLS.KernelDefinition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Product-vector pairing is unchanged when a symmetric-sector operator is
transported along an equality of particle-count indices. -/
private theorem inner_castSymSectorOperator_product {m n : ℕ} (h : m = n)
    (T : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) (u : H) :
    ⟪(htpow n u : HilbertTensorPower ℂ H n),
      ((castSymSectorOperator (H := H) h T
        ⟨htpow n u, htpow_mem_symSector n u⟩ : SymSector ℂ H n) :
          HilbertTensorPower ℂ H n)⟫_ℂ =
      ⟪(htpow m u : HilbertTensorPower ℂ H m),
        ((T ⟨htpow m u, htpow_mem_symSector m u⟩ : SymSector ℂ H m) :
          HilbertTensorPower ℂ H m)⟫_ℂ := by
  cases h
  rfl

variable [CompleteSpace H]

/-- The arbitrary-total generic placement has the same product pairing as its
canonical `r + (N-r)` realization, including the spectator norm factor for a
non-unit profile. -/
theorem inner_genericU_N_r_product (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) (u : H) :
    ⟪(htpow N u : HilbertTensorPower ℂ H N),
      ((genericU_N_r (H := H) N r hr A
        ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) :
          HilbertTensorPower ℂ H N)⟫_ℂ =
      kernelProductSymbol A u *
        ⟪(htpow (N - r) u : HilbertTensorPower ℂ H (N - r)),
          htpow (N - r) u⟫_ℂ := by
  unfold genericU_N_r
  rw [inner_castSymSectorOperator_product]
  exact inner_U_N_r_product A u

variable (L : ℝ) [Fact (0 < L)]

/-- Physical product expectation for the DEF-009 operator at total particle
number `N`.  For a general profile, the untouched `N-r` factors contribute
their inner-product norm square. -/
theorem inner_physicalU_N_r_product (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel (L2T L) r) (u : L2T L) :
    ⟪(htpow N u : HilbertTensorPower ℂ (L2T L) N),
      ((physicalU_N_r L N r hr A
        ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ (L2T L) N) :
          HilbertTensorPower ℂ (L2T L) N)⟫_ℂ =
      kernelProductSymbol A u *
        ⟪(htpow (N - r) u : HilbertTensorPower ℂ (L2T L) (N - r)),
          htpow (N - r) u⟫_ℂ := by
  rw [PlacementConsistency.physicalU_N_r_eq_genericU_N_r L N r hr A]
  exact inner_genericU_N_r_product N r hr A u

/-- Unit-profile specialization, matching DEF-009's printed product symbol. -/
theorem inner_physicalU_N_r_product_of_unit (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel (L2T L) r) (u : L2T L) (hu : ‖u‖ = 1) :
    ⟪(htpow N u : HilbertTensorPower ℂ (L2T L) N),
      ((physicalU_N_r L N r hr A
        ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ (L2T L) N) :
          HilbertTensorPower ℂ (L2T L) N)⟫_ℂ = kernelProductSymbol A u := by
  rw [inner_physicalU_N_r_product L N r hr A u]
  have hq : ⟪(htpow (N - r) u : HilbertTensorPower ℂ (L2T L) (N - r)),
      htpow (N - r) u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_htpow, hu]
    simp
  rw [hq, mul_one]

end QuantumNLS.PhysicalProductExpectation

#print axioms QuantumNLS.PhysicalProductExpectation.inner_genericU_N_r_product
#print axioms QuantumNLS.PhysicalProductExpectation.inner_physicalU_N_r_product
#print axioms QuantumNLS.PhysicalProductExpectation.inner_physicalU_N_r_product_of_unit
