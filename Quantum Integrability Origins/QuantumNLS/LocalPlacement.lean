import QuantumNLS.GenericPlacementsZero
import QuantumNLS.PhysicalProductExpectation

/-!
QuantumNLS.LocalPlacement — the chosen kernel-expansion radius used in
LOCAL-011, together with its directly available placement consequences.

The source's full LOCAL-011 product theorem needs a bounded kernel for each
overlap size of two placements; its commutator estimate additionally needs a
radius-losing kernel formula.  Those fusion constructions are not supplied
by the frozen placement modules, so this file records the exact expansion
contract, its operator-norm and product-vector consequences, and the
zero-body product case without postulating the missing algebra.
-/

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition

noncomputable section

namespace QuantumNLS.LocalPlacement

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The finite list of symmetric-sector kernels at a fixed total particle
number.  The index `p` carries the literal constraint `p ≤ N`. -/
abbrev KernelList (N : ℕ) :=
  (p : Fin (N + 1)) → BoundedSymmetricKernel H p.1

/-- The operator represented by a chosen finite kernel list. -/
def representedOperator {N : ℕ} (A : KernelList (H := H) N) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  Finset.univ.sum (fun p : Fin (N + 1) =>
    genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p))

/-- A chosen expansion retains its kernels and its represented sector
operator.  This is a specified expansion, not a uniqueness assertion. -/
structure ChosenExpansion (N : ℕ) where
  kernels : KernelList (H := H) N
  operator : SymSector ℂ H N →L[ℂ] SymSector ℂ H N
  represents : operator = representedOperator kernels

/-- The radius bound of a chosen expansion, as in DEF-050. -/
def radiusBound {N : ℕ} (A : ChosenExpansion (H := H) N) (R : ℝ) : ℝ :=
  Finset.univ.sum (fun p : Fin (N + 1) => R ^ p.1 * ‖A.kernels p‖)

/-- The represented operator is controlled by every radius `R ≥ 1` of its
chosen expansion.  The constant is independent of the total particle number. -/
theorem norm_operator_le_radius {N : ℕ} (A : ChosenExpansion (H := H) N)
    {R : ℝ} (hR : 1 ≤ R) :
    ‖A.operator‖ ≤ radiusBound A R := by
  rw [A.represents]
  unfold representedOperator radiusBound
  calc
    ‖Finset.univ.sum (fun p : Fin (N + 1) =>
        genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A.kernels p))‖
        ≤ Finset.univ.sum (fun p : Fin (N + 1) =>
          ‖genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A.kernels p)‖) :=
      by
        simpa using (norm_sum_le (Finset.univ : Finset (Fin (N + 1)))
          (fun p => genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2)
            (A.kernels p)))
    _ ≤ Finset.univ.sum (fun p : Fin (N + 1) =>
        R ^ p.1 * ‖A.kernels p‖) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        ‖genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A.kernels p)‖
            ≤ ‖A.kernels p‖ :=
              norm_genericU_N_r_le N p.1 (Nat.lt_succ_iff.mp p.2) (A.kernels p)
        _ = 1 * ‖A.kernels p‖ := by ring
        _ ≤ R ^ p.1 * ‖A.kernels p‖ :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hR)
            (norm_nonneg (A.kernels p))

omit [CompleteSpace H] in
/-- Casting a scalar identity between two particle-count presentations does
not change the scalar operator. -/
theorem castSymSectorOperator_smul_id {m n : ℕ} (h : m = n) (c : ℂ) :
    castSymSectorOperator (H := H) h
      (c • ContinuousLinearMap.id ℂ (SymSector ℂ H m)) =
    c • ContinuousLinearMap.id ℂ (SymSector ℂ H n) := by
  cases h
  rfl

/-- The zero-body term is a scalar operator at every literal total particle
number.  This is the frozen generic `p = 0` placement theorem transported to
the total-count indexing used by expansions. -/
theorem genericU_N_0_eq_scalar (N : ℕ)
    (A : BoundedSymmetricKernel H 0) :
    genericU_N_r N 0 (Nat.zero_le N) A =
      GenericPlacementsZero.zeroKernelScalar (H := H) A •
        ContinuousLinearMap.id ℂ (SymSector ℂ H N) := by
  have hz := congrArg
    (castSymSectorOperator (Nat.add_sub_of_le (Nat.zero_le N)))
    (GenericPlacementsZero.Q_N_0_eq_scalar_id_on_split (H := H) N A)
  change castSymSectorOperator (Nat.add_sub_of_le (Nat.zero_le N))
      (U_N_r (r := 0) (q := N) A) = _
  rw [U_N_r_eq_Q_N_p]
  calc
    castSymSectorOperator (Nat.add_sub_of_le (Nat.zero_le N))
        (Q_N_p (p := 0) (q := N) A) =
      castSymSectorOperator (Nat.add_sub_of_le (Nat.zero_le N))
        (GenericPlacementsZero.zeroKernelScalar (H := H) A •
          ContinuousLinearMap.id ℂ (SymSector ℂ H (0 + N))) := hz
    _ = GenericPlacementsZero.zeroKernelScalar (H := H) A •
        ContinuousLinearMap.id ℂ (SymSector ℂ H N) :=
      castSymSectorOperator_smul_id (H := H)
        (Nat.add_sub_of_le (Nat.zero_le N)) _

/-- Left multiplication by the zero-body placement is scalar multiplication
on every operator on the same symmetric sector. -/
theorem genericU_N_0_comp (N : ℕ) (A : BoundedSymmetricKernel H 0)
    (B : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    (genericU_N_r N 0 (Nat.zero_le N) A).comp B =
      GenericPlacementsZero.zeroKernelScalar (H := H) A • B := by
  rw [genericU_N_0_eq_scalar]
  ext x
  simp

/-- A unit product vector evaluates a literal-total generic placement at its
kernel product symbol.  This is the frozen product-expectation constituent,
stated in the notation of the local expansion. -/
theorem inner_genericU_N_r_product_of_unit (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) (u : H) (hu : ‖u‖ = 1) :
    ⟪(htpow N u : HilbertTensorPower ℂ H N),
      ((genericU_N_r N r hr A
        ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) :
          HilbertTensorPower ℂ H N)⟫_ℂ = kernelProductSymbol A u := by
  rw [PhysicalProductExpectation.inner_genericU_N_r_product]
  have htail :
      ⟪(htpow (N - r) u : HilbertTensorPower ℂ H (N - r)),
        htpow (N - r) u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_htpow, hu]
    simp
  rw [htail, mul_one]

/-- The expectation of a chosen expansion on a unit product vector is the
finite sum of the product symbols of its kernels. -/
theorem inner_chosenExpansion_product_vector {N : ℕ}
    (A : ChosenExpansion (H := H) N) (u : H) (hu : ‖u‖ = 1) :
    ⟪(htpow N u : HilbertTensorPower ℂ H N),
      ((A.operator ⟨htpow N u, htpow_mem_symSector N u⟩ :
        SymSector ℂ H N) : HilbertTensorPower ℂ H N)⟫_ℂ =
      ∑ p : Fin (N + 1), kernelProductSymbol (A.kernels p) u := by
  rw [A.represents]
  simp only [representedOperator, sum_apply]
  rw [Submodule.coe_sum]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact inner_genericU_N_r_product_of_unit N p.1
    (Nat.lt_succ_iff.mp p.2) (A.kernels p) u hu

end QuantumNLS.LocalPlacement

#print axioms QuantumNLS.LocalPlacement.norm_operator_le_radius
#print axioms QuantumNLS.LocalPlacement.genericU_N_0_eq_scalar
#print axioms QuantumNLS.LocalPlacement.genericU_N_0_comp
#print axioms QuantumNLS.LocalPlacement.inner_genericU_N_r_product_of_unit
#print axioms QuantumNLS.LocalPlacement.inner_chosenExpansion_product_vector
