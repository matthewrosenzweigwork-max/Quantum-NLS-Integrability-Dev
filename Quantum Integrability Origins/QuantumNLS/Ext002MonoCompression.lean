import Mathlib
import QuantumNLS.Ext002MonoSymm

/-!
# EXT-002 / V-01 full monodromy (owner decision D4), stage M4c: the A04 compression identity

`source/chapters/foundations/A04.tex:54-99`, eq. `(A04-compression)`: for a bounded measurable
kernel `a` on `(0,L)^r × (0,L)^r`, `Ã` its integral operator and `A = P_r Ã P_r`, the
normal-ordered integral with `r` creation and `r` annihilation normalized fields, restricted to
`H_N`, equals `(N)_r P_N (A ⊗ 1^{⊗(N−r)}) P_N`.

* `compression`: `monomial q (ofKernel k) = (r+q)_r • placement (physOp k)` on `H_{r+q}`, where
  `placement` is the frozen DEF-048 normalized placement `P_N (A ⊗ 1) P_N` and
  `physOp k = P_r Ã P_r`;
* `compression_total`: the same at a literal particle number `N` with the frozen
  `totalPlacement N r` (the operator used in `BethePhysicalTransfer.transferTerm`).
Proof chain: weak matrix element (`inner_monomial`/`sliceOp`), symmetrization
(`inner_sliceOp_avg`, A04.tex:92-95), general-degree slice formula on `L²`
(`tensor_eq_sliceOp`), and `P_N` insertion (adjoint of the sector inclusion, A04.tex:95-96).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace QuantumNLS.Ext002MonoCompression
open PhysicalTensor TensorCarrier TensorPlacements BethePhysicalTransfer BetheIntegralOperator
open Ext002MonoLift Ext002MonoFields Ext002MonoSlice Ext002MonoSymm

variable (L : ℝ) [Fact (0 < L)]

/-- **A04 compression identity** (eq. A04-compression), spectator form. -/
theorem compression {r : ℕ} (q : ℕ) (k : Kernel (torusPiMeasure L r)) :
    monomial L q (ofKernel L k) =
      (((r+q).descFactorial r : ℕ) : ℂ) • placement (q := q) (physOp L k) := by
  apply ContinuousLinearMap.ext
  intro G
  apply ext_inner_left ℂ
  intro F
  have hc : ((Real.sqrt (((r+q).descFactorial r * (r+q).descFactorial r : ℕ) : ℝ) : ℝ) : ℂ) =
      (((r+q).descFactorial r : ℕ) : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hT := congrArg (fun T : L2TN L (r+q) →L[ℂ] L2TN L (r+q) =>
    ⟪positionInclusion L (r+q) F, T (positionInclusion L (r+q) G)⟫_ℂ) (tensor_eq_sliceOp L q k)
  rw [monomial]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rw [hc, ← inner_sliceOp_avg, ← hT]
  congr 1
  simp only [placement, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  change ⟪physUnitary (F : HilbertTensorPower ℂ (L2T L) (r+q)),
      physUnitary (firstPlacement (q := q) (physOp L k)
        ((physUnitary (L := L) (N := r+q)).symm
          (physUnitary (G : HilbertTensorPower ℂ (L2T L) (r+q)))))⟫_ℂ =
    ⟪(F : HilbertTensorPower ℂ (L2T L) (r+q)),
      firstPlacement (q := q) (physOp L k) (G : HilbertTensorPower ℂ (L2T L) (r+q))⟫_ℂ
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]

/-- **A04 compression identity at literal particle number `N`**:
`W_{r,r}(a)|_{H_N} = (N)_r · totalPlacement N r (P_r Ã P_r)`. -/
theorem compression_total (N r : ℕ) (hr : r ≤ N) (k : Kernel (torusPiMeasure L r)) :
    KernelDefinition.castSymSectorOperator (Nat.add_sub_of_le hr)
        (monomial L (N - r) (ofKernel L k)) =
      ((N.descFactorial r : ℕ) : ℂ) • totalPlacement N r hr (physOp L k) := by
  have hd : (((r + (N - r)).descFactorial r : ℕ) : ℂ) = ((N.descFactorial r : ℕ) : ℂ) := by
    rw [Nat.add_sub_of_le hr]
  rw [compression, totalPlacement, cast_smul, hd]

end QuantumNLS.Ext002MonoCompression

#print axioms QuantumNLS.Ext002MonoCompression.compression
#print axioms QuantumNLS.Ext002MonoCompression.compression_total
