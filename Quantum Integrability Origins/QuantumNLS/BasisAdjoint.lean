import QuantumNLS.NormalizedTransfer

/-!
# R-99FDE9B6 `basis:lem:adjoint`: adjoints of the physical transfer operators
(`periodic_basis.tex:377–397`)

> For every `z ∈ ℂ`, `K_{m,z}^* = e^{-iL\bar z} K_{m,\bar z}` and `S_{N,c}(z)^* = e^{-iL\bar z} S_{N,c}(\bar z)`.
> In particular `T_{N,c}(x) = e^{-iLx/2} S_{N,c}(x)` is self-adjoint for every real `x`.

Printed proof: `(K̃⁺_{m,z})^* = e^{-iL\bar z} K̃⁻_{m,\bar z}` and `(K̃⁻_{m,z})^* = e^{-iL\bar z} K̃⁺_{m,\bar z}` (swap
input/output coordinates and conjugate); `P_m` is an orthogonal projection and the averaged placement preserves
adjoints; the scalar term `(1 + e^{iLz})` has the same adjoint phase; for real `x` conjugating the scalar gauge.

Every printed clause is stated here in the printed form, for the frozen physical Bethe operators
(`BetheTransferKernelAdjoint`, `BetheTransferOperators`, `BethePhysicalTransfer`), whose proofs are reused read-only,
and for DEF-048's normalized transfer `NormalizedTransfer.normalizedTransfer` (coupling `c = κ/N`) via
`normalizedTransfer_adjoint` (already proved in `NormalizedTransfer` through the bridge
`normalizedTransfer_eq_transfer`).  The phase `e^{-iL\bar z}` is `BetheTransferKernelAdjoint.adjointPhase L z`
(`adjointPhase_eq`).  Clauses:
* pointwise kernel adjoints (`rawPlus_adjoint'`, `rawMinus_adjoint'`) and their operator forms
  (`plusOperator_adjoint'`, `minusOperator_adjoint'`) on `L²(𝕋_L^m)`;
* `K_{m,z}^* = e^{-iL\bar z} K_{m,\bar z}` for all `z` (`kernel_adjoint`);
* the scalar term (`scalar_adjoint'`) and the preservation of adjoints by `P_m` and by the averaged placement
  (`placement_adjoint'`);
* `S_{N,c}(z)^* = e^{-iL\bar z} S_{N,c}(\bar z)` for every real `c` (`transfer_adjoint'`) and for the normalized
  transfer (`normalizedTransfer_adjoint'`);
* self-adjointness of `T_{N,c}(x) = e^{-iLx/2} S_{N,c}(x)` for real `x` (`T_selfAdjoint`) and of the normalized
  `T_N(x) = e^{-iLx/2} S_N(x)` (`normalizedT_selfAdjoint`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.BasisAdjoint

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
open QuantumNLS.BetheTransferKernelAdjoint QuantumNLS.BetheTransferOperators
  QuantumNLS.BethePhysicalTransfer QuantumNLS.NormalizedTransfer

variable (L : ℝ) [Fact (0 < L)]

/-- The printed phase `e^{-iL\bar z}` is `adjointPhase`. -/
theorem adjointPhase_eq (z : ℂ) : adjointPhase L z = Complex.exp (-Complex.I * L * conj z) := rfl

omit [Fact (0 < L)] in
/-- `(K̃⁺_{m,z})^*(x;y) = e^{-iL\bar z} K̃⁻_{m,\bar z}(x;y)`, pointwise (swap and conjugate). -/
theorem rawPlus_adjoint' {m : ℕ} (z : ℂ) (x y : Fin m → ℝ) :
    conj (rawPlus L z y x) = Complex.exp (-Complex.I * L * conj z) * rawMinus L (conj z) x y :=
  rawPlus_adjoint L z x y

omit [Fact (0 < L)] in
/-- `(K̃⁻_{m,z})^*(x;y) = e^{-iL\bar z} K̃⁺_{m,\bar z}(x;y)`, pointwise. -/
theorem rawMinus_adjoint' {m : ℕ} (z : ℂ) (x y : Fin m → ℝ) :
    conj (rawMinus L z y x) = Complex.exp (-Complex.I * L * conj z) * rawPlus L (conj z) x y :=
  rawMinus_adjoint L z x y

/-- Operator form of the first printed identity on `L²(𝕋_L^m)`. -/
theorem plusOperator_adjoint' (m : ℕ) (z : ℂ) :
    (plusKernel L m z).operator.adjoint =
      Complex.exp (-Complex.I * L * conj z) • (minusKernel L m (conj z)).operator :=
  plusOperator_adjoint L m z

/-- Operator form of the second printed identity. -/
theorem minusOperator_adjoint' (m : ℕ) (z : ℂ) :
    (minusKernel L m z).operator.adjoint =
      Complex.exp (-Complex.I * L * conj z) • (plusKernel L m (conj z)).operator :=
  minusOperator_adjoint L m z

/-- `(K̃⁺ + K̃⁻)^* = e^{-iL\bar z}(K̃⁺ + K̃⁻)_{\bar z}`. -/
theorem rawOperator_adjoint' (m : ℕ) (z : ℂ) :
    (rawOperator L m z).adjoint = Complex.exp (-Complex.I * L * conj z) • rawOperator L m (conj z) :=
  rawOperator_adjoint L m z

/-- **`K_{m,z}^* = e^{-iL\bar z} K_{m,\bar z}`** for every `z ∈ ℂ` (`K_{m,z} = P_m(K̃⁺+K̃⁻)P_m`). -/
theorem kernel_adjoint (m : ℕ) (z : ℂ) :
    (orderedKernel L m z).adjoint =
      Complex.exp (-Complex.I * L * conj z) • orderedKernel L m (conj z) :=
  physicalKernel_adjoint L m z

omit [Fact (0 < L)] in
/-- The scalar term of `S_{N,c}(z)` has the same adjoint phase: `conj(1+e^{iLz}) = e^{-iL\bar z}(1+e^{iL\bar z})`. -/
theorem scalar_adjoint' (z : ℂ) :
    conj (1 + Complex.exp (Complex.I * L * z)) =
      Complex.exp (-Complex.I * L * conj z) * (1 + Complex.exp (Complex.I * L * conj z)) :=
  scalar_adjoint L z

/-- The averaged placement `U_{N,m}` preserves adjoints (`P_N` orthogonal). -/
theorem placement_adjoint' (N m : ℕ) (hm : m ≤ N) (K : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m) :
    (genericU_N_r N m hm K).adjoint = genericU_N_r N m hm K.adjoint := by
  rw [← totalPlacement_eq_genericU, ← totalPlacement_eq_genericU]
  exact totalPlacement_adjoint N m hm K

/-- **`S_{N,c}(z)^* = e^{-iL\bar z} S_{N,c}(\bar z)`** for every `z ∈ ℂ` and real `c`. -/
theorem transfer_adjoint' (N : ℕ) (c : ℝ) (z : ℂ) :
    (transfer L N c z).adjoint =
      Complex.exp (-Complex.I * L * conj z) • transfer L N c (conj z) :=
  transfer_adjoint L N c z

/-- The same identity for DEF-048's normalized transfer `S_N(z)` (coupling `κ/N`). -/
theorem normalizedTransfer_adjoint' (κ : ℝ) (N : ℕ) (z : ℂ) :
    (normalizedTransfer L κ N z).adjoint =
      Complex.exp (-Complex.I * L * conj z) • normalizedTransfer L κ N (conj z) :=
  NormalizedTransfer.normalizedTransfer_adjoint L κ N z

/-- **`T_{N,c}(x) = e^{-iLx/2} S_{N,c}(x)` is self-adjoint** for every real `x`. -/
theorem T_selfAdjoint (N : ℕ) (c x : ℝ) :
    IsSelfAdjoint (Complex.exp (-Complex.I * L * x / 2) • transfer L N c x) :=
  realTransfer_isSelfAdjoint L N c x

/-- The normalized `T_N(x) = e^{-iLx/2} S_N(x)` is self-adjoint for real `x`. -/
theorem normalizedT_selfAdjoint (κ : ℝ) (N : ℕ) (x : ℝ) :
    IsSelfAdjoint (Complex.exp (-Complex.I * L * x / 2) • normalizedTransfer L κ N x) := by
  rw [normalizedTransfer_eq_transfer]
  exact realTransfer_isSelfAdjoint L N (κ / N) x

#print axioms kernel_adjoint
#print axioms transfer_adjoint'
#print axioms normalizedTransfer_adjoint'
#print axioms T_selfAdjoint
#print axioms normalizedT_selfAdjoint
#print axioms placement_adjoint'

end QuantumNLS.BasisAdjoint
