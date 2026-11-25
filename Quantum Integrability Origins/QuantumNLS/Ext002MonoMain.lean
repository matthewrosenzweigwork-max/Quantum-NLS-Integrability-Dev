import Mathlib
import QuantumNLS.Ext002MonoEntries
import QuantumNLS.Ext002MonoCompression

/-!
# EXT-002 / V-01 full monodromy (owner decision D4), stage M5: gauged trace = DEF-048 transfer

Owner decision D4 (`implementation/ops/contracts/OWNER_DECISIONS_DEF043_DEF035_EXT005_EXT002_2026-11-16.md`,
sha256 37414179…): the source-pinned fixed-sector monodromy `[[A, cB], [C, D]]`
(`Ext002MonoEntries.monodromy`, Vlaar (2.4.1)-(2.4.4), p. 17 display, normalized fields
A04.tex:72-85 / Vlaar (2.2.1)) has gauged trace equal to the DEF-048 transfer
`BethePhysicalTransfer.transfer` (periodic_basis.tex:326-339):

  `e^{izL/2} (A_N(z) + D_N(z)) = S_N(z)`   (A04.tex:33-36, periodic_basis.tex:358).

Proof: termwise in the coupling power `n`,
* `n = 0`: the zero-field terms `e^{−izL/2} + e^{izL/2}`, gauged, give `1 + e^{izL}`
  (A04.tex:36; `Ext002MonoFields.monomial_const`);
* `n ≥ 1`: the gauged source kernels are the DEF-048 kernels `rawPlus`/`rawMinus`
  (`Ext002MonoKernels.sourceA_gauge`/`sourceD_gauge`), and the A04 compression identity
  (`Ext002MonoCompression.compression_total`) turns the normal-ordered field monomial into
  `(N)_n · totalPlacement N n (physicalKernel n z)`, i.e. `transferTerm` with `cⁿ (N)_n`.
`B` and `C` are not used (and are not inferred from the transfer); no identification axiom.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace QuantumNLS.Ext002MonoMain
open PhysicalTensor TensorCarrier BethePhysicalTransfer BetheTransferKernelAdjoint
open BetheTransferOperators Ext002MonoFields Ext002MonoEntries Ext002MonoSlice
open Ext002MonoCompression

variable (L : ℝ) [Fact (0 < L)]

theorem cast_add {m n : ℕ} (h : m = n)
    (A B : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m) :
    KernelDefinition.castSymSectorOperator h (A + B) =
      KernelDefinition.castSymSectorOperator h A + KernelDefinition.castSymSectorOperator h B := by
  cases h
  rfl

theorem cast_id {m n : ℕ} (h : m = n) (a : ℂ) :
    KernelDefinition.castSymSectorOperator h (a • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) m)) =
      a • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) n) := by
  cases h
  rfl

omit [Fact (0 < L)] in
theorem rawPlus_zero (z : ℂ) (x y : Fin 0 → ℝ) : rawPlus L z x y = 1 := by
  unfold rawPlus
  rw [if_pos (show PlusOrder L x y from ⟨fun j => j.elim0, fun i _ _ => i.elim0⟩)]
  simp only [displacement, Fin.sum_univ_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

omit [Fact (0 < L)] in
theorem rawMinus_zero (z : ℂ) (x y : Fin 0 → ℝ) :
    rawMinus L z x y = Complex.exp (Complex.I * L * z) := by
  unfold rawMinus MinusOrder
  rw [if_pos (show PlusOrder L y x from ⟨fun j => j.elim0, fun i _ _ => i.elim0⟩)]
  simp only [Fin.sum_univ_zero, Complex.ofReal_zero, mul_zero, sub_zero]
  congr 1
  ring

/-- The zero-particle DEF-048 kernel is the constant `1 + e^{izL}`. -/
theorem zero_kernel (z : ℂ) (p : (Fin 0 → AddCircle L) × (Fin 0 → AddCircle L)) :
    (BetheTensorSlice.sumKernel (plusKernel L 0 z) (minusKernel L 0 z)).fn p =
      1 + Complex.exp (Complex.I * L * z) := by
  show rawPlus L z (BetheWeakGradient.representatives L p.1)
      (BetheWeakGradient.representatives L p.2) +
    rawMinus L z (BetheWeakGradient.representatives L p.1)
      (BetheWeakGradient.representatives L p.2) = _
  rw [rawPlus_zero, rawMinus_zero]

theorem zero_monomial (z : ℂ) (q : ℕ) :
    monomial L q (ofKernel L (BetheTensorSlice.sumKernel (plusKernel L 0 z) (minusKernel L 0 z))) =
      (1 + Complex.exp (Complex.I * L * z)) • ContinuousLinearMap.id ℂ (H L (0+q)) := by
  have hfn : (ofKernel L (BetheTensorSlice.sumKernel (plusKernel L 0 z) (minusKernel L 0 z))).fn =
      (constKernel L (1 + Complex.exp (Complex.I * L * z))).fn :=
    funext fun p => zero_kernel L z p
  rw [monomial_congr L q _ _ hfn, monomial_const]

/-- The gauge `e^{izL/2}` turns the `n`-th terms of `A_N + D_N` into the monomial of the
DEF-048 kernel `K⁺ + K⁻` of degree `n`. -/
theorem gauged_term (N : ℕ) (c : ℝ) (z : ℂ) (n : Fin (N+1)) :
    Complex.exp (Complex.I * z * L / 2) •
        ((c : ℂ) ^ (n : ℕ) • KernelDefinition.castSymSectorOperator (sector_eq N n)
            (monomial L (N - n) (kernelA L n z)) +
          (c : ℂ) ^ (n : ℕ) • KernelDefinition.castSymSectorOperator (sector_eq N n)
            (monomial L (N - n) (kernelD L n z))) =
      (c : ℂ) ^ (n : ℕ) • KernelDefinition.castSymSectorOperator (sector_eq N n)
        (monomial L (N - n) (ofKernel L
          (BetheTensorSlice.sumKernel (plusKernel L n z) (minusKernel L n z)))) := by
  have hfn : (((kernelA L n z).smul (Complex.exp (Complex.I * z * L / 2))).add
      ((kernelD L n z).smul (Complex.exp (Complex.I * z * L / 2)))).fn =
      (ofKernel L (BetheTensorSlice.sumKernel (plusKernel L n z) (minusKernel L n z))).fn := by
    funext p
    show Complex.exp (Complex.I * z * L / 2) * (kernelA L n z).fn p +
        Complex.exp (Complex.I * z * L / 2) * (kernelD L n z).fn p =
      (plusKernel L n z).fn p + (minusKernel L n z).fn p
    rw [kernelA_gauge, kernelD_gauge]
  have key : Complex.exp (Complex.I * z * L / 2) • monomial L (N - n) (kernelA L n z) +
      Complex.exp (Complex.I * z * L / 2) • monomial L (N - n) (kernelD L n z) =
      monomial L (N - n) (ofKernel L
        (BetheTensorSlice.sumKernel (plusKernel L n z) (minusKernel L n z))) := by
    rw [← monomial_smul, ← monomial_smul, ← monomial_add, monomial_congr L _ _ _ hfn]
  calc _ = (c : ℂ) ^ (n : ℕ) • KernelDefinition.castSymSectorOperator (sector_eq N n)
          (Complex.exp (Complex.I * z * L / 2) • monomial L (N - n) (kernelA L n z) +
            Complex.exp (Complex.I * z * L / 2) • monomial L (N - n) (kernelD L n z)) := by
        rw [cast_add, cast_smul, cast_smul]
        simp only [smul_add, smul_smul, mul_comm]
    _ = _ := by rw [key]

/-- The coupling-power-zero term. -/
theorem term_of_val_zero (N : ℕ) (c : ℝ) (z : ℂ) (n : Fin (N+1)) (hn : (n : ℕ) = 0) :
    (c : ℂ) ^ (n : ℕ) • KernelDefinition.castSymSectorOperator (sector_eq N n)
        (monomial L (N - n) (ofKernel L
          (BetheTensorSlice.sumKernel (plusKernel L n z) (minusKernel L n z)))) =
      (1 + Complex.exp (Complex.I * L * z)) • ContinuousLinearMap.id ℂ (H L N) := by
  obtain ⟨k, hk⟩ := n
  have hk0 : k = 0 := hn
  subst hk0
  show (c : ℂ) ^ 0 • KernelDefinition.castSymSectorOperator (sector_eq N ⟨0, hk⟩)
      (monomial L (N - 0) (ofKernel L
        (BetheTensorSlice.sumKernel (plusKernel L 0 z) (minusKernel L 0 z)))) = _
  rw [pow_zero, one_smul, zero_monomial, cast_id]

/-- The positive coupling-power terms: A04 compression gives `transferTerm`. -/
theorem term_pos (N : ℕ) (c : ℝ) (z : ℂ) (n : Fin (N+1)) (hn : 0 < (n : ℕ)) :
    (c : ℂ) ^ (n : ℕ) • KernelDefinition.castSymSectorOperator (sector_eq N n)
        (monomial L (N - n) (ofKernel L
          (BetheTensorSlice.sumKernel (plusKernel L n z) (minusKernel L n z)))) =
      transferTerm L N c z n := by
  rw [transferTerm, if_pos hn, compression_total L N n (Nat.le_of_lt_succ n.isLt),
    physOp_sumKernel, smul_smul]
  congr 1
  push_cast
  ring

theorem transferTerm_zero (N : ℕ) (c : ℝ) (z : ℂ) : transferTerm L N c z 0 = 0 := by
  simp [transferTerm]

/-- **EXT-002 / V-01 headline (owner decision D4).** For the source-pinned fixed-sector
monodromy `[[A_N, cB_N], [C_N, D_N]]` of Vlaar (2.4.1)-(2.4.4), built from weak normal-ordered
monomials of normalized fields on the fixed sectors `H_N`, translated from `[−L/2, L/2]` to
the torus, the gauged trace equals the DEF-048 bounded physical transfer:
`e^{izL/2} (A_N(z) + D_N(z)) = BethePhysicalTransfer.transfer L N c z`. -/
theorem v01_gauged_trace_eq_transfer (N : ℕ) (c : ℝ) (z : ℂ) :
    Complex.exp (Complex.I * z * L / 2) • (monodromy L N c z).trace =
      BethePhysicalTransfer.transfer L N c z := by
  rw [monodromy_trace, entryA, entryD, ← Finset.sum_add_distrib, Finset.smul_sum]
  simp only [gauged_term]
  rw [Fin.sum_univ_succ, transfer, Fin.sum_univ_succ,
    term_of_val_zero L N c z 0 (by simp), transferTerm_zero, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact term_pos L N c z i.succ (by simp)

end QuantumNLS.Ext002MonoMain

#print axioms QuantumNLS.Ext002MonoMain.gauged_term
#print axioms QuantumNLS.Ext002MonoMain.term_of_val_zero
#print axioms QuantumNLS.Ext002MonoMain.term_pos
#print axioms QuantumNLS.Ext002MonoMain.v01_gauged_trace_eq_transfer

/- Dependency audit: the headline reaches the four source kernels (through the matrix in its
statement), the normalized-field monomial construction, the A04 compression, the general slice
formula, the M1 gauge identities and the frozen DEF-048 transfer ingredients. -/
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.Ext002MonoMain.v01_gauged_trace_eq_transfer]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.Ext002MonoKernels.sourceA,
      ``QuantumNLS.Ext002MonoKernels.sourceD,
      ``QuantumNLS.Ext002MonoKernels.sourceA_gauge,
      ``QuantumNLS.Ext002MonoKernels.sourceD_gauge,
      ``QuantumNLS.Ext002OddKernels.sourceCreationKernel,
      ``QuantumNLS.Ext002OddKernels.sourceAnnihilationKernel,
      ``QuantumNLS.Ext002MonoEntries.monodromy,
      ``QuantumNLS.Ext002MonoEntries.entryB,
      ``QuantumNLS.Ext002MonoEntries.entryC,
      ``QuantumNLS.Ext002MonoFields.monomial,
      ``QuantumNLS.Ext002MonoFields.sliceOp,
      ``QuantumNLS.Ext002MonoFields.monomial_const,
      ``QuantumNLS.Ext002MonoCompression.compression_total,
      ``QuantumNLS.Ext002MonoSymm.inner_sliceOp_avg,
      ``QuantumNLS.Ext002MonoSlice.tensor_eq_sliceOp,
      ``QuantumNLS.BethePhysicalTransfer.transfer,
      ``QuantumNLS.BethePhysicalTransfer.totalPlacement,
      ``QuantumNLS.BethePhysicalTransfer.physicalKernel,
      ``QuantumNLS.BethePhysicalTransfer.positionInclusion,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawPlus,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus] do
    unless seen.contains n do
      throwError "V-01 route missed ingredient: {n}"
  if seen.contains ``sorryAx then
    throwError "V-01 route contains sorryAx"
  Lean.logInfo m!"V-01 full-monodromy route PASS: {seen.size} transitive constants; source kernels A,B,C,D, normalized-field monomials, A04 compression, general slice formula, M1 gauge and DEF-048 transfer reached; no sorryAx."
