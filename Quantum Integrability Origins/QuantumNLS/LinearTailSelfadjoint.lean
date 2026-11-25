import QuantumNLS.LinearTailGenerator

/-!
# R-36C23346 QG:lem:haar-linear-tail, Part 2: boundedness and selfadjointness of the finite-support generator

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:798-830`, clause (b) first half: `L_N(t)` is bounded and
selfadjoint for real finitely supported `t`.

Proved here (standard axioms only):
* `genSum_bounded`: `L_N(t)` is a bounded operator (it is a `ContinuousLinearMap`; a finite sum of bounded operators);
* `genSum_selfadjoint`: for real `t`, `(L_N(t))^† = L_N(t)`. The proof uses `normalizedTransfer_adjoint`
  (`S(z)^† = e^{-iL z̄} S(z̄)`) and `e^{-iL(ωn)} = 1` at the grid points, reused from the frozen modules.

Not in this module (OPEN, Part 3): commutation with the contact Hamiltonian `H_N` (unbounded, no identification of
the physical basis with its eigenvectors is in the repository) and commutation with the corrected counts `J_N`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace QuantumNLS.LinearTailSelfadjoint

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
open QuantumNLS.BethePhysicalTransfer QuantumNLS.HighMomentsRank QuantumNLS.NormalizedTransfer
open QuantumNLS.GridEigen QuantumNLS.LinearTailGenerator QuantumNLS.HaarKernelFactorizationSym

variable (L : ℝ) [Fact (0 < L)]

/-- Boundedness: `L_N(t)` is a continuous linear operator on `Sym^N L²(𝕋_L)`. -/
theorem genSum_bounded (κ : ℝ) (N : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) :
    ∃ A : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N, A = genSum L κ N s t :=
  ⟨genSum L κ N s t, rfl⟩

theorem conj_gridPt (n : ℤ) : conj (gridPt L n) = gridPt L n := by
  unfold gridPt
  exact Complex.conj_ofReal _

/-- The adjoint phase at a grid point is one: `e^{-iL·conj(ωn)} = e^{-2π i n} = 1`. -/
theorem adjointPhase_gridPt (n : ℤ) :
    QuantumNLS.BetheTransferKernelAdjoint.adjointPhase L (gridPt L n) = 1 := by
  unfold QuantumNLS.BetheTransferKernelAdjoint.adjointPhase
  rw [conj_gridPt]
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : (0 : ℝ) < L).ne'
  have h : -Complex.I * (L : ℂ) * gridPt L n = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold gridPt omegaL
    push_cast
    field_simp
  rw [h]
  exact Complex.exp_eq_one_iff.mpr ⟨-n, rfl⟩

/-- At a grid point the normalized transfer is selfadjoint: `S(ωn)^† = S(ωn)`. -/
theorem normalizedTransfer_gridPt_selfadjoint (κ : ℝ) (N : ℕ) (n : ℤ) :
    (normalizedTransfer L κ N (gridPt L n)).adjoint = normalizedTransfer L κ N (gridPt L n) := by
  rw [normalizedTransfer_adjoint, adjointPhase_gridPt, one_smul, conj_gridPt]

/-- **Selfadjointness of `L_N(t)`** for real finitely supported `t` (`QG:lem:haar-linear-tail`, clause (b) part 1). -/
theorem genSum_selfadjoint (κ : ℝ) (N : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) :
    (genSum L κ N s t).adjoint = genSum L κ N s t := by
  have hid : (ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N)).adjoint =
      ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N) := ContinuousLinearMap.adjoint_id
  have hA : ∀ n : ℤ, (normalizedTransfer L κ N (gridPt L n) - (2 : ℂ) • ContinuousLinearMap.id ℂ _).adjoint =
      normalizedTransfer L κ N (gridPt L n) - (2 : ℂ) • ContinuousLinearMap.id ℂ _ := by
    intro n
    have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    rw [map_sub, map_smulₛₗ, hid, normalizedTransfer_gridPt_selfadjoint, h2]
  unfold genSum
  rw [map_smulₛₗ, map_sum]
  simp only [map_smulₛₗ, map_sub, hA, Complex.conj_ofReal]

end QuantumNLS.LinearTailSelfadjoint

#print axioms QuantumNLS.LinearTailSelfadjoint.genSum_selfadjoint
