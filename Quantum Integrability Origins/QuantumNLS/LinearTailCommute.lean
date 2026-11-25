import QuantumNLS.LinearTailSelfadjoint
import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.CartesianOccupationTransfer
import QuantumNLS.TransferNormality

/-!
# R-36C23346 QG:lem:haar-linear-tail, Part 3: commutation of `L_N(t)` with the corrected counts `J_N`

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:798-830`, clause (b) second half (commutation with every
actual corrected count `J_N`).

Realized inputs (read-only, frozen or accepted):
* `UnconditionalBetheBasis.meanField_physicalBasis` (complete orthonormal Bethe basis at `κ/N`, accepted ae212789) and
  `UnconditionalBetheBasis.transfer_physicalBasis` (`S_N(z)` diagonal in it, accepted);
* `CartesianOccupationTransfer.physical` and its diagonal lemma `physical_diag` (`J_N = physical b g a a` multiplies
  `gaugedBasis b g m` by `m_a/N`);
* `TransferNormality.commute_of_diag` (two operators diagonal in one Hilbert basis commute, frozen 2fa59f86);
* `LinearTailGenerator.genSum`, `LinearTailSelfadjoint` (Parts 1–2, frozen).

Proved here (standard axioms only):
* `genSum_meanField`: `L_N(t)` acts on each Bethe vector by a scalar (`genEigen`);
* `genSum_gaugedBasis`: the same for the gauged basis;
* `genSum_commutes_correctedCount`: `L_N(t)` commutes with every corrected count `J_N = physical b g a a`.

OPEN (not in this module): commutation with the contact Hamiltonian `H_N` (unbounded; its eigenrelation on the physical
basis is not assembled here), and the marginal estimate (clause (c)).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace QuantumNLS.LinearTailCommute

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BethePhysicalTransfer
open QuantumNLS.NormalizedTransfer QuantumNLS.GridEigen QuantumNLS.LinearTailGenerator
open QuantumNLS.BetheOccupationGauge QuantumNLS.CartesianOccupationTransfer

variable (L : ℝ) [Fact (0 < L)]

/-- The diagonal eigenvalue of `L_N(t)` on the Bethe vector `b m`. -/
def genEigen (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N) (s : Finset ℤ) (t : ℤ → ℝ)
    (m : QuantumNLS.BetheLabels.MArr N) : ℂ :=
  ((1 / (κ * L) : ℝ) : ℂ) * ∑ n ∈ s, (t n : ℂ) *
    (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (gridPt L n) - 2)

/-- `L_N(t)` acts on each Bethe vector of the mean-field basis by the scalar `genEigen`. -/
theorem genSum_meanField (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (s : Finset ℤ) (t : ℤ → ℝ)
    (m : QuantumNLS.BetheLabels.MArr N) :
    genSum L κ N s t (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m) =
      genEigen L κ hκ N (by omega) s t m •
        QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m := by
  have hN0 : 0 < N := by omega
  have hterm : ∀ n : ℤ,
      (normalizedTransfer L κ N (gridPt L n) -
          (2 : ℂ) • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N))
        (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m) =
      (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN0 m (gridPt L n) - 2) •
        QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m := by
    intro n
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,
      QuantumNLS.UnconditionalBetheBasis.transfer_physicalBasis (L := L) hκ hN0 (gridPt L n) m,
      sub_smul, two_smul]
  unfold genSum genEigen
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smul_apply, hterm, smul_smul, ← Finset.sum_smul]

/-- `L_N(t)` is diagonal in the gauged Bethe basis `gaugedBasis b g` with the same scalars. -/
theorem genSum_gaugedBasis (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (s : Finset ℤ) (t : ℤ → ℝ)
    (g : Gauge) (m : QuantumNLS.BetheLabels.MArr N) :
    genSum L κ N s t (gaugedBasis (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) g m) =
      genEigen L κ hκ N (by omega) s t m •
        gaugedBasis (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) g m := by
  rw [gaugedBasis_apply, map_smul, genSum_meanField, smul_comm]

/-- **Commutation of `L_N(t)` with every corrected count `J_N = physical b g a a`**
(`QG:lem:haar-linear-tail`, clause (b), commutation with the actual corrected counts). -/
theorem genSum_commutes_correctedCount (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (s : Finset ℤ)
    (t : ℤ → ℝ) (g : Gauge) (a : ℤ) :
    Commute (genSum L κ N s t)
      (physical (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) g a a) :=
  QuantumNLS.TransferNormality.commute_of_diag
    (gaugedBasis (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) g) _ _ _ _
    (fun m => genSum_gaugedBasis L κ hκ N hN s t g m)
    (fun m => physical_diag _ g a m)

end QuantumNLS.LinearTailCommute

#print axioms QuantumNLS.LinearTailCommute.genSum_commutes_correctedCount
