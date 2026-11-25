import QuantumNLS.NormalizedTransfer
import QuantumNLS.GridEigen

/-!
# R-36C23346 QG:lem:haar-linear-tail, Part 1: the finite-support generator and identity (a)

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:798-830`, equation
`QG:eq:haar-linear-generator`. For a finitely supported real sequence `t` (support `s`):

  `L_N(t) = (1/(κL)) Σ_n t_n (S_N(ωn) − 2·1) = (1/L) Σ_{r=1}^N κ^{r−1} ϑ_{N,r} U_{N,r}(T_r(t))`,

with `S_N = normalizedTransfer` (the transfer at `κ/N`, accepted), `ϑ_{N,r} = (N)_r/N^r = fallR N r`,
`U_{N,r} = genericU_N_r`, and `T_r(t) = Σ_n t_n K_{r,ω n}` (`K_{r,z} = physicalKernel`, definitionally the ordered
kernel). The sum over `r = 1..N` is written with `j = r−1 : Fin N`.

Proved here (standard axioms only): `generator_identity`. The operator-level clauses (selfadjointness, commutation
with `H_N` and the corrected counts) and the marginal estimate are NOT in this module (Part 2 and later).

Existing lemmas reused read-only: `NormalizedTransfer.normalizedTransfer`, `GridEigen.exp_grid`,
`RootOverlapLimit.genericU_add`, `RootOverlapLimit.genericU_smul`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate
open Finset

namespace QuantumNLS.LinearTailGenerator

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
open QuantumNLS.BethePhysicalTransfer QuantumNLS.HighMomentsRank QuantumNLS.NormalizedTransfer
open QuantumNLS.GridEigen

variable (L : ℝ) [Fact (0 < L)]

/-- The finitely supported operator `T_r(t) = Σ_{n∈s} t_n K_{r, ω n}` on `Sym^r L²(𝕋_L)`. -/
def finiteT (r : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) : BoundedSymmetricKernel (L2T L) r :=
  ∑ n ∈ s, (t n : ℂ) • physicalKernel L r (gridPt L n)

/-- The finitely supported generator `L_N(t) = (1/(κL)) Σ_{n∈s} t_n (S_N(ωn) − 2·1)`. -/
def genSum (κ : ℝ) (N : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) :
    SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  ((1 / (κ * L) : ℝ) : ℂ) •
    ∑ n ∈ s, (t n : ℂ) • (normalizedTransfer L κ N (gridPt L n) - (2 : ℂ) • ContinuousLinearMap.id ℂ _)

/-- `genericU_N_r` is additive and homogeneous in the kernel, so it commutes with finite sums. -/
theorem genericU_sum_smul (N r : ℕ) (hr : r ≤ N) (s : Finset ℤ) (c : ℤ → ℂ)
    (K : ℤ → BoundedSymmetricKernel (L2T L) r) :
    genericU_N_r N r hr (∑ n ∈ s, c n • K n) = ∑ n ∈ s, c n • genericU_N_r N r hr (K n) := by
  have h0 : genericU_N_r (H := L2T L) N r hr 0 = 0 := by
    have h := QuantumNLS.RootOverlapLimit.genericU_add (H := L2T L) N r hr 0 0
    rw [add_zero] at h
    simpa using h
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      QuantumNLS.RootOverlapLimit.genericU_add (H := L2T L) N r hr, ih,
      QuantumNLS.RootOverlapLimit.genericU_smul (H := L2T L) N r hr]

/-- The grid point `ωn` gives `e^{i(ωn)L} = 1`, so `S_N(ωn) − 2·1` is the falling-ratio kernel sum. -/
theorem normalizedTransfer_grid_sub_two (κ : ℝ) (N : ℕ) (n : ℤ) :
    normalizedTransfer L κ N (gridPt L n) - (2 : ℂ) • ContinuousLinearMap.id ℂ _ =
      ∑ j : Fin N, (((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ) •
        genericU_N_r N (j.val + 1) j.2 (physicalKernel L (j.val + 1) (gridPt L n)) := by
  unfold normalizedTransfer
  rw [exp_grid L n, show (1 : ℂ) + 1 = 2 by norm_num, add_sub_cancel_left]
  rfl

/-- **Identity (a) of `QG:eq:haar-linear-generator`.** For `κ > 0` and finitely supported `t` with support `s`,
`L_N(t) = (1/L) Σ_{r=1}^N κ^{r−1} ϑ_{N,r} U_{N,r}(T_r(t))` (with `j = r−1`, `ϑ_{N,r} = fallR N r`). -/
theorem generator_identity (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) :
    genSum L κ N s t =
      ∑ j : Fin N, (((1 / L) * κ ^ j.val * fallR N (j.val + 1) : ℝ) : ℂ) •
        genericU_N_r N (j.val + 1) j.2 (finiteT L (j.val + 1) s t) := by
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hL0 : L ≠ 0 := (Fact.out : (0 : ℝ) < L).ne'
  have h1 : ∑ n ∈ s, (t n : ℂ) • (normalizedTransfer L κ N (gridPt L n) -
        (2 : ℂ) • ContinuousLinearMap.id ℂ _) =
      ∑ j : Fin N, (((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ) •
        ∑ n ∈ s, (t n : ℂ) • genericU_N_r N (j.val + 1) j.2 (physicalKernel L (j.val + 1) (gridPt L n)) := by
    simp only [normalizedTransfer_grid_sub_two L κ N, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun n _ => ?_))
    rw [smul_comm]
  have hsumU : ∀ j : Fin N, genericU_N_r N (j.val + 1) j.2 (finiteT L (j.val + 1) s t) =
      ∑ n ∈ s, (t n : ℂ) • genericU_N_r N (j.val + 1) j.2 (physicalKernel L (j.val + 1) (gridPt L n)) := by
    intro j
    exact genericU_sum_smul L N (j.val + 1) j.2 s (fun n => (t n : ℂ))
      (fun n => physicalKernel L (j.val + 1) (gridPt L n))
  unfold genSum
  rw [h1, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul, hsumU j]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp
  ring

end QuantumNLS.LinearTailGenerator

#print axioms QuantumNLS.LinearTailGenerator.generator_identity
