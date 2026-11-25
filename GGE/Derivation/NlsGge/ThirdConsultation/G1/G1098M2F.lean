import NlsGge.ThirdConsultation.G1.G1098Host
import NlsGge.ThirdConsultation.G1.G1098PairCLM
import NlsGge.ThirdConsultation.G1.G1098M2G
import NlsGge.ThirdConsultation.G1.G1098M2A
import NlsGge.ThirdConsultation.G1.G1098M2DE

/-! # G1-098 M2f, proof development (AUTHOR; not reviewed).
The column error is the first-coordinate class of a kernel difference. Linearity of the bounded
map `pairKernelL2CLM38` (`map_sub`) and the vacuum identity `complexMixedColumn_vacuum` give
`complexMixedColumn φ ψ n b - mixedReference n b = (pairKernelL2Class38 (K - K₀)).1`. Then the
finite-sum integration lemma `m2g_summable_of_pointwise` (M2g) applied to `g j = K_j - K₀_j` gives
summability of the squared column errors and the `tsum` bound, from the uniform finite-sum bound
of M2e (`mixed_finite_sum_bound`). No hypothesis beyond M2e is added. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open NlsGge.GK38 NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.G1098M2F
noncomputable section

theorem pairKernelL2Class38_sub_eq (A B : PairKernelCont38) :
    pairKernelL2Class38 (A - B) = pairKernelL2Class38 A - pairKernelL2Class38 B := by
  have h := map_sub pairKernelL2CLM38 A B
  simpa only [pairKernelL2CLM38_apply] using h

/-- The complex mixed column error equals the first-coordinate class of the kernel difference. -/
theorem complexMixedColumn_sub_vacuum (φ ψ : PotPair) (n : ℤ) (b : Bool) :
    complexMixedColumn φ ψ n b - mixedReference n b =
      (pairKernelL2Class38 (complexMixedKernel φ ψ n b - complexMixedKernel 0 0 n b)).1 := by
  rw [← NlsGge.ThirdConsultation.G1098M2A.complexMixedColumn_vacuum, pairKernelL2Class38_sub_eq]
  unfold complexMixedColumn
  exact (Prod.fst_sub _ _).symm

/-- M2f: summability of the squared complex mixed column errors and the uniform `tsum` bound,
from the pointwise finite-sum bound `hC` (M2e) through M2g. -/
theorem mixedColumn_error_summable (φ ψ : PotPair) (C : ℝ)
    (hC : ∀ t : Set.Icc (0 : ℝ) 1, ∀ T : Finset (ℤ × Bool),
      ∑ j ∈ T, ‖(complexMixedKernel φ ψ j.1 j.2 - complexMixedKernel 0 0 j.1 j.2) t 0‖ ^ 2 ≤ C) :
    Summable (fun j : ℤ × Bool =>
      ‖complexMixedColumn φ ψ j.1 j.2 - mixedReference j.1 j.2‖ ^ 2) ∧
    (∑' j : ℤ × Bool, ‖complexMixedColumn φ ψ j.1 j.2 - mixedReference j.1 j.2‖ ^ 2) ≤ C := by
  have hg := m2g_summable_of_pointwise
    (fun j : ℤ × Bool => complexMixedKernel φ ψ j.1 j.2 - complexMixedKernel 0 0 j.1 j.2) hC
  have hfun : (fun j : ℤ × Bool => ‖complexMixedColumn φ ψ j.1 j.2 - mixedReference j.1 j.2‖ ^ 2) =
      (fun j : ℤ × Bool => ‖(pairKernelL2Class38
        (complexMixedKernel φ ψ j.1 j.2 - complexMixedKernel 0 0 j.1 j.2)).1‖ ^ 2) := by
    funext j
    rw [complexMixedColumn_sub_vacuum]
  rw [hfun]
  exact hg

end
end NlsGge.ThirdConsultation.G1098M2F
