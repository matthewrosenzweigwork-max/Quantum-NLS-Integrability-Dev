import NlsGge.GK38.GradFundamentalL2
import NlsGge.GK38.GradFundamentalPairing

/-! # G1-098 M2 supporting module (g), proof development (AUTHOR; not reviewed).
Finite-sum integration for pointwise square bounds on pair kernels. If at every time in `[0,1]`
every finite partial sum of the squared first coordinates of the kernels `g j` is bounded by `C`,
then the squared L2 norms of the first coordinates of their actual classes are summable with
`tsum ≤ C`. Route: `norm_intervalKernelL2Class38_sq` gives each squared norm as an interval
integral, finite sums are moved inside the integral (all integrands are continuous), and the
pointwise bound is integrated over `[0,1]`. No hypothesis beyond the stated pointwise bound. -/
set_option autoImplicit false
open MeasureTheory Set Filter Topology
namespace NlsGge.GK38
noncomputable section

/-- The squared norm of the first coordinate of a pair-kernel class is the interval integral of the
squared first coordinate of the kernel. -/
theorem norm_pairKernelL2Class38_fst_sq (g : PairKernelCont38) :
    ‖(pairKernelL2Class38 g).1‖ ^ 2 = ∫ s in (0 : ℝ)..1, ‖pairKernelExt38 g s 0‖ ^ 2 :=
  norm_intervalKernelL2Class38_sq (memLp_pairKernelExt38 g 0)

/-- Continuity of the squared first coordinate of a pair kernel on the real line. -/
theorem continuous_pairKernelExt38_fst_sq_norm (g : PairKernelCont38) :
    Continuous (fun s : ℝ => ‖pairKernelExt38 g s 0‖ ^ 2) :=
  (((continuous_apply 0).comp (continuous_pairKernelExt38 g)).norm).pow 2

/-- Finite sums of squared first coordinates integrate termwise. -/
theorem integral_pairKernel_fst_sq_finset_sum {ι : Type*} (T : Finset ι) (g : ι → PairKernelCont38) :
    ∫ s in (0 : ℝ)..1, ∑ j ∈ T, ‖pairKernelExt38 (g j) s 0‖ ^ 2 =
      ∑ j ∈ T, ∫ s in (0 : ℝ)..1, ‖pairKernelExt38 (g j) s 0‖ ^ 2 :=
  intervalIntegral.integral_finsetSum (fun j _ =>
    (continuous_pairKernelExt38_fst_sq_norm (g j)).intervalIntegrable 0 1)

/-- Pointwise-in-time finite sum bound, integrated over the unit interval. -/
theorem m2g_finset_sum_le {ι : Type*} (g : ι → PairKernelCont38) {C : ℝ}
    (h : ∀ t : Set.Icc (0 : ℝ) 1, ∀ T : Finset ι, ∑ j ∈ T, ‖g j t 0‖ ^ 2 ≤ C)
    (T : Finset ι) :
    ∑ j ∈ T, ‖(pairKernelL2Class38 (g j)).1‖ ^ 2 ≤ C := by
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∑ j ∈ T, ‖pairKernelExt38 (g j) s 0‖ ^ 2 ≤ C := by
    intro s hs
    have hev : ∀ j : ι, pairKernelExt38 (g j) s 0 = g j ⟨s, hs⟩ 0 :=
      fun j => by rw [pairKernelExt38_of_mem (g j) hs]
    simp only [hev]
    exact h ⟨s, hs⟩ T
  calc ∑ j ∈ T, ‖(pairKernelL2Class38 (g j)).1‖ ^ 2
      = ∑ j ∈ T, ∫ s in (0 : ℝ)..1, ‖pairKernelExt38 (g j) s 0‖ ^ 2 :=
        Finset.sum_congr rfl (fun j _ => norm_pairKernelL2Class38_fst_sq (g j))
    _ = ∫ s in (0 : ℝ)..1, ∑ j ∈ T, ‖pairKernelExt38 (g j) s 0‖ ^ 2 :=
        (integral_pairKernel_fst_sq_finset_sum T g).symm
    _ ≤ ∫ _ in (0 : ℝ)..1, C :=
        intervalIntegral.integral_mono_on zero_le_one
          (continuous_finset_sum T (fun j _ => continuous_pairKernelExt38_fst_sq_norm (g j))
            |>.intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1) hpt
    _ = C := by simp

/-- M2g: summability of the squared first-coordinate L2 norms and the tsum bound. -/
theorem m2g_summable_of_pointwise {ι : Type*} (g : ι → PairKernelCont38) {C : ℝ}
    (h : ∀ t : Set.Icc (0 : ℝ) 1, ∀ T : Finset ι, ∑ j ∈ T, ‖g j t 0‖ ^ 2 ≤ C) :
    Summable (fun j : ι => ‖(pairKernelL2Class38 (g j)).1‖ ^ 2) ∧
      ∑' j : ι, ‖(pairKernelL2Class38 (g j)).1‖ ^ 2 ≤ C := by
  have hfin := m2g_finset_sum_le g h
  have hsum : Summable (fun j : ι => ‖(pairKernelL2Class38 (g j)).1‖ ^ 2) :=
    summable_of_sum_le (fun j => sq_nonneg _) hfin
  exact ⟨hsum, hsum.tsum_le_of_sum_le hfin⟩

end
end NlsGge.GK38
