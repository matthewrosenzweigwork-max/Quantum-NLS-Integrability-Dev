import Mathlib
import NlsGge.GK38.PairPotential
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

/- G5-004 SUPPORT1 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/Atomic/G5/G5004Support1.lean.  Pro round 10 section 7 (commit 178f84d6), statements byte-identical:
   sourceBetaW_subset_gkW, fderiv_realSlice_eq, norm_fderiv_realSlice_le.
   No new names in NlsGge.GKDefinitionDesign beyond these three. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem sourceBetaW_subset_gkW : sourceBetaW ⊆ gkW := by
  intro φ hφ
  exact sourceFamily.W_gk (sourceFamily.V_W hφ)

theorem fderiv_realSlice_eq (f : PotPair → ℂ) (u : PhysicalL2)
    (hf : DifferentiableAt ℂ f (realSlice u)) :
  fderiv ℝ (fun v : PhysicalL2 => f (realSlice v)) u =
    ((fderiv ℂ f (realSlice u)).restrictScalars ℝ).comp realSlice := by
  have h1 : HasFDerivAt f ((fderiv ℂ f (realSlice u)).restrictScalars ℝ) (realSlice u) :=
    hf.hasFDerivAt.restrictScalars ℝ
  exact (h1.comp u realSlice.hasFDerivAt).fderiv

theorem norm_fderiv_realSlice_le (f : PotPair → ℂ) (u : PhysicalL2)
    (hf : DifferentiableAt ℂ f (realSlice u)) :
  ‖fderiv ℝ (fun v : PhysicalL2 => f (realSlice v)) u‖ ≤
    ‖fderiv ℂ f (realSlice u)‖ := by
  rw [fderiv_realSlice_eq f u hf]
  have hrs : ‖realSlice‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [norm_realSlice, one_mul]
  calc ‖((fderiv ℂ f (realSlice u)).restrictScalars ℝ).comp realSlice‖
      ≤ ‖(fderiv ℂ f (realSlice u)).restrictScalars ℝ‖ * ‖realSlice‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℂ f (realSlice u)‖ * 1 := by
        rw [ContinuousLinearMap.norm_restrictScalars]
        exact mul_le_mul_of_nonneg_left hrs (norm_nonneg _)
    _ = ‖fderiv ℂ f (realSlice u)‖ := mul_one _

end
end NlsGge.GKDefinitionDesign
