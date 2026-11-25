import NlsGge.GK38.GradEigenKernels
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

def RealKernelInjectiveTarget : Prop :=
  ∀ w : PairKernelCont38, realSymmetric w → realKernelCLM w=0 → w=0

theorem real_kernel_conjugate_direction (w : PairKernelCont38) (hw : realSymmetric w) :
    ∃ h : PhysicalL2, realKernelCLM w h=energy w := by
  let a : PhysicalL2 := intervalKernelL2Class38 (fun s => pairKernelExt38 w s 0)
    (memLp_pairKernelExt38 w 0)
  let h : PhysicalL2 := star a
  have hrep : coverRep38 a =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun s => pairKernelExt38 w s 0 :=
    coverRep_intervalKernelL2Class38 (memLp_pairKernelExt38 w 0)
  have hi := intervalIntegrable_pairKernel38 w t1 (realSlice h)
  have hE := (kernel_integrability w).2.1
  have heq : (fun s => pairKernelExt38 w s 0*potRepFst38 (realSlice h) s+
      pairKernelExt38 w s 1*potRepSnd38 (realSlice h) s) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun s => ((‖pairKernelExt38 w s 0‖^2+‖pairKernelExt38 w s 1‖^2 : ℝ) : ℂ) := by
    filter_upwards [hrep,ae_restrict_of_ae (coverRep38_star_ae a),
      ae_restrict_of_ae (potRepSnd38_realSlice_ae h),ae_restrict_mem measurableSet_Icc]
      with s ha hh hs hm
    have hfst : potRepFst38 (realSlice h) s=star (pairKernelExt38 w s 0) := by
      change coverRep38 (star a) s=star (pairKernelExt38 w s 0)
      rw [hh,ha]
    have hsnd : potRepSnd38 (realSlice h) s=pairKernelExt38 w s 0 := by
      rw [hs,hfst,star_star]
    have hsym : pairKernelExt38 w s 1=star (pairKernelExt38 w s 0) := by
      rw [pairKernelExt38_of_mem w hm]
      exact hw ⟨s,hm⟩
    rw [hfst,hsnd,hsym]
    simp only [Complex.star_def,Complex.mul_conj',Complex.conj_mul',Complex.norm_conj,
      Complex.ofReal_add,Complex.ofReal_pow]
  have hpair : pairIntegral38 w t1 (realSlice h)=(energy w : ℂ) := by
    unfold pairIntegral38 energy
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae_restrict
    simp only [t1]
    rw [uIoc_of_le zero_le_one,restrict_Ioc_eq_restrict_Icc]
    exact heq
  refine ⟨h,?_⟩
  change (pairIntegral38 w t1 (realSlice h)).re=energy w
  rw [hpair]
  rfl

theorem real_kernel_injective_target : RealKernelInjectiveTarget := by
  intro w hw hzero
  obtain ⟨h,he⟩ := real_kernel_conjugate_direction w hw
  have hz := congrArg (fun L : PhysicalL2 →L[ℝ] ℝ => L h) hzero
  change realKernelCLM w h=0 at hz
  have hE : energy w=0 := he.symm.trans hz
  apply ContinuousMap.ext
  intro t
  by_contra hval
  have hp := energy_pos_of_value w t hval
  rw [hE] at hp
  exact (lt_irrefl (0 : ℝ)) hp

end
end NlsGge.GK38.GradEigen38
