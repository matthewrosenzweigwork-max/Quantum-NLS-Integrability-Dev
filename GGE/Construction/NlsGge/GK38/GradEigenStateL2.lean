import NlsGge.GK38.GradEigenStateODE

/-! K2: the actual coefficient-times-state derivative is L² for every complex
L² potential pair, spectral parameter and initial vector. No H¹ input is used. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem memLp_coverRep_unit (f : PhysicalL2) :
    MemLp (coverRep38 f) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_coverRep38 f).aestronglyMeasurable).2
  have hi := intervalIntegrable_iff.mp (intervalIntegrable_coverRep38_sq_one f)
  simpa only [Set.uIoc_of_le zero_le_one, IntegrableOn,
    restrict_Ioc_eq_restrict_Icc] using hi

theorem memLp_coefficient_entry (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    MemLp (fun s => zsCoeffPot38 φ z s i j) 2
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  have h0 := memLp_coverRep_unit φ.1
  have h1 := memLp_coverRep_unit φ.2
  fin_cases i <;> fin_cases j <;> simp only [zsCoeffPot38, zsCoeffPair]
  · exact memLp_const _
  · exact h0.const_mul Complex.I
  · exact (h1.const_mul Complex.I).neg
  · exact memLp_const _

theorem memLp_coefficient_kernel_product (φ : PotPair) (z : ℂ)
    (w : PairKernelCont38) (i j : Fin 2) :
    MemLp (fun s => zsCoeffPot38 φ z s i j * pairKernelExt38 w s j) 2
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hc := memLp_coefficient_entry φ z i j
  apply hc.of_le_mul
    (hc.aestronglyMeasurable.mul (continuous_component w j).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  calc
    ‖zsCoeffPot38 φ z s i j * pairKernelExt38 w s j‖ =
        ‖zsCoeffPot38 φ z s i j‖ * ‖pairKernelExt38 w s j‖ := norm_mul _ _
    _ ≤ ‖zsCoeffPot38 φ z s i j‖ * ‖w‖ :=
      mul_le_mul_of_nonneg_left (norm_pairKernelExt38_le w hs j) (norm_nonneg _)
    _ = ‖w‖ * ‖zsCoeffPot38 φ z s i j‖ := mul_comm _ _

theorem memLp_coefficient_kernel_mulVec (φ : PotPair) (z : ℂ)
    (w : PairKernelCont38) (i : Fin 2) :
    MemLp (fun s => Matrix.mulVec (zsCoeffPot38 φ z s) (pairKernelExt38 w s) i) 2
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hm := memLp_finsetSum (Finset.univ : Finset (Fin 2))
    (fun j _ => memLp_coefficient_kernel_product φ z w i j)
  simpa only [Matrix.mulVec, dotProduct] using hm

theorem state_derivative_L2 (φ : PotPair) (z : ℂ) (a : PairVec38) (i : Fin 2) :
    MemLp (fun s => Matrix.mulVec (zsCoeffPot38 φ z s)
      (pairKernelExt38 (state φ z a) s) i) 2
      (volume.restrict (Icc (0 : ℝ) 1)) :=
  memLp_coefficient_kernel_mulVec φ z (state φ z a) i

theorem state_deriv_memLp (φ : PotPair) (z : ℂ) (a : PairVec38) (i : Fin 2) :
    MemLp (deriv (fun s => pairKernelExt38 (state φ z a) s i)) 2
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  apply (state_derivative_L2 φ z a i).ae_eq
  filter_upwards [ae_hasDerivAt_state_component_restrict φ z a i] with s hs
  exact hs.deriv.symm

end
end NlsGge.GK38.GradEigen38
