import NlsGge.GK38.GradFundamentalGradient

/-! # K1: independent bounded diagonal spectral forcing.
GK Chapter I, Proposition3.1. Entrywise primitive integrability and continuity
precede operator construction; this does not define any derivative by fderiv.
-/
set_option autoImplicit false
open MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

theorem continuousOn_entryPrimitive38 (N : PairCont38) (i j : Fin 2) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, ext38 N s i j) (Icc (0 : ℝ) 1) := by
  have hc : Continuous (fun s => ext38 N s i j) := by
    have hn := continuous_ext38 N
    fun_prop
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (hc.intervalIntegrable (μ := volume) (0 : ℝ) 1)
  have hp := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1)
    (f := fun s => ext38 N s i j) (μ := volume) (by rwa [uIcc_of_le zero_le_one])
  rwa [uIcc_of_le zero_le_one] at hp

def entryPrimitiveCont38 (N : PairCont38) : PairCont38 :=
  ⟨fun t i j => ∫ s in (0 : ℝ)..(t : ℝ), ext38 N s i j,
    continuous_pi fun i => continuous_pi fun j => (continuousOn_entryPrimitive38 N i j).domRestrict⟩

theorem norm_entryPrimitiveCont38_le (N : PairCont38) : ‖entryPrimitiveCont38 N‖ ≤ ‖N‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg N)).mpr
  intro t
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg N)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg N)).mpr
  intro j
  change ‖∫ s in (0 : ℝ)..(t : ℝ), ext38 N s i j‖ ≤ ‖N‖
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs =>
    norm_ext38_entry_le N (show s ∈ Icc (0 : ℝ) 1 by
      simpa only [uIcc_of_le zero_le_one] using (uIcc_zero_subset t.2) (uIoc_subset_uIcc hs)) i j)
  rw [sub_zero, abs_of_nonneg t.2.1] at hb
  exact hb.trans (mul_le_of_le_one_right (norm_nonneg N) t.2.2)

def entryPrimitiveCLM38 : PairCont38 →L[ℂ] PairCont38 :=
  LinearMap.mkContinuous
    { toFun := entryPrimitiveCont38
      map_add' := by
        intro N P
        ext t i j
        change (∫ s in (0 : ℝ)..(t : ℝ), ext38 (N + P) s i j) =
          (∫ s in (0 : ℝ)..(t : ℝ), ext38 N s i j) + ∫ s in (0 : ℝ)..(t : ℝ), ext38 P s i j
        rw [← intervalIntegral.integral_add]
        · apply intervalIntegral.integral_congr
          intro s hs
          have hs' : s ∈ Icc (0 : ℝ) 1 := by
            simpa only [uIcc_of_le zero_le_one] using (uIcc_zero_subset t.2) hs
          simp only [ext38_of_mem _ hs', ContinuousMap.add_apply, Pi.add_apply]
        · exact (((continuous_apply j).comp ((continuous_apply i).comp
            (continuous_ext38 N))).intervalIntegrable _ _)
        · exact (((continuous_apply j).comp ((continuous_apply i).comp
            (continuous_ext38 P))).intervalIntegrable _ _)
      map_smul' := by
        intro c N
        ext t i j
        change (∫ s in (0 : ℝ)..(t : ℝ), ext38 (c • N) s i j) =
          c * ∫ s in (0 : ℝ)..(t : ℝ), ext38 N s i j
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le zero_le_one] using (uIcc_zero_subset t.2) hs
        simp only [ext38_of_mem _ hs', ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul] }
    1 (fun N => by simpa using norm_entryPrimitiveCont38_le N)

def spectralRowCLM38 : PairCont38 →L[ℂ] PairCont38 :=
  mulRowL 0 (ContinuousMap.const _ (-Complex.I)) + mulRowL 1 (ContinuousMap.const _ Complex.I)

theorem spectralRowCLM38_apply (N : PairCont38) (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    spectralRowCLM38 N t i j = (spectralCoeff38 * (Matrix.of (N t))) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [spectralRowCLM38, mulRowFun, spectralCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

/-- Independent bounded forcing operator `E_z(t) ∫ E_z(-s) Z N(s) ds`. -/
def spectralForcingCLM38 (z : ℂ) : PairCont38 →L[ℂ] PairCont38 :=
  (mulFree38 z).comp (entryPrimitiveCLM38.comp ((mulFree38 (-z)).comp spectralRowCLM38))


def spectralGaugeSource38 (z : ℂ) (N : PairCont38) (s : ℝ) : PairMat38 :=
  freeE z (-s) * spectralCoeff38 * ext38 N s

theorem intervalIntegrable_spectralGaugeSource38 (z : ℂ) (N : PairCont38) (i j : Fin 2) :
    IntervalIntegrable (fun s => spectralGaugeSource38 z N s i j) volume 0 1 := by
  have he : Continuous (fun s : ℝ => freeE z (-s)) := (continuous_freeE z).comp continuous_neg
  have hn := continuous_ext38 N
  have hc : Continuous (fun s => spectralGaugeSource38 z N s i j) := by
    unfold spectralGaugeSource38
    fun_prop
  exact hc.intervalIntegrable _ _

theorem freeE_neg_parameter38 (z : ℂ) (s : ℝ) : freeE (-z) s = freeE z (-s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [freeE]

theorem spectralForcingCLM38_apply (z : ℂ) (N : PairCont38) (t : Icc (0 : ℝ) 1)
    (i j : Fin 2) : spectralForcingCLM38 z N t i j =
      freeE z t i i * ∫ s in (0 : ℝ)..(t : ℝ), spectralGaugeSource38 z N s i j := by
  change mulFree38 z (entryPrimitiveCLM38 (mulFree38 (-z) (spectralRowCLM38 N))) t i j = _
  rw [mulFree38_apply]
  congr 1
  change (∫ s in (0 : ℝ)..(t : ℝ), ext38 (mulFree38 (-z) (spectralRowCLM38 N)) s i j) = _
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using (uIcc_zero_subset t.2) hs
  change ext38 (mulFree38 (-z) (spectralRowCLM38 N)) s i j = spectralGaugeSource38 z N s i j
  rw [ext38_of_mem _ hs', mulFree38_apply, spectralRowCLM38_apply,
    freeE_neg_parameter38]
  have hn : ext38 N s = Matrix.of (N ⟨s, hs'⟩) := by
    rw [ext38_of_mem _ hs']; rfl
  change freeE z (-s) i i * (spectralCoeff38 * Matrix.of (N ⟨s, hs'⟩)) i j = _
  rw [spectralGaugeSource38, mul_assoc, freeE_mul_apply, hn]

end
end NlsGge.GK38
