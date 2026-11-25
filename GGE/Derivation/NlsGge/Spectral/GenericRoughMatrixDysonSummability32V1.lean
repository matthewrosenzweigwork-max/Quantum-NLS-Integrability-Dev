import NlsGge.Spectral.GenericRoughMatrixDysonFactorial32V1
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open CumulativePowerV3 CumulativePowerGeneralEndpointV1

/-- The actual series of the generic left-ordered iterates. Every use as a
fundamental solution must separately establish summability and the equation. -/
def genericRoughMatrixDysonTsum32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∑' n, genericRoughMatrixDysonTerm32 B n t i j

theorem continuousOn_genericRoughMatrixDysonTerm32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 T)
    (n : ℕ) (i j : Fin 2) :
    ContinuousOn (fun t => genericRoughMatrixDysonTerm32 B n t i j) (Set.Icc (0 : ℝ) T) := by
  induction n generalizing i j with
  | zero =>
      simpa [genericRoughMatrixDysonTerm32] using
        (continuousOn_const : ContinuousOn
          (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) (Set.Icc (0 : ℝ) T))
  | succ n ih =>
      change ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t,
        (B s * genericRoughMatrixDysonTerm32 B n s) i j) (Set.Icc (0 : ℝ) T)
      have hD (k : Fin 2) : ContinuousOn
          (fun s => genericRoughMatrixDysonTerm32 B n s k j) (Set.uIcc (0 : ℝ) T) := by
        simpa only [Set.uIcc_of_le hT] using ih k j
      have hprod (k : Fin 2) := (hB i k).mul_continuousOn (hD k)
      have hg : IntervalIntegrable
          (fun s => (B s * genericRoughMatrixDysonTerm32 B n s) i j) volume 0 T := by
        simpa only [Matrix.mul_apply, Fin.sum_univ_two] using (hprod 0).add (hprod 1)
      have hz : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) T := Set.left_mem_uIcc
      simpa only [Set.uIcc_of_le hT] using
        intervalIntegral.continuousOn_primitive_interval' (μ := volume) hg hz

theorem genericRoughMatrixDysonTerm_uniform_bound32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T) (hqpos : ∀ s, 0 ≤ q s)
    (hmajorant : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    ‖genericRoughMatrixDysonTerm32 B n t i j‖ ≤
      (2 * actualCumulativeRealIntegral q T) ^ n / (n.factorial : ℝ) := by
  have hn : 0 ≤ actualCumulativeRealIntegral q t :=
    intervalIntegral.integral_nonneg_of_forall ht.1 hqpos
  have hend : actualCumulativeRealIntegral q t ≤ actualCumulativeRealIntegral q T :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall hqpos) hq
  have hpow := pow_le_pow_left₀ hn hend n
  calc
    _ ≤ (2 ^ n / (n.factorial : ℝ)) * actualCumulativeRealIntegral q t ^ n :=
      genericRoughMatrixDysonTerm_factorial_bound32 B q T hq hqpos hmajorant n t ht i j
    _ ≤ (2 ^ n / (n.factorial : ℝ)) * actualCumulativeRealIntegral q T ^ n :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem summable_genericRoughMatrixDysonTerm32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T) (hqpos : ∀ s, 0 ≤ q s)
    (hmajorant : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    Summable (fun n : ℕ => genericRoughMatrixDysonTerm32 B n t i j) := by
  exact Summable.of_norm_bounded
    (NormedSpace.expSeries_div_hasSum_exp (2 * actualCumulativeRealIntegral q T)).summable
    (fun n => genericRoughMatrixDysonTerm_uniform_bound32 B q T hq hqpos hmajorant n t ht i j)

theorem hasSum_genericRoughMatrixDysonProduct32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T) (hqpos : ∀ s, 0 ≤ q s)
    (hmajorant : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    HasSum (fun n => (B t * genericRoughMatrixDysonTerm32 B n t) i j)
      ((B t * genericRoughMatrixDysonTsum32 B t) i j) := by
  have h0 := (summable_genericRoughMatrixDysonTerm32 B q T hq hqpos hmajorant t ht 0 j).hasSum
  have h1 := (summable_genericRoughMatrixDysonTerm32 B q T hq hqpos hmajorant t ht 1 j).hasSum
  simpa only [genericRoughMatrixDysonTsum32, Matrix.mul_apply, Fin.sum_univ_two] using
    (h0.mul_left (B t i 0)).add (h1.mul_left (B t i 1))

/-- Rough entrywise L¹ coefficients and the realized majorant give continuity
of the actual series on the compact interval, without coefficient continuity. -/
theorem continuousOn_genericRoughMatrixDysonTsum32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 T)
    (hq : IntervalIntegrable q volume 0 T) (hqpos : ∀ s, 0 ≤ q s)
    (hmajorant : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s)
    (i j : Fin 2) :
    ContinuousOn (fun t => genericRoughMatrixDysonTsum32 B t i j) (Set.Icc (0 : ℝ) T) := by
  let bound : ℕ → ℝ := fun n => (2 * actualCumulativeRealIntegral q T) ^ n / (n.factorial : ℝ)
  have hb : Summable bound := (NormedSpace.expSeries_div_hasSum_exp
    (2 * actualCumulativeRealIntegral q T)).summable
  have hu : HasSumUniformlyOn (fun n t => genericRoughMatrixDysonTerm32 B n t i j)
      (fun t => ∑' n, genericRoughMatrixDysonTerm32 B n t i j) (Set.Icc (0 : ℝ) T) :=
    HasSumUniformlyOn.of_norm_le_summable hb
      (fun n t ht => genericRoughMatrixDysonTerm_uniform_bound32 B q T hq hqpos hmajorant n t ht i j)
  have hc := (hasSumUniformlyOn_iff_tendstoUniformlyOn).mp hu
  have hpart : ∀ s : Finset ℕ, ContinuousOn
      (fun t => ∑ n ∈ s, genericRoughMatrixDysonTerm32 B n t i j) (Set.Icc (0 : ℝ) T) :=
    fun s => continuousOn_finsetSum s
      (fun n _ => continuousOn_genericRoughMatrixDysonTerm32 B T hT hB n i j)
  simpa only [genericRoughMatrixDysonTsum32] using
    hc.continuousOn (Filter.Eventually.of_forall hpart).frequently

end NlsGge.SpectralFoundations
end
