import NlsGge.Spectral.ActualPhysicalL2ZsDysonIntegralEquationV2
import NlsGge.Spectral.ComplexIntervalIntegralPrimitiveAbsolutelyContinuousV2
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Actual rough L² Dyson entries are continuous, using the uniform factorial
bound on the closed doubled interval, not continuity of the coefficient. -/
theorem continuousOn_actualPhysicalL2ZsDysonTsum_entry
    (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    ContinuousOn (fun t => actualComplexZsDysonTsum
      (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      z t i j) (Set.Icc (0 : ℝ) 2) := by
  let U : ℝ → ℂ := fun s =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle)
  let B : ℕ → ℝ := fun n =>
    (2 * actualPhysicalL2ZsCumulativeMajorant u z 2) ^ n / (n.factorial : ℝ)
  have hB : Summable B := (NormedSpace.expSeries_div_hasSum_exp
    (2 * actualPhysicalL2ZsCumulativeMajorant u z 2)).summable
  have hunif : HasSumUniformlyOn
      (fun n t => actualComplexZsDysonTerm U z n t i j)
      (fun t => ∑' n, actualComplexZsDysonTerm U z n t i j) (Set.Icc (0 : ℝ) 2) :=
    HasSumUniformlyOn.of_norm_le_summable hB
      (fun n t ht => actualPhysicalL2ZsDysonTerm_entry_uniform_bound u z n t ht i j)
  have hconv := (hasSumUniformlyOn_iff_tendstoUniformlyOn).mp hunif
  have hpartial : ∀ s : Finset ℕ, ContinuousOn
      (fun t => ∑ n ∈ s, actualComplexZsDysonTerm U z n t i j)
      (Set.Icc (0 : ℝ) 2) := fun s =>
    continuousOn_finsetSum s (fun n _ => continuousOn_actualPhysicalL2ZsDysonTerm_entry u z n i j)
  have hc := hconv.continuousOn (Filter.Eventually.of_forall hpartial).frequently
  simpa only [actualComplexZsDysonTsum] using hc

/-- The actual product appearing in the rough Volterra equation is truly L¹. -/
theorem actualPhysicalL2ZsDysonProduct_intervalIntegrable
    (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    IntervalIntegrable (fun s => (zsCoefficientComplex
      (fun t => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (t : SpectralCircle)) z s *
      actualComplexZsDysonTsum
      (fun t => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (t : SpectralCircle)) z s) i j)
      volume 0 2 := by
  let U : ℝ → ℂ := fun t =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (t : SpectralCircle)
  have hA (k : Fin 2) := actualPhysicalL2ZsCoefficient_all_entries_intervalIntegrable u z i k
  have hX (k : Fin 2) : ContinuousOn
      (fun t => actualComplexZsDysonTsum U z t k j) (Set.uIcc (0 : ℝ) 2) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using
      continuousOn_actualPhysicalL2ZsDysonTsum_entry u z k j
  simpa only [U, actualPhysicalL2ZsCoefficient, Matrix.mul_apply, Fin.sum_univ_two] using
    ((hA 0).mul_continuousOn (hX 0)).add ((hA 1).mul_continuousOn (hX 1))

/-- Every actual complex entry is absolutely continuous on the true doubled
interval for each physical L² input; no continuous field representative is
added. Fundamental-solution uniqueness and spectral identification remain
separate obligations. -/
theorem absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry
    (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => actualComplexZsDysonTsum
      (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      z t i j) 0 2 := by
  let U : ℝ → ℂ := fun s =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle)
  let g : ℝ → ℂ := fun s =>
    (zsCoefficientComplex U z s * actualComplexZsDysonTsum U z s) i j
  have hg : IntervalIntegrable g volume 0 2 :=
    actualPhysicalL2ZsDysonProduct_intervalIntegrable u z i j
  have hprim := complex_intervalIntegral_primitive_absolutelyContinuousV2 hg
    (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 2)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) 0 2 :=
    contDiffOn_const.absolutelyContinuousOnInterval
  apply (hconst.add hprim).congr
  intro t ht
  have ht2 : t ∈ Set.Icc (0 : ℝ) 2 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  exact (actualPhysicalL2ZsDysonTsum_integral_equationV2 u z t ht2 i j).symm

theorem actualPhysicalL2ZsDysonTsum_initial_entry
    (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    actualComplexZsDysonTsum
      (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      z 0 i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  simpa only [intervalIntegral.integral_same, add_zero] using
    actualPhysicalL2ZsDysonTsum_integral_equationV2 u z 0
      ⟨le_rfl, by norm_num⟩ i j
end NlsGge.SpectralFoundations
end
