import NlsGge.Spectral.ActualPhysicalL2ZsDysonContinuousAndACV1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual rough-L² Dyson series satisfies the ZS system almost everywhere
on the doubled interval. Endpoint null sets are explicit; no pointwise
continuity of the field is assumed. This does not assert uniqueness or spectral
identification. -/
theorem actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry
    (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z s i j)
        ((zsCoefficientComplex
          (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z t *
          actualComplexZsDysonTsum
            (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
            z t) i j) t := by
  let U : ℝ → ℂ := fun x =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)
  let g : ℝ → ℂ := fun t =>
    (zsCoefficientComplex U z t * actualComplexZsDysonTsum U z t) i j
  have hg : IntervalIntegrable g volume 0 2 :=
    actualPhysicalL2ZsDysonProduct_intervalIntegrable u z i j
  have h0 : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  have h2 : ∀ᵐ t ∂volume, t ≠ (2 : ℝ) := by simp [ae_iff, measure_singleton]
  filter_upwards [hg.ae_hasDerivAt_integral, h0, h2] with t ht ht0 ht2
  intro hmem
  have hcc : t ∈ Set.Icc (0 : ℝ) 2 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hmem
  have hlo : (0 : ℝ) < t := lt_of_le_of_ne hcc.1 (Ne.symm ht0)
  have hhi : t < (2 : ℝ) := lt_of_le_of_ne hcc.2 ht2
  have hd := (ht hmem 0 (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 2)).const_add
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlo hhi] with s hs
  exact actualPhysicalL2ZsDysonTsum_integral_equationV2 u z s
    ⟨hs.1.le, hs.2.le⟩ i j
end NlsGge.SpectralFoundations
end
