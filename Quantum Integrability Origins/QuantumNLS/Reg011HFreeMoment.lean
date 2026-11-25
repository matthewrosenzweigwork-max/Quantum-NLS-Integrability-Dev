import QuantumNLS.Reg010LowPrinted
import QuantumNLS.Reg010LowCorrection
import QuantumNLS.TerraMultiRound76PhysicalKernels

/-! REG-011 GAP B (haiku_inventory, module Reg011HFreeMoment).
Free-moment passage for 0 < s < 1/2: the free-measure power moment of order 2s is the
Fourier-weighted sum Σ_n |momentum n|^{2s} ‖û(n)‖² (a Plancherel-type identity, lintegral
source `free_fourier_power_moment`); the physical-to-free passage is the frozen identity
`all_L2_fractional_identity` with the frozen continuous correction `J_continuous`. Hence the
free-moment sums converge along any L²-convergent sequence whose physical 2s-moments converge.
Read-only imports of the frozen round-46 REG-010 modules Reg010LowPrinted and Reg010LowCorrection
(the REG-010 chain is pending review, so every result here is conditional on it), and of the
frozen round-76 module TerraMultiRound76PhysicalKernels. No review record unfrozen module. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Fourier QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.Reg011HFreeMoment

variable {L : ℝ} [Fact (0 < L)]

/-- The free-measure power moment of order p is the weighted Fourier sum
Σ_n |momentum n|^p ‖û(n)‖². No integrability hypothesis is needed: both sides are
the Bochner value of a nonnegative function, through the lintegral identity. -/
theorem free_moment_eq_tsum (u : L2T L) (p : ℝ) :
    ∫ t : ℝ, |t| ^ p ∂(QuantumNLS.FreeLimit.freeMeasure L u) =
      ∑' n : ℤ, |momentum L n| ^ p * ‖fourierL2 L u n‖ ^ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun t => by positivity))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  rw [QuantumNLS.TerraMultiRound76PhysicalKernels.free_fourier_power_moment u p,
    ENNReal.tsum_toReal_eq (fun n => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  refine tsum_congr (fun n => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    fourierL2_apply]
  ring

/-- Physical-to-free passage at order 2s, 0 < s < 1/2, for a physically integrable power:
the free moment is the physical moment minus the frozen correction J. -/
theorem free_eq_phys_sub_J (κ : ℝ) (hκ : 0 < κ) (u : L2T L) (s : ℝ) (hs : 0 < s) (hs' : s < 1 / 2)
    (hm : Integrable (fun x : ℝ => |x| ^ (2 * s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) :
    ∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L u) =
      (∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
        QuantumNLS.Reg010LowCorrection.J κ hκ s u := by
  have h := QuantumNLS.Reg010LowPrinted.all_L2_fractional_identity κ hκ u s hs hs' hm
  linarith

/-- **GAP B (free-moment passage).** If u_j → u in L² and the physical 2s-moments of the u_j
converge to that of u (0 < s < 1/2), then the free Fourier sums Σ_n |momentum n|^{2s} ‖û_j(n)‖²
converge to Σ_n |momentum n|^{2s} ‖û(n)‖². -/
theorem free_moment_tendsto (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs : 0 < s) (hs' : s < 1 / 2)
    (x : ℕ → L2T L) (y : L2T L) (hx : Tendsto x atTop (𝓝 y))
    (hxm : ∀ j, Integrable (fun t : ℝ => |t| ^ (2 * s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ (x j)))
    (hym : Integrable (fun t : ℝ => |t| ^ (2 * s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ y))
    (hphys : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (x j)))
      atTop (𝓝 (∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ y)))) :
    Tendsto (fun j => ∑' n : ℤ, |momentum L n| ^ (2 * s) * ‖fourierL2 L (x j) n‖ ^ 2) atTop
      (𝓝 (∑' n : ℤ, |momentum L n| ^ (2 * s) * ‖fourierL2 L y n‖ ^ 2)) := by
  have hJ : Tendsto (fun j => QuantumNLS.Reg010LowCorrection.J κ hκ s (x j)) atTop
      (𝓝 (QuantumNLS.Reg010LowCorrection.J κ hκ s y)) :=
    ((QuantumNLS.Reg010LowCorrection.J_continuous (L := L) κ hκ s hs hs').tendsto y).comp hx
  have hfree : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L (x j))) atTop
      (𝓝 (∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L y))) := by
    rw [free_eq_phys_sub_J κ hκ y s hs hs' hym]
    exact (hphys.sub hJ).congr (fun j => (free_eq_phys_sub_J κ hκ (x j) s hs hs' (hxm j)).symm)
  simp only [free_moment_eq_tsum] at hfree
  exact hfree

#print axioms free_moment_eq_tsum
#print axioms free_eq_phys_sub_J
#print axioms free_moment_tendsto
end QuantumNLS.Reg011HFreeMoment
