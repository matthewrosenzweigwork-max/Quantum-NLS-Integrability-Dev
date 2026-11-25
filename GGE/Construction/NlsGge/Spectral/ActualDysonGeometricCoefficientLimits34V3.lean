import NlsGge.Schur.SourceInterval
import NlsGge.Definitions.PilotInterfaces
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot

/-- The concrete coefficient from both actual geometric Dyson bounds tends
to zero. No algebraic square-root rewrite or extra regularity is assumed. -/
theorem actualDysonGeometricCoefficient_tendsto_zero34 (u : PhysicalL2) :
    Tendsto (fun Y : ℝ => ‖u‖*Real.sqrt (‖u‖^2/(4*Y))) atTop (𝓝 0) := by
  have hden : Tendsto (fun Y : ℝ => 4*Y) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) tendsto_id
  have hnum : Tendsto (fun Y : ℝ => ‖u‖^2) atTop (𝓝 (‖u‖^2)) :=
    tendsto_const_nhds
  have hs := (hnum.div_atTop hden).sqrt
  simpa only [Real.sqrt_zero, mul_zero] using hs.const_mul ‖u‖

/-- The tail coefficient is used only eventually, when its denominator is
positive. Its limit is obtained at the nonzero limiting denominator one. -/
theorem actualDysonGeometricTailCoefficient_tendsto_zero34 (u : PhysicalL2) :
    Tendsto (fun Y : ℝ => (‖u‖*Real.sqrt (‖u‖^2/(4*Y)))/
      (1-‖u‖*Real.sqrt (‖u‖^2/(4*Y)))) atTop (𝓝 0) := by
  have h := actualDysonGeometricCoefficient_tendsto_zero34 u
  simpa only [Pi.div_def, Pi.sub_def, zero_div, sub_zero] using h.div (tendsto_const_nhds.sub h) (by norm_num : (1 : ℝ)-0 ≠ 0)

/-- Actual coefficient smallness and positive imaginary height both hold on
one tail of the original real parameter, including the zero potential. -/
theorem actualDysonGeometricCoefficient_eventually_small34 (u : PhysicalL2) :
    ∀ᶠ Y : ℝ in atTop, 0 < Y ∧ ‖u‖*Real.sqrt (‖u‖^2/(4*Y)) < 1 := by
  exact (eventually_gt_atTop (0 : ℝ)).and
    ((actualDysonGeometricCoefficient_tendsto_zero34 u).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))

/-- The weighted11 zeroth term vanishes on the same upper imaginary ray. -/
theorem actualDysonScaled11Base_tendsto_zero34 :
    Tendsto (fun Y : ℝ => (Real.exp (-2*Y) : ℂ)) atTop (𝓝 0) := by
  have hden : Tendsto (fun Y : ℝ => 2*Y) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  have he : Tendsto (fun Y : ℝ => Real.exp (-2*Y)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hden
  simpa only [Function.comp_def, Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp he

end NlsGge.SpectralFoundations
end
