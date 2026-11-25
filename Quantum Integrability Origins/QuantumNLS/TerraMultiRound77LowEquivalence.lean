import QuantumNLS.TerraMultiRound77MomentCriterion
import QuantumNLS.Reg010LowL4Correction

/-! Low fractional moment equivalence from the actual integrable correction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Reg010LowBasic
open QuantumNLS.TerraMultiRound77CorrectionIdentity QuantumNLS.TerraMultiRound77MomentCriterion
namespace QuantumNLS.TerraMultiRound77LowEquivalence

/-- Integrability of the printed correction transfers to the squared variable. -/
theorem squared_correction_integrable (s : ℝ) (F : ℝ → ℝ)
    (h : IntegrableOn (fun Y : ℝ => Y ^ (2*s-3) * F Y) (Ioi 0)) :
    IntegrableOn (fun t : ℝ => t ^ (s-2) * F (Real.sqrt t)) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_rpow_iff' (fun t : ℝ => t ^ (s-2) * F (Real.sqrt t))
    (p := 2) (by norm_num)).mp
  apply h.congr_fun _ measurableSet_Ioi
  intro Y hY
  simp only [smul_eq_mul, Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.sqrt_sq (le_of_lt hY)]
  have hp : (Y ^ 2) ^ (s-2) = Y ^ (2*(s-2)) := by
    rw [Real.rpow_mul hY.le, Real.rpow_two]
  rw [hp]
  have he : 1 + 2*(s-2) = 2*s-3 := by ring
  have hr := Real.rpow_add hY 1 (2*(s-2))
  rw [Real.rpow_one, he] at hr
  rw [hr]
  ring

/-- An absolutely integrable correction makes the physical and free moments
finite together, even when neither is known finite initially. -/
theorem physical_free_moment_iff_of_correction {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hc : IntegrableOn (fun Y : ℝ => Y ^ (2*s-3) * correction κ hκ u Y) (Ioi 0)) :
    Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L u) := by
  let μ := PhysicalQuantumMeasure.measure hκ u
  let ν := freeMeasure L u
  haveI : IsFiniteMeasure ν := free_finite u
  let A : ℝ → ℝ := fun t => ∫ x : ℝ, Real.rpowIntegrand₀₁ s t (x^2) ∂μ
  let B : ℝ → ℝ := fun t => ∫ x : ℝ, Real.rpowIntegrand₀₁ s t (x^2) ∂ν
  let G : ℝ → ℝ := fun t => t ^ (s-2) * correction κ hκ u (Real.sqrt t)
  have hG : Integrable G (volume.restrict (Ioi 0)) := squared_correction_integrable s _ hc
  have heq : G =ᵐ[volume.restrict (Ioi 0)] fun t => A t - B t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : (fun x : ℝ => Real.rpowIntegrand₀₁ s t (x^2)) =
        fun x => t ^ (s-2) * QuantumNLS.RootH1PositiveSpectral.kernel (Real.sqrt t) x := by
      funext x
      exact kernel_factor s t x hs0 hs1 ht
    dsimp [G, correction, A, B, μ, ν]
    rw [hp, integral_const_mul, integral_const_mul]
    ring
  have hdiff : Integrable (fun t => A t - B t) (volume.restrict (Ioi 0)) := hG.congr heq
  rw [← low_outer_integrable_iff μ s hs0 hs1, ← low_outer_integrable_iff ν s hs0 hs1]
  change Integrable A _ ↔ Integrable B _
  constructor
  · intro hA
    have hh := hA.sub hdiff
    convert hh using 1 <;> ext t <;> simp
  · intro hB
    have hh := hdiff.add hB
    convert hh using 1 <;> ext t <;> simp

/-- The all-L² low-order characterization, in the range where the existing
L² correction estimate applies. -/
theorem physical_free_moment_iff_L2 {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (s : ℝ) (hs0 : 0 < s) (hs : s < 1/2) :
    Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L u) := by
  exact physical_free_moment_iff_of_correction hκ u s hs0 (by linarith)
    (QuantumNLS.Reg010LowCorrection.weighted_correction_integrable κ hκ s hs0 hs u)

/-- Native L⁴ fields have the full low-order fractional equivalence. -/
theorem physical_free_moment_iff_L4 {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : QuantumNLS.Reg010LowL4Space.L4T L) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    Integrable (fun x : ℝ => |x| ^ (2*s))
      (PhysicalQuantumMeasure.measure hκ (QuantumNLS.Reg010LowL4Space.toL2 u)) ↔
    Integrable (fun x : ℝ => |x| ^ (2*s))
      (freeMeasure L (QuantumNLS.Reg010LowL4Space.toL2 u)) := by
  exact physical_free_moment_iff_of_correction hκ _ s hs0 hs1
    (QuantumNLS.Reg010LowL4Correction.weighted_correction_integrable κ hκ s hs0 hs1 u)

#print axioms squared_correction_integrable
#print axioms physical_free_moment_iff_of_correction
#print axioms physical_free_moment_iff_L2
#print axioms physical_free_moment_iff_L4
end QuantumNLS.TerraMultiRound77LowEquivalence
