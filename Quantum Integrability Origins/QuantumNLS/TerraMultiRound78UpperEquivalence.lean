import QuantumNLS.TerraMultiRound78UpperCriterion
import QuantumNLS.TerraMultiRound78UpperPhysical
import QuantumNLS.TerraMultiRound77LowEquivalence

/-! Finiteness equivalence in the upper range on H¹ fields. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound78UpperIdentity QuantumNLS.TerraMultiRound78UpperCriterion
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound64FieldIdentity
open QuantumNLS.TerraMultiRound64FreeSobolev QuantumNLS.Reg014Moments
open QuantumNLS.TerraMultiRound77LowEquivalence QuantumNLS.TerraMultiRound75Correction
namespace QuantumNLS.TerraMultiRound78UpperEquivalence

variable {L : ℝ} [Fact (0 < L)]

theorem physical_free_upper_iff (κ : ℝ) (hκ : 0 < κ) (u : Hk L 1)
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u.val) ↔
    Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L u.val) := by
  let μ := PhysicalQuantumMeasure.measure hκ u.val
  let ν := freeMeasure L u.val
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  have hu := representative_hsq (L := L) 1 u
  have hμ2 : Integrable (fun x : ℝ => x^2) μ := by
    simpa [μ] using physical_moment_integrable κ hκ 1 (by omega) u.val hu
  have hν2 : Integrable (fun x : ℝ => x^2) ν := by
    simpa [ν] using (free_even_integrable_iff_hsq u.val 1).mpr hu
  let A : ℝ → ℝ := fun t => ∫ x : ℝ, x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2) ∂μ
  let B : ℝ → ℝ := fun t => ∫ x : ℝ, x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2) ∂ν
  let G : ℝ → ℝ := fun t => t ^ (s-3) * Dfun κ hκ 2 u.val (Real.sqrt t)
  have hc := correction_integrable κ hκ s hs1 hs2 u
  have hG : Integrable G (volume.restrict (Ioi 0)) := by
    have hh := squared_correction_integrable (s-1) (Dfun κ hκ 2 u.val) (by
      simpa only [show 2*(s-1)-3 = 2*s-5 by ring] using hc)
    change IntegrableOn (fun t : ℝ => t ^ (s-3) * Dfun κ hκ 2 u.val (Real.sqrt t)) (Ioi 0)
    simpa only [show s-1-2 = s-3 by ring] using hh
  have heq : G =ᵐ[volume.restrict (Ioi 0)] fun t => A t - B t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : (fun x : ℝ => x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)) =
        fun x => t ^ (s-3) * kernel 2 (Real.sqrt t) x := by
      funext x
      exact upper_kernel_factor s t x hs1 hs2 ht
    dsimp [G, A, B, μ, ν]
    rw [hp, integral_const_mul, integral_const_mul,
      free_kernel_sum (Real.sqrt_pos.2 ht) u.val 1 (by simpa using hν2)]
    simp only [Dfun, kernel, Nat.reduceMul, Nat.reduceAdd]
    ring
  have hdiff : Integrable (fun t => A t - B t) (volume.restrict (Ioi 0)) := hG.congr heq
  rw [← upper_outer_integrable_iff μ s hs1 hs2 hμ2, ← upper_outer_integrable_iff ν s hs1 hs2 hν2]
  change Integrable A _ ↔ Integrable B _
  constructor
  · intro hA
    have hh := hA.sub hdiff
    convert hh using 1 <;> ext t <;> simp
  · intro hB
    have hh := hdiff.add hB
    convert hh using 1 <;> ext t <;> simp

#print axioms physical_free_upper_iff
end QuantumNLS.TerraMultiRound78UpperEquivalence
