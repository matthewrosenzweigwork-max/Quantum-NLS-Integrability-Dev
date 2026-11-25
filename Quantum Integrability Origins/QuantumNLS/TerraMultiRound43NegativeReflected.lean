import QuantumNLS.TerraMultiRound42SmoothPositive
import QuantumNLS.TerraMultiRound43ReflectionFixed
import QuantumNLS.TerraMultiRound43ReflectionPhysical

/-! All-order negative-height expansion for a reflected smooth field, with
coefficients displayed as reflected positive coefficients. Identifying these
with the printed recursion for the reflected field remains separate. -/
set_option autoImplicit false
noncomputable section
open Complex Finset
namespace QuantumNLS.TerraMultiRound43NegativeReflected
open QuantumNLS.ClassicalCharges QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiODEConverse QuantumNLS.RiccatiExpansions
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound42SmoothPositive QuantumNLS.TerraMultiRound43Reflection
open QuantumNLS.TerraMultiRound43ReflectionFixed QuantumNLS.TerraMultiRound43ReflectionPhysical

/-- For one Fourier representative and every order, the fixed point at `-Y`
for the reflected field has an explicit reflected all-order polynomial. -/
theorem smooth_negative_reflected_expansion (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (κ : ℝ) (f : ℝ → ℂ) (hf : SmoothPeriodic L f) :
    ∃ x : Ell2, physRep L a x = f ∧
      (∀ t : ℝ, physRep L a (reflectEll x) t = f (-t)) ∧
      ∀ M : ℕ, 1 ≤ M → ∃ B C : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y →
        ∃ (hY : 0 < Y) (r p : Ell2), ‖r‖ ≤ 2 * ‖reflectEll x‖ / Y ∧
          physicalT hLf.out ha (by simpa using (abs_pos.mpr hY.ne') : 0 < |-Y|)
            κ (reflectEll x) r = r ∧
          (∀ t : ℝ, physRep L a p t =
            -(∑ n ∈ Finset.Icc 1 M, aseq κ f n (-t) * ((Y : ℂ)⁻¹) ^ n)) ∧
          ‖r - p‖ ≤ C * (Y ^ (M + 1))⁻¹ := by
  obtain ⟨x, hx, hexp⟩ := smooth_positive_expansion L ha κ f hf
  refine ⟨x, hx, ?_, ?_⟩
  · intro t
    rw [physRep_reflect, hx]
  intro M hM
  obtain ⟨B, C, hB, hb⟩ := hexp M hM
  refine ⟨B, C, hB, ?_⟩
  intro Y hYB
  obtain ⟨hY, r, p, hrn, hr, hp, herr⟩ := hb Y hYB
  refine ⟨hY, -reflectEll r, -reflectEll p, ?_, ?_, ?_, ?_⟩
  · simpa [norm_reflectEll] using hrn
  · exact reflect_physical_fixed hLf.out ha (abs_pos.mpr hY.ne') κ x r hr
  · intro t
    rw [← neg_one_smul ℂ (reflectEll p), physRep_smul]
    simp only [Pi.smul_apply, neg_smul, one_smul]
    rw [physRep_reflect, hp]
  · have he : -reflectEll r - -reflectEll p = -reflectEll (r - p) := by
      rw [reflectEll_sub]
      abel
    rw [he, norm_neg, norm_reflectEll]
    exact herr

#print axioms smooth_negative_reflected_expansion
end QuantumNLS.TerraMultiRound43NegativeReflected
