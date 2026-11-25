import QuantumNLS.TerraMultiRound43NegativeReflected
import QuantumNLS.TerraMultiRound43CoefficientReflection

/-! The all-order negative-height expansion with the literal printed recursion. -/
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
open Complex Finset
namespace QuantumNLS.TerraMultiRound43NegativeExpansion
open QuantumNLS.ClassicalCharges QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound43Reflection
open QuantumNLS.TerraMultiRound43NegativeReflected QuantumNLS.TerraMultiRound43CoefficientReflection

theorem negative_polynomial {L κ Y : ℝ} {f : ℝ → ℂ} (hf : SmoothPeriodic L f)
    (M : ℕ) (t : ℝ) :
    -(∑ n ∈ Finset.Icc 1 M, aseq κ (fun s => f (-s)) n (-t) * ((Y : ℂ)⁻¹) ^ n) =
      ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * (((-Y : ℝ) : ℂ)⁻¹) ^ n := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := (Finset.mem_Icc.mp hn).1
  have hc := congrFun (aseq_reflect (κ := κ) hf n hn') (-t)
  simp only [neg_neg] at hc
  rw [hc]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one, Complex.ofReal_neg, inv_neg]
  rw [show (-((Y : ℂ)⁻¹)) ^ (m + 1) = (-1 : ℂ) ^ (m + 1) * ((Y : ℂ)⁻¹) ^ (m + 1) from neg_pow _ _]
  rw [pow_succ (-1 : ℂ) m, pow_succ ((Y : ℂ)⁻¹) m]
  ring

/-- For a single Fourier representative of any smooth periodic field and any
finite order, its negative signed fixed point has the printed physical
polynomial and an `O(Y^(-M-1))` weighted Fourier-norm remainder. -/
theorem smooth_negative_expansion (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (κ : ℝ) (f : ℝ → ℂ) (hf : SmoothPeriodic L f) :
    ∃ x : Ell2, physRep L a x = f ∧
      ∀ M : ℕ, 1 ≤ M → ∃ B C : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y →
        ∃ (hY : 0 < Y) (r p : Ell2), ‖r‖ ≤ 2 * ‖x‖ / Y ∧
          physicalT hLf.out ha (by simpa using (abs_pos.mpr hY.ne') : 0 < |-Y|)
            κ x r = r ∧
          (∀ t : ℝ, physRep L a p t =
            ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * (((-Y : ℝ) : ℂ)⁻¹) ^ n) ∧
          ‖r - p‖ ≤ C * (Y ^ (M + 1))⁻¹ := by
  obtain ⟨x, _, hx, hexp⟩ := smooth_negative_reflected_expansion L ha κ
    (fun t => f (-t)) (smooth_reflect hf)
  refine ⟨reflectEll x, ?_, ?_⟩
  · funext t
    simpa using hx t
  intro M hM
  obtain ⟨B, C, hB, hrest⟩ := hexp M hM
  refine ⟨B, C, hB, ?_⟩
  intro Y hYB
  obtain ⟨hY, r, p, hrn, hr, hp, herr⟩ := hrest Y hYB
  refine ⟨hY, r, p, hrn, hr, ?_, herr⟩
  intro t
  exact (hp t).trans (negative_polynomial hf M t)

#print axioms negative_polynomial
#print axioms smooth_negative_expansion
end QuantumNLS.TerraMultiRound43NegativeExpansion
