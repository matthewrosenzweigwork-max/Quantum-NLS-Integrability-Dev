import Mathlib
import NlsGge.Hierarchy.UniformPartitionBoundAux38
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                                                                    
                                                                                                                                             
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Measure
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.S

theorem reservedRate_deficits_summable :
    ∃ L : ℝ, 0 < L ∧ ∀ (lo up : ℝ) (c : BoundedCoefficients lo up),
      let a := fun n : ℤ => fullWeightRate c.val n
      let b := reservedRateV6 c
      let ε := shiftEps38 lo up
      Summable (fun n : ℤ => ε * b n / a n) ∧
      (∑' n : ℤ, ε * b n / a n) ≤ L ∧
      (∀ n : ℤ, 0 ≤ ε * b n / a n ∧ ε * b n / a n ≤ (1 / 4 : ℝ)) ∧
      (∀ n : ℤ, n ≠ 0 → b n / a n ≤ (2 * Real.pi * (n : ℝ))⁻¹ ^ 2) ∧
      b 0 / a 0 = NlsGge.coefficient c.val 1 / NlsGge.coefficient c.val 0 ∧
      b 0 / a 0 ≤ up / lo := by
  refine ⟨∑' m : ℤ, modeBound38 m, ?_, fun lo up c => ?_⟩
  · exact modeBound38_summable.tsum_pos modeBound38_nonneg 0 (by norm_num [modeBound38])
  intro a b ε
  have hkey : ∀ n : ℤ, ε * b n / a n = modeT38 c (2 * Real.pi * (n : ℝ)) := fun n => rfl
  have hnn : ∀ n : ℤ, 0 ≤ ε * b n / a n := fun n => by
    rw [hkey n]; exact modeT38_nonneg c _
  have hle : ∀ n : ℤ, ε * b n / a n ≤ modeBound38 n := fun n => by
    rw [hkey n]; exact modeT38_le_bound c n
  have hle4 : ∀ n : ℤ, ε * b n / a n ≤ (1 / 4 : ℝ) := fun n => by
    rw [hkey n]; exact modeT38_le c _
  have hsum : Summable (fun n : ℤ => ε * b n / a n) :=
    Summable.of_nonneg_of_le hnn hle modeBound38_summable
  have hb0 : b 0 = NlsGge.coefficient c.val 1 := by
    show reservedRateV6 c 0 = _
    unfold reservedRateV6 lowerWeightV6
    simp only [Int.cast_zero, mul_zero]
    rw [tsum_eq_single 0]
    · simp
    · intro j hj
      rw [zero_pow (by omega : 2 * j ≠ 0), mul_zero]
  have ha0 : a 0 = NlsGge.coefficient c.val 0 := by
    have h := sq_mul_reservedSymbol38 c 0
    have hz : 2 * Real.pi * ((0 : ℤ) : ℝ) = 0 := by simp
    have h0 : (0 : ℝ) ^ 2 * reservedSymbol38 c.val 0 = 0 := by ring
    show fullWeightRate c.val 0 = _
    unfold fullWeightRate
    rw [hz]
    linarith
  have hc0pos : 0 < NlsGge.coefficient c.val 0 := by
    have e : NlsGge.coefficient c.val 0 = c.val 0 := by
      unfold NlsGge.coefficient; simp
    have h := (c.property.2.2 0).1
    have hl := c.property.1
    rw [e]; linarith
  have hratio : NlsGge.coefficient c.val 1 / NlsGge.coefficient c.val 0 ≤ up / lo := by
    rw [div_le_iff₀ hc0pos]
    exact NlsGge.Weights.coefficient_succ_le38 lo up c.val c.property.1
      (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) 0
  refine ⟨hsum, ?_, fun n => ⟨hnn n, hle4 n⟩, ?_, ?_, ?_⟩
  · exact hsum.tsum_le_tsum hle modeBound38_summable
  · intro n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hr : 2 * Real.pi * (n : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn'
    have hr2 : 0 < (2 * Real.pi * (n : ℝ)) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hr))
    have hW := weight_pos_c38 c (2 * Real.pi * (n : ℝ))
    have hs := sq_mul_reservedSymbol38 c (2 * Real.pi * (n : ℝ))
    have hc0 := coefficient_nonneg_c38 c 0
    show reservedSymbol38 c.val (2 * Real.pi * (n : ℝ)) /
        NlsGge.Weights.weight c.val (2 * Real.pi * (n : ℝ)) ≤ (2 * Real.pi * (n : ℝ))⁻¹ ^ 2
    have key : (2 * Real.pi * (n : ℝ))⁻¹ ^ 2 * NlsGge.Weights.weight c.val (2 * Real.pi * (n : ℝ)) =
        NlsGge.Weights.weight c.val (2 * Real.pi * (n : ℝ)) / (2 * Real.pi * (n : ℝ)) ^ 2 := by
      ring
    have hs' : reservedSymbol38 c.val (2 * Real.pi * (n : ℝ)) * (2 * Real.pi * (n : ℝ)) ^ 2 =
        NlsGge.Weights.weight c.val (2 * Real.pi * (n : ℝ)) - NlsGge.coefficient c.val 0 := by
      rw [← hs]; ring
    rw [div_le_iff₀ hW, key, le_div_iff₀ hr2]
    linarith
  · rw [hb0, ha0]
  · rw [hb0, ha0]; exact hratio

end NlsGge.ThirdConsultation.S

end
