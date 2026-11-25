import Mathlib
import NlsGge.ThirdConsultation.M.M031Host
import NlsGge.ThirdConsultation.M.M021Host

   
                                                                                                                     

                                                                                                    
                                                                                              
                                                                                                             
                                                                                               
  

set_option autoImplicit false

noncomputable section

open NlsGge.GK38
open scoped ENNReal

namespace NlsGge.ThirdConsultation.M

theorem sourceH1Weight_pos (k : ℤ) : 0 < sourceH1Weight k := by
  unfold sourceH1Weight; positivity

theorem inv_sourceH1Weight_sq_le (k : ℤ) :
    1 / sourceH1Weight k ^ 2 ≤ (if k = 0 then 1 else 0) + (1 / 9) * (1 / (k : ℝ) ^ 2) := by
  by_cases hk : k = 0
  · subst hk; simp [sourceH1Weight]
  · rw [if_neg hk, zero_add]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have ha : 0 < |(k : ℝ)| := abs_pos.mpr hk'
    have hw : 9 * (k : ℝ) ^ 2 ≤ sourceH1Weight k ^ 2 := by
      unfold sourceH1Weight
      rw [abs_mul, abs_of_pos Real.pi_pos, ← sq_abs (k : ℝ)]
      have h1 : 3 * |(k : ℝ)| ≤ Real.pi * |(k : ℝ)| := by nlinarith
      nlinarith
    rw [show (1 / 9 : ℝ) * (1 / (k : ℝ) ^ 2) = 1 / (9 * (k : ℝ) ^ 2) by field_simp]
    exact one_div_le_one_div_of_le (by positivity) hw

theorem hasSum_inv_sq_int : HasSum (fun k : ℤ => 1 / (k : ℝ) ^ 2) (Real.pi ^ 2 / 3) := by
  have h1 : HasSum (fun n : ℕ => 1 / ((n : ℤ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    simpa only [Int.cast_natCast] using hasSum_zeta_two
  have h2' := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
  have e : ∑ i ∈ Finset.range 1, (1 : ℝ) / (i : ℝ) ^ 2 = 0 := by simp
  rw [e, sub_zero] at h2'
  have hf : (fun n : ℕ => 1 / ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) =
      (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ)) : ℝ) ^ 2) := by
    funext n
    push_cast
    ring
  have h2 : HasSum (fun n : ℕ => 1 / ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    rw [hf]
    exact h2'
  have h3 := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => 1 / (k : ℝ) ^ 2) h1 h2
  rwa [show Real.pi ^ 2 / 6 + Real.pi ^ 2 / 6 = Real.pi ^ 2 / 3 by ring] at h3

theorem inv_sourceH1Weight_sq_summable :
    Summable (fun k : ℤ => 1 / sourceH1Weight k ^ 2) ∧
      ∑' k : ℤ, 1 / sourceH1Weight k ^ 2 ≤ 2 := by
  have hD : HasSum (fun k : ℤ => (if k = 0 then (1 : ℝ) else 0) + (1 / 9) * (1 / (k : ℝ) ^ 2))
      (1 + (1 / 9) * (Real.pi ^ 2 / 3)) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).add (hasSum_inv_sq_int.mul_left (1 / 9))
  have hs : Summable (fun k : ℤ => 1 / sourceH1Weight k ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by have := sourceH1Weight_pos k; positivity)
      inv_sourceH1Weight_sq_le hD.summable
  refine ⟨hs, ?_⟩
  have hle := hs.tsum_le_tsum inv_sourceH1Weight_sq_le hD.summable
  rw [hD.tsum_eq] at hle
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem amgm_weight (a w t : ℝ) (hw : 0 < w) (ht : 0 < t) :
    a ≤ 1 / (w ^ 2 * (2 * t)) + t / 2 * (w ^ 2 * a ^ 2) := by
  have h : 1 / (w ^ 2 * (2 * t)) + t / 2 * (w ^ 2 * a ^ 2) - a =
      (t * w ^ 2 * a - 1) ^ 2 / (2 * t * w ^ 2) := by
    field_simp
    ring
  have h2 : 0 ≤ (t * w ^ 2 * a - 1) ^ 2 / (2 * t * w ^ 2) := by positivity
  linarith

/-- Pro round 14 M-031 support E4. -/
theorem coefficient_l1_le (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy sourceH1Weight φ ≠ ⊤) :
    (∀ b : Bool, Summable (fun k : ℤ => ‖MTwoMode.potentialCoefficientPair φ b k‖)) ∧
    (∑' k : ℤ, ‖MTwoMode.potentialCoefficientPair φ true k‖) +
      (∑' k : ℤ, ‖MTwoMode.potentialCoefficientPair φ false k‖) ≤
        2 * MTwoMode.potentialCoefficientNorm sourceH1Weight φ := by
  set c : Bool → ℤ → ℝ := fun b k => ‖MTwoMode.potentialCoefficientPair φ b k‖ with hc
  set g : ℤ → ℝ := fun k => sourceH1Weight k ^ 2 * (c true k ^ 2 + c false k ^ 2) with hgdef
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  have hg : Summable g := by
    refine (ENNReal.summable_toReal hφ).congr (fun k => ?_)
    exact ENNReal.toReal_ofReal (hg0 k)
  have hQ : MTwoMode.potentialCoefficientNorm sourceH1Weight φ ^ 2 = ∑' k, g k := by
    unfold MTwoMode.potentialCoefficientNorm
    rw [Real.sq_sqrt ENNReal.toReal_nonneg]
    unfold MTwoMode.potentialCoefficientEnergy
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun k => ENNReal.toReal_ofReal (hg0 k))
  obtain ⟨hS, hS2⟩ := inv_sourceH1Weight_sq_summable
  have hcb : ∀ b, ∀ k, sourceH1Weight k ^ 2 * c b k ^ 2 ≤ g k := by
    intro b k
    have hw := sourceH1Weight_pos k
    cases b
    · show _ ≤ sourceH1Weight k ^ 2 * (c true k ^ 2 + c false k ^ 2)
      nlinarith [sq_nonneg (c true k), sq_nonneg (sourceH1Weight k)]
    · show _ ≤ sourceH1Weight k ^ 2 * (c true k ^ 2 + c false k ^ 2)
      nlinarith [sq_nonneg (c false k), sq_nonneg (sourceH1Weight k)]
  have hsum : ∀ b, Summable (c b) := by
    intro b
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hS.add hg)
    have hw := sourceH1Weight_pos k
    have h := amgm_weight (c b k) (sourceH1Weight k) 1 hw one_pos
    have h1 : 1 / (sourceH1Weight k ^ 2 * (2 * 1)) ≤ 1 / sourceH1Weight k ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg (sourceH1Weight k)])
    have h2 := hcb b k
    have h3 : 0 ≤ sourceH1Weight k ^ 2 * c b k ^ 2 := by positivity
    linarith
  refine ⟨hsum, ?_⟩
  set Q := MTwoMode.potentialCoefficientNorm sourceH1Weight φ with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  -- the bound for every t > 0
  have hT : ∀ t : ℝ, 0 < t → (∑' k, c true k) + (∑' k, c false k) ≤ 2 / t + t / 2 * Q ^ 2 := by
    intro t ht
    have hpt : ∀ k, c true k + c false k ≤ 1 / sourceH1Weight k ^ 2 / t + t / 2 * g k := by
      intro k
      have hw := sourceH1Weight_pos k
      have h1 := amgm_weight (c true k) (sourceH1Weight k) t hw ht
      have h2 := amgm_weight (c false k) (sourceH1Weight k) t hw ht
      have he : 1 / sourceH1Weight k ^ 2 / t =
          1 / (sourceH1Weight k ^ 2 * (2 * t)) + 1 / (sourceH1Weight k ^ 2 * (2 * t)) := by
        field_simp
        ring
      rw [he]
      show _ ≤ _ + t / 2 * (sourceH1Weight k ^ 2 * (c true k ^ 2 + c false k ^ 2))
      nlinarith
    have hR : Summable (fun k => 1 / sourceH1Weight k ^ 2 / t + t / 2 * g k) :=
      (hS.div_const t).add (hg.mul_left (t / 2))
    rw [← (hsum true).tsum_add (hsum false)]
    calc ∑' k, (c true k + c false k)
        ≤ ∑' k, (1 / sourceH1Weight k ^ 2 / t + t / 2 * g k) :=
          ((hsum true).add (hsum false)).tsum_le_tsum hpt hR
      _ = (∑' k, 1 / sourceH1Weight k ^ 2) / t + t / 2 * ∑' k, g k := by
          rw [(hS.div_const t).tsum_add (hg.mul_left (t / 2)), tsum_div_const, tsum_mul_left]
      _ ≤ 2 / t + t / 2 * Q ^ 2 := by
          rw [hQ]
          gcongr
  rcases hQ0.lt_or_eq with hpos | hzero
  · have h := hT (2 / Q) (by positivity)
    have e1 : 2 / (2 / Q) = Q := by field_simp
    have e2 : 2 / Q / 2 * Q ^ 2 = Q := by field_simp
    rw [e1, e2] at h
    linarith
  · rw [← hzero, mul_zero]
    apply le_of_forall_pos_lt_add
    intro ε hε
    have h := hT (4 / ε) (by positivity)
    rw [← hzero] at h
    have e1 : 2 / (4 / ε) = ε / 2 := by field_simp; ring
    rw [e1] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h
    linarith

end NlsGge.ThirdConsultation.M

end
