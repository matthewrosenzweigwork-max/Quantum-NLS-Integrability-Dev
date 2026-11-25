import Mathlib
import NlsGge.Birkhoff.W12Tilt38

                                                                                                                  
                                                                                                                 

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.ThirdConsultation.T

def WeightClass (lo up : ℝ) (W : ℕ → ℝ) : Prop :=
  0 < lo ∧ lo ≤ up ∧ ∀ j : ℕ, lo ≤ W j ∧ W j ≤ up

theorem bCoef_bounds {cMinus cPlus : ℝ} {W : ℕ → ℝ} (hW : WeightClass cMinus cPlus W) (j : ℕ) :
    0 ≤ NlsGge.Birkhoff.bCoef38 W j ∧ NlsGge.Birkhoff.bCoef38 W j ≤ cPlus := by
  unfold WeightClass at hW
  obtain ⟨hpos, _, hbd⟩ := hW
  have hq : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast Nat.succ_pos j)
  have hq0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ 4 := by linarith
  have hn : 0 ≤ W (j + 1) := le_trans hpos.le (hbd (j + 1)).1
  unfold NlsGge.Birkhoff.bCoef38
  constructor
  · exact div_nonneg hn hq0.le
  · calc W (j + 1) / ((j + 1 : ℕ) : ℝ) ^ 4 ≤ W (j + 1) := div_le_self hn hq
      _ ≤ cPlus := (hbd (j + 1)).2

theorem beta_succ_le {cMinus cPlus : ℝ} {W : ℕ → ℝ} (hW : WeightClass cMinus cPlus W) (j : ℕ) :
    NlsGge.coefficient W (j + 1) ≤ (cPlus / cMinus) * NlsGge.coefficient W j := by
  have hW0 := hW
  unfold WeightClass at hW0
  have hcM : 0 < cMinus := hW0.1
  have hcP : 0 ≤ cPlus := le_trans hcM.le (le_trans hW0.2.1 le_rfl)
  have hWj : cMinus ≤ W j := (hW0.2.2 j).1
  have hF : (0 : ℝ) < (Nat.factorial j : ℝ) ^ 4 := by positivity
  have e1 : NlsGge.coefficient W (j + 1) = NlsGge.Birkhoff.bCoef38 W j / (Nat.factorial j : ℝ) ^ 4 :=
    (NlsGge.Birkhoff.coefficient_bCoef38 W j).symm
  have e0 : NlsGge.coefficient W j = W j / (Nat.factorial j : ℝ) ^ 4 := rfl
  have hb2 := (bCoef_bounds hW j).2
  rw [e1, e0]
  calc NlsGge.Birkhoff.bCoef38 W j / (Nat.factorial j : ℝ) ^ 4
      ≤ cPlus / (Nat.factorial j : ℝ) ^ 4 := div_le_div_of_nonneg_right hb2 hF.le
    _ ≤ (cPlus / cMinus) * (W j / (Nat.factorial j : ℝ) ^ 4) := by
        rw [div_mul_div_comm, div_le_div_iff₀ hF (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hcP hF.le) (sub_nonneg.2 hWj)]

theorem ratio_le {cMinus cPlus : ℝ} {W : ℕ → ℝ} (hW : WeightClass cMinus cPlus W) (j : ℕ) :
    NlsGge.coefficient W (j + 1) / NlsGge.coefficient W j ≤
      (cPlus / cMinus) / (((j + 1 : ℕ) : ℝ) ^ 4) := by
  have hW0 := hW
  unfold WeightClass at hW0
  have hcM : 0 < cMinus := hW0.1
  have hWj : cMinus ≤ W j := (hW0.2.2 j).1
  have hWjpos : 0 < W j := lt_of_lt_of_le hcM hWj
  have hF : (0 : ℝ) < (Nat.factorial j : ℝ) ^ 4 := by positivity
  have hq0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
    positivity
  have e1 : NlsGge.coefficient W (j + 1) = NlsGge.Birkhoff.bCoef38 W j / (Nat.factorial j : ℝ) ^ 4 :=
    (NlsGge.Birkhoff.coefficient_bCoef38 W j).symm
  have e0 : NlsGge.coefficient W j = W j / (Nat.factorial j : ℝ) ^ 4 := rfl
  have hcp : cPlus = (cPlus / cMinus) * cMinus := by field_simp
  rw [e1, e0, div_div_div_cancel_right₀ hF.ne']
  unfold NlsGge.Birkhoff.bCoef38
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hW1 : W (j + 1) ≤ cPlus := (hW0.2.2 (j + 1)).2
  have hcP0 : 0 ≤ cPlus := le_trans hcM.le (le_trans hW0.2.1 le_rfl)
  have h1 : W (j + 1) * cMinus ≤ cPlus * W j :=
    mul_le_mul hW1 hWj hcM.le hcP0
  nlinarith [mul_le_mul_of_nonneg_right h1 hq0.le]

theorem margin_core {cMinus cPlus : ℝ} {W : ℕ → ℝ} (hW : WeightClass cMinus cPlus W) (δ : ℝ)
    (hδ : 0 ≤ δ) (j : ℕ) :
    (1 - δ * (cPlus / cMinus)) * NlsGge.coefficient W j ≤
      NlsGge.coefficient (NlsGge.Birkhoff.tiltCoef38 W δ) j := by
  rw [NlsGge.Birkhoff.coefficient_tiltCoef38, NlsGge.Birkhoff.coefficient_bCoef38]
  have hb0 : 0 ≤ NlsGge.coefficient W j := by
    have hW0 := hW
    unfold WeightClass at hW0
    have hWj : 0 < W j := lt_of_lt_of_le hW0.1 (hW0.2.2 j).1
    unfold NlsGge.coefficient
    positivity
  have hs := beta_succ_le hW j
  have hmul := mul_le_mul_of_nonneg_left hs hδ
  nlinarith [hmul]

theorem lowerWeightTilt_weightClass
    (cMinus cPlus : ℝ) (W : ℕ → ℝ) (delta : ℝ)
    (hW : WeightClass cMinus cPlus W)
    (hdelta : 0 < delta ∧ delta < cMinus / (4 * cPlus)) :
    WeightClass (3 * cMinus / 4) cPlus
      (fun j : ℕ => W j - delta * NlsGge.Birkhoff.bCoef38 W j) := by
  have hW0 := hW
  unfold WeightClass at hW0
  obtain ⟨hcM, hle, _⟩ := hW0
  have hcP : 0 < cPlus := lt_of_lt_of_le hcM hle
  have hd : delta * cPlus < cMinus / 4 := by
    have h := hdelta.2
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith [h]
  refine ⟨by linarith, by linarith, fun j => ?_⟩
  have hbj := bCoef_bounds hW j
  have hwj := (hW.2.2 j)
  unfold WeightClass at hwj
  constructor
  · have : delta * NlsGge.Birkhoff.bCoef38 W j ≤ delta * cPlus :=
      mul_le_mul_of_nonneg_left hbj.2 hdelta.1.le
    simp only
    linarith [hwj.1]
  · have : 0 ≤ delta * NlsGge.Birkhoff.bCoef38 W j := mul_nonneg hdelta.1.le hbj.1
    simp only
    linarith [hwj.2]

theorem lowerWeightTilt_coefficient_ratio
    (cMinus cPlus : ℝ) (W : ℕ → ℝ)
    (hW : WeightClass cMinus cPlus W) (j : ℕ) :
    NlsGge.coefficient W (j + 1) / NlsGge.coefficient W j ≤
      (cPlus / cMinus) / (((j + 1 : ℕ) : ℝ) ^ 4) :=
  ratio_le hW j

theorem lowerWeightTilt_coefficient_margin
    (cMinus cPlus : ℝ) (W : ℕ → ℝ) (delta : ℝ)
    (hW : WeightClass cMinus cPlus W)
    (hdelta : 0 < delta ∧ delta < cMinus / (4 * cPlus)) :
    ∀ j : ℕ,
      (3 / 4 : ℝ) * NlsGge.coefficient W j ≤
        NlsGge.coefficient (NlsGge.Birkhoff.tiltCoef38 W delta) j := by
  intro j
  have hW0 := hW
  unfold WeightClass at hW0
  obtain ⟨hcM, hle, _⟩ := hW0
  have hcP : 0 < cPlus := lt_of_lt_of_le hcM hle
  have hd : delta * (cPlus / cMinus) < 1 / 4 := by
    have h := hdelta.2
    rw [lt_div_iff₀ (by positivity)] at h
    rw [show delta * (cPlus / cMinus) = delta * cPlus / cMinus by ring, div_lt_iff₀ hcM]
    nlinarith [h]
  have hb0 : 0 ≤ NlsGge.coefficient W j := by
    have hW1 := hW
    unfold WeightClass at hW1
    have hWj : 0 < W j := lt_of_lt_of_le hW1.1 (hW1.2.2 j).1
    unfold NlsGge.coefficient
    positivity
  have hcore := margin_core hW delta hdelta.1.le j
  nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hd) hb0]

theorem lowerWeightTilt_weightClass_one_two
    (W : ℕ → ℝ) (delta : ℝ)
    (hW : WeightClass 1 2 W)
    (hdelta : 0 < delta ∧ delta < (1 / 4 : ℝ)) :
    WeightClass (1 / 2) 2
      (fun j : ℕ => W j - delta * NlsGge.Birkhoff.bCoef38 W j) := by
  refine ⟨by norm_num, by norm_num, fun j => ?_⟩
  have hbj := bCoef_bounds hW j
  have hwj := (hW.2.2 j)
  unfold WeightClass at hwj
  constructor
  · have : delta * NlsGge.Birkhoff.bCoef38 W j ≤ delta * 2 :=
      mul_le_mul_of_nonneg_left hbj.2 hdelta.1.le
    simp only
    linarith [hwj.1, hdelta.2]
  · have : 0 ≤ delta * NlsGge.Birkhoff.bCoef38 W j := mul_nonneg hdelta.1.le hbj.1
    simp only
    linarith [hwj.2]

theorem lowerWeightTilt_coefficient_margin_one_two
    (W : ℕ → ℝ) (delta : ℝ)
    (hW : WeightClass 1 2 W)
    (hdelta : 0 < delta ∧ delta < (1 / 4 : ℝ)) :
    ∀ j : ℕ,
      (1 / 2 : ℝ) * NlsGge.coefficient W j ≤
        NlsGge.coefficient (NlsGge.Birkhoff.tiltCoef38 W delta) j := by
  intro j
  have hcore := margin_core hW delta hdelta.1.le j
  have hb0 : 0 ≤ NlsGge.coefficient W j := by
    have hW1 := hW
    unfold WeightClass at hW1
    have hWj : 0 < W j := lt_of_lt_of_le hW1.1 (hW1.2.2 j).1
    unfold NlsGge.coefficient
    positivity
  have h2 : (1 / 2 : ℝ) ≤ 1 - delta * (2 / 1) := by norm_num; linarith [hdelta.2]
  nlinarith [mul_le_mul_of_nonneg_right h2 hb0]

end NlsGge.ThirdConsultation.T
end

