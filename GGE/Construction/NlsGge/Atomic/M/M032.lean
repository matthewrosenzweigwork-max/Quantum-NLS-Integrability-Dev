import Mathlib
import NlsGge.Atomic.M.M030
import NlsGge.Atomic.M.M028
import NlsGge.ThirdConsultation.M.M032Tail
import NlsGge.ThirdConsultation.M.MSchurBound

   
                                                                                                        

                                                                                                                  
                                                                                               
                                                                                                   
                                                                                                
                                                                                                                   
                                                                                                                
                                                                                                                   
                                                                       
  

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace NlsGge.ThirdConsultation.M032S

open NlsGge.GK38 NlsGge.ThirdConsultation

theorem prod_bound (W a b ep em x y : ℝ) (hW : 0 ≤ W) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : W * x ≤ W * a + ep) (h2 : W * y ≤ W * b + em) :
    W ^ 2 * (x * y) ≤ W ^ 2 * (a ^ 2 + b ^ 2) + (ep ^ 2 + em ^ 2) := by
  have hWx : 0 ≤ W * x := mul_nonneg hW hx
  have hWy : 0 ≤ W * y := mul_nonneg hW hy
  have e1 : (W * x) ^ 2 ≤ (W * a + ep) ^ 2 := pow_le_pow_left₀ hWx h1 2
  have e2 : (W * y) ^ 2 ≤ (W * b + em) ^ 2 := pow_le_pow_left₀ hWy h2 2
  have : W ^ 2 * (x * y) = (W * x) * (W * y) := by ring
  rw [this]
  nlinarith [sq_nonneg (W * x - W * y), sq_nonneg (W * a - ep), sq_nonneg (W * b - em)]

/-- Per-label weighted bound for a thresholded index. -/
theorem weighted_gap_label_bound
    (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (φ : PotPair)
    (hW : φ ∈ gkW) (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤) (n : ℤ)
    (hth : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    w (2 * n) ^ 2 * ‖NlsGge.GKDefinitionDesign.gap φ n‖ ^ 2 ≤
      6 * (w (2 * n) ^ 2 * (‖MTwoMode.fourierPotential φ true (2 * n)‖ ^ 2 +
        ‖MTwoMode.fourierPotential φ false (-2 * n)‖ ^ 2)) +
      384 * MTwoMode.potentialCoefficientNorm w φ ^ 6 *
        (1 / NlsGge.Atomic.M.M054.indexWeight n ^ 2) := by
  obtain ⟨hne, _, hg⟩ := NlsGge.ThirdConsultation.M.gap_square_schur_bound w hw φ hW hφ n hth
  set W := w (2 * n) with hWdef
  have hW1 : 1 ≤ W := by
    have h := (NlsGge.ThirdConsultation.M029R.weight_facts w hw (2 * n)).1
    have : (1 : ℝ) ≤ NlsGge.Atomic.M.M054.indexWeight (2 * n) := by
      unfold NlsGge.Atomic.M.M054.indexWeight
      have := abs_nonneg ((2 * n : ℤ) : ℝ)
      linarith
    linarith
  have hW0 : 0 < W := by linarith
  set Q := MTwoMode.potentialCoefficientNorm w φ with hQdef
  set cp := NlsGge.ThirdConsultation.M.componentNorm w φ true with hcp
  set cm := NlsGge.ThirdConsultation.M.componentNorm w φ false with hcm
  set ρ := NlsGge.Atomic.M.M054.indexWeight n with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    unfold NlsGge.Atomic.M.M054.indexWeight
    have := abs_nonneg (n : ℝ)
    linarith
  set a := ‖MTwoMode.fourierPotential φ true (2 * n)‖ with ha
  set b := ‖MTwoMode.fourierPotential φ false (-2 * n)‖ with hb
  have hQ2 : Q ^ 2 = cp ^ 2 + cm ^ 2 := NlsGge.ThirdConsultation.MTwoModeB.potentialNorm_sq w φ hφ
  set K : ℝ := W ^ 2 * (a ^ 2 + b ^ 2) + 64 * Q ^ 6 / ρ ^ 2 with hK
  have hpt : ∀ z : ℂ, ∀ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n,
      W ^ 2 * ‖MTwoMode.offDiagonal φ n z hz true * MTwoMode.offDiagonal φ n z hz false‖ ≤ K := by
    intro z hz
    have e1 := NlsGge.ThirdConsultation.M.schur_offdiagonal_bound w hw φ hφ n z hz hth true
    have e2 := NlsGge.ThirdConsultation.M.schur_offdiagonal_bound w hw φ hφ n z hz hth false
    rw [if_pos rfl] at e1
    rw [if_neg Bool.false_ne_true] at e2
    have t1 : W * ‖MTwoMode.offDiagonal φ n z hz true‖ ≤ W * a + 8 * Q ^ 2 * cp / ρ := by
      have := norm_add_le (MTwoMode.offDiagonal φ n z hz true - MTwoMode.fourierPotential φ true (2 * n))
        (MTwoMode.fourierPotential φ true (2 * n))
      rw [sub_add_cancel] at this
      have := mul_le_mul_of_nonneg_left this hW0.le
      rw [mul_add] at this
      linarith
    have t2 : W * ‖MTwoMode.offDiagonal φ n z hz false‖ ≤ W * b + 8 * Q ^ 2 * cm / ρ := by
      have := norm_add_le (MTwoMode.offDiagonal φ n z hz false - MTwoMode.fourierPotential φ false (-2 * n))
        (MTwoMode.fourierPotential φ false (-2 * n))
      rw [sub_add_cancel] at this
      have := mul_le_mul_of_nonneg_left this hW0.le
      rw [mul_add] at this
      linarith
    have hpb := prod_bound W a b (8 * Q ^ 2 * cp / ρ) (8 * Q ^ 2 * cm / ρ) _ _ hW0.le (norm_nonneg _)
      (norm_nonneg _) t1 t2
    have hsq : (8 * Q ^ 2 * cp / ρ) ^ 2 + (8 * Q ^ 2 * cm / ρ) ^ 2 = 64 * Q ^ 6 / ρ ^ 2 := by
      have : Q ^ 6 = Q ^ 4 * (cp ^ 2 + cm ^ 2) := by rw [← hQ2]; ring
      rw [this]
      field_simp
      ring
    rw [norm_mul, hK]
    linarith
  have hsup : sSup {r : ℝ | ∃ z : ℂ, ∃ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n,
      r = ‖MTwoMode.offDiagonal φ n z hz true * MTwoMode.offDiagonal φ n z hz false‖} ≤ K / W ^ 2 := by
    apply csSup_le hne
    rintro r ⟨z, hz, rfl⟩
    rw [le_div_iff₀ (by positivity)]
    have := hpt z hz
    linarith
  have hgap := hg
  calc W ^ 2 * ‖NlsGge.GKDefinitionDesign.gap φ n‖ ^ 2
      ≤ W ^ 2 * (6 * (K / W ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 6 * K := by field_simp
    _ = 6 * (W ^ 2 * (a ^ 2 + b ^ 2)) + 384 * Q ^ 6 * (1 / ρ ^ 2) := by
        rw [hK]
        ring

/-- Telescoping majorant. -/
def tele (N k : ℕ) : ℝ :=
  if N ≤ k then 2 / (2 * (k : ℝ) + 1) - 2 / (2 * (k : ℝ) + 3) else 0

theorem tele_nonneg (N k : ℕ) : 0 ≤ tele N k := by
  unfold tele
  split_ifs
  · have h1 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    have h2 : 2 / (2 * (k : ℝ) + 3) ≤ 2 / (2 * (k : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by norm_num) h1 (by linarith)
    linarith
  · exact le_refl _

theorem tele_sum (N m : ℕ) :
    ∑ k ∈ Finset.range m, tele N k =
      if N ≤ m then 2 / (2 * (N : ℝ) + 1) - 2 / (2 * (m : ℝ) + 1) else 0 := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    split_ifs with h
    · have : N = 0 := by omega
      subst this
      norm_num
    · rfl
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold tele
    by_cases h1 : N ≤ m
    · rw [if_pos h1, if_pos h1, if_pos (by omega)]
      push_cast
      ring
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : N = m + 1
      · rw [if_pos (by omega), h2]
        push_cast
        ring
      · rw [if_neg (by omega)]
        ring

theorem tele_sum_le (N m : ℕ) : ∑ k ∈ Finset.range m, tele N k ≤ 2 / (2 * (N : ℝ) + 1) := by
  rw [tele_sum]
  split_ifs
  · have : 0 ≤ 2 / (2 * (m : ℝ) + 1) := by positivity
    linarith
  · positivity

theorem inv_sq_le_tele (N k : ℕ) (h : N ≤ k) :
    1 / (1 + (k : ℝ)) ^ 2 ≤ tele N k := by
  unfold tele
  rw [if_pos h]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The signed-integer tail `Σ_{N ≤ |n|} <n>⁻² ≤ 3/<N>`, in `ℝ≥0∞`. -/
theorem int_tail_inv_sq (N : ℕ) :
    ∑' n : ℤ, (if N ≤ n.natAbs then
      ENNReal.ofReal (1 / NlsGge.Atomic.M.M054.indexWeight n ^ 2) else 0) ≤
      ENNReal.ofReal (3 / NlsGge.Atomic.M.M054.indexWeight (N : ℤ)) := by
  set f : ℤ → ℝ≥0∞ := fun n => if N ≤ n.natAbs then
    ENNReal.ofReal (1 / NlsGge.Atomic.M.M054.indexWeight n ^ 2) else 0 with hf
  rw [← tsum_nat_add_neg_add_one ENNReal.summable]
  have hpos : ∀ k : ℕ, f (k : ℤ) ≤ ENNReal.ofReal (tele N k) := by
    intro k
    simp only [hf]
    have hab : ((k : ℤ)).natAbs = k := Int.natAbs_natCast k
    rw [hab]
    split_ifs with h
    · apply ENNReal.ofReal_le_ofReal
      have : NlsGge.Atomic.M.M054.indexWeight (k : ℤ) = 1 + (k : ℝ) := by
        unfold NlsGge.Atomic.M.M054.indexWeight
        push_cast
        rw [abs_of_nonneg (Nat.cast_nonneg k)]
      rw [this]
      exact inv_sq_le_tele N k h
    · exact zero_le
  have hneg : ∀ k : ℕ, f (-((k : ℤ) + 1)) ≤ ENNReal.ofReal (tele N (k + 1)) := by
    intro k
    simp only [hf]
    have hab : (-((k : ℤ) + 1)).natAbs = k + 1 := by
      rw [Int.natAbs_neg]
      exact Int.natAbs_natCast (k + 1)
    rw [hab]
    split_ifs with h
    · apply ENNReal.ofReal_le_ofReal
      have : NlsGge.Atomic.M.M054.indexWeight (-((k : ℤ) + 1)) = 1 + ((k + 1 : ℕ) : ℝ) := by
        unfold NlsGge.Atomic.M.M054.indexWeight
        push_cast
        rw [abs_neg, abs_of_nonneg (by positivity)]
      rw [this]
      exact inv_sq_le_tele N (k + 1) h
    · exact zero_le
  have hbound : 2 / (2 * (N : ℝ) + 1) + (2 / (2 * (N : ℝ) + 1) - tele N 0) ≤
      3 / NlsGge.Atomic.M.M054.indexWeight (N : ℤ) := by
    have hw : NlsGge.Atomic.M.M054.indexWeight (N : ℤ) = 1 + (N : ℝ) := by
      unfold NlsGge.Atomic.M.M054.indexWeight
      push_cast
      rw [abs_of_nonneg (Nat.cast_nonneg N)]
    rw [hw]
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      unfold tele
      norm_num
    · have ht : tele N 0 = 0 := by
        unfold tele
        rw [if_neg (by omega)]
      rw [ht]
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h0
      rw [sub_zero, ← two_mul, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  refine ENNReal.tsum_le_of_sum_range_le fun m => ?_
  calc ∑ k ∈ Finset.range m, (f (k : ℤ) + f (-((k : ℤ) + 1)))
      ≤ ∑ k ∈ Finset.range m, ENNReal.ofReal (tele N k + tele N (k + 1)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [ENNReal.ofReal_add (tele_nonneg N k) (tele_nonneg N (k + 1))]
        exact add_le_add (hpos k) (hneg k)
    _ = ENNReal.ofReal (∑ k ∈ Finset.range m, (tele N k + tele N (k + 1))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro k _
        exact add_nonneg (tele_nonneg N k) (tele_nonneg N (k + 1))
    _ ≤ ENNReal.ofReal (3 / NlsGge.Atomic.M.M054.indexWeight (N : ℤ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.sum_add_distrib]
        have h1 := tele_sum_le N m
        have h2 := tele_sum_le N (m + 1)
        rw [Finset.sum_range_succ'] at h2
        linarith

end NlsGge.ThirdConsultation.M032S

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem gap_weighted_tail
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w)
    (N : ℕ) (φ : PotPair) (hW : φ ∈ gkW)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (hN : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight (N : ℤ)) :
    MTwoMode.potentialTailEnergy w φ N ≠ ⊤ ∧
    MTwoMode.complexGapTailEnergy w φ N ≠ ⊤ ∧
    MTwoMode.complexGapTailEnergy w φ N ≤
      6 * MTwoMode.potentialTailEnergy w φ N +
      ENNReal.ofReal (1152 * MTwoMode.potentialCoefficientNorm w φ ^ 6 /
        NlsGge.Atomic.M.M054.indexWeight (N : ℤ)) := by
  have htail := potential_tail_energy_ne_top w hw φ hφ N
  set Q := MTwoMode.potentialCoefficientNorm w φ with hQ
  have hQ6 : 0 ≤ 384 * Q ^ 6 := by
    have : 0 ≤ Q := Real.sqrt_nonneg _
    positivity
  have hthr : ∀ n : ℤ, N ≤ n.natAbs → 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n := by
    intro n hn
    have : NlsGge.Atomic.M.M054.indexWeight (N : ℤ) ≤ NlsGge.Atomic.M.M054.indexWeight n := by
      unfold NlsGge.Atomic.M.M054.indexWeight
      have h1 : |((N : ℤ) : ℝ)| = (N : ℝ) := by
        push_cast
        exact abs_of_nonneg (Nat.cast_nonneg N)
      have h2 : (N : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        have : ((N : ℤ)) ≤ |n| := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast hn
        exact_mod_cast this
      linarith
    linarith
  have hterm : ∀ n : ℤ,
      (if N ≤ n.natAbs then ENNReal.ofReal (w (2 * n) ^ 2 *
        ‖NlsGge.GKDefinitionDesign.gap φ n‖ ^ 2) else 0) ≤
      6 * (if N ≤ n.natAbs then ENNReal.ofReal (w (2 * n) ^ 2 *
          (‖MTwoMode.fourierPotential φ true (2 * n)‖ ^ 2 +
           ‖MTwoMode.fourierPotential φ false (-2 * n)‖ ^ 2)) else 0) +
        ENNReal.ofReal (384 * Q ^ 6) *
          (if N ≤ n.natAbs then
            ENNReal.ofReal (1 / NlsGge.Atomic.M.M054.indexWeight n ^ 2) else 0) := by
    intro n
    split_ifs with hn
    · have hb := NlsGge.ThirdConsultation.M032S.weighted_gap_label_bound w hw φ hW hφ n (hthr n hn)
      have hT : 0 ≤ w (2 * n) ^ 2 *
          (‖MTwoMode.fourierPotential φ true (2 * n)‖ ^ 2 +
           ‖MTwoMode.fourierPotential φ false (-2 * n)‖ ^ 2) := by positivity
      have hR : 0 ≤ 1 / NlsGge.Atomic.M.M054.indexWeight n ^ 2 := by positivity
      rw [← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hQ6,
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg hQ6 hR)]
      apply ENNReal.ofReal_le_ofReal
      linarith
    · simp
  have hle : MTwoMode.complexGapTailEnergy w φ N ≤
      6 * MTwoMode.potentialTailEnergy w φ N +
        ENNReal.ofReal (384 * Q ^ 6) *
          ∑' n : ℤ, (if N ≤ n.natAbs then
            ENNReal.ofReal (1 / NlsGge.Atomic.M.M054.indexWeight n ^ 2) else 0) := by
    unfold MTwoMode.complexGapTailEnergy MTwoMode.potentialTailEnergy
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum hterm
  have hsum := NlsGge.ThirdConsultation.M032S.int_tail_inv_sq N
  have hfin : ENNReal.ofReal (384 * Q ^ 6) *
      ENNReal.ofReal (3 / NlsGge.Atomic.M.M054.indexWeight (N : ℤ)) =
      ENNReal.ofReal (1152 * Q ^ 6 / NlsGge.Atomic.M.M054.indexWeight (N : ℤ)) := by
    rw [← ENNReal.ofReal_mul hQ6]
    congr 1
    ring
  have hmain : MTwoMode.complexGapTailEnergy w φ N ≤
      6 * MTwoMode.potentialTailEnergy w φ N +
      ENNReal.ofReal (1152 * Q ^ 6 / NlsGge.Atomic.M.M054.indexWeight (N : ℤ)) := by
    refine hle.trans ?_
    rw [← hfin]
    gcongr
  refine ⟨htail, ?_, hmain⟩
  refine ne_top_of_le_ne_top ?_ hmain
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) htail, ENNReal.ofReal_ne_top⟩

end NlsGge.ThirdConsultation.M

end
