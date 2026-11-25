import Mathlib
import NlsGge.Atomic.KSN.KSN013Asm
import NlsGge.Atomic.G4.G4037
import NlsGge.ThirdConsultation.G3.G3026Support
import NlsGge.Atomic.KSN.KSN012BetaPure
import NlsGge.Atomic.KSN.KSN012Sup7Core

                                                                                      
                                                                                                                
                                                                                                           
                                                                                                                      
                                                                                                                  
                                                                                
                                                                                                       
                                                                                                                   
                                                                                                                          
                                                                                                                        
                                                                                                      
                                                                                                                   
                           
set_option autoImplicit false

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN012L
noncomputable section
open NlsGge.ThirdConsultation.KSN

theorem jb_sq_le_two_bracket_sq (n : ℤ) : japaneseBracket n ^ 2 ≤ 2 * bracket n ^ 2 := by
  rw [NlsGge.Atomic.KSN011.br_sq]
  unfold bracket
  have hm : ((n.natAbs : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rcases max_cases 1 ((n.natAbs : ℕ) : ℝ) with ⟨h, h1⟩ | ⟨h, h1⟩
  · rw [h]
    have : (n : ℝ) ^ 2 ≤ 1 := by rw [← hm]; nlinarith [Nat.cast_nonneg (α := ℝ) n.natAbs]
    linarith
  · rw [h, hm]
    have : 1 ≤ (n : ℝ) ^ 2 := by rw [← hm]; nlinarith
    linarith

theorem ite_ofReal (c : Prop) [Decidable c] (a : ℝ) :
    (if c then ENNReal.ofReal a else 0) = ENNReal.ofReal (if c then a else 0) := by
  split_ifs <;> simp

/-- Finite partial sums of a nonnegative real sequence dominated by an ENNReal tsum bound. -/
theorem fin_le_of_tsum (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n) (c : ℝ) (hc : 0 ≤ c)
    (h : ∑' n : ℤ, ENNReal.ofReal (f n) ≤ ENNReal.ofReal c) (F : Finset ℤ) :
    ∑ n ∈ F, f n ≤ c := by
  have h1 : ENNReal.ofReal (∑ n ∈ F, f n) ≤ ENNReal.ofReal c := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => hf n)]
    exact (ENNReal.sum_le_tsum F).trans h
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 h1

/-- Complex M-032 with B1: the weighted gap TAIL SUM is bounded on every H¹ ball. -/
theorem gap_tail_sum
    (hM032 : ∀ (w : ℤ → ℝ), NlsGge.ThirdConsultation.M.OneDerivativeWeight w → ∀ (N : ℕ) (φ : PotPair),
      φ ∈ gkW → NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤ →
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight (N : ℤ) →
      NlsGge.ThirdConsultation.MTwoMode.complexGapTailEnergy w φ N ≤
        6 * NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy w φ N +
        ENNReal.ofReal (1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 6 /
          NlsGge.Atomic.M.M054.indexWeight (N : ℤ)))
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ (N : ℕ) (Γ : ℝ), 0 ≤ Γ ∧ ∀ x : PairScale 1, ‖x‖ ≤ H →
      pairPotential 1 (by norm_num) x ∈ gkW → ∀ F : Finset ℤ,
        ∑ k ∈ F, (if N ≤ k.natAbs then
          japaneseBracket k ^ 2 * ‖lamPlus (pairPotential 1 (by norm_num) x) k -
            lamMinus (pairPotential 1 (by norm_num) x) k‖ ^ 2 else 0) ≤ Γ := by
  obtain ⟨w₁, hw₁, Cb, hCb⟩ := KSN012B1_main
  set E0 : ℝ := max Cb 0 * H ^ 2 with hE0
  have hE00 : 0 ≤ E0 := by positivity
  set Γ : ℝ := 6 * E0 + 1152 * E0 ^ 3 with hΓ
  have hΓ0 : 0 ≤ Γ := by positivity
  refine ⟨⌈8 * E0⌉₊, Γ, hΓ0, fun x hx hW F => ?_⟩
  set φ := pairPotential 1 (by norm_num) x with hφ
  have hEn : NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w₁ φ ≤ ENNReal.ofReal E0 := by
    refine (hCb x).trans (ENNReal.ofReal_le_ofReal ?_)
    have hx2 : ‖x‖ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    calc Cb * ‖x‖ ^ 2 ≤ max Cb 0 * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      _ ≤ max Cb 0 * H ^ 2 := mul_le_mul_of_nonneg_left hx2 (le_max_right _ _)
  have hne : NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w₁ φ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEn
  have hQ2 : NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w₁ φ ^ 2 ≤ E0 := by
    unfold NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm
    rw [Real.sq_sqrt ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal hE00 hEn
  have hQ0 : 0 ≤ NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w₁ φ ^ 2 := sq_nonneg _
  have hiw : NlsGge.Atomic.M.M054.indexWeight ((⌈8 * E0⌉₊ : ℕ) : ℤ) = 1 + (⌈8 * E0⌉₊ : ℝ) := by
    unfold NlsGge.Atomic.M.M054.indexWeight
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have hiw1 : 1 ≤ NlsGge.Atomic.M.M054.indexWeight ((⌈8 * E0⌉₊ : ℕ) : ℤ) := by
    rw [hiw]; linarith [(Nat.cast_nonneg ⌈8 * E0⌉₊ : (0 : ℝ) ≤ _)]
  have hN : 8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w₁ φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight ((⌈8 * E0⌉₊ : ℕ) : ℤ) := by
    rw [hiw]
    have := Nat.le_ceil (8 * E0)
    linarith
  have hT := hM032 w₁ hw₁ ⌈8 * E0⌉₊ φ hW hne hN
  have htail := (ksn013_tail_le_energy w₁ hw₁ φ ⌈8 * E0⌉₊).trans hEn
  have hQ6 : 1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w₁ φ ^ 6 /
      NlsGge.Atomic.M.M054.indexWeight ((⌈8 * E0⌉₊ : ℕ) : ℤ) ≤ 1152 * E0 ^ 3 := by
    have h6 : NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w₁ φ ^ 6 ≤ E0 ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul]
      exact pow_le_pow_left₀ hQ0 hQ2 3
    have hpos : 0 ≤ 1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w₁ φ ^ 6 := by
      positivity
    calc 1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w₁ φ ^ 6 /
          NlsGge.Atomic.M.M054.indexWeight ((⌈8 * E0⌉₊ : ℕ) : ℤ)
        ≤ 1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w₁ φ ^ 6 :=
          div_le_self hpos hiw1
      _ ≤ 1152 * E0 ^ 3 := by linarith
  have hgapT : NlsGge.ThirdConsultation.MTwoMode.complexGapTailEnergy w₁ φ ⌈8 * E0⌉₊ ≤
      ENNReal.ofReal Γ := by
    refine hT.trans ?_
    calc 6 * NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy w₁ φ ⌈8 * E0⌉₊ +
          ENNReal.ofReal (1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w₁ φ ^ 6 /
            NlsGge.Atomic.M.M054.indexWeight ((⌈8 * E0⌉₊ : ℕ) : ℤ))
        ≤ 6 * ENNReal.ofReal E0 + ENNReal.ofReal (1152 * E0 ^ 3) :=
          add_le_add (by gcongr) (ENNReal.ofReal_le_ofReal hQ6)
      _ = ENNReal.ofReal Γ := by
          rw [hΓ, ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
          norm_num
  have hfin := fin_le_of_tsum (fun n : ℤ => if ⌈8 * E0⌉₊ ≤ n.natAbs then
      w₁ (2 * n) ^ 2 * ‖NlsGge.GKDefinitionDesign.gap φ n‖ ^ 2 else 0)
    (fun n => by split_ifs <;> positivity) Γ hΓ0 (by
      refine le_trans (le_of_eq ?_) hgapT
      unfold NlsGge.ThirdConsultation.MTwoMode.complexGapTailEnergy
      exact tsum_congr (fun n => (ite_ofReal _ _).symm)) F
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) hfin
  split_ifs
  · exact mul_le_mul_of_nonneg_right (ksn013_bracket_le_weight w₁ hw₁ k) (sq_nonneg _)
  · exact le_rfl

/-- Low-label count: Σ_{k∈F, |k|<N} c ≤ (2N+1)·c. -/
theorem low_sum_le (F : Finset ℤ) (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ k ∈ F, (if k.natAbs < N then c else 0) ≤ (2 * N + 1) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hc
  have hsub : F.filter (fun k : ℤ => k.natAbs < N) ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro k hk
    have h := (Finset.mem_filter.1 hk).2
    rw [Finset.mem_Icc]
    omega
  have h1 := Finset.card_le_card hsub
  rw [Int.card_Icc] at h1
  have h2 : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [h2] at h1
  exact_mod_cast h1

theorem pure_sq (j m g d P : ℝ) (hj : 0 ≤ j) (hm : 0 ≤ m) (h : m ≤ P * g + d) :
    (j * m) ^ 2 ≤ 2 * P ^ 2 * (j ^ 2 * g ^ 2) + 2 * (j ^ 2 * d ^ 2) := by
  have h1 : j * m ≤ P * (j * g) + j * d := by
    have := mul_le_mul_of_nonneg_left h hj
    linarith
  have h2 := pow_le_pow_left₀ (mul_nonneg hj hm) h1 2
  have h3 := NlsGge.ThirdConsultation.KSN012U.sup7_sq2 (P * (j * g)) (j * d)
  have e : 2 * ((P * (j * g)) ^ 2 + (j * d) ^ 2) = 2 * P ^ 2 * (j ^ 2 * g ^ 2) + 2 * (j ^ 2 * d ^ 2) := by ring
  linarith

theorem mass_split (φ : PotPair) (hφW : φ ∈ gkW) (Rm Ca : ℝ) (hRm0 : 0 ≤ Rm)
    (hgk : ∀ k, ‖lamPlus φ k - lamMinus φ k‖ ≤ 2 * Rm)
    (hid : ∀ k, lamDot φ k - tauN φ k = gamma2 φ k * a5CriticalA38 k φ)
    (ha : ∀ k, ‖a5CriticalA38 k φ‖ ≤ Real.sqrt Ca) (k : ℤ) :
    ‖lamPlus φ k - lamMinus φ k‖ + ‖muSeq φ k - tauN φ k‖ ≤
      (1 + 2 * Rm * Real.sqrt Ca) * ‖lamPlus φ k - lamMinus φ k‖ + ‖muSeq φ k - lamDot φ k‖ := by
  have hlt : ‖lamDot φ k - tauN φ k‖ ≤ 2 * Rm * Real.sqrt Ca * ‖lamPlus φ k - lamMinus φ k‖ := by
    rw [hid k, gamma2_value38 φ hφW k, norm_mul, norm_pow]
    have hg := hgk k
    have hg0 := norm_nonneg (lamPlus φ k - lamMinus φ k)
    have h1 : ‖lamPlus φ k - lamMinus φ k‖ ^ 2 ≤ 2 * Rm * ‖lamPlus φ k - lamMinus φ k‖ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hg hg0
    calc ‖lamPlus φ k - lamMinus φ k‖ ^ 2 * ‖a5CriticalA38 k φ‖
        ≤ (2 * Rm * ‖lamPlus φ k - lamMinus φ k‖) * Real.sqrt Ca :=
          mul_le_mul h1 (ha k) (norm_nonneg _) (by positivity)
      _ = 2 * Rm * Real.sqrt Ca * ‖lamPlus φ k - lamMinus φ k‖ := by ring
  have htri : ‖muSeq φ k - tauN φ k‖ ≤ ‖muSeq φ k - lamDot φ k‖ + ‖lamDot φ k - tauN φ k‖ := by
    have h := norm_add_le (muSeq φ k - lamDot φ k) (lamDot φ k - tauN φ k)
    simpa only [sub_add_sub_cancel] using h
  have e : (1 + 2 * Rm * Real.sqrt Ca) * ‖lamPlus φ k - lamMinus φ k‖ =
      ‖lamPlus φ k - lamMinus φ k‖ + 2 * Rm * Real.sqrt Ca * ‖lamPlus φ k - lamMinus φ k‖ := by ring
  linarith

theorem jb_sq_le_low (k : ℤ) (N : ℕ) (hk : k.natAbs < N) : japaneseBracket k ^ 2 ≤ 1 + (N : ℝ) ^ 2 := by
  rw [NlsGge.Atomic.KSN011.br_sq]
  have h1 : (k : ℝ) ^ 2 = ((k.natAbs : ℕ) : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have h2 : ((k.natAbs : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk.le
  have h3 := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2
  linarith

theorem gap_sum (φ : PotPair) (Rm Γ : ℝ) (Ng : ℕ) (hRm0 : 0 ≤ Rm)
    (hgk : ∀ k, ‖lamPlus φ k - lamMinus φ k‖ ≤ 2 * Rm)
    (hgF : ∀ F : Finset ℤ, ∑ k ∈ F, (if Ng ≤ k.natAbs then
      japaneseBracket k ^ 2 * ‖lamPlus φ k - lamMinus φ k‖ ^ 2 else 0) ≤ Γ) (F : Finset ℤ) :
    ∑ k ∈ F, japaneseBracket k ^ 2 * ‖lamPlus φ k - lamMinus φ k‖ ^ 2 ≤
      Γ + (2 * Ng + 1) * ((1 + (Ng : ℝ) ^ 2) * (2 * Rm) ^ 2) := by
  have hpt : ∀ k ∈ F, japaneseBracket k ^ 2 * ‖lamPlus φ k - lamMinus φ k‖ ^ 2 ≤
      (if Ng ≤ k.natAbs then japaneseBracket k ^ 2 * ‖lamPlus φ k - lamMinus φ k‖ ^ 2 else 0) +
      (if k.natAbs < Ng then (1 + (Ng : ℝ) ^ 2) * (2 * Rm) ^ 2 else 0) := by
    intro k _
    by_cases hk : Ng ≤ k.natAbs
    · rw [if_pos hk, if_neg (not_lt.2 hk)]; simp
    · rw [if_neg hk, if_pos (not_le.1 hk), zero_add]
      have hg2 : ‖lamPlus φ k - lamMinus φ k‖ ^ 2 ≤ (2 * Rm) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hgk k) 2
      exact mul_le_mul (jb_sq_le_low k Ng (not_le.1 hk)) hg2 (sq_nonneg _) (by positivity)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add (hgF F) (low_sum_le F Ng _ (by positivity))

theorem mu_sum (φ : PotPair) (Rm Cb : ℝ) (Nb : ℕ) (hRm0 : 0 ≤ Rm)
    (hmk : ∀ k, ‖muSeq φ k - lamDot φ k‖ ≤ 2 * Rm)
    (hmF : ∀ F : Finset ℤ, ∑ k ∈ F, (if Nb ≤ k.natAbs then
      bracket k ^ 2 * ‖muSeq φ k - lamDot φ k‖ ^ 2 else 0) ≤ Cb) (F : Finset ℤ) :
    ∑ k ∈ F, japaneseBracket k ^ 2 * ‖muSeq φ k - lamDot φ k‖ ^ 2 ≤
      2 * Cb + (2 * Nb + 1) * ((1 + (Nb : ℝ) ^ 2) * (2 * Rm) ^ 2) := by
  have hpt : ∀ k ∈ F, japaneseBracket k ^ 2 * ‖muSeq φ k - lamDot φ k‖ ^ 2 ≤
      2 * (if Nb ≤ k.natAbs then bracket k ^ 2 * ‖muSeq φ k - lamDot φ k‖ ^ 2 else 0) +
      (if k.natAbs < Nb then (1 + (Nb : ℝ) ^ 2) * (2 * Rm) ^ 2 else 0) := by
    intro k _
    by_cases hk : Nb ≤ k.natAbs
    · rw [if_pos hk, if_neg (not_lt.2 hk), add_zero]
      have := mul_le_mul_of_nonneg_right (jb_sq_le_two_bracket_sq k) (sq_nonneg ‖muSeq φ k - lamDot φ k‖)
      linarith
    · rw [if_neg hk, if_pos (not_le.1 hk), mul_zero, zero_add]
      have hg2 : ‖muSeq φ k - lamDot φ k‖ ^ 2 ≤ (2 * Rm) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hmk k) 2
      exact mul_le_mul (jb_sq_le_low k Nb (not_le.1 hk)) hg2 (sq_nonneg _) (by positivity)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := hmF F
  have := low_sum_le F Nb ((1 + (Nb : ℝ) ^ 2) * (2 * Rm) ^ 2) (by positivity)
  linarith

theorem mass_sum (φ : PotPair) (hφW : φ ∈ gkW) (Rm Ca Γ Cb : ℝ) (Ng Nb : ℕ) (hRm0 : 0 ≤ Rm)
    (hgk : ∀ k, ‖lamPlus φ k - lamMinus φ k‖ ≤ 2 * Rm)
    (hmk : ∀ k, ‖muSeq φ k - lamDot φ k‖ ≤ 2 * Rm)
    (hid : ∀ k, lamDot φ k - tauN φ k = gamma2 φ k * a5CriticalA38 k φ)
    (ha : ∀ k, ‖a5CriticalA38 k φ‖ ≤ Real.sqrt Ca)
    (hgF : ∀ F : Finset ℤ, ∑ k ∈ F, (if Ng ≤ k.natAbs then
      japaneseBracket k ^ 2 * ‖lamPlus φ k - lamMinus φ k‖ ^ 2 else 0) ≤ Γ)
    (hmF : ∀ F : Finset ℤ, ∑ k ∈ F, (if Nb ≤ k.natAbs then
      bracket k ^ 2 * ‖muSeq φ k - lamDot φ k‖ ^ 2 else 0) ≤ Cb) (F : Finset ℤ) :
    ∑ k ∈ F, (japaneseBracket k * (‖lamPlus φ k - lamMinus φ k‖ + ‖muSeq φ k - tauN φ k‖)) ^ 2 ≤
      2 * (1 + 2 * Rm * Real.sqrt Ca) ^ 2 * (Γ + (2 * Ng + 1) * ((1 + (Ng : ℝ) ^ 2) * (2 * Rm) ^ 2)) +
      2 * (2 * Cb + (2 * Nb + 1) * ((1 + (Nb : ℝ) ^ 2) * (2 * Rm) ^ 2)) := by
  have hpt : ∀ k ∈ F, (japaneseBracket k * (‖lamPlus φ k - lamMinus φ k‖ + ‖muSeq φ k - tauN φ k‖)) ^ 2 ≤
      2 * (1 + 2 * Rm * Real.sqrt Ca) ^ 2 * (japaneseBracket k ^ 2 * ‖lamPlus φ k - lamMinus φ k‖ ^ 2) +
      2 * (japaneseBracket k ^ 2 * ‖muSeq φ k - lamDot φ k‖ ^ 2) := fun k _ =>
    pure_sq _ _ _ _ _ (jb_pos k).le (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (mass_split φ hφW Rm Ca hRm0 hgk hid ha k)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := mul_le_mul_of_nonneg_left (gap_sum φ Rm Γ Ng hRm0 hgk hgF F)
    (by positivity : (0 : ℝ) ≤ 2 * (1 + 2 * Rm * Real.sqrt Ca) ^ 2)
  have h2 := mul_le_mul_of_nonneg_left (mu_sum φ Rm Cb Nb hRm0 hmk hmF F) (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- Ball-uniform ℓ² mass and betaSum bound on an L²-open neighbourhood of each point of sourceBetaW. -/
theorem beta_local
    (hM032 : ∀ (w : ℤ → ℝ), NlsGge.ThirdConsultation.M.OneDerivativeWeight w → ∀ (N : ℕ) (φ : PotPair),
      φ ∈ gkW → NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤ →
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight (N : ℤ) →
      NlsGge.ThirdConsultation.MTwoMode.complexGapTailEnergy w φ N ≤
        6 * NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy w φ N +
        ENNReal.ofReal (1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 6 /
          NlsGge.Atomic.M.M054.indexWeight (N : ℤ)))
    (hmissB : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : PairScale 1, ‖x‖ ≤ B →
        (∑' n : ℤ, if N ≤ n.natAbs then
          ENNReal.ofReal (bracket n ^ 2 *
            ‖muSeq (pairPotential 1 (by norm_num) x) n - lamDot (pairPotential 1 (by norm_num) x) n‖ ^ 2)
          else 0) ≤ ENNReal.ofReal C)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
    ∃ O : Set PotPair, IsOpen O ∧ φ₀ ∈ O ∧ O ⊆ sourceBetaW ∧
      ∀ H : ℝ, 0 ≤ H → ∃ A : ℝ, 0 ≤ A ∧ ∀ x : PairScale 1, ‖x‖ ≤ H →
        pairPotential 1 (by norm_num) x ∈ O → ∀ n : ℤ,
          ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ A / bracket n ∧
          ‖lamPlus (pairPotential 1 (by norm_num) x) n - lamMinus (pairPotential 1 (by norm_num) x) n‖ +
            ‖muSeq (pairPotential 1 (by norm_num) x) n - tauN (pairPotential 1 (by norm_num) x) n‖ ≤
              A / bracket n := by
  have hW₀ : φ₀ ∈ gkW := ksn013_sourceBetaW_gkW hφ₀
  obtain ⟨V1, hV1, -, hV1o, -, C, R, c, J, hgeom, hspec⟩ := local_isolatingFamily_common38 φ₀ hW₀
  obtain ⟨U2, hU2o, hφU2, -, Ca, -, hU2⟩ := G2_026 φ₀ hW₀
  obtain ⟨V, hVo, hφV, hVS, Cβ, Mβ, hCβ, -, hVb⟩ := source_beta_inverse_distance_on_sourceBetaW φ₀ hφ₀
  obtain ⟨K, hK0, hK⟩ := beta_pure
  refine ⟨V1 ∩ U2 ∩ V, (hV1o.inter hU2o).inter hVo, ⟨⟨mem_of_mem_nhds hV1, hφU2⟩, hφV⟩,
    fun φ hφ => hVS hφ.2, fun H hH => ?_⟩
  -- geometric radius bound
  set Rm : ℝ := Real.pi / 4 + ∑ k ∈ Finset.Icc (-(J : ℤ)) J, R k with hRm
  have hRpos : ∀ k, 0 < R k := fun k => (hgeom.1 k).1
  have hsum0 : 0 ≤ ∑ k ∈ Finset.Icc (-(J : ℤ)) J, R k :=
    Finset.sum_nonneg (fun k _ => (hRpos k).le)
  have hRm0 : 0 ≤ Rm := by rw [hRm]; linarith [Real.pi_pos]
  have hRle : ∀ k, R k ≤ Rm := by
    intro k
    by_cases hk : (J : ℤ) < |k|
    · rw [(hgeom.2.2.2.2 k hk).2.1]
      linarith
    · push_neg at hk
      have hmem : k ∈ Finset.Icc (-(J : ℤ)) J := Finset.mem_Icc.mpr (abs_le.mp hk)
      have := Finset.single_le_sum (fun j _ => (hRpos j).le) hmem
      linarith [Real.pi_pos]
  have hball2 : ∀ (k : ℤ) (u v : ℂ), u ∈ ball (C k) (R k) → v ∈ ball (C k) (R k) → ‖u - v‖ ≤ 2 * Rm := by
    intro k u v hu hv
    have e1 := mem_ball_iff_norm.mp hu
    have e2 := mem_ball_iff_norm.mp hv
    have : ‖u - v‖ ≤ ‖u - C k‖ + ‖v - C k‖ := by
      have h := norm_sub_le (u - C k) (v - C k)
      simpa only [sub_sub_sub_cancel_right] using h
    linarith [hRle k]
  -- tail constants
  obtain ⟨Ng, Γ, hΓ0, hgapF⟩ := gap_tail_sum hM032 H hH
  obtain ⟨Cb, Nb, hCb0, hmB⟩ := hmissB H hH
  set S : ℝ := 2 * (1 + 2 * Rm * Real.sqrt Ca) ^ 2 *
      (Γ + (2 * Ng + 1) * ((1 + (Ng : ℝ) ^ 2) * (2 * Rm) ^ 2)) +
    2 * (2 * Cb + (2 * Nb + 1) * ((1 + (Nb : ℝ) ^ 2) * (2 * Rm) ^ 2)) with hS
  have hS0 : 0 ≤ S := by positivity
  refine ⟨max (K * Cβ * Real.sqrt S) (Real.sqrt S), le_trans (Real.sqrt_nonneg _) (le_max_right _ _),
    fun x hx hxO n => ?_⟩
  set φ := pairPotential 1 (by norm_num) x with hφdef
  have hφS : φ ∈ sourceBetaW := hVS hxO.2
  have hφW : φ ∈ gkW := ksn013_sourceBetaW_gkW hφS
  have hsp : IsolatingSpectral38 φ C R := hspec φ hxO.1.1
  obtain ⟨hid, hsumA, hboundA⟩ := hU2 φ hxO.1.2
  have ha : ∀ k, ‖a5CriticalA38 k φ‖ ≤ Real.sqrt Ca := by
    intro k
    have h1 : ‖a5CriticalA38 k φ‖ ^ 2 ≤ Ca :=
      (hsumA.le_tsum k (fun j _ => sq_nonneg _)).trans hboundA
    have := Real.abs_le_sqrt h1
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hgF : ∀ F : Finset ℤ, ∑ k ∈ F, (if Ng ≤ k.natAbs then
      japaneseBracket k ^ 2 * ‖lamPlus φ k - lamMinus φ k‖ ^ 2 else 0) ≤ Γ := hgapF x hx hφW
  have hmF : ∀ F : Finset ℤ, ∑ k ∈ F, (if Nb ≤ k.natAbs then
      bracket k ^ 2 * ‖muSeq φ k - lamDot φ k‖ ^ 2 else 0) ≤ Cb := fun F =>
    fin_le_of_tsum (fun n : ℤ => if Nb ≤ n.natAbs then
        bracket n ^ 2 * ‖muSeq φ n - lamDot φ n‖ ^ 2 else 0)
      (fun n => by split_ifs <;> positivity) Cb hCb0 (by
        refine le_trans (le_of_eq (tsum_congr (fun n => (ite_ofReal _ _).symm))) (hmB x hx)) F
  have hgk : ∀ k, ‖lamPlus φ k - lamMinus φ k‖ ≤ 2 * Rm := fun k =>
    hball2 k _ _ ((hsp.1 k).1 (right_mem_segment ℝ _ _)) ((hsp.1 k).1 (left_mem_segment ℝ _ _))
  have hmk : ∀ k, ‖muSeq φ k - lamDot φ k‖ ≤ 2 * Rm := fun k =>
    hball2 k _ _ (hsp.1 k).2.1 (hsp.1 k).2.2.2.1
  set mass : ℤ → ℝ := fun k => ‖lamPlus φ k - lamMinus φ k‖ + ‖muSeq φ k - tauN φ k‖ with hmass
  have hm0 : ∀ k, 0 ≤ mass k := fun k => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hfinS : ∀ F : Finset ℤ, ∑ k ∈ F, (japaneseBracket k * mass k) ^ 2 ≤ S := by
    intro F
    rw [hS]
    exact mass_sum φ hφW Rm Ca Γ Cb Ng Nb hRm0 hgk hmk hid ha hgF hmF F
  have hs : Summable (fun k : ℤ => (japaneseBracket k * mass k) ^ 2) :=
    summable_of_sum_le (fun k => sq_nonneg _) hfinS
  have hts : (∑' k : ℤ, (japaneseBracket k * mass k) ^ 2) ≤ S := hs.tsum_le_of_sum_le hfinS
  have hbr := ksn013_bracket_pos n
  have hjb := ksn013_bracket_le_japanese n
  constructor
  · have hβ := hK Cβ hCβ.le mass hm0 S hs hts n (betaSum n φ) (fun m => offDiagonalBeta n m φ)
      (hasSum_offDiagonalBeta_betaSum n φ hφS) (fun m => by
        have h := (hVb φ hxO.2).2.2 n m
        rwa [norm_gk151BetaMass38] at h)
    refine hβ.trans ?_
    calc K * Cβ * Real.sqrt S / japaneseBracket n ≤ K * Cβ * Real.sqrt S / bracket n :=
          div_le_div_of_nonneg_left (by positivity) hbr hjb
      _ ≤ max (K * Cβ * Real.sqrt S) (Real.sqrt S) / bracket n :=
          div_le_div_of_nonneg_right (le_max_left _ _) hbr.le
  · have hp := mass_pointwise mass hm0 S hs hts n
    have hj := jb_pos n
    have h1 : mass n ≤ Real.sqrt S / japaneseBracket n := by
      rw [le_div_iff₀ hj, mul_comm]; exact hp
    calc mass n ≤ Real.sqrt S / japaneseBracket n := h1
      _ ≤ Real.sqrt S / bracket n := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hbr hjb
      _ ≤ max (K * Cβ * Real.sqrt S) (Real.sqrt S) / bracket n :=
          div_le_div_of_nonneg_right (le_max_right _ _) hbr.le

end
end NlsGge.ThirdConsultation.KSN012L
