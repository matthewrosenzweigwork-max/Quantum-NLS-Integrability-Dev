import Mathlib
import NlsGge.Atomic.KSN.KSN013Core
import NlsGge.Atomic.KSN.KSN012Host
import NlsGge.Atomic.KSN.KSN012B1
import NlsGge.Atomic.KSN.KSN012B2
import NlsGge.Atomic.KSN.KSN012Sup4
import NlsGge.Atomic.G2.G2026
import NlsGge.Atomic.G1.G1049
import NlsGge.ThirdConsultation.M.M032Host
import NlsGge.ThirdConsultation.M.MSchurBound

                                                                                              
                                                                                                                       
                                                                                                         
                                                                                                                    
                                                                                                                       
                                                                 
                                                                                                                 
                                                                                                                         
                                                                                                                        
                                                                                                               
                                                                                                                      
                                                                                                                
                                                                                                                  
                     
set_option autoImplicit false

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

/-- `potentialTailEnergy ≤ potentialCoefficientEnergy` (the domination inside the landed M032Tail proof). -/
theorem ksn013_tail_le_energy (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : PotPair) (N : ℕ) :
    NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy w φ N ≤
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ := by
  classical
  have hev : ∀ k : ℤ, w (-k) = w k := by
    obtain ⟨v, -, hve, -, hwv⟩ := hw
    intro k
    rw [hwv, hwv, hve]
    unfold NlsGge.Atomic.M.M054.indexWeight
    push_cast
    rw [abs_neg]
  have h1 : ∑' n : ℤ, ENNReal.ofReal (w (2 * n) ^ 2 *
      ‖NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ true (2 * n)‖ ^ 2) ≤
      NlsGge.ThirdConsultation.MTwoModeB.compEnergy w φ true := by
    unfold NlsGge.ThirdConsultation.MTwoModeB.compEnergy
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℤ => 2 * n)
      (fun a b h => by simpa using h)
      (fun k : ℤ => ENNReal.ofReal (w k ^ 2 *
        ‖NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ true k‖ ^ 2))
  have h2 : ∑' n : ℤ, ENNReal.ofReal (w (2 * n) ^ 2 *
      ‖NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ false (-2 * n)‖ ^ 2) ≤
      NlsGge.ThirdConsultation.MTwoModeB.compEnergy w φ false := by
    unfold NlsGge.ThirdConsultation.MTwoModeB.compEnergy
    have e : ∀ n : ℤ, ENNReal.ofReal (w (2 * n) ^ 2 *
        ‖NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ false (-2 * n)‖ ^ 2) =
        (fun k : ℤ => ENNReal.ofReal (w k ^ 2 *
          ‖NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ false k‖ ^ 2)) (-2 * n) := by
      intro n
      simp only
      have : (-2 * n : ℤ) = -(2 * n) := by ring
      rw [this, hev]
    rw [tsum_congr e]
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℤ => -2 * n)
      (fun a b h => by simpa using h)
      (fun k : ℤ => ENNReal.ofReal (w k ^ 2 *
        ‖NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ false k‖ ^ 2))
  have hle : NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy w φ N ≤
      ∑' n : ℤ, (ENNReal.ofReal (w (2 * n) ^ 2 *
          ‖NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ true (2 * n)‖ ^ 2) +
        ENNReal.ofReal (w (2 * n) ^ 2 *
          ‖NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ false (-2 * n)‖ ^ 2)) := by
    unfold NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy
    refine ENNReal.tsum_le_tsum fun n => ?_
    split_ifs
    · rw [← ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)), mul_add]
    · exact zero_le
  rw [ENNReal.tsum_add] at hle
  rw [NlsGge.ThirdConsultation.MTwoModeB.potentialEnergy_split]
  exact hle.trans (add_le_add h1 h2)

/-- `⟨k⟩ ≤ w(2k)` for every one-derivative weight. -/
theorem ksn013_bracket_le_weight (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (k : ℤ) : japaneseBracket k ^ 2 ≤ w (2 * k) ^ 2 := by
  obtain ⟨v, hv1, -, -, hwv⟩ := hw
  have hiw : NlsGge.Atomic.M.M054.indexWeight (2 * k) = 1 + 2 * |(k : ℝ)| := by
    unfold NlsGge.Atomic.M.M054.indexWeight
    push_cast
    rw [abs_mul, abs_two]
  have hw2 : 1 + 2 * |(k : ℝ)| ≤ w (2 * k) := by
    rw [hwv, hiw]
    have := hv1 (2 * k)
    have h0 : 0 ≤ 1 + 2 * |(k : ℝ)| := by positivity
    nlinarith
  have hb : japaneseBracket k ^ 2 = 1 + (k : ℝ) ^ 2 := NlsGge.Atomic.KSN011.br_sq k
  rw [hb]
  have hk : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
  have h0 : 0 ≤ 1 + 2 * |(k : ℝ)| := by positivity
  have h3 : (1 + 2 * |(k : ℝ)|) ^ 2 ≤ w (2 * k) ^ 2 := pow_le_pow_left₀ h0 hw2 2
  nlinarith [abs_nonneg (k : ℝ)]

/-- Complex M-032 with B1: a uniform high-mode gap bound on every H¹ ball (conditional on M-032's conclusion). -/
theorem ksn013_gap_high
    (hM032 : ∀ (w : ℤ → ℝ), NlsGge.ThirdConsultation.M.OneDerivativeWeight w → ∀ (N : ℕ) (φ : PotPair),
      φ ∈ gkW → NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤ →
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight (N : ℤ) →
      NlsGge.ThirdConsultation.MTwoMode.complexGapTailEnergy w φ N ≤
        6 * NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy w φ N +
        ENNReal.ofReal (1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 6 /
          NlsGge.Atomic.M.M054.indexWeight (N : ℤ))) :
    ∀ H : ℝ, 0 ≤ H → ∃ (N : ℕ) (Γ : ℝ), ∀ x : PairScale 1, ‖x‖ ≤ H →
      pairPotential 1 (by norm_num) x ∈ gkW → ∀ k : ℤ, N ≤ k.natAbs →
        japaneseBracket k ^ 2 * ‖gamma2 (pairPotential 1 (by norm_num) x) k‖ ≤ Γ := by
  obtain ⟨w₁, hw₁, Cb, hCb⟩ := KSN012B1_main
  intro H hH
  set E0 : ℝ := max Cb 0 * H ^ 2 with hE0
  have hE00 : 0 ≤ E0 := by positivity
  set Γ : ℝ := 6 * E0 + 1152 * E0 ^ 3 with hΓ
  have hΓ0 : 0 ≤ Γ := by positivity
  refine ⟨⌈8 * E0⌉₊, Γ, fun x hx hW k hk => ?_⟩
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
  have hterm : ENNReal.ofReal (w₁ (2 * k) ^ 2 * ‖NlsGge.GKDefinitionDesign.gap φ k‖ ^ 2) ≤
      ENNReal.ofReal Γ := by
    refine le_trans ?_ hgapT
    unfold NlsGge.ThirdConsultation.MTwoMode.complexGapTailEnergy
    have := ENNReal.le_tsum (f := fun n : ℤ => if ⌈8 * E0⌉₊ ≤ n.natAbs then
      ENNReal.ofReal (w₁ (2 * n) ^ 2 * ‖NlsGge.GKDefinitionDesign.gap φ n‖ ^ 2) else 0) k
    simpa only [if_pos hk] using this
  have hterm' := (ENNReal.ofReal_le_ofReal_iff hΓ0).mp hterm
  have hg2 : ‖gamma2 φ k‖ = ‖NlsGge.GKDefinitionDesign.gap φ k‖ ^ 2 := by
    rw [gamma2_value38 φ hW k, norm_pow]
    rfl
  rw [hg2]
  calc japaneseBracket k ^ 2 * ‖NlsGge.GKDefinitionDesign.gap φ k‖ ^ 2
      ≤ w₁ (2 * k) ^ 2 * ‖NlsGge.GKDefinitionDesign.gap φ k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (ksn013_bracket_le_weight w₁ hw₁ k) (sq_nonneg _)
    _ ≤ Γ := hterm'

theorem ksn013_bracket_le_japanese (n : ℤ) : bracket n ≤ japaneseBracket n := by
  unfold bracket japaneseBracket
  have hm : ((n.natAbs : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have h0 : 0 ≤ max 1 ((n.natAbs : ℕ) : ℝ) := le_trans zero_le_one (le_max_left _ _)
  rw [← Real.sqrt_sq h0]
  apply Real.sqrt_le_sqrt
  rcases max_cases 1 ((n.natAbs : ℕ) : ℝ) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; nlinarith [sq_nonneg (n : ℝ)]
  · rw [h, hm]; linarith

theorem ksn013_bracket_pos (n : ℤ) : 0 < bracket n :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

theorem ksn013_sourceBetaW_gkW {φ : PotPair} (h : φ ∈ sourceBetaW) : φ ∈ gkW :=
  sourceFamily.W_gk (sourceFamily.V_W h)

/-- Local data around a point of sourceBetaW: one common isolating geometry on an L²-open neighbourhood and, for
    each H¹ bound, a uniform bound for the G2-026 coefficients and for ⟨k⟩²|γ_k²|. -/
theorem ksn013_local_bounds
    (hgap : ∀ H : ℝ, 0 ≤ H → ∃ (N : ℕ) (Γ : ℝ), ∀ x : PairScale 1, ‖x‖ ≤ H →
      pairPotential 1 (by norm_num) x ∈ gkW → ∀ k : ℤ, N ≤ k.natAbs →
        japaneseBracket k ^ 2 * ‖gamma2 (pairPotential 1 (by norm_num) x) k‖ ≤ Γ)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
    ∃ O : Set PotPair, IsOpen O ∧ φ₀ ∈ O ∧ O ⊆ sourceBetaW ∧
      ∃ (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ),
        IsolatingGeometry38 C R c J ∧ (∀ φ ∈ O, IsolatingSpectral38 φ C R) ∧
        ∀ H : ℝ, 0 ≤ H → ∃ Aa Γ : ℝ, ∀ x : PairScale 1, ‖x‖ ≤ H →
          pairPotential 1 (by norm_num) x ∈ O →
            (∀ k, ‖a5CriticalA38 k (pairPotential 1 (by norm_num) x)‖ ≤ Aa) ∧
            (∀ k, japaneseBracket k ^ 2 * ‖gamma2 (pairPotential 1 (by norm_num) x) k‖ ≤ Γ) := by
  have hW₀ : φ₀ ∈ gkW := ksn013_sourceBetaW_gkW hφ₀
  obtain ⟨V1, hV1, -, hV1o, -, C, R, c, J, hgeom, hspec⟩ := local_isolatingFamily_common38 φ₀ hW₀
  obtain ⟨U2, hU2o, hφU2, -, Ca, -, hU2⟩ := G2_026 φ₀ hW₀
  have hVo : IsOpen sourceBetaW := sourceFamily.V_open
  refine ⟨V1 ∩ U2 ∩ sourceBetaW, (hV1o.inter hU2o).inter hVo,
    ⟨⟨mem_of_mem_nhds hV1, hφU2⟩, hφ₀⟩, fun φ hφ => hφ.2, C, R, c, J, hgeom,
    fun φ hφ => hspec φ hφ.1.1, ?_⟩
  intro H hH
  obtain ⟨N, Γh, hgapN⟩ := hgap H hH
  set Rm : ℝ := Real.pi / 4 + ∑ k ∈ Finset.Icc (-(J : ℤ)) J, R k with hRm
  have hRpos : ∀ k, 0 < R k := fun k => (hgeom.1 k).1
  have hsum0 : 0 ≤ ∑ k ∈ Finset.Icc (-(J : ℤ)) J, R k :=
    Finset.sum_nonneg (fun k _ => (hRpos k).le)
  have hRle : ∀ k, R k ≤ Rm := by
    intro k
    by_cases hk : (J : ℤ) < |k|
    · rw [(hgeom.2.2.2.2 k hk).2.1]
      linarith
    · push_neg at hk
      have hmem : k ∈ Finset.Icc (-(J : ℤ)) J := Finset.mem_Icc.mpr (abs_le.mp hk)
      have := Finset.single_le_sum (fun j _ => (hRpos j).le) hmem
      linarith [Real.pi_pos]
  set Γ : ℝ := max Γh 0 + (1 + (N : ℝ) ^ 2) * (2 * Rm) ^ 2 with hΓ
  refine ⟨Real.sqrt Ca, Γ, fun x hx hxO => ?_⟩
  set φ := pairPotential 1 (by norm_num) x with hφdef
  have hφW : φ ∈ gkW := ksn013_sourceBetaW_gkW hxO.2
  have hsp : IsolatingSpectral38 φ C R := hspec φ hxO.1.1
  obtain ⟨-, hsumA, hboundA⟩ := hU2 φ hxO.1.2
  have ha : ∀ k, ‖a5CriticalA38 k φ‖ ≤ Real.sqrt Ca := by
    intro k
    have h1 : ‖a5CriticalA38 k φ‖ ^ 2 ≤ Ca :=
      (hsumA.le_tsum k (fun j _ => sq_nonneg _)).trans hboundA
    have := Real.abs_le_sqrt h1
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hΓk : ∀ k, japaneseBracket k ^ 2 * ‖gamma2 φ k‖ ≤ Γ := by
    intro k
    have hlowpart : 0 ≤ (1 + (N : ℝ) ^ 2) * (2 * Rm) ^ 2 := by positivity
    by_cases hk : N ≤ k.natAbs
    · have := hgapN x hx hφW k hk
      linarith [le_max_left Γh 0]
    · push_neg at hk
      have hjb : japaneseBracket k ^ 2 ≤ 1 + (N : ℝ) ^ 2 := by
        rw [NlsGge.Atomic.KSN011.br_sq]
        have h1 : (k : ℝ) ^ 2 = ((k.natAbs : ℕ) : ℝ) ^ 2 := by
          rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
        have h2 : ((k.natAbs : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk.le
        have h3 : ((k.natAbs : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2
        linarith
      have hseg := (hsp.1 k).1
      have hlp : lamPlus φ k ∈ ball (C k) (R k) := hseg (right_mem_segment ℝ _ _)
      have hlm : lamMinus φ k ∈ ball (C k) (R k) := hseg (left_mem_segment ℝ _ _)
      have hdiff : ‖lamPlus φ k - lamMinus φ k‖ ≤ 2 * Rm := by
        have e1 := mem_ball_iff_norm.mp hlp
        have e2 := mem_ball_iff_norm.mp hlm
        have : ‖lamPlus φ k - lamMinus φ k‖ ≤ ‖lamPlus φ k - C k‖ + ‖lamMinus φ k - C k‖ := by
          have h := norm_sub_le (lamPlus φ k - C k) (lamMinus φ k - C k)
          simpa only [sub_sub_sub_cancel_right] using h
        linarith [hRle k]
      have hg2 : ‖gamma2 φ k‖ ≤ (2 * Rm) ^ 2 := by
        rw [gamma2_value38 φ hφW k, norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hdiff 2
      have hjb0 : 0 ≤ japaneseBracket k ^ 2 := sq_nonneg _
      have := mul_le_mul hjb hg2 (norm_nonneg _) (by positivity)
      linarith [le_max_right Γh 0]
  exact ⟨ha, hΓk⟩

/-- Local data around a point of sourceBetaW: one common isolating geometry on an L²-open neighbourhood, and for each
    H¹ bound one constant for the full disc estimate. -/
theorem ksn013_local
    (hgap : ∀ H : ℝ, 0 ≤ H → ∃ (N : ℕ) (Γ : ℝ), ∀ x : PairScale 1, ‖x‖ ≤ H →
      pairPotential 1 (by norm_num) x ∈ gkW → ∀ k : ℤ, N ≤ k.natAbs →
        japaneseBracket k ^ 2 * ‖gamma2 (pairPotential 1 (by norm_num) x) k‖ ≤ Γ)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
    ∃ O : Set PotPair, IsOpen O ∧ φ₀ ∈ O ∧ O ⊆ sourceBetaW ∧
      ∃ (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ),
        IsolatingGeometry38 C R c J ∧ (∀ φ ∈ O, IsolatingSpectral38 φ C R) ∧
        ∀ H : ℝ, 0 ≤ H → ∃ A : ℝ, 0 ≤ A ∧ ∀ x : PairScale 1, ‖x‖ ≤ H →
          pairPotential 1 (by norm_num) x ∈ O →
          ∀ n : ℤ, ∀ z ∈ Metric.closedBall (C n) (R n),
            Multipliable (fun k : ℤ =>
              criticalOmittedFactor n k (pairPotential 1 (by norm_num) x) z) ∧
            (∀ k : ℤ, k ≠ n →
              stdRoot38 (tauN (pairPotential 1 (by norm_num) x) k)
                (gamma2 (pairPotential 1 (by norm_num) x) k) z ≠ 0) ∧
            ‖criticalOmittedProduct n (pairPotential 1 (by norm_num) x) z - 1‖
              ≤ A / bracket n := by
  obtain ⟨O, hOo, hφO, hOsub, C, R, c, J, hgeom, hspec, hbd⟩ := ksn013_local_bounds hgap φ₀ hφ₀
  refine ⟨O, hOo, hφO, hOsub, C, R, c, J, hgeom, hspec, fun H hH => ?_⟩
  obtain ⟨Aa, Γ, hbx⟩ := hbd H hH
  obtain ⟨A0, hA0, hest⟩ := ksn013_disc_estimate C R c J hgeom Aa Γ
  refine ⟨A0, hA0, fun x hx hxO n z hz => ?_⟩
  obtain ⟨ha, hΓk⟩ := hbx x hx hxO
  obtain ⟨hm, hnv, hb⟩ := hest _ (ksn013_sourceBetaW_gkW (hOsub hxO)) (hspec _ hxO) ha hΓk n z hz
  refine ⟨hm, hnv, hb.trans ?_⟩
  exact div_le_div_of_nonneg_left hA0 (ksn013_bracket_pos n) (ksn013_bracket_le_japanese n)

/-- Weighted bound giving membership of a real H¹ ball in the landed G1-049 ellipsoid. -/
theorem ksn013_weight_bound (m : ℤ) : 1 + (m : ℝ) ^ 2 ≤ 2 * scaleWeight 1 m ^ 2 := by
  have hw : scaleWeight 1 m = max 1 |(m : ℝ)| := by
    unfold scaleWeight bracket
    rw [Real.rpow_one, Nat.cast_natAbs, Int.cast_abs]
  rw [hw]
  rcases le_total 1 |(m : ℝ)| with h | h
  · rw [max_eq_right h]
    have : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
    nlinarith
  · rw [max_eq_left h]
    have : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
    have h0 := abs_nonneg (m : ℝ)
    nlinarith

theorem ksn013_rawL2_mem_ellipsoid (B : ℝ) (b : Bool) (x : PairScale 1) (hx : ‖x‖ ≤ B) :
    KSN012B2_rawL2 b x ∈ NlsGge.Atomic.G1049S1.ellipsoid (Real.sqrt 2 * B) := by
  intro F
  have hsq : HasSum (fun j : Bool × ℤ => ‖x j‖ ^ 2) (‖x‖ ^ 2) := by
    have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hF : ∑ n ∈ F, ‖x (b, n)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have e : ∑ n ∈ F, ‖x (b, n)‖ ^ 2 =
        ∑ j ∈ F.map ⟨Prod.mk b, Prod.mk_right_injective b⟩, ‖x j‖ ^ 2 := by
      rw [Finset.sum_map]; rfl
    rw [e]
    exact sum_le_hasSum _ (fun j _ => sq_nonneg _) hsq
  have hterm : ∀ n : ℤ, (1 + (n : ℝ) ^ 2) * ‖KSN012B2_rawL2 b x n‖ ^ 2 ≤ 2 * ‖x (b, n)‖ ^ 2 := by
    intro n
    have hs : 0 < scaleWeight 1 n := by
      unfold scaleWeight bracket
      rw [Real.rpow_one]
      exact lt_of_lt_of_le one_pos (le_max_left _ _)
    have hval : ‖KSN012B2_rawL2 b x n‖ = ‖x (b, n)‖ / scaleWeight 1 n := by
      change ‖rawCoefficient 1 x b n‖ = _
      rw [rawCoefficient, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
    rw [hval, div_pow]
    have hwb := ksn013_weight_bound n
    have hs2 : 0 < scaleWeight 1 n ^ 2 := by positivity
    rw [mul_div_assoc', div_le_iff₀ hs2]
    have h0 : 0 ≤ ‖x (b, n)‖ ^ 2 := sq_nonneg _
    nlinarith
  have hB2 : ‖x‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  calc ∑ n ∈ F, (1 + (n : ℝ) ^ 2) * ‖KSN012B2_rawL2 b x n‖ ^ 2
      ≤ ∑ n ∈ F, 2 * ‖x (b, n)‖ ^ 2 := Finset.sum_le_sum (fun n _ => hterm n)
    _ = 2 * ∑ n ∈ F, ‖x (b, n)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * B ^ 2 := by linarith
    _ = (Real.sqrt 2 * B) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- A compact subset of sourceBetaW containing the image of each real H¹ ball. -/
theorem ksn013_realBall_compact (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : Set PotPair, IsCompact K ∧ K ⊆ sourceBetaW ∧
      ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → pairPotential 1 (by norm_num) x ∈ K := by
  set E := NlsGge.Atomic.G1049S1.ellipsoid (Real.sqrt 2 * B) with hEdef
  have hE : IsCompact E :=
    (NlsGge.Atomic.G1049S1.totallyBounded_ellipsoid (by positivity)).isCompact_of_isClosed
      (NlsGge.Atomic.G1049S1.isClosed_ellipsoid _)
  set K0 : Set PotPair := (physicalFourierL2.symm '' E) ×ˢ (physicalFourierL2.symm '' E) with hK0def
  have hK0 : IsCompact K0 :=
    (hE.image physicalFourierL2.symm.continuous).prod (hE.image physicalFourierL2.symm.continuous)
  set S : Set PotPair := {φ | ∃ x : PairScale 1, IsRealPair 1 x ∧ ‖x‖ ≤ B ∧
    pairPotential 1 (by norm_num) x = φ} with hSdef
  have hSK0 : S ⊆ K0 := by
    rintro φ ⟨x, -, hx, rfl⟩
    exact ⟨⟨KSN012B2_rawL2 true x, ksn013_rawL2_mem_ellipsoid B true x hx, rfl⟩,
      ⟨KSN012B2_rawL2 false x, ksn013_rawL2_mem_ellipsoid B false x hx, rfl⟩⟩
  set T : Set PotPair := {p | realSlice p.1 = p} with hTdef
  have hT : IsClosed T := isClosed_eq (realSlice.continuous.comp continuous_fst) continuous_id
  have hST : S ⊆ T := by
    rintro φ ⟨x, hxr, -, rfl⟩
    exact (sup4_pairPotential_eq_realSlice x hxr).symm
  refine ⟨closure S, hK0.of_isClosed_subset isClosed_closure (closure_minimal hSK0 hK0.isClosed),
    ?_, fun x hxr hx => subset_closure ⟨x, hxr, hx, rfl⟩⟩
  intro φ hφ
  have hφT : realSlice φ.1 = φ := closure_minimal hST hT hφ
  rw [← hφT]
  exact sourceFamily.V_real ⟨_, rfl⟩

/-- The corrected KSN-013 head, conditional only on the landed M-032 conclusion. -/
theorem KSN013_of_M032
    (hM032 : ∀ (w : ℤ → ℝ), NlsGge.ThirdConsultation.M.OneDerivativeWeight w → ∀ (N : ℕ) (φ : PotPair),
      φ ∈ gkW → NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤ →
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight (N : ℤ) →
      NlsGge.ThirdConsultation.MTwoMode.complexGapTailEnergy w φ N ≤
        6 * NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy w φ N +
        ENNReal.ofReal (1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 6 /
          NlsGge.Atomic.M.M054.indexWeight (N : ℤ))) :
  (∀ x₀ ∈ complexDomain 1 (by norm_num),
    ∃ (U : Set (PairScale 1)) (A : ℝ)
      (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ),
      IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ A ∧
      IsolatingGeometry38 C R c J ∧
      (∀ x ∈ U,
        IsolatingSpectral38 (pairPotential 1 (by norm_num) x) C R) ∧
      ∀ x ∈ U, ∀ n : ℤ,
        ∀ z ∈ Metric.closedBall (C n) (R n),
          Multipliable (fun k : ℤ =>
            criticalOmittedFactor n k (pairPotential 1 (by norm_num) x) z) ∧
          (∀ k : ℤ, k ≠ n →
            stdRoot38 (tauN (pairPotential 1 (by norm_num) x) k)
              (gamma2 (pairPotential 1 (by norm_num) x) k) z ≠ 0) ∧
          ‖criticalOmittedProduct n (pairPotential 1 (by norm_num) x) z - 1‖
            ≤ A / bracket n) ∧
  (∀ B : ℝ, 0 ≤ B →
    ∃ (A : ℝ) (m : ℕ)
      (V : Fin m → Set PotPair)
      (C : Fin m → ℤ → ℂ) (R : Fin m → ℤ → ℝ)
      (c : Fin m → ℝ) (J : Fin m → ℕ),
      0 ≤ A ∧
      (∀ i : Fin m,
        IsOpen (V i) ∧ V i ⊆ sourceBetaW ∧
        IsolatingGeometry38 (C i) (R i) (c i) (J i) ∧
        ∀ φ ∈ V i, IsolatingSpectral38 φ (C i) (R i)) ∧
      (∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B →
        ∃ i : Fin m, pairPotential 1 (by norm_num) x ∈ V i) ∧
      ∀ (i : Fin m) (x : PairScale 1),
        IsRealPair 1 x → ‖x‖ ≤ B →
        pairPotential 1 (by norm_num) x ∈ V i →
        ∀ n : ℤ, ∀ z ∈ Metric.closedBall (C i n) (R i n),
          Multipliable (fun k : ℤ =>
            criticalOmittedFactor n k (pairPotential 1 (by norm_num) x) z) ∧
          (∀ k : ℤ, k ≠ n →
            stdRoot38 (tauN (pairPotential 1 (by norm_num) x) k)
              (gamma2 (pairPotential 1 (by norm_num) x) k) z ≠ 0) ∧
          ‖criticalOmittedProduct n (pairPotential 1 (by norm_num) x) z - 1‖
            ≤ A / bracket n) := by
  have hgap := ksn013_gap_high hM032
  constructor
  · intro x₀ hx₀
    obtain ⟨O, hOo, hφO, hOsub, C, R, c, J, hgeom, hspec, hA⟩ :=
      ksn013_local hgap (pairPotential 1 (by norm_num) x₀) hx₀
    obtain ⟨A, hA0, hAest⟩ := hA (‖x₀‖ + 1) (by positivity)
    refine ⟨pairPotential 1 (by norm_num) ⁻¹' O ∩ ball x₀ 1, A, C, R, c, J,
      (hOo.preimage KSN012B2_main).inter isOpen_ball, ⟨hφO, mem_ball_self one_pos⟩,
      fun x hx => hOsub hx.1, hA0, hgeom, fun x hx => hspec _ hx.1, ?_⟩
    intro x hx n z hz
    have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have h1 := norm_sub_norm_le x x₀
      have h2 := mem_ball_iff_norm.mp hx.2
      linarith
    exact hAest x hxn hx.1 n z hz
  · intro B hB
    obtain ⟨K, hK, hKsub, hKmem⟩ := ksn013_realBall_compact B hB
    have hloc := fun φ : K => ksn013_local hgap φ.1 (hKsub φ.2)
    choose O hOo hφO hOsub C R c J hgeom hspec hA using hloc
    choose A hA0 hAest using fun φ : K => hA φ B hB
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun φ : K => O φ) hOo
      (fun φ hφ => mem_iUnion.mpr ⟨⟨φ, hφ⟩, hφO _⟩)
    let e : Fin t.card ≃ t := t.equivFin.symm
    refine ⟨∑ φ ∈ t, A φ, t.card, fun i => O (e i).1, fun i => C (e i).1, fun i => R (e i).1,
      fun i => c (e i).1, fun i => J (e i).1, Finset.sum_nonneg (fun φ _ => hA0 φ),
      fun i => ⟨hOo _, hOsub _, hgeom _, hspec _⟩, ?_, ?_⟩
    · intro x hxr hx
      have hmem := ht (hKmem x hxr hx)
      rw [mem_iUnion₂] at hmem
      obtain ⟨φ, hφt, hφx⟩ := hmem
      refine ⟨e.symm ⟨φ, hφt⟩, ?_⟩
      simpa only [Equiv.apply_symm_apply] using hφx
    · intro i x _ hx hxV n z hz
      obtain ⟨hm, hnv, hb⟩ := hAest (e i).1 x hx hxV n z hz
      refine ⟨hm, hnv, hb.trans ?_⟩
      exact div_le_div_of_nonneg_right
        (Finset.single_le_sum (fun φ _ => hA0 φ) (e i).2) (ksn013_bracket_pos n).le

end
end NlsGge.ThirdConsultation.KSN
