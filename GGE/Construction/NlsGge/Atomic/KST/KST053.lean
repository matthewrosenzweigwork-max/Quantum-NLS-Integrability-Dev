import Mathlib
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST031
import NlsGge.Atomic.KST.KST032
import NlsGge.Atomic.KST.KST047
import NlsGge.Atomic.KST.KST049
import NlsGge.Atomic.KST.KST050
import NlsGge.Atomic.KST.KST051
import NlsGge.Atomic.KST.KST059
import NlsGge.GK38.Lib.CircleArgument
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST047Host

                                                                                                        
                                                                                                    
                                                                                                                   
                                                                                               
                                                                                                                
                                                                                                                      
                                                                                                                    
                                                                                                                           
                                                                 
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open NlsGge.Atomic.KST004
open NlsGge.Atomic.KST059
open NlsGge.GK38
open NlsGge.Atomic.KST (SlowWeight)
open Filter

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

namespace KST053S

theorem ball_mono (w : ℤ → ℝ) (R R' : ℝ) (h0 : 0 ≤ R) (h : R ≤ R') :
    physicalComponentBall w R ⊆ physicalComponentBall w R' := by
  intro φ hφ channel
  refine (hφ channel).trans ?_
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ h0 h 2)

theorem rootRadius_eq (b c : ℂ → ℂ) (σ : ℂ) (h : ‖b σ‖ = ‖c σ‖) :
    rootRadius b c σ = ‖b σ‖ := by
  unfold rootRadius
  rw [norm_mul, ← h, Real.sqrt_mul_self (norm_nonneg _)]

theorem pair_cases {x y u v : ℂ} (h : ({x, y} : Multiset ℂ) = {u, v}) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons] at h
  rcases Multiset.cons_eq_cons.1 h with ⟨h1, h2⟩ | ⟨-, cs, h2, h3⟩
  · exact Or.inl ⟨h1, Multiset.singleton_inj.1 h2⟩
  · have hu : u ∈ ({y} : Multiset ℂ) := by rw [h2]; exact Multiset.mem_cons_self _ _
    have hx : x ∈ ({v} : Multiset ℂ) := by rw [h3]; exact Multiset.mem_cons_self _ _
    exact Or.inr ⟨Multiset.mem_singleton.1 hx, (Multiset.mem_singleton.1 hu).symm⟩

/-- Core coefficient/gap comparison at one index above the diagonal threshold. -/
theorem b_le_gap (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hw : UnboundedWeight w) (φ : Potential)
    (hφ : φ ∈ physicalComponentBall w (2*M)) (ε : ℝ)
    (hreal : RealForm ε (periodicPair φ))
    (n : ℤ) (hn : diagonalThreshold w M ≤ n.natAbs) :
    ‖b φ n (diagonalZero n φ)‖ = ‖c φ n (diagonalZero n φ)‖ ∧
    ‖b φ n (diagonalZero n φ)‖ ≤ ‖actualGapSequence (periodicPair φ) n‖ := by
  obtain ⟨-, -, hnorm, hratio⟩ := kst051 w M hM hw φ hφ ε hreal n hn
  refine ⟨hnorm, ?_⟩
  set σ := diagonalZero n φ with hσdef
  by_cases hb0 : b φ n σ = 0
  · rw [hb0, norm_zero]; exact norm_nonneg _
  · have hc0 : c φ n σ ≠ 0 := by
      intro h0
      apply hb0
      rw [← norm_eq_zero, hnorm, h0, norm_zero]
    obtain ⟨-, hall⟩ := (kst031 w M hM hw).2.1
    obtain ⟨hSC, -, hzero⟩ := hall φ hφ n hn
    obtain ⟨-, -, hmem, hfix, -⟩ := kst032 w M hM hw φ hφ n hn
    have hr1 : ‖c φ n σ / b φ n σ‖ = 1 := hratio hb0
    have hBal : Balanced n (a φ n) (b φ n) (c φ n) σ := by
      refine ⟨hSC, hfix, ?_, mul_ne_zero hb0 hc0, ?_, ?_⟩
      · simpa [dist_eq_norm] using Metric.mem_closedBall.1 hmem
      · rw [hr1]; norm_num
      · rw [hr1]; norm_num
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_pow_nat_eq (b φ n σ * c φ n σ) (by norm_num : 0 < 2)
    obtain ⟨q, hq, hqσ, hqall⟩ := kst049 n (a φ n) (b φ n) (c φ n) σ ξ hBal hξ
    obtain ⟨xp, xm, -, -, hdet, hlow, -⟩ :=
      kst050 n (a φ n) (b φ n) (c φ n) σ ξ hBal hξ q hq hqσ
        (fun z hz => (hqall z hz).1) (fun z hz => (hqall z hz).2.2.2)
    rw [rootRadius_eq _ _ _ hnorm] at hlow
    have hms : ({xp, xm} : Multiset ℂ) =
        {lamMinus (periodicPair φ) n, lamPlus (periodicPair φ) n} := hdet.symm.trans hzero
    have hgap : ‖xp - xm‖ = ‖actualGapSequence (periodicPair φ) n‖ := by
      have hunf : actualGapSequence (periodicPair φ) n =
          lamPlus (periodicPair φ) n - lamMinus (periodicPair φ) n := rfl
      rcases pair_cases hms with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hunf, norm_sub_rev]
      · rw [h1, h2, hunf]
    rw [← hgap]
    exact hlow

theorem diagonalThreshold_le_adaptedThreshold (w : ℤ → ℝ) (M : ℝ) :
    diagonalThreshold w M ≤ adaptedThreshold w M := by
  unfold adaptedThreshold
  by_cases h : ∃ N : ℕ, adaptedCutoffCondition w M N
  · rw [dif_pos h]; exact (Nat.find_spec h).1
  · rw [dif_neg h]

theorem productWeight_even (w v : ℤ → ℝ) (Cw : ℝ) (hw : SlowWeight w Cw)
    (hv : SecondaryWeight v) (k : ℤ) :
    productWeight w v (-k) = productWeight w v k := by
  unfold productWeight
  rw [hw.even k, hv.1.2.1 k]

/-- Above the adapted threshold the two adapted coefficients are controlled by the two gaps. -/
theorem tail_term_le (w v : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M) (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (hv : SecondaryWeight v) (φ : Potential)
    (hφ : φ ∈ physicalComponentBall w (2*M)) (ε : ℝ)
    (hreal : RealForm ε (periodicPair φ)) (m : ℤ)
    (hm : adaptedThreshold w M < m.natAbs) :
    ENNReal.ofReal (productWeight w v (2*m) ^ 2 *
      (‖adaptedCoefficients (adaptedThreshold w M) φ true m‖ ^ 2 +
        ‖adaptedCoefficients (adaptedThreshold w M) φ false m‖ ^ 2)) ≤
    ENNReal.ofReal (productWeight w v (2*(-m)) ^ 2 *
      ‖actualGapSequence (periodicPair φ) (-m)‖ ^ 2) +
    ENNReal.ofReal (productWeight w v (2*m) ^ 2 *
      ‖actualGapSequence (periodicPair φ) m‖ ^ 2) := by
  have hUnb : UnboundedWeight w := ⟨⟨hw.one_le, hw.even, hw.radial_mono⟩, hunbounded⟩
  have hdiag := diagonalThreshold_le_adaptedThreshold w M
  have hnot : ¬ m.natAbs ≤ adaptedThreshold w M := not_le.2 hm
  have h1 := b_le_gap w M hM hUnb φ hφ ε hreal m (hdiag.trans hm.le)
  have h2 := b_le_gap w M hM hUnb φ hφ ε hreal (-m)
    (hdiag.trans (by rw [Int.natAbs_neg]; exact hm.le))
  have hE : productWeight w v (2*(-m)) = productWeight w v (2*m) := by
    rw [show 2*(-m) = -(2*m) by ring]
    exact productWeight_even w v Cw hw hv _
  have htrue : adaptedCoefficients (adaptedThreshold w M) φ true m =
      c φ (-m) (diagonalZero (-m) φ) := by
    simp [adaptedCoefficients, hnot]
  have hfalse : adaptedCoefficients (adaptedThreshold w M) φ false m =
      b φ m (diagonalZero m φ) := by
    simp [adaptedCoefficients, hnot]
  rw [htrue, hfalse, hE, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hc : ‖c φ (-m) (diagonalZero (-m) φ)‖ ≤ ‖actualGapSequence (periodicPair φ) (-m)‖ :=
    h2.1 ▸ h2.2
  have hb : ‖b φ m (diagonalZero m φ)‖ ≤ ‖actualGapSequence (periodicPair φ) m‖ := h1.2
  have hc2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hw2 : 0 ≤ productWeight w v (2*m) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hc2 hw2, mul_le_mul_of_nonneg_left hb2 hw2]

end KST053S

theorem kst053 (w v : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (hv : SecondaryWeight v) (φ : Potential)
    (hφ : φ ∈ physicalComponentBall w M) (ε : ℝ)
    (hreal : RealForm ε (periodicPair φ))
    (hgaps : weightedGapEnergy (productWeight w v)
      (actualGapSequence (periodicPair φ)) < ⊤) :
  (∀ n : ℤ, adaptedThreshold w M < n.natAbs →
    ‖b φ n (diagonalZero n φ)‖ = ‖c φ n (diagonalZero n φ)‖ ∧
    ‖b φ n (diagonalZero n φ)‖ ≤ ‖actualGapSequence (periodicPair φ) n‖) ∧
  rawEnergy (productWeight w v)
    (adaptedCoefficients (adaptedThreshold w M) φ) < ⊤ := by
  have hUnb : UnboundedWeight w := ⟨⟨hw.one_le, hw.even, hw.radial_mono⟩, hunbounded⟩
  have hφ2 : φ ∈ physicalComponentBall w (2*M) :=
    KST053S.ball_mono w M (2*M) (by linarith) (by linarith) hφ
  have hdiag := KST053S.diagonalThreshold_le_adaptedThreshold w M
  refine ⟨fun n hn => KST053S.b_le_gap w M hM hUnb φ hφ2 ε hreal n (hdiag.trans hn.le), ?_⟩
  set N := adaptedThreshold w M with hNdef
  let f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal
    (productWeight w v (2*n) ^ 2 * ‖actualGapSequence (periodicPair φ) n‖ ^ 2)
  have hf : ∑' n, f n < ⊤ := hgaps
  let F : ℤ → ℝ≥0∞ := fun m => if m.natAbs ≤ N then ENNReal.ofReal
    (productWeight w v (2*m) ^ 2 *
      (‖adaptedCoefficients N φ true m‖ ^ 2 + ‖adaptedCoefficients N φ false m‖ ^ 2)) else 0
  have hpt : ∀ m : ℤ, ENNReal.ofReal (productWeight w v (2*m) ^ 2 *
      (‖adaptedCoefficients N φ true m‖ ^ 2 + ‖adaptedCoefficients N φ false m‖ ^ 2)) ≤
      F m + (f (-m) + f m) := by
    intro m
    by_cases hm : m.natAbs ≤ N
    · simp only [F, if_pos hm]
      exact le_self_add
    · simp only [F, if_neg hm, zero_add]
      exact KST053S.tail_term_le w v Cw M hM hw hunbounded hv φ hφ2 ε hreal m (not_le.1 hm)
  have hFfin : ∑' m, F m < ⊤ := by
    have hz : ∀ m ∉ Finset.Icc (-(N : ℤ)) N, F m = 0 := by
      intro m hm
      have : ¬ m.natAbs ≤ N := by
        simp only [Finset.mem_Icc] at hm
        omega
      simp [F, this]
    rw [tsum_eq_sum hz]
    refine ENNReal.sum_lt_top.2 (fun m _ => ?_)
    simp only [F]
    split_ifs
    · exact ENNReal.ofReal_lt_top
    · exact ENNReal.zero_lt_top
  have hneg : ∑' m, f (-m) = ∑' m, f m := (Equiv.neg ℤ).tsum_eq f
  calc rawEnergy (productWeight w v) (adaptedCoefficients N φ)
      ≤ ∑' m, (F m + (f (-m) + f m)) := ENNReal.tsum_le_tsum hpt
    _ = ∑' m, F m + (∑' m, f (-m) + ∑' m, f m) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ < ⊤ := by
        rw [hneg]
        exact ENNReal.add_lt_top.2 ⟨hFfin, ENNReal.add_lt_top.2 ⟨hf, hf⟩⟩

end NlsGge.ThirdConsultation.KST
end
