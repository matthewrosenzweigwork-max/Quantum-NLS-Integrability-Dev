import Mathlib
import NlsGge.Atomic.KSN.KSN018Ident
import NlsGge.Atomic.KSN.KSN018Pure
import NlsGge.Atomic.KSN.KSN018Sup3
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform0

/- KSN018 COEF PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN018Coef.lean.
   SUPPORT (no packet increment) for KSN-018: for ONE x ∈ PairScale N (φ = pairPotential N x), from
   * the per-label factor bounds with one constant K (the KSN-012/014/017 conclusion forms at φ): |ξ_n − 1|, |β_n|,
     |η_n^{±} − 1|, |δ_n⁻¹ − (−1)ⁿ| ≤ K/⟨n⟩;
   * the exact identities (cartZ_plus/minus, KSN-010 first conjunct) at φ;
   * finite-sum bounds CE1, CE2 for the two weighted remainders (the KSPS companions, transported):
       E1_n = τ_n − μ_n + (F1_n + F2_n)/2,  E2_n = antiDiscrim(μ_n) − i(−1)ⁿ(F1_n − F2_n),
     F1_n = raw true (−n), F2_n = raw false n (KSN-001 reflected signs),
   it proves Memℓp (storedSequence (N+1) (smoothingCoefficient N x)) 2 and ‖complexSmoothing N x‖ ≤ Kc·√(4(2‖x‖² + CE1 + CE2))·√2
   with Kc explicit in K. Route = Pro r15 L858 (KSN018Pure.pure_coeff per label; Fourier part ‖x‖ in weighted hᴺ). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem ksn018_bracket_one_le (n : ℤ) : 1 ≤ bracket n := le_max_left _ _

theorem ksn018_sw_nat (N : ℕ) (n : ℤ) : scaleWeight (N : ℝ) n = bracket n ^ N := by
  unfold scaleWeight; exact Real.rpow_natCast _ _

theorem ksn018_sw_succ (N : ℕ) (n : ℤ) : scaleWeight ((N : ℝ) + 1) n = bracket n ^ (N + 1) := by
  unfold scaleWeight
  rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring]
  exact Real.rpow_natCast _ _

theorem ksn018_bracket_neg (n : ℤ) : bracket (-n) = bracket n := by
  unfold bracket; rw [Int.natAbs_neg]

theorem ksn018_weighted_raw (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) (n : ℤ) :
    bracket n ^ N * ‖rawCoefficient (N : ℝ) x b n‖ = ‖x (b, n)‖ := by
  unfold rawCoefficient
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (ksn018_scaleWeight_pos _ _).le, ksn018_sw_nat]
  have h := pow_pos (lt_of_lt_of_le one_pos (ksn018_bracket_one_le n)) N
  field_simp

theorem ksn018_fibre_le (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) (F : Finset ℤ) (g : ℤ → ℤ)
    (hg : Function.Injective g) :
    ∑ n ∈ F, ‖x (b, g n)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.sum_rpow_le_norm_rpow hp x (F.map ⟨fun n => (b, g n), fun a c h => hg (by simpa using h)⟩)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Finset.sum_map, Function.Embedding.coeFn_mk] at h
  exact h

/-- Per-label weighted bound (both Boolean components). -/
theorem ksn018_label (N : ℕ) (x : PairScale (N : ℝ)) (K : ℝ) (hK : 0 ≤ K) (n : ℤ)
    (hξ : ‖xiN38 n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) - 1‖ ≤ K / bracket n)
    (hβ : ‖betaSum n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)‖ ≤ K / bracket n)
    (hη : ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) - 1‖ ≤ K / bracket n)
    (hδ : ‖(deltaFactor n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
        (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n))⁻¹ - (-1 : ℂ) ^ n‖ ≤ K / bracket n)
    (hcp : cartesianZExtended n 1 (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      gk16ActualScalarZPlus38 sourceF n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x))
    (hcm : cartesianZExtended n (-1) (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      gk16ActualScalarZMinus38 sourceF n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x))
    (hZ : ∀ a : ℤ, (a = 1 ∨ a = -1) → sourceZ n a (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      ((tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
          muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
        (a : ℂ) * Complex.I * antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
          (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) /
          (2 * deltaFactor n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
            (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n))) *
        eta n a (pairPotential (N : ℝ) (Nat.cast_nonneg N) x))
    (b : Bool) :
    bracket n ^ (N + 1) * ‖smoothingCoefficient N x b n‖ ≤
      (4 * (1 + ((2 + Real.exp K) * K + K)) ^ 4 * (1 + ((2 + Real.exp K) * K + K))) *
        (‖x (true, -n)‖ + ‖x (false, n)‖ +
          bracket n ^ (N + 1) * ‖tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
            muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n +
            (rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2‖ +
          bracket n ^ (N + 1) * ‖antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
              (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
            Complex.I * (-1 : ℂ) ^ n *
              (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n)‖) := by
  set φ := pairPotential (N : ℝ) (Nat.cast_nonneg N) x with hφ
  set w : ℝ := bracket n with hwdef
  have hw : 1 ≤ w := ksn018_bracket_one_le n
  have hw0 : 0 < w := by linarith
  set Ka : ℝ := (2 + Real.exp K) * K + K with hKa
  have hKa0 : 0 ≤ Ka := by positivity
  have hKle : K / w ≤ Ka / w := div_le_div_of_nonneg_right (by rw [hKa]; nlinarith [Real.exp_pos K]) hw0.le
  have hKw : K / w ≤ K := div_le_self hK hw
  have hexp : ∀ c : ℂ, ‖c‖ = 1 → ‖Complex.exp (c * betaSum n φ) - 1‖ ≤ Ka / w := by
    intro c hc
    have h1 : ‖c * betaSum n φ‖ ≤ K / w := by rw [norm_mul, hc, one_mul]; exact hβ
    have := NlsGge.ThirdConsultation.KSN018P.exp_sub_one_le _ (K / w) K h1 hKw
    refine this.trans ?_
    rw [hKa]
    have : (2 + Real.exp K) * (K / w) = ((2 + Real.exp K) * K) / w := by ring
    rw [this, add_div]
    have : 0 ≤ K / w := by positivity
    linarith
  set σ : ℂ := (-1 : ℂ) ^ n with hσ
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num
  have hσn : ‖σ‖ = 1 := by rw [hσ, norm_zpow, norm_neg, norm_one, one_zpow]
  have hraw1 : bracket n ^ N * ‖rawCoefficient (N : ℝ) x true (-n)‖ = ‖x (true, -n)‖ := by
    rw [← ksn018_weighted_raw N x true (-n), ksn018_bracket_neg]
  have hraw2 : bracket n ^ N * ‖rawCoefficient (N : ℝ) x false n‖ = ‖x (false, n)‖ :=
    ksn018_weighted_raw N x false n
  cases b
  · have hs := ksn018_smooth_false N x n hcp (by simpa using hZ 1 (Or.inl rfl))
    have key := NlsGge.ThirdConsultation.KSN018P.pure_coeff N w Ka hw hKa0 _ _ _ _ _ _ _ _
      (tauN φ n - muSeq φ n + (rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2)
      (antiDiscrim φ (muSeq φ n) - Complex.I * σ *
        (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n))
      (rawCoefficient (N : ℝ) x true (-n)) (rawCoefficient (N : ℝ) x false n) σ 1 hs (by ring) (by ring) rfl
      hσ2 hσn (by simp) (hξ.trans hKle) (by simpa using hexp Complex.I (by simp))
      ((hη 1 (Or.inl rfl)).trans hKle) (hδ.trans hKle)
    rw [hraw1, hraw2] at key
    exact key
  · have hs := ksn018_smooth_true N x n hcm (by simpa using hZ (-1) (Or.inr rfl))
    have key := NlsGge.ThirdConsultation.KSN018P.pure_coeff N w Ka hw hKa0 _ _ _ _ _ _ _ _
      (tauN φ n - muSeq φ n + (rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2)
      (antiDiscrim φ (muSeq φ n) - Complex.I * σ *
        (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n))
      (rawCoefficient (N : ℝ) x true (-n)) (rawCoefficient (N : ℝ) x false n) σ (-1) hs (by ring) (by ring) rfl
      hσ2 hσn (by simp) (hξ.trans hKle) (by simpa using hexp (-Complex.I) (by simp))
      ((hη (-1) (Or.inr rfl)).trans hKle) (hδ.trans hKle)
    rw [hraw1, hraw2] at key
    exact key

end
end NlsGge.ThirdConsultation.KSN
