import Mathlib
import NlsGge.Atomic.KSN.KSN018Coef

/- KSN018 SUM PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN018Sum.lean.
   SUPPORT (no packet increment) for KSN-018: from the per-label hypotheses of KSN018Coef (for all labels, one K) and
   the finite-sum bounds CE1, CE2 of the two weighted remainders, the weighted coefficient sequence is in lp 2 and
   ‖complexSmoothing N x‖ ≤ √(2T), T = Kc²·(4·(‖x‖² + ‖x‖² + CE1 + CE2)). Fibrewise finite sums (KSPS017U0.sum_sq_le_fin),
   summable_prod_of_nonneg on Bool × ℤ, lp.norm_rpow_eq_tsum. No hypothesis added. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem ksn018_stored_norm (N : ℕ) (x : PairScale (N : ℝ)) (j : Bool × ℤ) :
    ‖storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x) j‖ =
      bracket j.2 ^ (N + 1) * ‖smoothingCoefficient N x j.1 j.2‖ := by
  unfold storedSequence
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ksn018_scaleWeight_pos _ _).le, ksn018_sw_succ]

theorem ksn018_smooth_l2 (N : ℕ) (x : PairScale (N : ℝ)) (K : ℝ) (hK : 0 ≤ K)
    (hξ : ∀ n : ℤ, ‖xiN38 n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) - 1‖ ≤ K / bracket n)
    (hβ : ∀ n : ℤ, ‖betaSum n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)‖ ≤ K / bracket n)
    (hη : ∀ n : ℤ, ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) - 1‖ ≤ K / bracket n)
    (hδ : ∀ n : ℤ, ‖(deltaFactor n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
        (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n))⁻¹ - (-1 : ℂ) ^ n‖ ≤ K / bracket n)
    (hcp : ∀ n : ℤ, cartesianZExtended n 1 (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      gk16ActualScalarZPlus38 sourceF n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x))
    (hcm : ∀ n : ℤ, cartesianZExtended n (-1) (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      gk16ActualScalarZMinus38 sourceF n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x))
    (hZ : ∀ n : ℤ, ∀ a : ℤ, (a = 1 ∨ a = -1) → sourceZ n a (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      ((tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
          muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
        (a : ℂ) * Complex.I * antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
          (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) /
          (2 * deltaFactor n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
            (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n))) *
        eta n a (pairPotential (N : ℝ) (Nat.cast_nonneg N) x))
    (CE1 CE2 : ℝ)
    (hE1 : ∀ F : Finset ℤ, ∑ n ∈ F, (bracket n ^ (N + 1) * ‖tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
            muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n +
            (rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2‖) ^ 2 ≤ CE1)
    (hE2 : ∀ F : Finset ℤ, ∑ n ∈ F, (bracket n ^ (N + 1) * ‖antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
              (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
            Complex.I * (-1 : ℂ) ^ n *
              (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n)‖) ^ 2 ≤ CE2) :
    Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
      ‖complexSmoothing N x‖ ≤ Real.sqrt (2 * ((4 * (1 + ((2 + Real.exp K) * K + K)) ^ 4 * (1 + ((2 + Real.exp K) * K + K))) ^ 2 *
        (((4 : ℕ) : ℝ) * (‖x‖ ^ 2 + ‖x‖ ^ 2 + CE1 + CE2)))) := by
  set Kc : ℝ := (4 * (1 + ((2 + Real.exp K) * K + K)) ^ 4 * (1 + ((2 + Real.exp K) * K + K))) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set T : ℝ := Kc ^ 2 * (((4 : ℕ) : ℝ) * (‖x‖ ^ 2 + ‖x‖ ^ 2 + CE1 + CE2)) with hT
  set f : Bool × ℤ → ℝ := fun j => ‖storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x) j‖ ^ 2 with hf
  have hf0 : 0 ≤ f := fun j => sq_nonneg _
  have hfib : ∀ (b : Bool) (F : Finset ℤ), ∑ n ∈ F, f (b, n) ≤ T := by
    intro b F
    simp only [hf, ksn018_stored_norm]
    refine NlsGge.ThirdConsultation.KSPS017U0.sum_sq_le_fin F _
      ![fun n => ‖x (true, -n)‖, fun n => ‖x (false, n)‖,
        fun n => bracket n ^ (N + 1) * ‖tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
            muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n +
            (rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2‖,
        fun n => bracket n ^ (N + 1) * ‖antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
              (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
            Complex.I * (-1 : ℂ) ^ n *
              (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n)‖]
      Kc hKc0 ?_ ![‖x‖ ^ 2, ‖x‖ ^ 2, CE1, CE2] ?_ |>.trans (le_of_eq ?_)
    · intro n _
      refine ⟨mul_nonneg (pow_nonneg (le_trans zero_le_one (ksn018_bracket_one_le n)) _) (norm_nonneg _), ?_⟩
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      have h := ksn018_label N x K hK n (hξ n) (hβ n) (hη n) (hδ n) (hcp n) (hcm n) (hZ n) b
      refine h.trans (le_of_eq ?_)
      ring
    · intro j
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        exact ksn018_fibre_le N x true F (fun n => -n) neg_injective
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
        exact ksn018_fibre_le N x false F id Function.injective_id
      · simp only [Fin.reduceFinMk, Matrix.cons_val]
        exact hE1 F
      · simp only [Fin.reduceFinMk, Matrix.cons_val]
        exact hE2 F
    · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      rw [hT]; ring
  have hsb : ∀ b : Bool, Summable (fun n : ℤ => f (b, n)) := fun b =>
    summable_of_sum_le (fun n => hf0 _) (hfib b)
  have htb : ∀ b : Bool, ∑' n : ℤ, f (b, n) ≤ T := fun b => (hsb b).tsum_le_of_sum_le (hfib b)
  have hs : Summable f := (summable_prod_of_nonneg hf0).2 ⟨hsb, (hasSum_fintype _).summable⟩
  have hmem : Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 := by
    refine memℓp_gen ?_
    refine hs.congr (fun j => ?_)
    simp only [hf, ENNReal.toReal_ofNat, Real.rpow_two]
  refine ⟨hmem, ?_⟩
  have hcs : complexSmoothing N x = ⟨storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x), hmem⟩ := by
    unfold complexSmoothing sequenceLift
    rw [dif_pos hmem]
  rw [hcs]
  have h0 := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num)
    (⟨storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x), hmem⟩ : PairScale ((N : ℝ) + 1))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h0
  have h1 : ∑' j : Bool × ℤ, f j ≤ 2 * T := by
    rw [hs.tsum_prod' hsb, tsum_fintype, Fintype.sum_bool]
    linarith [htb true, htb false]
  have h2 : ‖(⟨storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x), hmem⟩ : PairScale ((N : ℝ) + 1))‖ ^ 2
      ≤ 2 * T := by
    rw [h0]; exact h1
  have := Real.abs_le_sqrt h2
  rwa [abs_of_nonneg (norm_nonneg _)] at this

end
end NlsGge.ThirdConsultation.KSN
