import Mathlib
import NlsGge.Atomic.G1.G1036
import NlsGge.Atomic.G1.G1037Host
import NlsGge.Atomic.G1.G1037Sup1
import NlsGge.Atomic.G1.G1037Sup2
import NlsGge.Atomic.G1.G1037Sup3
import NlsGge.GK38.PairAnalyticDet
import NlsGge.GK38.PairRealBridge

                                                                                               
                                                                                                           
                                                                                                   
                                                                                                                   
                                                                                                                  
                                                                                                                 
                                                                                                              
                                                                                                             
                                             
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g37_partial_H1_decay (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 < K ∧ ∃ p : ℕ, ∀ φ : PotPair, pairSobolev (N : ℝ) φ → ∀ z : ℂ, 1 ≤ ‖z‖ →
      physicalSobolev 1 (wkbPartial N z φ) ∧
        physicalSobolevNorm 1 (wkbPartial N z φ) ≤
          ‖z‖⁻¹ * (K * (1 + pairSobolevNorm (N : ℝ) φ) ^ p) := by
  obtain ⟨C0, hC0, p0, hw⟩ := wkb_bound N N hN le_rfl
  refine ⟨((N : ℝ) + 1) * C0, by positivity, p0, ?_⟩
  intro φ hφ z hz
  have hX : 0 ≤ pairSobolevNorm (N : ℝ) φ := (pairSobolevNorm_ge N φ).1
  have hY : 0 ≤ (1 + pairSobolevNorm (N : ℝ) φ) ^ p0 := pow_nonneg (by linarith) _
  have hz0 : 0 < ‖z‖ := by linarith
  have hcoef : ∀ n : ℕ, 1 ≤ n → ‖((2 * Complex.I * z) ^ n)⁻¹‖ ≤ ‖z‖⁻¹ := by
    intro n hn
    rw [norm_inv, norm_pow]
    have h2 : ‖2 * Complex.I * z‖ = 2 * ‖z‖ := by simp [norm_mul]
    rw [h2]
    have h3 : ‖z‖ ≤ (2 * ‖z‖) ^ n :=
      calc ‖z‖ ≤ 2 * ‖z‖ := by linarith
        _ = (2 * ‖z‖) ^ 1 := (pow_one _).symm
        _ ≤ (2 * ‖z‖) ^ n := pow_le_pow_right₀ (by linarith) hn
    exact inv_anti₀ hz0 h3
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      physicalSobolev ((1 : ℕ) : ℝ) (((2 * Complex.I * z) ^ n)⁻¹ • wkbR φ n) ∧
      physicalSobolevNorm ((1 : ℕ) : ℝ) (((2 * Complex.I * z) ^ n)⁻¹ • wkbR φ n) ≤
        ‖z‖⁻¹ * (C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    obtain ⟨h1, h2⟩ := hw φ hφ n hn1 hn2
    obtain ⟨h3, h4⟩ := psn_mono (show 1 ≤ N + 1 - n by omega) h1
    refine ⟨g35_H1_cast _ (g35_H1_smul _ (g35_H1_nat _ h3)), ?_⟩
    rw [g36_psn_smul]
    exact mul_le_mul (hcoef n hn1) (h4.trans h2) (psn_nonneg 1 _) (inv_nonneg.2 hz0.le)
  obtain ⟨hs1, hs2⟩ := psn_sum 1 (Finset.Icc 1 N)
    (fun n => ((2 * Complex.I * z) ^ n)⁻¹ • wkbR φ n) (fun n hn => (hterm n hn).1)
  have hsum : ∑ n ∈ Finset.Icc 1 N,
      physicalSobolevNorm ((1 : ℕ) : ℝ) (((2 * Complex.I * z) ^ n)⁻¹ • wkbR φ n) ≤
      (N : ℝ) * (‖z‖⁻¹ * (C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0)) := by
    calc _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖z‖⁻¹ * (C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0) :=
          Finset.sum_le_sum (fun n hn => (hterm n hn).2)
      _ = (N : ℝ) * (‖z‖⁻¹ * (C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0)) := by simp
  have hcast : physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbPartial N z φ) =
      physicalSobolevNorm 1 (wkbPartial N z φ) := by rw [Nat.cast_one]
  unfold wkbPartial at hcast ⊢
  refine ⟨g35_H1_nat _ hs1, ?_⟩
  rw [← hcast]
  refine hs2.trans (hsum.trans ?_)
  have hnn : 0 ≤ ‖z‖⁻¹ * (C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0) :=
    mul_nonneg (inv_nonneg.2 hz0.le) (mul_nonneg hC0.le hY)
  nlinarith

theorem g37_J_norm_le (N : ℕ) (z : ℂ) (φ : PotPair) (A : ℝ)
    (hα : ∀ s : ℝ, ‖wkbAlpha N z φ s‖ ≤ A) :
    ‖∫ s in (0 : ℝ)..1, potRepFst38 φ s * wkbAlpha N z φ s‖ ≤ A * ‖φ.1‖ := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hα 0)
  have hgint : IntervalIntegrable (fun s => A * ‖potRepFst38 φ s‖) volume 0 1 :=
    (intervalIntegrable_norm_coverRep38_one φ.1).const_mul A
  have h1 : ‖∫ s in (0 : ℝ)..1, potRepFst38 φ s * wkbAlpha N z φ s‖ ≤
      ∫ s in (0 : ℝ)..1, A * ‖potRepFst38 φ s‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hgint
    refine Filter.Eventually.of_forall (fun s _ => ?_)
    rw [norm_mul]
    calc ‖potRepFst38 φ s‖ * ‖wkbAlpha N z φ s‖ ≤ ‖potRepFst38 φ s‖ * A :=
          mul_le_mul_of_nonneg_left (hα s) (norm_nonneg _)
      _ = A * ‖potRepFst38 φ s‖ := mul_comm _ _
  have h3 : ∫ s in (0 : ℝ)..1, A * ‖potRepFst38 φ s‖ ≤ A * ‖φ.1‖ := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_coverRep38_le_one φ.1) hA
  exact h1.trans h3

theorem g37_unif (N : ℕ) (hN : 1 ≤ N) (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 ≤ τ) :
    ∃ A K1 C1 : ℝ, 0 ≤ A ∧ 0 < K1 ∧ 0 < C1 ∧
      ∀ φ : PotPair, pairSobolev (N : ℝ) φ → pairSobolevNorm (N : ℝ) φ ≤ B →
      ∀ z : ℂ, |z.im| ≤ τ → 1 ≤ ‖z‖ →
        (∀ s : ℝ, ‖wkbAlpha N z φ s‖ ≤ A * ‖z‖⁻¹) ∧
        ‖wkbPhase N z φ 1‖ ≤ K1 ∧ ‖(wkbPhase N z φ 1)⁻¹‖ ≤ K1 ∧
        ‖wkbRemainder N z φ 1‖ ≤ C1 := by
  obtain ⟨C1, hC1, hmain⟩ := g36_s6_main N hN B τ hB hτ
  obtain ⟨K, hK, p, hdec⟩ := g37_partial_H1_decay N hN
  have hR : 0 ≤ ‖NlsGge.Analysis.reciprocalBracketL2‖ := norm_nonneg _
  have hB1 : 0 ≤ 1 + B := by linarith
  have hA0 : 0 ≤ ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p) :=
    mul_nonneg hR (mul_nonneg hK.le (pow_nonneg hB1 _))
  refine ⟨‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p),
    Real.exp (τ + ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p) * B), C1,
    hA0, Real.exp_pos _, hC1, ?_⟩
  intro φ hφ hnorm z hzτ hz
  have hz0 : 0 < ‖z‖ := by linarith
  have hX0 : 0 ≤ pairSobolevNorm (N : ℝ) φ := (pairSobolevNorm_ge N φ).1
  obtain ⟨hP, hnP⟩ := hdec φ hφ z hz
  obtain ⟨hn1, -⟩ := g36_s6_norm_le_pair N φ hφ
  have hpow : (1 + pairSobolevNorm (N : ℝ) φ) ^ p ≤ (1 + B) ^ p :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  set A := ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p) with hAdef
  have hα : ∀ s : ℝ, ‖wkbAlpha N z φ s‖ ≤ A * ‖z‖⁻¹ := by
    intro s
    refine (g36_s6_alpha_norm_le N z φ hP s).trans ?_
    calc ‖NlsGge.Analysis.reciprocalBracketL2‖ * physicalSobolevNorm 1 (wkbPartial N z φ)
        ≤ ‖NlsGge.Analysis.reciprocalBracketL2‖ *
          (‖z‖⁻¹ * (K * (1 + pairSobolevNorm (N : ℝ) φ) ^ p)) :=
          mul_le_mul_of_nonneg_left hnP hR
      _ ≤ ‖NlsGge.Analysis.reciprocalBracketL2‖ * (‖z‖⁻¹ * (K * (1 + B) ^ p)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hK.le)
              (inv_nonneg.2 hz0.le)) hR
      _ = A * ‖z‖⁻¹ := by rw [hAdef]; ring
  have hinv : ‖z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz
  have hα' : ∀ s : ℝ, ‖wkbAlpha N z φ s‖ ≤ A := fun s =>
    (hα s).trans (mul_le_of_le_one_right hA0 hinv)
  have hJ := g37_J_norm_le N z φ A hα'
  have hJB : ‖∫ s in (0 : ℝ)..1, potRepFst38 φ s * wkbAlpha N z φ s‖ ≤ A * B :=
    hJ.trans (mul_le_mul_of_nonneg_left (hn1.trans hnorm) hA0)
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hzim : |z.im| ≤ τ := hzτ
  refine ⟨hα, ?_, ?_, hmain φ hφ hnorm z hzτ hz 1 h1mem⟩
  · have := g36_s6_phase_exp_le z 1 A B h1mem _ hJB
    unfold wkbPhase
    exact this.trans (Real.exp_le_exp.mpr (by linarith))
  · have := g36_s6_phase_exp_le (-z) 1 A B h1mem
      (-∫ s in (0 : ℝ)..1, potRepFst38 φ s * wkbAlpha N z φ s) (by rwa [norm_neg])
    have heq : (wkbPhase N z φ 1)⁻¹ = Complex.exp (-Complex.I * (-z) * ((1 : ℝ) : ℂ) +
        Complex.I * -∫ s in (0 : ℝ)..1, potRepFst38 φ s * wkbAlpha N z φ s) := by
      unfold wkbPhase
      rw [← Complex.exp_neg]
      congr 1
      ring
    rw [heq]
    refine this.trans (Real.exp_le_exp.mpr ?_)
    simp only [Complex.neg_im, abs_neg]
    linarith

theorem g37_S_mulVec (v : Fin 2 → ℂ) : g37_S.mulVec v = ![v 1, v 0] := by
  ext i
  fin_cases i <;> simp [g37_S, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem G1_037 (N : ℕ) (hN : 1 ≤ N)
    (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 ≤ τ) :
    ∃ C Λ : ℝ, 0 < C ∧ 1 ≤ Λ ∧
      ∀ φ : PotPair, pairSobolev (N : ℝ) φ →
        pairSobolevNorm (N : ℝ) φ ≤ B →
      ∀ l : ℂ, |l.im| ≤ τ → Λ ≤ ‖l‖ →
        ‖discrim φ l - 2 * Complex.cosh (wkbSigma N l φ)‖ ≤
          C / ‖l‖^N := by
  obtain ⟨A, K1, C1, hA, hK1, hC1, hu⟩ := g37_unif N hN B τ hB hτ
  have hT : 0 ≤ 4 + K1 * (4 * K1 + 3 * C1) := by positivity
  refine ⟨(4 + K1 * (4 * K1 + 3 * C1)) * C1 + 1, max 1 (2 * A), by positivity,
    le_max_left _ _, ?_⟩
  intro φ hφ hnorm l hlτ hl
  have hl1 : 1 ≤ ‖l‖ := (le_max_left _ _).trans hl
  have hl2 : 2 * A ≤ ‖l‖ := (le_max_right _ _).trans hl
  have hρ : 0 < ‖l‖ := by linarith
  obtain ⟨hψ, hψn⟩ := g36_s6_swapped N φ hφ
  obtain ⟨hα1, hΦ1, hΦi1, hR1⟩ := hu φ hφ hnorm l hlτ hl1
  obtain ⟨hα2, hΦ2, -, hR2⟩ := hu (swappedPotential φ) hψ (hψn.le.trans hnorm) (-l)
    (by simpa using hlτ) (by simpa using hl1)
  have hnl : ‖-l‖ = ‖l‖ := norm_neg l
  rw [hnl] at hα2
  have hc1 : (2 * Complex.I * l) ^ N ≠ 0 := by
    have : 2 * Complex.I * l ≠ 0 := by
      have : l ≠ 0 := by
        intro h
        rw [h, norm_zero] at hρ
        exact lt_irrefl _ hρ
      simp [this]
    exact pow_ne_zero _ this
  have hc2 : (2 * Complex.I * (-l)) ^ N ≠ 0 := by
    have : 2 * Complex.I * (-l) ≠ 0 := by
      have : l ≠ 0 := by
        intro h
        rw [h, norm_zero] at hρ
        exact lt_irrefl _ hρ
      simp [this]
    exact pow_ne_zero _ this
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hMe : Set.IccExtend zero_le_one (fundPair φ l) 1 = monodromyPair φ l := by
    rw [monodromyPair_eq_fundPair]
    exact Set.IccExtend_right _ _
  have hMe2 : Set.IccExtend zero_le_one (fundPair (swappedPotential φ) (-l)) 1 =
      g37_S * monodromyPair φ l * g37_S := by
    rw [Set.IccExtend_right, g37_fundPair_swap, monodromyPair_eq_fundPair]
  set M := monodromyPair φ l with hM
  set a := wkbAlpha N l φ 0 with ha
  set a' := wkbAlpha N (-l) (swappedPotential φ) 0 with ha'
  set Φ := wkbPhase N l φ 1 with hΦ
  set Φ' := wkbPhase N (-l) (swappedPotential φ) 1 with hΦ'
  -- first column
  have hr1 : wkbRemainder N l φ 1 = (2 * Complex.I * l) ^ N •
      (M.mulVec ![1, a] - Φ • ![1, a]) := by
    unfold wkbRemainder
    rw [hMe, g37_alpha_one]
  have h1 : M.mulVec ![1, a] = Φ • ![1, a] + ((2 * Complex.I * l) ^ N)⁻¹ • wkbRemainder N l φ 1 := by
    rw [hr1, inv_smul_smul₀ hc1]
    abel
  -- second column
  have hr2 : wkbRemainder N (-l) (swappedPotential φ) 1 = (2 * Complex.I * (-l)) ^ N •
      ((g37_S * M * g37_S).mulVec ![1, a'] - Φ' • ![1, a']) := by
    unfold wkbRemainder
    rw [hMe2, g37_alpha_one]
  have h2' : (g37_S * M * g37_S).mulVec ![1, a'] = Φ' • ![1, a'] +
      ((2 * Complex.I * (-l)) ^ N)⁻¹ • wkbRemainder N (-l) (swappedPotential φ) 1 := by
    rw [hr2, inv_smul_smul₀ hc2]
    abel
  have h2 : M.mulVec ![a', 1] = Φ' • ![a', 1] +
      ((2 * Complex.I * (-l)) ^ N)⁻¹ • g37_S.mulVec (wkbRemainder N (-l) (swappedPotential φ) 1) := by
    have hS1 : g37_S.mulVec ![1, a'] = ![a', 1] := by
      rw [g37_S_mulVec]; simp
    have hSM : g37_S * (g37_S * M * g37_S) = M * g37_S := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, g37_S_mul_S, Matrix.one_mul]
    have e1 : M.mulVec ![a', 1] = g37_S.mulVec ((g37_S * M * g37_S).mulVec ![1, a']) := by
      rw [← hS1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSM]
    rw [e1, h2', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hS1]
  -- the error terms
  have hpow : 0 < (2 * ‖l‖) ^ N := by positivity
  have hnc1 : ‖((2 * Complex.I * l) ^ N)⁻¹‖ = ((2 * ‖l‖) ^ N)⁻¹ := by
    simp [norm_mul, norm_pow]
  have hnc2 : ‖((2 * Complex.I * (-l)) ^ N)⁻¹‖ = ((2 * ‖l‖) ^ N)⁻¹ := by
    simp [norm_mul, norm_pow]
  have he1 : ∀ j, ‖(((2 * Complex.I * l) ^ N)⁻¹ • wkbRemainder N l φ 1) j‖ ≤ C1 / (2 * ‖l‖) ^ N := by
    intro j
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, hnc1]
    calc ((2 * ‖l‖) ^ N)⁻¹ * ‖wkbRemainder N l φ 1 j‖ ≤ ((2 * ‖l‖) ^ N)⁻¹ * C1 :=
          mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ j).trans hR1) (inv_nonneg.2 hpow.le)
      _ = C1 / (2 * ‖l‖) ^ N := (div_eq_inv_mul _ _).symm
  have he2 : ∀ j, ‖(((2 * Complex.I * (-l)) ^ N)⁻¹ •
      g37_S.mulVec (wkbRemainder N (-l) (swappedPotential φ) 1)) j‖ ≤ C1 / (2 * ‖l‖) ^ N := by
    intro j
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, hnc2, g37_S_mulVec]
    have hsw : ∀ r : Fin 2 → ℂ, (![r 1, r 0] : Fin 2 → ℂ) j = r (g37_sw j) := by
      intro r
      fin_cases j <;> rfl
    rw [hsw]
    calc ((2 * ‖l‖) ^ N)⁻¹ * ‖wkbRemainder N (-l) (swappedPotential φ) 1 (g37_sw j)‖
        ≤ ((2 * ‖l‖) ^ N)⁻¹ * C1 :=
          mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ _).trans hR2) (inv_nonneg.2 hpow.le)
      _ = C1 / (2 * ‖l‖) ^ N := (div_eq_inv_mul _ _).symm
  have he0 : 0 ≤ C1 / (2 * ‖l‖) ^ N := by positivity
  have hec : C1 / (2 * ‖l‖) ^ N ≤ C1 :=
    div_le_self hC1.le (one_le_pow₀ (by linarith))
  have hAl : A * ‖l‖⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hρ]
    linarith
  have haN : ‖a‖ ≤ 1 / 2 := (hα1 0).trans hAl
  have haN' : ‖a'‖ ≤ 1 / 2 := (hα2 0).trans hAl
  have hΦne : Φ ≠ 0 := by
    rw [hΦ, g37_phase_eq N hN l hl1 φ hφ]
    exact Complex.exp_ne_zero _
  have hest := g37_est M (det_monodromyPair φ l) a a' Φ Φ' _ _ (C1 / (2 * ‖l‖) ^ N) K1 C1
    h1 h2 haN haN' he1 he2 he0 hec hΦ1 hΦ2 hΦi1 hΦne
  have hcosh : 2 * Complex.cosh (wkbSigma N l φ) = Φ + Φ⁻¹ := by
    rw [Complex.two_cosh, hΦ, g37_phase_eq N hN l hl1 φ hφ, Complex.exp_neg]
  calc ‖discrim φ l - 2 * Complex.cosh (wkbSigma N l φ)‖ = ‖M.trace - (Φ + Φ⁻¹)‖ := by
        rw [hcosh]; rfl
    _ ≤ (4 + K1 * (4 * K1 + 3 * C1)) * (C1 / (2 * ‖l‖) ^ N) := hest
    _ ≤ (4 + K1 * (4 * K1 + 3 * C1)) * (C1 / ‖l‖ ^ N) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hC1.le (by positivity)
            (pow_le_pow_left₀ hρ.le (by linarith) N)) hT
    _ = ((4 + K1 * (4 * K1 + 3 * C1)) * C1) / ‖l‖ ^ N := by ring
    _ ≤ ((4 + K1 * (4 * K1 + 3 * C1)) * C1 + 1) / ‖l‖ ^ N :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)

end
end NlsGge.GKDefinitionDesign
