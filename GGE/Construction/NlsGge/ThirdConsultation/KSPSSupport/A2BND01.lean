import Mathlib
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPSSupport.EXP01
import NlsGge.ThirdConsultation.KSPSSupport.UNI01
import NlsGge.ThirdConsultation.KSPSSupport.A1U01
import NlsGge.ThirdConsultation.KSPSSupport.A2ID01
import NlsGge.ThirdConsultation.KSPSSupport.ANA01
import NlsGge.ThirdConsultation.KSPSSupport.CORE01

                                                                                
                                                          
                                                                                                     
                                                                                           
                                                                                               
                                                                   
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- Abstract norm inequality for the expansion of a2 (all atoms are complex numbers). -/
theorem h161_bound_abs (C Q1 Tp M σ W2 Yp v : ℂ) (X S ι K2 DW DY ΩT : ℝ)
    (hσ : ‖σ‖ = 1) (hι : 0 ≤ ι) (hv : ‖v‖ ≤ ι) (hK2 : 0 ≤ K2) (hM : ‖M‖ ≤ K2)
    (hDW : 0 ≤ DW) (hW2 : ‖W2‖ ≤ DW) (hDY : 0 ≤ DY) (hY : ‖Yp‖ ≤ DY) (hΩT : 0 ≤ ΩT)
    (hT : ‖Tp‖ ≤ ΩT * S) (hS : 0 ≤ S) (hQ1 : ‖Q1‖ ≤ S) (hC : ‖C‖ ≤ X) (hSX : S ≤ X) :
    ‖Tp + σ * M * Q1 + v * (σ * M) * Tp + W2 * (C + v * Q1 + v ^ 2 * Tp) +
        Yp * (C + v * Q1 + v ^ 2 * Tp)‖ ≤
      (ΩT + K2 + ι * K2 * ΩT + (DW + DY) * (1 + ι + ι ^ 2 * ΩT)) * X := by
  have hX : 0 ≤ X := le_trans (norm_nonneg _) hC
  have hG : ‖C + v * Q1 + v ^ 2 * Tp‖ ≤ (1 + ι + ι ^ 2 * ΩT) * X := by
    have h1 : ‖v * Q1‖ ≤ ι * S := by
      rw [norm_mul]
      exact mul_le_mul hv hQ1 (norm_nonneg _) hι
    have h2 : ‖v ^ 2 * Tp‖ ≤ ι ^ 2 * (ΩT * S) := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hv 2) hT (norm_nonneg _)
        (sq_nonneg _)
    have h3 := norm_add_le (C + v * Q1) (v ^ 2 * Tp)
    have h4 := norm_add_le C (v * Q1)
    have h5 : ι * S ≤ ι * X := mul_le_mul_of_nonneg_left hSX hι
    have h6 : ι ^ 2 * (ΩT * S) ≤ ι ^ 2 * (ΩT * X) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSX hΩT) (sq_nonneg _)
    have h7 : (1 + ι + ι ^ 2 * ΩT) * X = X + ι * X + ι ^ 2 * (ΩT * X) := by ring
    linarith
  have hTX : ‖Tp‖ ≤ ΩT * X := hT.trans (mul_le_mul_of_nonneg_left hSX hΩT)
  have hA : ‖σ * M * Q1‖ ≤ K2 * X := by
    simp only [norm_mul, hσ, one_mul]
    exact (mul_le_mul hM hQ1 (norm_nonneg _) hK2).trans (mul_le_mul_of_nonneg_left hSX hK2)
  have hB : ‖v * (σ * M) * Tp‖ ≤ ι * K2 * (ΩT * X) := by
    simp only [norm_mul, hσ, one_mul]
    exact mul_le_mul (mul_le_mul hv hM (norm_nonneg _) hι) hTX (norm_nonneg _)
      (mul_nonneg hι hK2)
  have hWG : ‖W2 * (C + v * Q1 + v ^ 2 * Tp)‖ ≤ DW * ((1 + ι + ι ^ 2 * ΩT) * X) := by
    rw [norm_mul]
    exact mul_le_mul hW2 hG (norm_nonneg _) hDW
  have hYG : ‖Yp * (C + v * Q1 + v ^ 2 * Tp)‖ ≤ DY * ((1 + ι + ι ^ 2 * ΩT) * X) := by
    rw [norm_mul]
    exact mul_le_mul hY hG (norm_nonneg _) hDY
  have e1 := norm_add_le (Tp + σ * M * Q1 + v * (σ * M) * Tp + W2 * (C + v * Q1 + v ^ 2 * Tp))
    (Yp * (C + v * Q1 + v ^ 2 * Tp))
  have e2 := norm_add_le (Tp + σ * M * Q1 + v * (σ * M) * Tp) (W2 * (C + v * Q1 + v ^ 2 * Tp))
  have e3 := norm_add_le (Tp + σ * M * Q1) (v * (σ * M) * Tp)
  have e4 := norm_add_le Tp (σ * M * Q1)
  have hfin : ΩT * X + K2 * X + ι * K2 * (ΩT * X) + DW * ((1 + ι + ι ^ 2 * ΩT) * X) +
      DY * ((1 + ι + ι ^ 2 * ΩT) * X) =
      (ΩT + K2 + ι * K2 * ΩT + (DW + DY) * (1 + ι + ι ^ 2 * ΩT)) * X := by ring
  linarith

/-- The exponential remainder of the phase exponent, with the uniform constant. -/
theorem h161_Yn (z v w : ℂ) (R ι : ℝ) (hzv : ‖z‖ * ‖v‖ = 1) (hv : ‖v‖ ≤ ι) (hR : 0 ≤ R)
    (hw : ‖w‖ ≤ ‖v‖ * R) :
    ‖z ^ 2 * (Complex.exp w - 1 - w)‖ ≤ R ^ 2 * Real.exp (ι * R) := by
  have hι : ‖w‖ ≤ ι * R := hw.trans (mul_le_mul_of_nonneg_right hv hR)
  have hexp : Real.exp ‖w‖ ≤ Real.exp (ι * R) := Real.exp_le_exp.mpr hι
  have h1 := h161_exp_remainder w
  calc ‖z ^ 2 * (Complex.exp w - 1 - w)‖ = ‖z‖ ^ 2 * ‖Complex.exp w - 1 - w‖ := by
        rw [norm_mul, norm_pow]
    _ ≤ ‖z‖ ^ 2 * (‖w‖ ^ 2 * Real.exp (ι * R)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hexp (sq_nonneg _)))
          (sq_nonneg _)
    _ ≤ ‖z‖ ^ 2 * ((‖v‖ * R) ^ 2 * Real.exp (ι * R)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw 2)
            (Real.exp_pos _).le)
          (sq_nonneg _)
    _ = (‖z‖ * ‖v‖) ^ 2 * R ^ 2 * Real.exp (ι * R) := by ring
    _ = R ^ 2 * Real.exp (ι * R) := by rw [hzv]; ring

/-- The phase exponent is bounded by the norm of v times K2 + ι DW. -/
theorem h161_wbound (v σ M W2 : ℂ) (K2 DW ι : ℝ) (hσ : ‖σ‖ = 1) (hι : 0 ≤ ι) (hv : ‖v‖ ≤ ι)
    (hM : ‖M‖ ≤ K2) (hDW : 0 ≤ DW) (hW2 : ‖W2‖ ≤ DW) :
    ‖v * (σ * M) + v ^ 2 * W2‖ ≤ ‖v‖ * (K2 + ι * DW) := by
  have h1 := norm_add_le (v * (σ * M)) (v ^ 2 * W2)
  have h2 : ‖v * (σ * M)‖ ≤ ‖v‖ * K2 := by
    simp only [norm_mul, hσ, one_mul]
    exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)
  have h3 : ‖v ^ 2 * W2‖ ≤ ‖v‖ * (ι * DW) := by
    rw [norm_mul, norm_pow]
    have : ‖v‖ ^ 2 * ‖W2‖ ≤ ‖v‖ * ι * DW := by
      have hn : ‖v‖ ^ 2 ≤ ‖v‖ * ι := by
        have := mul_le_mul_of_nonneg_left hv (norm_nonneg v)
        nlinarith
      nlinarith [norm_nonneg v, norm_nonneg W2]
    nlinarith [this]
  nlinarith [h1, h2, h3]

/-- W2 is bounded by the sum of the prefix bounds with powers of ι. -/
theorem h161_W2_bound {N : ℕ} (ψ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ) (ι DP : ℝ)
    (hι : 0 ≤ ι) (hv : ‖h161_v lam‖ ≤ ι) (hP : ∀ k : ℕ, 2 ≤ k → k ≤ N →
      ‖KSPSRiccati.«prefix» ψ b k x‖ ≤ DP) :
    ‖h161_W2 ψ b lam x‖ ≤ ∑ k ∈ Finset.Icc 2 N, ι ^ (k - 2) * DP := by
  have hs : ‖h161_sgn b‖ = 1 := by
    cases b <;> simp [h161_sgn]
  unfold h161_W2
  rw [norm_mul, hs, one_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  rw [norm_mul, norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hv _) (hP k hk1 hk2) (norm_nonneg _)
    (pow_nonneg hι _)

/-- The tail sum Tp is bounded by (1+ι)^N times the sum of the quadratic L2 norms. -/
theorem h161_Tp_bound {N : ℕ} (hN : 1 ≤ N) (ψ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ)
    (ι : ℝ) (hι : 0 ≤ ι) (hv : ‖h161_v lam‖ ≤ ι) :
    ‖h161_Tp ψ b lam x‖ ≤ (1 + ι) ^ N *
      ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) x‖ := by
  unfold h161_Tp
  have hsub : ∑ j ∈ Finset.Icc (N + 2) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) x‖ ≤
      ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) x‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
      (fun j _ _ => norm_nonneg _)
  have hpow1 : 0 ≤ (1 + ι) ^ N := pow_nonneg (by linarith) _
  have hterm : ∀ j ∈ Finset.Icc (N + 2) (2 * N),
      ‖h161_v lam ^ (j - N - 2) * coverRep38 (KSPSRiccati.quadratic ψ b j) x‖ ≤
        (1 + ι) ^ N * ‖coverRep38 (KSPSRiccati.quadratic ψ b j) x‖ := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
    rw [norm_mul, norm_pow]
    have hpow : ‖h161_v lam‖ ^ (j - N - 2) ≤ (1 + ι) ^ N := by
      calc ‖h161_v lam‖ ^ (j - N - 2) ≤ ι ^ (j - N - 2) := pow_le_pow_left₀ (norm_nonneg _) hv _
        _ ≤ (1 + ι) ^ (j - N - 2) := pow_le_pow_left₀ hι (by linarith) _
        _ ≤ (1 + ι) ^ N := pow_le_pow_right₀ (by linarith) (by omega)
    exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
  calc ‖∑ j ∈ Finset.Icc (N + 2) (2 * N), h161_v lam ^ (j - N - 2) *
        coverRep38 (KSPSRiccati.quadratic ψ b j) x‖
      ≤ ∑ j ∈ Finset.Icc (N + 2) (2 * N),
          ‖h161_v lam ^ (j - N - 2) * coverRep38 (KSPSRiccati.quadratic ψ b j) x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc (N + 2) (2 * N), (1 + ι) ^ N *
          ‖coverRep38 (KSPSRiccati.quadratic ψ b j) x‖ :=
        Finset.sum_le_sum hterm
    _ = (1 + ι) ^ N * ∑ j ∈ Finset.Icc (N + 2) (2 * N),
          ‖coverRep38 (KSPSRiccati.quadratic ψ b j) x‖ := by
        rw [Finset.mul_sum]
    _ ≤ (1 + ι) ^ N * ∑ j ∈ Finset.Icc (N + 1) (2 * N),
          ‖coverRep38 (KSPSRiccati.quadratic ψ b j) x‖ :=
        mul_le_mul_of_nonneg_left hsub hpow1

/-- The square of a sum of N+1 nonnegative terms, Cauchy-Schwarz form. -/
theorem h161_sq_bound (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (q : ℕ → ℝ) (hq : ∀ j, 0 ≤ q j) (hc : 0 ≤ c) :
    (c + ∑ j ∈ Finset.Icc (N + 1) (2 * N), q j) ^ 2 ≤
      2 * ((N : ℝ) + 1) * (c ^ 2 + ∑ j ∈ Finset.Icc (N + 1) (2 * N), q j ^ 2) := by
  have hcard : ((Finset.Icc (N + 1) (2 * N)).card : ℝ) = N := by
    rw [Nat.card_Icc]
    have : 2 * N + 1 - (N + 1) = N := by omega
    rw [this]
  have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.Icc (N + 1) (2 * N)) (f := q)
  rw [hcard] at hCS
  have hsq0 : 0 ≤ ∑ j ∈ Finset.Icc (N + 1) (2 * N), q j ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hS0 : 0 ≤ ∑ j ∈ Finset.Icc (N + 1) (2 * N), q j :=
    Finset.sum_nonneg (fun j _ => hq j)
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [sq_nonneg (c - ∑ j ∈ Finset.Icc (N + 1) (2 * N), q j), mul_nonneg hsq0 (by linarith : (0 : ℝ) ≤ (N : ℝ) - 1), sq_nonneg c]

/-- The prefix bound constant on the ball. -/
def h161_DP (K D1 : ℝ) : ℝ := (K ^ 2 + D1 ^ 2) / 2

/-- The sum of the prefix bounds with powers of ι (the W2 constant). -/
def h161_DW (N : ℕ) (ι DP : ℝ) : ℝ := ∑ k ∈ Finset.Icc 2 N, ι ^ (k - 2) * DP

/-- The exponential-remainder constant. -/
def h161_DY (K ι DW : ℝ) : ℝ := (K ^ 2 + ι * DW) ^ 2 * Real.exp (ι * (K ^ 2 + ι * DW))

/-- The uniform constant Kappa of the a2 pointwise bound. -/
def h161_Kap (N : ℕ) (K D1 ι : ℝ) : ℝ :=
  (1 + ι) ^ N + K ^ 2 + ι * K ^ 2 * (1 + ι) ^ N +
    (h161_DW N ι (h161_DP K D1) + h161_DY K ι (h161_DW N ι (h161_DP K D1))) *
      (1 + ι + ι ^ 2 * (1 + ι) ^ N)

theorem h161_Kap_nonneg (N : ℕ) (K D1 ι : ℝ) (hι : 0 ≤ ι) : 0 ≤ h161_Kap N K D1 ι := by
  have hDP : 0 ≤ h161_DP K D1 := by unfold h161_DP; positivity
  have hDW : 0 ≤ h161_DW N ι (h161_DP K D1) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hι _) hDP)
  have hpow : 0 ≤ (1 + ι) ^ N := pow_nonneg (by linarith) _
  have hDY : 0 ≤ h161_DY K ι (h161_DW N ι (h161_DP K D1)) := by
    unfold h161_DY
    exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have h1 : 0 ≤ 1 + ι + ι ^ 2 * (1 + ι) ^ N := add_nonneg (by linarith) (mul_nonneg (sq_nonneg ι) hpow)
  have h2 := mul_nonneg (add_nonneg hDW hDY) h1
  have h3 : 0 ≤ ι * K ^ 2 * (1 + ι) ^ N := mul_nonneg (mul_nonneg hι (sq_nonneg K)) hpow
  unfold h161_Kap
  linarith [sq_nonneg K]

/-- Pointwise bound of a2 squared (for a.e. t in [0,1]), given the a.e. expansion at t. -/
theorem h161_pointwise {N : ℕ} (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) (ι : ℝ) (hι : 0 ≤ ι)
    (ψ : SobolevC N) (hS : ‖ψ.1‖ + ‖ψ.2‖ ≤ K) (b : Bool) (lam : ℂ) (hlam : lam ≠ 0)
    (hv : ‖h161_v lam‖ ≤ ι) (D1 : ℝ) (hD1 : 0 ≤ D1)
    (hH1 : ∀ k : ℕ, 1 ≤ k → k ≤ N → ‖KSPSRiccati.coefficient ψ b k‖ ≤ D1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hid : KSPSRiccati.a2 ψ b lam t =
      h161_Tp ψ b lam t + h161_sig b * KSPSRiccati.massPrefix ψ t *
          coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) t +
        h161_v lam * (h161_sig b * KSPSRiccati.massPrefix ψ t) * h161_Tp ψ b lam t +
        h161_W2 ψ b lam t * h161_G ψ b lam t +
        (2 * Complex.I * lam) ^ 2 *
          (Complex.exp (h161_wexp ψ b lam t) - 1 - h161_wexp ψ b lam t) * h161_G ψ b lam t) :
    ‖KSPSRiccati.a2 ψ b lam t‖ ^ 2 ≤
      2 * ((N : ℝ) + 1) * h161_Kap N K D1 ι ^ 2 *
        (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ^ 2 +
          ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ ^ 2) := by
  have hDP0 : 0 ≤ h161_DP K D1 := by unfold h161_DP; positivity
  have hDW0 : 0 ≤ h161_DW N ι (h161_DP K D1) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hι _) hDP0)
  have hR : 0 ≤ K ^ 2 + ι * h161_DW N ι (h161_DP K D1) :=
    add_nonneg (sq_nonneg K) (mul_nonneg hι hDW0)
  have hP : ∀ k : ℕ, 2 ≤ k → k ≤ N → ‖KSPSRiccati.«prefix» ψ b k t‖ ≤ h161_DP K D1 := by
    intro k hk1 hk2
    have hb := h161_prefix_bound ψ b k ht
    have hsd := h161_side_psn1 hN ψ b
    have hside : ‖KSPSRiccati.sidePotential ψ b‖ ≤ K :=
      (h161_L2_le_psn1 _ hsd.1).trans (hsd.2.trans hS)
    have hcoef : ‖KSPSRiccati.coefficient ψ b k‖ ≤ D1 := hH1 k (by omega) hk2
    have h1 : ‖KSPSRiccati.sidePotential ψ b‖ ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hside 2
    have h2 : ‖KSPSRiccati.coefficient ψ b k‖ ^ 2 ≤ D1 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hcoef 2
    unfold h161_DP
    linarith
  have hM := h161_massPrefix_ball ψ K hS ht
  have hσ : ‖h161_sig b‖ = 1 := by
    cases b <;> simp [h161_sig]
  have hW2 := h161_W2_bound ψ b lam t ι (h161_DP K D1) hι hv hP
  have hw := h161_wbound (h161_v lam) (h161_sig b) (KSPSRiccati.massPrefix ψ t)
    (h161_W2 ψ b lam t) (K ^ 2) (h161_DW N ι (h161_DP K D1)) ι hσ hι hv hM hDW0 hW2
  have hzv : ‖2 * Complex.I * lam‖ * ‖h161_v lam‖ = 1 := by
    have hz0 : ‖2 * Complex.I * lam‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hlam
    unfold h161_v
    rw [norm_inv]
    exact mul_inv_cancel₀ hz0
  have hYn := h161_Yn (2 * Complex.I * lam) (h161_v lam) (h161_wexp ψ b lam t)
    (K ^ 2 + ι * h161_DW N ι (h161_DP K D1)) ι hzv hv hR hw
  have hDY0 : 0 ≤ h161_DY K ι (h161_DW N ι (h161_DP K D1)) := by
    unfold h161_DY
    positivity
  have hΩT : 0 ≤ (1 + ι) ^ N := pow_nonneg (by linarith) _
  have hT := h161_Tp_bound hN ψ b lam t ι hι hv
  have hS0 : 0 ≤ ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hQ1 : ‖coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) t‖ ≤
      ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ :=
    Finset.single_le_sum (f := fun j => ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖)
      (fun j _ => norm_nonneg _) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hC : ‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ≤
      ‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ +
        ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ :=
    le_add_of_nonneg_right hS0
  have hSX : ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ ≤
      ‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ +
        ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ :=
    le_add_of_nonneg_left (norm_nonneg _)
  have hbound := h161_bound_abs (coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t)
    (coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) t) (h161_Tp ψ b lam t)
    (KSPSRiccati.massPrefix ψ t) (h161_sig b) (h161_W2 ψ b lam t)
    ((2 * Complex.I * lam) ^ 2 * (Complex.exp (h161_wexp ψ b lam t) - 1 - h161_wexp ψ b lam t))
    (h161_v lam)
    (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ +
      ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖)
    (∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖)
    ι (K ^ 2) (h161_DW N ι (h161_DP K D1)) (h161_DY K ι (h161_DW N ι (h161_DP K D1)))
    ((1 + ι) ^ N) hσ hι hv (sq_nonneg K) hM hDW0 hW2 hDY0 hYn hΩT hT hS0 hQ1 hC hSX
  have hnorm : ‖h161_Tp ψ b lam t + h161_sig b * KSPSRiccati.massPrefix ψ t *
          coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) t +
        h161_v lam * (h161_sig b * KSPSRiccati.massPrefix ψ t) * h161_Tp ψ b lam t +
        h161_W2 ψ b lam t * h161_G ψ b lam t +
        (2 * Complex.I * lam) ^ 2 *
          (Complex.exp (h161_wexp ψ b lam t) - 1 - h161_wexp ψ b lam t) * h161_G ψ b lam t‖ ≤
      h161_Kap N K D1 ι * (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ +
        ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖) := by
    unfold h161_G h161_Kap
    exact hbound
  rw [hid]
  have hX2 := h161_sq_bound N hN (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖)
    (fun j => ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖) (fun j => norm_nonneg _) (norm_nonneg _)
  calc _ ^ 2 ≤ (h161_Kap N K D1 ι * (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ +
        ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = h161_Kap N K D1 ι ^ 2 * (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ +
        ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖) ^ 2 := by
        ring
    _ ≤ h161_Kap N K D1 ι ^ 2 * (2 * ((N : ℝ) + 1) *
        (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ^ 2 +
          ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hX2 (sq_nonneg _)
    _ = 2 * ((N : ℝ) + 1) * h161_Kap N K D1 ι ^ 2 *
        (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ^ 2 +
          ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ ^ 2) := by
        ring

/-- R2 (uniform a2): the uniform L2 bound of a2 on the ball for |lam| >= Lambda. -/
theorem h161_a2_uniform (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ ψ : SobolevC N, ‖ψ.1‖ + ‖ψ.2‖ ≤ K → ∀ (b : Bool) (lam : ℂ),
      Λ ≤ ‖lam‖ →
      MemLp (KSPSRiccati.a2 ψ b lam) 2 KSPSRiccati.intervalMeasure ∧
      eLpNorm (KSPSRiccati.a2 ψ b lam) 2 KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal Ca := by
  obtain ⟨D1, hD1, hH1⟩ := h161_coef_H1 N hN K hK
  obtain ⟨Dc, hDc, hC⟩ := h161_coef_top N hN K hK
  obtain ⟨DQ, hDQ, hQ⟩ := h161_quad_H1 N hN K hK
  have hι : 0 ≤ (2 * Λ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hKap := h161_Kap_nonneg N K D1 (2 * Λ)⁻¹ hι
  have hCa0 : 0 ≤ 2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ * (Dc + N * DQ) :=
    mul_nonneg (mul_nonneg (by positivity) hKap)
      (add_nonneg hDc (mul_nonneg (Nat.cast_nonneg _) hDQ))
  have hcard : ((Finset.Icc (N + 1) (2 * N)).card : ℝ) = N := by
    rw [Nat.card_Icc]
    have : 2 * N + 1 - (N + 1) = N := by omega
    rw [this]
  refine ⟨2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ * (Dc + N * DQ), hCa0,
    fun ψ hS b lam hlam => ?_⟩
  have hl0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlam
    linarith
  have hv : ‖h161_v lam‖ ≤ (2 * Λ)⁻¹ := by
    unfold h161_v
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, h2, mul_one]
    exact inv_anti₀ (by linarith) (by linarith)
  have hmem := h150_a2_memLp ψ b lam
  refine ⟨hmem, ?_⟩
  apply h161_eLp2_le _ hmem _ hCa0
  have hH1' : ∀ k : ℕ, 1 ≤ k → k ≤ N → ‖KSPSRiccati.coefficient ψ b k‖ ≤ D1 := fun k hk1 hk2 =>
    ((h161_L2_le_psn1 _ (hH1 ψ hS b k hk1 hk2).1).trans (hH1 ψ hS b k hk1 hk2).2)
  have hpt : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖KSPSRiccati.a2 ψ b lam t‖ ^ 2 ≤
        2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ ^ 2 *
          (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ^ 2 +
            ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae (h161_a2_identity hN ψ b lam hl0),
      MeasureTheory.ae_restrict_mem measurableSet_Icc] with t hid ht
    exact h161_pointwise hN K hK (2 * Λ)⁻¹ hι ψ hS b lam hl0 hv D1 hD1 hH1' t ht hid
  have hint_lhs := h161_intervalIntegrable_sq _ hmem
  have hQi : ∀ j ∈ Finset.Icc (N + 1) (2 * N),
      IntervalIntegrable (fun t => ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ ^ 2) volume 0 1 :=
    fun j _ => intervalIntegrable_coverRep38_sq_one _
  have hQsum : IntervalIntegrable (fun t => ∑ j ∈ Finset.Icc (N + 1) (2 * N),
      ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ ^ 2) volume 0 1 := by
    have h := IntervalIntegrable.sum (Finset.Icc (N + 1) (2 * N)) hQi
    convert h using 1
    funext t
    simp [Finset.sum_apply]
  have hint_rhs : IntervalIntegrable (fun t =>
      2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ ^ 2 *
        (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ^ 2 +
          ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ ^ 2))
      volume 0 1 :=
    IntervalIntegrable.const_mul ((intervalIntegrable_coverRep38_sq_one _).add hQsum) _
  have hmono := intervalIntegral.integral_mono_ae_restrict zero_le_one hint_lhs hint_rhs hpt
  have hI : ∫ t in (0 : ℝ)..1,
      2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ ^ 2 *
        (‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ^ 2 +
          ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖coverRep38 (KSPSRiccati.quadratic ψ b j) t‖ ^ 2) =
      2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ ^ 2 *
        (‖KSPSRiccati.coefficient ψ b (N + 1)‖ ^ 2 +
          ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖KSPSRiccati.quadratic ψ b j‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (intervalIntegrable_coverRep38_sq_one _) hQsum,
      integral_sq_coverRep38_one, intervalIntegral.integral_finset_sum hQi]
    simp only [integral_sq_coverRep38_one]
  have hCn : ‖KSPSRiccati.coefficient ψ b (N + 1)‖ ≤ Dc := by
    have h := hC ψ hS b
    rw [Nat.sub_self, Nat.cast_zero, h161_norm_eq_psn0] at h
    exact h
  have hQn : ∀ j ∈ Finset.Icc (N + 1) (2 * N), ‖KSPSRiccati.quadratic ψ b j‖ ≤ DQ :=
    fun j _ => (h161_L2_le_psn1 _ (quadratic_H1 ψ b j hN)).trans (hQ ψ hS b j)
  have hsum2 : ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖KSPSRiccati.quadratic ψ b j‖ ^ 2 ≤
      (N : ℝ) * DQ ^ 2 := by
    calc ∑ j ∈ Finset.Icc (N + 1) (2 * N), ‖KSPSRiccati.quadratic ψ b j‖ ^ 2
        ≤ ∑ j ∈ Finset.Icc (N + 1) (2 * N), DQ ^ 2 :=
          Finset.sum_le_sum (fun j hj => pow_le_pow_left₀ (norm_nonneg _) (hQn j hj) 2)
      _ = (N : ℝ) * DQ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hCsq : ‖KSPSRiccati.coefficient ψ b (N + 1)‖ ^ 2 ≤ Dc ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hCn 2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK2 : 0 ≤ 2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ ^ 2 := by positivity
  have hstep2 := mul_le_mul_of_nonneg_left (add_le_add hCsq hsum2) hK2
  have hstep3 : Dc ^ 2 + (N : ℝ) * DQ ^ 2 ≤ (Dc + (N : ℝ) * DQ) ^ 2 := by
    nlinarith [mul_nonneg hDc (mul_nonneg (Nat.cast_nonneg N) hDQ),
      mul_nonneg (sub_nonneg.mpr hN1) (sq_nonneg DQ)]
  have hstep4 := mul_le_mul_of_nonneg_left hstep3 hK2
  have hstep5 : 2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ ^ 2 * (Dc + (N : ℝ) * DQ) ^ 2 ≤
      (2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ * (Dc + (N : ℝ) * DQ)) ^ 2 := by
    have e : (2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ * (Dc + (N : ℝ) * DQ)) ^ 2 =
        2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ ^ 2 * (Dc + (N : ℝ) * DQ) ^ 2 *
          (2 * ((N : ℝ) + 1)) := by ring
    rw [e]
    have h2 : (1 : ℝ) ≤ 2 * ((N : ℝ) + 1) := by linarith
    have hnn : 0 ≤ 2 * ((N : ℝ) + 1) * h161_Kap N K D1 (2 * Λ)⁻¹ ^ 2 * (Dc + (N : ℝ) * DQ) ^ 2 :=
      mul_nonneg hK2 (sq_nonneg _)
    nlinarith [hnn]
  refine hmono.trans (le_of_eq hI |>.trans ?_)
  linarith [hstep2, hstep4, hstep5]

end
end NlsGge.ThirdConsultation.KSPSSupport
