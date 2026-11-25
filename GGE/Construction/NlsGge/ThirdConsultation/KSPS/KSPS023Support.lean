import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS023Host
import NlsGge.ThirdConsultation.KSPS.KSPS023Support1
import NlsGge.ThirdConsultation.KSPS.KSPS021Support

                                                                                                                  
                                                                              
                                                                                       
                                                                                                         
                                                                             
                                                                                                            
                                                                                                      
                                                                                                                    
                                                                                                            
                                                                                                                       
                                                                                          
                                                                                                              
                                                                                                                    
                                                                                     
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS023W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W

/-! ### Pure lemmas -/

theorem sine_identity (Q sε dE G IL X sg : ℂ) (hsg : sg * sg = 1)
    (h : dE = 0 - (Q * (2 * Complex.I * (sg * sε)) + Complex.I * (-sg) * G + 2 * (-sg) / X * IL)) :
    sε = G / 2 - Complex.I * IL / X + ((1 - Q) * sε + Complex.I * sg * dE / 2) := by
  linear_combination (-(Complex.I * sg / 2)) * h + (-(Q * sε - G / 2) - Complex.I * IL / X) * hsg +
    (Q * sε - G / 2) * sg ^ 2 * Complex.I_sq

theorem one_sub_Q_bound (w X S : ℝ) (α β : ℂ) (hw : 1 ≤ w) (hwX : w ≤ 2 * X) (hS : 0 ≤ S)
    (hD : 1 - α * β ≠ 0) (hDinv : ‖(1 - β * α)⁻¹‖ ≤ 2)
    (hα : ‖α‖ ≤ S / (2 * X)) (hβ : ‖β‖ ≤ S / (2 * X)) :
    ‖1 - (1 - α) * (1 - β) / (1 - α * β)‖ ≤ (4 * S + 4 * S ^ 2) / w := by
  have hw0 : 0 < w := by linarith
  have e : 1 - (1 - α) * (1 - β) / (1 - α * β) = (α + β - 2 * (α * β)) * (1 - β * α)⁻¹ := by
    rw [mul_comm β α]
    field_simp
    ring
  have hSw : S / (2 * X) ≤ S / w := div_le_div_of_nonneg_left hS hw0 hwX
  have ha : ‖α‖ ≤ S / w := hα.trans hSw
  have hb : ‖β‖ ≤ S / w := hβ.trans hSw
  have hSw0 : 0 ≤ S / w := div_nonneg hS hw0.le
  have hsq : S / w * (S / w) ≤ S ^ 2 / w := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hw0]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg S) hw0.le) (sub_nonneg.2 hw)]
  have hab : ‖α * β‖ ≤ S / w * (S / w) := by
    rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) hSw0
  have hnum : ‖α + β - 2 * (α * β)‖ ≤ 2 * (S / w) + 2 * (S ^ 2 / w) := by
    calc ‖α + β - 2 * (α * β)‖ ≤ ‖α + β‖ + ‖2 * (α * β)‖ := norm_sub_le _ _
      _ ≤ ‖α‖ + ‖β‖ + 2 * ‖α * β‖ := by
          rw [norm_mul, Complex.norm_ofNat]; gcongr; exact norm_add_le _ _
      _ ≤ 2 * (S / w) + 2 * (S ^ 2 / w) := by linarith
  rw [e, norm_mul]
  calc ‖α + β - 2 * (α * β)‖ * ‖(1 - β * α)⁻¹‖ ≤ (2 * (S / w) + 2 * (S ^ 2 / w)) * 2 :=
        mul_le_mul hnum hDinv (norm_nonneg _) (by positivity)
    _ = (4 * S + 4 * S ^ 2) / w := by ring

theorem norm_sin_sub_self_le (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖Complex.sin z - z‖ ≤ ‖z‖ ^ 2 := by
  have hzI : ‖z * Complex.I‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  have hzI' : ‖-(z * Complex.I)‖ = ‖z‖ := by rw [norm_neg, hzI]
  have h1 := Complex.norm_exp_sub_one_sub_id_le (x := z * Complex.I) (by rw [hzI]; exact hz)
  have h2 := Complex.norm_exp_sub_one_sub_id_le (x := -(z * Complex.I)) (by rw [hzI']; exact hz)
  rw [hzI] at h1
  rw [hzI'] at h2
  have hs : Complex.sin z = (Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)) * Complex.I / 2 := by
    simp only [Complex.sin, neg_mul]
  have e : Complex.sin z - z = ((Complex.exp (-(z * Complex.I)) - 1 - -(z * Complex.I)) -
      (Complex.exp (z * Complex.I) - 1 - z * Complex.I)) * Complex.I / 2 := by
    rw [hs]
    linear_combination (-z) * Complex.I_sq
  rw [e, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  have := norm_sub_le (Complex.exp (-(z * Complex.I)) - 1 - -(z * Complex.I))
    (Complex.exp (z * Complex.I) - 1 - z * Complex.I)
  rw [div_le_iff₀ (by norm_num)]
  linarith

theorem eps_le_two_sin (ε : ℂ) (hε : ‖ε‖ ≤ 1 / 2) : ‖ε‖ ≤ 2 * ‖Complex.sin ε‖ := by
  have h := norm_sin_sub_self_le ε (by linarith)
  have h2 : ‖ε‖ ≤ ‖Complex.sin ε‖ + ‖Complex.sin ε - ε‖ := by
    have := norm_sub_le (Complex.sin ε) (Complex.sin ε - ε)
    rw [sub_sub_cancel] at this
    linarith
  have h3 : ‖ε‖ ^ 2 ≤ ‖ε‖ / 2 := by nlinarith [norm_nonneg ε]
  linarith

theorem norm_pow_sub_pow_le (u v : ℂ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (k : ℕ) :
    ‖u ^ k - v ^ k‖ ≤ k * ‖u - v‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : u ^ (k + 1) - v ^ (k + 1) = u * (u ^ k - v ^ k) + (u - v) * v ^ k := by ring
    rw [e]
    have hvk : ‖v ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hv
    calc ‖u * (u ^ k - v ^ k) + (u - v) * v ^ k‖
        ≤ ‖u * (u ^ k - v ^ k)‖ + ‖(u - v) * v ^ k‖ := norm_add_le _ _
      _ = ‖u‖ * ‖u ^ k - v ^ k‖ + ‖u - v‖ * ‖v ^ k‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * (k * ‖u - v‖) + ‖u - v‖ * 1 := by
          gcongr
      _ = ((k + 1 : ℕ) : ℝ) * ‖u - v‖ := by push_cast; ring

theorem phasePoly_lip {N : ℕ} (φ : SobolevC N) (K : ℕ) (u v : ℂ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖KSPSRiccati.phasePolynomial φ K u - KSPSRiccati.phasePolynomial φ K v‖ ≤
      (∑ k ∈ Finset.Icc 1 K, (k : ℝ) * ‖integralRiccatiLeft φ k‖) * ‖u - v‖ := by
  unfold KSPSRiccati.phasePolynomial
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, Complex.norm_I, one_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  have hc : ‖((2 * Complex.I) ^ k)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have e : ((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * u ^ k -
      ((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * v ^ k =
      ((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * (u ^ k - v ^ k) := by ring
  rw [e, norm_mul, norm_mul]
  have hp := norm_pow_sub_pow_le u v hu hv k
  calc ‖((2 * Complex.I) ^ k)⁻¹‖ * ‖integralRiccatiLeft φ k‖ * ‖u ^ k - v ^ k‖
      ≤ 1 * ‖integralRiccatiLeft φ k‖ * (k * ‖u - v‖) := by gcongr
    _ = (k : ℝ) * ‖integralRiccatiLeft φ k‖ * ‖u - v‖ := by ring

theorem phase_poly_eq {N : ℕ} (φ : SobolevC N) (μ : ℂ) :
    μ + KSPSRiccati.phasePolynomial φ (N + 1) μ⁻¹ =
      NlsGge.ThirdConsultation.KSPS.wkbPhase φ μ +
        Complex.I * (((2 * Complex.I * μ) ^ (N + 1))⁻¹ * integralRiccatiLeft φ (N + 1)) := by
  rw [KSPS015W.wkbPhase_eq]
  unfold KSPSRiccati.phasePolynomial
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  have hterm : ∀ k : ℕ, ((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * μ⁻¹ ^ k =
      ((2 * Complex.I * μ) ^ k)⁻¹ * integralRiccatiLeft φ k := by
    intro k
    simp only [mul_pow, mul_inv, inv_pow]
    ring
  simp only [hterm]
  ring

theorem final_pure (N : ℕ) (w ν L CT g0 ψ : ℝ) (D G r2 Δp T0 : ℂ)
    (hw : 1 ≤ w) (hν : 1 ≤ ν) (hwν : w ≤ 2 * ν) (hL0 : 0 ≤ L) (hL : 2 * L ≤ ν ^ 2) (hCT : 0 ≤ CT)
    (hD : D + Δp = G / 2 + r2) (hΔp : ‖Δp‖ ≤ L * ‖D‖ / ν ^ 2) (hT0 : ‖T0‖ ≤ CT / ν ^ (N + 2))
    (hG : w ^ N * ‖G‖ ≤ g0) (hr2 : w ^ (N + 1) * ‖r2‖ ≤ ψ) :
    w ^ (N + 1) * ‖r2 - Δp + T0‖ ≤ ψ + L * (4 * g0 + 2 * ψ) + CT * 2 ^ (N + 2) * (1 / w) := by
  have hw0 : 0 < w := by linarith
  have hν0 : 0 < ν := by linarith
  have hν2 : 0 < ν ^ 2 := by positivity
  have hwp : 0 < w ^ (N + 1) := pow_pos hw0 _
  -- |D| <= |G| + 2|r2|
  have hLD : L * ‖D‖ / ν ^ 2 ≤ ‖D‖ / 2 := by
    rw [div_le_div_iff₀ hν2 (by norm_num)]
    nlinarith [norm_nonneg D]
  have hDb : ‖D‖ ≤ ‖G‖ + 2 * ‖r2‖ := by
    have e : D = (G / 2 + r2) - Δp := by rw [← hD]; ring
    have h1 : ‖D‖ ≤ ‖G / 2 + r2‖ + ‖Δp‖ := by rw [e]; exact norm_sub_le _ _
    have h2 : ‖G / 2 + r2‖ ≤ ‖G‖ / 2 + ‖r2‖ := by
      have := norm_add_le (G / 2) r2
      rwa [norm_div, Complex.norm_ofNat] at this
    linarith
  have hΔ2 : ‖Δp‖ ≤ L * (‖G‖ + 2 * ‖r2‖) / ν ^ 2 := by
    refine hΔp.trans ?_
    gcongr
  -- weights
  have hwν2 : w ^ 2 ≤ 4 * ν ^ 2 := by nlinarith
  have hw1 : w ^ (N + 1) / ν ^ 2 ≤ 4 * w ^ N := by
    rw [div_le_iff₀ hν2]
    have h1 : w ^ (N + 1) ≤ w ^ N * w ^ 2 := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (pow_nonneg hw0.le N)
    nlinarith [pow_nonneg hw0.le N]
  have hw2 : w ^ (N + 1) / ν ^ 2 ≤ w ^ (N + 1) := div_le_self hwp.le (by nlinarith)
  have hGw : w ^ (N + 1) * ‖G‖ / ν ^ 2 ≤ 4 * g0 := by
    rw [mul_comm (w ^ (N + 1)) ‖G‖, mul_div_assoc]
    calc ‖G‖ * (w ^ (N + 1) / ν ^ 2) ≤ ‖G‖ * (4 * w ^ N) :=
          mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
      _ = 4 * (w ^ N * ‖G‖) := by ring
      _ ≤ 4 * g0 := by linarith
  have hrw : w ^ (N + 1) * ‖r2‖ / ν ^ 2 ≤ ψ := by
    rw [mul_comm (w ^ (N + 1)) ‖r2‖, mul_div_assoc]
    calc ‖r2‖ * (w ^ (N + 1) / ν ^ 2) ≤ ‖r2‖ * w ^ (N + 1) :=
          mul_le_mul_of_nonneg_left hw2 (norm_nonneg _)
      _ ≤ ψ := by linarith
  have hΔw : w ^ (N + 1) * ‖Δp‖ ≤ L * (4 * g0 + 2 * ψ) := by
    have h1 := mul_le_mul_of_nonneg_left hΔ2 hwp.le
    have e : w ^ (N + 1) * (L * (‖G‖ + 2 * ‖r2‖) / ν ^ 2) =
        L * (w ^ (N + 1) * ‖G‖ / ν ^ 2 + 2 * (w ^ (N + 1) * ‖r2‖ / ν ^ 2)) := by ring
    rw [e] at h1
    have h2 : L * (w ^ (N + 1) * ‖G‖ / ν ^ 2 + 2 * (w ^ (N + 1) * ‖r2‖ / ν ^ 2)) ≤
        L * (4 * g0 + 2 * ψ) := by
      apply mul_le_mul_of_nonneg_left _ hL0
      linarith
    linarith
  have hTw : w ^ (N + 1) * ‖T0‖ ≤ CT * 2 ^ (N + 2) * (1 / w) := by
    have h1 := mul_le_mul_of_nonneg_left hT0 hwp.le
    have h2 : w ^ (N + 1) ≤ (2 * ν) ^ (N + 1) := pow_le_pow_left₀ hw0.le hwν _
    have h3 : w ^ (N + 1) * (CT / ν ^ (N + 2)) ≤ (2 * ν) ^ (N + 1) * (CT / ν ^ (N + 2)) :=
      mul_le_mul_of_nonneg_right h2 (div_nonneg hCT (pow_nonneg hν0.le _))
    have h4 : (2 * ν) ^ (N + 1) * (CT / ν ^ (N + 2)) = CT * 2 ^ (N + 1) * (1 / ν) := by
      rw [mul_pow, pow_succ ν (N + 1)]
      field_simp
    have h5 : 1 / ν ≤ 2 * (1 / w) := by
      have e2 : 2 * (1 / w) = 2 / w := by ring
      rw [e2, div_le_div_iff₀ hν0 hw0]
      linarith
    have h6 : CT * 2 ^ (N + 1) * (1 / ν) ≤ CT * 2 ^ (N + 1) * (2 * (1 / w)) :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg hCT (by positivity))
    have h7 : CT * 2 ^ (N + 1) * (2 * (1 / w)) = CT * 2 ^ (N + 2) * (1 / w) := by ring
    linarith
  have hbb : ‖r2 - Δp + T0‖ ≤ ‖r2‖ + ‖Δp‖ + ‖T0‖ := by
    calc ‖r2 - Δp + T0‖ ≤ ‖r2 - Δp‖ + ‖T0‖ := norm_add_le _ _
      _ ≤ ‖r2‖ + ‖Δp‖ + ‖T0‖ := by gcongr; exact norm_sub_le _ _
  have := mul_le_mul_of_nonneg_left hbb hwp.le
  have e : w ^ (N + 1) * (‖r2‖ + ‖Δp‖ + ‖T0‖) =
      w ^ (N + 1) * ‖r2‖ + w ^ (N + 1) * ‖Δp‖ + w ^ (N + 1) * ‖T0‖ := by ring
  rw [e] at this
  linarith

/-! ### The inverse-phase germ and its Taylor polynomial -/

theorem tendsto_inv_int : Tendsto (fun n : ℤ => ((n : ℂ))⁻¹) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [KSPS015W.eventually_natAbs (⌈1 / δ⌉₊ + 1)] with n hn
  have h1 : ((⌈1 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ |(n : ℝ)| := by
    have : (((⌈1 / δ⌉₊ + 1 : ℕ) : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hn
    rwa [Int.cast_abs, Int.cast_natCast] at this
  push_cast at h1
  have h2 := Nat.le_ceil (1 / δ)
  have hpos : 0 < |(n : ℝ)| := by linarith [(Nat.cast_nonneg ⌈1 / δ⌉₊ : (0 : ℝ) ≤ _)]
  rw [dist_zero_right, norm_inv, Complex.norm_intCast, inv_lt_comm₀ hpos hδ, ← one_div]
  linarith

theorem partialSum_eq {N : ℕ} (φ : SobolevC N) (ζ : ℂ → ℂ) (hζ0 : ζ 0 = 0)
    (hcoef : ∀ k : ℕ, k ≤ N + 1 →
      KSPSRiccati.spectralCoefficient φ k = iteratedDeriv k ζ 0 / (Nat.factorial k : ℂ))
    (y : ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ (fun k => iteratedDeriv k ζ 0 / (Nat.factorial k : ℂ))).partialSum
        (N + 2) y =
      ∑ k ∈ Finset.Icc 1 (N + 1), KSPSRiccati.spectralCoefficient φ k * y ^ k := by
  unfold FormalMultilinearSeries.partialSum
  simp_rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hr : Finset.range (N + 2) = insert 0 (Finset.Icc 1 (N + 1)) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 (N + 1) := by simp
  rw [hr, Finset.sum_insert h0]
  simp only [iteratedDeriv_zero, hζ0, zero_div, zero_mul, zero_add]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [hcoef k (Finset.mem_Icc.1 hk).2]

theorem spoly_eq {N : ℕ} (φ : SobolevC N) (n : ℤ) :
    spectralPolynomial φ n = (n : ℂ) * (Real.pi : ℂ) +
      ∑ k ∈ Finset.Icc 1 (N + 1), KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k := by
  unfold spectralPolynomial
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [div_eq_mul_inv, inv_pow]

theorem lamStar_eq {N : ℕ} (φ : SobolevC N) (ζ : ℂ → ℂ) (n : ℤ) (hn : (n : ℂ) ≠ 0)
    (hne : (Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹ ≠ 0)
    (heq : ζ (n : ℂ)⁻¹ + KSPSRiccati.phasePolynomial φ (N + 1)
      ((n : ℂ)⁻¹ / ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹)) = 0) :
    ((n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹) +
      KSPSRiccati.phasePolynomial φ (N + 1) ((n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹)⁻¹ =
      (n : ℂ) * (Real.pi : ℂ) := by
  have e : ((n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹)⁻¹ =
      (n : ℂ)⁻¹ / ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹) := by
    have e1 : (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ =
        (n : ℂ) * ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹) := by
      field_simp
    rw [e1, mul_inv, div_eq_mul_inv]
  rw [e]
  linear_combination heq

/-! ### The tail estimate at one index -/

def Lsum {N : ℕ} (φ : SobolevC N) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (N + 1), (k : ℝ) * ‖integralRiccatiLeft φ k‖

def psi (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  (4 + (4 * KSPS016W.Sb φ + 4 * KSPS016W.Sb φ ^ 2)) * tau N φ n +
    indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2

def bound (N : ℕ) (φ : SobolevC N) (CT : ℝ) (n : ℤ) : ℝ :=
  psi N φ n + Lsum φ * (4 * (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
      ‖physicalFourier (iteratedDerivative N φ.2) n‖) + 2 * psi N φ n) +
    CT * 2 ^ (N + 2) * (1 / indexWeight n)

theorem tail023A (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h3 : (1 : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tau N φ n ≤ 1) :
    ∃ r2 : ℂ, indexWeight n ^ (N + 1) * ‖r2‖ ≤ psi N φ n ∧
      mu φ n + KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ) =
        (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 + r2 := by
  obtain ⟨hst, hε⟩ := sine_tail N hN φ a ha hxi n h1 h2 h3 h4
  obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a _ ha (mu φ) hxi n h1
  obtain ⟨-, hXS, -⟩ := KSPS015W.tail_facts a _ ha (mu φ) hxi n h2
  obtain ⟨hν1, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hX0 : 0 < ‖mu φ n‖ := by linarith
  have hthr : WKBThreshold N (sobolevNorm N φ) (mu φ n) := ⟨hX0, hXT⟩
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  obtain ⟨hDinv, -, hα, hβ⟩ := KSPS016W.dinv_facts φ (mu φ n) (indexWeight n) hX1 hthr hw0 hwX
  have hS0 := KSPS016W.Sb_nonneg φ
  have hq : KSPS016W.Sb φ / (2 * ‖mu φ n‖) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hα4 := hα.trans hq
  have hβ4 := hβ.trans hq
  have hD : 1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0 ≠ 0 := by
    intro h0
    have h6 : ‖KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0‖ = 1 := by
      rw [show KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0 = 1 by linear_combination -h0]
      simp
    rw [norm_mul] at h6
    linarith [mul_le_mul hα4 hβ4 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := hν1
  obtain ⟨-, -, hF1, hF2⟩ := KSPS016W.fourier_facts φ n hn1R
  -- (1) the exact sine identity at the Dirichlet root
  obtain ⟨-, hsn⟩ := shift (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n)) n
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n) with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have hsg1 : (-1 : ℂ) ^ (n + 1) = -(-1 : ℂ) ^ n := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]; ring
  have hdE : KSPSWKB.dirichletError N φ (mu φ) n = 0 -
      ((1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
        (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0) *
          (2 * Complex.I * ((-1 : ℂ) ^ n * Complex.sin ε)) +
        Complex.I * (-(-1 : ℂ) ^ n) *
          (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) +
        2 * (-(-1 : ℂ) ^ n) / (2 * Complex.I * mu φ n) ^ (N + 1) * integralRiccatiLeft φ (N + 1)) := by
    unfold KSPSWKB.dirichletError
    rw [dirichletNumerator_mu φ n, ← hθ, hsn, hsg1]
  have hsi := sine_identity _ (Complex.sin ε) _ _ _ _ _ (neg_one_zpow_mul_self n) hdE
  -- (2) eps versus sin eps
  have hsε : ‖Complex.sin ε‖ = ‖Complex.sin θ‖ := by
    rw [hsn, norm_mul, norm_neg_one_zpow, one_mul]
  have hεs := eps_le_two_sin ε hε
  have hss := norm_sin_sub_self_le ε (by linarith)
  have hQ1 := one_sub_Q_bound (indexWeight n) ‖mu φ n‖ (KSPS016W.Sb φ) (KSPSWKB.alpha φ (mu φ n) 0)
    (KSPSWKB.beta φ (mu φ n) 0) hw1 hwX hS0 hD hDinv hα hβ
  set C1 : ℝ := 4 * KSPS016W.Sb φ + 4 * KSPS016W.Sb φ ^ 2 with hC1
  have hC10 : 0 ≤ C1 := by positivity
  set r2 : ℂ := (ε - Complex.sin ε) +
    ((1 - (1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
        (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0)) * Complex.sin ε +
      Complex.I * (-1 : ℂ) ^ n * KSPSWKB.dirichletError N φ (mu φ) n / 2) with hr2def
  have hr2 : indexWeight n ^ (N + 1) * ‖r2‖ ≤ psi N φ n := by
    have hb : ‖r2‖ ≤ 4 * ‖Complex.sin θ‖ ^ 2 + C1 / indexWeight n * ‖Complex.sin θ‖ +
        ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2 := by
      have e1 : ‖ε - Complex.sin ε‖ ≤ 4 * ‖Complex.sin θ‖ ^ 2 := by
        rw [norm_sub_rev]
        refine hss.trans ?_
        rw [← hsε]
        calc ‖ε‖ ^ 2 ≤ (2 * ‖Complex.sin ε‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hεs 2
          _ = 4 * ‖Complex.sin ε‖ ^ 2 := by ring
      have e2 : ‖(1 - (1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
          (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0)) * Complex.sin ε‖ ≤
          C1 / indexWeight n * ‖Complex.sin θ‖ := by
        rw [norm_mul, hsε]
        exact mul_le_mul_of_nonneg_right hQ1 (norm_nonneg _)
      have e3 : ‖Complex.I * (-1 : ℂ) ^ n * KSPSWKB.dirichletError N φ (mu φ) n / 2‖ =
          ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2 := by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_I, norm_neg_one_zpow, Complex.norm_ofNat]
        ring
      calc ‖r2‖ ≤ ‖ε - Complex.sin ε‖ +
            (‖(1 - (1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
              (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0)) * Complex.sin ε‖ +
            ‖Complex.I * (-1 : ℂ) ^ n * KSPSWKB.dirichletError N φ (mu φ) n / 2‖) := by
            rw [hr2def]
            exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ _ := by rw [e3]; linarith
    have hsq := sq_weight_le N hN (indexWeight n) ‖Complex.sin θ‖ (tau N φ n) hw1 (norm_nonneg _) hst h5
    have hlin : indexWeight n ^ (N + 1) * (C1 / indexWeight n * ‖Complex.sin θ‖) ≤ C1 * tau N φ n := by
      have e : indexWeight n ^ (N + 1) * (C1 / indexWeight n * ‖Complex.sin θ‖) =
          C1 * (indexWeight n ^ N * ‖Complex.sin θ‖) := by
        rw [pow_succ]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hst hC10
    have hwp : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
    have h6 := mul_le_mul_of_nonneg_left hb hwp
    have e : indexWeight n ^ (N + 1) * (4 * ‖Complex.sin θ‖ ^ 2 + C1 / indexWeight n * ‖Complex.sin θ‖ +
        ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2) =
        4 * (indexWeight n ^ (N + 1) * ‖Complex.sin θ‖ ^ 2) +
          indexWeight n ^ (N + 1) * (C1 / indexWeight n * ‖Complex.sin θ‖) +
          indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2 := by ring
    rw [e] at h6
    unfold psi
    rw [← hC1]
    linarith
  -- g(mu) - n pi = G/2 + r2
  have hg : mu φ n + KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ) =
      (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 + r2 := by
    rw [phase_poly_eq φ (mu φ n), ← hθ]
    have e : θ = ε + (n : ℂ) * (Real.pi : ℂ) := by rw [hεdef]; ring
    rw [e, hr2def]
    linear_combination hsi
  exact ⟨r2, hr2, hg⟩

theorem tail023 (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (ζ : ℂ → ℂ) (CT : ℝ) (hCT : 0 ≤ CT) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h3 : (1 : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tau N φ n ≤ 1)
    (hL : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2)
    (hne : (Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹ ≠ 0)
    (heq : ζ (n : ℂ)⁻¹ + KSPSRiccati.phasePolynomial φ (N + 1)
      ((n : ℂ)⁻¹ / ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹)) = 0)
    (hsmall : ‖ζ (n : ℂ)⁻¹‖ ≤ 1)
    (htay : ‖ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
        KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k‖ ≤ CT * ‖(n : ℂ)⁻¹‖ ^ (N + 2)) :
    indexWeight n ^ (N + 1) *
      ‖mu φ n - spectralPolynomial φ n -
        (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖ ≤
      bound N φ CT n := by
  obtain ⟨r2, hr2, hg⟩ := tail023A N hN φ a ha hxi n h1 h2 h3 h4 h5
  obtain ⟨hν1, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := hν1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  obtain ⟨-, -, hF1, hF2⟩ := KSPS016W.fourier_facts φ n hn1R
  -- (3) the exact solution lam*
  have hnC : (n : ℂ) ≠ 0 := by
    intro h0
    have : (n : ℝ) = 0 := by exact_mod_cast h0
    rw [this, abs_zero] at hn1R
    linarith
  set ls : ℂ := (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ with hls
  have hgs := lamStar_eq φ ζ n hnC hne heq
  rw [← hls] at hgs
  -- norms
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hpi := Real.pi_gt_three
  have hμν : |(n : ℝ)| ≤ ‖mu φ n‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (mu φ n)
    rw [norm_sub_rev, hnpi] at h7
    have h8 : a / indexWeight n ≤ a := div_le_self ha hw1
    have h9 := hxi n
    have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
    linarith
  have hlsν : |(n : ℝ)| ≤ ‖ls‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) ls
    rw [norm_sub_rev, hnpi] at h7
    have h8 : ls - (n : ℂ) * (Real.pi : ℂ) = ζ (n : ℂ)⁻¹ := by rw [hls]; ring
    rw [h8] at h7
    have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
    linarith
  have hν0 : 0 < |(n : ℝ)| := by linarith
  have hμ0 : mu φ n ≠ 0 := by intro h0; rw [h0, norm_zero] at hμν; linarith
  have hls0 : ls ≠ 0 := by intro h0; rw [h0, norm_zero] at hlsν; linarith
  have hμi : ‖(mu φ n)⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hlsi : ‖ls⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hinv : ‖(mu φ n)⁻¹ - ls⁻¹‖ ≤ ‖mu φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    rw [inv_sub_inv hμ0 hls0, norm_div, norm_mul, norm_sub_rev]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hν0 2)
    rw [pow_two]
    exact mul_le_mul hμν hlsν hν0.le (norm_nonneg _)
  have hlip := phasePoly_lip φ (N + 1) _ _ hμi hlsi
  have hΔp : ‖KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹‖ ≤ Lsum φ * ‖mu φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
    refine hlip.trans ?_
    unfold Lsum
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hinv (Finset.sum_nonneg (fun k _ => by positivity))
  have hDeq : (mu φ n - ls) + (KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) =
      (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 + r2 := by
    rw [← hg]
    linear_combination (-1 : ℂ) * hgs
  -- Taylor error
  have hT0 : ‖ls - spectralPolynomial φ n‖ ≤ CT / |(n : ℝ)| ^ (N + 2) := by
    rw [spoly_eq, hls]
    have e : (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ - ((n : ℂ) * (Real.pi : ℂ) +
        ∑ k ∈ Finset.Icc 1 (N + 1), KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k) =
        ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
          KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k := by ring
    rw [e]
    refine htay.trans (le_of_eq ?_)
    rw [norm_inv, Complex.norm_intCast, inv_pow]
    ring
  have hG : indexWeight n ^ N *
      ‖physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n‖ ≤
      ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
        ‖physicalFourier (iteratedDerivative N φ.2) n‖ := by
    have := norm_add_le (physicalFourier (toPotPair φ).1 (-n)) (physicalFourier (toPotPair φ).2 n)
    have h8 := mul_le_mul_of_nonneg_left this (pow_nonneg hw0.le N)
    rw [mul_add] at h8
    linarith
  have hwν : indexWeight n ≤ 2 * |(n : ℝ)| := KSPS015W.w_le_two n hn1R
  have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  have hfin := final_pure N (indexWeight n) |(n : ℝ)| (Lsum φ) CT
    (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖physicalFourier (iteratedDerivative N φ.2) n‖)
    (psi N φ n) (mu φ n - ls)
    (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) r2
    (KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ - KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹)
    (ls - spectralPolynomial φ n)
    hw1 hn1R hwν hL0 hL hCT hDeq hΔp hT0 hG hr2
  have e : mu φ n - spectralPolynomial φ n -
      (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 =
      r2 - (KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ -
        KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) + (ls - spectralPolynomial φ n) := by
    linear_combination hDeq
  rw [e]
  unfold bound
  exact hfin

/-! ### The weighted estimate (conditional on the KSPS-016 head conclusion at xi = mu) -/

theorem dirichlet_spectral_expansion_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (h16 : AntiTraceDirichletWKB N φ (mu φ)) :
    WeightedL2Error (N+1)
      (fun n => mu φ n - spectralPolynomial φ n -
        (physicalFourier (toPotPair φ).1 (-n) +
         physicalFourier (toPotPair φ).2 n)/2) := by
  obtain ⟨-, hD⟩ := h16
  rw [wl2_iff] at hD
  -- the inverse-phase germ (K = N + 1)
  obtain ⟨ζ, hζa, hζ0, hev, hcoef⟩ :=
    NlsGge.ThirdConsultation.KSPS023T.spectralCoefficient_consistent φ (N + 1) le_rfl
  obtain ⟨CT0, hCT0⟩ := (hζa.hasFPowerSeriesAt.isBigO_sub_partialSum_pow (N + 2)).bound
  set CT : ℝ := max CT0 0 with hCTdef
  have hCT : 0 ≤ CT := le_max_right _ _
  have htay0 : ∀ᶠ y : ℂ in 𝓝 0, ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
      KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤ CT * ‖y‖ ^ (N + 2) := by
    filter_upwards [hCT0] with y hy
    beta_reduce at hy
    rw [zero_add, partialSum_eq φ ζ hζ0 hcoef y, norm_pow, norm_norm] at hy
    exact hy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsmall0 : ∀ᶠ y : ℂ in 𝓝 0, ‖ζ y‖ ≤ 1 := by
    have h := hζa.continuousAt.eventually (Metric.closedBall_mem_nhds (ζ 0) one_pos)
    filter_upwards [h] with y hy
    rw [dist_eq_norm, hζ0, sub_zero] at hy
    exact hy
  have et := tendsto_inv_int.eventually htay0
  have es := tendsto_inv_int.eventually hsmall0
  have ee := tendsto_inv_int.eventually hev
  -- summability of the bound
  have hF1 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2) :=
    (hasSum_physicalFourier_sq (iteratedDerivative N φ.1)).summable.comp_injective neg_injective
  have hF2 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2) :=
    (hasSum_physicalFourier_sq _).summable
  have hI : Summable (fun n : ℤ => (2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n)) ^ 2) :=
    KSPS015W.sq_summable_mul_left _ KSPS016W.sq_summable_inv_w
  have hτ : Summable (fun n : ℤ => tau N φ n ^ 2) := by
    unfold tau
    exact KSPS015W.sq_summable_add (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add hD hF1) hF2) hI
  have hψ : Summable (fun n : ℤ => psi N φ n ^ 2) := by
    have h := KSPS015W.sq_summable_add
      (KSPS015W.sq_summable_mul_left (4 + (4 * KSPS016W.Sb φ + 4 * KSPS016W.Sb φ ^ 2)) hτ)
      (KSPS015W.sq_summable_mul_left (1 / 2) hD)
    refine h.congr (fun n => ?_)
    unfold psi
    ring
  have hb : Summable (fun n : ℤ => bound N φ CT n ^ 2) := by
    have h := KSPS015W.sq_summable_add (KSPS015W.sq_summable_add hψ
      (KSPS015W.sq_summable_mul_left (Lsum φ) (KSPS015W.sq_summable_add
        (KSPS015W.sq_summable_mul_left 4 (KSPS015W.sq_summable_add hF1 hF2))
        (KSPS015W.sq_summable_mul_left 2 hψ))))
      (KSPS015W.sq_summable_mul_left (CT * 2 ^ (N + 2)) KSPS016W.sq_summable_inv_w)
    refine h.congr (fun n => ?_)
    unfold bound
    ring
  have hs : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hs]
  have e1 := KSPS015W.eventually_natAbs
    (⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)
  have e2 := KSPS015W.eventually_natAbs (⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1)
  have e3 := KSPS015W.eventually_natAbs 1
  have e4 := eventually_w_ge (2 * (a + Jsum φ))
  have e5 := eventually_le_of_sq (tau N φ) hτ 1 one_pos
  have e6 := KSPS015W.eventually_natAbs ⌈2 * Lsum φ⌉₊
  refine wl2_of_eventually N _ (bound N φ CT) hb ?_
  filter_upwards [e1, e2, e3, e4, e5, e6, et, es, ee] with n g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hL : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2 := by
    have h7 : ((⌈2 * Lsum φ⌉₊ : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g6
    rw [Int.cast_abs] at h7
    push_cast at h7
    have h8 := Nat.le_ceil (2 * Lsum φ)
    have h9 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g3
      rw [Int.cast_abs] at this
      simpa using this
    nlinarith
  exact tail023 N hN φ a ha hxi ζ CT hCT n g1 g2 (by exact_mod_cast g3) g4 g5 hL g9.1 g9.2 g8 g7

end
end NlsGge.ThirdConsultation.KSPS023W
