import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support11
import NlsGge.ThirdConsultation.KSPSSupport.NLT01
import NlsGge.ThirdConsultation.KSPSSupport.UNI01

                                                                                 
                                                                                                  
                                                                                                                
                                                                                                                     
                                                                                                 
                                                                        
                                                                 
                                                               
                                                                            
                                                           
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSQ3
noncomputable section

theorem psn_nonneg (r : ℝ) (u : PhysicalL2) : 0 ≤ physicalSobolevNorm r u := Real.sqrt_nonneg _

theorem psn_fst_le_pair (r : ℝ) (p : PotPair) : physicalSobolevNorm r p.1 ≤ pairSobolevNorm r p := by
  unfold pairSobolevNorm
  exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))

theorem R_claim_U (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∀ m : ℕ, m < N → ∃ D : ℝ, 0 ≤ D ∧ ∀ p : PotPair, pairSobolev (N : ℝ) p →
      pairSobolevNorm (N : ℝ) p ≤ K →
      physicalSobolev ((N + 1 - m : ℕ) : ℝ) (wkbR p (m + 1 + 1) + weakDerivative^[m + 1] p.2) ∧
      physicalSobolevNorm ((N + 1 - m : ℕ) : ℝ)
        (wkbR p (m + 1 + 1) + weakDerivative^[m + 1] p.2) ≤ D := by
  obtain ⟨C0, hC0, p0, hG⟩ := G1_034 N hN
  set G : ℝ := C0 * (1 + K) ^ p0 with hGdef
  have hG0 : 0 ≤ G := by positivity
  have hcoef : ∀ p : PotPair, pairSobolev (N : ℝ) p → pairSobolevNorm (N : ℝ) p ≤ K →
      ∀ i : ℕ, 1 ≤ i → i ≤ N → physicalSobolev ((N + 1 - i : ℕ) : ℝ) (wkbR p i) ∧
        physicalSobolevNorm ((N + 1 - i : ℕ) : ℝ) (wkbR p i) ≤ G := by
    intro p hp hpK i hi1 hi2
    obtain ⟨hm, hn⟩ := (hG p hp).2.2.1 i hi1 hi2
    refine ⟨hm, hn.trans ?_⟩
    have hp0 : 0 ≤ pairSobolevNorm (N : ℝ) p := Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) p0) hC0.le
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨0, le_rfl, fun p hp hpK => ?_⟩
    have h0 : wkbR p (0 + 1 + 1) + weakDerivative^[0 + 1] p.2 = 0 :=
      NlsGge.ThirdConsultation.KSPSSupport.h150_R_one p
    rw [h0]
    exact ⟨by simpa using NlsGge.ThirdConsultation.KSPSSupport.h150_zero_mem (((N + 1 - 0 : ℕ)) : ℝ),
      (NlsGge.ThirdConsultation.KSPSSupport.h161_psn_zero (N + 1 - 0)).le⟩
  | succ m ih =>
    intro hm
    obtain ⟨Dm, hDm, hR⟩ := ih (by omega)
    obtain ⟨CP, hCP, hPr⟩ := psn_prod (N - m) (by omega)
    refine ⟨2 * Real.pi * Dm + CP * K * (((m + 1 : ℕ) : ℝ) * (CP * G * G)),
      by positivity, fun p hp hpK => ?_⟩
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hRm, hRn⟩ := hR p ⟨hp1, hp2⟩ hpK
    have hW : physicalSobolev 1 (wkbR p (m + 1 + 1)) :=
      NlsGge.ThirdConsultation.KSPSSupport.h150_wkbR_H1 N hN p ⟨hp1, hp2⟩ (m + 1 + 1) (by omega) (by omega)
    have hV : physicalSobolev 1 (weakDerivative^[m + 1] p.2) :=
      g35_H1_nat _ (psn_mono (show 1 ≤ N - (m + 1) by omega)
        (NlsGge.ThirdConsultation.KSPSSupport.h150_iter_coeff N p.2 hp2 (m + 1) (by omega)).1).1
    have hrec := wkbR_succ p (m + 1 + 1) (by omega)
    have hit : weakDerivative^[m + 1 + 1] p.2 = weakDerivative (weakDerivative^[m + 1] p.2) :=
      Function.iterate_succ_apply' _ _ _
    have hfin : wkbR p (m + 1 + 1 + 1) + weakDerivative^[m + 1 + 1] p.2 =
        weakDerivative (wkbR p (m + 1 + 1) + weakDerivative^[m + 1] p.2) +
          physicalProduct p.1 (∑ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
            physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) := by
      rw [hrec, hit, g35_D_add hW hV]
      abel
    rw [hfin]
    have e1 : N + 1 - m = N - m + 1 := by omega
    rw [e1] at hRm hRn
    obtain ⟨hDmem, hDnorm⟩ := psn_deriv (N - m) hRm
    have hpA : physicalSobolev ((N - m : ℕ) : ℝ) p.1 := (psn_mono (show N - m ≤ N by omega) hp1).1
    have hpAn : physicalSobolevNorm ((N - m : ℕ) : ℝ) p.1 ≤ K :=
      ((psn_mono (show N - m ≤ N by omega) hp1).2.trans (psn_fst_le_pair _ p)).trans hpK
    have hterm : ∀ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
        physicalSobolev ((N - m : ℕ) : ℝ) (physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) ∧
        physicalSobolevNorm ((N - m : ℕ) : ℝ)
          (physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) ≤ CP * G * G := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
      obtain ⟨hAm, hAn⟩ := hcoef p ⟨hp1, hp2⟩ hpK i hi1 (by omega)
      obtain ⟨hBm, hBn⟩ := hcoef p ⟨hp1, hp2⟩ hpK (m + 1 + 1 - i) (by omega) (by omega)
      have hA := psn_mono (show N - m ≤ N + 1 - i by omega) hAm
      have hB := psn_mono (show N - m ≤ N + 1 - (m + 1 + 1 - i) by omega) hBm
      obtain ⟨hPm, hPn⟩ := hPr _ _ hA.1 hB.1
      refine ⟨hPm, hPn.trans ?_⟩
      have h1 := hA.2.trans hAn
      have h2 := hB.2.trans hBn
      have hn1 := psn_nonneg ((N - m : ℕ) : ℝ) (wkbR p i)
      have hn2 := psn_nonneg ((N - m : ℕ) : ℝ) (wkbR p (m + 1 + 1 - i))
      calc CP * physicalSobolevNorm ((N - m : ℕ) : ℝ) (wkbR p i) *
            physicalSobolevNorm ((N - m : ℕ) : ℝ) (wkbR p (m + 1 + 1 - i))
          ≤ CP * G * physicalSobolevNorm ((N - m : ℕ) : ℝ) (wkbR p (m + 1 + 1 - i)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCP.le) hn2
        _ ≤ CP * G * G := mul_le_mul_of_nonneg_left h2 (mul_nonneg hCP.le hG0)
    obtain ⟨hSm, hSn⟩ := psn_sum (N - m) (Finset.Icc 1 (m + 1 + 1 - 1))
      (fun i => physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) (fun i hi => (hterm i hi).1)
    have hSn' : physicalSobolevNorm ((N - m : ℕ) : ℝ) (∑ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
        physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) ≤ ((m + 1 : ℕ) : ℝ) * (CP * G * G) := by
      refine hSn.trans ?_
      refine (Finset.sum_le_sum (fun i hi => (hterm i hi).2)).trans (le_of_eq ?_)
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      congr 2
    obtain ⟨hPm, hPn⟩ := hPr _ _ hpA hSm
    obtain ⟨hAm, hAn⟩ := psn_add (N - m) hDmem hPm
    have e2 : N + 1 - (m + 1) = N - m := by omega
    rw [e2]
    refine ⟨hAm, hAn.trans ?_⟩
    have hq1 : physicalSobolevNorm ((N - m : ℕ) : ℝ)
        (weakDerivative (wkbR p (m + 1 + 1) + weakDerivative^[m + 1] p.2)) ≤ 2 * Real.pi * Dm :=
      hDnorm.trans (mul_le_mul_of_nonneg_left hRn (by positivity))
    have hsn0 := psn_nonneg ((N - m : ℕ) : ℝ) (∑ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
        physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i)))
    have hq2 : CP * physicalSobolevNorm ((N - m : ℕ) : ℝ) p.1 *
        physicalSobolevNorm ((N - m : ℕ) : ℝ) (∑ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
          physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) ≤
        CP * K * (((m + 1 : ℕ) : ℝ) * (CP * G * G)) :=
      calc _ ≤ CP * K * physicalSobolevNorm ((N - m : ℕ) : ℝ) (∑ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
              physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpAn hCP.le) hsn0
        _ ≤ _ := mul_le_mul_of_nonneg_left hSn' (mul_nonneg hCP.le hK)
    linarith

/-- the top remainder, order two, with a norm bound -/
theorem R_final_U (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p : PotPair, pairSobolev (N : ℝ) p → pairSobolevNorm (N : ℝ) p ≤ K →
      physicalSobolev ((2 : ℕ) : ℝ) (wkbR p (N + 1) + weakDerivative^[N] p.2) ∧
      physicalSobolevNorm ((2 : ℕ) : ℝ) (wkbR p (N + 1) + weakDerivative^[N] p.2) ≤ D := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨D, hD, h⟩ := R_claim_U (m + 1) hN K hK m (by omega)
  refine ⟨D, hD, fun p hp hpK => ?_⟩
  have hc := h p hp hpK
  have e3 : m + 1 + 1 - m = 2 := by omega
  rw [e3] at hc
  exact hc

/-- weighted Fourier sums of an H¹ field are bounded by its H¹ norm squared -/
theorem fourier_sum_le_psn1 (r : PhysicalL2) (hr : physicalSobolev ((1 : ℕ) : ℝ) r) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) (F : Finset ℤ) :
    ∑ n ∈ F, indexWeight n ^ 2 * ‖physicalFourier r (σ * n)‖ ^ 2 ≤
      physicalSobolevNorm ((1 : ℕ) : ℝ) r ^ 2 := by
  unfold physicalSobolev SobolevSquareSummable at hr
  set g : ℤ → ℝ := fun m => Real.rpow (japaneseBracket m) (2 * ((1 : ℕ) : ℝ)) *
    ‖reflectedFourierL2 r m‖ ^ 2 with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => mul_nonneg (Real.rpow_nonneg (le_of_lt (by
    unfold japaneseBracket; positivity)) _) (sq_nonneg _)
  have hpsn : physicalSobolevNorm ((1 : ℕ) : ℝ) r ^ 2 = ∑' m, g m := by
    unfold physicalSobolevNorm
    exact Real.sq_sqrt (tsum_nonneg hg0)
  have hterm : ∀ n : ℤ, indexWeight n ^ 2 * ‖physicalFourier r (σ * n)‖ ^ 2 = g (-(σ * n)) := by
    intro n
    rw [hg]
    simp only
    rw [reflectedFourierL2_apply]
    unfold reflectedFourier
    rw [neg_neg, norm_neg]
    have e : Real.rpow (japaneseBracket (-(σ * n))) (2 * ((1 : ℕ) : ℝ)) = indexWeight n ^ 2 := by
      show (japaneseBracket (-(σ * n))) ^ (2 * ((1 : ℕ) : ℝ)) = _
      rw [Nat.cast_one, mul_one, Real.rpow_two]
      unfold japaneseBracket indexWeight
      rcases hσ with rfl | rfl <;> simp
    rw [e]
  simp_rw [hterm]
  have hinj : Set.InjOn (fun n : ℤ => -(σ * n)) F := by
    intro x _ y _ h
    rcases hσ with rfl | rfl <;> simp at h <;> exact h
  rw [← Finset.sum_image (f := g) hinj, hpsn]
  exact hr.sum_le_tsum _ (fun m _ => hg0 m)

theorem coef_top_fourier_U (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ K → ∀ (b : Bool) (σ : ℤ),
      (σ = 1 ∨ σ = -1) → ∀ F : Finset ℤ,
      ∑ n ∈ F, indexWeight n ^ 2 *
        ‖physicalFourier (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) (σ * n) -
          (if b then ((-1 : ℂ) ^ (N + 1)) else (-1 : ℂ)) *
            physicalFourier (iteratedDerivative N (if b then φ.1 else φ.2)) (σ * n)‖ ^ 2 ≤ D ^ 2 := by
  obtain ⟨D, hD, hR⟩ := R_final_U N hN K hK
  refine ⟨D, hD, fun φ hS b σ hσ F => ?_⟩
  have hidx : ∀ u : PhysicalSobolev38 (N : ℝ),
      iteratedDerivative N u = weakDerivative^[N] (physicalSobolevEmbed N u) :=
    fun u => NlsGge.ThirdConsultation.KSPSSupport.physicalSobolevDerivative38_eq_iterate N u
  -- the remainder field and its bound
  have key : ∀ (p : PotPair), pairSobolev (N : ℝ) p → pairSobolevNorm (N : ℝ) p ≤ K →
      ∀ (κ : ℂ), ‖κ‖ = 1 → ∀ (c D0 : PhysicalL2) (s : ℂ),
      c = s • D0 + κ • (wkbR p (N + 1) + weakDerivative^[N] p.2) →
      ∑ n ∈ F, indexWeight n ^ 2 * ‖physicalFourier c (σ * n) - s * physicalFourier D0 (σ * n)‖ ^ 2 ≤
        D ^ 2 := by
    intro p hp hpK κ hκ c D0 s hc
    obtain ⟨hm, hn⟩ := hR p hp hpK
    generalize wkbR p (N + 1) + weakDerivative^[N] p.2 = R at hc hm hn
    have hm1 := psn_mono (show 1 ≤ 2 by norm_num) hm
    have hsum := fourier_sum_le_psn1 _ hm1.1 σ hσ F
    have he : ∀ n : ℤ, ‖physicalFourier c (σ * n) - s * physicalFourier D0 (σ * n)‖ =
        ‖physicalFourier R (σ * n)‖ := by
      intro n
      rw [hc, NlsGge.ThirdConsultation.KSPSWKB.pF_add, NlsGge.ThirdConsultation.KSPSWKB.pF_smul,
        NlsGge.ThirdConsultation.KSPSWKB.pF_smul, add_sub_cancel_left, norm_mul, hκ, one_mul]
    simp_rw [he]
    refine hsum.trans ?_
    have h0 := psn_nonneg ((1 : ℕ) : ℝ) R
    exact pow_le_pow_left₀ h0 (hm1.2.trans hn) 2
  cases b
  · refine key (toPotPair φ) (NlsGge.ThirdConsultation.KSPSSupport.pairSobolev_toPotPair φ)
      ((NlsGge.ThirdConsultation.KSPSSupport.h161_pair_le N φ).trans hS) 1 (by simp) _ _ _ ?_
    simp only [Bool.false_eq_true, if_false, one_smul]
    rw [NlsGge.ThirdConsultation.KSPSSupport.h150_coef_false, hidx]
    show _ = (-1 : ℂ) • weakDerivative^[N] (toPotPair φ).2 + _
    rw [neg_one_smul]; abel
  · refine key (Prod.swap (toPotPair φ)) (NlsGge.ThirdConsultation.KSPSSupport.pairSobolev_swap_toPotPair φ)
      ((NlsGge.ThirdConsultation.KSPSSupport.h161_pair_swap_le N φ).trans hS)
      ((-1 : ℂ) ^ (N + 1 + 1)) (by simp) _ _ _ ?_
    simp only [if_true]
    rw [NlsGge.ThirdConsultation.KSPSSupport.h150_coef_true, hidx]
    show _ = ((-1 : ℂ) ^ (N + 1)) • weakDerivative^[N] (toPotPair φ).1 + _
    have hc3 : (-1 : ℂ) ^ (N + 1 + 1) = -(-1 : ℂ) ^ (N + 1) := by rw [pow_succ]; ring
    rw [hc3, neg_smul, smul_add]
    simp only [Prod.snd_swap, neg_smul]
    abel

end
end NlsGge.ThirdConsultation.KSPSQ3
