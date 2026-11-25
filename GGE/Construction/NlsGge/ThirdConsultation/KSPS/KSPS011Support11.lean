import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support1
import NlsGge.ThirdConsultation.KSPS.KSPS011Support9
import NlsGge.ThirdConsultation.KSPSSupport.NLT01
import NlsGge.ThirdConsultation.KSPSSupport.CORE01
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.Sobolev.PeriodicBridge

                                                                                                                                                                 
                                                                                                 
                                                                                                                   
                                                                                                               
                                                                                                                                
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

def RealSqSummable (f : ℤ → ℝ) : Prop := Summable (fun n : ℤ => f n ^ 2)

theorem RealSqSummable.add {f g : ℤ → ℝ} (hf : RealSqSummable f) (hg : RealSqSummable g) :
    RealSqSummable (fun n => f n + g n) := by
  unfold RealSqSummable at *
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ((hf.mul_left 2).add (hg.mul_left 2))
  nlinarith [sq_nonneg (f n - g n)]

theorem RealSqSummable.mul_left {f : ℤ → ℝ} (K : ℝ) (hf : RealSqSummable f) :
    RealSqSummable (fun n => K * f n) := by
  unfold RealSqSummable at *
  simp_rw [mul_pow]
  exact hf.mul_left _

theorem RealSqSummable.of_eventually_le {f g : ℤ → ℝ} (hg : RealSqSummable g)
    (h : ∀ᶠ n in Filter.cofinite, |f n| ≤ |g n|) : RealSqSummable f := by
  unfold RealSqSummable at *
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [h] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc f n ^ 2 = |f n| ^ 2 := (sq_abs _).symm
    _ ≤ |g n| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hn 2
    _ = g n ^ 2 := sq_abs _

theorem eventually_cofinite_natAbs (N0 : ℕ) : ∀ᶠ n : ℤ in Filter.cofinite, (N0 : ℤ) ≤ |n| := by
  rw [Filter.eventually_cofinite]
  apply (Set.finite_Icc (-(N0 : ℤ)) N0).subset
  intro n hn
  simp only [Set.mem_setOf_eq, not_le] at hn
  rw [Set.mem_Icc]
  constructor <;> [skip; skip] <;> cases abs_cases n <;> omega

theorem squareSummable_of_bound (e : ℤ → ℂ) (t : ℤ → ℝ) (ht : RealSqSummable t) (K : ℝ) (N0 : ℕ)
    (h : ∀ n : ℤ, (N0 : ℤ) ≤ |n| → ‖e n‖ ≤ K * t n) (ht0 : ∀ n, 0 ≤ t n) :
    SquareSummable (e) := by
  have h2 := (ht.mul_left K)
  have : RealSqSummable (fun n => ‖e n‖) := by
    refine RealSqSummable.of_eventually_le h2 ?_
    filter_upwards [eventually_cofinite_natAbs N0] with n hn
    rw [abs_of_nonneg (norm_nonneg _)]
    exact (h n hn).trans (le_abs_self _)
  exact this

theorem indexWeight_neg011 (n : ℤ) : indexWeight (-n) = indexWeight n := by
  unfold indexWeight
  simp

theorem neg_one_zpow_neg (n : ℤ) : (-1 : ℂ) ^ (-n) = (-1 : ℂ) ^ n := by
  rw [zpow_neg, ← inv_zpow, inv_neg_one]

theorem pF_add (f g : PhysicalL2) (m : ℤ) :
    physicalFourier ((f + g : PhysicalL2)) m = physicalFourier f m + physicalFourier g m := by
  rw [← physicalFourierL2_apply, ← physicalFourierL2_apply, ← physicalFourierL2_apply, map_add]
  first | done | rfl | simp

theorem pF_smul (c : ℂ) (f : PhysicalL2) (m : ℤ) :
    physicalFourier (c • f : PhysicalL2) m = c * physicalFourier f m := by
  rw [← physicalFourierL2_apply, ← physicalFourierL2_apply, map_smul]
  first | done | rfl | simp

/-- the parameter data: xi n = n pi + beta n, |beta n| <= a / indexWeight n -/
theorem osc_pert_seq {u : PhysicalL2} (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Summable (fun n : ℤ => indexWeight n ^ 2 *
      ‖endpointOsc ((σ : ℂ) * xi n) (coverRep38 u) - (-1 : ℂ) ^ n * physicalFourier u (σ * n)‖ ^ 2) := by
  have hH := NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc u
  rcases hσ with rfl | rfl
  · have h := endpointOsc_pert_summable hH a ha (fun n => xi n - (n : ℂ) * Real.pi) hxi
    refine h.congr (fun n => ?_)
    simp only [add_sub_cancel, endpointOsc_natPi_coverRep, Int.cast_one, one_mul]
  · have hβ : ∀ m : ℤ, ‖-(xi (-m) - ((-m : ℤ) : ℂ) * Real.pi)‖ ≤ a / indexWeight m := by
      intro m
      rw [norm_neg]
      have := hxi (-m)
      rwa [indexWeight_neg011] at this
    have h := endpointOsc_pert_summable hH a ha (fun m => -(xi (-m) - ((-m : ℤ) : ℂ) * Real.pi)) hβ
    have h2 := (Equiv.neg ℤ).summable_iff.2 h
    refine h2.congr (fun n => ?_)
    simp only [Function.comp, Equiv.neg_apply, indexWeight_neg011, endpointOsc_natPi_coverRep, neg_neg,
      neg_one_zpow_neg]
    have e : ((-n : ℤ) : ℂ) * (Real.pi : ℂ) + -(xi n - ((n : ℂ)) * Real.pi) = ((-1 : ℤ) : ℂ) * xi n := by
      push_cast; ring
    rw [e]
    simp

theorem osc_sq_seq {H : ℝ → ℂ} (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)
    (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Summable (fun n : ℤ => ‖endpointOsc ((σ : ℂ) * xi n) H‖ ^ 2) := by
  rcases hσ with rfl | rfl
  · have h := endpointOsc_sq_summable hH a ha (fun n => xi n - (n : ℂ) * Real.pi) hxi
    refine h.congr (fun n => ?_)
    simp only [add_sub_cancel, Int.cast_one, one_mul]
  · have hβ : ∀ m : ℤ, ‖-(xi (-m) - ((-m : ℤ) : ℂ) * Real.pi)‖ ≤ a / indexWeight m := by
      intro m
      rw [norm_neg]
      have := hxi (-m)
      rwa [indexWeight_neg011] at this
    have h := endpointOsc_sq_summable hH a ha (fun m => -(xi (-m) - ((-m : ℤ) : ℂ) * Real.pi)) hβ
    have h2 := (Equiv.neg ℤ).summable_iff.2 h
    refine h2.congr (fun n => ?_)
    simp only [Function.comp, Equiv.neg_apply, neg_neg]
    have e : ((-n : ℤ) : ℂ) * (Real.pi : ℂ) + -(xi n - ((n : ℂ)) * Real.pi) = ((-1 : ℤ) : ℂ) * xi n := by
      push_cast; ring
    rw [e]

theorem sobolev_fourier_summable {r : PhysicalL2} {m : ℕ} (hm : 1 ≤ m)
    (hr : physicalSobolev (m : ℝ) r) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Summable (fun n : ℤ => indexWeight n ^ 2 * ‖physicalFourier r (σ * n)‖ ^ 2) := by
  have h1 := (psn_mono hm hr).1
  unfold physicalSobolev SobolevSquareSummable at h1
  have h2 : Summable (fun n : ℤ => indexWeight n ^ 2 * ‖physicalFourier r (-n)‖ ^ 2) := by
    refine h1.congr (fun n => ?_)
    rw [reflectedFourierL2_apply]
    unfold reflectedFourier
    rw [norm_neg]
    have : Real.rpow (japaneseBracket n) (2 * ((1 : ℕ) : ℝ)) = indexWeight n ^ 2 := by
      show (japaneseBracket n) ^ (2 * ((1 : ℕ) : ℝ)) = _
      rw [Nat.cast_one, mul_one, Real.rpow_two]
      rfl
    rw [this]
  rcases hσ with rfl | rfl
  · have h3 := (Equiv.neg ℤ).summable_iff.2 h2
    refine h3.congr (fun n => ?_)
    simp [indexWeight_neg011]
  · refine h2.congr (fun n => ?_)
    simp

theorem physicalSobolev_smul' {m : ℕ} (c : ℂ) {u : PhysicalL2} (hu : physicalSobolev (m : ℝ) u) :
    physicalSobolev (m : ℝ) (c • u) := by
  unfold physicalSobolev SobolevSquareSummable at *
  have := hu.mul_left (‖c‖ ^ 2)
  refine this.congr (fun n => ?_)
  rw [NlsGge.ThirdConsultation.KSPSSupport.reflectedFourierL2_smul_apply, norm_mul, mul_pow]
  ring

theorem coef_top_decomp {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) :
    ∃ r : PhysicalL2, physicalSobolev ((2 : ℕ) : ℝ) r ∧
      NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1) =
        (if b then ((-1 : ℂ) ^ (N + 1)) else (-1 : ℂ)) •
          iteratedDerivative N (if b then φ.1 else φ.2) + r := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hp : pairSobolev (((m + 1 : ℕ)) : ℝ) (toPotPair φ) :=
    ⟨NlsGge.ThirdConsultation.KSPSSupport.physicalSobolevEmbed_mem _ _,
     NlsGge.ThirdConsultation.KSPSSupport.physicalSobolevEmbed_mem _ _⟩
  have hidx : ∀ u : NlsGge.Atomic.Common.PhysicalSobolev38 ((m + 1 : ℕ) : ℝ),
      iteratedDerivative (m + 1) u = weakDerivative^[m + 1] (physicalSobolevEmbed (m + 1) u) :=
    fun u => NlsGge.ThirdConsultation.KSPSSupport.physicalSobolevDerivative38_eq_iterate (m + 1) u
  have h2 : m + 1 + 1 - m = 2 := by omega
  cases b
  · have hc := NlsGge.ThirdConsultation.KSPSSupport.h150_R_claim (m + 1) hN (toPotPair φ) hp m
      (Nat.lt_succ_self m)
    rw [h2] at hc
    refine ⟨_, hc, ?_⟩
    have e1 : NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (m + 1 + 1) =
        wkbR (toPotPair φ) (m + 1 + 1) := rfl
    rw [e1]
    simp only [Bool.false_eq_true, if_false]
    rw [hidx]
    show _ = (-1 : ℂ) • weakDerivative^[m + 1] (toPotPair φ).2 + _
    rw [neg_one_smul]; abel
  · have hc := NlsGge.ThirdConsultation.KSPSSupport.h150_R_claim (m + 1) hN (Prod.swap (toPotPair φ))
      ⟨hp.2, hp.1⟩ m (Nat.lt_succ_self m)
    rw [h2] at hc
    refine ⟨((-1 : ℂ) ^ (m + 1 + 1 + 1)) • (wkbR (Prod.swap (toPotPair φ)) (m + 1 + 1) +
      weakDerivative^[m + 1] (Prod.swap (toPotPair φ)).2), physicalSobolev_smul' _ hc, ?_⟩
    rw [NlsGge.ThirdConsultation.KSPSSupport.h150_coef_true]
    simp only [if_true]
    rw [hidx]
    show _ = ((-1 : ℂ) ^ (m + 1 + 1)) • weakDerivative^[m + 1] (toPotPair φ).1 + _
    have hc3 : (-1 : ℂ) ^ (m + 1 + 1 + 1) = -(-1 : ℂ) ^ (m + 1 + 1) := by rw [pow_succ]; ring
    rw [hc3, neg_smul, smul_add]
    simp only [Prod.snd_swap, neg_smul]
    abel

theorem coef_top_fourier {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) :
    Summable (fun n : ℤ => indexWeight n ^ 2 *
      ‖physicalFourier (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) (σ * n) -
        (if b then ((-1 : ℂ) ^ (N + 1)) else (-1 : ℂ)) *
          physicalFourier (iteratedDerivative N (if b then φ.1 else φ.2)) (σ * n)‖ ^ 2) := by
  obtain ⟨r, hr, he⟩ := coef_top_decomp hN φ b
  have h := sobolev_fourier_summable (by norm_num) hr σ hσ
  refine h.congr (fun n => ?_)
  rw [he, pF_add, pF_smul, add_sub_cancel_left]

end NlsGge.ThirdConsultation.KSPSWKB
