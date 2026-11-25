import Mathlib
import NlsGge.Atomic.G1.G1054
import NlsGge.Atomic.KSPS.KSPS020
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU1

                                                                                 
                                                                                                            
                                             
                                                                                                                  
                                                                                                                     
                                                                                                                      
                                                                                          
                                                                                                                
                                                                               
                                                                                                           
                                                                                                          
                                                                                             
                                                                                                                          
                                                                                                               
                                                            
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS025U4
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPS
open NlsGge.Atomic.G1049S1

/-! ### (1) G1-054 on the compact set `Cset B` -/

theorem g1054_cover (B : ℝ) (hB : 0 ≤ B) :
    ∃ (M : ℕ) (C : ℝ), 0 < C ∧ ∀ ψ ∈ Cset B, ∃ a : ℤ → ℂ,
      (∀ n : ℤ, (M : ℤ) ≤ |n| →
        lamDot ψ n - (lamPlus ψ n + lamMinus ψ n) / 2 = (lamPlus ψ n - lamMinus ψ n) ^ 2 * a n) ∧
      (∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) → ∑ n ∈ F, ‖a n‖ ^ 2 ≤ C) := by
  choose Nf Cf hCf V hV hVa using NlsGge.Atomic.G1054S3.Final.G1054_main
  obtain ⟨t, -, hcov⟩ := (isCompact_Cset hB).elim_nhds_subcover V (fun x _ => hV x)
  refine ⟨∑ x ∈ t, Nf x, 1 + ∑ x ∈ t, Cf x, ?_, fun ψ hψ => ?_⟩
  · have : 0 ≤ ∑ x ∈ t, Cf x := Finset.sum_nonneg (fun x _ => (hCf x).le)
    linarith
  obtain ⟨x, hx, hψx⟩ := Set.mem_iUnion₂.1 (hcov hψ)
  obtain ⟨a, hid, hsum⟩ := hVa x ψ hψx
  have hNx : (Nf x : ℤ) ≤ ((∑ y ∈ t, Nf y : ℕ) : ℤ) := by
    exact_mod_cast Finset.single_le_sum (f := Nf) (fun _ _ => Nat.zero_le _) hx
  have hCx : Cf x ≤ 1 + ∑ y ∈ t, Cf y := by
    have := Finset.single_le_sum (f := Cf) (fun y _ => (hCf y).le) hx
    linarith
  refine ⟨a, fun n hn => hid n (hNx.trans hn), fun F hF => ?_⟩
  exact (hsum F (fun n hn => hNx.trans (hF n hn))).trans hCx

/-! ### (2) The same on the order-N Sobolev ball (KSPS carrier) -/

theorem g1054_ball (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ (M : ℕ) (C : ℝ), 0 < C ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ a : ℤ → ℂ,
      (∀ n : ℤ, (M : ℤ) ≤ |n| →
        criticalEigenvalue φ n - (periodicPlus φ n + periodicMinus φ n) / 2 =
          (periodicPlus φ n - periodicMinus φ n) ^ 2 * a n) ∧
      (∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) → ∑ n ∈ F, ‖a n‖ ^ 2 ≤ C) := by
  obtain ⟨M, C, hC, h⟩ := g1054_cover B₀ hB₀
  refine ⟨M, C, hC, fun φ hφ => ?_⟩
  have hmem : toPotPair φ ∈ Cset B₀ := by
    have h1 := NlsGge.ThirdConsultation.KSPS019Support.toPotPair_mem_Cset
      (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      ((NlsGge.ThirdConsultation.KSPSU1.sobolevNorm_toOne_le hN φ).trans hφ)
    rwa [NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne] at h1
  obtain ⟨a, hid, hsum⟩ := h (toPotPair φ) hmem
  exact ⟨a, hid, hsum⟩

/-! ### (3) Ball-uniform localization of both periodic endpoints at all labels -/

theorem periodicPlus_toOne {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (n : ℤ) :
    periodicPlus (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ) n = periodicPlus φ n := by
  unfold periodicPlus; rw [NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne]

theorem periodicMinus_toOne {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (n : ℤ) :
    periodicMinus (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ) n = periodicMinus φ n := by
  unfold periodicMinus; rw [NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne]

/-- Low labels: both periodic endpoints of a potential with root counting at cutoff `N1` lie within
    `countingRadius38 N1 + N1 π` of `n π`. -/
theorem low_label_periodic {ψ : PotPair} {N1 : ℕ} (hp : RootCountingAt38 (perChar ψ) 2 N1) (n : ℤ) :
    ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ countingRadius38 N1 + N1 * Real.pi ∧
    ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ countingRadius38 N1 + N1 * Real.pi := by
  have hpi := Real.pi_pos
  have hR0 : 0 ≤ countingRadius38 N1 := (countingRadius_pos38 N1).le
  have hN0 : (0 : ℝ) ≤ N1 * Real.pi := by positivity
  by_cases hn : (N1 : ℤ) < |n|
  · obtain ⟨h1, h2⟩ := NlsGge.ThirdConsultation.KSPS020Support.labels_mem_ball hp hn
    have h3 : Real.pi / 4 ≤ countingRadius38 N1 := by
      unfold countingRadius38; linarith
    exact ⟨by linarith, by linarith⟩
  · push_neg at hn
    have hab := abs_le.mp hn
    have habsR : |(n : ℝ)| ≤ N1 := by exact_mod_cast hn
    have hS := lamSeq_eq_candidate38 ψ hp
    have hc1 : periodicCentralIndex38 N1 (2 * n) := by
      unfold periodicCentralIndex38; omega
    have hc2 : periodicCentralIndex38 N1 (2 * n + 1) := by
      unfold periodicCentralIndex38; omega
    have g1 := periodicCandidate_central_mem38 hp hc1
    have g2 := periodicCandidate_central_mem38 hp hc2
    rw [Metric.mem_ball, dist_zero_right] at g1 g2
    have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ ≤ N1 * Real.pi := by
      rw [NlsGge.ThirdConsultation.KSN012U.sup6_norm_npi]
      exact mul_le_mul_of_nonneg_right habsR hpi.le
    have e1 : lamMinus ψ n = periodicCandidate38 (perChar ψ) N1 (2 * n) := by
      unfold lamMinus; rw [hS]
    have e2 : lamPlus ψ n = periodicCandidate38 (perChar ψ) N1 (2 * n + 1) := by
      unfold lamPlus; rw [hS]
    rw [e1, e2]
    constructor
    · calc _ ≤ ‖periodicCandidate38 (perChar ψ) N1 (2 * n)‖ + ‖(n : ℂ) * (Real.pi : ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    · calc _ ≤ ‖periodicCandidate38 (perChar ψ) N1 (2 * n + 1)‖ + ‖(n : ℂ) * (Real.pi : ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith

theorem periodic_loc_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ n : ℤ,
      ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n ∧
      ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := by
  obtain ⟨C, N0, hC, h20⟩ := rough_periodic_endpoints (B₀ + 1) (by linarith)
  obtain ⟨N1, hcount⟩ := NlsGge.ThirdConsultation.KSPS020Support.unif_periodic_counting
    (B := B₀ + 1) (by linarith)
  have hpi := Real.pi_pos
  set M : ℕ := N0 + N1 + 1 with hM
  set K : ℝ := countingRadius38 N1 + N1 * Real.pi with hK
  have hK0 : 0 ≤ K := by
    have := (countingRadius_pos38 N1).le
    have : (0 : ℝ) ≤ N1 * Real.pi := by positivity
    linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  refine ⟨2 * C + K * (1 + M), by positivity, fun φ hφ n => ?_⟩
  set φ' := NlsGge.ThirdConsultation.KSPSU1.toOne hN φ with hφ'
  have hφ1 : sobolevNorm 1 φ' ≤ B₀ + 1 := by
    have := NlsGge.ThirdConsultation.KSPSU1.sobolevNorm_toOne_le hN φ
    linarith
  have hw1 := NlsGge.ThirdConsultation.KSN012U.sup6_one_le_w n
  have hw0 := NlsGge.ThirdConsultation.KSN012U.sup6_w_pos n
  have hKM0 : 0 ≤ K * (1 + M) := by positivity
  rw [← periodicPlus_toOne hN φ n, ← periodicMinus_toOne hN φ n, ← hφ']
  by_cases hn : M ≤ n.natAbs
  · have hb := h20 φ' hφ1 n (by omega)
    rw [NlsGge.ThirdConsultation.KSN012U.sup6_natAbs_cast] at hb
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← NlsGge.ThirdConsultation.KSN012U.sup6_natAbs_cast]; exact_mod_cast (show 1 ≤ n.natAbs by omega)
    have hpos : 0 < |(n : ℝ)| := by linarith
    have hw2 := NlsGge.ThirdConsultation.KSN012U.sup6_w_le_two n hn1
    have hCn : C / |(n : ℝ)| ≤ (2 * C + K * (1 + M)) / indexWeight n := by
      rw [div_le_div_iff₀ hpos hw0]
      nlinarith [mul_le_mul_of_nonneg_left hw2 hC, mul_nonneg hKM0 hpos.le]
    exact ⟨(le_max_left _ _).trans (hb.trans hCn), (le_max_right _ _).trans (hb.trans hCn)⟩
  · have hwM : indexWeight n ≤ 1 + M :=
      NlsGge.ThirdConsultation.KSN012U.sup6_w_le_of_natAbs n M (by omega)
    have hKw : K ≤ (2 * C + K * (1 + M)) / indexWeight n := by
      rw [le_div_iff₀ hw0]
      have := mul_le_mul_of_nonneg_left hwM hK0
      linarith
    have hp := hcount (toPotPair φ')
      (NlsGge.ThirdConsultation.KSPS019Support.toPotPair_mem_Cset φ' hφ1)
    obtain ⟨h1, h2⟩ := low_label_periodic hp n
    exact ⟨(show ‖lamPlus (toPotPair φ') n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ _ from h2.trans hKw),
      (show ‖lamMinus (toPotPair φ') n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ _ from h1.trans hKw)⟩

end
end NlsGge.ThirdConsultation.KSPS025U4
