import Mathlib
import NlsGge.Atomic.KSPS.KSPS019
import NlsGge.ThirdConsultation.KSPS.KSPS020Host
import NlsGge.ThirdConsultation.KSPS.KSPS020Support

                                                                                                     
                                                                                                                           
                                                                                                                   
                                                                                                                                   
                                                                                                                                    
                                                                                                                              
                                                                                                                                 
                                                                             
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem rough_periodic_endpoints :
  ∀ B : ℝ, 0 < B →
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
    ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
      ∀ n : ℤ, N ≤ n.natAbs →
        max ‖periodicPlus φ n-(n:ℂ)*Real.pi‖
            ‖periodicMinus φ n-(n:ℂ)*Real.pi‖ ≤
          C/(n.natAbs:ℝ) := by
  intro B hB
  have hB0 : 0 ≤ B := hB.le
  obtain ⟨Ca, Na, hCa, ha⟩ := rough_boundary_roots B hB
  obtain ⟨C0, L0, hC0, hL0, h0⟩ := spectral_derivative_rough_complete 0 B 1 hB0 zero_le_one
  obtain ⟨C1, L1, hC1, hL1, h1⟩ := spectral_derivative_rough_complete 1 B 1 hB0 zero_le_one
  obtain ⟨Nb, hNb⟩ := NlsGge.ThirdConsultation.KSPS020Support.unif_periodic_counting hB0
  set K : ℝ := C0 + C1 + Ca + (C0 + C1) ^ 2 + C0 ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  have hsq1 := sq_nonneg (C0 + C1)
  have hsq2 := sq_nonneg C0
  have hC0K : C0 ≤ K := by rw [hKdef]; linarith
  have hC1K : C1 ≤ K := by rw [hKdef]; linarith
  have hCaK : Ca ≤ K := by rw [hKdef]; linarith
  have hCsq : (C0 + C1) ^ 2 + C0 ^ 2 ≤ K := by rw [hKdef]; linarith
  refine ⟨39 * K + 1, Na + Nb + 1 + ⌈L0⌉₊ + ⌈L1⌉₊ + ⌈2 * K⌉₊, by positivity, ?_⟩
  intro φ hφ n hn
  have hCset := NlsGge.ThirdConsultation.KSPS019Support.toPotPair_mem_Cset φ hφ
  have hn1 : 1 ≤ n.natAbs := by omega
  have hnb : Nb < n.natAbs := by omega
  have hna : Na ≤ n.natAbs := by omega
  set ν : ℝ := (n.natAbs : ℝ) with hν
  have hν1 : (1 : ℝ) ≤ ν := by rw [hν]; exact_mod_cast hn1
  have hνpos : 0 < ν := lt_of_lt_of_le one_pos hν1
  have hL0ν : L0 ≤ ν := by
    have h := Nat.le_ceil L0
    have : ((⌈L0⌉₊ : ℕ) : ℝ) ≤ ν := by rw [hν]; exact_mod_cast (by omega : ⌈L0⌉₊ ≤ n.natAbs)
    linarith
  have hL1ν : L1 ≤ ν := by
    have h := Nat.le_ceil L1
    have : ((⌈L1⌉₊ : ℕ) : ℝ) ≤ ν := by rw [hν]; exact_mod_cast (by omega : ⌈L1⌉₊ ≤ n.natAbs)
    linarith
  have hKν2 : 2 * K ≤ ν := by
    have h := Nat.le_ceil (2 * K)
    have : ((⌈2 * K⌉₊ : ℕ) : ℝ) ≤ ν := by rw [hν]; exact_mod_cast (by omega : ⌈2 * K⌉₊ ≤ n.natAbs)
    linarith
  have hKν : K / ν ≤ 7 / 10 := by
    rw [div_le_iff₀ hνpos]; nlinarith
  set c : ℂ := (n : ℂ) * (Real.pi : ℂ) with hc
  set ψ := toPotPair φ with hψ
  -- fixed-strip bounds on the whole quarter disc
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hrad : ∀ z ∈ Metric.ball c (Real.pi / 4), 2 * ν ≤ ‖z‖ ∧ |z.im| ≤ 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact NlsGge.ThirdConsultation.KSPS020Support.ball_facts hz hn1
  have hD0 : ∀ z : ℂ, L0 ≤ ‖z‖ → |z.im| ≤ 1 →
      ‖NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ 1 z - freePropagator 1 z‖ ≤ C0 / ‖z‖ := by
    intro z hz1 hz2
    obtain ⟨-, hD, hsup⟩ := h0 φ hφ z hz1 hz2
    have hD1 := hD 1 ⟨zero_le_one, le_rfl⟩
    rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, iteratedDeriv_zero, iteratedDeriv_zero] at hD1
    exact hD1.trans hsup
  have hD1 : ∀ z : ℂ, L1 ≤ ‖z‖ → |z.im| ≤ 1 →
      ‖deriv (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ 1 l) z -
        deriv (fun l : ℂ => freePropagator 1 l) z‖ ≤ C1 / ‖z‖ := by
    intro z hz1 hz2
    obtain ⟨-, hD, hsup⟩ := h1 φ hφ z hz1 hz2
    have hD1 := hD 1 ⟨zero_le_one, le_rfl⟩
    rw [show ((1 : Fin 3) : ℕ) = 1 from rfl, iteratedDeriv_one, iteratedDeriv_one] at hD1
    exact hD1.trans hsup
  have hdiv : ∀ {C : ℝ} {z : ℂ}, 0 ≤ C → 2 * ν ≤ ‖z‖ → C / ‖z‖ ≤ C / (2 * ν) := fun hC hz =>
    div_le_div_of_nonneg_left hC (by positivity) hz
  have hQ0 : ∀ z ∈ Metric.ball c (Real.pi / 4),
      ‖NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ 1 z - freePropagator 1 z‖ ≤ C0 / (2 * ν) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hrad z hz
    exact (hD0 z (by linarith) hz2).trans (hdiv hC0 hz1)
  have hQ1 : ∀ z ∈ Metric.ball c (Real.pi / 4),
      ‖deriv (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ 1 l) z -
        deriv (fun l : ℂ => freePropagator 1 l) z‖ ≤ C1 / (2 * ν) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hrad z hz
    exact (hD1 z (by linarith) hz2).trans (hdiv hC1 hz1)
  have hCdiv : ∀ C : ℝ, 0 ≤ C → C ≤ K → 2 * (C / (2 * ν)) ≤ K / ν := by
    intro C hC hCK
    have : 2 * (C / (2 * ν)) = C / ν := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right hCK hνpos.le
  have hh0 : ∀ z ∈ Metric.ball c (Real.pi / 4),
      ‖NlsGge.GK38.discrim ψ z - 2 * Complex.cos z‖ ≤ K / ν := by
    intro z hz
    exact (NlsGge.ThirdConsultation.KSPS020Support.disc_sub_two_cos_le φ z).trans
      ((mul_le_mul_of_nonneg_left (hQ0 z hz) (by norm_num)).trans (hCdiv C0 hC0 hC0K))
  have hh1 : ∀ z ∈ Metric.ball c (Real.pi / 4),
      DifferentiableAt ℂ (NlsGge.GK38.discrim ψ) z ∧
      ‖deriv (NlsGge.GK38.discrim ψ) z + 2 * Complex.sin z‖ ≤ K / ν := by
    intro z hz
    refine ⟨NlsGge.ThirdConsultation.KSPS020Support.differentiableAt_discrim φ z, ?_⟩
    exact (NlsGge.ThirdConsultation.KSPS020Support.deriv_disc_add_two_sin_le φ z).trans
      ((mul_le_mul_of_nonneg_left (hQ1 z hz) (by norm_num)).trans (hCdiv C1 hC1 hC1K))
  -- the critical root
  have hcrit := (ha φ hφ n hna)
  have hcr1 : ‖NlsGge.GK38.lamDot ψ n - c‖ ≤ Ca / ν := by
    have : ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Ca / ν := by
      have := norm_nonneg (mu φ n - (n : ℂ) * (Real.pi : ℂ))
      linarith
    exact this
  have hCaν : Ca / ν ≤ 1 / 2 := by
    rw [div_le_iff₀ hνpos]; nlinarith
  have hcr2 : ‖NlsGge.GK38.lamDot ψ n - c‖ ≤ K / ν :=
    hcr1.trans (div_le_div_of_nonneg_right hCaK hνpos.le)
  have hcrball : NlsGge.GK38.lamDot ψ n ∈ Metric.ball c (Real.pi / 4) := by
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [Real.pi_gt_d2]
  have hcrroot : deriv (NlsGge.GK38.discrim ψ) (NlsGge.GK38.lamDot ψ n) = 0 :=
    (NlsGge.GK38.lamDot_enumeration38 ψ).1 n
  have hcid : ‖NlsGge.GK38.discrim ψ (NlsGge.GK38.lamDot ψ n) ^ 2 - 4‖ ≤ K / ν ^ 2 := by
    set l' := NlsGge.GK38.lamDot ψ n with hl'
    obtain ⟨hz1, hz2⟩ := hrad l' hcrball
    have hs := NlsGge.ThirdConsultation.KSPS019Support.sin_le_of_critical_root φ l' hcrroot
    have hb := NlsGge.ThirdConsultation.KSPS020Support.sq_sub_four_le φ l'
    have ha0 := hQ0 l' hcrball
    have hsin : ‖Complex.sin l'‖ ≤ C1 / (2 * ν) := hs.trans (hQ1 l' hcrball)
    set a := ‖NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ 1 l' - freePropagator 1 l'‖ with ha_
    set b := ‖Complex.sin l'‖ with hb_
    have hapos : 0 ≤ a := norm_nonneg _
    have hbpos : 0 ≤ b := norm_nonneg _
    have e1 : 2 * a + 2 * b ≤ (C0 + C1) / ν := by
      have : (C0 + C1) / ν = 2 * (C0 / (2 * ν)) + 2 * (C1 / (2 * ν)) := by field_simp
      rw [this]; linarith
    have e2 : 2 * a ≤ C0 / ν := by
      have : C0 / ν = 2 * (C0 / (2 * ν)) := by field_simp
      rw [this]; linarith
    have e3 : (2 * a + 2 * b) ^ 2 + 4 * a ^ 2 ≤ (C0 + C1) ^ 2 / ν ^ 2 + C0 ^ 2 / ν ^ 2 := by
      have s1 : (2 * a + 2 * b) ^ 2 ≤ ((C0 + C1) / ν) ^ 2 :=
        pow_le_pow_left₀ (by positivity) e1 2
      have s2 : (2 * a) ^ 2 ≤ (C0 / ν) ^ 2 := pow_le_pow_left₀ (by positivity) e2 2
      rw [div_pow] at s1 s2
      nlinarith
    have e4 : (C0 + C1) ^ 2 / ν ^ 2 + C0 ^ 2 / ν ^ 2 ≤ K / ν ^ 2 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    exact hb.trans (e3.trans e4)
  -- labelled endpoints
  have hp := hNb _ hCset
  have hnabs : (Nb : ℤ) < |n| := NlsGge.ThirdConsultation.KSPS019Support.natAbs_lt_iff.1 hnb
  obtain ⟨hm1, hp1⟩ := NlsGge.ThirdConsultation.KSPS020Support.labels_mem_ball hp hnabs
  have hmball : NlsGge.GK38.lamMinus ψ n ∈ Metric.ball c (Real.pi / 4) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hm1
  have hpball : NlsGge.GK38.lamPlus ψ n ∈ Metric.ball c (Real.pi / 4) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hp1
  have hs : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← zpow_add₀ (by norm_num)]
    rw [← two_mul, zpow_mul]; norm_num
  have hroot : ∀ k : ℤ, NlsGge.GK38.discrim ψ (NlsGge.GK38.lamSeq ψ k) ^ 2 = 4 := by
    intro k
    have := (NlsGge.GK38.lamSeq_enumeration38 ψ).1 k
    rw [NlsGge.GK38.perChar_eq] at this
    exact sub_eq_zero.mp this
  have key : ∀ l : ℂ, l ∈ Metric.ball c (Real.pi / 4) → NlsGge.GK38.discrim ψ l ^ 2 = 4 →
      ‖l - c‖ ≤ (39 * K + 1) / ν := fun l hl hr =>
    NlsGge.ThirdConsultation.KSPS020Support.endpoint_close hs
      (NlsGge.ThirdConsultation.KSPS020Support.cos_int_mul_pi_add n) hK hν1 hKν hh0 hh1 hl hcrball
      hr hcid hcr2
  have kp := key _ hpball (hroot (2 * n + 1))
  have km := key _ hmball (hroot (2 * n))
  exact max_le kp km

end
end NlsGge.ThirdConsultation.KSPS
