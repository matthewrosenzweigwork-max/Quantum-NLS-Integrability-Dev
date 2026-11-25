import Mathlib
import NlsGge.Atomic.KSPS.KSPS018
import NlsGge.ThirdConsultation.KSPS.KSPS019Host
import NlsGge.ThirdConsultation.KSPS.KSPS019Support

/- KSPS-019 PRODUCTION01 (proof development, AUTHOR; not reviewed; target NlsGge/Atomic/KSPS/KSPS019.lean).
   Head: STATEMENTS/KSPS.md "KSPS-019 -- rough Dirichlet and critical root localization" (identical text in followup1..10; no
   Pro round 4-12 response entry touches KSPS-019), VERBATIM. The constant C and the index N are chosen after B and before
   phi, n, as printed (the numerator depends on B; no universal numerator 1 is asserted).
   Proof (source Lemma 6.2): uniform quarter-disc localisation of mu_n and lambda_dot_n for |n| > N(B) from the local L2 counting
   lemmas and the compactness of the H1 ball in L2 (G1-049 route, KSPS019Support Part B), then the fixed-strip bounds of KSPS-018
   (j = 0 for chi_D = sin + O(1/lam), j = 1 for Delta' = -2 sin + O(1/lam)) and |w| <= 5 |sin w| on |w| < pi/4. -/
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem rough_boundary_roots :
  ∀ B : ℝ, 0 < B →
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
    ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
      ∀ n : ℤ, N ≤ n.natAbs →
        ‖mu φ n-(n:ℂ)*Real.pi‖ +
        ‖criticalEigenvalue φ n-(n:ℂ)*Real.pi‖ ≤
          C/(n.natAbs:ℝ) := by
  intro B hB
  have hB0 : 0 ≤ B := hB.le
  obtain ⟨N0, hN0, hloc⟩ := NlsGge.ThirdConsultation.KSPS019Support.unif_localization hB0
  obtain ⟨C0, L0, hC0, hL0, h0⟩ := spectral_derivative_rough_complete 0 B 1 hB0 zero_le_one
  obtain ⟨C1, L1, hC1, hL1, h1⟩ := spectral_derivative_rough_complete 1 B 1 hB0 zero_le_one
  refine ⟨5 * C0 + 5 * C1, N0 + 1 + ⌈L0⌉₊ + ⌈L1⌉₊, by linarith, ?_⟩
  intro φ hφ n hn
  have hCset := NlsGge.ThirdConsultation.KSPS019Support.toPotPair_mem_Cset φ hφ
  have hn0 : N0 < n.natAbs := by omega
  have hn1 : 1 ≤ n.natAbs := by omega
  obtain ⟨hmu_ball, hmu_root, hcr_ball, hcr_root⟩ := hloc (toPotPair φ) hCset n hn0
  -- norms of the roots and their strip position
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi' : 3.14 < Real.pi := Real.pi_gt_d2
  have hm : ‖(n : ℂ)‖ = (n.natAbs : ℝ) := by
    rw [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  have hnn : (1 : ℝ) ≤ n.natAbs := by exact_mod_cast hn1
  have hnz : ‖(n : ℂ) * (Real.pi : ℂ)‖ = (n.natAbs : ℝ) * Real.pi := by
    rw [norm_mul, hm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hbig0 : L0 ≤ (n.natAbs : ℝ) := by
    have h := Nat.le_ceil L0
    have : ((⌈L0⌉₊ : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast (by omega : ⌈L0⌉₊ ≤ n.natAbs)
    linarith
  have hbig1 : L1 ≤ (n.natAbs : ℝ) := by
    have h := Nat.le_ceil L1
    have : ((⌈L1⌉₊ : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast (by omega : ⌈L1⌉₊ ≤ n.natAbs)
    linarith
  have hlow : ∀ z : ℂ, ‖z - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 →
      (n.natAbs : ℝ) ≤ ‖z‖ ∧ |z.im| ≤ 1 := by
    intro z hz
    constructor
    · have h1' := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) z
      rw [norm_sub_rev, hnz] at h1'
      have hmpi : 3.14 * (n.natAbs : ℝ) ≤ (n.natAbs : ℝ) * Real.pi := by nlinarith
      linarith
    · have him : z.im = (z - (n : ℂ) * (Real.pi : ℂ)).im := by simp
      rw [him]
      calc |(z - (n : ℂ) * (Real.pi : ℂ)).im| ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖ :=
            Complex.abs_im_le_norm _
        _ ≤ 1 := by linarith
  have hmpos : (0 : ℝ) < n.natAbs := lt_of_lt_of_le one_pos hnn
  -- Dirichlet root
  have hmuK : ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 5 * ((2 * C0) / (2 * (n.natAbs : ℝ))) := by
    obtain ⟨hz1, hz2⟩ := hlow (mu φ n) hmu_ball
    have hs := NlsGge.ThirdConsultation.KSPS019Support.sin_le_of_dirichlet_root φ (mu φ n) hmu_root
    obtain ⟨-, hD, hsup⟩ := h0 φ hφ (mu φ n) (hbig0.trans hz1) hz2
    have hD1 := hD 1 ⟨zero_le_one, le_rfl⟩
    rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, iteratedDeriv_zero, iteratedDeriv_zero] at hD1
    have hsin : ‖Complex.sin (mu φ n)‖ ≤ (2 * C0) / ‖mu φ n‖ := by
      calc _ ≤ 2 * ‖NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ 1 (mu φ n) -
              freePropagator 1 (mu φ n)‖ := hs
        _ ≤ 2 * (C0 / ‖mu φ n‖) := by
          gcongr
          exact hD1.trans hsup
        _ = _ := by ring
    exact NlsGge.ThirdConsultation.KSPS019Support.close_of_sin hmu_ball hn1 (by positivity) hsin
  -- critical root
  have hcrK : ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 5 * (C1 / (2 * (n.natAbs : ℝ))) := by
    obtain ⟨hz1, hz2⟩ := hlow (criticalEigenvalue φ n) hcr_ball
    have hs := NlsGge.ThirdConsultation.KSPS019Support.sin_le_of_critical_root φ
      (criticalEigenvalue φ n) hcr_root
    obtain ⟨-, hD, hsup⟩ := h1 φ hφ (criticalEigenvalue φ n) (hbig1.trans hz1) hz2
    have hD1 := hD 1 ⟨zero_le_one, le_rfl⟩
    rw [show ((1 : Fin 3) : ℕ) = 1 from rfl, iteratedDeriv_one, iteratedDeriv_one] at hD1
    have hsin : ‖Complex.sin (criticalEigenvalue φ n)‖ ≤ C1 / ‖criticalEigenvalue φ n‖ :=
      hs.trans (hD1.trans hsup)
    exact NlsGge.ThirdConsultation.KSPS019Support.close_of_sin hcr_ball hn1 hC1 hsin
  have e1 : 5 * ((2 * C0) / (2 * (n.natAbs : ℝ))) = 5 * C0 / (n.natAbs : ℝ) := by
    field_simp
  have e2 : 5 * (C1 / (2 * (n.natAbs : ℝ))) = (5 * C1 / (n.natAbs : ℝ)) / 2 := by
    field_simp
  have e3 : 0 ≤ 5 * C1 / (n.natAbs : ℝ) := by positivity
  have e4 : (5 * C0 + 5 * C1) / (n.natAbs : ℝ) = 5 * C0 / (n.natAbs : ℝ) + 5 * C1 / (n.natAbs : ℝ) :=
    add_div _ _ _
  rw [e4]
  linarith

end
end NlsGge.ThirdConsultation.KSPS
