import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Host
import NlsGge.ThirdConsultation.KSPS.KSPS011Support14

/- KSPS-011 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/KSPS/KSPS011.lean.
   Head: Pro round 13 section 4 (KSPS-011), theorem `WKB_endpoint_offdiagonal`, VERBATIM.
   Proof: eLower/eUpper are indexWeight n * (endpoint - leading term) for ALL n (Pro item 6), so the identity is algebra
   and the content is SquareSummable, supplied by KSPS011Support14.endpoint_remainder_square_summable (b = false / true);
   the zero samples and low frequencies are absorbed there by an eventual bound. The upper sequence is
   (-1)^N times the master sequence, which has the same norms. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem WKB_endpoint_offdiagonal
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (xi : ℤ → ℂ)
    (hxi : ∃ a : ℝ, 0 ≤ a ∧ ∀ n,
      ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) :
  ∃ eLower eUpper : ℤ → ℂ,
    SquareSummable eLower ∧ SquareSummable eUpper ∧
    ∀ n : ℤ,
      NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
        Complex.I * ((-1 : ℂ) ^ (n + 1)) *
          NlsGge.Pilot.physicalFourier
            (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
          eLower n / indexValue n ∧
      NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
        Complex.I * ((-1 : ℂ) ^ n) *
          NlsGge.Pilot.physicalFourier
            (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
          eUpper n / indexValue n := by
  obtain ⟨a, ha, hxi'⟩ := hxi
  have hL := NlsGge.ThirdConsultation.KSPSWKB.endpoint_remainder_square_summable hN φ false a ha xi hxi'
  have hU := NlsGge.ThirdConsultation.KSPSWKB.endpoint_remainder_square_summable hN φ true a ha xi hxi'
  have hw : ∀ n : ℤ, (indexWeight n : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (indexWeight_pos n).ne'
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  obtain ⟨eL, hLs, hLe⟩ : ∃ e : ℤ → ℂ, SquareSummable e ∧ ∀ n : ℤ, e n = (indexWeight n : ℂ) *
      (NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n -
        Complex.I * (-1 : ℂ) ^ n * (-1 : ℂ) *
          NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.2) n) :=
    ⟨_, hL, fun n => by simp [NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower]⟩
  obtain ⟨eU, hUs, hUe⟩ : ∃ e : ℤ → ℂ, SquareSummable e ∧ ∀ n : ℤ, e n = (indexWeight n : ℂ) *
      ((if hz : xi n = 0 then 0 else
          NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ true ⟨xi n, hz⟩ 1 0) -
        (-Complex.I) * (-1 : ℂ) ^ n * (-1 : ℂ) ^ (N + 1) *
          NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.1) (-n)) :=
    ⟨_, hU, fun n => by simp⟩
  refine ⟨eL, fun n => (-1 : ℂ) ^ N * eU n, hLs, ?_, fun n => ⟨?_, ?_⟩⟩
  · unfold SquareSummable at *
    refine hUs.congr (fun n => ?_)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  · rw [hLe n, zpow_add_one₀ hm1]
    unfold indexValue
    field_simp [hw n]
    ring
  · have hpow : (-1 : ℂ) ^ N * (-1 : ℂ) ^ (N + 1) = -1 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]; simp
    unfold NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper indexValue
    beta_reduce
    rw [hUe n]
    have hcancel : ∀ y z : ℂ, y * ((indexWeight n : ℂ) * z) / (indexWeight n : ℂ) = y * z :=
      fun y z => by field_simp [hw n]
    rw [hcancel]
    by_cases hz : xi n = 0
    · simp only [dif_pos hz]
      linear_combination (-(Complex.I * (-1 : ℂ) ^ n *
        NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.1) (-n))) * hpow
    · simp only [dif_neg hz]
      linear_combination (-(Complex.I * (-1 : ℂ) ^ n *
        NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.1) (-n))) * hpow

end
end NlsGge.ThirdConsultation.KSPS
