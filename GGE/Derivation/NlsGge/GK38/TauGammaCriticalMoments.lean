import NlsGge.GK38.TauGammaCircleMoments

/-! The critical singleton is used only after circle integrability. -/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem isolating_critical_singleton38 {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    Lib.zeroMultiset (deriv (discrim φ)) (ball (C n) (R n)) = {lamDot φ n} := by
  obtain ⟨c, N, _, hs⟩ := hf
  exact ((hs.1 n).2.2.2.2.2.2.2.1).symm

theorem isolating_critical_boundary38 {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    ∀ z ∈ sphere (C n) (R n), deriv (discrim φ) z ≠ 0 := by
  obtain ⟨c, N, _, hs⟩ := hf
  intro z hz
  exact ((hs.1 n).2.2.2.2.2.2.2.2.2.2.2.2 z hz).2.2.2

theorem critical_moment_circleIntegrable38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (fun z => z * deriv (deriv (discrim φ)) z / deriv (discrim φ) z)
      (C n) (R n) := by
  simp_rw [mul_div_assoc]
  change CircleIntegrable (fun z => z * logDeriv (deriv (discrim φ)) z) (C n) (R n)
  apply ContinuousOn.circleIntegrable (isolating_radius_pos38 hf n).le
  refine continuousOn_id.mul ?_
  intro z hz
  exact (Lib.continuousAt_logDeriv' (analyticOnNhd_discrimDeriv38 φ z (mem_univ z))
    (isolating_critical_boundary38 hf n z hz)).continuousWithinAt

theorem critical_fixedMoment38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral (fun z => z * deriv (deriv (discrim φ)) z / deriv (discrim φ) z)
        (C n) (R n) = lamDot φ n := by
  have hint := critical_moment_circleIntegrable38 φ C R hf n
  have he : (fun z => z * deriv (deriv (discrim φ)) z / deriv (discrim φ) z) =
      (fun z => z * logDeriv (deriv (discrim φ)) z) := by
    funext z
    simp only [logDeriv_apply, mul_div_assoc]
  rw [he, Lib.circleIntegral_mul_logDeriv (g := fun z : ℂ => z) (isolating_radius_pos38 hf n)
    ((analyticOnNhd_discrimDeriv38 φ).mono (subset_univ _))
    (isolating_critical_boundary38 hf n) differentiable_id.diffContOnCl,
    isolating_critical_singleton38 hf n]
  simp only [Multiset.map_singleton, Multiset.sum_singleton]
  have hp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

end
end NlsGge.GK38
