import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.Lib.CircleArgument

/-! Integrability precedes the weighted argument principle; repeated roots remain two entries. -/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem isolating_radius_pos38 {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) (n : ℤ) : 0 < R n := by
  obtain ⟨c, N, hg, _⟩ := hf
  exact (hg.1 n).1

theorem isolating_periodic_pair38 {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    Lib.zeroMultiset (perChar φ) (ball (C n) (R n)) =
      lamMinus φ n ::ₘ lamPlus φ n ::ₘ 0 := by
  obtain ⟨c, N, _, hs⟩ := hf
  exact ((hs.1 n).2.2.2.2.1).symm

theorem isolating_periodic_boundary38 {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    ∀ z ∈ sphere (C n) (R n), perChar φ z ≠ 0 := by
  obtain ⟨c, N, _, hs⟩ := hf
  intro z hz
  exact ((hs.1 n).2.2.2.2.2.2.2.2.2.2.2.2 z hz).1

theorem momentIntegrand_eq_logDeriv38 (φ : PotPair) (k : ℕ) :
    momentIntegrand38 φ k = fun z => z ^ k * logDeriv (perChar φ) z := by
  funext z
  simp only [momentIntegrand38, logDeriv_apply, mul_div_assoc]

theorem moment_circleIntegrable38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (n : ℤ) (k : ℕ) :
    CircleIntegrable (momentIntegrand38 φ k) (C n) (R n) := by
  rw [momentIntegrand_eq_logDeriv38]
  apply ContinuousOn.circleIntegrable (isolating_radius_pos38 hf n).le
  refine (continuousOn_id.pow k).mul ?_
  intro z hz
  exact (Lib.continuousAt_logDeriv' (analyticOnNhd_perChar_z φ z (mem_univ z))
    (isolating_periodic_boundary38 hf n z hz)).continuousWithinAt

theorem moment_circleIntegral38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (n : ℤ) (k : ℕ) :
    circleIntegral (momentIntegrand38 φ k) (C n) (R n) =
      (2 * (Real.pi : ℂ) * Complex.I) * ((lamMinus φ n) ^ k + (lamPlus φ n) ^ k) := by
  have hint := moment_circleIntegrable38 φ C R hf n k
  rw [momentIntegrand_eq_logDeriv38]
  have hg : DiffContOnCl ℂ (fun z : ℂ => z ^ k) (ball (C n) (R n)) :=
    (differentiable_id.pow k).diffContOnCl
  rw [Lib.circleIntegral_mul_logDeriv (g := fun z : ℂ => z ^ k) (isolating_radius_pos38 hf n)
    ((analyticOnNhd_perChar_z φ).mono (subset_univ _))
    (isolating_periodic_boundary38 hf n) hg]
  rw [isolating_periodic_pair38 hf n]
  simp

theorem fixedMoment_pair38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (n : ℤ) (k : ℕ) :
    fixedMoment38 φ C R n k = (lamMinus φ n) ^ k + (lamPlus φ n) ^ k := by
  rw [fixedMoment38, moment_circleIntegral38 φ C R hf n k]
  have hp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

end
end NlsGge.GK38
