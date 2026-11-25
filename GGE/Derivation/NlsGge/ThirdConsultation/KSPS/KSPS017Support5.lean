import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Support9

/- KSPS-017 SUPPORT5 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS017Support5.lean.
   S017-3 (differentiated OFF-DIAGONAL endpoint remainders are square summable on the samples), stated for any
   function g that is holomorphic on lam != 0 and agrees there with the remainder component idx_b
   (the zero-filled KSPS017W.Rfun is such a g by KSPS017Support2; the instantiation is made where both are imported).
   Route: E = g - kappa_b endpointOsc(sigma_b ., c_b) is holomorphic and |E| <= C/|lam| on the strip
   |Im| <= a + 1 (off_approx); the Cauchy estimate on the FIXED radius-1 disc about xi_n gives |E'(xi_n)| <= 2C/|xi_n|;
   the derivative of the principal part is kappa_b sigma_b endpointOsc(sigma_b xi_n, i(1-2t) c_b) (hasDerivAt_endpointOsc),
   square summable along xi by Bessel + KSPS-008 perturbation (osc_sq_seq). Low |n| absorbed by an eventual bound. -/
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS

theorem sqs_add {f g : ℤ → ℝ} (hf : Summable (fun n => f n ^ 2)) (hg : Summable (fun n => g n ^ 2)) :
    Summable (fun n => (f n + g n) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ((hf.mul_left 2).add (hg.mul_left 2))
  nlinarith [sq_nonneg (f n - g n)]

theorem sqs_mul_left {f : ℤ → ℝ} (K : ℝ) (hf : Summable (fun n => f n ^ 2)) :
    Summable (fun n => (K * f n) ^ 2) := by
  simp_rw [mul_pow]
  exact hf.mul_left _

theorem offdiag_deriv_sq_summable {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (a : ℝ) (ha : 0 ≤ a)
    (xi : ℤ → ℂ) (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n)
    (g : ℂ → ℂ) (hgd : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z)
    (hge : ∀ (z : ℂ) (hz : z ≠ 0), g z = KSPSWKB.sourceRemainderVector φ b ⟨z, hz⟩ 1 (if b then 0 else 1)) :
    Summable (fun n : ℤ => ‖deriv g (xi n)‖ ^ 2) := by
  obtain ⟨C, L, hC, hL, happ⟩ := off_approx hN φ b (a + 1) (by linarith)
  set cc : ℝ → ℂ := coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) with hccdef
  set σc : ℂ := if b then (-1 : ℂ) else 1 with hσc
  set κ : ℂ := if b then -Complex.I else Complex.I with hκdef
  have hκ : ‖κ‖ = 1 := by cases b <;> simp [hκdef]
  have hσn : ‖σc‖ = 1 := by cases b <;> simp [hσc]
  set σ : ℤ := if b then -1 else 1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by cases b <;> simp [hσdef]
  have hσσ : ((σ : ℤ) : ℂ) = σc := by cases b <;> simp [hσdef, hσc]
  have hcmem : MemLp cc 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc _
  have hcii : IntervalIntegrable cc volume 0 1 := KSPSWKB.intervalIntegrable_of_memLp hcmem
  set H' : ℝ → ℂ := fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * cc t with hH'def
  have hH'mem : MemLp H' 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.h150_memLp_mul_bdd cc (fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ))
      hcmem (Continuous.continuousOn (by fun_prop))
  have hOd : ∀ z : ℂ, HasDerivAt (fun w : ℂ => κ * KSPSWKB.endpointOsc (σc * w) cc)
      (κ * (σc * KSPSWKB.endpointOsc (σc * z) H')) z := by
    intro z
    have h1 := (hasDerivAt_endpointOsc hcii (σc * z)).comp z ((hasDerivAt_id z).const_mul σc)
    refine (h1.const_mul κ).congr_deriv ?_
    simp only [hH'def]
    ring
  -- the dominating sequence
  have S1 : Summable (fun n : ℤ => (1 / |(n : ℝ)|) ^ 2) := by
    have h := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    refine h.congr (fun n => ?_)
    rw [div_pow, one_pow, sq_abs]
  have S2 : Summable (fun n : ℤ => ‖KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖ ^ 2) :=
    KSPSWKB.osc_sq_seq hH'mem a ha xi hxi σ hσ
  have Stot : Summable (fun n : ℤ => (2 * C * (1 / |(n : ℝ)|) + ‖KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖) ^ 2) :=
    sqs_add (sqs_mul_left (2 * C) S1) S2
  set n0 : ℕ := ⌈a + L + 2⌉₊ with hn0
  refine Summable.of_norm_bounded_eventually Stot ?_
  filter_upwards [KSPSWKB.eventually_cofinite_natAbs n0] with n hn
  -- tail facts
  have hn0' : a + L + 2 ≤ (n0 : ℝ) := Nat.le_ceil _
  have hnabs : a + L + 2 ≤ |(n : ℝ)| := by
    have h1 : ((n0 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 hn
    rw [Int.cast_abs] at h1
    simp only [Int.cast_natCast] at h1
    linarith
  obtain ⟨hlow, himxi⟩ := KSPSWKB.norm_xi_lower a xi hxi n
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hm0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  have hξ : |(n : ℝ)| + L + 2 ≤ ‖xi n‖ := by
    have : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hπ hm0
    linarith
  have hξ2 : 2 ≤ ‖xi n‖ := by linarith
  have hn1 : 0 < |(n : ℝ)| := by linarith
  have hz : xi n ≠ 0 := by intro h; rw [h, norm_zero] at hξ2; norm_num at hξ2
  -- the remainder E
  set E : ℂ → ℂ := fun w => g w - κ * KSPSWKB.endpointOsc (σc * w) cc with hEdef
  have hEd : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ E z := fun z hz0 =>
    (hgd z hz0).sub (hOd z).differentiableAt
  have hball : ∀ z ∈ Metric.closedBall (xi n) 1, ‖xi n‖ - 1 ≤ ‖z‖ ∧ |z.im| ≤ a + 1 := by
    intro z hzb
    rw [Metric.mem_closedBall, dist_eq_norm] at hzb
    have h1 := norm_sub_norm_le (xi n) z
    have h4 : ‖xi n - z‖ ≤ 1 := by rw [norm_sub_rev]; exact hzb
    have h2 : |z.im - (xi n).im| ≤ ‖z - xi n‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h3 := abs_sub_abs_le_abs_sub z.im (xi n).im
    constructor <;> linarith
  have hEdb : ∀ z ∈ Metric.closedBall (xi n) 1, DifferentiableAt ℂ E z := by
    intro z hzb
    have h := (hball z hzb).1
    have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h; linarith
    exact hEd z hz0
  have hEs : ∀ z ∈ Metric.sphere (xi n) 1, ‖E z‖ ≤ 2 * C / ‖xi n‖ := by
    intro z hzs
    have hzb : z ∈ Metric.closedBall (xi n) 1 := Metric.sphere_subset_closedBall hzs
    obtain ⟨h1, h2⟩ := hball z hzb
    have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; linarith
    have hzL : L ≤ ‖z‖ := by linarith
    have hb := happ ⟨z, hz0⟩ hzL h2
    have hEz : E z = KSPSWKB.sourceRemainderVector φ b ⟨z, hz0⟩ 1 (if b then 0 else 1) -
        κ * KSPSWKB.endpointOsc (σc * z) cc := by
      simp only [hEdef, hge z hz0]
    rw [hEz]
    refine hb.trans ?_
    have hzpos : 0 < ‖z‖ := by linarith
    have hhalf : ‖xi n‖ / 2 ≤ ‖z‖ := by linarith
    rw [div_le_div_iff₀ hzpos (by linarith)]
    nlinarith
  have hcauchy := norm_deriv_le_of_sphere one_pos hEdb hEs
  rw [div_one] at hcauchy
  -- deriv g = deriv E + principal derivative
  have hgE : deriv g (xi n) = deriv E (xi n) + κ * (σc * KSPSWKB.endpointOsc (σc * xi n) H') := by
    have h1 : HasDerivAt E (deriv g (xi n) - κ * (σc * KSPSWKB.endpointOsc (σc * xi n) H')) (xi n) :=
      (hgd (xi n) hz).hasDerivAt.sub (hOd (xi n))
    rw [h1.deriv]; ring
  have hprin : ‖κ * (σc * KSPSWKB.endpointOsc (σc * xi n) H')‖ =
      ‖KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖ := by
    rw [norm_mul, norm_mul, hκ, hσn, one_mul, one_mul, hσσ]
  have hξn : 2 * C / ‖xi n‖ ≤ 2 * C * (1 / |(n : ℝ)|) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) hn1 (by linarith)
  have hbound : ‖deriv g (xi n)‖ ≤ 2 * C * (1 / |(n : ℝ)|) + ‖KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖ := by
    rw [hgE]
    refine (norm_add_le _ _).trans ?_
    rw [hprin]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hbound 2

end
end NlsGge.ThirdConsultation.KSPS017W
