import Mathlib
import NlsGge.Atomic.G5.G5001
import NlsGge.Atomic.G5.G5004Host
import NlsGge.Atomic.G5.G5004Support1
import NlsGge.GK38.XiSqChiMajorant
import NlsGge.GK38.XiSqActualC3
import NlsGge.GK38.DirichletL2
import NlsGge.GK38.Lib.EntireProductsC34h

/- G5-004 SUPPORT2 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/Atomic/G5/G5004Support2.lean.  Pro round 10 section 7 (commit 178f84d6):
   radiusOmittedNormalized_analytic and radiusOmittedNormalized_local_l2 (statements byte-identical).
   Route: a_n = A_n/pi_n = omitProd_n(tau shift, mu_n) * Q_n on the tail; (omitProd - sinc) via Lib.omitProd_asymp,
   Q-1 via a5QCorrectionProduct_linear_bound38 with a5GammaConvolution bounds, sinc(mu_n)-(-1)^n by the local
   sin(w)-w <= w^2 estimate; finitely many remaining labels by analytic continuity. Template: XiSqChiMajorant. -/
set_option autoImplicit false

open Set Filter Topology Metric SummationFilter
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem radiusOmittedNormalized_analytic (n : ℤ) :
  AnalyticOnNhd ℂ (radiusOmittedNormalized n) sourceBetaW := by
  intro φ hφ
  have hJ : AnalyticAt ℂ (fun ψ : PotPair => (ψ, muSeq ψ n)) φ :=
    analyticAt_id.prod (analyticOnNhd_muSeq_complex38 n φ (g5001_gk φ hφ))
  have hA : AnalyticAt ℂ (fun ψ : PotPair => a5OmittedRootProduct38 n (ψ, muSeq ψ n)) φ :=
    AnalyticAt.comp (g := a5OmittedRootProduct38 n) (f := fun ψ : PotPair => (ψ, muSeq ψ n))
      (a5OmittedRoot_analytic38 n (φ, muSeq φ n) (g5001_dom φ hφ n)) hJ
  exact hA.div_const

theorem g5004_sin_sub_le (w : ℂ) (hw : ‖w‖ ≤ 1) : ‖Complex.sin w - w‖ ≤ ‖w‖ ^ 2 := by
  have h1 := Complex.norm_exp_sub_one_sub_id_le (x := w * Complex.I) (by simpa using hw)
  have h2 := Complex.norm_exp_sub_one_sub_id_le (x := -w * Complex.I) (by simpa using hw)
  have e : Complex.sin w - w =
      ((Complex.exp (-w * Complex.I) - 1 - (-w * Complex.I)) -
        (Complex.exp (w * Complex.I) - 1 - w * Complex.I)) * Complex.I / 2 := by
    rw [Complex.sin]
    linear_combination (-w) * Complex.I_sq
  rw [e, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h1' : ‖Complex.exp (w * Complex.I) - 1 - w * Complex.I‖ ≤ ‖w‖ ^ 2 := by
    simpa [norm_mul, Complex.norm_I] using h1
  have h2' : ‖Complex.exp (-w * Complex.I) - 1 - (-w * Complex.I)‖ ≤ ‖w‖ ^ 2 := by
    simpa [norm_mul, norm_neg, Complex.norm_I] using h2
  have h3 := norm_sub_le (Complex.exp (-w * Complex.I) - 1 - (-w * Complex.I))
    (Complex.exp (w * Complex.I) - 1 - w * Complex.I)
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4]
  linarith

theorem g5004_sincAt_sub_sign (n : ℤ) {lam : ℂ} (hlam : lam ∈ Lib.Dn n) :
    ‖Lib.sincAt n lam - (-1 : ℂ) ^ n‖ ≤ ‖lam - (n : ℂ) * (Real.pi : ℂ)‖ := by
  have hpi := Real.pi_pos
  have hD : ‖lam - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
    simpa [Lib.Dn, Metric.mem_ball, dist_eq_norm] using hlam
  have hpi4 : Real.pi / 4 < 1 := by linarith [Real.pi_lt_four]
  have hcos : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ n := by
    have h := Real.cos_int_mul_pi n
    have h' : ((Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) = (((-1 : ℝ) ^ n : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) h
    rw [Complex.ofReal_cos] at h'
    simpa using h'
  have hnorm : ‖(-1 : ℂ) ^ n‖ = 1 := by simp
  unfold Lib.sincAt
  by_cases h : lam = (n : ℂ) * (Real.pi : ℂ)
  · simp only [h, ite_true, sub_self, norm_zero]
    have hc : ((Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) = (-1 : ℂ) ^ n := by
      rw [Complex.ofReal_cos]
      simpa using hcos
    rw [hc, sub_self, norm_zero]
  · simp only [h, ite_false]
    set w : ℂ := lam - (n : ℂ) * (Real.pi : ℂ) with hw
    have hw0 : w ≠ 0 := sub_ne_zero.mpr h
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hs : Complex.sin lam = Complex.sin w * Complex.cos ((n : ℂ) * (Real.pi : ℂ)) := by
      have h0 := Complex.sin_add w ((n : ℂ) * (Real.pi : ℂ))
      simpa only [hw, sub_add_cancel, Complex.sin_int_mul_pi, mul_zero, add_zero] using h0
    have hdiff : Complex.sin lam / w - (-1 : ℂ) ^ n =
        (-1 : ℂ) ^ n * ((Complex.sin w - w) / w) := by
      rw [hs, hcos]
      field_simp
    rw [hdiff, norm_mul, hnorm, one_mul, norm_div]
    have hb := g5004_sin_sub_le w (by linarith)
    rw [div_le_iff₀ hwn]
    nlinarith

end
end NlsGge.GKDefinitionDesign
