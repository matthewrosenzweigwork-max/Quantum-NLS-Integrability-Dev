import NlsGge.GK38.EigenvalueCompactnessPhaseIntegrable
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import NlsGge.Spectral.ComplexAbsolutelyContinuousAEODEIntegralIdentityV1

/-! # S7: absolutely continuous scalar integrating factor

Integrability and actual AE derivative hypotheses precede all primitive identities.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem ac_complex_exp38 {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => Complex.exp (f t)) a b := by
  obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn hf.continuousOn
  have he : ContDiffOn ℝ 1 Complex.exp (closedBall (0 : ℂ) R) :=
    ((Complex.contDiff_exp : ContDiff ℂ 1 Complex.exp).restrict_scalars ℝ).contDiffOn
  obtain ⟨K, hK⟩ := he.exists_lipschitzOnWith (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  exact hK.comp_absolutelyContinuousOnInterval
    (fun t ht => by simpa only [mem_closedBall, dist_zero_right] using hR t ht) hf

theorem ac_scalar_integrating_factor38 (F q : ℝ → ℂ)
    (hF : AbsolutelyContinuousOnInterval F 0 2) (hq : IntervalIntegrable q volume 0 2)
    (hder : ∀ᵐ t ∂volume, t ∈ uIcc (0 : ℝ) 2 → HasDerivAt F (q t * F t) t) :
    ∀ t ∈ uIcc (0 : ℝ) 2, F t = F 0 * Complex.exp (∫ r in (0 : ℝ)..t, q r) := by
  let P : ℝ → ℂ := fun t => ∫ r in (0 : ℝ)..t, q r
  let G : ℝ → ℂ := fun t => Complex.exp (-P t) * F t
  have hP : AbsolutelyContinuousOnInterval P 0 2 := complex_intervalIntegral_primitive_absolutelyContinuousV2 hq
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc (0 : ℝ) 2)
  have hG : AbsolutelyContinuousOnInterval G 0 2 := by
    simpa only [G, smul_eq_mul, Pi.mul_apply, Pi.neg_apply] using! (ac_complex_exp38 hP.neg).smul hF
  have hz : ∀ᵐ t ∂volume, t ∈ uIcc (0 : ℝ) 2 → HasDerivAt G 0 t := by
    filter_upwards [hder, hq.ae_hasDerivAt_integral] with t ht hp
    intro hmem
    have hpd : HasDerivAt P (q t) t := hp hmem 0 left_mem_uIcc
    have hd := hpd.neg.cexp.mul (ht hmem)
    convert hd using 1
    dsimp [G]
    ring
  obtain ⟨C, hC⟩ := hG.const_of_ae_hasDerivAt_zero hz
  have hC0 : C = F 0 := by
    simpa only [G, P, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, one_mul] using
      (hC 0 left_mem_uIcc).symm
  intro t ht
  have he : Complex.exp (-P t) * F t = F 0 := (hC t ht).trans hC0
  calc
    F t = Complex.exp (P t) * (Complex.exp (-P t) * F t) := by
      rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = Complex.exp (P t) * F 0 := congrArg (fun w : ℂ => Complex.exp (P t) * w) he
    _ = F 0 * Complex.exp (P t) := mul_comm _ _

theorem complex_exp_normalized38 (z : ℂ) :
    Complex.exp z / (‖Complex.exp z‖ : ℂ) = Complex.exp (Complex.I * (z.im : ℂ)) := by
  rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

end
end NlsGge.GK38
