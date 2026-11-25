import Mathlib
import QuantumNLS.RiccatiSobolevBanach
import QuantumNLS.RiccatiPicardBall
import QuantumNLS.Ext025A5Triangular

/-!
# R-3FEAD88B blocker 3, stage E3b: analytic dependence of the small Riccati solution on (u, v)

Residual `G(p, r) = r − T(u,v; r)` on `(Ell2 × Ell2) × Ell2`, with `T` from stage E3a.
At a base point `p0 = (u0, v0)` with `‖u0‖, ‖v0‖ < β`, the small fixed point `r0` of E3a has
`∂_r G = I + N` with `N = κ R_z ∘ (v0 · (r0 · + · r0))`, and `‖N‖ ≤ 1/4` (since `‖r0‖ ≤ 2β/η`
and the E3a condition `16 |κ| C² β² ≤ η²`). So `I + N` is a continuous linear equivalence
(Neumann series, `Units.oneSub`). The GP-03 constituent `Ext025A5.analytic_implicit` then gives an
analytic branch `ψ` near `p0` with `G(p, ψ p) = 0`. By the E3a uniqueness in the ball of radius
`4β/η`, `ψ p` is the unique small solution for `p` near `p0`.

Main result, `riccati_local_analytic_branch`: for every `p0` in the open parameter set
`{‖u‖ < β, ‖v‖ < β}`, there is `ψ` analytic at `p0` such that eventually in `p`, `ψ p` is a fixed point
of `T(p,·)` and the unique fixed point of norm at most `4β/η`.

Standard axioms only (the GP-03 dependency `Ext025A5.analytic_implicit` uses no extra axioms).
No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric

namespace QuantumNLS.RiccatiPicardAnalytic

open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPicardBall

/-- Parameter space `p = (u, v)`. -/
abbrev Par : Type := Ell2 × Ell2

/-- Residual `G(p, r) = r − T(u,v; r)`, on the domain `(Par) × Ell2`. -/
def residG {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    (w : Par × Ell2) : Ell2 :=
  w.2 - riccatiT hL ha hz κ w.1.1 w.1.2 w.2

/-- Analyticity of the residual at every point (polynomial in `r`, bounded bilinear products). -/
theorem residG_analyticAt {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ : ℝ) (x0 : Par × Ell2) : AnalyticAt ℂ (residG hL ha hz κ) x0 := by
  have hA_r : AnalyticAt ℂ (fun w : Par × Ell2 => w.2) x0 := analyticAt_snd
  have hA_u : AnalyticAt ℂ (fun w : Par × Ell2 => ropCLM L z hz w.1.1) x0 :=
    AnalyticAt.comp ((ropCLM L z hz).analyticAt (x0.1.1)) (analyticAt_fst.comp analyticAt_fst)
  have hs : AnalyticAt ℂ (fun w : Par × Ell2 => mulBil hL ha w.2 w.2) x0 :=
    AnalyticAt.comp (f := fun w : Par × Ell2 => (w.2, w.2))
      (ContinuousLinearMap.analyticAt_bilinear (mulBil hL ha) (x0.2, x0.2))
      (analyticAt_snd.prod analyticAt_snd)
  have ht : AnalyticAt ℂ (fun w : Par × Ell2 => mulBil hL ha w.1.2 (mulBil hL ha w.2 w.2)) x0 :=
    AnalyticAt.comp (f := fun w : Par × Ell2 => (w.1.2, mulBil hL ha w.2 w.2))
      (ContinuousLinearMap.analyticAt_bilinear (mulBil hL ha) (x0.1.2, mulBil hL ha x0.2 x0.2))
      ((analyticAt_snd.comp analyticAt_fst).prod hs)
  have hR : AnalyticAt ℂ
      (fun w : Par × Ell2 => ((κ : ℂ) • ropCLM L z hz) (mulBil hL ha w.1.2 (mulBil hL ha w.2 w.2))) x0 :=
    AnalyticAt.comp (((κ : ℂ) • ropCLM L z hz).analyticAt _) ht
  show AnalyticAt ℂ (fun w : Par × Ell2 => w.2 - riccatiT hL ha hz κ w.1.1 w.1.2 w.2) x0
  exact hA_r.sub (hA_u.sub hR)

/-- The derivative in the direction of `r` at `r0`: `dR h = r0·h + h·r0`. -/
def dR {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (r0 : Ell2) : Ell2 →L[ℂ] Ell2 :=
  (mulBil hL ha r0).comp (ContinuousLinearMap.id ℂ Ell2) + (mulBil hL ha).flip r0

/-- The operator `N = κ R_z ∘ (v0 · dR r0)`, the `r`-derivative correction. -/
def Nop {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    (v0 r0 : Ell2) : Ell2 →L[ℂ] Ell2 :=
  ((κ : ℂ) • ropCLM L z hz).comp ((mulBil hL ha v0).comp (dR hL ha r0))

/-- Slice derivative: `r ↦ residG (p0, r)` has derivative `I + N` at `r0`. -/
theorem slice_deriv {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    (p0 : Par) (r0 : Ell2) :
    HasFDerivAt (fun r : Ell2 => residG hL ha hz κ (p0, r))
      (ContinuousLinearMap.id ℂ Ell2 + Nop hL ha hz κ p0.2 r0) r0 := by
  have hsq1 : HasFDerivAt (fun r : Ell2 => mulBil hL ha r r) (dR hL ha r0) r0 :=
    (mulBil hL ha).hasFDerivAt.clm_apply (hasFDerivAt_id r0)
  have hsq2 : HasFDerivAt (fun r : Ell2 => mulBil hL ha p0.2 (mulBil hL ha r r))
      ((mulBil hL ha p0.2).comp (dR hL ha r0)) r0 :=
    (mulBil hL ha p0.2).hasFDerivAt.comp r0 hsq1
  have hsq3 : HasFDerivAt
      (fun r : Ell2 => ((κ : ℂ) • ropCLM L z hz) (mulBil hL ha p0.2 (mulBil hL ha r r)))
      (((κ : ℂ) • ropCLM L z hz).comp ((mulBil hL ha p0.2).comp (dR hL ha r0))) r0 :=
    ((κ : ℂ) • ropCLM L z hz).hasFDerivAt.comp r0 hsq2
  have hfun := ((hasFDerivAt_id r0).sub_const (ropCLM L z hz p0.1)).add hsq3
  have hfeq : (fun r : Ell2 => residG hL ha hz κ (p0, r))
      = fun r : Ell2 => (id r - ropCLM L z hz p0.1)
          + ((κ : ℂ) • ropCLM L z hz) (mulBil hL ha p0.2 (mulBil hL ha r r)) := by
    funext r
    simp only [residG, riccatiT, id, ContinuousLinearMap.smul_apply]
    abel
  rw [hfeq]
  exact hfun

/-- Operator bound: `‖N h‖ ≤ |κ| η⁻¹ C² β (2‖r0‖) ‖h‖` for `‖v0‖ ≤ β`. -/
theorem norm_Nop_apply_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ β : ℝ) (v0 r0 h : Ell2) (hv : ‖v0‖ ≤ β) :
    ‖Nop hL ha hz κ v0 r0 h‖ ≤ (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (2 * ‖r0‖)) * ‖h‖ := by
  have hC0 : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β := (norm_nonneg v0).trans hv
  have hk0 : 0 ≤ |κ| := abs_nonneg κ
  have hw : ‖mulBil hL ha r0 h + mulBil hL ha h r0‖
      ≤ Cmul L a * ‖r0‖ * ‖h‖ + Cmul L a * ‖h‖ * ‖r0‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_mulBil_le hL ha _ _) (norm_mulBil_le hL ha _ _))
  have hv' : ‖mulBil hL ha v0 (mulBil hL ha r0 h + mulBil hL ha h r0)‖
      ≤ Cmul L a * β * (Cmul L a * ‖r0‖ * ‖h‖ + Cmul L a * ‖h‖ * ‖r0‖) := by
    have h1 := norm_mulBil_le hL ha v0 (mulBil hL ha r0 h + mulBil hL ha h r0)
    have h2 : Cmul L a * ‖v0‖ * ‖mulBil hL ha r0 h + mulBil hL ha h r0‖
        ≤ Cmul L a * β * (Cmul L a * ‖r0‖ * ‖h‖ + Cmul L a * ‖h‖ * ‖r0‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hv hC0) hw (norm_nonneg _) (mul_nonneg hC0 hβ0)
    exact h1.trans h2
  have e : Nop hL ha hz κ v0 r0 h
      = (κ : ℂ) • ropCLM L z hz (mulBil hL ha v0 (mulBil hL ha r0 h + mulBil hL ha h r0)) := rfl
  have hR := norm_ropCLM_le L z hz (mulBil hL ha v0 (mulBil hL ha r0 h + mulBil hL ha h r0))
  rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc |κ| * ‖ropCLM L z hz (mulBil hL ha v0 (mulBil hL ha r0 h + mulBil hL ha h r0))‖
      ≤ |κ| * (z.im⁻¹ * ‖mulBil hL ha v0 (mulBil hL ha r0 h + mulBil hL ha h r0)‖) :=
        mul_le_mul_of_nonneg_left hR hk0
    _ ≤ |κ| * (z.im⁻¹ * (Cmul L a * β * (Cmul L a * ‖r0‖ * ‖h‖ + Cmul L a * ‖h‖ * ‖r0‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv' (inv_nonneg.2 hz.le)) hk0
    _ = (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (2 * ‖r0‖)) * ‖h‖ := by ring

/-- Operator norm of `N` at a small fixed point: `‖N‖ ≤ 1/4` under the E3a condition. -/
theorem norm_Nop_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ β : ℝ) (v0 r0 : Ell2) (hv : ‖v0‖ ≤ β) (hr0 : ‖r0‖ ≤ 2 * β / z.im)
    (hκ : 16 * |κ| * Cmul L a ^ 2 * β ^ 2 ≤ z.im ^ 2) :
    ‖Nop hL ha hz κ v0 r0‖ ≤ 1 / 4 := by
  have hβ0 : 0 ≤ β := (norm_nonneg v0).trans hv
  have hc0 : 0 ≤ |κ| * z.im⁻¹ * Cmul L a ^ 2 * β := by positivity
  have hM := contract_const_le (L := L) (a := a) hz κ β hκ
  have hK : |κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (2 * ‖r0‖)
      ≤ (1 / 2) * (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (2 * (4 * β / z.im))) := by
    have h2 : 2 * ‖r0‖ ≤ 4 * β / z.im := by
      have e4 : 4 * β / z.im = 2 * (2 * β / z.im) := by ring
      rw [e4]
      linarith
    calc |κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (2 * ‖r0‖)
        ≤ |κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (4 * β / z.im) :=
          mul_le_mul_of_nonneg_left h2 hc0
      _ = (1 / 2) * (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (2 * (4 * β / z.im))) := by ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  calc ‖Nop hL ha hz κ v0 r0 h‖
      ≤ (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (2 * ‖r0‖)) * ‖h‖ := norm_Nop_apply_le hL ha hz κ β v0 r0 h hv
    _ ≤ (1 / 4) * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        linarith

/-- The total derivative of the residual at `(p0, r0)` restricted to the `r`-slice is the
equivalence `I + N`. Its inverse is provided by the Neumann series `Units.oneSub`. -/
theorem id_add_Nop_isUnit {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ β : ℝ) (v0 r0 : Ell2) (hv : ‖v0‖ ≤ β) (hr0 : ‖r0‖ ≤ 2 * β / z.im)
    (hκ : 16 * |κ| * Cmul L a ^ 2 * β ^ 2 ≤ z.im ^ 2) :
    ‖-(Nop hL ha hz κ v0 r0)‖ < 1 := by
  rw [norm_neg]
  have := norm_Nop_le hL ha hz κ β v0 r0 hv hr0 hκ
  linarith

end QuantumNLS.RiccatiPicardAnalytic

#print axioms QuantumNLS.RiccatiPicardAnalytic.residG_analyticAt
#print axioms QuantumNLS.RiccatiPicardAnalytic.slice_deriv
#print axioms QuantumNLS.RiccatiPicardAnalytic.norm_Nop_le
