import QuantumNLS.LOCAL017NativeHaarR19
import QuantumNLS.ResetMoserOrbit

/-!
# `thm:reset-moser` (LOCAL-017), item 4 (data): the derivative bound and real analyticity of the radial primitive `β`

Source: `symplectic_correction.tex`, eq:reset-beta-bounds: "`dβ = Ω − ω`, `‖β_z‖ ≤ C‖z‖³`, `‖Dβ_z‖ ≤ C‖z‖²`, `‖D²β_z‖ ≤ C‖z‖`", and the complexification step
("Real analyticity at zero in the operator-valued sense gives a holomorphic extension ... on a ball in the complexification").

* `norm_Lval_le'`, `norm_fderiv_betaR_le`: `‖Dβ_z‖ ≤ 2M‖z‖²` on `B_ρ` (the sharper form of `norm_Lval_le`, with `‖z‖` in place of `ρ`);
* `betaR_analyticAt`: `β` is real analytic on `B_{ρ}` (`ρ` the radius of the frozen sol_ext_b native extension `LOCAL017SourceR19.nativeExtension`): `β = Re ∘ (complex radial primitive) ∘ ι`,
  the complex radial primitive being holomorphic (hence analytic, by the accepted GP-05 bridge).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.LOCAL017SourceR19
  QuantumNLS.Ext025A4BanachComplexification

theorem norm_Lval_le' (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖Lval S x t‖ ≤ 2 * M * ‖x‖ ^ 2 := by
  have htx : t • x ∈ ball (0 : K) ρ := scale_mem' hx ht
  have hn : ‖t • x‖ ≤ ‖x‖ := norm_scale_le ht
  have hn0 : 0 ≤ ‖t • x‖ := norm_nonneg _
  have hM := hL.M0
  have e1 : ‖Dl S (t • x)‖ ≤ M * ‖x‖ ^ 2 :=
    (hL.b2 _ htx).trans (mul_le_mul_of_nonneg_left (by nlinarith) hM)
  have e2 : ‖fderiv ℝ S.Ω (t • x)‖ ≤ M * ‖x‖ :=
    (hL.b1 _ htx).trans (mul_le_mul_of_nonneg_left hn hM)
  have h0 : 0 ≤ t := ht.1
  have h1 : t ≤ 1 := ht.2
  have e3 : ‖(ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))‖ ≤ M * ‖x‖ ^ 2 := by
    refine (norm_applycomp_le x _).trans ?_
    calc ‖fderiv ℝ S.Ω (t • x)‖ * ‖x‖ ≤ (M * ‖x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
      _ = M * ‖x‖ ^ 2 := by ring
  have hMx : 0 ≤ M * ‖x‖ ^ 2 := by positivity
  unfold Lval
  calc ‖t • Dl S (t • x) + (t ^ 2) • (ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))‖
      ≤ ‖t • Dl S (t • x)‖ + ‖(t ^ 2) • (ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))‖ :=
        norm_add_le _ _
    _ ≤ M * ‖x‖ ^ 2 + M * ‖x‖ ^ 2 := by
        refine add_le_add ?_ ?_
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
          calc t * ‖Dl S (t • x)‖ ≤ 1 * (M * ‖x‖ ^ 2) := mul_le_mul h1 e1 (norm_nonneg _) zero_le_one
            _ = M * ‖x‖ ^ 2 := one_mul _
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          calc t ^ 2 * ‖(ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))‖
              ≤ 1 * (M * ‖x‖ ^ 2) := mul_le_mul (by nlinarith) e3 (norm_nonneg _) zero_le_one
            _ = M * ‖x‖ ^ 2 := one_mul _
    _ = 2 * M * ‖x‖ ^ 2 := by ring

theorem norm_fderiv_betaR_le (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) :
    ‖fderiv ℝ (betaR S) x‖ ≤ 2 * M * ‖x‖ ^ 2 := by
  rw [(betaR_hasFDerivAt S hL hx).fderiv]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => Lval S x t) (C := 2 * M * ‖x‖ ^ 2) (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      exact norm_Lval_le' S hL hx ⟨ht.1.le, ht.2⟩)
  simpa using h

/-- The real part of a complex covector, restricted to the real slice. -/
def reRestr : CCov →L[ℝ] Cov :=
  LinearMap.mkContinuous
    { toFun := fun φ => Complex.reCLM.comp ((φ.restrictScalars ℝ).comp (Cx.ιL : K →L[ℝ] CH))
      map_add' := fun φ ψ => by ext h; simp
      map_smul' := fun c φ => by ext h; simp }
    1 (fun φ => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun h => ?_)
      change ‖(φ (Cx.ι h)).re‖ ≤ 1 * ‖φ‖ * ‖h‖
      calc ‖(φ (Cx.ι h)).re‖ ≤ ‖φ (Cx.ι h)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖φ‖ * ‖Cx.ι h‖ := φ.le_opNorm _
        _ = 1 * ‖φ‖ * ‖h‖ := by rw [Cx.norm_ι]; ring)

theorem reRestr_apply (φ : CCov) (h : K) : reRestr φ h = (φ (Cx.ι h)).re := rfl

theorem betaR_analyticAt (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) (nativeExtension S).radius) :
    AnalyticAt ℝ (betaR S) z := by
  set N := nativeExtension S with hN
  have hAn : AnalyticOnNhd ℂ (radialBeta N.form) (ball (0 : CH) N.radius) :=
    GP05AcceptedBridgeR16.banachHolomorphicBridge _ _ isOpen_ball N.holomorphic
  have hzC : Cx.ι z ∈ ball (0 : CH) N.radius := by
    simpa [mem_ball_zero_iff, Cx.norm_ι] using hz
  have h1 : AnalyticAt ℝ (radialBeta N.form) (Cx.ι z) := (hAn _ hzC).restrictScalars
  have h2 : AnalyticAt ℝ (fun w : K => radialBeta N.form (Cx.ι w)) z :=
    h1.comp (Cx.ιL.analyticAt z)
  have h3 : AnalyticAt ℝ (fun w : K => reRestr (radialBeta N.form (Cx.ι w))) z :=
    (reRestr.analyticAt _).comp h2
  refine h3.congr ?_
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  ext h
  rw [reRestr_apply, N.real_slice w hw h]
  simp

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.norm_fderiv_betaR_le
#print axioms QuantumNLS.ResetMoser.betaR_analyticAt
