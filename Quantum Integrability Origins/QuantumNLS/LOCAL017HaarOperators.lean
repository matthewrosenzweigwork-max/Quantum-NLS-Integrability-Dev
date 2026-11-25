import QuantumNLS.LOCAL017HaarAnalytic
import QuantumNLS.Ext025A4BanachComplexification

/-! Canonical complexified rotations and velocities, with their original
bounds. Strong continuity for fixed vectors proves scalar measurability of
the holomorphic integrand; this is not an extra source premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.LOCAL017Haar
open Ext025B7LocalPath Ext025A4BanachComplexification

/-- The literal rotation as a bounded real operator. -/
def rotationCLM (p : PathParameter) : H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := rotation p
      map_add' := fun z w => by
        ext n
        simp only [Ext025B7LocalPath.rotation, ActionTorus.rotate_apply, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c z => by
        ext n
        change (rotationAngles p n : ℂ) * ((c : ℂ) * z n) =
          (c : ℂ) * ((rotationAngles p n : ℂ) * z n)
        ring }
    1 (fun z => by
      change ‖Ext025B7LocalPath.rotation p z‖ ≤ 1 * ‖z‖
      rw [rotation_norm, one_mul])

theorem rotationCLM_norm (p : PathParameter) : ‖rotationCLM p‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

abbrev CH := Cx H

def complexRotation (p : PathParameter) : CH →L[ℂ] CH := Cx.mapL (rotationCLM p)
def complexVelocity (p : PathParameter) : CH →L[ℂ] CH :=
  Cx.mapL ((velocity p.1).restrictScalars ℝ)

theorem complexRotation_bound (p : PathParameter) (z : CH) :
    ‖complexRotation p z‖ ≤ ‖z‖ := by
  exact ((complexRotation p).le_opNorm z).trans (by
    have hh : ‖complexRotation p‖ ≤ 1 := (Cx.norm_mapL_le _).trans (rotationCLM_norm p)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (norm_nonneg z))

theorem complexVelocity_bound (p : PathParameter) (z : CH) :
    ‖complexVelocity p z‖ ≤ Real.pi * ‖z‖ := by
  have hv : ‖(velocity p.1).restrictScalars ℝ‖ ≤ Real.pi :=
    ContinuousLinearMap.opNorm_le_bound _ Real.pi_pos.le (velocity_norm_le p.1)
  exact ((complexVelocity p).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right ((Cx.norm_mapL_le _).trans hv) (norm_nonneg z))

/-- No operator-norm continuity is used, even after complexification. -/
theorem complexRotation_fixed (z : CH) : Continuous (fun p => complexRotation p z) := by
  change Continuous (fun p : PathParameter => Cx.mk (rotation p (Cx.re z)) (rotation p (Cx.im z)))
  simp_rw [Cx.mk_eq]
  have hr (w : H) : Continuous (fun p : PathParameter => rotation p w) :=
    rotation_continuous.comp (continuous_id.prodMk continuous_const)
  exact (Cx.ιL.continuous.comp (hr _)).add
    ((Cx.ιL.continuous.comp (hr _)).const_smul Complex.I)

theorem complexVelocity_rotated_fixed (z : CH) :
    Continuous (fun p => complexVelocity p (complexRotation p z)) := by
  change Continuous (fun p : PathParameter =>
    Cx.mk (velocity p.1 (rotation p (Cx.re z))) (velocity p.1 (rotation p (Cx.im z))))
  simp_rw [Cx.mk_eq]
  have hv (w : H) : Continuous (fun p : PathParameter => velocity p.1 (rotation p w)) := by
    exact velocity_continuous.comp (continuous_fst.prodMk
      (rotation_continuous.comp (continuous_id.prodMk continuous_const)))
  exact (Cx.ιL.continuous.comp (hv _)).add
    ((Cx.ιL.continuous.comp (hv _)).const_smul Complex.I)

theorem complex_integrand_measurable {R : ℝ} (b : CH → CH →L[ℂ] ℂ)
    (hb : DifferentiableOn ℂ b (ball 0 R)) {z : CH} (hz : z ∈ ball 0 R) :
    Measurable (fun p => GP05ScalarAverageR14.correctingIntegrand b complexRotation complexVelocity p z) := by
  have hr := complexRotation_fixed z
  have hm : ∀ p, complexRotation p z ∈ ball (0 : CH) R := fun p =>
    mem_ball_zero_iff.mpr ((complexRotation_bound p z).trans_lt (mem_ball_zero_iff.mp hz))
  exact ((hb.continuousOn.comp_continuous hr hm).clm_apply
    (complexVelocity_rotated_fixed z)).neg.measurable

/-- Instantiating the common holomorphic beta extension now supplies all
operator and parameter bindings automatically, rather than assuming them. -/
def canonicalData (β : H → Cov) (b : CH → CH →L[ℂ] ℂ) {R C : ℝ}
    (hr : ∀ z ∈ ball (0 : H) R, ∀ h, b (Cx.ι z) (Cx.ι h) = (β z h : ℂ))
    (hb : DifferentiableOn ℂ b (ball 0 R))
    (hc : ∀ z ∈ ball (0 : CH) R, ‖b z‖ ≤ C * ‖z‖^3)
    (bridge : GP05CauchyMajorantsR14.BanachHolomorphicBridge CH (CH →L[ℂ] ℂ)) :
    ComplexData (E := CH) β R C where
  embed := Cx.ιL
  embed_norm := Cx.norm_ι
  beta := b
  rot := complexRotation
  vel := complexVelocity
  rot_bound := complexRotation_bound
  vel_bound := complexVelocity_bound
  rot_real := fun p z => Cx.mapL_ι (rotationCLM p) z
  vel_real := fun p z => Cx.mapL_ι ((velocity p.1).restrictScalars ℝ) z
  beta_real := hr
  holomorphic := hb
  cubic := hc
  measurable := fun _ hz => complex_integrand_measurable b hb hz
  bridge := bridge

end QuantumNLS.LOCAL017Haar
