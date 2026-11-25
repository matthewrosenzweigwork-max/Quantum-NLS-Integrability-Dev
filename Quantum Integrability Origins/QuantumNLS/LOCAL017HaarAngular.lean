import QuantumNLS.LOCAL017HaarPath
import QuantumNLS.ResetMoserIsotropy
import QuantumNLS.ResetMoserAnnihilate

/-! LOCAL-017 item 3: Haar invariance removes the orbit-dependent constant
from any finite-torus primitive furnished by item 2.  Truncation then gives
exactly ResetMoserAnnihilate.hann on the entire Hilbert ball.  The item-2
finite-torus primitive is explicit in the interface and is not proved here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.LOCAL017Haar
open Ext025B7LocalPath ActionTorus ResetNormalizationUniqueness Ext025BHaar

/-- The rotation path, with real time extended beyond [0,1] for differentiation. -/
def ray (θ : AngleBox) (t : ℝ) (z : H) : H :=
  rotate (fun n => Circle.exp (t * (θ n).val)) z

theorem ray_zero (θ : AngleBox) (z : H) : ray θ 0 z = z := by
  ext n
  simp only [ray, rotate_apply, zero_mul, Circle.exp_zero, Circle.coe_one, one_mul]

theorem ray_norm (θ : AngleBox) (t : ℝ) (z : H) : ‖ray θ t z‖ = ‖z‖ := by
  apply norm_eq_of_norm_apply_eq
  intro n
  simp only [ray, rotate_apply, norm_mul, Circle.norm_coe, one_mul]

theorem ray_continuous (θ : AngleBox) (z : H) : Continuous (fun t : ℝ => ray θ t z) := by
  exact continuous_rotate.comp ((continuous_pi fun n =>
    Circle.exp.continuous.comp (continuous_id.mul_const _)).prodMk continuous_const)

theorem ray_lift_one (ψ : Torus) (z : H) : ray (angleLift ψ) 1 z = rotate ψ z := by
  unfold ray
  congr 1
  funext n
  exact (congrArg Circle.exp (one_mul _)).trans (Circle.exp_arg _)

def coordAngle (j : ℤ) : AngleBox := fun n =>
  ⟨if n = j then 1 else 0, by split_ifs <;> constructor <;> linarith [Real.pi_gt_three]⟩

theorem ray_coord (j : ℤ) (t : ℝ) (z : H) : ray (coordAngle j) t z = rot j t z := by
  ext n
  rw [rot_apply]
  simp only [ray, rotate_apply, coordAngle, Circle.coe_exp]
  by_cases hn : n = j <;> simp [hn]

theorem velocity_coord (j : ℤ) (z : H) : velocity (coordAngle j) z = vecX j z := by
  ext n
  rw [velocity_apply, vecX_apply]
  by_cases hn : n = j <;> simp [coordAngle, hn]

theorem norm_rotate (ψ : Torus) (z : H) : ‖rotate ψ z‖ = ‖z‖ := by
  apply norm_eq_of_norm_apply_eq
  intro n
  simp only [rotate_apply, norm_mul, Circle.norm_coe, one_mul]

/-- Item 2's periodic primitive on one finite coordinate torus, expressed only
through its values on that orbit and derivatives along the source paths.
This contains neither f, df, beta0 nor the annihilation conclusion. -/
structure OrbitPotential (β : H → Cov) (z : H) where
  value : H → ℝ
  continuous : Continuous (fun ψ : Torus => value (rotate ψ z))
  derivative : ∀ η : Torus, ∀ θ : AngleBox, ∀ t : ℝ,
    HasDerivAt (fun s => value (ray θ s (rotate η z)))
      (β (ray θ t (rotate η z)) (velocity θ (ray θ t (rotate η z)))) t

/-- Normalized interval volume has exactly the same scalar integral as
Lebesgue integration from 0 to 1. -/
theorem integral_unit (g : ℝ → ℝ) :
    (∫ t : unitInterval, g t) = ∫ t in (0 : ℝ)..1, g t := by
  rw [unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe,
    intervalIntegral.integral_of_le zero_le_one]
  exact integral_Icc_eq_integral_Ioc

theorem potential_path {R : ℝ} {β : H → Cov}
    (hβ : ContinuousOn β (ball 0 R)) {z : H} (hz : z ∈ ball 0 R)
    (P : OrbitPotential β z) (η : Torus) (θ : AngleBox) :
    (∫ t : unitInterval, pathIntegrand β (rotate η z) (θ,t)) =
      P.value (ray θ 1 (rotate η z)) - P.value (rotate η z) := by
  let g : ℝ → ℝ := fun t =>
    β (ray θ t (rotate η z)) (velocity θ (ray θ t (rotate η z)))
  have hc : Continuous g := by
    have hr := ray_continuous θ (rotate η z)
    have hm : ∀ t, ray θ t (rotate η z) ∈ ball (0 : H) R := by
      intro t
      simpa only [mem_ball_zero_iff, ray_norm, norm_rotate] using hz
    exact (hβ.comp_continuous hr hm).clm_apply (((velocity θ).restrictScalars ℝ).continuous.comp hr)
  have he : (fun t : unitInterval => pathIntegrand β (rotate η z) (θ,t)) = fun t : unitInterval => g (t : ℝ) := rfl
  rw [he, integral_unit]
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => P.derivative η θ t) (hc.intervalIntegrable 0 1)
  simpa only [ray_zero] using hh

/-- Haar invariance is used on scalar P-values, never on operator-valued maps. -/
theorem primitive_orbit {R : ℝ} {β : H → Cov}
    (hβ : ContinuousOn β (ball 0 R)) {z : H} (hz : z ∈ ball 0 R)
    (P : OrbitPotential β z) (η : Torus) :
    primitive β (rotate η z) = P.value (rotate η z) -
      ∫ ψ : Torus, P.value (rotate ψ z) ∂productCircleHaar := by
  have hw : rotate η z ∈ ball (0 : H) R := by
    simpa only [mem_ball_zero_iff, norm_rotate] using hz
  rw [primitive_haar β hβ hw]
  change -(∫ ψ : Torus, ∫ t : unitInterval,
    pathIntegrand β (rotate η z) (angleLift ψ, t) ∂volume ∂productCircleHaar) = _
  simp_rw [potential_path hβ hz P η, ray_lift_one]
  have hi : Integrable (fun ψ : Torus => P.value (rotate ψ (rotate η z))) productCircleHaar := by
    have he : (fun ψ : Torus => P.value (rotate ψ (rotate η z))) =
        fun ψ => P.value (rotate (η * ψ) z) := by
      funext ψ; rw [mul_comm η ψ, rotate_mul]
    rw [he]
    exact by
      simpa only [Function.comp_def, Pi.mul_apply, id_eq, integrableOn_univ] using
        (P.continuous.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact
        (μ := productCircleHaar) isCompact_univ
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
  have he : (fun ψ : Torus => P.value (rotate ψ (rotate η z))) =
      fun ψ => P.value (rotate (η * ψ) z) := by
    funext ψ; rw [mul_comm η ψ, rotate_mul]
  have hhaar : (∫ ψ : Torus, P.value (rotate (η * ψ) z) ∂productCircleHaar) =
      ∫ ψ : Torus, P.value (rotate ψ z) ∂productCircleHaar :=
    integral_mul_left_eq_self (μ := productCircleHaar) (fun ψ : Torus => P.value (rotate ψ z)) η
  rw [he, hhaar]
  ring

/-- Angular differentiation on a finite orbit, before passing to the closure. -/
theorem primitive_vecX {R : ℝ} {β : H → Cov}
    (hβ : ContinuousOn β (ball 0 R)) {z : H} (hz : z ∈ ball 0 R)
    (P : OrbitPotential β z) (hf : DifferentiableAt ℝ (primitive β) z) (j : ℤ) :
    fderiv ℝ (primitive β) z (vecX j z) = β z (vecX j z) := by
  have hh := P.derivative 1 (coordAngle j) 0
  simp_rw [rotate_one, ray_coord, rot_zero, velocity_coord] at hh
  have he : (fun t => primitive β (rot j t z)) = fun t => P.value (rot j t z) -
      ∫ ψ : Torus, P.value (rotate ψ z) ∂productCircleHaar := by
    funext t
    rw [← ray_coord]
    exact primitive_orbit hβ hz P (fun n => Circle.exp (t * (coordAngle j n).val))
  have hp := hh.sub_const (∫ ψ : Torus, P.value (rotate ψ z) ∂productCircleHaar)
  rw [← he] at hp
  have hc := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_rot j z 0)
    (rot_zero j z).symm
  simp only [rot_zero] at hc
  exact hc.unique hp

/-- The finite support stage uses only a finite linear combination of the
coordinate angular fields, including zero coordinates without division. -/
theorem primitive_angular_finite {R : ℝ} {β : H → Cov}
    (hβ : ContinuousOn β (ball 0 R)) {z : H} (hz : z ∈ ball 0 R)
    (hzfin : {n | z n ≠ 0}.Finite) (P : OrbitPotential β z)
    (hf : DifferentiableAt ℝ (primitive β) z) :
    ∀ h ∈ ResetMoser.Tz z, fderiv ℝ (primitive β) z h = β z h := by
  intro h hh
  classical
  obtain ⟨a, _, ha⟩ := ResetMoser.Tz_sum hzfin.toFinset (by simp) hh
  rw [ha]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he : ResetMoser.eT z j = vecX j z := by
    ext n
    rw [ResetMoser.eT_apply, vecX_apply]
  rw [he]
  exact primitive_vecX hβ hz P hf j

/-- **Exact hann interface** for ResetMoserAnnihilate.dq_Ycov_zero.
The finite-orbit potential is the output required from item 2. The full
C1 regularity below is supplied by primitive_analytic, not by an angular
derivative hypothesis. -/
theorem annihilates {R : ℝ} {β : H → Cov}
    (hβ : ContinuousOn β (ball 0 R))
    (hf : ContDiffOn ℝ 1 (primitive β) (ball 0 R))
    (hpot : ∀ z ∈ ball (0 : H) R, {n | z n ≠ 0}.Finite → Nonempty (OrbitPotential β z)) :
    ∀ z ∈ ball (0 : H) R, ∀ h ∈ ResetMoser.Tz z,
      (β z - fderiv ℝ (primitive β) z) h = 0 := by
  intro z hz h hh
  have hev : ∀ᶠ F : Finset ℤ in atTop, ResetMoser.trunc F z ∈ ball (0 : H) R :=
    (ResetMoser.trunc_tendsto z).eventually (isOpen_ball.mem_nhds hz)
  have hDc : ContinuousOn (fderiv ℝ (primitive β)) (ball (0 : H) R) :=
    hf.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  have hc : ContinuousOn (fun w => β w - fderiv ℝ (primitive β) w) (ball (0 : H) R) :=
    hβ.sub hDc
  have hcov : Tendsto (fun F : Finset ℤ => β (ResetMoser.trunc F z) -
      fderiv ℝ (primitive β) (ResetMoser.trunc F z)) atTop
      (𝓝 (β z - fderiv ℝ (primitive β) z)) :=
    (hc.continuousAt (isOpen_ball.mem_nhds hz)).tendsto.comp (ResetMoser.trunc_tendsto z)
  have hl : Tendsto (fun F : Finset ℤ => (β (ResetMoser.trunc F z) -
      fderiv ℝ (primitive β) (ResetMoser.trunc F z)) (ResetMoser.trunc F h)) atTop
      (𝓝 ((β z - fderiv ℝ (primitive β) z) h)) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := H) (F := ℝ)).continuous.tendsto
      (β z - fderiv ℝ (primitive β) z, h)).comp (hcov.prodMk_nhds (ResetMoser.trunc_tendsto h))
  have he : ∀ᶠ F : Finset ℤ in atTop,
      (β (ResetMoser.trunc F z) - fderiv ℝ (primitive β) (ResetMoser.trunc F z))
        (ResetMoser.trunc F h) = 0 := by
    filter_upwards [hev] with F hF
    obtain ⟨P⟩ := hpot _ hF (ResetMoser.trunc_finite F z)
    have hd := ((hf _ hF).contDiffAt (isOpen_ball.mem_nhds hF)).differentiableAt one_ne_zero
    have hh' := primitive_angular_finite hβ hF (ResetMoser.trunc_finite F z) P hd
      _ (ResetMoser.trunc_mem_Tz F hh)
    simp only [sub_apply, hh', sub_self]
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr' (he.mono fun F hF => hF.symm))

end QuantumNLS.LOCAL017Haar
