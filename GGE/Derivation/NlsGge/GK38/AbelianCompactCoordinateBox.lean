import NlsGge.GK38.AbelianSolutionGapPlacement
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.Compact

/-! Uncompiled P5 compactness prerequisite. A FIXED genuine square-summable
coordinate radius gives a compact lp2 box. No lp2-ball envelope is asserted. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem p5Lp_coordinate_box_isCompact38 (ι : Type*) (e : ι → ℝ)
    (he0 : ∀ i, 0 ≤ e i) (hes : Summable (fun i => e i^2)) :
    IsCompact {t : lp (fun _ : ι => ℝ) 2 | ∀ i, ‖t i‖ ≤ e i} := by
  classical
  let K : Type _ := ∀ i : ι, Icc (-e i) (e i)
  have hxB (x : K) (i : ι) : ‖(x i : ℝ)‖ ≤ e i := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (x i).2
  have hxS (x : K) : Summable (fun i : ι => ‖(x i : ℝ)‖^2) :=
    hes.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i =>
      (sq_le_sq₀ (norm_nonneg _) (he0 i)).mpr (hxB x i))
  let T : K → lp (fun _ : ι => ℝ) 2 := fun x =>
    ⟨fun i => (x i : ℝ),(memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
      (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hxS x)⟩
  have hTB (x : K) (i : ι) : ‖T x i‖ ≤ e i := hxB x i
  have hcoord (i : ι) : Continuous (fun x : K => (x i : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  have hT : Continuous T := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hpoint (i : ι) :
        Tendsto (fun x : K => ‖T x i-T y i‖^2) (𝓝 y) (𝓝 (0 : ℝ)) := by
      change Tendsto (fun x : K => ‖(x i : ℝ)-(y i : ℝ)‖^2) (𝓝 y) (𝓝 (0 : ℝ))
      have hc : Tendsto (fun x : K => (x i : ℝ)-(y i : ℝ)) (𝓝 y) (𝓝 (0 : ℝ)) := by
        have hy : Tendsto (fun _ : K => (y i : ℝ)) (𝓝 y) (𝓝 (y i : ℝ)) :=
          tendsto_const_nhds
        simpa only [sub_self] using ((hcoord i).tendsto y).sub hy
      simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        hc.norm.pow 2
    have hbound : ∀ᶠ x : K in 𝓝 y, ∀ i : ι,
        ‖‖T x i-T y i‖^2‖ ≤ 4*e i^2 := by
      apply Eventually.of_forall
      intro x i
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hd : ‖T x i-T y i‖ ≤ 2*e i :=
        (norm_sub_le _ _).trans (by linarith [hTB x i,hTB y i])
      have hh := mul_self_le_mul_self (norm_nonneg _) hd
      nlinarith [hh]
    have hseries : Tendsto (fun x : K => ∑' i : ι, ‖T x i-T y i‖^2)
        (𝓝 y) (𝓝 (0 : ℝ)) := by
      simpa only [tsum_zero] using
        (tendsto_tsum_of_dominated_convergence (f := fun x i => ‖T x i-T y i‖^2)
          (g := fun _ => (0 : ℝ)) (hes.mul_left 4) hpoint hbound)
    have hnormsq : Tendsto (fun x : K => ‖T x-T y‖^2) (𝓝 y) (𝓝 (0 : ℝ)) := by
      apply hseries.congr'
      apply Eventually.of_forall
      intro x
      have hnorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (T x-T y)
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,lp.coeFn_sub,Pi.sub_apply] using hnorm.symm
    have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hnormsq
    have hnorm : Tendsto (fun x : K => ‖T x-T y‖) (𝓝 y) (𝓝 (0 : ℝ)) := by
      change Tendsto (fun x : K => Real.sqrt (‖T x-T y‖^2)) (𝓝 y)
        (𝓝 (Real.sqrt 0)) at hroot
      have heq : (fun x : K => Real.sqrt (‖T x-T y‖^2)) =
          (fun x : K => ‖T x-T y‖) := funext (fun x => Real.sqrt_sq (norm_nonneg _))
      rw [heq,Real.sqrt_zero] at hroot
      exact hroot
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hcompact : IsCompact (range T) := by
    simpa only [image_univ] using (isCompact_univ : IsCompact (univ : Set K)).image hT
  have hrange : range T={t : lp (fun _ : ι => ℝ) 2 | ∀ i, ‖t i‖ ≤ e i} := by
    ext t
    constructor
    · rintro ⟨x,rfl⟩
      exact hTB x
    · intro ht
      let x : K := fun i => ⟨t i,abs_le.mp (by simpa only [Real.norm_eq_abs] using ht i)⟩
      refine ⟨x,?_⟩
      apply Subtype.ext
      funext i
      rfl
  rwa [hrange] at hcompact

end
end NlsGge.GK38
