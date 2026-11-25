import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB15AnFix
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB15Holder

/-! # Track B, contracts 18–19 (step 4): real-analytic local solution map

For local data `D : LocData M δ R Kd Cf` (PdeB13Local):
* the free and Duhamel operators as real continuous linear maps (`FWL`, `DWL`, `FVL`, `DVL`);
* `fp_analytic`: the fixed point `a ↦ fp δ R a ∈ L⁴` is real-analytic at every `a₀` with `‖a₀‖ < M`
  (generic `analytic_fixedPoint` with `G (a, f) = Pic δ a f`, analytic by `analyticOnNhd_Ncub`;
  `‖∂_f G‖ ≤ 1/2` from the contraction estimate on the ball `B(fp a₀, R/3) ⊆ B(0,R)`, and
  identification of the analytic branch with `fp` by uniqueness in the `R`-ball);
* `LF a = FVL a + DVL (Ncub δ (fp δ R a)) ∈ C([0,δ], L²)`: real-analytic on `‖a‖ < M`, and
  `LF a t = l2Flow t a` for `‖a‖ ≤ M`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open scoped ENNReal NNReal

attribute [local instance] isProbabilityMeasure_spatialMeasure

/-- The free trajectory `t ↦ e^{it∂ₓ²}a` on `[0,δ]`. -/
def fV (δ : ℝ) (a : PhysicalL2) : C(Set.Icc (0 : ℝ) δ, PhysicalL2) :=
  ⟨fun t => freeL2 t a, (continuous_freeL2 a).comp continuous_subtype_val⟩

theorem fV_sub (δ : ℝ) (a b : PhysicalL2) : fV δ (a - b) = fV δ a - fV δ b := by
  ext1 t
  exact freeL2_sub t a b

theorem fV_norm (δ : ℝ) (a : PhysicalL2) : ‖fV δ a‖ ≤ 1 * ‖a‖ := by
  rw [one_mul]
  refine (ContinuousMap.norm_le _ (norm_nonneg a)).2 fun t => ?_
  exact le_of_eq (norm_freeL2 t a)

namespace LocData

variable {M δ R Kd Cf : ℝ}

def FWL (D : LocData M δ R Kd Cf) : PhysicalL2 →L[ℝ] Lp ℂ 4 (slabMeasure δ) :=
  (AddMonoidHom.ofMapSub (fW δ) (fW_sub D.hδ1)).toRealLinearMap
    (AddMonoidHomClass.continuous_of_bound _ Cf D.fW_le)

def DWL (D : LocData M δ R Kd Cf) : Lp ℂ (4 / 3) (slabMeasure δ) →L[ℝ] Lp ℂ 4 (slabMeasure δ) :=
  (AddMonoidHom.ofMapSub (dW δ) (dW_sub D.hδ D.hδ1)).toRealLinearMap
    (AddMonoidHomClass.continuous_of_bound _ Kd D.dW_le)

theorem dV_norm_le (D : LocData M δ R Kd Cf) (F : Lp ℂ (4 / 3) (slabMeasure δ)) :
    ‖dV δ F‖ ≤ Kd * ‖F‖ :=
  (ContinuousMap.norm_le _ (mul_nonneg D.hKd (norm_nonneg F))).2 fun t => D.dV_le F t

def DVL (D : LocData M δ R Kd Cf) :
    Lp ℂ (4 / 3) (slabMeasure δ) →L[ℝ] C(Set.Icc (0 : ℝ) δ, PhysicalL2) :=
  (AddMonoidHom.ofMapSub (dV δ) (dV_sub D.hδ D.hδ1)).toRealLinearMap
    (AddMonoidHomClass.continuous_of_bound _ Kd D.dV_norm_le)

def FVL (_D : LocData M δ R Kd Cf) : PhysicalL2 →L[ℝ] C(Set.Icc (0 : ℝ) δ, PhysicalL2) :=
  (AddMonoidHom.ofMapSub (fV δ) (fV_sub δ)).toRealLinearMap
    (AddMonoidHomClass.continuous_of_bound _ 1 (fV_norm δ))

theorem FWL_apply (D : LocData M δ R Kd Cf) (a : PhysicalL2) : D.FWL a = fW δ a := rfl
theorem DWL_apply (D : LocData M δ R Kd Cf) (F : Lp ℂ (4 / 3) (slabMeasure δ)) :
    D.DWL F = dW δ F := rfl
theorem DVL_apply (D : LocData M δ R Kd Cf) (F : Lp ℂ (4 / 3) (slabMeasure δ)) :
    D.DVL F = dV δ F := rfl
theorem FVL_apply (D : LocData M δ R Kd Cf) (a : PhysicalL2) : D.FVL a = fV δ a := rfl

/-- The Picard map as a function on the product. -/
def picG (D : LocData M δ R Kd Cf) (p : PhysicalL2 × Lp ℂ 4 (slabMeasure δ)) :
    Lp ℂ 4 (slabMeasure δ) :=
  D.FWL p.1 + D.DWL (Ncub δ p.2)

theorem picG_eq (D : LocData M δ R Kd Cf) (a : PhysicalL2) (f : Lp ℂ 4 (slabMeasure δ)) :
    D.picG (a, f) = Pic δ a f := rfl

theorem analyticAt_picG (D : LocData M δ R Kd Cf) (p : PhysicalL2 × Lp ℂ 4 (slabMeasure δ)) :
    AnalyticAt ℝ D.picG p := by
  have h1 : AnalyticAt ℝ (fun q : PhysicalL2 × Lp ℂ 4 (slabMeasure δ) => D.FWL q.1) p :=
    AnalyticAt.comp (g := D.FWL) (f := fun q : PhysicalL2 × Lp ℂ 4 (slabMeasure δ) => q.1)
      (D.FWL.analyticAt _) analyticAt_fst
  have h2 : AnalyticAt ℝ (fun q : PhysicalL2 × Lp ℂ 4 (slabMeasure δ) => Ncub δ q.2) p :=
    AnalyticAt.comp (g := Ncub δ) (f := fun q : PhysicalL2 × Lp ℂ 4 (slabMeasure δ) => q.2)
      (analyticOnNhd_Ncub δ _ (Set.mem_univ _)) analyticAt_snd
  have h3 : AnalyticAt ℝ (fun q : PhysicalL2 × Lp ℂ 4 (slabMeasure δ) => D.DWL (Ncub δ q.2)) p :=
    AnalyticAt.comp (g := D.DWL) (f := fun q : PhysicalL2 × Lp ℂ 4 (slabMeasure δ) => Ncub δ q.2)
      (D.DWL.analyticAt _) h2
  exact h1.add h3

/-- **The fixed point depends analytically on the datum.** -/
theorem fp_analytic (D : LocData M δ R Kd Cf) {a₀ : PhysicalL2} (ha₀ : ‖a₀‖ < M) :
    AnalyticAt ℝ (fp δ R) a₀ := by
  set x₀ := fp δ R a₀ with hx₀
  have hfix : D.picG (a₀, x₀) = x₀ := by rw [picG_eq]; exact (D.fp_spec ha₀.le).2
  have hsmall : ‖x₀‖ ≤ 2 / 3 * R := D.fp_small ha₀.le
  have hGa := D.analyticAt_picG (a₀, x₀)
  have hφ : HasFDerivAt (fun x => D.picG (a₀, x))
      ((fderiv ℝ D.picG (a₀, x₀)).comp (ContinuousLinearMap.inr ℝ PhysicalL2
        (Lp ℂ 4 (slabMeasure δ)))) x₀ :=
    hGa.differentiableAt.hasFDerivAt.comp x₀ (hasFDerivAt_prodMk_right a₀ x₀)
  have hR3 : 0 < R / 3 := by linarith [D.hR]
  have hlip : LipschitzOnWith (2⁻¹ : ℝ≥0) (fun x => D.picG (a₀, x)) (Metric.ball x₀ (R / 3)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hxR : ‖x‖ ≤ R := by
      have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall hx)
      have h2 := norm_sub_norm_le x x₀
      rw [Metric.mem_ball, dist_eq_norm] at hx
      linarith
    have hyR : ‖y‖ ≤ R := by
      have h2 := norm_sub_norm_le y x₀
      rw [Metric.mem_ball, dist_eq_norm] at hy
      linarith
    rw [picG_eq, picG_eq, dist_eq_norm, dist_eq_norm]
    have h := D.pic_sub a₀ a₀ x y
    rw [sub_self, norm_zero, mul_zero, zero_add] at h
    refine h.trans ((D.contr hxR hyR).trans (le_of_eq ?_))
    simp
  have hnorm := hφ.le_of_lipschitzOn (Metric.ball_mem_nhds x₀ hR3) hlip
  have hL : ‖(fderiv ℝ D.picG (a₀, x₀)).comp
      (ContinuousLinearMap.inr ℝ PhysicalL2 (Lp ℂ 4 (slabMeasure δ)))‖ < 1 := by
    refine hnorm.trans_lt ?_
    norm_num
  obtain ⟨g, hg, hg0, hgfix⟩ := analytic_fixedPoint hGa hfix hL
  have hgR : ∀ᶠ a in 𝓝 a₀, ‖g a‖ < R := by
    have hc : Tendsto (fun x => ‖g x‖) (𝓝 a₀) (𝓝 ‖x₀‖) := by
      have := hg.continuousAt.norm.tendsto
      simpa only [hg0] using this
    exact hc.eventually (gt_mem_nhds (by linarith [D.hR]))
  have hM : ∀ᶠ a in 𝓝 a₀, ‖a‖ < M := continuous_norm.continuousAt.eventually (gt_mem_nhds ha₀)
  have heq : g =ᶠ[𝓝 a₀] fp δ R := by
    filter_upwards [hgR, hM, hgfix] with a h1 h2 h3
    rw [picG_eq] at h3
    exact (D.fp_eq h2.le h1.le h3).symm
  exact hg.congr heq

/-- The local solution map into `C([0,δ], L²)`. -/
def LF (D : LocData M δ R Kd Cf) (a : PhysicalL2) : C(Set.Icc (0 : ℝ) δ, PhysicalL2) :=
  D.FVL a + D.DVL (Ncub δ (fp δ R a))

theorem LF_apply (D : LocData M δ R Kd Cf) {a : PhysicalL2} (ha : ‖a‖ ≤ M)
    (t : Set.Icc (0 : ℝ) δ) : D.LF a t = l2Flow t a := by
  rw [D.l2Flow_eq ha t]
  rfl

theorem LF_analytic (D : LocData M δ R Kd Cf) {a₀ : PhysicalL2} (ha₀ : ‖a₀‖ < M) :
    AnalyticAt ℝ D.LF a₀ := by
  have h1 : AnalyticAt ℝ (fun a => Ncub δ (fp δ R a)) a₀ :=
    AnalyticAt.comp (g := Ncub δ) (f := fp δ R) (analyticOnNhd_Ncub δ _ (Set.mem_univ _))
      (D.fp_analytic ha₀)
  have h2 : AnalyticAt ℝ (fun a => D.DVL (Ncub δ (fp δ R a))) a₀ :=
    AnalyticAt.comp (g := D.DVL) (f := fun a => Ncub δ (fp δ R a)) (D.DVL.analyticAt _) h1
  exact (D.FVL.analyticAt a₀).add h2

end LocData

end LiebLiniger.FixedPeriod.ALLS.PdeB
