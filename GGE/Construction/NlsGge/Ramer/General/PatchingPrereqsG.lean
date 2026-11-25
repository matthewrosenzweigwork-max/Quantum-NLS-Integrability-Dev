import NlsGge.Ramer.General.ClosedDivergenceProductRuleGb
import NlsGge.Ramer.General.LocalBumpG

/-!
# Prerequisites for patching local closed divergences (GB8)

Generalization of `NlsGge/Ramer/PatchingPrereqs.lean` to a `RamerSetting S`.

1. `S.exists_countable_cover`, `S.exists_countable_cover_balls`: second countability of `S.E`
   (`S.instSecondCountableTopologyE` of G0) gives countable subcovers of open covers.
2. `S.exists_bump_productRuleClass_support` : product-rule-class bump with prescribed radius.
3. `S.exists_bumped_field_radius` : the field `ρ • K` with the bump of 2.

The purely generic bump lemmas `exists_bump_generic`, `bumped_field_generic` live in
`NlsGge.Ramer.Gen` (copied from the old file, which is not imported because it pulls in the
isotropic `ClosedDivergenceProductRule`).
-/

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace

namespace NlsGge.Ramer.Gen

section Bump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Generic bump: a `C²` function `η : E → ℝ` with values in `[0,1]`, `η = 1` on `B(x₀, r)`,
`η = 0` off `B(x₀, 2r)`, and globally bounded derivative. -/
theorem exists_bump_generic (x₀ : E) {r : ℝ} (hr0 : 0 < r) :
    ∃ η : E → ℝ, ContDiff ℝ 2 η ∧ (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧
      (∀ x ∈ Metric.ball x₀ r, η x = 1) ∧ (∀ x, x ∉ Metric.ball x₀ (2 * r) → η x = 0) ∧
      ∃ Mη : ℝ, ∀ x, ‖fderiv ℝ η x‖ ≤ Mη := by
  obtain ⟨M, hM⟩ := smoothTransition_deriv_bounded
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set φ : E → ℝ := fun x => (4 * r ^ 2 - ‖x - x₀‖ ^ 2) / (3 * r ^ 2) with hφ
  set η : E → ℝ := fun x => Real.smoothTransition (φ x) with hη
  have hφd : ContDiff ℝ 2 φ := by
    have : ContDiff ℝ 2 fun x : E => ‖x - x₀‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    exact (contDiff_const.sub this).div_const _
  have hηd : ContDiff ℝ 2 η := Real.smoothTransition.contDiff.comp hφd
  have hηout : ∀ x, 2 * r ≤ ‖x - x₀‖ → η x = 0 := by
    intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    have : (2 * r) ^ 2 ≤ ‖x - x₀‖ ^ 2 := by gcongr
    have h3 : 0 < 3 * r ^ 2 := by positivity
    rw [hφ]; dsimp only
    apply div_nonpos_of_nonpos_of_nonneg _ h3.le
    nlinarith
  have hηin : ∀ x, ‖x - x₀‖ < r → η x = 1 := by
    intro x hx
    apply Real.smoothTransition.one_of_one_le
    have : ‖x - x₀‖ ^ 2 ≤ r ^ 2 := by
      have := norm_nonneg (x - x₀)
      nlinarith
    have h3 : 0 < 3 * r ^ 2 := by positivity
    rw [hφ]; dsimp only
    rw [le_div_iff₀ h3]; nlinarith
  have hφder : ∀ x, HasFDerivAt φ ((-(1 / (3 * r ^ 2))) • (2 • (innerSL ℝ (x - x₀)))) x := by
    intro x
    have h0 : HasFDerivAt (fun y : E => y - x₀) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).sub_const x₀
    have h1 := (hasStrictFDerivAt_norm_sq (x - x₀)).hasFDerivAt.comp x h0
    have h2 := ((h1.const_sub (4 * r ^ 2)).const_mul (1 / (3 * r ^ 2)))
    convert h2 using 1
    · ext y; simp only [hφ, Function.comp]; field_simp
    · ext y; simp
  have hηder : ∀ x, ‖x - x₀‖ < 3 * r →
      ‖fderiv ℝ η x‖ ≤ M * (2 / (3 * r ^ 2) * (3 * r)) := by
    intro x hx
    have hd : HasFDerivAt η (deriv Real.smoothTransition (φ x) •
        ((-(1 / (3 * r ^ 2))) • (2 • (innerSL ℝ (x - x₀))))) x := by
      have := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) (φ x)
      exact (this.hasDerivAt).comp_hasFDerivAt x (hφder x)
    rw [hd.fderiv]
    have hn : ‖(-(1 / (3 * r ^ 2))) • (2 • (innerSL ℝ (x - x₀)))‖ ≤
        2 / (3 * r ^ 2) * (3 * r) := by
      have h2 : ‖(2 : ℕ) • innerSL ℝ (x - x₀)‖ ≤ 2 * ‖x - x₀‖ := by
        have := norm_nsmul_le (n := 2) (a := innerSL ℝ (x - x₀))
        rw [innerSL_apply_norm] at this
        simpa using this
      rw [norm_smul, norm_neg, norm_div, norm_one, Real.norm_of_nonneg (by positivity)]
      calc 1 / (3 * r ^ 2) * ‖(2 : ℕ) • innerSL ℝ (x - x₀)‖
          ≤ 1 / (3 * r ^ 2) * (2 * (3 * r)) := by gcongr; linarith
        _ = _ := by field_simp
    calc _ ≤ ‖deriv Real.smoothTransition (φ x)‖ *
          ‖(-(1 / (3 * r ^ 2))) • (2 • (innerSL ℝ (x - x₀)))‖ := norm_smul_le _ _
      _ ≤ M * (2 / (3 * r ^ 2) * (3 * r)) := mul_le_mul (hM _) hn (norm_nonneg _) hM0
  refine ⟨η, hηd, fun x => Real.smoothTransition.nonneg _, fun x => Real.smoothTransition.le_one _,
    fun x hx => hηin x (by rwa [Metric.mem_ball, dist_eq_norm] at hx), fun x hx =>
    hηout x (by rw [Metric.mem_ball, dist_eq_norm, not_lt] at hx; exact hx),
    M * (2 / (3 * r ^ 2) * (3 * r)), fun x => ?_⟩
  by_cases hx : ‖x - x₀‖ < 3 * r
  · exact hηder x hx
  · have hz : η =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {y : E | 2 * r < ‖y - x₀‖} :=
        isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
      refine Filter.eventually_of_mem (hopen.mem_nhds ?_) fun y hy => ?_
      · show 2 * r < ‖x - x₀‖
        linarith [not_lt.1 hx]
      · exact hηout y (le_of_lt hy)
    rw [hz.fderiv_eq, fderiv_fun_const, Pi.zero_apply, norm_zero]
    positivity

/-- Generic bounds for the bumped field `η • K`. -/
theorem bumped_field_generic {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K : E → F) (hK : ContDiff ℝ 2 K) (x₀ : E) {r : ℝ}
    (hr : 0 < r) (Kb Db : ℝ) (hKb : ∀ x ∈ Metric.ball x₀ (2 * r), ‖K x‖ ≤ Kb)
    (hDb : ∀ x ∈ Metric.ball x₀ (2 * r), ‖fderiv ℝ K x‖ ≤ Db)
    (η : E → ℝ) (hηd : ContDiff ℝ 2 η) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hηin : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hηout : ∀ x, x ∉ Metric.ball x₀ (2 * r) → η x = 0) (Mη : ℝ)
    (hMη : ∀ x, ‖fderiv ℝ η x‖ ≤ Mη) :
    ∃ B : ℝ, ContDiff ℝ 2 (fun x => η x • K x) ∧ (∀ x, ‖η x • K x‖ ≤ B) ∧
      (∀ x, ‖fderiv ℝ (fun x => η x • K x) x‖ ≤ B) ∧ Set.EqOn (fun x => η x • K x) K
        (Metric.ball x₀ r) := by
  have hKb0 : 0 ≤ Kb := by
    have := hKb x₀ (Metric.mem_ball_self (by positivity))
    exact (norm_nonneg _).trans this
  have hDb0 : 0 ≤ Db := by
    have := hDb x₀ (Metric.mem_ball_self (by positivity))
    exact (norm_nonneg _).trans this
  have hMη0 : 0 ≤ Mη := (norm_nonneg _).trans (hMη 0)
  have hGd : ContDiff ℝ 2 (fun x => η x • K x) := hηd.smul hK
  set G : E → F := fun x => η x • K x with hG
  -- derivative bound on the open ball
  have hGball : ∀ x ∈ Metric.ball x₀ (2 * r), ‖fderiv ℝ G x‖ ≤ Db + Mη * Kb := by
    intro x hx
    have hKd : HasFDerivAt K (fderiv ℝ K x) x :=
      ((hK.differentiable (by norm_num)) x).hasFDerivAt
    have hηd' : HasFDerivAt η (fderiv ℝ η x) x :=
      ((hηd.differentiable (by norm_num)) x).hasFDerivAt
    show ‖fderiv ℝ (fun y => η y • K y) x‖ ≤ _
    have hG' : HasFDerivAt (fun y => η y • K y) _ x := hηd'.smul hKd
    rw [hG'.fderiv]
    calc ‖η x • fderiv ℝ K x + (fderiv ℝ η x).smulRight (K x)‖
        ≤ ‖η x • fderiv ℝ K x‖ + ‖(fderiv ℝ η x).smulRight (K x)‖ := norm_add_le _ _
      _ ≤ Db + Mη * Kb := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη0 x)]
          calc η x * ‖fderiv ℝ K x‖ ≤ 1 * Db :=
              mul_le_mul (hη1 x) (hDb x hx) (norm_nonneg _) zero_le_one
            _ = Db := one_mul _
        · calc ‖(fderiv ℝ η x).smulRight (K x)‖ ≤ ‖fderiv ℝ η x‖ * ‖K x‖ :=
              (ContinuousLinearMap.norm_smulRight_apply _ _).le
            _ ≤ Mη * Kb := mul_le_mul (hMη x) (hKb x hx) (norm_nonneg _) hMη0
  -- extend to the closed ball by continuity, and to the exterior by local vanishing
  have hGcl : ∀ x ∈ Metric.closedBall x₀ (2 * r), ‖fderiv ℝ G x‖ ≤ Db + Mη * Kb := by
    intro x hx
    have hclosed : IsClosed {y : E | ‖fderiv ℝ G y‖ ≤ Db + Mη * Kb} :=
      isClosed_le ((hGd.continuous_fderiv (by norm_num)).norm) continuous_const
    have hsub : Metric.ball x₀ (2 * r) ⊆ {y | ‖fderiv ℝ G y‖ ≤ Db + Mη * Kb} := hGball
    have := closure_minimal hsub hclosed
    rw [closure_ball x₀ (by positivity)] at this
    exact this hx
  have hGbd : ∀ x, ‖fderiv ℝ G x‖ ≤ max (Db + Mη * Kb) 0 := by
    intro x
    by_cases hx : x ∈ Metric.closedBall x₀ (2 * r)
    · exact (hGcl x hx).trans (le_max_left _ _)
    · have hx' : 2 * r < ‖x - x₀‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hx; exact hx
      have hz : G =ᶠ[nhds x] fun _ => (0 : F) := by
        have hopen : IsOpen {y : E | 2 * r < ‖y - x₀‖} :=
          isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
        refine Filter.eventually_of_mem (hopen.mem_nhds hx') fun y hy => ?_
        show η y • K y = 0
        have : η y = 0 := hηout y (by
          rw [Metric.mem_ball, dist_eq_norm, not_lt]; exact le_of_lt hy)
        rw [this, zero_smul]
      rw [hz.fderiv_eq, fderiv_fun_const, Pi.zero_apply, norm_zero]
      exact le_max_right _ _
  have hGv : ∀ x, ‖G x‖ ≤ max Kb 0 := by
    intro x
    by_cases hx : x ∈ Metric.ball x₀ (2 * r)
    · calc ‖η x • K x‖ = |η x| * ‖K x‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * Kb := by
          rw [abs_of_nonneg (hη0 x)]
          exact mul_le_mul (hη1 x) (hKb x hx) (norm_nonneg _) zero_le_one
        _ ≤ _ := by rw [one_mul]; exact le_max_left _ _
    · show ‖η x • K x‖ ≤ _
      rw [hηout x hx, zero_smul, norm_zero]
      exact le_max_right _ _
  refine ⟨max (max Kb 0) (max (Db + Mη * Kb) 0), hGd, fun x => (hGv x).trans (le_max_left _ _),
    fun x => (hGbd x).trans (le_max_right _ _), ?_⟩
  intro x hx
  show η x • K x = K x
  rw [hηin x hx, one_smul]

end Bump


end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

section Cover

/-- Lindelof property of `S.E` for open covers. -/
theorem exists_countable_cover {ι : Type*} (U : ι → Set S.E)
    (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i) :
    ∃ T : Set ι, T.Countable ∧ ∀ x, ∃ i ∈ T, x ∈ U i := by
  obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable U hU
  refine ⟨T, hT, fun x => ?_⟩
  have hx : x ∈ ⋃ i, U i := by
    obtain ⟨i, hi⟩ := hcov x
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  rw [← hTeq] at hx
  simpa using hx

/-- Countable subcover by balls: if `r x > 0` for all `x`, countably many of the balls `B(x, r x)`
cover `S.E`. -/
theorem exists_countable_cover_balls (r : S.E → ℝ) (hr : ∀ x, 0 < r x) :
    ∃ T : Set S.E, T.Countable ∧
      ∀ x, ∃ y ∈ T, x ∈ Metric.ball y (r y) := by
  obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun x => Metric.ball x (r x)) (fun x => Metric.ball_mem_nhds x (hr x))
  refine ⟨T, hT, fun x => ?_⟩
  have hx : x ∈ ⋃ y ∈ T, Metric.ball y (r y) := by rw [hTeq]; trivial
  simpa using hx

end Cover

section Class

/-- **Bump in the product-rule class with prescribed radius.** For `x₀ ∈ S.E` and `r > 0` there is
`ρ` in the product-rule class with `ρ = 1` on `B(x₀, r)` and `ρ = 0` off `B(x₀, 2r)`. -/
theorem exists_bump_productRuleClass_support (x₀ : S.E) {r : ℝ} (hr : 0 < r) :
    ∃ (ρ : S.E → ℝ) (gradρ : S.E → S.H) (B : ℝ),
      S.ProductRuleClass ρ gradρ B ∧ (∀ x ∈ Metric.ball x₀ r, ρ x = 1) ∧
      (∀ x, x ∉ Metric.ball x₀ (2 * r) → ρ x = 0) := by
  obtain ⟨η, hηd, hη0, hη1, hηin, hηout, Mη, hMη⟩ := exists_bump_generic x₀ hr
  obtain ⟨gradρ, hρ⟩ := S.exists_productRuleClass η hηd (max 1 Mη)
    (fun x => by
      rw [Real.norm_of_nonneg (hη0 x)]; exact (hη1 x).trans (le_max_left _ _))
    (fun x => (hMη x).trans (le_max_right _ _))
  exact ⟨η, gradρ, _, hρ, hηin, hηout⟩

/-- **Bumped field with prescribed radius.** If `K : S.E → S.H` is `C²` and `K`, `DK` are bounded on
`B(x₀, 2r)`, then with the bump `ρ` of `exists_bump_productRuleClass_support`, the field
`G = ρ • K` is `C²`, bounded with globally bounded derivative, and `G = K` on `B(x₀, r)`. -/
theorem exists_bumped_field_radius (K : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (x₀ : S.E) {r : ℝ} (hr : 0 < r)
    (Kb Db : ℝ) (hKb : ∀ x ∈ Metric.ball x₀ (2 * r), ‖K x‖ ≤ Kb)
    (hDb : ∀ x ∈ Metric.ball x₀ (2 * r), ‖fderiv ℝ K x‖ ≤ Db) :
    ∃ (ρ : S.E → ℝ) (gradρ : S.E → S.H) (Bρ : ℝ),
      S.ProductRuleClass ρ gradρ Bρ ∧ (∀ x ∈ Metric.ball x₀ r, ρ x = 1) ∧
      (∀ x, x ∉ Metric.ball x₀ (2 * r) → ρ x = 0) ∧
      ∃ (G : S.E → S.H) (B : ℝ),
        G = (fun x => ρ x • K x) ∧ ContDiff ℝ 2 G ∧ (∀ x, ‖G x‖ ≤ B) ∧
        (∀ x, ‖fderiv ℝ G x‖ ≤ B) ∧ Set.EqOn G K (Metric.ball x₀ r) := by
  obtain ⟨η, hηd, hη0, hη1, hηin, hηout, Mη, hMη⟩ := exists_bump_generic x₀ hr
  obtain ⟨gradρ, hρ⟩ := S.exists_productRuleClass η hηd (max 1 Mη)
    (fun x => by
      rw [Real.norm_of_nonneg (hη0 x)]; exact (hη1 x).trans (le_max_left _ _))
    (fun x => (hMη x).trans (le_max_right _ _))
  obtain ⟨B, hGd, hGv, hGD, hEq⟩ := bumped_field_generic K hK x₀ hr Kb Db hKb hDb η hηd hη0 hη1
    hηin hηout Mη hMη
  exact ⟨η, gradρ, _, hρ, hηin, hηout, fun x => η x • K x, B, rfl, hGd, hGv, hGD, hEq⟩

end Class

end NlsGge.Ramer.General.RamerSetting
