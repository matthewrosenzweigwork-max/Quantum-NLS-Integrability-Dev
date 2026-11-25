import NlsGge.Ramer.ActualHeadLawBridge
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Sobolev.RealBasis
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Local bump truncation of a `C²` field

Generic lemma: a `C²` map `K : E → F` between real normed spaces (`E` inner product space) agrees on a
small ball around `x₀` with a `C²` map `G` that is globally bounded with globally bounded derivative.
Instantiated at `FullWeightedHilbert c s → ActualCM c`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Ramer

open Real

/-- The derivative of `smoothTransition` is bounded. -/
theorem smoothTransition_deriv_bounded : ∃ M : ℝ, ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hsupp : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) ?_
    intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · have : Real.smoothTransition =ᶠ[nhds t] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (Iio_mem_nhds h)
          fun y hy => Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [this.deriv_eq]; simp
    · have : Real.smoothTransition =ᶠ[nhds t] fun _ => (1 : ℝ) :=
        Filter.eventually_of_mem (Ioi_mem_nhds h)
          fun y hy => Real.smoothTransition.one_of_one_le (le_of_lt hy)
      rw [this.deriv_eq]; simp
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hsupp
  exact ⟨M, hM⟩

/-- Generic local bump truncation. -/
theorem exists_bumped_field_generic {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K : E → F) (hK : ContDiff ℝ 2 K) (x₀ : E) :
    ∃ r > 0, ∃ G : E → F, ∃ B : ℝ,
      ContDiff ℝ 2 G ∧ (∀ x, ‖G x‖ ≤ B) ∧ (∀ x, ‖fderiv ℝ G x‖ ≤ B) ∧
      Set.EqOn G K (Metric.ball x₀ r) := by
  -- radius from continuity
  have hKc : Continuous K := hK.continuous
  have hDc : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by norm_num)
  have h1 : ∀ᶠ x in nhds x₀, ‖K x‖ < ‖K x₀‖ + 1 :=
    (hKc.continuousAt.norm).eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ x in nhds x₀, ‖fderiv ℝ K x‖ < ‖fderiv ℝ K x₀‖ + 1 :=
    (hDc.continuousAt.norm).eventually (gt_mem_nhds (by linarith))
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  set r : ℝ := ρ / 3 with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨M, hM⟩ := smoothTransition_deriv_bounded
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- cutoff
  set φ : E → ℝ := fun x => (4 * r ^ 2 - ‖x - x₀‖ ^ 2) / (3 * r ^ 2) with hφ
  set η : E → ℝ := fun x => Real.smoothTransition (φ x) with hη
  have hφd : ContDiff ℝ 2 φ := by
    have : ContDiff ℝ 2 fun x : E => ‖x - x₀‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    exact (contDiff_const.sub this).div_const _
  have hηd : ContDiff ℝ 2 η := Real.smoothTransition.contDiff.comp hφd
  have hη0 : ∀ x, 0 ≤ η x := fun x => Real.smoothTransition.nonneg _
  have hη1 : ∀ x, η x ≤ 1 := fun x => Real.smoothTransition.le_one _
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
  -- derivative of the cutoff
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
  set Kb : ℝ := ‖K x₀‖ + 1 with hKb
  set Db : ℝ := ‖fderiv ℝ K x₀‖ + 1 with hDb
  set Mη : ℝ := M * (2 / (3 * r ^ 2) * (3 * r)) with hMη
  have hKb0 : 0 ≤ Kb := by positivity
  have hDb0 : 0 ≤ Db := by positivity
  have hMη0 : 0 ≤ Mη := by positivity
  have hρr : ρ = 3 * r := by rw [hr]; ring
  refine ⟨r, hr0, fun x => η x • K x, max Kb (Db + Mη * Kb), hηd.smul hK, ?_, ?_, ?_⟩
  · intro x
    show ‖η x • K x‖ ≤ _
    by_cases hx : ‖x - x₀‖ < 3 * r
    · have hxb : x ∈ Metric.ball x₀ ρ := by rw [Metric.mem_ball, dist_eq_norm, hρr]; exact hx
      calc ‖η x • K x‖ = |η x| * ‖K x‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * Kb := by
          rw [abs_of_nonneg (hη0 x)]
          exact mul_le_mul (hη1 x) (hρ' x hxb).1.le (norm_nonneg _) zero_le_one
        _ ≤ _ := by rw [one_mul]; exact le_max_left _ _
    · rw [hηout x (by linarith [not_lt.1 hx]), zero_smul, norm_zero]
      exact le_trans hKb0 (le_max_left _ _)
  · intro x
    by_cases hx : ‖x - x₀‖ < 3 * r
    · have hxb : x ∈ Metric.ball x₀ ρ := by rw [Metric.mem_ball, dist_eq_norm, hρr]; exact hx
      have hKd : HasFDerivAt K (fderiv ℝ K x) x :=
        ((hK.differentiable (by norm_num)) x).hasFDerivAt
      have hηd' : HasFDerivAt η (fderiv ℝ η x) x :=
        ((hηd.differentiable (by norm_num)) x).hasFDerivAt
      have hG : HasFDerivAt (fun y => η y • K y) _ x := hηd'.smul hKd
      rw [hG.fderiv]
      have hb := hρ' x hxb
      calc ‖η x • fderiv ℝ K x + (fderiv ℝ η x).smulRight (K x)‖
          ≤ ‖η x • fderiv ℝ K x‖ + ‖(fderiv ℝ η x).smulRight (K x)‖ := norm_add_le _ _
        _ ≤ Db + Mη * Kb := by
          apply add_le_add
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη0 x)]
            calc η x * ‖fderiv ℝ K x‖ ≤ 1 * Db :=
                mul_le_mul (hη1 x) hb.2.le (norm_nonneg _) zero_le_one
              _ = Db := one_mul _
          · calc ‖(fderiv ℝ η x).smulRight (K x)‖ ≤ ‖fderiv ℝ η x‖ * ‖K x‖ :=
                (ContinuousLinearMap.norm_smulRight_apply _ _).le
              _ ≤ Mη * Kb := mul_le_mul (hηder x hx) hb.1.le (norm_nonneg _) hMη0
        _ ≤ _ := le_max_right _ _
    · have hz : (fun y => η y • K y) =ᶠ[nhds x] fun _ => (0 : F) := by
        have hopen : IsOpen {y : E | 2 * r < ‖y - x₀‖} :=
          isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
        refine Filter.eventually_of_mem (hopen.mem_nhds ?_) fun y hy => ?_
        · show 2 * r < ‖x - x₀‖
          linarith [not_lt.1 hx]
        · show η y • K y = 0
          rw [hηout y (le_of_lt hy), zero_smul]
      rw [hz.fderiv_eq, fderiv_fun_const, Pi.zero_apply, norm_zero]
      exact le_trans hKb0 (le_max_left _ _)
  · intro x hx
    have hx' : ‖x - x₀‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    show η x • K x = K x
    rw [hηin x hx', one_smul]

open NlsGge.Pilot

theorem exists_bumped_field {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ)
    (K : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K)
    (x₀ : NlsGge.Pilot.FullWeightedHilbert c s) :
    ∃ r > 0, ∃ G : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c, ∃ B : ℝ,
      ContDiff ℝ 2 G ∧ (∀ x, ‖G x‖ ≤ B) ∧ (∀ x, ‖fderiv ℝ G x‖ ≤ B) ∧
      Set.EqOn G K (Metric.ball x₀ r) :=
  exists_bumped_field_generic K hK x₀

end NlsGge.Ramer
