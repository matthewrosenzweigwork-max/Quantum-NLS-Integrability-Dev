import NlsGge.Birkhoff.F01Determinant38d
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! # W08 (Birkhoff wave B2), file 1: B-free compactness of the `h²` ball in `h¹` and the tail factor

Claim `W08` (`D:lem:localinject`, v2 l.1587-1614), blueprint `blueprint/claims/W08.md`.
This file contains only declarations that do not mention `BirkhoffInput38`:

* the finite-rank/finite-dimensionality of `P_N` at every Sobolev level,
* the one-derivative tail factor `‖(1-P_N) ι₂₁ y‖_{h¹} ≤ ⟨N⟩⁻¹ ‖y‖_{h²}` (v2: `C_R ⟨N⟩⁻¹ ‖x-y‖`),
* the inclusion `ι₂₁ : h² → h¹` is a compact operator, hence the `h²` ball has compact closure in `h¹`
  (v2: "The closed `h²` ball is compact in `h¹`").
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations
open Filter Topology Metric

theorem projC38_toLinearMap_W08 (r : ℝ) (N : ℕ) :
    ((projC38 r N : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r) : SobolevCarrier38 r →ₗ[ℝ] SobolevCarrier38 r) =
      projLin38 r N := rfl

/-- The range of `P_N` on `h^r` is finite-dimensional. -/
theorem finiteDimensional_range_projC38_W08 (r : ℝ) (N : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (projLin38 r N)) := by
  let g : SobolevCarrier38 r →ₗ[ℝ] (↥(symmetricModes N) → ℂ) :=
    { toFun := fun x n => carrierCoe38 r x n
      map_add' := fun x y => rfl
      map_smul' := fun c x => by
        funext n
        simp [Complex.real_smul]
        rfl }
  refine Module.Finite.of_injective (g.domRestrict (LinearMap.range (projLin38 r N))) ?_
  intro x y hxy
  apply Subtype.ext
  apply carrierExt38
  funext n
  obtain ⟨x', hx'⟩ := x.2
  obtain ⟨y', hy'⟩ := y.2
  by_cases hn : n ∈ symmetricModes N
  · exact congrFun hxy ⟨n, hn⟩
  · have e1 : carrierCoe38 r x.1 n = 0 := by
      rw [← hx']
      show carrierCoe38 r (projC38 r N x') n = 0
      rw [carrierCoe38_projC38, ite_eq_right_iff.2 (fun h => absurd h hn)]
    have e2 : carrierCoe38 r y.1 n = 0 := by
      rw [← hy']
      show carrierCoe38 r (projC38 r N y') n = 0
      rw [carrierCoe38_projC38, ite_eq_right_iff.2 (fun h => absurd h hn)]
    rw [e1, e2]

/-- `η_N = ⟨N⟩⁻¹`, the one-derivative tail factor. -/
def tailFactor38 (N : ℕ) : ℝ := (japaneseBracket (N : ℤ))⁻¹

theorem tailFactor38_nonneg (N : ℕ) : 0 ≤ tailFactor38 N :=
  inv_nonneg.2 (japaneseBracket_pos _).le

theorem tendsto_tailFactor38 : Tendsto tailFactor38 atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => japaneseBracket (N : ℤ)) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    unfold japaneseBracket
    refine Real.le_sqrt_of_sq_le ?_
    push_cast
    nlinarith
  exact tendsto_inv_atTop_zero.comp h

/-- **W08.04 (tail factor).** For `y ∈ h²`,
`‖(1-P_N) y‖_{h¹} ≤ ⟨N⟩⁻¹ ‖y‖_{h²}`. -/
theorem norm_compl_i21_le_W08 (N : ℕ) (y : H2_38) :
    ‖compl38 ((1 : ℕ) : ℝ) N (i21_38 y)‖ ≤ tailFactor38 N * ‖y‖ := by
  have hB : (japaneseBracket (N : ℤ)) ^ 2 = 1 + (N : ℝ) ^ 2 := by
    unfold japaneseBracket
    rw [Real.sq_sqrt (by positivity)]
    push_cast; ring
  have hpos : 0 < japaneseBracket (N : ℤ) := japaneseBracket_pos _
  set a := compl38 ((1 : ℕ) : ℝ) N (i21_38 y) with ha
  have h1 := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) a
  have h2 := (carrier_hasSum_norm_sq38 (((1 + 1 : ℕ)) : ℝ) y).mul_left ((japaneseBracket (N : ℤ))⁻¹ ^ 2)
  have hle : ‖a‖ ^ 2 ≤ (japaneseBracket (N : ℤ))⁻¹ ^ 2 * ‖y‖ ^ 2 := by
    refine hasSum_le (fun n => ?_) h1 h2
    have han : carrierCoe38 ((1 : ℕ) : ℝ) a n =
        carrierCoe38 ((1 : ℕ) : ℝ) (i21_38 y) n -
          (if n ∈ symmetricModes N then carrierCoe38 ((1 : ℕ) : ℝ) (i21_38 y) n else 0) := rfl
    have hw1 : sobolevModeWeight ((1 : ℕ) : ℝ) n = 1 + (n : ℝ) ^ 2 := by
      rw [sobolevModeWeight_natCast_F01_38]; ring
    have hw2 : sobolevModeWeight (((1 + 1 : ℕ)) : ℝ) n = (1 + (n : ℝ) ^ 2) ^ 2 := by
      rw [sobolevModeWeight_natCast_F01_38]
    rw [hw1, hw2, han]
    by_cases hn : n ∈ symmetricModes N
    · rw [ite_eq_left_iff.2 (fun h => absurd hn h), sub_self]; simp only [norm_zero]
      rw [zero_pow two_ne_zero, mul_zero]; positivity
    · rw [ite_eq_right_iff.2 (fun h => absurd h hn), sub_zero, carrierCoe38_i21]
      have hn' : (N : ℝ) + 1 ≤ |(n : ℝ)| := by
        have : (N : ℤ) + 1 ≤ |n| := by
          unfold symmetricModes at hn
          rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
          rcases hn with h | h
          · rw [abs_of_neg (by omega)]; omega
          · rw [abs_of_pos (by omega)]; omega
        exact_mod_cast this
      have hsq : 1 + (N : ℝ) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by
        have : (N : ℝ) ^ 2 ≤ |(n : ℝ)| ^ 2 := by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
        rw [sq_abs] at this
        linarith
      rw [inv_pow, hB]
      have ht : 0 ≤ ‖carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y n‖ ^ 2 := sq_nonneg _
      generalize ‖carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y n‖ ^ 2 = t at ht ⊢
      have hp : 0 < 1 + (N : ℝ) ^ 2 := by positivity
      have hq : 0 < 1 + (n : ℝ) ^ 2 := by positivity
      rw [← sub_nonneg]
      have e : (1 + (N : ℝ) ^ 2)⁻¹ * ((1 + (n : ℝ) ^ 2) ^ 2 * t) - (1 + (n : ℝ) ^ 2) * t =
          (1 + (n : ℝ) ^ 2) * t * ((1 + (n : ℝ) ^ 2) - (1 + (N : ℝ) ^ 2)) / (1 + (N : ℝ) ^ 2) := by
        field_simp
      rw [e]
      apply div_nonneg _ hp.le
      exact mul_nonneg (mul_nonneg hq.le ht) (by linarith)
  have hle' : ‖a‖ ^ 2 ≤ (tailFactor38 N * ‖y‖) ^ 2 := by
    rw [mul_pow]; exact hle
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (tailFactor38_nonneg N) (norm_nonneg _))).1 hle'

/-- `‖ι₂₁ − P_N ι₂₁‖ ≤ ⟨N⟩⁻¹` in operator norm. -/
theorem norm_i21_sub_proj_le_W08 (N : ℕ) :
    ‖i21_38 - (projC38 ((1 : ℕ) : ℝ) N).comp i21_38‖ ≤ tailFactor38 N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (tailFactor38_nonneg N) (fun y => ?_)
  have := norm_compl_i21_le_W08 N y
  rw [compl38_apply] at this
  simpa using this

theorem isCompactOperator_i21_W08 : IsCompactOperator i21_38 := by
  have hlim : Tendsto (fun N : ℕ => (projC38 ((1 : ℕ) : ℝ) N).comp i21_38) atTop (𝓝 i21_38) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) tendsto_tailFactor38
    rw [norm_sub_rev]
    exact norm_i21_sub_proj_le_W08 N
  refine isCompactOperator_of_tendsto hlim (Eventually.of_forall (fun N => ?_))
  have := finiteDimensional_range_projC38_W08 ((1 : ℕ) : ℝ) N
  let g : H2_38 →L[ℝ] LinearMap.range (projLin38 ((1 : ℕ) : ℝ) N) :=
    ((projC38 ((1 : ℕ) : ℝ) N).comp i21_38).codRestrict (LinearMap.range (projLin38 ((1 : ℕ) : ℝ) N))
      (fun y => ⟨i21_38 y, rfl⟩)
  have h1 : IsCompactOperator (LinearMap.range (projLin38 ((1 : ℕ) : ℝ) N)).subtypeL :=
    isCompactOperator_of_locallyCompactSpace_rng _
  have := h1.comp_clm g
  exact this

/-- **W08 (compactness).** The closed `h²` ball, viewed in `h¹`, has compact closure
(v2: "The closed `h²` ball is compact in `h¹`"). -/
theorem isCompact_closure_ballH1_W08 (R : ℝ) :
    IsCompact (closure (i21_38 '' closedBall (0 : H2_38) R)) :=
  isCompactOperator_i21_W08.isCompact_closure_image_closedBall R


/-! ## The `h²` ball inside `h¹` -/

/-- `{x ∈ h² : ‖x‖_{h²} ≤ R}` as a subset of `h¹` (the image of the closed ball under `ι₂₁`). -/
def ballH1 (R : ℝ) : Set H1_38 := i21_38 '' closedBall (0 : H2_38) R

theorem mem_ballH1_iff (R : ℝ) (x : H1_38) :
    x ∈ ballH1 R ↔ ∃ y : H2_38, ‖y‖ ≤ R ∧ i21_38 y = x := by
  unfold ballH1
  simp only [Set.mem_image, mem_closedBall, dist_zero_right]

theorem convex_ballH1 (R : ℝ) : Convex ℝ (ballH1 R) :=
  (convex_closedBall (0 : H2_38) R).linear_image i21_38.toLinearMap

theorem isCompact_closure_ballH1 (R : ℝ) : IsCompact (closure (ballH1 R)) :=
  isCompact_closure_ballH1_W08 R

theorem ballH1_mono {R R' : ℝ} (h : R ≤ R') : ballH1 R ⊆ ballH1 R' :=
  Set.image_mono (closedBall_subset_closedBall h)

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)

/-! ## W08.01: `K : h¹ → h²` is Lipschitz on the `h²` ball (derivative bounded by compactness) -/

/-- `DK` is uniformly bounded on the (compact closure of the) `h²` ball. -/
theorem exists_fderiv_Kfwd1_bound (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ballH1 R, ‖fderiv ℝ (B.Kfwd1 O) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closure_ballH1 R).exists_bound_of_continuousOn
    (f := fun x => B.Dfwd O x) ((B.continuous_Dfwd O).continuousOn)
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x (subset_closure hx)).trans (le_max_left _ _)⟩

/-- **W08.01.** `‖K(x) − K(y)‖_{h²} ≤ C_R ‖x − y‖_{h¹}` for `x, y` in the `h²` ball of radius `R`
(mean-value formula along segments of the convex ball). -/
theorem lipschitz_Kfwd1_ballH1 (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ballH1 R, ∀ y ∈ ballH1 R,
      ‖B.Kfwd1 O x - B.Kfwd1 O y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨C, hC0, hC⟩ := B.exists_fderiv_Kfwd1_bound O R
  exact ⟨C, hC0, fun x hx y hy =>
    (convex_ballH1 R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => B.differentiableAt_Kfwd1 O z) hC hy hx⟩

theorem continuous_Kfwd1 : Continuous (B.Kfwd1 O) :=
  continuous_iff_continuousAt.2 (fun x => (B.differentiableAt_Kfwd1 O x).continuousAt)

/-! ## W08.02: image bounded in `h²`; inverse Lipschitz estimate in `h¹` -/

/-- `K` is bounded in `h²` on the `h²` ball of radius `R` (continuous image of a compact set). -/
theorem exists_bound_Kfwd1 (R : ℝ) : ∃ M : ℝ, ∀ x ∈ ballH1 R, ‖B.Kfwd1 O x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closure_ballH1 R).exists_bound_of_continuousOn
    (f := B.Kfwd1 O) (B.continuous_Kfwd1 O).continuousOn
  exact ⟨M, fun x hx => hM x (subset_closure hx)⟩

include O in
/-- `T(x) = x + K(x)` maps the `h²` ball of radius `R` into the `h²` ball of radius `R + M`
(v2: "The image of the ball under `T` is bounded in `h²`"). -/
theorem TC1_mem_ballH1 {R M : ℝ} (hM : ∀ x ∈ ballH1 R, ‖B.Kfwd1 O x‖ ≤ M) {x : H1_38}
    (hx : x ∈ ballH1 R) : B.TC 1 x ∈ ballH1 (R + M) := by
  obtain ⟨y, hy, rfl⟩ := (mem_ballH1_iff R x).1 hx
  rw [mem_ballH1_iff]
  refine ⟨y + B.Kfwd1 O (i21_38 y), ?_, ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add hy (hM _ hx))
  · rw [B.TC1_eq O]; simp

/-- `DT⁻¹ : h¹ → h¹` is uniformly bounded on the compact closure of an `h²` ball; mean-value
formula on the convex `h²` ball. -/
theorem lipschitz_TinvC1_ballH1 (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a ∈ ballH1 R, ∀ b ∈ ballH1 R,
      ‖B.TinvC 1 a - B.TinvC 1 b‖ ≤ L * ‖a - b‖ := by
  have hcd : ContDiff ℝ 1 (B.TinvC 1) :=
    contDiff_iff_contDiffAt.2 (fun x => (B.analyticOnNhd_TinvC 1 x trivial).contDiffAt)
  have hcont : Continuous (fun x => fderiv ℝ (B.TinvC 1) x) := hcd.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closure_ballH1 R).exists_bound_of_continuousOn hcont.continuousOn
  have hdiff : ∀ z : H1_38, DifferentiableAt ℝ (B.TinvC 1) z :=
    fun z => (B.analyticOnNhd_TinvC 1 z trivial).differentiableAt
  refine ⟨max C 0, le_max_right _ _, fun a ha b hb => ?_⟩
  exact (convex_ballH1 R).norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
    (fun z hz => (hC z (subset_closure hz)).trans (le_max_left _ _)) hb ha

include O in
/-- **W08.02.** `‖x − y‖_{h¹} ≤ L_R ‖T x − T y‖_{h¹}` for `x, y` in the `h²` ball of radius `R`. -/
theorem inverse_lipschitz_ballH1 (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ ballH1 R, ∀ y ∈ ballH1 R,
      ‖x - y‖ ≤ L * ‖B.TC 1 x - B.TC 1 y‖ := by
  obtain ⟨M, hM⟩ := B.exists_bound_Kfwd1 O R
  obtain ⟨L, hL0, hL⟩ := B.lipschitz_TinvC1_ballH1 (R + M)
  refine ⟨L, hL0, fun x hx y hy => ?_⟩
  have h := hL _ (B.TC1_mem_ballH1 O hM hx) _ (B.TC1_mem_ballH1 O hM hy)
  rwa [B.TinvC_TC, B.TinvC_TC] at h

/-! ## W08.03 and W08.04: coinciding low outputs, the tail factor, injectivity -/

/-- **W08.03.** If `x, y ∈ P_N h¹` and `P_N T x = P_N T y`, then
`T x − T y = (1 − P_N)(K x − K y)`, entirely a high tail. -/
theorem TC1_sub_eq_compl (N : ℕ) {x y : H1_38}
    (hx : projC38 ((1 : ℕ) : ℝ) N x = x) (hy : projC38 ((1 : ℕ) : ℝ) N y = y)
    (hxy : projC38 ((1 : ℕ) : ℝ) N (B.TC 1 x) = projC38 ((1 : ℕ) : ℝ) N (B.TC 1 y)) :
    B.TC 1 x - B.TC 1 y = compl38 ((1 : ℕ) : ℝ) N (i21_38 (B.Kfwd1 O x - B.Kfwd1 O y)) := by
  have h0 : projC38 ((1 : ℕ) : ℝ) N (B.TC 1 x - B.TC 1 y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h1 : B.TC 1 x - B.TC 1 y = compl38 ((1 : ℕ) : ℝ) N (B.TC 1 x - B.TC 1 y) := by
    rw [compl38_apply, h0, sub_zero]
  rw [h1, B.TC1_eq O]
  simp only [compl38_apply, map_sub, map_add, hx, hy]
  abel

include O in
/-- **W08.04 (injectivity at the level of `h¹`).** For every `R` there is `N₀` such that for
`N ≥ N₀`, two points of the `h²` ball of radius `R` lying in `P_N h¹` with the same low output
`P_N T` coincide. -/
theorem injOn_projTC1_ballH1 (R : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ ballH1 R, ∀ y ∈ ballH1 R,
      projC38 ((1 : ℕ) : ℝ) N x = x → projC38 ((1 : ℕ) : ℝ) N y = y →
      projC38 ((1 : ℕ) : ℝ) N (B.TC 1 x) = projC38 ((1 : ℕ) : ℝ) N (B.TC 1 y) → x = y := by
  obtain ⟨C, hC0, hC⟩ := B.lipschitz_Kfwd1_ballH1 O R
  obtain ⟨L, hL0, hL⟩ := B.inverse_lipschitz_ballH1 O R
  have hev : ∀ᶠ N : ℕ in atTop, L * C * tailFactor38 N < 1 := by
    have h := (tendsto_tailFactor38.const_mul (L * C))
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds one_pos) |>.mono (fun N hN => by simpa [mul_assoc] using hN)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN x hx y hy hPx hPy hxy => ?_⟩
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h1 := hL x hx y hy
  rw [B.TC1_sub_eq_compl O N hPx hPy hxy] at h1
  have h2 := norm_compl_i21_le_W08 N (B.Kfwd1 O x - B.Kfwd1 O y)
  have h3 := hC x hx y hy
  have h4 : ‖x - y‖ ≤ L * (tailFactor38 N * (C * ‖x - y‖)) :=
    h1.trans (mul_le_mul_of_nonneg_left (h2.trans
      (mul_le_mul_of_nonneg_left h3 (tailFactor38_nonneg N))) hL0)
  have h5 := hN₀ N hN
  nlinarith [h4, h5, hpos]

end BirkhoffInput38

end NlsGge.Birkhoff
