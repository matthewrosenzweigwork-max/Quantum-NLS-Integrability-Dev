import Mathlib

/-!
# Ramer Lemma 5.2, part (III): injectivity and surjectivity onto `B_{ε/2}`

Generic statements for `Φ : E → H` (to be used with `Φ = L` and `Φ = P ∘ L`).
-/

namespace NlsGge.Ramer

open Metric Set

section Generic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Fibre Lipschitz bound along `i`, by the mean value theorem on the segment. -/
theorem fibre_lipschitz (i : H →L[ℝ] E) (Φ : E → H) {ε : ℝ}
    (hd : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ Φ y)
    (hb : ∀ y ∈ closedBall (0 : E) ε, ‖(fderiv ℝ Φ y).comp i‖ ≤ 1 / 2)
    {x x' : E} (hx : x ∈ closedBall (0 : E) ε) (hx' : x' ∈ closedBall (0 : E) ε)
    {h : H} (hxh : x - x' = i h) : ‖Φ x - Φ x'‖ ≤ 1 / 2 * ‖h‖ := by
  set γ : ℝ → E := fun t => x' + t • i h with hγ
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ closedBall (0 : E) ε := by
    intro t ht
    have : γ t = (1 - t) • x' + t • x := by
      simp only [hγ, ← hxh, sub_smul, smul_sub, one_smul]; abel
    rw [this]
    exact (convex_closedBall (0 : E) ε) hx' hx (by linarith [ht.2]) ht.1 (by ring)
  have hγd : ∀ t, HasDerivAt γ (i h) t := by
    intro t
    simpa [hγ] using ((hasDerivAt_id t).smul_const (i h)).const_add x'
  have hdv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (Φ ∘ γ) ((fderiv ℝ Φ (γ t)) (i h)) (Icc (0 : ℝ) 1) t := by
    intro t ht
    exact (((hd _ (hmem t ht)).hasFDerivAt).comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := Φ ∘ γ) hdv
    (C := 1 / 2 * ‖h‖) (by
      intro t ht
      have := (fderiv ℝ Φ (γ t)).comp i |>.le_opNorm h
      calc ‖(fderiv ℝ Φ (γ t)) (i h)‖ = ‖((fderiv ℝ Φ (γ t)).comp i) h‖ := rfl
        _ ≤ ‖(fderiv ℝ Φ (γ t)).comp i‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 / 2 * ‖h‖ := by
          gcongr
          exact hb _ (hmem t (Ico_subset_Icc_self ht)))
  have h1 : γ 1 = x := by simp [hγ, ← hxh]
  have h0 : γ 0 = x' := by simp [hγ]
  simpa [Function.comp, h1, h0] using key

/-- Injectivity of `y ↦ y + i (Φ y)` on the closed ball. -/
theorem injOn_add_image (i : H →L[ℝ] E) (Φ : E → H) {ε : ℝ}
    (hd : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ Φ y)
    (hb : ∀ y ∈ closedBall (0 : E) ε, ‖(fderiv ℝ Φ y).comp i‖ ≤ 1 / 2) :
    InjOn (fun y => y + i (Φ y)) (closedBall (0 : E) ε) := by
  intro x hx x' hx' hS
  simp only at hS
  have hxh : x - x' = i (Φ x' - Φ x) := by
    rw [map_sub, sub_eq_sub_iff_add_eq_add, hS, add_comm]
  have := fibre_lipschitz i Φ hd hb hx hx' hxh
  have h2 : ‖Φ x - Φ x'‖ = ‖Φ x' - Φ x‖ := norm_sub_rev _ _
  have h3 : ‖Φ x - Φ x'‖ = 0 := by
    rw [h2] at this ⊢; rw [← h2] at this ⊢
    nlinarith [norm_nonneg (Φ x - Φ x')]
  have h4 : Φ x = Φ x' := sub_eq_zero.1 (norm_eq_zero.1 h3)
  rw [h4] at hS; exact add_right_cancel hS

/-- Continuity of `y ↦ y + i (Φ y)` on the closed ball. -/
theorem continuousOn_add_image (i : H →L[ℝ] E) (Φ : E → H) {ε : ℝ}
    (hd : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ Φ y) :
    ContinuousOn (fun y => y + i (Φ y)) (closedBall (0 : E) ε) := by
  intro y hy
  exact ((continuousAt_id).add (i.continuous.continuousAt.comp (hd y hy).continuousAt))
    |>.continuousWithinAt

variable [CompleteSpace H]

/-- Surjectivity of `y ↦ y + i (Φ y)` from the closed ball onto the open `ε/2`-ball,
by the Banach fixed point theorem on the fibre `{h | ‖z + i h‖ ≤ ε}`. -/
theorem exists_add_image_eq (i : H →L[ℝ] E) (Φ : E → H) {ε : ℝ} (hε : 0 < ε)
    (hd : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ Φ y)
    (hb : ∀ y ∈ closedBall (0 : E) ε, ‖(fderiv ℝ Φ y).comp i‖ ≤ 1 / 2)
    (hΦ : ∀ y ∈ closedBall (0 : E) ε, ‖i (Φ y)‖ < ε / 2)
    {z : E} (hz : ‖z‖ < ε / 2) :
    ∃ x ∈ closedBall (0 : E) ε, x + i (Φ x) = z := by
  set F : Set H := {h | ‖z + i h‖ ≤ ε} with hF
  have hFc : IsClosed F :=
    isClosed_le (by fun_prop) continuous_const
  have hmemB : ∀ h ∈ F, z + i h ∈ closedBall (0 : E) ε := by
    intro h hh
    have : ‖z + i h‖ ≤ ε := hh
    simpa [mem_closedBall, dist_zero_right] using this
  set G : H → H := fun h => -Φ (z + i h) with hG
  have hmaps : MapsTo G F F := by
    intro h hh
    show ‖z + i (-Φ (z + i h))‖ ≤ ε
    have := hΦ _ (hmemB h hh)
    calc ‖z + i (-Φ (z + i h))‖ ≤ ‖z‖ + ‖i (-Φ (z + i h))‖ := norm_add_le _ _
      _ = ‖z‖ + ‖i (Φ (z + i h))‖ := by rw [map_neg, norm_neg]
      _ ≤ ε := by linarith
  have hlip : ∀ h ∈ F, ∀ h' ∈ F, dist (G h) (G h') ≤ (1 / 2 : ℝ) * dist h h' := by
    intro h hh h' hh'
    have := fibre_lipschitz i Φ hd hb (hmemB h hh) (hmemB h' hh') (h := h - h')
      (by rw [map_sub]; abel)
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖G h - G h'‖ = ‖Φ (z + i h) - Φ (z + i h')‖ := by
          simp only [hG]; rw [← norm_neg]; congr 1; abel
      _ ≤ _ := this
  have hcw : ContractingWith (1 / 2 : NNReal) (hmaps.restrict G F F) := by
    refine ⟨by rw [show (1 / 2 : NNReal) = ⟨1/2, by norm_num⟩ from rfl]
                       ; exact_mod_cast (by norm_num : (1/2 : ℝ) < 1), ?_⟩
    refine LipschitzWith.of_dist_le_mul ?_
    intro a b
    simpa [Subtype.dist_eq] using hlip a a.2 b b.2
  have h0 : (0 : H) ∈ F := by simpa [hF] using hz.le.trans (by linarith : ε / 2 ≤ ε)
  obtain ⟨h, hhF, hfix, -⟩ := ContractingWith.exists_fixedPoint' hFc.isComplete hmaps hcw h0
    (edist_ne_top _ _)
  refine ⟨z + i h, hmemB h hhF, ?_⟩
  have : h = -Φ (z + i h) := hfix.symm
  have e := congrArg i this
  rw [map_neg] at e
  have e' : i (Φ (z + i h)) + i h = 0 := neg_eq_iff_add_eq_zero.1 e.symm
  rw [add_assoc, add_comm (i h), e', add_zero]

end Generic

section Lemma52

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Lemma 5.2 (III) for `S y = y + i (L y)` and `S_P y = y + i (P (L y))`.
`L` is only assumed differentiable at each point of the closed ball (continuity of
`fderiv` and the bound `c` are not needed here). -/
theorem lemma52 (i : H →L[ℝ] E) (P : H →L[ℝ] H) (hP : ‖P‖ ≤ 1) (L : E → H) {ε : ℝ}
    (hε : 0 < ε)
    (hd : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ L y)
    (ha : ∀ y ∈ closedBall (0 : E) ε, ‖i (L y)‖ < ε / 2)
    (ha' : ∀ y ∈ closedBall (0 : E) ε, ‖i (P (L y))‖ < ε / 2)
    (hb : ∀ y ∈ closedBall (0 : E) ε, ‖(fderiv ℝ L y).comp i‖ ≤ 1 / 2) :
    -- fibre Lipschitz
    (∀ x ∈ closedBall (0 : E) ε, ∀ x' ∈ closedBall (0 : E) ε, ∀ h : H, x - x' = i h →
        ‖L x - L x'‖ ≤ 1 / 2 * ‖h‖ ∧ ‖P (L x) - P (L x')‖ ≤ 1 / 2 * ‖h‖) ∧
    -- injectivity
    InjOn (fun y => y + i (L y)) (closedBall (0 : E) ε) ∧
    InjOn (fun y => y + i (P (L y))) (closedBall (0 : E) ε) ∧
    -- continuity
    ContinuousOn (fun y => y + i (L y)) (closedBall (0 : E) ε) ∧
    ContinuousOn (fun y => y + i (P (L y))) (closedBall (0 : E) ε) ∧
    -- surjectivity onto the open ε/2-ball
    (∀ z : E, ‖z‖ < ε / 2 → ∃ x ∈ closedBall (0 : E) ε, x + i (L x) = z) ∧
    (∀ z : E, ‖z‖ < ε / 2 → ∃ x ∈ closedBall (0 : E) ε, x + i (P (L x)) = z) := by
  have hdP : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ (fun y => P (L y)) y :=
    fun y hy => P.differentiableAt.comp y (hd y hy)
  have hbP : ∀ y ∈ closedBall (0 : E) ε,
      ‖(fderiv ℝ (fun y => P (L y)) y).comp i‖ ≤ 1 / 2 := by
    intro y hy
    have e : fderiv ℝ (fun y => P (L y)) y = P.comp (fderiv ℝ L y) := by
      have := P.hasFDerivAt.comp y (hd y hy).hasFDerivAt
      exact this.fderiv
    rw [e, ContinuousLinearMap.comp_assoc]
    calc ‖P.comp ((fderiv ℝ L y).comp i)‖ ≤ ‖P‖ * ‖(fderiv ℝ L y).comp i‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (1 / 2) := mul_le_mul hP (hb y hy) (norm_nonneg _) zero_le_one
      _ = 1 / 2 := one_mul _
  refine ⟨?_, injOn_add_image i L hd hb, injOn_add_image i (fun y => P (L y)) hdP hbP,
    continuousOn_add_image i L hd, continuousOn_add_image i (fun y => P (L y)) hdP,
    fun z hz => exists_add_image_eq i L hε hd hb ha hz,
    fun z hz => exists_add_image_eq i (fun y => P (L y)) hε hdP hbP ha' hz⟩
  intro x hx x' hx' h hxh
  exact ⟨fibre_lipschitz i L hd hb hx hx' hxh, fibre_lipschitz i (fun y => P (L y)) hdP hbP hx hx' hxh⟩

/-- Images contain the open `ε/2`-ball. -/
theorem ball_subset_image_S (i : H →L[ℝ] E) (L : E → H) {ε : ℝ} (hε : 0 < ε)
    (hd : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ L y)
    (ha : ∀ y ∈ closedBall (0 : E) ε, ‖i (L y)‖ < ε / 2)
    (hb : ∀ y ∈ closedBall (0 : E) ε, ‖(fderiv ℝ L y).comp i‖ ≤ 1 / 2) :
    ball (0 : E) (ε / 2) ⊆ (fun y => y + i (L y)) '' closedBall (0 : E) ε := by
  intro z hz
  obtain ⟨x, hx, hxz⟩ := exists_add_image_eq i L hε hd hb ha (by simpa using hz)
  exact ⟨x, hx, hxz⟩

end Lemma52

end NlsGge.Ramer
