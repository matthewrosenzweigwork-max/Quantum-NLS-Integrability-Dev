import Mathlib

set_option autoImplicit false

open Set Filter Topology Metric Complex MeasureTheory
open scoped Real

namespace NlsGge.G2037P5
noncomputable section

/-- A punctured ball is preconnected: four convex pieces chained through corner points. -/
theorem ballDiffZero_isPreconnected {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball (0 : ℂ) r \ {0}) := by
  have hball : ∀ a b : ℝ, |a| < r / 2 → |b| < r / 2 → (⟨a, b⟩ : ℂ) ∈ ball (0 : ℂ) r := by
    intro a b ha hb
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_lt (norm_le_abs_re_add_abs_im _) ?_
    show |a| + |b| < r
    linarith
  have hq : |r / 4| < r / 2 := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hqn : |-(r / 4)| < r / 2 := by
    rw [abs_neg]
    exact hq
  have hA1 : Convex ℝ (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) :=
    (convex_ball _ _).inter (convex_halfSpace_im_gt (r := 0))
  have hA2 : Convex ℝ (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.re}) :=
    (convex_ball _ _).inter (convex_halfSpace_re_gt (r := 0))
  have hA3 : Convex ℝ (ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) :=
    (convex_ball _ _).inter (convex_halfSpace_im_lt (r := 0))
  have hA4 : Convex ℝ (ball (0 : ℂ) r ∩ {z : ℂ | z.re < 0}) :=
    (convex_ball _ _).inter (convex_halfSpace_re_lt (r := 0))
  have p12 : (⟨r / 4, r / 4⟩ : ℂ) ∈
      (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∩ (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.re}) :=
    ⟨⟨hball _ _ hq hq, show (0 : ℝ) < r / 4 by linarith⟩,
      ⟨hball _ _ hq hq, show (0 : ℝ) < r / 4 by linarith⟩⟩
  have p23 : (⟨r / 4, -(r / 4)⟩ : ℂ) ∈
      (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.re}) ∩ (ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) :=
    ⟨⟨hball _ _ hq hqn, show (0 : ℝ) < r / 4 by linarith⟩,
      ⟨hball _ _ hq hqn, show -(r / 4) < (0 : ℝ) by linarith⟩⟩
  have p34 : (⟨-(r / 4), -(r / 4)⟩ : ℂ) ∈
      (ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∩ (ball (0 : ℂ) r ∩ {z : ℂ | z.re < 0}) :=
    ⟨⟨hball _ _ hqn hqn, show -(r / 4) < (0 : ℝ) by linarith⟩,
      ⟨hball _ _ hqn hqn, show -(r / 4) < (0 : ℝ) by linarith⟩⟩
  have h12 := IsPreconnected.union' ⟨_, p12⟩ hA1.isPreconnected hA2.isPreconnected
  have q23 : (⟨r / 4, -(r / 4)⟩ : ℂ) ∈
      (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im} ∪ ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.re}) ∩
        (ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) := ⟨Or.inr p23.1, p23.2⟩
  have q34 : (⟨-(r / 4), -(r / 4)⟩ : ℂ) ∈
      ((ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im} ∪ ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.re}) ∪
        ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∩ (ball (0 : ℂ) r ∩ {z : ℂ | z.re < 0}) :=
    ⟨Or.inr p34.1, p34.2⟩
  have h123 := IsPreconnected.union' ⟨_, q23⟩ h12 hA3.isPreconnected
  have h1234 := IsPreconnected.union' ⟨_, q34⟩ h123 hA4.isPreconnected
  have hEq : ball (0 : ℂ) r \ {0} =
      ((ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im} ∪ ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.re}
        ∪ ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∪ ball (0 : ℂ) r ∩ {z : ℂ | z.re < 0}) := by
    ext z
    constructor
    · rintro ⟨hz, hz0⟩
      have hz0' : ¬ (z.re = 0 ∧ z.im = 0) := fun h => hz0 (Complex.ext h.1 h.2)
      rcases lt_trichotomy z.im 0 with h1 | h1 | h1
      · exact Or.inl (Or.inr ⟨hz, h1⟩)
      · rcases lt_trichotomy z.re 0 with h2 | h2 | h2
        · exact Or.inr ⟨hz, h2⟩
        · exact absurd ⟨h2, h1⟩ hz0'
        · exact Or.inl (Or.inl (Or.inr ⟨hz, h2⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨hz, h1⟩))
    · intro hz
      have hz' : z ∈ ball (0 : ℂ) r := by
        rcases hz with ((h | h) | h) | h <;> exact h.1
      refine ⟨hz', ?_⟩
      intro h0
      rw [Set.mem_singleton_iff] at h0
      subst h0
      rcases hz with ((h | h) | h) | h <;> simp at h
  rw [hEq]
  exact h1234

/-- Circle integral of a derivative vanishes (fundamental theorem of calculus on a circle). -/
theorem circleIntegral_eq_zero_of_hasDerivAt {K k : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hK : ∀ w ∈ sphere c r, HasDerivAt K (k w) w) (hk : ContinuousOn k (sphere c r)) :
    (∮ z in C(c, r), k z) = 0 := by
  have hsph : ∀ θ : ℝ, circleMap c r θ ∈ sphere c r := fun θ => circleMap_mem_sphere c hr.le θ
  have hder : ∀ θ ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun θ : ℝ => K (circleMap c r θ))
        (k (circleMap c r θ) * (circleMap 0 r θ * I)) θ :=
    fun θ _ => HasDerivAt.comp θ (hK _ (hsph θ)) (hasDerivAt_circleMap c r θ)
  have hint : IntervalIntegrable
      (fun θ : ℝ => k (circleMap c r θ) * (circleMap 0 r θ * I)) volume 0 (2 * π) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · exact hk.comp (continuous_circleMap c r).continuousOn (fun θ _ => hsph θ)
    · exact ((continuous_circleMap 0 r).mul continuous_const).continuousOn
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have h2pi : circleMap c r (2 * π) = circleMap c r 0 := by
    simp [circleMap, Complex.exp_two_pi_mul_I]
  unfold circleIntegral
  have hcongr : ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap c r) θ • k (circleMap c r θ)
      = ∫ θ in (0 : ℝ)..2 * π, k (circleMap c r θ) * (circleMap 0 r θ * I) := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [(hasDerivAt_circleMap c r θ).deriv, smul_eq_mul]
    ring
  rw [hcongr, hfund]
  simp only [h2pi, sub_self]

/-- Core primitive expansion: a primitive of `-I * Q(1/z)` on an exterior, with `Q` analytic at
zero and `Q 0 = 1`, has the form `F z = -I*z + g(1/z)` with `g` analytic at zero. -/
theorem primitive_expansion_core (F Q : ℂ → ℂ) {R r0 : ℝ} (hR : 0 < R) (hr0 : 0 < r0)
    (hQ : DifferentiableOn ℂ Q (ball (0 : ℂ) r0)) (hQ0 : Q 0 = 1)
    (hF : ∀ z : ℂ, R < ‖z‖ → HasDerivAt F (-I * Q z⁻¹) z) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ z : ℂ, 1 / min r0 (1 / R) < ‖z‖ → F z = -I * z + g z⁻¹ := by
  set r1 : ℝ := min r0 (1 / R) with hr1def
  have hr1 : 0 < r1 := lt_min hr0 (one_div_pos.mpr hR)
  have hr1r0 : r1 ≤ r0 := min_le_left _ _
  have hr1R : r1 ≤ 1 / R := min_le_right _ _
  have hA : DifferentiableOn ℂ (fun z : ℂ => Q z - 1) (ball (0 : ℂ) r0) := hQ.sub_const 1
  have hA0 : (fun z : ℂ => Q z - 1) 0 = 0 := by simp [hQ0]
  -- derivative of the composed function on the punctured disc
  have hKder : ∀ w : ℂ, w ≠ 0 → ‖w‖ < r1 →
      HasDerivAt (fun y : ℂ => F y⁻¹ + I * y⁻¹) (I * ((w ^ 2)⁻¹ * (Q w - 1))) w := by
    intro w hw hwn
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hwR : R < ‖w⁻¹‖ := by
      rw [norm_inv, lt_inv_comm₀ hR hwpos]
      have h1 : ‖w‖ < R⁻¹ := by
        rw [← one_div]
        exact lt_of_lt_of_le hwn hr1R
      exact h1
    have hd1 := HasDerivAt.comp w (hF w⁻¹ hwR) (hasDerivAt_inv hw)
    have hd2 := (hasDerivAt_inv hw).const_mul I
    have hval : I * ((w ^ 2)⁻¹ * (Q w - 1))
        = (-I * Q w⁻¹⁻¹) * -(w ^ 2)⁻¹ + I * -(w ^ 2)⁻¹ := by
      rw [inv_inv]
      ring
    rw [hval]
    exact hd1.add hd2
  -- divided differences of A = Q - 1
  have hB : DifferentiableOn ℂ (dslope (fun z : ℂ => Q z - 1) 0) (ball (0 : ℂ) r0) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hr0))).mpr hA
  have hN0 : DifferentiableOn ℂ (dslope (dslope (fun z : ℂ => Q z - 1) 0) 0) (ball (0 : ℂ) r0) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hr0))).mpr hB
  obtain ⟨N, hNdef⟩ : ∃ N : ℂ → ℂ, N = dslope (dslope (fun z : ℂ => Q z - 1) 0) 0 :=
    ⟨_, rfl⟩
  have hN : DifferentiableOn ℂ N (ball (0 : ℂ) r0) := by
    rw [hNdef]
    exact hN0
  have hB0 : dslope (fun z : ℂ => Q z - 1) 0 0 = 0 := by
    rw [dslope_same]
    -- the derivative of Q - 1 at zero vanishes (Cauchy formula + single-valuedness)
    have hrpos : 0 < r1 / 2 := half_pos hr1
    have hrlt : r1 / 2 < r1 := half_lt_self hr1
    have hsub : closedBall (0 : ℂ) (r1 / 2) ⊆ ball (0 : ℂ) r0 :=
      closedBall_subset_ball (lt_of_lt_of_le hrlt hr1r0)
    have hAc : ContinuousOn (fun z : ℂ => Q z - 1) (sphere (0 : ℂ) (r1 / 2)) :=
      hA.continuousOn.mono (sphere_subset_closedBall.trans hsub)
    have hne : ∀ z ∈ sphere (0 : ℂ) (r1 / 2), z ≠ 0 := by
      intro z hz h0
      have hz' : ‖z‖ = r1 / 2 := mem_sphere_zero_iff_norm.mp hz
      rw [h0, norm_zero] at hz'
      linarith
    have hcont : ContinuousOn (fun z : ℂ => I * ((z ^ 2)⁻¹ * (Q z - 1)))
        (sphere (0 : ℂ) (r1 / 2)) :=
      continuousOn_const.mul
        (ContinuousOn.mul ((continuous_pow 2).continuousOn.inv₀
          (fun z hz => pow_ne_zero 2 (hne z hz))) hAc)
    have hk : (∮ z in C(0, r1 / 2), I * ((z ^ 2)⁻¹ * (Q z - 1))) = 0 := by
      refine circleIntegral_eq_zero_of_hasDerivAt (K := fun y : ℂ => F y⁻¹ + I * y⁻¹)
        (k := fun z : ℂ => I * ((z ^ 2)⁻¹ * (Q z - 1))) hrpos ?_ hcont
      intro w hw
      have hwn : ‖w‖ = r1 / 2 := mem_sphere_zero_iff_norm.mp hw
      exact hKder w (hne w hw) (by rw [hwn]; exact hrlt)
    rw [circleIntegral.integral_const_mul] at hk
    have hint0 : (∮ z in C(0, r1 / 2), (z ^ 2)⁻¹ * (Q z - 1)) = 0 :=
      (mul_eq_zero.mp hk).resolve_left Complex.I_ne_zero
    have hcauchy := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      (c := 0) (w₀ := 0) (R := r1 / 2) (f := fun z : ℂ => Q z - 1) isOpen_ball hsub hA
      (mem_ball_self hrpos)
    simp only [sub_zero, smul_eq_mul] at hcauchy
    rw [hint0, mul_zero] at hcauchy
    exact hcauchy.symm
  -- algebraic identity Q w - 1 = w^2 * N w off the origin
  have hkey : ∀ w : ℂ, w ∈ ball (0 : ℂ) r0 → w ≠ 0 → Q w - 1 = w ^ 2 * N w := by
    intro w _ hw
    have hBw : dslope (fun z : ℂ => Q z - 1) 0 w = (Q w - 1) / w := by
      rw [dslope_of_ne _ hw, slope_def_field]
      simp [hQ0]
    have hNw : N w = dslope (fun z : ℂ => Q z - 1) 0 w / w := by
      rw [hNdef, dslope_of_ne _ hw, slope_def_field, hB0]
      simp
    rw [hNw, hBw]
    field_simp
  -- primitive of N
  obtain ⟨P, hP⟩ := hN.isExactOn_ball
  have hPdiff : DifferentiableOn ℂ P (ball (0 : ℂ) r0) :=
    fun z hz => (hP z hz).differentiableAt.differentiableWithinAt
  set s : Set ℂ := ball (0 : ℂ) r1 \ {0} with hs
  have hsr0 : s ⊆ ball (0 : ℂ) r0 := fun z hz => ball_subset_ball hr1r0 hz.1
  have hDer : ∀ w ∈ s, HasDerivAt (fun y : ℂ => (F y⁻¹ + I * y⁻¹) - I * P y) 0 w := by
    intro w hw
    have hw0 : w ≠ 0 := hw.2
    have hwn : ‖w‖ < r1 := by simpa using hw.1
    have h1 := (hKder w hw0 hwn).sub ((hP w (hsr0 hw)).const_mul I)
    have hval : I * ((w ^ 2)⁻¹ * (Q w - 1)) - I * N w = 0 := by
      rw [hkey w (hsr0 hw) hw0, inv_mul_cancel_left₀ (pow_ne_zero 2 hw0), sub_self]
    rw [hval] at h1
    exact h1
  have hs_open : IsOpen s := isOpen_ball.sdiff isClosed_singleton
  have hs_conn : IsPreconnected s := ballDiffZero_isPreconnected hr1
  have hconst : ∀ w ∈ s, ∀ w' ∈ s,
      (F w⁻¹ + I * w⁻¹) - I * P w = (F w'⁻¹ + I * w'⁻¹) - I * P w' := by
    intro w hw w' hw'
    exact hs_open.is_const_of_deriv_eq_zero (f := fun y : ℂ => (F y⁻¹ + I * y⁻¹) - I * P y) hs_conn
      (fun z hz => (hDer z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hDer z hz).deriv) hw hw'
  have hw₀ : ((r1 / 2 : ℝ) : ℂ) ∈ s := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · rw [Set.mem_singleton_iff]
      exact Complex.ofReal_ne_zero.mpr (half_pos hr1).ne'
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ w ∈ s, (F w⁻¹ + I * w⁻¹) - I * P w = c :=
    ⟨_, fun w hw => hconst w hw _ hw₀⟩
  refine ⟨fun w => I * P w + c, ?_, ?_⟩
  · exact (analyticAt_const.mul
      (hPdiff.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr0)))).add analyticAt_const
  · intro z hz
    have hzp : 0 < ‖z‖ := lt_trans (one_div_pos.mpr hr1) hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp hzp
    have hwmem : z⁻¹ ∈ s := by
      refine ⟨?_, inv_ne_zero hz0⟩
      rw [mem_ball_zero_iff, norm_inv, inv_lt_comm₀ hzp hr1, ← one_div]
      exact hz
    have key := hc z⁻¹ hwmem
    rw [inv_inv] at key
    show F z = -I * z + (I * P z⁻¹ + c)
    linear_combination key

end

end NlsGge.G2037P5
