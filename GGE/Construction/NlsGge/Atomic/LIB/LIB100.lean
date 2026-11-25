import Mathlib
                                                                                                                                                                                                                                                               
                                           

/-! LIB-100 helper steps (no placeholders). Source: Pro LIB-100 (STATEMENTS/LIB.md) plan:
identity principle along real discs, then a two-variable argument. -/

open Metric Filter Topology Set

namespace NlsGge.Atomic.LIB100

lemma mem_ball_of_real {R : ℝ} {t : ℝ} (h : |t| < R) : (t : ℂ) ∈ ball (0 : ℂ) R := by
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
  exact h

/-- One complex variable: a function holomorphic on a disc that vanishes on a real interval
around `0` vanishes on the whole disc. -/
lemma oneVar_zero_of_real {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    {φ : ℂ → G} {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hφ : DifferentiableOn ℂ φ (ball (0 : ℂ) R))
    (hreal : ∀ t : ℝ, |t| < δ → φ (t : ℂ) = 0) :
    ∀ z ∈ ball (0 : ℂ) R, φ z = 0 := by
  have hA : AnalyticOnNhd ℂ φ (ball (0 : ℂ) R) := hφ.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), φ z = 0 := by
    have hT : Tendsto (fun n : ℕ => (((δ / 2) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop
        (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h1 : Tendsto (fun n : ℕ => (δ / 2) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
          simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (δ / 2)
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        rw [Complex.ofReal_zero] at h2
        exact h2
      · refine Eventually.of_forall (fun n => ?_)
        simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
        have : (0 : ℝ) < (δ / 2) * (1 / ((n : ℝ) + 1)) := by positivity
        exact this.ne'
    refine hT.frequently ?_
    refine Eventually.frequently (Eventually.of_forall (fun n => ?_))
    apply hreal
    have hpos : (0 : ℝ) < (δ / 2) * (1 / ((n : ℝ) + 1)) := by positivity
    have hle : (δ / 2) * (1 / ((n : ℝ) + 1)) ≤ δ / 2 := by
      have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith
    rw [abs_of_pos hpos]
    linarith
  intro z hz
  exact hA.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball _ _).isPreconnected
    (mem_ball_self hR) hfreq hz

/-- Two complex variables: a function holomorphic in each variable on the disc of radius `2`
that vanishes at all real points of the unit square vanishes on the disc. -/
lemma twoVar_zero_of_real {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    {F : ℂ → ℂ → G}
    (hd1 : ∀ z2 ∈ ball (0 : ℂ) 2, DifferentiableOn ℂ (fun z1 => F z1 z2) (ball (0 : ℂ) 2))
    (hd2 : ∀ z1 ∈ ball (0 : ℂ) 2, DifferentiableOn ℂ (fun z2 => F z1 z2) (ball (0 : ℂ) 2))
    (hreal : ∀ t1 t2 : ℝ, |t1| < 1 → |t2| < 1 → F (t1 : ℂ) (t2 : ℂ) = 0) :
    ∀ z1 ∈ ball (0 : ℂ) 2, ∀ z2 ∈ ball (0 : ℂ) 2, F z1 z2 = 0 := by
  have step1 : ∀ t2 : ℝ, |t2| < 1 → ∀ z1 ∈ ball (0 : ℂ) 2, F z1 (t2 : ℂ) = 0 := by
    intro t2 ht2
    exact oneVar_zero_of_real (by norm_num) (by norm_num) (hd1 _ (mem_ball_of_real (by linarith)))
      (fun t1 ht1 => hreal t1 t2 ht1 ht2)
  intro z1 hz1 z2 hz2
  have step2 : ∀ z2' ∈ ball (0 : ℂ) 2, F z1 z2' = 0 := by
    intro z2' hz2'
    refine oneVar_zero_of_real (φ := fun w => F z1 w) (by norm_num) (by norm_num) (hd2 z1 hz1)
      (fun t hT => step1 t hT z1 hz1) z2' hz2'
  exact step2 z2 hz2


/-- LIB-100 (Pro statement): identity from the real Hilbert slice and connected propagation. -/
theorem analytic_eq_of_realSlice
    {H E F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (c : (H × H) ≃L[ℝ] E)
    (hc : ∀ x y : H, c (x, y) = c (x, 0) + Complex.I • c (y, 0))
    (a : H) (r : ℝ) (hr : 0 < r)
    (U : Set E) (hU : IsOpen U)
    (hreal : (fun x : H => c (x, 0)) '' ball a r ⊆ U)
    (f g : E → F) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (heq : ∀ x ∈ ball a r, f (c (x, 0)) = g (c (x, 0))) :
    (∀ x ∈ ball a r, ∀ᶠ z in 𝓝 (c (x, 0)), f z = g z) ∧
    (IsPreconnected U → EqOn f g U) := by
  have hlocal : ∀ x0 ∈ ball a r, ∀ᶠ z in 𝓝 (c (x0, 0)), f z = g z := by
    intro x0 hx0
    obtain ⟨p0, hp0⟩ : ∃ p0, p0 = c (x0, 0) := ⟨_, rfl⟩
    rw [← hp0]
    have hp0U : p0 ∈ U := by rw [hp0]; exact hreal ⟨x0, hx0, rfl⟩
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU p0 hp0U
    obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.1 isOpen_ball x0 hx0
    have hcs : Continuous c.symm := c.symm.continuous
    have h1 : Continuous (fun z => (c.symm z).1) := continuous_fst.comp hcs
    have h2 : Continuous (fun z => (c.symm z).2) := continuous_snd.comp hcs
    have hcontA : Continuous (fun z => ‖(c.symm z).1 - x0‖ + ‖(c.symm z).2‖) :=
      ((h1.sub continuous_const).norm).add h2.norm
    have hcontB : Continuous (fun z => ‖c ((c.symm z).1 - x0, 0)‖ + ‖c ((c.symm z).2, 0)‖) :=
      (((c.continuous.comp ((h1.sub continuous_const).prodMk continuous_const)).norm).add
        (c.continuous.comp (h2.prodMk continuous_const)).norm)
    have hA : ∀ᶠ z in 𝓝 p0, ‖(c.symm z).1 - x0‖ + ‖(c.symm z).2‖ < η := by
      have := hcontA.continuousAt (x := p0)
      refine this.eventually_lt continuousAt_const ?_
      rw [hp0]
      simp [hη]
    have hB : ∀ᶠ z in 𝓝 p0, ‖c ((c.symm z).1 - x0, 0)‖ + ‖c ((c.symm z).2, 0)‖ < ρ / 4 := by
      have := hcontB.continuousAt (x := p0)
      refine this.eventually_lt continuousAt_const ?_
      rw [hp0]
      simp [hρ, Prod.mk_zero_zero, map_zero]
    filter_upwards [hA, hB] with z hAz hBz
    obtain ⟨x, y, hxy⟩ : ∃ x y : H, c.symm z = (x, y) := ⟨_, _, rfl⟩
    have hz : c (x, y) = z := by rw [← hxy]; exact c.apply_symm_apply z
    rw [hxy] at hAz hBz
    simp only at hAz hBz
    obtain ⟨Δ1, hΔ1⟩ : ∃ D : E, c (x - x0, 0) = D := ⟨_, rfl⟩
    obtain ⟨Δ2, hΔ2⟩ : ∃ D : E, c (y, 0) = D := ⟨_, rfl⟩
    rw [hΔ1, hΔ2] at hBz
    have hp0Δ1 : p0 + Δ1 = c (x, 0) := by
      rw [← hΔ1, hp0, ← map_add]
      congr 1
      ext <;> simp
    have hdiff : ∀ ζ1 ∈ ball (0 : ℂ) 2, ∀ ζ2 ∈ ball (0 : ℂ) 2,
        p0 + ζ1 • Δ1 + ζ2 • Δ2 ∈ ball p0 ρ := by
      intro ζ1 h1' ζ2 h2'
      rw [mem_ball_zero_iff] at h1' h2'
      rw [mem_ball, dist_eq_norm]
      have e : p0 + ζ1 • Δ1 + ζ2 • Δ2 - p0 = ζ1 • Δ1 + ζ2 • Δ2 := by abel
      rw [e]
      have k := norm_add_le (ζ1 • Δ1) (ζ2 • Δ2)
      rw [norm_smul, norm_smul] at k
      have k1 := mul_le_mul_of_nonneg_right h1'.le (norm_nonneg Δ1)
      have k2 := mul_le_mul_of_nonneg_right h2'.le (norm_nonneg Δ2)
      linarith
    have hmapsU : ∀ ζ1 ∈ ball (0 : ℂ) 2, ∀ ζ2 ∈ ball (0 : ℂ) 2,
        p0 + ζ1 • Δ1 + ζ2 • Δ2 ∈ U := fun ζ1 h1' ζ2 h2' => hρU (hdiff ζ1 h1' ζ2 h2')
    have hfU : DifferentiableOn ℂ (fun w => f w - g w) U :=
      hf.differentiableOn.sub hg.differentiableOn
    have hd1 : ∀ z2 ∈ ball (0 : ℂ) 2,
        DifferentiableOn ℂ (fun z1 => f (p0 + z1 • Δ1 + z2 • Δ2) - g (p0 + z1 • Δ1 + z2 • Δ2))
          (ball (0 : ℂ) 2) := by
      intro z2 hz2
      have haff : DifferentiableOn ℂ (fun z1 : ℂ => p0 + z1 • Δ1 + z2 • Δ2) (ball (0 : ℂ) 2) :=
        (by fun_prop : Differentiable ℂ (fun z1 : ℂ => p0 + z1 • Δ1 + z2 • Δ2)).differentiableOn
      exact hfU.comp haff (fun z1 hz1 => hmapsU z1 hz1 z2 hz2)
    have hd2 : ∀ z1 ∈ ball (0 : ℂ) 2,
        DifferentiableOn ℂ (fun z2 => f (p0 + z1 • Δ1 + z2 • Δ2) - g (p0 + z1 • Δ1 + z2 • Δ2))
          (ball (0 : ℂ) 2) := by
      intro z1 hz1
      have haff : DifferentiableOn ℂ (fun z2 : ℂ => p0 + z1 • Δ1 + z2 • Δ2) (ball (0 : ℂ) 2) :=
        (by fun_prop : Differentiable ℂ (fun z2 : ℂ => p0 + z1 • Δ1 + z2 • Δ2)).differentiableOn
      exact hfU.comp haff (fun z2 hz2 => hmapsU z1 hz1 z2 hz2)
    have hreal' : ∀ t1 t2 : ℝ, |t1| < 1 → |t2| < 1 →
        f (p0 + (t1 : ℂ) • Δ1 + (t2 : ℂ) • Δ2) - g (p0 + (t1 : ℂ) • Δ1 + (t2 : ℂ) • Δ2) = 0 := by
      intro t1 t2 ht1 ht2
      have hq : x0 + t1 • (x - x0) + t2 • y ∈ ball x0 η := by
        rw [mem_ball, dist_eq_norm]
        have e : x0 + t1 • (x - x0) + t2 • y - x0 = t1 • (x - x0) + t2 • y := by abel
        rw [e]
        have k := norm_add_le (t1 • (x - x0)) (t2 • y)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at k
        have k1 := mul_le_mul_of_nonneg_right ht1.le (norm_nonneg (x - x0))
        have k2 := mul_le_mul_of_nonneg_right ht2.le (norm_nonneg y)
        linarith
      have hqball : x0 + t1 • (x - x0) + t2 • y ∈ ball a r := hηball hq
      have hcq : c (x0 + t1 • (x - x0) + t2 • y, 0) = p0 + (t1 : ℂ) • Δ1 + (t2 : ℂ) • Δ2 := by
        have e : (x0 + t1 • (x - x0) + t2 • y, (0 : H)) =
            (x0, (0 : H)) + t1 • (x - x0, (0 : H)) + t2 • (y, (0 : H)) := by
          ext <;> simp
        rw [e, map_add, map_add, map_smul, map_smul, ← hp0, hΔ1, hΔ2,
          RCLike.real_smul_eq_coe_smul (K := ℂ) t1 Δ1, RCLike.real_smul_eq_coe_smul (K := ℂ) t2 Δ2]
        rfl
      rw [← hcq, heq _ hqball, sub_self]
    have hzero := twoVar_zero_of_real
      (F := fun z1 z2 => f (p0 + z1 • Δ1 + z2 • Δ2) - g (p0 + z1 • Δ1 + z2 • Δ2))
      hd1 hd2 hreal' 1 (mem_ball_zero_iff.2 (by norm_num)) Complex.I
      (mem_ball_zero_iff.2 (by simp))
    have hfin : p0 + (1 : ℂ) • Δ1 + Complex.I • Δ2 = z := by
      rw [one_smul, hp0Δ1, ← hΔ2, ← hc x y]
      exact hz
    rw [hfin] at hzero
    exact sub_eq_zero.1 hzero
  refine ⟨hlocal, fun hpre => ?_⟩
  have hac : c (a, 0) ∈ U := hreal ⟨a, mem_ball_self hr, rfl⟩
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hpre hac (hlocal a (mem_ball_self hr))

end NlsGge.Atomic.LIB100

