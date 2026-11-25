import QuantumNLS.RootSpectralInputsDischarge

/-! Full-mass version of the frozen scalar rectangle nonvanishing argument.
Source provenance: RootSpectralInputsDischarge sections Cut and Gamma.
Probability normalization is replaced by the actual finite mass bound m;
the phase Lipschitz constant is L/2 + κ m/δ². -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
open QuantumNLS.SpatialTransfer QuantumNLS.EmpiricalRapidity QuantumNLS.ResolventNeighborhood QuantumNLS.NonvanishingD
namespace QuantumNLS.Q07FiniteGeometryR16
open RootSpectralInputsDischarge (im_phase' im_phase_ge norm_sin_sq sinh_le_norm_sin
  norm_Dsrc yzero slow dlow dlow_pos)

variable {L κ : ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem norm_ge_of_gap {δ c q : ℝ} {z : ℂ} (hz : z.re = c) (h : δ ≤ |q - c|) : δ ≤ ‖z - (q : ℂ)‖ := by
  have h2 := Complex.abs_re_le_norm (z - (q : ℂ))
  have h3 : (z - (q : ℂ)).re = c - q := by simp [hz]
  rw [h3] at h2
  rw [abs_sub_comm] at h
  linarith

theorem integrable_inv_gap {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|) {z : ℂ} (hz : z.re = c) :
    Integrable (fun q : ℝ => (z - (q : ℂ))⁻¹) μ := by
  refine Integrable.mono' (integrable_const (δ⁻¹)) ?_ ?_
  · exact (measurable_const.sub Complex.measurable_ofReal).inv.aestronglyMeasurable
  · filter_upwards [hg] with q hq
    rw [norm_inv]
    exact inv_anti₀ hδ (norm_ge_of_gap hz hq)

theorem cauchy_lip (m : ℝ) (hm : μ.real univ ≤ m) {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|) (y : ℝ) :
    ‖cauchyTransform μ ((c : ℂ) + (y : ℂ) * Complex.I) - cauchyTransform μ (c : ℂ)‖ ≤ |y| / δ ^ 2 * m := by
  have hz : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
  have hz0 : ((c : ℂ)).re = c := by simp
  unfold cauchyTransform
  rw [← integral_sub (integrable_inv_gap hδ hg hz) (integrable_inv_gap hδ hg hz0)]
  have hb : ∀ᵐ (q : ℝ) ∂μ, ‖((c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ))⁻¹ - ((c : ℂ) - (q : ℂ))⁻¹‖ ≤ |y| / δ ^ 2 := by
    filter_upwards [hg] with q hq
    have h1 := norm_ge_of_gap hz hq
    have h2 := norm_ge_of_gap hz0 hq
    have hb0 : ((c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ)) ≠ 0 := by
      intro h; rw [h, norm_zero] at h1; linarith
    have ha0 : ((c : ℂ) - (q : ℂ)) ≠ 0 := by
      intro h; rw [h, norm_zero] at h2; linarith
    rw [inv_sub_inv hb0 ha0, norm_div, norm_mul]
    have hnum : ‖((c : ℂ) - (q : ℂ)) - ((c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ))‖ = |y| := by
      have : ((c : ℂ) - (q : ℂ)) - ((c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ)) = -((y : ℂ) * Complex.I) := by ring
      rw [this, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [hnum]
    have hd : δ ^ 2 ≤ ‖(c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ)‖ * ‖(c : ℂ) - (q : ℂ)‖ := by
      rw [sq]; exact mul_le_mul h1 h2 hδ.le (norm_nonneg _)
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hd
  calc _ ≤ |y| / δ ^ 2 * μ.real (univ : Set ℝ) := norm_integral_le_of_norm_le_const hb
    _ ≤ |y| / δ ^ 2 * m := mul_le_mul_of_nonneg_left hm (by positivity)

theorem im_cauchy_cut {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|) :
    (cauchyTransform μ (c : ℂ)).im = 0 := by
  have hint := integrable_inv_gap hδ hg (z := (c : ℂ)) (by simp)
  unfold cauchyTransform
  have := Complex.imCLM.integral_comp_comm hint
  simp only [Complex.imCLM_apply] at this
  rw [← this]
  have h0 : ∀ q : ℝ, (((c : ℂ) - (q : ℂ))⁻¹).im = 0 := fun q => by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_inv]; exact Complex.ofReal_im _
  simp [h0]

theorem phase_lip (m : ℝ) (hm : μ.real univ ≤ m) (hκ : 0 < κ) (hL : 0 ≤ L) {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|) (y : ℝ) :
    ‖boundaryPhase L κ μ ((c : ℂ) + (y : ℂ) * Complex.I) - boundaryPhase L κ μ (c : ℂ)‖ ≤
      |y| * (L / 2 + κ * m / δ ^ 2) := by
  have e : boundaryPhase L κ μ ((c : ℂ) + (y : ℂ) * Complex.I) - boundaryPhase L κ μ (c : ℂ) =
      (L : ℂ) * ((y : ℂ) * Complex.I) / 2 -
        (κ : ℂ) * (cauchyTransform μ ((c : ℂ) + (y : ℂ) * Complex.I) - cauchyTransform μ (c : ℂ)) := by
    unfold boundaryPhase; ring
  rw [e]
  have h1 : ‖(L : ℂ) * ((y : ℂ) * Complex.I) / 2‖ = L * |y| / 2 := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL]
    simp
  have h2 : ‖(κ : ℂ) * (cauchyTransform μ ((c : ℂ) + (y : ℂ) * Complex.I) - cauchyTransform μ (c : ℂ))‖ ≤
      κ * (|y| / δ ^ 2 * m) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
    exact mul_le_mul_of_nonneg_left (cauchy_lip m hm hδ hg y) hκ.le
  calc _ ≤ ‖(L : ℂ) * ((y : ℂ) * Complex.I) / 2‖ + ‖(κ : ℂ) * (cauchyTransform μ ((c : ℂ) + (y : ℂ) * Complex.I) -
          cauchyTransform μ (c : ℂ))‖ := norm_sub_le _ _
    _ ≤ L * |y| / 2 + κ * (|y| / δ ^ 2 * m) := by rw [h1]; linarith
    _ = |y| * (L / 2 + κ * m / δ ^ 2) := by ring

/-- **Lower bound for `|sin γ|` near a gapped cut.**  If the support of `μ` has distance `≥ δ` from `c`, `2 cos γ = Δ` on the upper half-plane for a continuous `Δ`,
and `‖Δ(c)‖ ≤ 1/2`, then `|sin γ(c+iy)| ≥ 1/2` for `|y| (L/2 + κ/δ²) ≤ 1/4`. -/
theorem sin_lower_cut (m : ℝ) (hm : μ.real univ ≤ m) (hκ : 0 < κ) (hL : 0 ≤ L) {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|)
    {Δ : ℂ → ℂ} (hΔ : Continuous Δ)
    (hcos : ∀ z : ℂ, 0 < z.im → 2 * Complex.cos (boundaryPhase L κ μ z) = Δ z)
    (hΔc : ‖Δ (c : ℂ)‖ ≤ 1 / 2) {y : ℝ} (hy : |y| * (L / 2 + κ * m / δ ^ 2) ≤ 1 / 4) :
    1 / 2 ≤ ‖Complex.sin (boundaryPhase L κ μ ((c : ℂ) + (y : ℂ) * Complex.I))‖ := by
  set g := boundaryPhase L κ μ (c : ℂ) with hg_def
  have hgim : g.im = 0 := by
    rw [hg_def, im_phase', im_cauchy_cut hδ hg]; simp
  have hlim1 : Tendsto (fun t : ℝ => boundaryPhase L κ μ ((c : ℂ) + (t : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 g) := by
    have hC : Tendsto (fun t : ℝ => |t| * (L / 2 + κ * m / δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => |t| * (L / 2 + κ * m / δ ^ 2)) (𝓝 0) (𝓝 (|(0 : ℝ)| * (L / 2 + κ * m / δ ^ 2))) :=
        (continuous_abs.mul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ => norm_nonneg _) (fun t => phase_lip m hm hκ hL hδ hg t) hC)
  have hlim2 : Tendsto (fun t : ℝ => 2 * Complex.cos (boundaryPhase L κ μ ((c : ℂ) + (t : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 (2 * Complex.cos g)) :=
    ((continuous_const.mul Complex.continuous_cos).continuousAt.tendsto).comp hlim1
  have hlim3 : Tendsto (fun t : ℝ => Δ ((c : ℂ) + (t : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 (Δ (c : ℂ))) := by
    have hc : Continuous fun t : ℝ => ((c : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have := (hΔ.comp hc).tendsto 0
    simpa [Function.comp_def] using this.mono_left nhdsWithin_le_nhds
  have hcg : 2 * Complex.cos g = Δ (c : ℂ) :=
    tendsto_nhds_unique_of_eventuallyEq hlim2 hlim3 (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hcos _ (by simpa using ht))
  have hnorm : ‖Complex.cos g‖ ≤ 1 / 4 := by
    have : ‖Complex.cos g‖ = ‖Δ (c : ℂ)‖ / 2 := by
      rw [← hcg, norm_mul]; simp
    linarith
  have hgre : g = (g.re : ℂ) := Complex.ext (by simp) (by simp [hgim])
  have hcosθ : |Real.cos g.re| ≤ 1 / 4 := by
    have : Complex.cos g = ((Real.cos g.re : ℝ) : ℂ) := by
      conv_lhs => rw [hgre]
      exact (Complex.ofReal_cos _).symm
    rw [this, Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact hnorm
  have hsinθ : 3 / 4 ≤ |Real.sin g.re| := by
    by_contra hlt
    push Not at hlt
    have h1 := Real.sin_sq_add_cos_sq g.re
    have h2 : Real.cos g.re ^ 2 ≤ 1 / 16 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hcosθ 2
      rw [sq_abs] at this
      linarith
    have h3 : Real.sin g.re ^ 2 < 9 / 16 := by
      have := pow_lt_pow_left₀ hlt (abs_nonneg _) (two_ne_zero)
      rw [sq_abs] at this
      linarith
    linarith
  set z : ℂ := (c : ℂ) + (y : ℂ) * Complex.I with hz
  have hre : |(boundaryPhase L κ μ z).re - g.re| ≤ 1 / 4 := by
    have h1 := Complex.abs_re_le_norm (boundaryPhase L κ μ z - g)
    have h2 : (boundaryPhase L κ μ z - g).re = (boundaryPhase L κ μ z).re - g.re := by simp
    rw [h2] at h1
    exact le_trans h1 (le_trans (phase_lip m hm hκ hL hδ hg y) hy)
  have hsx : 1 / 2 ≤ |Real.sin (boundaryPhase L κ μ z).re| := by
    have h1 := Real.abs_sin_sub_sin_le (boundaryPhase L κ μ z).re g.re
    have h5 := abs_sub_abs_le_abs_sub (Real.sin g.re) (Real.sin (boundaryPhase L κ μ z).re)
    rw [abs_sub_comm] at h5
    linarith
  have hsq : (1 / 2 : ℝ) ^ 2 ≤ ‖Complex.sin (boundaryPhase L κ μ z)‖ ^ 2 := by
    rw [norm_sin_sq]
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hsx 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (Real.sinh (boundaryPhase L κ μ z).im)]
  exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) two_ne_zero).1 hsq


theorem norm_Dsrc_lower (m : ℝ) (hM : 0 < m) (hm : μ.real univ ≤ m) (hκ : 0 < κ) (hL : 0 < L) {δ a h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hga : ∀ᵐ q ∂μ, δ ≤ |q - a|) (hgb : ∀ᵐ q ∂μ, δ ≤ |q - (-a)|)
    {Δ : ℂ → ℂ} (hΔ : Continuous Δ)
    (hcos : ∀ z : ℂ, 0 < z.im → 2 * Complex.cos (boundaryPhase L κ μ z) = Δ z)
    (hΔa : ‖Δ (a : ℂ)‖ ≤ 1 / 2) (hΔb : ‖Δ ((-a : ℝ) : ℂ)‖ ≤ 1 / 2)
    {w : ℂ} (hw : w ∈ GammaN a h) : dlow L (κ*m) δ h ≤ ‖Dsrc κ L μ w‖ := by
  have hCc : 0 < L / 2 + κ / δ ^ 2 := by positivity
  have hy0 : 0 < yzero L (κ*m) δ := by unfold yzero; positivity
  have near : ∀ c : ℝ, (∀ᵐ q ∂μ, δ ≤ |q - c|) → ‖Δ (c : ℂ)‖ ≤ 1 / 2 → w.re = c →
      |w.im| * (L / 2 + κ * m / δ ^ 2) ≤ 1 / 4 →
      1 / 2 ≤ ‖Complex.sin (boundaryPhase L κ μ w)‖ := by
    intro c hg hΔc hre hy
    have hwe : w = (c : ℂ) + (w.im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
    have := sin_lower_cut m hm hκ hL.le hδ hg hΔ hcos hΔc hy
    rwa [← hwe] at this
  have far : yzero L (κ*m) δ < |w.im| → slow L (κ*m) δ h ≤ ‖Complex.sin (boundaryPhase L κ μ w)‖ := by
    intro hyz
    have hne : w.im ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hyz; linarith
    have h1 := im_phase_ge μ hκ hL.le hne
    refine le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) ?_
    refine sinh_le_norm_sin (by positivity) (le_trans ?_ h1)
    nlinarith
  have hs : slow L (κ*m) δ h ≤ ‖Complex.sin (boundaryPhase L κ μ w)‖ ∧ |w.im| ≤ h := by
    simp only [GammaN, Set.mem_union, Set.mem_ofPred_eq] at hw
    rcases hw with ⟨hre, him⟩ | ⟨him, hre⟩
    · refine ⟨?_, him⟩
      by_cases hn : |w.im| * (L / 2 + κ * m / δ ^ 2) ≤ 1 / 4
      · refine le_trans (min_le_left _ _) ?_
        rcases hre with hre | hre
        · exact near a hga hΔa hre hn
        · exact near (-a) hgb hΔb hre hn
      · apply far
        push Not at hn
        unfold yzero
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
    · have habs : |w.im| = h := by
        rcases him with him | him
        · rw [him, abs_of_pos hh]
        · rw [him, abs_neg, abs_of_pos hh]
      have hne : w.im ≠ 0 := by
        intro h0; rw [h0, abs_zero] at habs; linarith
      have h1 := im_phase_ge μ hκ hL.le hne
      refine ⟨?_, habs.le⟩
      refine le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) ?_
      refine sinh_le_norm_sin (by positivity) (le_trans ?_ h1)
      rw [habs]
  obtain ⟨hs1, hs2⟩ := hs
  rw [norm_Dsrc]
  unfold dlow
  have he : Real.exp (-(L * h) / 2) ≤ Real.exp (-(L * w.im) / 2) := by
    apply Real.exp_le_exp.2
    have : w.im ≤ h := le_trans (le_abs_self _) hs2
    nlinarith
  have hs0 : 0 ≤ slow L (κ*m) δ h := by
    unfold slow
    refine le_min (by norm_num) (le_min ?_ ?_)
    · exact Real.sinh_nonneg_iff.2 (by positivity)
    · exact Real.sinh_nonneg_iff.2 (by positivity)
  exact mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hs1 hs0 (by positivity)

end QuantumNLS.Q07FiniteGeometryR16
