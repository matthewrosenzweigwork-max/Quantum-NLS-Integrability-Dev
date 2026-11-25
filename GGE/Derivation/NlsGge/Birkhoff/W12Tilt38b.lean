import NlsGge.Birkhoff.W12Tilt38

/-! # W12 (`D:prop:tilt`), part 2 (Birkhoff-free): the tilted Gaussian has density
`D_δ exp(δ ∑ b_n |z_n|²)` relative to `γ_W`

v2 l.1856-1859: "The Gaussian with rates `a_n - δ b_n` has density `D_δ exp(δ ∑_n b_n |z_n|²)`
relative to `γ_W`; its normalization follows by independence and monotone convergence, since
`∑ b_n/a_n < ∞`."

Route: both sides are measures on `ℤ → ℂ`; by `Measure.eq_infinitePi` it suffices to compare them on
measurable boxes `∏_{n∈s} t_n`.  For a box, monotone convergence along `Λ_N = [-N,N]` reduces to the
finite independence computation (single-site Gaussian integral `∫ 1_t e^{b|y|²} dγ_a = a/(a-b) γ_{a-b}(t)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights Filter Topology
open scoped ENNReal Real

section SingleSite

/-- Single-site tilt: `∫ 1_t(y) e^{b|y|²} dγ_a(y) = a/(a-b) · γ_{a-b}(t)` for `b < a`. -/
theorem integral_indicator_exp_complexGaussian38 (a b : ℝ) (ha : 0 < a) (hba : b < a)
    (t : Set ℂ) (ht : MeasurableSet t) :
    Integrable (fun y : ℂ => t.indicator (fun _ => (1 : ℝ)) y * Real.exp (b * ‖y‖ ^ 2))
      (complexGaussian a) ∧
    ∫ y : ℂ, t.indicator (fun _ => (1 : ℝ)) y * Real.exp (b * ‖y‖ ^ 2) ∂(complexGaussian a) =
      a / (a - b) * (complexGaussian (a - b)).real t := by
  have hab : 0 < a - b := by linarith
  have hm : Measurable (fun y : ℂ => ENNReal.ofReal ((a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2))) := by
    fun_prop
  have hm' : Measurable (fun y : ℂ => ENNReal.ofReal
      (((a - b) / Real.pi) * Real.exp (-(a - b) * ‖y‖ ^ 2))) := by fun_prop
  have hpos : ∀ y : ℂ, 0 ≤ (a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2) := fun y =>
    mul_nonneg (div_nonneg ha.le Real.pi_pos.le) (Real.exp_pos _).le
  have hpos' : ∀ y : ℂ, 0 ≤ ((a - b) / Real.pi) * Real.exp (-(a - b) * ‖y‖ ^ 2) := fun y =>
    mul_nonneg (div_nonneg hab.le Real.pi_pos.le) (Real.exp_pos _).le
  have hconv : ∀ y : ℂ, (a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2) * Real.exp (b * ‖y‖ ^ 2) =
      (a / (a - b)) * (((a - b) / Real.pi) * Real.exp (-(a - b) * ‖y‖ ^ 2)) := fun y => by
    have h1 : Real.exp (-a * ‖y‖ ^ 2) * Real.exp (b * ‖y‖ ^ 2) =
        Real.exp (-(a - b) * ‖y‖ ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2) * Real.exp (b * ‖y‖ ^ 2)
        = (a / Real.pi) * (Real.exp (-a * ‖y‖ ^ 2) * Real.exp (b * ‖y‖ ^ 2)) := by ring
      _ = (a / Real.pi) * Real.exp (-(a - b) * ‖y‖ ^ 2) := by rw [h1]
      _ = _ := by field_simp
  have hind : Measurable (fun y : ℂ => t.indicator (fun _ => (1 : ℝ)) y) :=
    measurable_const.indicator ht
  refine ⟨?_, ?_⟩
  · refine (integrable_exp_complexGaussian38 a b ha hba).1.mono'
      (hind.mul (by fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have : |t.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
      by_cases hy : y ∈ t
      · simp [hy]
      · simp [hy]
    calc |t.indicator (fun _ => (1 : ℝ)) y| * Real.exp (b * ‖y‖ ^ 2)
        ≤ 1 * Real.exp (b * ‖y‖ ^ 2) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = _ := one_mul _
  · rw [complexGaussian_density a ha,
      integral_withDensity_eq_integral_toReal_smul hm (Filter.Eventually.of_forall
        (fun _ => ENNReal.ofReal_lt_top))]
    have h2 : (complexGaussian (a - b)).real t =
        ∫ y : ℂ, t.indicator (fun _ => (1 : ℝ)) y ∂(complexGaussian (a - b)) := by
      rw [← integral_indicator_one ht]
      rfl
    rw [h2, complexGaussian_density (a - b) hab,
      integral_withDensity_eq_integral_toReal_smul hm' (Filter.Eventually.of_forall
        (fun _ => ENNReal.ofReal_lt_top)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hpos y), ENNReal.toReal_ofReal (hpos' y)]
    calc (a / Real.pi * Real.exp (-a * ‖y‖ ^ 2)) *
          (t.indicator (fun _ => (1 : ℝ)) y * Real.exp (b * ‖y‖ ^ 2))
        = t.indicator (fun _ => (1 : ℝ)) y *
          ((a / Real.pi * Real.exp (-a * ‖y‖ ^ 2)) * Real.exp (b * ‖y‖ ^ 2)) := by ring
      _ = t.indicator (fun _ => (1 : ℝ)) y * ((a / (a - b)) *
          (((a - b) / Real.pi) * Real.exp (-(a - b) * ‖y‖ ^ 2))) := by rw [hconv]
      _ = _ := by ring

end SingleSite

section FiniteProduct

variable {lower upper : ℝ}

/-- **Independence (finitely many coordinates, general factors).** For measurable nonnegative
factors `g_n`, integrable against the single-site Gaussians,
`E_{γ_W} ∏_{n∈s} g_n(z_n) = ∏_{n∈s} E_{γ_{a_n}} g_n`. -/
theorem lintegral_prod_finset38 (c : BoundedCoefficients lower upper) (s : Finset ℤ)
    (g : ℤ → ℂ → ℝ) (hgm : ∀ n, Measurable (g n)) (hg0 : ∀ n y, 0 ≤ g n y)
    (hgi : ∀ n, Integrable (g n) (complexGaussian (fullWeightRate c.val n))) :
    ∫⁻ z, ENNReal.ofReal (∏ n ∈ s, g n (z n)) ∂(fullWeightSequenceGaussian c.val) =
      ENNReal.ofReal (∏ n ∈ s, ∫ y, g n y ∂(complexGaussian (fullWeightRate c.val n))) := by
  set G : (s → ℂ) → ℝ := fun y => ∏ i : s, g i (y i) with hG
  have hGm : Measurable G := by
    refine Finset.measurable_prod _ (fun i _ => ?_)
    exact (hgm i).comp (measurable_pi_apply i)
  have hGc : ∀ z : ℤ → ℂ, ∏ n ∈ s, g n (z n) = G (s.restrict z) := by
    intro z
    simp only [hG, Finset.restrict]
    rw [← Finset.prod_coe_sort s]
  simp_rw [hGc]
  have hlm := lintegral_map (μ := fullWeightSequenceGaussian c.val)
    (f := fun y => ENNReal.ofReal (G y)) (ENNReal.measurable_ofReal.comp hGm)
    (Finset.measurable_restrict s)
  rw [← hlm]
  have hmap : (fullWeightSequenceGaussian c.val).map s.restrict = Measure.pi (fun i : s =>
      complexGaussian (fullWeightRate c.val i)) := gammaΛ38_eq_map c.val s
  rw [hmap]
  have hint : Integrable G (Measure.pi (fun i : s => complexGaussian (fullWeightRate c.val i))) :=
    Integrable.fintype_prod (fun i : s => hgi (i : ℤ))
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall
    (fun y => Finset.prod_nonneg (fun i _ => hg0 _ _)))]
  congr 1
  rw [hG, integral_fintype_prod_eq_prod
    (μ := fun i : s => complexGaussian (fullWeightRate c.val i))
    (fun (i : s) (y : ℂ) => g i y)]
  rw [← Finset.prod_coe_sort s]

/-- **Box computation (finite stage).** For a finite stage `Λ ⊇ s` and measurable `t_n`,
`E_{γ_W}[1_{∏_s t_n} · e^{δ ∑_{n∈Λ} b_n|z_n|²}] = ∏_{n∈Λ} a_n/ã_n · ∏_{n∈s} γ_{ã_n}(t_n)`. -/
theorem lintegral_box_tilt_finset38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (Λ s : Finset ℤ) (hs : s ⊆ Λ) (t : ℤ → Set ℂ)
    (ht : ∀ n, MeasurableSet (t n)) :
    ∫⁻ z, (Set.pi (↑s : Set ℤ) t).indicator (fun z : ℤ → ℂ => ENNReal.ofReal
        (Real.exp (δ * ∑ n ∈ Λ, bRate38 c.val n * ‖z n‖ ^ 2))) z ∂(fullWeightSequenceGaussian c.val) =
      ENNReal.ofReal (∏ n ∈ Λ, fullWeightRate c.val n /
        fullWeightRate (tiltCoef38 c.val δ) n) *
        ∏ n ∈ s, complexGaussian (fullWeightRate (tiltCoef38 c.val δ) n) (t n) := by
  classical
  have ha := fullWeightRate_pos38 c
  have hrate : ∀ n, fullWeightRate (tiltCoef38 c.val δ) n =
      fullWeightRate c.val n - δ * bRate38 c.val n := fullWeightRate_tilt38 c δ
  have hta : ∀ n, 0 < fullWeightRate (tiltCoef38 c.val δ) n := fun n =>
    fullWeightRate_pos (lower - δ * upper) upper _ (tiltCoef38_bounds c hδ0 hδ).1
      (fun j => ((tiltCoef38_bounds c hδ0 hδ).2.2 j).1)
      (fun j => ((tiltCoef38_bounds c hδ0 hδ).2.2 j).2) n
  have hlt : ∀ n, δ * bRate38 c.val n < fullWeightRate c.val n := fun n => by
    have := hta n; rw [hrate n] at this; linarith
  set t' : ℤ → Set ℂ := fun n => if n ∈ s then t n else Set.univ with ht'
  have ht'm : ∀ n, MeasurableSet (t' n) := fun n => by
    simp only [ht']; split_ifs
    · exact ht n
    · exact MeasurableSet.univ
  set g : ℤ → ℂ → ℝ := fun n y =>
    (t' n).indicator (fun _ => (1 : ℝ)) y * Real.exp (δ * bRate38 c.val n * ‖y‖ ^ 2) with hg
  have hgm : ∀ n, Measurable (g n) := fun n =>
    (measurable_const.indicator (ht'm n)).mul (by fun_prop)
  have hg0 : ∀ n y, 0 ≤ g n y := fun n y => by
    simp only [hg]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Real.exp_pos _).le
  have hsite := fun n => integral_indicator_exp_complexGaussian38 (fullWeightRate c.val n)
    (δ * bRate38 c.val n) (ha n) (hlt n) (t' n) (ht'm n)
  have hgi : ∀ n, Integrable (g n) (complexGaussian (fullWeightRate c.val n)) :=
    fun n => (hsite n).1
  have hpt : ∀ z : ℤ → ℂ, ENNReal.ofReal (∏ n ∈ Λ, g n (z n)) =
      (Set.pi (↑s : Set ℤ) t).indicator (fun z : ℤ → ℂ => ENNReal.ofReal
        (Real.exp (δ * ∑ n ∈ Λ, bRate38 c.val n * ‖z n‖ ^ 2))) z := by
    intro z
    by_cases hz : z ∈ Set.pi (↑s : Set ℤ) t
    · rw [Set.indicator_of_mem hz]
      congr 1
      have h1 : ∀ n ∈ Λ, g n (z n) = Real.exp (δ * bRate38 c.val n * ‖z n‖ ^ 2) := by
        intro n hn
        have : z n ∈ t' n := by
          simp only [ht']
          split_ifs with h
          · exact hz n (by exact_mod_cast h)
          · exact Set.mem_univ _
        simp only [hg, Set.indicator_of_mem this, one_mul]
      rw [Finset.prod_congr rfl h1, ← Real.exp_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun n _ => by ring)
    · rw [Set.indicator_of_notMem hz]
      have : ∃ n ∈ s, z n ∉ t n := by
        by_contra hcon
        push Not at hcon
        exact hz (fun n hn => hcon n (by exact_mod_cast hn))
      obtain ⟨n, hn, hzn⟩ := this
      have hzero : g n (z n) = 0 := by
        have : z n ∉ t' n := by simp only [ht', hn, ite_true]; exact hzn
        simp only [hg, Set.indicator_of_notMem this, zero_mul]
      rw [Finset.prod_eq_zero (hs hn) hzero, ENNReal.ofReal_zero]
  simp_rw [← hpt]
  rw [lintegral_prod_finset38 c Λ g hgm hg0 hgi]
  -- evaluate the single-site integrals
  have hval : ∀ n, ∫ y, g n y ∂(complexGaussian (fullWeightRate c.val n)) =
      fullWeightRate c.val n / fullWeightRate (tiltCoef38 c.val δ) n *
        (complexGaussian (fullWeightRate (tiltCoef38 c.val δ) n)).real (t' n) := by
    intro n
    rw [(hsite n).2, hrate n]
  rw [Finset.prod_congr rfl (fun n _ => hval n), Finset.prod_mul_distrib]
  have hreal : ∏ n ∈ Λ, (complexGaussian (fullWeightRate (tiltCoef38 c.val δ) n)).real (t' n) =
      ∏ n ∈ s, (complexGaussian (fullWeightRate (tiltCoef38 c.val δ) n)).real (t n) := by
    rw [← Finset.prod_subset hs (fun n _ hn => by
      simp only [ht', hn, ite_false]
      exact probReal_univ)]
    refine Finset.prod_congr rfl (fun n hn => ?_)
    simp only [ht', hn, ite_true]
  rw [hreal, ENNReal.ofReal_mul (Finset.prod_nonneg (fun n _ =>
    div_nonneg (ha n).le (hta n).le))]
  congr 1
  rw [ENNReal.ofReal_prod_of_nonneg (fun n _ => measureReal_nonneg)]
  refine Finset.prod_congr rfl (fun n _ => ?_)
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end FiniteProduct

/-! ### The density identity -/

section Density

variable {lower upper : ℝ}

/-- `∑_n b_n |z_n|²`, totalized by `toReal` of the nonnegative extended sum (junk `0` if infinite,
which happens only on a `γ_W`-null set, see `ae_summable_bRate38`). -/
def bEnergy38 (c : ℕ → ℝ) (z : ℤ → ℂ) : ℝ := (sequenceEnergy (bRate38 c) z).toReal

theorem measurable_bEnergy38 (c : ℕ → ℝ) : Measurable (bEnergy38 c) :=
  (measurable_sequenceEnergy _).ennreal_toReal

theorem bEnergy38_nonneg (c : ℕ → ℝ) (z : ℤ → ℂ) : 0 ≤ bEnergy38 c z := ENNReal.toReal_nonneg

theorem bEnergy38_eq_tsum (c : BoundedCoefficients lower upper) {z : ℤ → ℂ}
    (hz : Summable (fun n : ℤ => bRate38 c.val n * ‖z n‖ ^ 2)) :
    bEnergy38 c.val z = ∑' n : ℤ, bRate38 c.val n * ‖z n‖ ^ 2 := by
  unfold bEnergy38 sequenceEnergy
  have h0 := fun n => mul_nonneg (bRate38_nonneg c n) (sq_nonneg (‖z n‖))
  rw [← ENNReal.ofReal_tsum_of_nonneg h0 hz, ENNReal.toReal_ofReal (tsum_nonneg h0)]

/-- `∑ b_n |z_n|² < ∞` `γ_W`-almost surely (`∑ b_n/a_n < ∞`). -/
theorem ae_summable_bRate38 (c : BoundedCoefficients lower upper) :
    ∀ᵐ z ∂(fullWeightSequenceGaussian c.val),
      Summable (fun n : ℤ => bRate38 c.val n * ‖z n‖ ^ 2) :=
  ae_sequenceSummable (fullWeightRate c.val) (bRate38 c.val) (fullWeightRate_pos38 c)
    (bRate38_nonneg c) (summable_bRate_div38 c)

/-- **v2 l.1856-1859.** The Gaussian with rates `ã_n = a_n - δ b_n` (the product of proper complex
Gaussians, `γ_W̃`) has density `D_δ · exp(δ ∑ b_n |z_n|²)` relative to `γ_W`. -/
theorem gaussian_tilt_density38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) :
    fullWeightSequenceGaussian (tiltCoef38 c.val δ) =
      (fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal (Dtilt38 c.val δ * Real.exp (δ * bEnergy38 c.val z))) := by
  classical
  obtain ⟨hDpos, -⟩ := hasProd_tilt38 c hδ0 hδ
  set D := Dtilt38 c.val δ with hD
  have ha := fullWeightRate_pos38 c
  have hta : ∀ n, 0 < fullWeightRate (tiltCoef38 c.val δ) n := fun n =>
    fullWeightRate_pos (lower - δ * upper) upper _ (tiltCoef38_bounds c hδ0 hδ).1
      (fun j => ((tiltCoef38_bounds c hδ0 hδ).2.2 j).1)
      (fun j => ((tiltCoef38_bounds c hδ0 hδ).2.2 j).2) n
  symm
  unfold fullWeightSequenceGaussian countableComplexGaussian
  refine Measure.eq_infinitePi (fun n : ℤ => complexGaussian
    (fullWeightRate (tiltCoef38 c.val δ) n)) (fun s t ht => ?_)
  set box : Set (ℤ → ℂ) := Set.pi (↑s : Set ℤ) t with hbox
  have hboxm : MeasurableSet box := MeasurableSet.pi (Set.to_countable _) (fun n _ => ht n)
  set P : ℝ≥0∞ := ∏ n ∈ s, complexGaussian (fullWeightRate (tiltCoef38 c.val δ) n) (t n) with hP
  set Ex : ℕ → (ℤ → ℂ) → ℝ≥0∞ := fun N => box.indicator (fun z : ℤ → ℂ => ENNReal.ofReal
        (Real.exp (δ * ∑ n ∈ stdExh38 N, bRate38 c.val n * ‖z n‖ ^ 2))) with hEx
  have hExm : ∀ N, Measurable (Ex N) := fun N => by
    refine Measurable.indicator ?_ hboxm
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact (Finset.measurable_sum _ (fun n _ =>
      ((measurable_pi_apply n).norm.pow_const 2).const_mul _)).const_mul _
  have hExmono : ∀ z, Monotone (fun N => Ex N z) := by
    intro z N M hNM
    by_cases hz : z ∈ box
    · simp only [hEx, Set.indicator_of_mem hz]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      refine mul_le_mul_of_nonneg_left ?_ hδ0.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (isExhaustion_stdExh38.mono hNM)
        (fun n _ _ => mul_nonneg (bRate38_nonneg c n) (sq_nonneg _))
    · simp only [hEx, Set.indicator_of_notMem hz]; exact le_rfl
  have hExlim : ∀ᵐ z ∂(fullWeightSequenceGaussian c.val), Tendsto (fun N => Ex N z) atTop
      (𝓝 (box.indicator (fun z : ℤ → ℂ => ENNReal.ofReal
        (Real.exp (δ * bEnergy38 c.val z))) z)) := by
    filter_upwards [ae_summable_bRate38 c] with z hz
    by_cases hzb : z ∈ box
    · simp only [hEx, Set.indicator_of_mem hzb]
      have h1 : Tendsto (fun N : ℕ => ∑ n ∈ stdExh38 N, bRate38 c.val n * ‖z n‖ ^ 2) atTop
          (𝓝 (bEnergy38 c.val z)) := by
        rw [bEnergy38_eq_tsum c hz]
        exact hz.hasSum.comp isExhaustion_stdExh38.tendsto_atTop
      exact (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp
        (h1.const_mul δ))
    · simp only [hEx, Set.indicator_of_notMem hzb]; exact tendsto_const_nhds
  have hT := lintegral_tendsto_of_tendsto_of_monotone (μ := fullWeightSequenceGaussian c.val)
    (fun N => (hExm N).aemeasurable) (Filter.Eventually.of_forall hExmono) hExlim
  -- the value of the finite stages
  have hstage : ∀ᶠ N in atTop, ∫⁻ z, Ex N z ∂(fullWeightSequenceGaussian c.val) =
      ENNReal.ofReal ((∏ n ∈ stdExh38 N, (1 - tiltRatio38 c.val δ n))⁻¹) * P := by
    have hev : ∀ᶠ N in atTop, s ⊆ stdExh38 N := by
      have := (Filter.eventually_all_finset s).2 (fun n _ => isExhaustion_stdExh38.eventually_mem n)
      filter_upwards [this] with N hN n hn using hN n hn
    filter_upwards [hev] with N hN
    have := lintegral_box_tilt_finset38 c hδ0 hδ (stdExh38 N) s hN t ht
    rw [hEx]
    simp only
    rw [this, hP]
    congr 2
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun n _ => ?_)
    rw [one_sub_tiltRatio38, inv_div]
  have hlim2 : Tendsto (fun N => ∫⁻ z, Ex N z ∂(fullWeightSequenceGaussian c.val)) atTop
      (𝓝 (ENNReal.ofReal D⁻¹ * P)) := by
    have h1 := tendsto_prod_tilt38 c hδ0 hδ
    have h2 : Tendsto (fun N => ENNReal.ofReal ((∏ n ∈ stdExh38 N, (1 - tiltRatio38 c.val δ n))⁻¹))
        atTop (𝓝 (ENNReal.ofReal D⁻¹)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (h1.inv₀ hDpos.ne')
    have h3 : Tendsto (fun N => ENNReal.ofReal ((∏ n ∈ stdExh38 N,
        (1 - tiltRatio38 c.val δ n))⁻¹) * P) atTop (𝓝 (ENNReal.ofReal D⁻¹ * P)) :=
      ENNReal.Tendsto.mul_const h2 (Or.inr (by
        rw [hP]
        refine ENNReal.prod_ne_top (fun n _ => measure_ne_top _ _)))
    exact h3.congr' (hstage.mono (fun N hN => hN.symm))
  have hint : ∫⁻ z, box.indicator (fun z : ℤ → ℂ => ENNReal.ofReal
      (Real.exp (δ * bEnergy38 c.val z))) z ∂(fullWeightSequenceGaussian c.val) =
      ENNReal.ofReal D⁻¹ * P := tendsto_nhds_unique hT hlim2
  rw [withDensity_apply _ hboxm, ← lintegral_indicator hboxm]
  have hf : ∀ z, box.indicator (fun z : ℤ → ℂ => ENNReal.ofReal
      (D * Real.exp (δ * bEnergy38 c.val z))) z =
      ENNReal.ofReal D * box.indicator (fun z : ℤ → ℂ => ENNReal.ofReal
        (Real.exp (δ * bEnergy38 c.val z))) z := by
    intro z
    by_cases hz : z ∈ box
    · simp only [Set.indicator_of_mem hz]
      rw [ENNReal.ofReal_mul hDpos.le]
    · simp only [Set.indicator_of_notMem hz, mul_zero]
  simp_rw [hf]
  have hint' : ∫⁻ z, box.indicator (fun z : ℤ → ℂ => ENNReal.ofReal
      (Real.exp (δ * bEnergy38 c.val z))) z ∂(Measure.infinitePi fun n : ℤ =>
        complexGaussian (fullWeightRate c.val n)) = ENNReal.ofReal D⁻¹ * P := hint
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hint', ← mul_assoc, ← ENNReal.ofReal_mul hDpos.le,
    mul_inv_cancel₀ hDpos.ne', ENNReal.ofReal_one, one_mul]

end Density


end NlsGge.Birkhoff
end
