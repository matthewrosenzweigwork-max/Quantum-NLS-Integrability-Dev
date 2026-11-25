import NlsGge.Measure.CountableGaussian
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic

/-! # F07 (v2 `C:lem:massmoment`), file a: the exact Gaussian density tilt (F07.03-F07.05)

Source: `paper/v2.tex` l.797-812 (`C:eq:GaussianTilt`).  Everything in this file is Phi-free (no
`BirkhoffInput38`).

Let `q`, `q'` be positive rate sequences on `ℤ` with `q' n ≤ q n` and a uniform margin
`ε q n ≤ q' n`, and put `c n = q n - q' n` (`c n = δ b_n` in v2).  Assume `Σ c n / q n < ∞`.
Then `d = ∏ q' n / q n` converges to a positive limit and the product complex Gaussian with rates
`q'` has density `d exp (Σ c n |z n|²)` with respect to the product complex Gaussian with rates `q`.
The proof is the one of v2: independence on finite cylinders and monotone convergence (no formal
infinite-product calculation of the exponential).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Measure Filter Topology
open scoped ENNReal

/-! ### One coordinate -/

/-- Single-coordinate tilt: `complexGaussian q` with density `(q'/q) e^{(q-q')|z|²}` is
`complexGaussian q'`. -/
theorem complexGaussian_tilt38 (q q' : ℝ) (hq' : 0 < q') (hle : q' ≤ q) :
    (complexGaussian q).withDensity
        (fun z : ℂ => ENNReal.ofReal (q' / q * Real.exp ((q - q') * ‖z‖ ^ 2))) =
      complexGaussian q' := by
  have hq : 0 < q := lt_of_lt_of_le hq' hle
  rw [complexGaussian_density q hq, complexGaussian_density q' hq',
    ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 : Real.exp (-q * ‖z‖ ^ 2) * Real.exp ((q - q') * ‖z‖ ^ 2) =
      Real.exp (-q' * ‖z‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc q / Real.pi * Real.exp (-q * ‖z‖ ^ 2) * (q' / q * Real.exp ((q - q') * ‖z‖ ^ 2))
      = q' / Real.pi * (Real.exp (-q * ‖z‖ ^ 2) * Real.exp ((q - q') * ‖z‖ ^ 2)) := by
        field_simp
    _ = q' / Real.pi * Real.exp (-q' * ‖z‖ ^ 2) := by rw [h1]

/-! ### Finite products of coordinate functions under the product Gaussian -/

theorem lintegral_prod_coord38 (q : ℤ → ℝ) (U : Finset ℤ) (h : ℤ → ℂ → ℝ≥0∞)
    (hh : ∀ n, Measurable (h n)) :
    ∫⁻ z : ℤ → ℂ, ∏ n ∈ U, h n (z n) ∂(countableComplexGaussian q) =
      ∏ n ∈ U, ∫⁻ x, h n x ∂(complexGaussian (q n)) := by
  have hind : ProbabilityTheory.iIndepFun (fun (n : ℤ) (z : ℤ → ℂ) => h n (z n))
      (countableComplexGaussian q) :=
    ProbabilityTheory.iIndepFun_infinitePi (P := fun n : ℤ => complexGaussian (q n))
      (X := fun n x => h n x) hh
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun U
    (fun n (z : ℤ → ℂ) => h n (z n)) hind (fun n => (hh n).comp (measurable_pi_apply n))]
  refine Finset.prod_congr rfl fun n _ => ?_
  have := (measurePreserving_eval_infinitePi (fun k : ℤ => complexGaussian (q k)) n).lintegral_comp
    (hh n)
  simpa [countableComplexGaussian] using this

/-! ### The box computation for the finite tilt -/

/-- The finite tilt factor in coordinate `n`. -/
def tiltFactor38 (q q' : ℤ → ℝ) (n : ℤ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (q' n / q n * Real.exp ((q n - q' n) * ‖x‖ ^ 2))

theorem measurable_tiltFactor38 (q q' : ℤ → ℝ) (n : ℤ) : Measurable (tiltFactor38 q q' n) := by
  unfold tiltFactor38; fun_prop

theorem tiltFactor_lintegral38 (q q' : ℤ → ℝ) (hq' : ∀ n, 0 < q' n) (hle : ∀ n, q' n ≤ q n)
    (n : ℤ) {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ x, A.indicator (tiltFactor38 q q' n) x ∂(complexGaussian (q n)) =
      complexGaussian (q' n) A := by
  rw [lintegral_indicator hA, ← withDensity_apply _ hA]
  have := complexGaussian_tilt38 (q n) (q' n) (hq' n) (hle n)
  unfold tiltFactor38
  rw [this]

theorem box_lintegral38 (q q' : ℤ → ℝ) (hq' : ∀ n, 0 < q' n) (hle : ∀ n, q' n ≤ q n)
    (s T : Finset ℤ) (hsT : s ⊆ T) (t : ℤ → Set ℂ) (ht : ∀ n, MeasurableSet (t n)) :
    ∫⁻ z : ℤ → ℂ, (Set.pi (s : Set ℤ) t).indicator
        (fun z => ∏ n ∈ T, tiltFactor38 q q' n (z n)) z ∂(countableComplexGaussian q) =
      ∏ n ∈ s, complexGaussian (q' n) (t n) := by
  classical
  set t' : ℤ → Set ℂ := fun n => if n ∈ s then t n else Set.univ with ht'
  have ht'm : ∀ n, MeasurableSet (t' n) := fun n => by
    simp only [ht']; split_ifs
    · exact ht n
    · exact MeasurableSet.univ
  have hpt : ∀ z : ℤ → ℂ, (Set.pi (s : Set ℤ) t).indicator
      (fun z => ∏ n ∈ T, tiltFactor38 q q' n (z n)) z =
      ∏ n ∈ T, (t' n).indicator (tiltFactor38 q q' n) (z n) := by
    intro z
    by_cases hz : z ∈ Set.pi (s : Set ℤ) t
    · rw [Set.indicator_of_mem hz]
      refine Finset.prod_congr rfl fun n _ => ?_
      rw [Set.indicator_of_mem]
      simp only [ht']
      split_ifs with hn
      · exact hz n (by exact_mod_cast hn)
      · trivial
    · rw [Set.indicator_of_notMem hz]
      have : ∃ n ∈ s, z n ∉ t n := by
        by_contra hcon
        push Not at hcon
        exact hz (fun n hn => hcon n (by exact_mod_cast hn))
      obtain ⟨n, hns, hnz⟩ := this
      symm
      refine Finset.prod_eq_zero (hsT hns) ?_
      rw [Set.indicator_of_notMem]
      simp only [ht', hns, ite_true]
      exact hnz
  simp_rw [hpt]
  rw [lintegral_prod_coord38 q T (fun n x => (t' n).indicator (tiltFactor38 q q' n) x)
    (fun n => (measurable_tiltFactor38 q q' n).indicator (ht'm n))]
  have hi : ∀ n, ∫⁻ x, (t' n).indicator (tiltFactor38 q q' n) x ∂(complexGaussian (q n)) =
      complexGaussian (q' n) (t' n) := fun n => tiltFactor_lintegral38 q q' hq' hle n (ht'm n)
  simp_rw [hi]
  have hsub : ∏ n ∈ s, complexGaussian (q' n) (t' n) = ∏ n ∈ T, complexGaussian (q' n) (t' n) := by
    refine Finset.prod_subset hsT ?_
    intro n _ hn
    simp only [ht', hn, ite_false]
    exact measure_univ
  rw [← hsub]
  refine Finset.prod_congr rfl fun n hn => ?_
  simp only [ht', hn, ite_true]

/-! ### The infinite product `d` -/

/-- Partial products over `[-M, M]` of a family with a product tend to its product. -/
theorem tendsto_Icc_neg_atTop38 : Tendsto (fun M : ℕ => Finset.Icc (-(M : ℤ)) M) atTop atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun n => ?_)
  · exact Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hab)
  · refine ⟨n.natAbs, ?_⟩
    simp only [Finset.mem_Icc]
    omega

theorem tendsto_prod_Icc38 {f : ℤ → ℝ} {d : ℝ} (hd : HasProd f d) :
    Tendsto (fun M : ℕ => ∏ n ∈ Finset.Icc (-(M : ℤ)) M, f n) atTop (𝓝 d) :=
  (by simpa [HasProd, SummationFilter.unconditional_filter] using hd :
    Tendsto (fun s : Finset ℤ => ∏ b ∈ s, f b) atTop (𝓝 d)).comp tendsto_Icc_neg_atTop38

/-- Positivity margin and summability of the relative deficits give a convergent product with a
positive limit (v2: `0 < d_δ < ∞`). -/
theorem hasProd_ratio38 (q q' : ℤ → ℝ) (hq' : ∀ n, 0 < q' n) (hle : ∀ n, q' n ≤ q n)
    (ε : ℝ) (hε : 0 < ε) (hmar : ∀ n, ε * q n ≤ q' n)
    (hsum : Summable (fun n : ℤ => (q n - q' n) / q n)) :
    ∃ d : ℝ, 0 < d ∧ HasProd (fun n : ℤ => q' n / q n) d := by
  have hq : ∀ n, 0 < q n := fun n => lt_of_lt_of_le (hq' n) (hle n)
  have hpos : ∀ n, 0 < q' n / q n := fun n => div_pos (hq' n) (hq n)
  have hlog : Summable (fun n : ℤ => Real.log (q' n / q n)) := by
    refine Summable.of_norm_bounded (hsum.mul_left (1 / ε)) (fun n => ?_)
    have hx : ε ≤ q' n / q n := by rw [le_div_iff₀ (hq n)]; linarith [hmar n]
    have hx1 : q' n / q n ≤ 1 := (div_le_one (hq n)).2 (hle n)
    have hlog_le : Real.log (q' n / q n) ≤ 0 := Real.log_nonpos (hpos n).le hx1
    rw [Real.norm_eq_abs, abs_of_nonpos hlog_le]
    have h1 : -Real.log (q' n / q n) ≤ (q n - q' n) / q n / (q' n / q n) := by
      have := Real.one_sub_inv_le_log_of_pos (hpos n)
      have e : (q n - q' n) / q n / (q' n / q n) = (q' n / q n)⁻¹ - 1 := by
        field_simp [(hq n).ne', (hq' n).ne']
      rw [e]
      have h2 : Real.log ((q' n / q n)⁻¹) = - Real.log (q' n / q n) := Real.log_inv _
      have h3 := Real.log_le_sub_one_of_pos (inv_pos.2 (hpos n))
      rw [h2] at h3
      exact h3
    refine h1.trans ?_
    have hnn : 0 ≤ (q n - q' n) / q n := div_nonneg (by linarith [hle n]) (hq n).le
    calc (q n - q' n) / q n / (q' n / q n) ≤ (q n - q' n) / q n / ε :=
          div_le_div_of_nonneg_left hnn hε hx
      _ = 1 / ε * ((q n - q' n) / q n) := by ring
  exact ⟨Real.exp (∑' n, Real.log (q' n / q n)), Real.exp_pos _,
    Real.hasProd_of_hasSum_log hpos hlog.hasSum⟩

theorem tendsto_sum_Icc38 {f : ℤ → ℝ} {a : ℝ} (h : HasSum f a) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc (-(M : ℤ)) M, f n) atTop (𝓝 a) :=
  (by simpa [HasSum, SummationFilter.unconditional_filter] using h :
    Tendsto (fun s : Finset ℤ => ∑ b ∈ s, f b) atTop (𝓝 a)).comp tendsto_Icc_neg_atTop38

/-! ### The tilt density and the exact density theorem -/

/-- `d exp (Σ_n c_n |z_n|²)`, with the nonnegative extended-real energy (finite a.s.). -/
def gaussTiltDensity38 (c : ℤ → ℝ) (d : ℝ) (z : ℤ → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal d * ENNReal.ofReal (Real.exp (sequenceEnergy c z).toReal)

theorem measurable_gaussTiltDensity38 (c : ℤ → ℝ) (d : ℝ) :
    Measurable (gaussTiltDensity38 c d) := by
  unfold gaussTiltDensity38
  exact (measurable_const.mul
    (Real.measurable_exp.comp (measurable_sequenceEnergy c).ennreal_toReal).ennreal_ofReal)

theorem gaussTiltDensity_eq38 (c : ℤ → ℝ) (hc : ∀ n, 0 ≤ c n) (d : ℝ) (z : ℤ → ℂ)
    (hz : Summable (fun n : ℤ => c n * ‖z n‖ ^ 2)) :
    gaussTiltDensity38 c d z =
      ENNReal.ofReal d * ENNReal.ofReal (Real.exp (∑' n : ℤ, c n * ‖z n‖ ^ 2)) := by
  unfold gaussTiltDensity38 sequenceEnergy
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hc n) (sq_nonneg _)) hz,
    ENNReal.toReal_ofReal (tsum_nonneg (fun n => mul_nonneg (hc n) (sq_nonneg _)))]

/-- **F07.05 (v2 `C:eq:GaussianTilt`).**  `dγ'/dγ = d exp (Σ c_n |z_n|²)` for the product complex
Gaussians with rates `q'`, `q`. -/
theorem countableGaussian_tilt38 (q q' : ℤ → ℝ) (hq' : ∀ n, 0 < q' n) (hle : ∀ n, q' n ≤ q n)
    (hsum : Summable (fun n : ℤ => (q n - q' n) / q n))
    (d : ℝ) (hd0 : 0 < d) (hd : HasProd (fun n : ℤ => q' n / q n) d) :
    countableComplexGaussian q' =
      (countableComplexGaussian q).withDensity (gaussTiltDensity38 (fun n => q n - q' n) d) := by
  classical
  have hq : ∀ n, 0 < q n := fun n => lt_of_lt_of_le (hq' n) (hle n)
  set c : ℤ → ℝ := fun n => q n - q' n with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => by simp only [hc]; linarith [hle n]
  set f : ℤ → ℝ := fun n => q' n / q n with hf
  have hfpos : ∀ n, 0 < f n := fun n => div_pos (hq' n) (hq n)
  set T : ℕ → Finset ℤ := fun M => Finset.Icc (-(M : ℤ)) M with hT
  have hTmono : Monotone T := fun a b hab =>
    Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hab)
  have hdM : Tendsto (fun M : ℕ => ∏ n ∈ T M, f n) atTop (𝓝 d) := tendsto_prod_Icc38 hd
  have hdMpos : ∀ M, 0 < ∏ n ∈ T M, f n := fun M => Finset.prod_pos fun n _ => hfpos n
  symm
  show _ = Measure.infinitePi (fun n : ℤ => complexGaussian (q' n))
  apply Measure.eq_infinitePi
  intro s t ht
  have hbox : MeasurableSet (Set.pi (s : Set ℤ) t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox]
  set P : ℝ≥0∞ := ∏ n ∈ s, complexGaussian (q' n) (t n) with hP
  set γ := countableComplexGaussian q with hγ
  set D : ℕ → ℝ := fun M => ∏ n ∈ T M, f n with hD
  have hDpos : ∀ M, 0 < D M := hdMpos
  let φ : ℕ → (ℤ → ℂ) → ℝ≥0∞ := fun M z =>
    ENNReal.ofReal d * ENNReal.ofReal (Real.exp (∑ n ∈ T M, c n * ‖z n‖ ^ 2))
  have hprodT : ∀ M (z : ℤ → ℂ), ∏ n ∈ T M, tiltFactor38 q q' n (z n) =
      ENNReal.ofReal (D M * Real.exp (∑ n ∈ T M, c n * ‖z n‖ ^ 2)) := by
    intro M z
    unfold tiltFactor38
    rw [← ENNReal.ofReal_prod_of_nonneg (fun n _ => mul_nonneg (hfpos n).le (Real.exp_pos _).le)]
    congr 1
    rw [Finset.prod_mul_distrib, Real.exp_sum]
  have hφ : ∀ M (z : ℤ → ℂ), φ M z =
      ENNReal.ofReal (d / D M) * ∏ n ∈ T M, tiltFactor38 q q' n (z n) := by
    intro M z
    rw [hprodT, ← ENNReal.ofReal_mul (div_nonneg hd0.le (hDpos M).le)]
    show ENNReal.ofReal d * _ = _
    rw [← ENNReal.ofReal_mul hd0.le]
    congr 1
    field_simp [(hDpos M).ne']
  have hmeasG : ∀ M, Measurable (fun z : ℤ → ℂ => ∏ n ∈ T M, tiltFactor38 q q' n (z n)) := fun M =>
    Finset.measurable_prod _ (fun n _ => (measurable_tiltFactor38 q q' n).comp (measurable_pi_apply n))
  have hA : ∀ M, s ⊆ T M →
      ∫⁻ z, (Set.pi (s : Set ℤ) t).indicator (φ M) z ∂γ = ENNReal.ofReal (d / D M) * P := by
    intro M hM
    have e : (Set.pi (s : Set ℤ) t).indicator (φ M) = fun z =>
        ENNReal.ofReal (d / D M) * (Set.pi (s : Set ℤ) t).indicator
          (fun z => ∏ n ∈ T M, tiltFactor38 q q' n (z n)) z := by
      funext z
      by_cases hz : z ∈ Set.pi (s : Set ℤ) t
      · simp only [Set.indicator_of_mem hz, hφ]
      · simp [Set.indicator_of_notMem hz]
    rw [e, lintegral_const_mul _ ((hmeasG M).indicator hbox), box_lintegral38 q q' hq' hle s (T M) hM t ht]
  have hsum' : Summable (fun n : ℤ => c n / q n) := hsum
  have hae : ∀ᵐ z ∂γ, Summable (fun n : ℤ => c n * ‖z n‖ ^ 2) :=
    ae_sequenceSummable q c hq hc0 hsum'
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (μ := γ) (f := fun M z => (Set.pi (s : Set ℤ) t).indicator (φ M) z)
    (F := (Set.pi (s : Set ℤ) t).indicator (gaussTiltDensity38 c d))
    (fun M => (((measurable_const.mul (Real.measurable_exp.comp
        (Finset.measurable_sum _ (fun n _ => (measurable_const.mul
          ((measurable_pi_apply n).norm.pow_const 2))))).ennreal_ofReal)).indicator hbox).aemeasurable)
    (Filter.Eventually.of_forall fun z a b hab => by
      by_cases hz : z ∈ Set.pi (s : Set ℤ) t
      · simp only [Set.indicator_of_mem hz, φ]
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) _
        exact Finset.sum_le_sum_of_subset_of_nonneg (hTmono hab)
          (fun n _ _ => mul_nonneg (hc0 n) (sq_nonneg _))
      · simp [Set.indicator_of_notMem hz])
    (by
      filter_upwards [hae] with z hz
      by_cases hzb : z ∈ Set.pi (s : Set ℤ) t
      · simp only [Set.indicator_of_mem hzb]
        rw [gaussTiltDensity_eq38 c hc0 d z hz]
        refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
        exact ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp
          (tendsto_sum_Icc38 hz.hasSum))
      · simp only [Set.indicator_of_notMem hzb]
        exact tendsto_const_nhds)
  have hlim2 : Tendsto (fun M : ℕ => ENNReal.ofReal (d / D M) * P) atTop (𝓝 P) := by
    have h1 : Tendsto (fun M : ℕ => d / D M) atTop (𝓝 (d / d)) :=
      tendsto_const_nhds.div hdM hd0.ne'
    rw [div_self hd0.ne'] at h1
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_one] at h2
    have := ENNReal.Tendsto.mul_const (b := P) h2 (Or.inl (one_ne_zero : (1 : ℝ≥0∞) ≠ 0))
    simpa using this
  have hev : ∀ᶠ M : ℕ in atTop, s ⊆ T M :=
    tendsto_Icc_neg_atTop38.eventually (eventually_ge_atTop s)
  refine tendsto_nhds_unique hlim ?_
  refine hlim2.congr' ?_
  filter_upwards [hev] with M hM
  exact (hA M hM).symm

/-- The tilted measure has total mass one: `∫ d exp(Σ c_n |z_n|²) dγ = 1` (v2: "this also verifies
that `C:eq:GaussianTilt` has total mass one"), in the extended-real form. -/
theorem lintegral_gaussTiltDensity38 (q q' : ℤ → ℝ) (hq' : ∀ n, 0 < q' n) (hle : ∀ n, q' n ≤ q n)
    (hsum : Summable (fun n : ℤ => (q n - q' n) / q n))
    (d : ℝ) (hd0 : 0 < d) (hd : HasProd (fun n : ℤ => q' n / q n) d) :
    ∫⁻ z, gaussTiltDensity38 (fun n => q n - q' n) d z ∂(countableComplexGaussian q) = 1 := by
  have h := countableGaussian_tilt38 q q' hq' hle hsum d hd0 hd
  have h1 := congrArg (fun μ : Measure (ℤ → ℂ) => μ Set.univ) h
  simp only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  exact h1.symm

end NlsGge.Birkhoff

end
