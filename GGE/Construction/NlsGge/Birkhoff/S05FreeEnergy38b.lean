import NlsGge.Measure.GibbsVariational38
import NlsGge.Measure.CountableGaussian
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # S05, part 2 (Φ-free): the rate-scaled actions `a_n |z_n|²` are independent exponential
random variables of mean one, and `∑_n a_n |z_n|² = ∞` almost surely

Source: `paper/v2.tex` l.480-486 ("under `γ_W` the variables `a_n|z_n|²` are independent exponential
random variables of mean one. Their sum is infinite almost surely, for example by the strong law
along `n = 1, 2, …`"), blueprint `S05.05`.

No `B` and no Birkhoff input.  The reference law is the project's `countableComplexGaussian q`
(`q n = a_n`, density `(a_n/π) e^{-a_n |z|²}` for the coordinate `z_n`, real-component variance
`1/(2 a_n)`).  The infinite sum is the nonnegative extended sum `∑' ofReal (a_n ‖z_n‖²)`.
-/

set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Function
open scoped ENNReal

namespace NlsGge.Measure

/-- Scaling of the proper complex Gaussian: `complexGaussian a` is the image of `complexGaussian 1`
under multiplication by `a^{-1/2}`. -/
lemma complexGaussian_eq_map_smul38 (a : ℝ) (ha : 0 < a) :
    complexGaussian a = (complexGaussian 1).map (fun z : ℂ => (Real.sqrt a)⁻¹ • z) := by
  set c : ℝ := (Real.sqrt a)⁻¹ with hc
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hvar : (NNReal.mk (c ^ 2) (sq_nonneg _)) * componentVariance 1 = componentVariance a := by
    apply NNReal.eq
    rw [NNReal.coe_mul, componentVariance_coe 1 one_pos, componentVariance_coe a ha]
    show c ^ 2 * (1 / (2 * 1)) = 1 / (2 * a)
    rw [hc, inv_pow, Real.sq_sqrt ha.le]
    field_simp
  have hp : ((gaussianReal 0 (componentVariance 1)).prod (gaussianReal 0 (componentVariance 1))).map
      (Prod.map (fun x : ℝ => c * x) (fun y : ℝ => c * y)) =
      (gaussianReal 0 (componentVariance a)).prod (gaussianReal 0 (componentVariance a)) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    simp only [gaussianReal_map_const_mul, mul_zero, hvar]
  have hf : (fun z : ℂ => c • z) ∘ Complex.measurableEquivRealProd.symm =
      Complex.measurableEquivRealProd.symm ∘ (Prod.map (fun x : ℝ => c * x) (fun y : ℝ => c * y)) := by
    funext p
    apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
  have hm : Measurable (fun z : ℂ => c • z) := by fun_prop
  unfold complexGaussian
  rw [Measure.map_map hm complexGaussian_measurable_transport, hf,
    ← Measure.map_map complexGaussian_measurable_transport (by fun_prop), hp]

/-- The action `a ‖z‖²` of the rate-`a` Gaussian has the same law as `‖w‖²` for the rate-one
Gaussian: the law does not depend on the rate. -/
lemma map_rateSqNorm_complexGaussian38 (a : ℝ) (ha : 0 < a) :
    (complexGaussian a).map (fun z : ℂ => a * ‖z‖ ^ 2) =
      (complexGaussian 1).map (fun w : ℂ => ‖w‖ ^ 2) := by
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hm : Measurable (fun z : ℂ => (Real.sqrt a)⁻¹ • z) := by fun_prop
  rw [complexGaussian_eq_map_smul38 a ha,
    Measure.map_map (by fun_prop) hm]
  congr 1
  funext w
  simp only [Function.comp, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsq]
  rw [mul_pow, inv_pow, Real.sq_sqrt ha.le]
  field_simp


/-- Radial integral: `∫_0^{√t} r (1/π) e^{-r²} dr = (1 - e^{-t})/(2π)`. -/
lemma radial_integral38 (t : ℝ) (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..Real.sqrt t, r * ((1 / Real.pi) * Real.exp (-r ^ 2)) =
      (1 - Real.exp (-t)) / (2 * Real.pi) := by
  have hd : ∀ r ∈ Set.uIcc (0 : ℝ) (Real.sqrt t),
      HasDerivAt (fun r : ℝ => -(1 / (2 * Real.pi)) * Real.exp (-r ^ 2))
        (r * ((1 / Real.pi) * Real.exp (-r ^ 2))) r := by
    intro r _
    have h0 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h1 := h0.neg
    have h2 := (h1.exp).const_mul (-(1 / (2 * Real.pi)))
    convert h2 using 1
    simp only [Pi.neg_apply]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    exact (by fun_prop : Continuous fun r : ℝ => r * ((1 / Real.pi) * Real.exp (-r ^ 2))).intervalIntegrable _ _)]
  simp only [Real.sq_sqrt ht, neg_zero, Real.exp_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_one]
  field_simp
  ring

/-- `P(|g|² ≤ t) = 1 - e^{-t}` for the rate-one proper complex Gaussian (polar coordinates). -/
lemma complexGaussian_sqNorm_le38 (t : ℝ) (ht : 0 ≤ t) :
    complexGaussian 1 {z : ℂ | ‖z‖ ^ 2 ≤ t} = ENNReal.ofReal (1 - Real.exp (-t)) := by
  have hs : MeasurableSet {z : ℂ | ‖z‖ ^ 2 ≤ t} := measurableSet_le (by fun_prop) measurable_const
  rw [complexGaussian_density 1 one_pos, withDensity_apply _ hs, ← lintegral_indicator hs,
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hpt : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 • ({z : ℂ | ‖z‖ ^ 2 ≤ t}.indicator
          (fun z : ℂ => ENNReal.ofReal ((1 / Real.pi) * Real.exp (-1 * ‖z‖ ^ 2)))
          (Complex.polarCoord.symm p)) =
        (Set.Ioc (0 : ℝ) (Real.sqrt t)).indicator
          (fun r : ℝ => ENNReal.ofReal (r * ((1 / Real.pi) * Real.exp (-r ^ 2)))) p.1 * 1 := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    simp only [Set.indicator, Set.mem_ofPred_eq, hn, Set.mem_Ioc, smul_eq_mul, mul_one]
    by_cases hle : p.1 ^ 2 ≤ t
    · have : p.1 ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hle
      simp only [hle, this, and_self, hp1, ite_true]
      rw [← ENNReal.ofReal_mul hp1.le]
      congr 1
      ring_nf
    · have : ¬ p.1 ≤ Real.sqrt t := fun h => hle (by
        have := pow_le_pow_left₀ hp1.le h 2
        rwa [Real.sq_sqrt ht] at this)
      simp [hle, this]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt]
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) =
      (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hF : Measurable (fun r : ℝ => ENNReal.ofReal (r * ((1 / Real.pi) * Real.exp (-r ^ 2)))) := by
    fun_prop
  rw [hprod, lintegral_prod_mul (hF.indicator measurableSet_Ioc).aemeasurable aemeasurable_const,
    lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self]
  have hcont : Continuous (fun r : ℝ => r * ((1 / Real.pi) * Real.exp (-r ^ 2))) := by fun_prop
  have hI : ∫⁻ r in Set.Ioc (0 : ℝ) (Real.sqrt t),
      ENNReal.ofReal (r * ((1 / Real.pi) * Real.exp (-r ^ 2))) =
      ENNReal.ofReal ((1 - Real.exp (-t)) / (2 * Real.pi)) := by
    have hint : IntegrableOn (fun r : ℝ => r * ((1 / Real.pi) * Real.exp (-r ^ 2)))
        (Set.Ioc (0 : ℝ) (Real.sqrt t)) :=
      (hcont.continuousOn.integrableOn_Icc (a := 0) (b := Real.sqrt t)).mono_set Set.Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioc
      (fun r hr => mul_nonneg hr.1.le (by positivity))), ← intervalIntegral.integral_of_le (Real.sqrt_nonneg t),
      radial_integral38 t ht]
  rw [hI, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioo, one_mul, ← ENNReal.ofReal_mul (div_nonneg (by
      have := Real.exp_le_one_iff.2 (show -t ≤ 0 by linarith)
      linarith) (by positivity))]
  congr 1
  field_simp
  ring_nf

/-- **The squared modulus of the rate-one proper complex Gaussian is an exponential random variable
of rate (and mean) one.** -/
theorem map_sqNorm_complexGaussian_eq_expMeasure38 :
    (complexGaussian 1).map (fun w : ℂ => ‖w‖ ^ 2) = expMeasure 1 := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  refine Measure.ext_of_Iic _ _ (fun t => ?_)
  have hE : expMeasure 1 (Set.Iic t) = ENNReal.ofReal (if 0 ≤ t then 1 - Real.exp (-(1 * t)) else 0) := by
    rw [← cdf_expMeasure_eq one_pos t, cdf_eq_real, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hE, Measure.map_apply (by fun_prop) measurableSet_Iic]
  by_cases ht : 0 ≤ t
  · simp only [ht, ite_true]
    have := complexGaussian_sqNorm_le38 t ht
    rw [one_mul]
    exact this
  · have : (fun w : ℂ => ‖w‖ ^ 2) ⁻¹' Set.Iic t = ∅ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (not_le.1 ht) (by positivity)
    simp [this, ht]

/-- For every rate `a > 0`, `a ‖z‖²` under `complexGaussian a` is exponential of mean one. -/
theorem map_rateSqNorm_complexGaussian_eq_expMeasure38 (a : ℝ) (ha : 0 < a) :
    (complexGaussian a).map (fun z : ℂ => a * ‖z‖ ^ 2) = expMeasure 1 := by
  rw [map_rateSqNorm_complexGaussian38 a ha, map_sqNorm_complexGaussian_eq_expMeasure38]

/-- **S05.05, independence and laws.** Under `countableComplexGaussian q` (`q n > 0`) the actions
`q_n ‖z_n‖²` are independent, and each has the exponential law of rate (and mean) one. -/
theorem iIndep_rateSqNorm_exp38 (q : ℤ → ℝ) (hq : ∀ n, 0 < q n) :
    iIndepFun (fun (n : ℤ) (z : ℤ → ℂ) => q n * ‖z n‖ ^ 2) (countableComplexGaussian q) ∧
    ∀ n : ℤ, (countableComplexGaussian q).map (fun z : ℤ → ℂ => q n * ‖z n‖ ^ 2) = expMeasure 1 := by
  refine ⟨?_, fun n => ?_⟩
  · exact iIndepFun_infinitePi (P := fun n : ℤ => complexGaussian (q n))
      (X := fun n (w : ℂ) => q n * ‖w‖ ^ 2) (fun n => by fun_prop)
  · have : (fun z : ℤ → ℂ => q n * ‖z n‖ ^ 2) =
        (fun w : ℂ => q n * ‖w‖ ^ 2) ∘ (fun z : ℤ → ℂ => z n) := rfl
    rw [this, ← Measure.map_map (g := fun w : ℂ => q n * ‖w‖ ^ 2) (by fun_prop) (measurable_pi_apply n),
      countableComplexGaussian_map_eval, map_rateSqNorm_complexGaussian_eq_expMeasure38 _ (hq n)]

/-- **S05.05 (Φ-free; strong law).** For positive rates `q`, almost surely under
`countableComplexGaussian q` the nonnegative extended sum `∑_n q_n ‖z_n‖²` is `+∞`.  Proof: the
`q_n ‖z_n‖²` are independent exponential variables of mean one (`iIndep_rateSqNorm_exp38`), so by
the strong law along `n = 0, 1, 2, …` their Cesàro means tend to `1`. -/
theorem tsum_rateSqNorm_eq_top_ae38 (q : ℤ → ℝ) (hq : ∀ n, 0 < q n) :
    ∀ᵐ z ∂countableComplexGaussian q, ∑' n : ℤ, ENNReal.ofReal (q n * ‖z n‖ ^ 2) = ∞ := by
  set μ := countableComplexGaussian q with hμ
  set X : ℕ → (ℤ → ℂ) → ℝ := fun n z => q (n : ℤ) * ‖z (n : ℤ)‖ ^ 2 with hX
  have hmeas : ∀ n, Measurable (X n) := fun n => by simp only [hX]; fun_prop
  have hint : Integrable (X 0) μ := by
    simpa [hX] using (integrable_countableComplexGaussian_sqNorm q 0).const_mul (q 0)
  obtain ⟨h0, hlaw⟩ := iIndep_rateSqNorm_exp38 q hq
  have hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X) := by
    intro i j hij
    exact (h0.precomp Nat.cast_injective).indepFun hij
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := by
    intro i
    refine ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, ?_⟩
    have := hlaw (i : ℤ)
    have h2 := hlaw ((0 : ℕ) : ℤ)
    simp only [hX]
    rw [this, h2]
  have hSL := strong_law_ae_real X hint hindep hident
  have hmean : μ[X 0] = 1 := by
    have := integral_countableComplexGaussian_sqNorm q hq 0
    simp only [hX, Nat.cast_zero]
    rw [integral_const_mul, this]
    field_simp [(hq 0).ne']
  filter_upwards [hSL] with z hz
  rw [hmean] at hz
  exact tsum_int_eq_top_of_cesaro38 (fun n => q n * ‖z n‖ ^ 2)
    (fun n => mul_nonneg (hq n).le (by positivity)) hz

/-- The same for the project's `γ_W = fullWeightSequenceGaussian c`: `∑_n a_n ‖z_n‖² = ∞` almost
surely, `a_n = W(2πn)`. -/
theorem tsum_fullWeight_sqNorm_eq_top_ae38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∀ᵐ z ∂fullWeightSequenceGaussian c,
      ∑' n : ℤ, ENNReal.ofReal (fullWeightRate c n * ‖z n‖ ^ 2) = ∞ :=
  tsum_rateSqNorm_eq_top_ae38 (fullWeightRate c)
    (fun n => fullWeightRate_pos lower upper c hlower hbound hupper n)

/-! ### S05.01: the extended relative entropy convention -/

/-- **S05.01 (convention).** For probability measures, `klDiv ν γ = +∞` exactly when `ν` is not
absolutely continuous w.r.t. `γ`, or `∫ (log dν/dγ)⁺ dν = ∞`.  (The negative part of the
log-likelihood ratio is always `ν`-integrable, as `-llr ≤ exp(-llr) = dγ/dν`, so integrability of
`llr` fails only through its positive part.)  Thus `klDiv` is the usual extended nonnegative
relative entropy `∫ log (dν/dγ) dν ∈ [0,∞]` with the stated `+∞` convention. -/
theorem klDiv_eq_top_iff_lintegral38 {α : Type*} [MeasurableSpace α] (ν γ : Measure α)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ] :
    klDiv ν γ = ∞ ↔ ¬ ν ≪ γ ∨ ∫⁻ x, ENNReal.ofReal (llr ν γ x) ∂ν = ∞ := by
  rw [klDiv_eq_top_iff]
  by_cases hac : ν ≪ γ
  · simp only [hac, true_imp_iff, not_true_eq_false, false_or]
    have hexp : Integrable (fun x => Real.exp (-llr ν γ x)) ν := by
      have := Measure.integrable_toReal_rnDeriv (μ := γ) (ν := ν)
      exact this.congr (exp_neg_llr hac).symm
    have hneg : ∫⁻ x, ENNReal.ofReal (-llr ν γ x) ∂ν ≠ ∞ := by
      refine ne_top_of_le_ne_top hexp.hasFiniteIntegral.ne ?_
      refine lintegral_mono (fun x => ?_)
      rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (-llr ν γ x)])
    have hm : Measurable (llr ν γ) := measurable_llr ν γ
    constructor
    · intro h
      by_contra hfin
      apply h
      refine ⟨hm.aestronglyMeasurable, ?_⟩
      show ∫⁻ x, ‖llr ν γ x‖ₑ ∂ν < ∞
      have : ∀ x, ‖llr ν γ x‖ₑ ≤ ENNReal.ofReal (llr ν γ x) + ENNReal.ofReal (-llr ν γ x) := by
        intro x
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total 0 (llr ν γ x) with h0 | h0
        · rw [abs_of_nonneg h0]; exact le_self_add
        · rw [abs_of_nonpos h0]; exact le_add_self
      refine lt_of_le_of_lt (lintegral_mono this) ?_
      rw [lintegral_add_left hm.ennreal_ofReal]
      exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hfin, lt_top_iff_ne_top.2 hneg⟩
    · intro h hint
      refine absurd h ?_
      exact ne_top_of_le_ne_top hint.hasFiniteIntegral.ne
        (lintegral_mono (fun x => by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)))
  · simp [hac]

end NlsGge.Measure
