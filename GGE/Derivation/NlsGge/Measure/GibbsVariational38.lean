import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Distributions.Exponential
import NlsGge.Measure.CountableGaussian

/-! S05.01-.05 (abstract part).  Source: `paper/v2.tex` lines 457-475, `A:eq:freeenergy`.

Conventions (S05.01).  For a probability measure `γ` and a measurable `R : α → ℝ` with
`R ≥ 0` (the source has `R_W(Φ⁻¹ z) ∈ [0,∞)`), put `Z = ∫ e^{-R} dγ` and
`ρ = Z⁻¹ e^{-R} γ = γ.tilted (-R)`.  The free energy of a probability measure `ν` is
`F(ν) = KL(ν ‖ γ) + ∫ R dν` valued in `[0,∞]`, with `KL = InformationTheory.klDiv`
(`+∞` when `ν` is not `≪ γ` or `log dν/dγ` is not `ν`-integrable) and `∫ R dν` the
nonnegative extended integral `∫⁻ ofReal R dν`.  Since `0 < Z ≤ 1`, `-log Z ≥ 0`. -/

set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace NlsGge.Measure

variable {α : Type*} [MeasurableSpace α]

/-- The partition function `Z = ∫ e^{-R} dγ`. -/
def gibbsPartition38 (γ : Measure α) (R : α → ℝ) : ℝ := ∫ x, Real.exp (-R x) ∂γ

/-- The Gibbs law `ρ = Z⁻¹ e^{-R} γ`. -/
def gibbsLaw38 (γ : Measure α) (R : α → ℝ) : Measure α := γ.tilted (fun x => -R x)

/-- The extended-real free energy `KL(ν‖γ) + ∫ R dν`. -/
def freeEnergy38 (γ : Measure α) (R : α → ℝ) (ν : Measure α) : ℝ≥0∞ :=
  klDiv ν γ + ∫⁻ x, ENNReal.ofReal (R x) ∂ν

/-- Real-valued integral and extended integral of a nonnegative integrable function. -/
lemma lintegral_ofReal_eq38 (R : α → ℝ) (hR0 : ∀ x, 0 ≤ R x) (ν : Measure α) (hI : Integrable R ν) :
    ∫⁻ x, ENNReal.ofReal (R x) ∂ν = ENNReal.ofReal (∫ x, R x ∂ν) :=
  (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hR0)).symm

/-- Finite free energy forces integrability of `R`. -/
lemma integrable_of_freeEnergy_ne_top38 (R : α → ℝ) (hR : Measurable R) (hR0 : ∀ x, 0 ≤ R x) (ν : Measure α)
    (h : ∫⁻ x, ENNReal.ofReal (R x) ∂ν ≠ ∞) : Integrable R ν :=
  ⟨hR.aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hR0)]; exact lt_top_iff_ne_top.mpr h⟩

/-- `r e^{-r} ≤ e^{-1}` for `r ≥ 0`. -/
lemma mul_exp_neg_le38 (r : ℝ) : r * Real.exp (-r) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (r - 1)
  have e1 : Real.exp (r - 1) = Real.exp r * Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add]; simp
  have e3 : 0 < Real.exp (-r) := Real.exp_pos _
  have h' := mul_le_mul_of_nonneg_left h e3.le
  have e4 : Real.exp (-r) * Real.exp (r - 1) = Real.exp (-1) := by
    rw [e1, ← mul_assoc, e2, one_mul]
  nlinarith [e4, e2]

section
variable (γ : Measure α) [IsProbabilityMeasure γ] (R : α → ℝ)
  (hR : Measurable R) (hR0 : ∀ x, 0 ≤ R x)
include hR hR0

lemma integrable_exp_neg38 : Integrable (fun x => Real.exp (-R x)) γ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by linarith [hR0 x])

lemma gibbsPartition38_pos : 0 < gibbsPartition38 γ R :=
  integral_exp_pos (integrable_exp_neg38 γ R hR hR0)

lemma gibbsPartition38_le_one : gibbsPartition38 γ R ≤ 1 := by
  have := integral_mono (integrable_exp_neg38 γ R hR hR0) (integrable_const (1 : ℝ))
    (fun x => (Real.exp_le_one_iff.mpr (by linarith [hR0 x]) :
      Real.exp (-R x) ≤ 1))
  simpa [gibbsPartition38] using this

theorem gibbsLaw38_prob : IsProbabilityMeasure (gibbsLaw38 γ R) :=
  isProbabilityMeasure_tilted (f := fun x => -R x) (integrable_exp_neg38 γ R hR hR0)

/-- The Gibbs law is `Z⁻¹ e^{-R} γ`. -/
lemma gibbsLaw38_eq_withDensity :
    gibbsLaw38 γ R = γ.withDensity
      (fun x => ENNReal.ofReal ((gibbsPartition38 γ R)⁻¹ * Real.exp (-R x))) := by
  unfold gibbsLaw38 Measure.tilted gibbsPartition38
  congr 1
  funext x
  rw [div_eq_inv_mul]

lemma gibbsLaw38_ac : gibbsLaw38 γ R ≪ γ := tilted_absolutelyContinuous _ _
lemma ac_gibbsLaw38 : γ ≪ gibbsLaw38 γ R :=
  absolutelyContinuous_tilted (f := fun x => -R x) (integrable_exp_neg38 γ R hR hR0)

/-- S05.02: chain identity, real form. -/
lemma toReal_klDiv_gibbs38 (ν : Measure α) [IsProbabilityMeasure ν] (hac : ν ≪ γ)
    (hK : Integrable (llr ν γ) ν) (hI : Integrable R ν) :
    klDiv ν (gibbsLaw38 γ R) ≠ ∞ ∧
    (klDiv ν (gibbsLaw38 γ R)).toReal =
      (klDiv ν γ).toReal + ∫ x, R x ∂ν + Real.log (gibbsPartition38 γ R) := by
  have hexp := integrable_exp_neg38 γ R hR hR0
  have hfν : Integrable (fun x => -R x) ν := hI.neg
  have hint := integrable_llr_tilted_right (f := fun x => -R x) hac hfν hK hexp
  have := gibbsLaw38_prob γ R hR hR0
  have hac' : ν ≪ gibbsLaw38 γ R := hac.trans (ac_gibbsLaw38 γ R hR hR0)
  refine ⟨klDiv_ne_top hac' hint, ?_⟩
  rw [toReal_klDiv_of_measure_eq hac' (by simp), toReal_klDiv_of_measure_eq hac (by simp)]
  have := integral_llr_tilted_right (f := fun x => -R x) hac hfν hexp hK
  unfold gibbsLaw38 gibbsPartition38
  rw [this, integral_neg]
  ring

/-- S05.02: chain identity for finite free energy:
`KL(ν‖ρ) = KL(ν‖γ) + ∫ R dν + log Z` (as extended reals `F ν = KL(ν‖ρ) + (-log Z)`). -/
theorem freeEnergy38_chain (ν : Measure α) [IsProbabilityMeasure ν]
    (h : freeEnergy38 γ R ν ≠ ∞) :
    freeEnergy38 γ R ν = klDiv ν (gibbsLaw38 γ R) + ENNReal.ofReal (-Real.log (gibbsPartition38 γ R)) := by
  have h1 : klDiv ν γ ≠ ∞ := fun e => h (by simp [freeEnergy38, e])
  have h2 : ∫⁻ x, ENNReal.ofReal (R x) ∂ν ≠ ∞ := fun e => h (by simp [freeEnergy38, e])
  have hI := integrable_of_freeEnergy_ne_top38 R hR hR0 ν h2
  obtain ⟨hac, hK⟩ := klDiv_ne_top_iff.mp h1
  obtain ⟨hne, hre⟩ := toReal_klDiv_gibbs38 γ R hR hR0 ν hac hK hI
  have hZ := gibbsPartition38_pos γ R hR hR0
  have hZ1 := gibbsPartition38_le_one γ R hR hR0
  have hlog : Real.log (gibbsPartition38 γ R) ≤ 0 := Real.log_nonpos hZ.le hZ1
  have hKnn : 0 ≤ (klDiv ν γ).toReal := ENNReal.toReal_nonneg
  have hInn : 0 ≤ ∫ x, R x ∂ν := integral_nonneg hR0
  have hρnn := ENNReal.toReal_nonneg (a := klDiv ν (gibbsLaw38 γ R))
  unfold freeEnergy38
  rw [lintegral_ofReal_eq38 R hR0 ν hI, ← ENNReal.ofReal_toReal h1,
    ← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_add hKnn hInn,
    ← ENNReal.ofReal_add hρnn (by linarith)]
  congr 1
  rw [hre]; ring

/-- S05.03: the Gibbs law has finite `R`-integral. -/
theorem integrable_gibbsLaw38 : Integrable R (gibbsLaw38 γ R) := by
  have hexp := integrable_exp_neg38 γ R hR hR0
  unfold gibbsLaw38
  rw [integrable_tilted_iff (f := fun x => -R x) hexp]
  have hb : ∀ x, ‖Real.exp (-R x) • R x‖ ≤ Real.exp (-1) := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (hR0 x)]
    linarith [mul_exp_neg_le38 (R x)]
  exact Integrable.mono' (integrable_const _) (by fun_prop) (ae_of_all _ hb)

/-- S05.03: `∫ R dρ ≤ 1/(e Z)`. -/
theorem integral_gibbsLaw38_le : ∫ x, R x ∂(gibbsLaw38 γ R) ≤
    1 / (Real.exp 1 * gibbsPartition38 γ R) := by
  have hZ := gibbsPartition38_pos γ R hR hR0
  unfold gibbsLaw38
  rw [integral_tilted]
  have : (1 : ℝ) / (Real.exp 1 * gibbsPartition38 γ R) = ∫ _ : α, Real.exp (-1) / gibbsPartition38 γ R ∂γ := by
    rw [integral_const]; simp [Real.exp_neg, gibbsPartition38]; field_simp
  rw [this]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) (integrable_const _) (ae_of_all _ fun x => ?_)
  · simp only [smul_eq_mul]
    exact mul_nonneg (div_nonneg (Real.exp_pos _).le (by exact hZ.le)) (hR0 x)
  · simp only [smul_eq_mul]
    have := mul_exp_neg_le38 (R x)
    rw [div_mul_eq_mul_div, mul_comm]
    exact div_le_div_of_nonneg_right this hZ.le

/-- Free energy of the Gibbs law is `-log Z` (S05.03). -/
theorem freeEnergy38_gibbs :
    freeEnergy38 γ R (gibbsLaw38 γ R) = ENNReal.ofReal (-Real.log (gibbsPartition38 γ R)) := by
  have := gibbsLaw38_prob γ R hR hR0
  have hI := integrable_gibbsLaw38 γ R hR hR0
  have hac := gibbsLaw38_ac γ R hR hR0
  have hexp := integrable_exp_neg38 γ R hR hR0
  have hK : Integrable (llr (gibbsLaw38 γ R) γ) (gibbsLaw38 γ R) := by
    have h1 := llr_tilted_left (μ := γ) (ν := γ) (f := fun x => -R x) (Measure.AbsolutelyContinuous.refl γ)
      hexp hR.neg.aemeasurable
    have h2 : llr (gibbsLaw38 γ R) γ =ᵐ[gibbsLaw38 γ R] fun x => -R x - Real.log (gibbsPartition38 γ R) + 0 := by
      filter_upwards [hac.ae_le h1, hac.ae_le (llr_self γ)] with x hx hx0
      unfold gibbsLaw38 gibbsPartition38; rw [hx, hx0]; simp
    rw [integrable_congr h2]
    exact (hI.neg.sub (integrable_const _)).add (integrable_const _)
  have hfin : freeEnergy38 γ R (gibbsLaw38 γ R) ≠ ∞ := by
    unfold freeEnergy38
    refine ENNReal.add_ne_top.mpr ⟨klDiv_ne_top hac hK, ?_⟩
    rw [lintegral_ofReal_eq38 R hR0 _ hI]; exact ENNReal.ofReal_ne_top
  rw [freeEnergy38_chain γ R hR hR0 _ hfin, klDiv_self, zero_add]


/-- S05.01/S05.04: the Gibbs variational principle.  For every probability measure `ν`,
`-log Z ≤ F(ν)` in `[0,∞]`. -/
theorem freeEnergy38_ge (ν : Measure α) [IsProbabilityMeasure ν] :
    ENNReal.ofReal (-Real.log (gibbsPartition38 γ R)) ≤ freeEnergy38 γ R ν := by
  by_cases h : freeEnergy38 γ R ν = ∞
  · rw [h]; exact le_top
  · rw [freeEnergy38_chain γ R hR hR0 ν h]; exact le_add_self

/-- S05.04: equality holds iff `ν` is the Gibbs law `ρ`; hence `ρ` is the unique minimizer
and the minimum is `-log Z`. -/
theorem freeEnergy38_eq_iff (ν : Measure α) [IsProbabilityMeasure ν] :
    freeEnergy38 γ R ν = ENNReal.ofReal (-Real.log (gibbsPartition38 γ R)) ↔
      ν = gibbsLaw38 γ R := by
  have := gibbsLaw38_prob γ R hR hR0
  constructor
  · intro h
    have hc : ENNReal.ofReal (-Real.log (gibbsPartition38 γ R)) ≠ ∞ := ENNReal.ofReal_ne_top
    have h' := freeEnergy38_chain γ R hR hR0 ν (by rw [h]; exact hc)
    rw [h] at h'
    have h0 : klDiv ν (gibbsLaw38 γ R) = 0 := by
      have : klDiv ν (gibbsLaw38 γ R) + ENNReal.ofReal (-Real.log (gibbsPartition38 γ R)) =
          0 + ENNReal.ofReal (-Real.log (gibbsPartition38 γ R)) := by rw [zero_add]; exact h'.symm
      exact (ENNReal.add_left_inj hc).mp this
    exact klDiv_eq_zero_iff.mp h0
  · rintro rfl; exact freeEnergy38_gibbs γ R hR hR0

end

/-! ### S05.05: `∑ |g_n|² = ∞` almost surely -/

open Filter Topology ProbabilityTheory Function

/-- Deterministic step: if Cesàro means of nonnegative reals tend to `1`, the `ℤ`-indexed
extended sum is infinite. -/
lemma tsum_int_eq_top_of_cesaro38 (x : ℤ → ℝ) (hx : ∀ n, 0 ≤ x n)
    (h : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, x (i : ℤ)) / n) atTop (𝓝 1)) :
    ∑' n : ℤ, ENNReal.ofReal (x n) = ∞ := by
  by_contra hne
  set T := ∑' n : ℤ, ENNReal.ofReal (x n) with hT
  have hb : ∀ n : ℕ, ∑ i ∈ Finset.range n, x (i : ℤ) ≤ T.toReal := by
    intro n
    have h1 : ENNReal.ofReal (∑ i ∈ Finset.range n, x (i : ℤ)) ≤ T := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hx _)]
      have := ENNReal.sum_le_tsum ((Finset.range n).image (fun i : ℕ => (i : ℤ)))
        (f := fun n : ℤ => ENNReal.ofReal (x n))
      rwa [Finset.sum_image (fun a _ b _ hab => Nat.cast_injective hab)] at this
    have := ENNReal.toReal_mono hne h1
    rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => hx _)] at this
  have hev := h.eventually (lt_mem_nhds (show (1/2 : ℝ) < 1 by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev.and (eventually_gt_atTop 0))
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * T.toReal)
  have hM' := hN (max N (M + 1)) (le_max_left _ _)
  have hpos : (0 : ℝ) < ((max N (M + 1) : ℕ) : ℝ) := by exact_mod_cast hM'.2
  have h2 := (lt_div_iff₀ hpos).mp hM'.1
  have h3 := hb (max N (M + 1))
  have h4 : (M : ℝ) + 1 ≤ ((max N (M + 1) : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  nlinarith

/-- S05.05: for the project's free law `countableComplexGaussian (fun _ => 1)`
(independent standard complex Gaussians, real-component variance `1/2`),
`∑_n |g_n|² = ∞` almost surely (extended nonnegative sum over `ℤ`). -/
theorem tsum_sqNorm_eq_top_ae38 :
    ∀ᵐ z ∂countableComplexGaussian (fun _ : ℤ => (1 : ℝ)),
      ∑' n : ℤ, ENNReal.ofReal (‖z n‖ ^ 2) = ∞ := by
  set μ := countableComplexGaussian (fun _ : ℤ => (1 : ℝ)) with hμ
  set X : ℕ → (ℤ → ℂ) → ℝ := fun n z => ‖z (n : ℤ)‖ ^ 2 with hX
  have hmeas : ∀ n, Measurable (X n) := fun n => by simp only [hX]; fun_prop
  have hint : Integrable (X 0) μ := by
    simpa [hX] using integrable_countableComplexGaussian_sqNorm (fun _ : ℤ => (1 : ℝ)) 0
  have hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X) := by
    intro i j hij
    have h0 : iIndepFun (fun (n : ℤ) (z : ℤ → ℂ) => ‖z n‖ ^ 2) μ :=
      iIndepFun_infinitePi (P := fun _ : ℤ => complexGaussian 1)
        (X := fun _ (w : ℂ) => ‖w‖ ^ 2) (fun _ => by fun_prop)
    exact (h0.precomp Nat.cast_injective).indepFun hij
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := by
    intro i
    refine ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, ?_⟩
    have key : ∀ n : ℕ, μ.map (X n) = (complexGaussian 1).map (fun w : ℂ => ‖w‖ ^ 2) := by
      intro n
      have : X n = (fun w : ℂ => ‖w‖ ^ 2) ∘ (fun z : ℤ → ℂ => z (n : ℤ)) := rfl
      rw [this, ← Measure.map_map (g := fun w : ℂ => ‖w‖ ^ 2) (by fun_prop) (measurable_pi_apply _)]
      rw [hμ, countableComplexGaussian_map_eval]
    rw [key, key]
  have hlaw := strong_law_ae_real X hint hindep hident
  have hmean : μ[X 0] = 1 := by
    simpa [hX] using integral_countableComplexGaussian_sqNorm (fun _ : ℤ => (1 : ℝ))
      (fun _ => one_pos) 0
  filter_upwards [hlaw] with z hz
  rw [hmean] at hz
  exact tsum_int_eq_top_of_cesaro38 (fun n => ‖z n‖ ^ 2) (fun n => by positivity) hz

end NlsGge.Measure
