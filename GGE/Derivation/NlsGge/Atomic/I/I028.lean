import Mathlib
import NlsGge.Birkhoff.S04Moments38c
import NlsGge.Measure.CountableSupport
import NlsGge.Atomic.I.I018
import NlsGge.Atomic.I.I039

/- I-028 PROOF01 (proof development, AUTHOR; not self-reviewed). Statement verbatim from STATEMENTS/I.md I-028.
   Design-name abbrevs `sobolevSequenceWeight` (hosted by landed I-018 on main; copied byte-identically here for
   the worker baseline) and `sobolevSeqNorm` (I.lean.md, not hosted elsewhere yet). Opens: only existing namespaces. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Birkhoff NlsGge.Sobolev38

namespace NlsGge.ThirdConsultation.I


theorem i028 (lower upper : ℝ) (c : BoundedCoefficients lower upper) (m : ℕ) :
    ∃ δ C L : ℝ, 0 < δ ∧ 0 < C ∧ 0 < L ∧ δ * C < 1 / 2 ∧
      (∀ n : ℤ, sobolevSequenceWeight m n / fullWeightRate c.val n ≤ C) ∧
      HasProd (fun n : ℤ =>
        (1 - δ * sobolevSequenceWeight m n / fullWeightRate c.val n)⁻¹) L ∧
      (∀ᵐ z ∂fullWeightSequenceGaussian c.val,
        SobolevSquareSummable (m : ℝ) z) ∧
      Integrable (fun z : ℤ → ℂ => Real.exp (δ * sobolevSeqNorm m z ^ 2))
        (fullWeightSequenceGaussian c.val) ∧
      (∫ z : ℤ → ℂ, Real.exp (δ * sobolevSeqNorm m z ^ 2)
        ∂fullWeightSequenceGaussian c.val) = L := by
  have hlower : 0 < lower := c.property.1
  have hbound : ∀ j : ℕ, lower ≤ c.val j := fun j => (c.property.2.2 j).1
  have hupper : ∀ j : ℕ, c.val j ≤ upper := fun j => (c.property.2.2 j).2
  have hq : ∀ n : ℤ, 0 < fullWeightRate c.val n :=
    fun n => fullWeightRate_pos lower upper c.val hlower hbound hupper n
  have hw := sobolevWeight38_nonneg m
  set a : ℤ → ℝ := fullWeightRate c.val with ha
  set r : ℤ → ℝ := fun n => sobolevWeight38 m n / a n with hr
  have hr0 : ∀ n, 0 ≤ r n := fun n => div_nonneg (hw n) (hq n).le
  have hrs : Summable r := by
    simpa only [hr, sobolevWeight38, Real.rpow_eq_pow] using
      summable_fullWeightRate_invSobolev lower upper c.val hlower hbound hupper m
  set C : ℝ := 1 + ∑' n, r n with hC
  have hCpos : 0 < C := by
    have h0 : 0 ≤ ∑' n, r n := tsum_nonneg hr0
    linarith
  have hrC : ∀ n, r n ≤ C := fun n => by
    have := hrs.le_tsum n (fun j _ => hr0 j); linarith
  set δ : ℝ := 1 / (4 * C) with hδdef
  have hδ : 0 < δ := by positivity
  have hδC : δ * C = 1 / 4 := by rw [hδdef]; field_simp
  have hxr : ∀ n, δ * sobolevWeight38 m n / a n = δ * r n := fun n => by
    simp only [hr]; ring
  have hδ2 : ∀ n : ℤ, δ * sobolevWeight38 m n / fullWeightRate c.val n ≤ 1 / 2 := fun n => by
    have h1 : δ * r n ≤ δ * C := mul_le_mul_of_nonneg_left (hrC n) hδ.le
    have := hxr n
    simp only [ha] at this
    rw [this]; linarith
  obtain ⟨hT, -, hne⟩ := exp_moment_sobolev38 lower upper c.val hlower hbound hupper m δ hδ hδ2
  set γ := fullWeightSequenceGaussian c.val with hγ
  set I : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (Real.exp (δ * sobEnergy38 m z)) ∂γ with hI
  set x : ℤ → ℝ := fun n => δ * sobolevWeight38 m n / fullWeightRate c.val n with hx
  have hx0 : ∀ n, 0 ≤ x n := fun n => by rw [hx]; simp only []; rw [hxr n]; exact mul_nonneg hδ.le (hr0 n)
  have hxh : ∀ n, x n ≤ 1 / 2 := hδ2
  have hxs : Summable x := by
    have := hrs.mul_left δ
    refine this.congr (fun n => ?_)
    simp only [hx]; exact (hxr n).symm
  set g : ℤ → ℝ := fun n => (1 - x n)⁻¹ with hg
  have hg1 : ∀ n, 1 ≤ g n := fun n => by
    have h1 : 0 < 1 - x n := by linarith [hxh n]
    rw [hg]; simp only []
    exact one_le_inv₀ h1 |>.2 (by linarith [hx0 n])
  set y : ℤ → ℝ := fun n => g n - 1 with hy
  have hy0 : ∀ n, 0 ≤ y n := fun n => by simp only [hy]; linarith [hg1 n]
  have hyle : ∀ n, y n ≤ 2 * x n := fun n => by
    have h1 : 0 < 1 - x n := by linarith [hxh n]
    have : g n ≤ 1 + 2 * x n := by
      rw [hg]; simp only []
      rw [inv_le_iff_one_le_mul₀' h1]
      nlinarith [hxh n, hx0 n]
    simp only [hy]; linarith
  have hys : Summable y :=
    Summable.of_nonneg_of_le hy0 hyle (hxs.mul_left 2)
  have hmult : Multipliable g := by
    have := multipliable_one_add_of_summable (f := y) (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hy0 _)] using hys)
    convert this using 2 with n
    simp only [Pi.add_apply, Pi.one_apply, hy]; ring
  set P : ℝ := ∏' n, g n with hP
  have hPh : HasProd g P := hmult.hasProd
  have hPlim : Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc (-(N : ℤ)) N, g n) atTop (𝓝 P) :=
    hPh.comp isExhaustion_stdExh38.tendsto_atTop
  have hprod0 : ∀ N : ℕ, 0 ≤ ∏ n ∈ Finset.Icc (-(N : ℤ)) N, g n :=
    fun N => Finset.prod_nonneg (fun n _ => by linarith [hg1 n])
  have hlim2 : Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc (-(N : ℤ)) N, g n) atTop (𝓝 I.toReal) := by
    have := (ENNReal.tendsto_toReal hne).comp hT
    refine this.congr (fun N => ?_)
    simp only [Function.comp]
    exact ENNReal.toReal_ofReal (hprod0 N)
  have hPI : P = I.toReal := tendsto_nhds_unique hPlim hlim2
  have hP1 : 1 ≤ P := by
    refine ge_of_tendsto' hPlim (fun N => ?_)
    exact Finset.prod_induction g (fun x => 1 ≤ x)
      (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun n _ => hg1 n)
  -- the exponential moment
  have hsq : ∀ z : ℤ → ℂ, sobolevSeqNorm m z ^ 2 = sobEnergy38 m z := fun z => by
    simp only [sobolevSeqNorm, hnorm38]
    exact Real.sq_sqrt (sobEnergy38_nonneg m z)
  have hmeas : Measurable (fun z : ℤ → ℂ => Real.exp (δ * sobEnergy38 m z)) :=
    Real.measurable_exp.comp ((measurable_sobEnergy38 m).const_mul δ)
  have hnn : 0 ≤ᵐ[γ] (fun z : ℤ → ℂ => Real.exp (δ * sobEnergy38 m z)) :=
    Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le)
  have hint : Integrable (fun z : ℤ → ℂ => Real.exp (δ * sobEnergy38 m z)) γ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_top_iff_ne_top.2 hne
  have hfun : (fun z : ℤ → ℂ => Real.exp (δ * sobolevSeqNorm m z ^ 2)) =
      fun z => Real.exp (δ * sobEnergy38 m z) := by
    funext z; rw [hsq z]
  refine ⟨δ, C, P, hδ, hCpos, by linarith, by rw [hδC]; norm_num, hrC, hPh,
    ae_fullWeightSequenceGaussian_sobolev lower upper c.val hlower hbound hupper m, ?_, ?_⟩
  · rw [hfun]; exact hint
  · rw [hfun, integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable, hPI]


end NlsGge.ThirdConsultation.I
