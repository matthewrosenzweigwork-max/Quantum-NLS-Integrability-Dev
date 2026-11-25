import Mathlib
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Atomic.AL.AL057
import NlsGge.Atomic.AL.AL058
import NlsGge.Atomic.AL.AL061

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik
open Set
namespace NlsGge.ThirdConsultation.AL

def densityStep (N : ℕ) (u : SobolevHilbert 1) (t : ℝ) : ℝ :=
  (‖sampleStep N 1 u t‖ ^ 2 - ‖sampleStep N 0 u t‖ ^ 2) / alh38 N

namespace AL062Aux

local instance finMeas062 : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by simp [Measure.restrict_apply_univ]⟩

theorem re_bound (z : ℂ) : ‖z.re‖ ≤ ‖z‖ := by
  rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm z

theorem re_mul_star_self (s : ℂ) : (s * star s).re = ‖s‖ ^ 2 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem re_sub_star (w : ℂ) : (w - star w).re = 0 := by
  rw [Complex.sub_re, Complex.star_def, Complex.conj_re, sub_self]

theorem forward_eq_samples (N : ℕ) (y : SobolevHilbert 1) (t : ℝ) :
    forwardStep N y t = (sampleStep N 1 y t - sampleStep N 0 y t) / (alh38 N : ℂ) := by
  unfold forwardStep sampleStep stepArray
  rw [alFd_sample38]
  simp only [Int.cast_one, Int.cast_zero, add_zero]

theorem density_identity (N : ℕ) (y : SobolevHilbert 1) (t : ℝ) :
    densityStep N y t =
      (forwardStep N y t * (star (sampleStep N 1 y t) + star (sampleStep N 0 y t))).re := by
  rw [forward_eq_samples, densityStep, div_mul_eq_mul_div, Complex.div_ofReal_re]
  congr 1
  have e : (sampleStep N 1 y t - sampleStep N 0 y t) *
      (star (sampleStep N 1 y t) + star (sampleStep N 0 y t)) =
      (sampleStep N 1 y t * star (sampleStep N 1 y t) - sampleStep N 0 y t * star (sampleStep N 0 y t)) +
      (sampleStep N 1 y t * star (sampleStep N 0 y t) - star (sampleStep N 1 y t * star (sampleStep N 0 y t))) := by
    simp only [star_mul, star_star]; ring
  rw [e, Complex.add_re, re_sub_star, Complex.sub_re]
  simp only [re_mul_star_self, add_zero]

theorem sample_norm_le (N : ℕ) (y : SobolevHilbert 1) (shift : ℤ) (hshift : |shift| ≤ 1) (t : ℝ) :
    ‖sampleStep N shift y t‖ ≤ ‖y‖ * ‖reciprocalBracketL2‖ := by
  obtain ⟨s, _, heq⟩ := al058Aux.sample_eq y N shift hshift t
  rw [heq]
  exact alCanon_norm_le38 y s

theorem sampleStep_measurable (N : ℕ) (shift : ℤ) (y : SobolevHilbert 1) :
    Measurable (sampleStep N shift y) := by
  unfold sampleStep stepArray
  have hg : Measurable (fun k : ℤ =>
      alSample38 N y ((k : ZMod (2 * N + 1)) + (shift : ZMod (2 * N + 1)))) := measurable_from_top
  exact hg.comp (Int.measurable_floor.comp (measurable_id.div_const (alh38 N)))

theorem densityStep_measurable (N : ℕ) (y : SobolevHilbert 1) : Measurable (densityStep N y) := by
  unfold densityStep
  exact ((((sampleStep_measurable N 1 y).norm.pow_const 2).sub
    ((sampleStep_measurable N 0 y).norm.pow_const 2)).div_const _)

theorem densityStep_bound (N : ℕ) (y : SobolevHilbert 1) (t : ℝ) :
    |densityStep N y t| ≤ (‖y‖ * ‖reciprocalBracketL2‖) ^ 2 / alh38 N := by
  have hM := sample_norm_le N y 1 (by norm_num) t
  have hM0 := sample_norm_le N y 0 (by norm_num) t
  have ha : ‖sampleStep N 1 y t‖ ^ 2 ≤ (‖y‖ * ‖reciprocalBracketL2‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hM 2
  have hb : ‖sampleStep N 0 y t‖ ^ 2 ≤ (‖y‖ * ‖reciprocalBracketL2‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hM0 2
  unfold densityStep
  rw [abs_div, abs_of_pos (alh38_pos N)]
  apply div_le_div_of_nonneg_right _ (alh38_pos N).le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ‖sampleStep N 1 y t‖, sq_nonneg ‖sampleStep N 0 y t‖]

theorem densityStep_memLp (N : ℕ) (y : SobolevHilbert 1) :
    MemLp (densityStep N y) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  MemLp.of_bound (densityStep_measurable N y).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact densityStep_bound N y t)

theorem alCanon_cont (u : SobolevHilbert 1) : Continuous (alCanon38 u) := by
  unfold alCanon38
  exact (physicalH1CanonicalContinuousRepresentativeCLM u).continuous.comp continuous_quotient_mk'

theorem limit_memLp (u : SobolevHilbert 1) :
    MemLp (fun t : ℝ => 2 * (alDeriv38 u t * star (alCanon38 u t)).re) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hf := AL061Aux.alDeriv_memLp u
  have hg : MemLp (fun t : ℝ => 2 * (‖u‖ * ‖reciprocalBracketL2‖) * ‖alDeriv38 u t‖) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := (hf.norm).const_mul _
  have hm : AEStronglyMeasurable (fun t : ℝ => 2 * (alDeriv38 u t * star (alCanon38 u t)).re)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (((hf.aestronglyMeasurable.mul (alCanon_cont u).star.aestronglyMeasurable).re).const_mul 2)
  refine MemLp.of_le hg hm (Filter.Eventually.of_forall fun t => ?_)
  have hn : ‖2 * (‖u‖ * ‖reciprocalBracketL2‖) * ‖alDeriv38 u t‖‖ =
      2 * (‖u‖ * ‖reciprocalBracketL2‖) * ‖alDeriv38 u t‖ :=
    Real.norm_of_nonneg (by positivity)
  rw [hn, Real.norm_eq_abs, abs_mul, abs_two]
  have h1 : ‖(alDeriv38 u t * star (alCanon38 u t)).re‖ ≤ ‖alDeriv38 u t‖ * (‖u‖ * ‖reciprocalBracketL2‖) := by
    refine (re_bound _).trans ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (alCanon_norm_le38 u t) (norm_nonneg _)
  have h1' : |(alDeriv38 u t * star (alCanon38 u t)).re| ≤
      ‖alDeriv38 u t‖ * (‖u‖ * ‖reciprocalBracketL2‖) := by
    rw [← Real.norm_eq_abs]; exact h1
  have h2 := mul_le_mul_of_nonneg_left h1' (by norm_num : (0:ℝ) ≤ 2)
  have h3 : 2 * (‖alDeriv38 u t‖ * (‖u‖ * ‖reciprocalBracketL2‖)) =
      2 * (‖u‖ * ‖reciprocalBracketL2‖) * ‖alDeriv38 u t‖ := by ring
  linarith [h2, h3]

theorem eLpNorm_scale_norm {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun t => c * ‖f t‖) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      ENNReal.ofReal c * eLpNorm f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have h := eLpNorm_const_smul (p := 2) (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) c
    (fun t => ‖f t‖)
  rw [eLpNorm_norm f hf, Real.enorm_eq_ofReal hc] at h
  exact h

end AL062Aux

open AL062Aux in
theorem al062 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hF : ∀ N, alInF38 N (x N)) (hx : Tendsto x atTop (𝓝 u)) :
    (∀ N : ℕ, ∀ t : ℝ,
      densityStep N (x N) t =
        (forwardStep N (x N) t *
          (star (sampleStep N 1 (x N) t) + star (sampleStep N 0 (x N) t))).re) ∧
    (∀ N, MemLp (densityStep N (x N)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
    MemLp (fun t : ℝ => 2 * (alDeriv38 u t * star (alCanon38 u t)).re)
      2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
    Tendsto (fun N => eLpNorm
      (fun t : ℝ => densityStep N (x N) t -
        2 * (alDeriv38 u t * star (alCanon38 u t)).re)
      2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
  refine ⟨fun N t => density_identity N (x N) t, fun N => densityStep_memLp N (x N),
    limit_memLp u, ?_⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ, η = fun N =>
      ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖ + sampleModulus u (2 * alh38 N) :=
    ⟨_, rfl⟩
  have hη_nonneg : ∀ N, 0 ≤ η N := fun N => by
    rw [hηdef]
    exact add_nonneg (norm_nonneg _) (al058Aux.modulus_nonneg u (by linarith [alh38_pos N]))
  have hη0 : Tendsto η atTop (𝓝 0) := by
    rw [hηdef]
    simpa using ((al057 x u hx).1).add ((al058 x u hx).2.1)
  have hsamp : ∀ (N : ℕ) (shift : ℤ), |shift| ≤ 1 → ∀ t : ℝ,
      ‖sampleStep N shift (x N) t - alCanon38 u t‖ ≤ η N := by
    intro N shift hs t
    rw [hηdef]
    exact (al058 x u hx).1 N shift hs t
  have hfw := al061 x u hF hx
  have hconv_fwd := hfw.2.2.2.1
  have hxn : Tendsto (fun N => ‖x N‖) atTop (𝓝 ‖u‖) := hx.norm
  have hc0 : Tendsto (fun N => ENNReal.ofReal (2 * (‖x N‖ * ‖reciprocalBracketL2‖))) atTop
      (𝓝 (ENNReal.ofReal (2 * (‖u‖ * ‖reciprocalBracketL2‖)))) :=
    ENNReal.tendsto_ofReal ((hxn.mul_const _).const_mul 2)
  have hc1 : Tendsto (fun N => ENNReal.ofReal (2 * η N)) atTop (𝓝 0) := by
    have h := hη0.const_mul 2
    rw [mul_zero] at h
    have h' := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rw [ENNReal.ofReal_zero] at h'
    exact h'
  have hfin : eLpNorm (alDeriv38 u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ ⊤ :=
    (AL061Aux.alDeriv_memLp u).eLpNorm_lt_top.ne
  have hA : Tendsto (fun N => ENNReal.ofReal (2 * (‖x N‖ * ‖reciprocalBracketL2‖)) *
      eLpNorm (fun t => forwardStep N (x N) t - alDeriv38 u t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul hc0 (Or.inr ENNReal.zero_ne_top) hconv_fwd
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hB : Tendsto (fun N => ENNReal.ofReal (2 * η N) *
      eLpNorm (alDeriv38 u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul hc1 (Or.inr hfin) tendsto_const_nhds (Or.inr ENNReal.zero_ne_top)
    simpa using this
  have hAB : Tendsto (fun N => ENNReal.ofReal (2 * (‖x N‖ * ‖reciprocalBracketL2‖)) *
      eLpNorm (fun t => forwardStep N (x N) t - alDeriv38 u t) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) +
      ENNReal.ofReal (2 * η N) * eLpNorm (alDeriv38 u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
      atTop (𝓝 0) := by
    simpa using hA.add hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAB
  · intro N; exact zero_le
  intro N
  -- pointwise bound
  have hpt : ∀ t : ℝ,
      ‖densityStep N (x N) t - 2 * (alDeriv38 u t * star (alCanon38 u t)).re‖ ≤
        2 * (‖x N‖ * ‖reciprocalBracketL2‖) * ‖forwardStep N (x N) t - alDeriv38 u t‖ +
          2 * η N * ‖alDeriv38 u t‖ := by
    intro t
    have hD := density_identity N (x N) t
    have key : forwardStep N (x N) t * (star (sampleStep N 1 (x N) t) + star (sampleStep N 0 (x N) t))
        - (alDeriv38 u t * star (alCanon38 u t) + alDeriv38 u t * star (alCanon38 u t)) =
        (forwardStep N (x N) t - alDeriv38 u t) *
            (star (sampleStep N 1 (x N) t) + star (sampleStep N 0 (x N) t)) +
          alDeriv38 u t * (star (sampleStep N 1 (x N) t - alCanon38 u t) +
            star (sampleStep N 0 (x N) t - alCanon38 u t)) := by
      simp only [star_sub]; ring
    have hre : densityStep N (x N) t - 2 * (alDeriv38 u t * star (alCanon38 u t)).re =
        ((forwardStep N (x N) t - alDeriv38 u t) *
            (star (sampleStep N 1 (x N) t) + star (sampleStep N 0 (x N) t))).re +
          (alDeriv38 u t * (star (sampleStep N 1 (x N) t - alCanon38 u t) +
            star (sampleStep N 0 (x N) t - alCanon38 u t))).re := by
      rw [hD]
      have h2 := congrArg Complex.re key
      simp only [Complex.sub_re, Complex.add_re] at h2
      linarith
    have hT : ‖star (sampleStep N 1 (x N) t) + star (sampleStep N 0 (x N) t)‖ ≤
        2 * (‖x N‖ * ‖reciprocalBracketL2‖) := by
      have h1 := sample_norm_le N (x N) 1 (by norm_num) t
      have h0 := sample_norm_le N (x N) 0 (by norm_num) t
      calc ‖star (sampleStep N 1 (x N) t) + star (sampleStep N 0 (x N) t)‖
          ≤ ‖star (sampleStep N 1 (x N) t)‖ + ‖star (sampleStep N 0 (x N) t)‖ := norm_add_le _ _
        _ = ‖sampleStep N 1 (x N) t‖ + ‖sampleStep N 0 (x N) t‖ := by rw [norm_star, norm_star]
        _ ≤ 2 * (‖x N‖ * ‖reciprocalBracketL2‖) := by linarith
    have hU : ‖star (sampleStep N 1 (x N) t - alCanon38 u t) +
        star (sampleStep N 0 (x N) t - alCanon38 u t)‖ ≤ 2 * η N := by
      have h1 := hsamp N 1 (by norm_num) t
      have h0 := hsamp N 0 (by norm_num) t
      calc ‖star (sampleStep N 1 (x N) t - alCanon38 u t) +
            star (sampleStep N 0 (x N) t - alCanon38 u t)‖
          ≤ ‖star (sampleStep N 1 (x N) t - alCanon38 u t)‖ +
              ‖star (sampleStep N 0 (x N) t - alCanon38 u t)‖ := norm_add_le _ _
        _ = ‖sampleStep N 1 (x N) t - alCanon38 u t‖ + ‖sampleStep N 0 (x N) t - alCanon38 u t‖ := by
            rw [norm_star, norm_star]
        _ ≤ 2 * η N := by linarith
    rw [hre]
    calc _ ≤ ‖((forwardStep N (x N) t - alDeriv38 u t) *
            (star (sampleStep N 1 (x N) t) + star (sampleStep N 0 (x N) t))).re‖ +
          ‖(alDeriv38 u t * (star (sampleStep N 1 (x N) t - alCanon38 u t) +
            star (sampleStep N 0 (x N) t - alCanon38 u t))).re‖ := norm_add_le _ _
      _ ≤ ‖(forwardStep N (x N) t - alDeriv38 u t) *
            (star (sampleStep N 1 (x N) t) + star (sampleStep N 0 (x N) t))‖ +
          ‖alDeriv38 u t * (star (sampleStep N 1 (x N) t - alCanon38 u t) +
            star (sampleStep N 0 (x N) t - alCanon38 u t))‖ :=
          add_le_add (re_bound _) (re_bound _)
      _ = ‖forwardStep N (x N) t - alDeriv38 u t‖ *
            ‖star (sampleStep N 1 (x N) t) + star (sampleStep N 0 (x N) t)‖ +
          ‖alDeriv38 u t‖ *
            ‖star (sampleStep N 1 (x N) t - alCanon38 u t) +
              star (sampleStep N 0 (x N) t - alCanon38 u t)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖forwardStep N (x N) t - alDeriv38 u t‖ * (2 * (‖x N‖ * ‖reciprocalBracketL2‖)) +
          ‖alDeriv38 u t‖ * (2 * η N) :=
          add_le_add (mul_le_mul_of_nonneg_left hT (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hU (norm_nonneg _))
      _ = 2 * (‖x N‖ * ‖reciprocalBracketL2‖) * ‖forwardStep N (x N) t - alDeriv38 u t‖ +
          2 * η N * ‖alDeriv38 u t‖ := by ring
  -- L2 estimate
  have hFu : MemLp (fun t => forwardStep N (x N) t - alDeriv38 u t) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hfw.1 N).1.sub (AL061Aux.alDeriv_memLp u)
  have hfm : AEStronglyMeasurable (fun t => densityStep N (x N) t -
      2 * (alDeriv38 u t * star (alCanon38 u t)).re) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (densityStep_memLp N (x N)).aestronglyMeasurable.sub (limit_memLp u).aestronglyMeasurable
  have hm1 := eLpNorm_mono_real (p := 2) hfm (fun t => hpt t)
  have hg : eLpNorm (fun t => 2 * (‖x N‖ * ‖reciprocalBracketL2‖) *
        ‖forwardStep N (x N) t - alDeriv38 u t‖ + 2 * η N * ‖alDeriv38 u t‖) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤
      eLpNorm (fun t => 2 * (‖x N‖ * ‖reciprocalBracketL2‖) *
        ‖forwardStep N (x N) t - alDeriv38 u t‖) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) +
      eLpNorm (fun t => 2 * η N * ‖alDeriv38 u t‖) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    eLpNorm_add_le (by norm_num)
  have hsc1 := eLpNorm_scale_norm hFu.aestronglyMeasurable
    (c := 2 * (‖x N‖ * ‖reciprocalBracketL2‖)) (by positivity)
  have hsc2 := eLpNorm_scale_norm (AL061Aux.alDeriv_memLp u).aestronglyMeasurable
    (c := 2 * η N) (by linarith [hη_nonneg N])
  calc eLpNorm (fun t => densityStep N (x N) t - 2 * (alDeriv38 u t * star (alCanon38 u t)).re) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))
      ≤ eLpNorm (fun t => 2 * (‖x N‖ * ‖reciprocalBracketL2‖) *
            ‖forwardStep N (x N) t - alDeriv38 u t‖ + 2 * η N * ‖alDeriv38 u t‖) 2
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) := hm1
    _ ≤ _ := hg
    _ = _ := by rw [hsc1, hsc2]

end NlsGge.ThirdConsultation.AL
