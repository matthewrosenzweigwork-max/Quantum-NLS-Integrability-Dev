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

def currentStep (N : ℕ) (u : SobolevHilbert 1) (t : ℝ) : ℝ :=
  (sampleStep N 0 u t * star (sampleStep N (-1) u t)).im / alh38 N

namespace AL063Aux

local instance finMeas063 : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by simp [Measure.restrict_apply_univ]⟩

theorem im_bound (z : ℂ) : ‖z.im‖ ≤ ‖z‖ := by
  rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm z

theorem im_mul_star_self (s : ℂ) : (s * star s).im = 0 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_im]

theorem backward_eq_samples (N : ℕ) (y : SobolevHilbert 1) (t : ℝ) :
    backwardStep N y t = (sampleStep N 0 y t - sampleStep N (-1) y t) / (alh38 N : ℂ) := by
  unfold backwardStep sampleStep stepArray
  rw [alBd_sample38]
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, add_zero, ← sub_eq_add_neg]

theorem current_identity (N : ℕ) (y : SobolevHilbert 1) (t : ℝ) :
    currentStep N y t = (backwardStep N y t * star (sampleStep N (-1) y t)).im := by
  rw [backward_eq_samples, currentStep, div_mul_eq_mul_div, Complex.div_ofReal_im]
  congr 1
  have e : (sampleStep N 0 y t - sampleStep N (-1) y t) * star (sampleStep N (-1) y t) =
      sampleStep N 0 y t * star (sampleStep N (-1) y t) -
        sampleStep N (-1) y t * star (sampleStep N (-1) y t) := by ring
  rw [e, Complex.sub_im, im_mul_star_self, sub_zero]

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

theorem currentStep_measurable (N : ℕ) (y : SobolevHilbert 1) : Measurable (currentStep N y) := by
  have hm : Measurable (fun t => sampleStep N 0 y t * star (sampleStep N (-1) y t)) :=
    (sampleStep_measurable N 0 y).mul (continuous_star.measurable.comp (sampleStep_measurable N (-1) y))
  unfold currentStep
  exact (Complex.measurable_im.comp hm).div_const _

theorem currentStep_bound (N : ℕ) (y : SobolevHilbert 1) (t : ℝ) :
    |currentStep N y t| ≤ (‖y‖ * ‖reciprocalBracketL2‖) ^ 2 / alh38 N := by
  have h0 := sample_norm_le N y 0 (by norm_num) t
  have h1 := sample_norm_le N y (-1) (by norm_num) t
  have hz := im_bound (sampleStep N 0 y t * star (sampleStep N (-1) y t))
  rw [Real.norm_eq_abs, norm_mul, norm_star] at hz
  have hmul : ‖sampleStep N 0 y t‖ * ‖sampleStep N (-1) y t‖ ≤
      (‖y‖ * ‖reciprocalBracketL2‖) * (‖y‖ * ‖reciprocalBracketL2‖) :=
    mul_le_mul h0 h1 (norm_nonneg _) (by positivity)
  unfold currentStep
  rw [abs_div, abs_of_pos (alh38_pos N)]
  apply div_le_div_of_nonneg_right _ (alh38_pos N).le
  nlinarith [hz, hmul]

theorem currentStep_memLp (N : ℕ) (y : SobolevHilbert 1) :
    MemLp (currentStep N y) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  MemLp.of_bound (currentStep_measurable N y).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact currentStep_bound N y t)

theorem alCanon_cont (u : SobolevHilbert 1) : Continuous (alCanon38 u) := by
  unfold alCanon38
  exact (physicalH1CanonicalContinuousRepresentativeCLM u).continuous.comp continuous_quotient_mk'

theorem limit_memLp (u : SobolevHilbert 1) :
    MemLp (fun t : ℝ => (alDeriv38 u t * star (alCanon38 u t)).im) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hf := AL061Aux.alDeriv_memLp u
  have hg : MemLp (fun t : ℝ => (‖u‖ * ‖reciprocalBracketL2‖) * ‖alDeriv38 u t‖) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := (hf.norm).const_mul _
  have hm : AEStronglyMeasurable (fun t : ℝ => (alDeriv38 u t * star (alCanon38 u t)).im)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hf.aestronglyMeasurable.mul (continuous_star.comp (alCanon_cont u)).aestronglyMeasurable).im
  refine MemLp.of_le hg hm (Filter.Eventually.of_forall fun t => ?_)
  have h1 : ‖(alDeriv38 u t * star (alCanon38 u t)).im‖ ≤
      ‖alDeriv38 u t‖ * (‖u‖ * ‖reciprocalBracketL2‖) := by
    refine (im_bound _).trans ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (alCanon_norm_le38 u t) (norm_nonneg _)
  have hn : ‖(‖u‖ * ‖reciprocalBracketL2‖) * ‖alDeriv38 u t‖‖ =
      (‖u‖ * ‖reciprocalBracketL2‖) * ‖alDeriv38 u t‖ :=
    Real.norm_of_nonneg (by positivity)
  rw [hn]
  linarith [h1, mul_comm ‖alDeriv38 u t‖ (‖u‖ * ‖reciprocalBracketL2‖)]

theorem eLpNorm_scale_norm {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun t => c * ‖f t‖) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      ENNReal.ofReal c * eLpNorm f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have h := eLpNorm_const_smul (p := 2) (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) c
    (fun t => ‖f t‖)
  rw [eLpNorm_norm f hf, Real.enorm_eq_ofReal hc] at h
  exact h

end AL063Aux

open AL063Aux in
theorem al063 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hF : ∀ N, alInF38 N (x N)) (hx : Tendsto x atTop (𝓝 u)) :
    (∀ N : ℕ, ∀ t : ℝ,
      currentStep N (x N) t =
        (backwardStep N (x N) t * star (sampleStep N (-1) (x N) t)).im) ∧
    (∀ N, MemLp (currentStep N (x N)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
    MemLp (fun t : ℝ => (alDeriv38 u t * star (alCanon38 u t)).im)
      2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
    Tendsto (fun N => eLpNorm
      (fun t : ℝ => currentStep N (x N) t -
        (alDeriv38 u t * star (alCanon38 u t)).im)
      2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
  refine ⟨fun N t => current_identity N (x N) t, fun N => currentStep_memLp N (x N),
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
  have hconv_bwd := hfw.2.2.2.2.1
  have hxn : Tendsto (fun N => ‖x N‖) atTop (𝓝 ‖u‖) := hx.norm
  have hc0 : Tendsto (fun N => ENNReal.ofReal (‖x N‖ * ‖reciprocalBracketL2‖)) atTop
      (𝓝 (ENNReal.ofReal (‖u‖ * ‖reciprocalBracketL2‖))) :=
    ENNReal.tendsto_ofReal (hxn.mul_const _)
  have hc1 : Tendsto (fun N => ENNReal.ofReal (η N)) atTop (𝓝 0) := by
    have h' := (ENNReal.continuous_ofReal.tendsto 0).comp hη0
    rw [ENNReal.ofReal_zero] at h'
    exact h'
  have hfin : eLpNorm (alDeriv38 u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ ⊤ :=
    (AL061Aux.alDeriv_memLp u).eLpNorm_lt_top.ne
  have hA : Tendsto (fun N => ENNReal.ofReal (‖x N‖ * ‖reciprocalBracketL2‖) *
      eLpNorm (fun t => backwardStep N (x N) t - alDeriv38 u t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul hc0 (Or.inr ENNReal.zero_ne_top) hconv_bwd
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hB : Tendsto (fun N => ENNReal.ofReal (η N) *
      eLpNorm (alDeriv38 u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul hc1 (Or.inr hfin) tendsto_const_nhds (Or.inr ENNReal.zero_ne_top)
    simpa using this
  have hAB : Tendsto (fun N => ENNReal.ofReal (‖x N‖ * ‖reciprocalBracketL2‖) *
      eLpNorm (fun t => backwardStep N (x N) t - alDeriv38 u t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) +
      ENNReal.ofReal (η N) * eLpNorm (alDeriv38 u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
      atTop (𝓝 0) := by
    simpa using hA.add hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAB
  · intro N; exact zero_le
  intro N
  have hpt : ∀ t : ℝ,
      ‖currentStep N (x N) t - (alDeriv38 u t * star (alCanon38 u t)).im‖ ≤
        ‖x N‖ * ‖reciprocalBracketL2‖ * ‖backwardStep N (x N) t - alDeriv38 u t‖ +
          η N * ‖alDeriv38 u t‖ := by
    intro t
    have hC := current_identity N (x N) t
    have key : backwardStep N (x N) t * star (sampleStep N (-1) (x N) t) -
        alDeriv38 u t * star (alCanon38 u t) =
        (backwardStep N (x N) t - alDeriv38 u t) * star (sampleStep N (-1) (x N) t) +
          alDeriv38 u t * star (sampleStep N (-1) (x N) t - alCanon38 u t) := by
      simp only [star_sub]; ring
    have hre : currentStep N (x N) t - (alDeriv38 u t * star (alCanon38 u t)).im =
        ((backwardStep N (x N) t - alDeriv38 u t) * star (sampleStep N (-1) (x N) t)).im +
          (alDeriv38 u t * star (sampleStep N (-1) (x N) t - alCanon38 u t)).im := by
      rw [hC]
      have h2 := congrArg Complex.im key
      simp only [Complex.sub_im, Complex.add_im] at h2
      linarith
    have hS' : ‖star (sampleStep N (-1) (x N) t)‖ ≤ ‖x N‖ * ‖reciprocalBracketL2‖ := by
      rw [norm_star]; exact sample_norm_le N (x N) (-1) (by norm_num) t
    have hU : ‖star (sampleStep N (-1) (x N) t - alCanon38 u t)‖ ≤ η N := by
      rw [norm_star]; exact hsamp N (-1) (by norm_num) t
    calc ‖currentStep N (x N) t - (alDeriv38 u t * star (alCanon38 u t)).im‖
        = ‖((backwardStep N (x N) t - alDeriv38 u t) * star (sampleStep N (-1) (x N) t)).im +
            (alDeriv38 u t * star (sampleStep N (-1) (x N) t - alCanon38 u t)).im‖ := by
          rw [hre]
      _ ≤ ‖((backwardStep N (x N) t - alDeriv38 u t) * star (sampleStep N (-1) (x N) t)).im‖ +
            ‖(alDeriv38 u t * star (sampleStep N (-1) (x N) t - alCanon38 u t)).im‖ := norm_add_le _ _
      _ ≤ ‖(backwardStep N (x N) t - alDeriv38 u t) * star (sampleStep N (-1) (x N) t)‖ +
            ‖alDeriv38 u t * star (sampleStep N (-1) (x N) t - alCanon38 u t)‖ :=
          add_le_add (im_bound _) (im_bound _)
      _ = ‖backwardStep N (x N) t - alDeriv38 u t‖ * ‖star (sampleStep N (-1) (x N) t)‖ +
            ‖alDeriv38 u t‖ * ‖star (sampleStep N (-1) (x N) t - alCanon38 u t)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖backwardStep N (x N) t - alDeriv38 u t‖ * (‖x N‖ * ‖reciprocalBracketL2‖) +
            ‖alDeriv38 u t‖ * η N :=
          add_le_add (mul_le_mul_of_nonneg_left hS' (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hU (norm_nonneg _))
      _ = ‖x N‖ * ‖reciprocalBracketL2‖ * ‖backwardStep N (x N) t - alDeriv38 u t‖ +
          η N * ‖alDeriv38 u t‖ := by ring
  have hBu : MemLp (fun t => backwardStep N (x N) t - alDeriv38 u t) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hfw.1 N).2.sub (AL061Aux.alDeriv_memLp u)
  have hfm : AEStronglyMeasurable (fun t => currentStep N (x N) t -
      (alDeriv38 u t * star (alCanon38 u t)).im) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (currentStep_memLp N (x N)).aestronglyMeasurable.sub (limit_memLp u).aestronglyMeasurable
  have hm1 := eLpNorm_mono_real (p := 2) hfm (fun t => hpt t)
  have hg : eLpNorm (fun t => ‖x N‖ * ‖reciprocalBracketL2‖ *
        ‖backwardStep N (x N) t - alDeriv38 u t‖ + η N * ‖alDeriv38 u t‖) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤
      eLpNorm (fun t => ‖x N‖ * ‖reciprocalBracketL2‖ *
        ‖backwardStep N (x N) t - alDeriv38 u t‖) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) +
      eLpNorm (fun t => η N * ‖alDeriv38 u t‖) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    eLpNorm_add_le (by norm_num)
  have hsc1 := eLpNorm_scale_norm hBu.aestronglyMeasurable
    (c := ‖x N‖ * ‖reciprocalBracketL2‖) (by positivity)
  have hsc2 := eLpNorm_scale_norm (AL061Aux.alDeriv_memLp u).aestronglyMeasurable
    (c := η N) (hη_nonneg N)
  calc eLpNorm (fun t => currentStep N (x N) t - (alDeriv38 u t * star (alCanon38 u t)).im) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))
      ≤ eLpNorm (fun t => ‖x N‖ * ‖reciprocalBracketL2‖ *
            ‖backwardStep N (x N) t - alDeriv38 u t‖ + η N * ‖alDeriv38 u t‖) 2
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) := hm1
    _ ≤ _ := hg
    _ = _ := by rw [hsc1, hsc2]

end NlsGge.ThirdConsultation.AL
