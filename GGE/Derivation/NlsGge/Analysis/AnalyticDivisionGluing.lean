import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

open Set Filter Topology

namespace NlsGge.Analysis.AnalyticDivisionGluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An analytic factor with one nonzero value can be cancelled from an eventual
identity at every point of its preconnected domain, including its zeros. The
other two factors need only be continuous at the point in question. -/
theorem cancel_at_of_eventually_mul_eq
    {U : Set E} {f g₁ g₂ : E → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected U) (hw : ∃ w ∈ U, f w ≠ 0)
    {x : E} (hx : x ∈ U) (hg₁ : ContinuousAt g₁ x) (hg₂ : ContinuousAt g₂ x)
    (heq : ∀ᶠ y in 𝓝 x, f y * g₁ y = f y * g₂ y) : g₁ x = g₂ x := by
  by_contra hne
  have hdiff : g₁ x - g₂ x ≠ 0 := sub_ne_zero.mpr hne
  have hdiff_evt : ∀ᶠ y in 𝓝 x, g₁ y - g₂ y ≠ 0 :=
    (hg₁.sub hg₂).eventually_ne hdiff
  have hfzero : f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [heq, hdiff_evt] with y hy hny
    have hmul : f y * (g₁ y - g₂ y) = 0 := by
      rw [mul_sub, hy, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right hny
  have hzero : EqOn f (fun _ => 0) U :=
    hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hx hfzero
  obtain ⟨w, hwU, hfw⟩ := hw
  exact hfw (hzero hwU)

/-- Actual analytic local solutions of `f * g = h` glue across the zeros of `f`.
The coefficient is analytic on a preconnected domain and has an earned nonzero
witness. No quotient, removability, global solution, or regularity of `h` is
assumed. Local solution domains are open subsets of the full domain. -/
theorem exists_analytic_mul_eq_of_local
    {U : Set E} {f h : E → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected U) (hw : ∃ w ∈ U, f w ≠ 0)
    (hlocal : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ g : E → ℂ, AnalyticOnNhd ℂ g V ∧ ∀ y ∈ V, f y * g y = h y) :
    ∃ G : E → ℂ, AnalyticOnNhd ℂ G U ∧ ∀ y ∈ U, f y * G y = h y := by
  classical
  have hlocal' : ∀ x : U, ∃ V : Set E, IsOpen V ∧ (x : E) ∈ V ∧ V ⊆ U ∧
      ∃ g : E → ℂ, AnalyticOnNhd ℂ g V ∧ ∀ y ∈ V, f y * g y = h y :=
    fun x => hlocal x x.property
  choose V hVo hVx hVU g hga hge using hlocal'
  let G : E → ℂ := fun x => if hx : x ∈ U then g ⟨x, hx⟩ x else 0
  have hagree : ∀ x : U, ∀ y ∈ V x, G y = g x y := by
    intro x y hy
    have hyU : y ∈ U := hVU x hy
    let yU : U := ⟨y, hyU⟩
    have hevent : ∀ᶠ z in 𝓝 y, f z * g x z = f z * g yU z := by
      filter_upwards [(hVo x).mem_nhds hy, (hVo yU).mem_nhds (hVx yU)]
        with z hzx hzy
      exact (hge x z hzx).trans (hge yU z hzy).symm
    have hval : g x y = g yU y :=
      cancel_at_of_eventually_mul_eq hf hU hw hyU
        (hga x y hy).continuousAt (hga yU y (hVx yU)).continuousAt hevent
    simpa only [G, dif_pos hyU] using hval.symm
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    let xU : U := ⟨x, hx⟩
    have hevent : g xU =ᶠ[𝓝 x] G := by
      filter_upwards [(hVo xU).mem_nhds (hVx xU)] with y hy
      exact (hagree xU y hy).symm
    exact (hga xU x (hVx xU)).congr hevent
  · intro y hy
    let yU : U := ⟨y, hy⟩
    rw [hagree yU y (hVx yU)]
    exact hge yU y (hVx yU)

end NlsGge.Analysis.AnalyticDivisionGluing
