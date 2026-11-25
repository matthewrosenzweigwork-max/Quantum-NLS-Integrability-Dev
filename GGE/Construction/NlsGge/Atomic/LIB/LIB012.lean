import Mathlib.Analysis.Complex.RemovableSingularity

/-! Bounded holomorphic functions on a punctured disc extend uniquely. -/

open Filter Metric Set
open scoped Filter Topology

set_option autoImplicit false

namespace NlsGge.Atomic

/-- A bounded holomorphic function on a punctured disc has a unique holomorphic
extension to the disc. Completeness of the target is required by the removable
singularity limit construction. -/
theorem removable_bounded_puncture
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball c r \ {c}))
    (hbound : BddAbove (Set.image norm (Set.image f (ball c r \ {c})))) :
    ∃ g, AnalyticOnNhd ℂ g (ball c r) ∧ EqOn g f (ball c r \ {c}) ∧
      ∀ g', (AnalyticOnNhd ℂ g' (ball c r) ∧ EqOn g' f (ball c r \ {c})) →
        EqOn g' g (ball c r) := by
  have hc : ball c r ∈ 𝓝 c := Metric.ball_mem_nhds c hr
  have hd : DifferentiableOn ℂ f (ball c r \ {c}) := hf.differentiableOn
  have hb : BddAbove (norm ∘ f '' (ball c r \ {c})) := by
    simpa only [Function.comp_apply, Set.image_image] using hbound
  let g : ℂ → E := Function.update f c (limUnder (𝓝[≠] c) f)
  have hgdiff : DifferentiableOn ℂ g (ball c r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hc hd hb
  have hgan : AnalyticOnNhd ℂ g (ball c r) := hgdiff.analyticOnNhd isOpen_ball
  have hgeq : EqOn g f (ball c r \ {c}) := by
    intro z hz
    simp [g, Function.update_of_ne (by simpa using hz.2)]
  refine ⟨g, hgan, hgeq, ?_⟩
  intro g' hg' z hzball
  by_cases hzc : z = c
  · subst z
    have hgt : Tendsto g' (𝓝[≠] c) (𝓝 (g' c)) :=
      (hg'.1 c (Metric.mem_ball_self hr)).continuousAt.mono_left nhdsWithin_le_nhds
    have htg : Tendsto g (𝓝[≠] c) (𝓝 (g c)) :=
      hgan c (Metric.mem_ball_self hr) |>.continuousAt.mono_left nhdsWithin_le_nhds
    have heq : g' =ᶠ[𝓝[≠] c] g := by
      change ∀ᶠ z in nhdsWithin c ({c}ᶜ), g' z = g z
      rw [eventually_nhdsWithin_iff]
      refine (eventually_mem_nhds_iff.2 hc).mono ?_
      intro z hz hzne
      have hzball : z ∈ ball c r := mem_of_mem_nhds hz
      have hzg' := hg'.2 ⟨hzball, by simpa using hzne⟩
      have hzg := hgeq ⟨hzball, by simpa using hzne⟩
      exact hzg'.trans hzg.symm
    exact tendsto_nhds_unique (hgt.congr' heq) htg
  · have hzg' := hg'.2 ⟨hzball, by simpa using hzc⟩
    have hzg := hgeq ⟨hzball, by simpa using hzc⟩
    exact hzg'.trans hzg.symm

/-- If the original function was continuous at the center, its assigned value is
already the removable extension value. -/
theorem removable_update_eq_self_of_continuousAt
    {E : Type*} [TopologicalSpace E] [T2Space E] [Nonempty E]
    {f : ℂ → E} {c : ℂ} (hc : ContinuousAt f c) :
    Function.update f c (limUnder (𝓝[≠] c) f) = f := by
  have hlim : limUnder (𝓝[≠] c) f = f c :=
    (hc.mono_left nhdsWithin_le_nhds).limUnder_eq
  funext z
  by_cases hz : z = c
  · subst z
    simp [hlim]
  · simp [Function.update_of_ne hz]

end NlsGge.Atomic
