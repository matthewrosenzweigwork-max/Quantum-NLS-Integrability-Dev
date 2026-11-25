import Mathlib
import NlsGge.Atomic.G1.G1080

/- G5-029 SUPPORT 1 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5029Sup1.lean, namespace NlsGge.GKDefinitionDesign.
   Head `isospectral_subsequence_of_base_tendsto` VERBATIM from PRO_DEFINITION_RESPONSE_FP80_14.md "G5029: all-left density".
   Route (Pro): same proof as landed G1080 g1080_compact with the constant base replaced by the convergent v_j:
   equal mass (g1080_norm_eq), bounded Hilbert weak subsequence (LIB082), weak continuity of discrim, weak + norm convergence is strong. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem isospectral_subsequence_of_base_tendsto
    (u : PhysicalL2) (v w : ℕ → PhysicalL2)
    (hv : Tendsto v atTop (𝓝 u))
    (hw : ∀ j : ℕ, isospectral (v j) (w j)) :
  ∃ (s : ℕ → ℕ) (wlim : PhysicalL2), StrictMono s ∧
    Tendsto (w ∘ s) atTop (𝓝 wlim) ∧ isospectral u wlim := by
  haveI := NlsGge.Atomic.G6Sup.physicalL2_separable
  have hnorm : ∀ j, ‖w j‖ = ‖v j‖ := fun j => g1080_norm_eq (v j) (w j) (hw j)
  have hb : ∃ C : ℝ, ∀ n, ‖w n‖ ≤ C := by
    obtain ⟨C, hC⟩ := hv.norm.bddAbove_range
    exact ⟨C, fun n => by rw [hnorm n]; exact hC ⟨n, rfl⟩⟩
  obtain ⟨s, hs, wl, hwl⟩ : ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ x : PhysicalL2, ∀ y : PhysicalL2,
      Tendsto (fun n => (inner ℂ y (w (s n))).re) atTop (𝓝 (inner ℂ y x).re) := by
    letI : InnerProductSpace ℝ PhysicalL2 := InnerProductSpace.rclikeToReal ℂ PhysicalL2
    exact NlsGge.Atomic.LIB.bounded_hilbert_weak_subsequence (E := PhysicalL2) w hb
  have hweak : IsWeakLim (w ∘ s) wl := g1080_weakLim_of_re hwl
  have hD := discrim_weakContinuous (weakLim_realSlice38 hweak)
  have hvs : Tendsto (v ∘ s) atTop (𝓝 u) := hv.comp hs.tendsto_atTop
  have hiso : isospectral u wl := by
    intro z
    have h1 : Tendsto (fun k => discrim (realSlice (w (s k))) z) atTop
        (𝓝 (discrim (realSlice wl) z)) :=
      (hD.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ z)
    have hc : Continuous (fun x : PhysicalL2 => discrim (realSlice x) z) :=
      Continuous.comp (g := fun p : PhysicalL2 × ℂ => discrim (realSlice p.1) p.2)
        (f := fun x : PhysicalL2 => (x, z)) continuous_discrim_realSlice_joint
        (Continuous.prodMk (continuous_id (X := PhysicalL2)) (continuous_const (y := z)))
    have h2 : Tendsto (fun k => discrim (realSlice (w (s k))) z) atTop
        (𝓝 (discrim (realSlice u) z)) := by
      have h3 := (hc.tendsto u).comp hvs
      refine h3.congr (fun k => ?_)
      exact (hw (s k) z).symm
    exact tendsto_nhds_unique h1 h2
  refine ⟨s, wl, hs, ?_, hiso⟩
  have hnv : ‖wl‖ = ‖u‖ := g1080_norm_eq u wl hiso
  have hin : Tendsto (fun k => (inner ℂ (w (s k)) wl).re) atTop (𝓝 (inner ℂ wl wl).re) := by
    have e1 : ∀ y : PhysicalL2, (inner ℂ y wl).re = (inner ℂ wl y).re := fun y => by
      rw [← inner_conj_symm (𝕜 := ℂ) wl y, Complex.conj_re]
    simp_rw [e1]
    exact hwl wl
  have hnt : Tendsto (fun k => ‖w (s k)‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2)) := by
    have := (hvs.norm).pow 2
    simpa only [Function.comp_apply, hnorm] using this
  have hsq : Tendsto (fun k => ‖w (s k) - wl‖ ^ 2) atTop (𝓝 0) := by
    have e : ∀ k, ‖w (s k) - wl‖ ^ 2 = ‖w (s k)‖ ^ 2 - 2 * (inner ℂ (w (s k)) wl).re + ‖u‖ ^ 2 :=
      fun k => by rw [norm_sub_sq (𝕜 := ℂ), hnv]; rfl
    simp_rw [e]
    have := (hnt.sub (hin.const_mul 2)).add_const (‖u‖ ^ 2)
    have hvv : (inner ℂ wl wl).re = ‖wl‖ ^ 2 := by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) wl
      simpa using this
    rw [hvv, hnv] at this
    have e0 : ‖u‖ ^ 2 - 2 * ‖u‖ ^ 2 + ‖u‖ ^ 2 = 0 := by ring
    rw [e0] at this
    exact this
  have h0 : Tendsto (fun k => ‖w (s k) - wl‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact (tendsto_iff_norm_sub_tendsto_zero).2 h0

end
end NlsGge.GKDefinitionDesign
