import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1Xsb

/-! # Track B, step B1: the time half of the physical-side `L⁴` identity

For time-side Schwartz functions `s_k` (the spatial Fourier modes `v̂_k(t)` of a dense-class
spacetime function) put `θ_k = 𝓕⁻ s_k`. Mathlib defines the Schwartz convolution by
`f ⋆ g = 𝓕⁻(𝓕f · 𝓕g)`, so `Σ_k s_k s_{m-k} = 𝓕(Σ_k θ_k ⋆ θ_{m-k})`; Plancherel then gives
`∫ |Σ_k s_k(t) s_{m-k}(t)|² dt ≤ ∫ (Σ_k ∫ |θ_k(η)| |θ_{m-k}(ξ-η)| dη)² dξ`,
which is the left side of the Fourier-side bilinear estimate (`PdeB1L4Core`) up to the change
of variables `λ = -2πη`, `τ = -2πξ`. All quantities are in `ℝ≥0∞`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory SchwartzMap FourierTransform
open scoped ENNReal

/-- Plancherel for Schwartz functions, in `ℝ≥0∞`: `∫ |𝓕h|² = ∫ |h|²`. -/
theorem lintegral_enorm_sq_fourier_schwartz (h : 𝓢(ℝ, ℂ)) :
    ∫⁻ ξ, ‖(𝓕 h) ξ‖ₑ ^ 2 = ∫⁻ t, ‖h t‖ₑ ^ 2 := by
  have e : ∀ g : 𝓢(ℝ, ℂ), ∫⁻ t, ‖g t‖ₑ ^ 2 = ‖g.toLp 2‖ₑ ^ 2 := fun g => by
    rw [← lintegral_enorm_sq_eq]
    exact lintegral_congr_ae ((g.coeFn_toLp 2 volume).mono fun x hx => by simp only [hx])
  have hT : 𝓕 (h.toLp 2) = (𝓕 h).toLp 2 := SchwartzMap.toLp_fourier_eq h
  have hn : ‖𝓕 (h.toLp 2)‖ₑ = ‖h.toLp 2‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    ext
    simp only [coe_nnnorm]
    exact MeasureTheory.Lp.norm_fourier_eq _
  rw [e (𝓕 h), e h, ← hT, hn]

/-- The product of two time-side Schwartz functions is the Fourier transform of the convolution
of their inverse transforms. -/
theorem mul_eq_fourier_convolution (f g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    f t * g t = 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ f) (𝓕⁻ g)) t := by
  rw [fourier_convolution, pairing_apply_apply]
  simp

/-- **Time half of the `L⁴` identity.** For a family `s` of time-side Schwartz functions and a
finite set `S`, with `θ_k = 𝓕⁻ s_k`:
`∫ |Σ_{k∈S} s_k s_{m-k}|² ≤ ∫ (Σ_{k∈S} ∫ |θ_k(η)| |θ_{m-k}(ξ-η)| dη)² dξ`. -/
theorem lintegral_sq_sum_mul_le (S : Finset ℤ) (s : ℤ → 𝓢(ℝ, ℂ)) (m : ℤ) :
    ∫⁻ t, ‖∑ k ∈ S, s k t * s (m - k) t‖ₑ ^ 2 ≤
      ∫⁻ ξ, (∑ k ∈ S, ∫⁻ η, ‖(𝓕⁻ (s k)) η‖ₑ * ‖(𝓕⁻ (s (m - k))) (ξ - η)‖ₑ) ^ 2 := by
  set B := ContinuousLinearMap.mul ℂ ℂ
  set h : 𝓢(ℝ, ℂ) := ∑ k ∈ S, SchwartzMap.convolution B (𝓕⁻ (s k)) (𝓕⁻ (s (m - k))) with hh
  have hF : ∀ t, ∑ k ∈ S, s k t * s (m - k) t = (𝓕 h) t := fun t => by
    rw [hh, fourier_sum, sum_apply]
    exact Finset.sum_congr rfl fun k _ => mul_eq_fourier_convolution _ _ t
  simp_rw [hF]
  rw [lintegral_enorm_sq_fourier_schwartz]
  refine lintegral_mono fun ξ => ?_
  gcongr
  rw [hh, sum_apply]
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [SchwartzMap.convolution_apply, convolution_def]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1
  funext η
  simp [B, enorm_mul]

end LiebLiniger.FixedPeriod.ALLS.PdeB
