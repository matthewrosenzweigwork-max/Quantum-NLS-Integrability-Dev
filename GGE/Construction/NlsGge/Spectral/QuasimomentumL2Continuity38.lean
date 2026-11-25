import NlsGge.Spectral.ActualQuasimomentumContinuityE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # R2 (TF-H^k): `u ↦ k_u(z)` is continuous in `L²` at interior points `z` (campaign 38)

The segment-continuation argument of E03-cont C2 started at the interior point `z` (`Im z > 0`) instead of
a real point: `sin k_{u₀}` never vanishes on `z + i[0,T]` (since `Im k > 0`), so no hypothesis on
`Δ_{u₀}` is needed. Hölder-½ in the `L²` distance, uniformly on `H¹` balls. -/

/-- **R2.** Hölder-½ continuity of `k_u(z)` in `u` (L² distance), uniform on an `H¹` ball, for `Im z > 0`. -/
theorem actualQuasimomentum_holder_in_u_E02_38 (u₀ : PhysicalL2)
    (hu₀ : SobolevSquareSummable 1 (physicalFourier u₀)) (B : ℝ) (hB : 1 ≤ B)
    (hu₀B : ‖physicalSobolevL2 1 u₀ hu₀‖ ≤ B) (z : ℂ) (hz : 0 < z.im) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ (u : PhysicalL2)
      (hu : SobolevSquareSummable 1 (physicalFourier u)), ‖physicalSobolevL2 1 u hu‖ ≤ B →
      ‖u - u₀‖ ≤ δ →
        ‖actualQuasimomentumE02_38 u z - actualQuasimomentumE02_38 u₀ z‖ ≤
          6 * Real.sqrt (C * ‖u - u₀‖) := by
  obtain ⟨X, hX, hext⟩ := actualQuasimomentum_uniformExterior_E02_38 B hB
  set T : ℝ := X + 2
  have hT0 : 0 ≤ T := by simp only [T]; linarith
  let seg : ℝ → ℂ := fun t => z + Complex.I * (t:ℂ)
  have hseg_im : ∀ t : ℝ, (seg t).im = z.im + t := by intro t; simp [seg]
  have hseg_c : Continuous seg := by fun_prop
  have hseg_pos : ∀ t : ℝ, 0 ≤ t → 0 < (seg t).im := by
    intro t ht; rw [hseg_im]; linarith
  have hseg_norm : ∀ t ∈ Icc (0:ℝ) T, ‖seg t‖ ≤ ‖z‖ + T := by
    intro t ht
    calc ‖seg t‖ ≤ ‖z‖ + ‖Complex.I * (t:ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + |t| := by simp
      _ ≤ ‖z‖ + T := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
  have hcont : ∀ v : PhysicalL2,
      ContinuousOn (fun t => actualQuasimomentumClosedE02_38 v (seg t)) (Icc 0 T) := by
    intro v
    refine (continuousOn_extend_actualQuasimomentumE02_38 v).comp hseg_c.continuousOn ?_
    intro t ht
    show 0 ≤ (seg t).im
    exact (hseg_pos t ht.1).le
  set g : ℝ → ℂ := fun t => actualQuasimomentumClosedE02_38 u₀ (seg t)
  have hsin_ne : ∀ t ∈ Icc (0:ℝ) T, Complex.sin (g t) ≠ 0 := by
    intro t ht hzero
    have hpos' := hseg_pos t ht.1
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp hzero
    have him := (isActualQuasimomentumBranch_actualQuasimomentumE02_38 u₀).2.2.1 _ hpos'
    have : (g t).im = 0 := by rw [hm]; simp
    simp only [g] at this
    rw [actualQuasimomentumClosed_eq_of_pos_E02_38 u₀ _ hpos'] at this
    linarith
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT0)
    ((Complex.continuous_sin.comp_continuousOn (hcont u₀)).norm)
  set s₀ := ‖Complex.sin (g t₀)‖
  have hs₀ : 0 < s₀ := norm_pos_iff.mpr (hsin_ne t₀ ht₀)
  set ρ : ℝ := min 1 (s₀ / 2)
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρ : ∀ t ∈ Icc (0:ℝ) T, ∀ m : ℤ, ρ ≤ ‖g t - (m:ℂ) * Real.pi‖ := by
    intro t ht m
    by_contra hlt
    push Not at hlt
    have h1 := norm_sin_le_two_mul_E02_38 (g t - (m:ℂ) * Real.pi) (by linarith)
    rw [norm_sin_sub_int_mul_pi_E02_38] at h1
    have h2 : s₀ ≤ ‖Complex.sin (g t)‖ := hmin ht
    have h3 : ρ ≤ s₀ / 2 := min_le_right _ _
    linarith
  obtain ⟨C, hC0, hLip⟩ := actualPhysicalUnitHalfTrace_lipschitz_E02_38 (‖u₀‖ + 1) (‖z‖ + T)
    (by positivity) (by positivity)
  refine ⟨C, hC0, min 1 (ρ^2 / (200 * (C + 1))), lt_min one_pos (by positivity), ?_⟩
  intro u hu huB hδ
  have hδ1 : ‖u - u₀‖ ≤ 1 := le_trans hδ (min_le_left _ _)
  have hδ2 : ‖u - u₀‖ ≤ ρ^2 / (200 * (C + 1)) := le_trans hδ (min_le_right _ _)
  set η := C * ‖u - u₀‖
  have hη0 : 0 ≤ η := mul_nonneg hC0 (norm_nonneg _)
  have hηρ : η ≤ ρ^2 / 200 := by
    have h1 : C * ‖u - u₀‖ ≤ (C + 1) * ‖u - u₀‖ := by nlinarith [norm_nonneg (u - u₀)]
    have h2 : (C + 1) * ‖u - u₀‖ ≤ (C + 1) * (ρ^2 / (200 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hδ2 (by linarith)
    have h3 : (C + 1) * (ρ^2 / (200 * (C + 1))) = ρ^2 / 200 := by field_simp
    linarith
  have hsq : Real.sqrt η ≤ ρ / 13 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg ρ]
  have hu_norm : ‖u‖ ≤ ‖u₀‖ + 1 := by
    calc ‖u‖ ≤ ‖u₀‖ + ‖u - u₀‖ := by
          have := norm_add_le u₀ (u - u₀); simpa using this
      _ ≤ ‖u₀‖ + 1 := by linarith
  set f : ℝ → ℂ := fun t => actualQuasimomentumClosedE02_38 u (seg t)
  have hTm : T ∈ Icc (0:ℝ) T := ⟨hT0, le_rfl⟩
  have hTpos : 0 < (seg T).im := hseg_pos T hT0
  have hTX : X ≤ ‖seg T‖ := by
    have := Complex.abs_im_le_norm (seg T)
    rw [hseg_im, abs_of_pos (by linarith)] at this
    simp only [T] at this ⊢; linarith
  have hfT : f T = actualQuasimomentumE02_38 u (seg T) :=
    actualQuasimomentumClosed_eq_of_pos_E02_38 u _ hTpos
  have hgT : g T = actualQuasimomentumE02_38 u₀ (seg T) :=
    actualQuasimomentumClosed_eq_of_pos_E02_38 u₀ _ hTpos
  have e1 := hext u hu huB (seg T) hTpos hTX
  have e2 := hext u₀ hu₀ hu₀B (seg T) hTpos hTX
  have hmain := segment_continuation_E02_38 f g T η ρ hT0 (hcont u) (hcont u₀) hρ0 hρ hη0
    (by linarith) (by linarith)
    (by
      intro t ht
      have h0 : 0 ≤ (seg t).im := (hseg_pos t ht.1).le
      simp only [f, g]
      rw [actualQuasimomentumClosed_cos_E02_38 u _ h0, actualQuasimomentumClosed_cos_E02_38 u₀ _ h0]
      exact hLip u u₀ hu_norm (by linarith) (seg t) (hseg_norm t ht))
    (by
      rw [hfT, hgT]
      have : actualQuasimomentumE02_38 u (seg T) - actualQuasimomentumE02_38 u₀ (seg T) =
          (actualQuasimomentumE02_38 u (seg T) - seg T) -
            (actualQuasimomentumE02_38 u₀ (seg T) - seg T) := by ring
      rw [this]
      have := norm_sub_le (actualQuasimomentumE02_38 u (seg T) - seg T)
        (actualQuasimomentumE02_38 u₀ (seg T) - seg T)
      linarith)
    (by
      rw [hgT]
      have h1 := Complex.abs_im_le_norm (actualQuasimomentumE02_38 u₀ (seg T) - seg T)
      rw [Complex.sub_im, hseg_im] at h1
      have h2 := (abs_le.mp (le_trans h1 e2)).1
      simp only [T] at h2 ⊢; linarith)
    (by
      rw [hfT]
      exact ((isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).2.2.1 _ hTpos).le)
  have h0m : (0:ℝ) ∈ Icc (0:ℝ) T := ⟨le_rfl, hT0⟩
  have := hmain 0 h0m
  have hs0 : seg 0 = z := by simp [seg]
  simp only [f, g, hs0] at this
  rwa [actualQuasimomentumClosed_eq_of_pos_E02_38 u z hz,
    actualQuasimomentumClosed_eq_of_pos_E02_38 u₀ z hz] at this

/-- **R2, sequence form.** If `u_N → u` in `L²` with `u_N` bounded in `H¹` and `u ∈ H¹`, then
`k_{u_N}(z) → k_u(z)` for every `z` with `Im z > 0` (in particular `z = iη`, `η > 0`). -/
theorem actualQuasimomentum_tendsto_of_L2_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (B : ℝ) (hB : 1 ≤ B)
    (huB : ‖physicalSobolevL2 1 u hu‖ ≤ B)
    (uN : ℕ → PhysicalL2) (hN : ∀ N, SobolevSquareSummable 1 (physicalFourier (uN N)))
    (hNB : ∀ N, ‖physicalSobolevL2 1 (uN N) (hN N)‖ ≤ B)
    (hconv : Tendsto (fun N => ‖uN N - u‖) atTop (𝓝 0)) (z : ℂ) (hz : 0 < z.im) :
    Tendsto (fun N => actualQuasimomentumE02_38 (uN N) z) atTop
      (𝓝 (actualQuasimomentumE02_38 u z)) := by
  obtain ⟨C, hC0, δ, hδ, h⟩ := actualQuasimomentum_holder_in_u_E02_38 u hu B hB huB z hz
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun N => 6 * Real.sqrt (C * ‖uN N - u‖)) atTop (𝓝 (6 * Real.sqrt (C * 0))) :=
    (((hconv.const_mul C).sqrt).const_mul 6)
  simp only [mul_zero, Real.sqrt_zero] at hb
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hb
  filter_upwards [(Metric.tendsto_atTop.mp hconv) δ hδ |> fun h => Filter.eventually_atTop.mpr h]
    with N hNδ
  have := hNδ
  exact h (uN N) (hN N) (hNB N) (by
    have := hNδ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact this.le)

end NlsGge.SpectralFoundations
end
