import NlsGge.Spectral.ActualQuasimomentumUniformExteriorE02_38
import NlsGge.Spectral.ActualHalfTraceLipschitzE02_38
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # E03-cont C2: continuity of the boundary quasimomentum in the potential (campaign 38)

At a real point `x` with `Δ_{u₀}(x)² ≠ 4` (i.e. `Δh_{u₀}(x)² ≠ 1`), the boundary value `k_u(x+i0)` is
Hölder-½ in `u` (L² distance), uniformly on H¹ balls. Route: `cos a - cos b = -2 sin((a+b)/2) sin((a-b)/2)`
forces `a ≈ ±b (mod 2π)`; continuation along the vertical segment `x + i[0,T]` from the uniform exterior
anchor `|k - z| ≤ 1/4` selects `+` and `m = 0`. -/

theorem norm_sin_sq_E02_38 (w : ℂ) :
    ‖Complex.sin w‖^2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  have h1 := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  ring_nf
  nlinarith [h1, h2]

/-- `|sin w| ≤ δ` forces `w` within `3δ` of `πℤ`. -/
theorem exists_int_near_of_norm_sin_le_E02_38 (w : ℂ) (δ : ℝ) (h : ‖Complex.sin w‖ ≤ δ) :
    ∃ m : ℤ, ‖w - (m:ℂ) * Real.pi‖ ≤ 3 * δ := by
  have hsq := norm_sin_sq_E02_38 w
  have hn0 : 0 ≤ ‖Complex.sin w‖ := norm_nonneg _
  have hsx : |Real.sin w.re| ≤ ‖Complex.sin w‖ := by
    have : Real.sin w.re ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by nlinarith [sq_nonneg (Real.sinh w.im)]
    have := sq_le_sq.mp this
    rwa [abs_of_nonneg hn0] at this
  have hsy : |Real.sinh w.im| ≤ ‖Complex.sin w‖ := by
    have : Real.sinh w.im ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by nlinarith [sq_nonneg (Real.sin w.re)]
    have := sq_le_sq.mp this
    rwa [abs_of_nonneg hn0] at this
  have hy : |w.im| ≤ δ := by
    have h1 : |w.im| ≤ Real.sinh |w.im| := Real.self_le_sinh_iff.mpr (abs_nonneg _)
    rw [← Real.abs_sinh] at h1
    linarith
  set m : ℤ := round (w.re / Real.pi)
  have hpi := Real.pi_pos
  set r : ℝ := w.re - m * Real.pi
  have hr : |r| ≤ Real.pi / 2 := by
    have h := abs_sub_round (w.re / Real.pi)
    have : r = (w.re / Real.pi - m) * Real.pi := by
      simp only [r]; field_simp
    rw [this, abs_mul, abs_of_pos hpi]
    nlinarith
  have hsr : |Real.sin r| = |Real.sin w.re| := by
    simp only [r]
    rw [Real.sin_sub_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have hjr : 2 / Real.pi * |r| ≤ |Real.sin r| := by
    rcases le_total 0 r with h0 | h0
    · rw [abs_of_nonneg h0]
      have := Real.mul_le_sin h0 (by rw [abs_of_nonneg h0] at hr; exact hr)
      exact le_trans this (le_abs_self _)
    · have h0' : 0 ≤ -r := by linarith
      have := Real.mul_le_sin h0' (by rw [abs_of_nonpos h0] at hr; exact hr)
      rw [abs_of_nonpos h0, Real.sin_neg] at *
      exact le_trans this (neg_le_abs _)
  have hrb : |r| ≤ Real.pi / 2 * δ := by
    have h3 : 2 / Real.pi * |r| ≤ δ := by linarith
    have : |r| = Real.pi / 2 * (2 / Real.pi * |r|) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  refine ⟨m, ?_⟩
  have hre : (w - (m:ℂ) * Real.pi).re = r := by simp [r]
  have him : (w - (m:ℂ) * Real.pi).im = w.im := by simp
  have hδ : 0 ≤ δ := le_trans hn0 h
  calc ‖w - (m:ℂ) * Real.pi‖ ≤ |(w - (m:ℂ) * Real.pi).re| + |(w - (m:ℂ) * Real.pi).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |r| + |w.im| := by rw [hre, him]
    _ ≤ Real.pi / 2 * δ + δ := add_le_add hrb hy
    _ ≤ 3 * δ := by nlinarith [Real.pi_le_four]

theorem norm_sin_le_two_mul_E02_38 (w : ℂ) (hw : ‖w‖ ≤ 1) : ‖Complex.sin w‖ ≤ 2 * ‖w‖ := by
  have h1 : ‖-w * Complex.I‖ ≤ 1 := by simpa using hw
  have h2 : ‖w * Complex.I‖ ≤ 1 := by simpa using hw
  have e1 := Complex.norm_exp_sub_one_le h1
  have e2 := Complex.norm_exp_sub_one_le h2
  have hs : Complex.sin w = ((Complex.exp (-w * Complex.I) - 1) - (Complex.exp (w * Complex.I) - 1))
      * Complex.I / 2 := by rw [Complex.sin]; ring
  rw [hs, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have := norm_sub_le (Complex.exp (-w * Complex.I) - 1) (Complex.exp (w * Complex.I) - 1)
  simp only [neg_mul, norm_neg, norm_mul, Complex.norm_I, mul_one] at e1 e2 this ⊢
  linarith

theorem norm_sin_sub_int_mul_pi_E02_38 (w : ℂ) (m : ℤ) :
    ‖Complex.sin (w - (m:ℂ) * Real.pi)‖ = ‖Complex.sin w‖ := by
  rw [Complex.sin_antiperiodic.sub_int_mul_eq m]
  rcases Int.units_eq_one_or m.negOnePow with h | h <;> simp [h]

/-- `cos a ≈ cos b` forces `a ≈ b` or `a ≈ -b` modulo `2π`. -/
theorem cos_close_dichotomy_E02_38 (a b : ℂ) (η : ℝ) (hη : 0 ≤ η)
    (h : ‖Complex.cos a - Complex.cos b‖ ≤ η) :
    (∃ m : ℤ, ‖a - b - 2 * (m:ℂ) * Real.pi‖ ≤ 6 * Real.sqrt η) ∨
    (∃ m : ℤ, ‖a + b - 2 * (m:ℂ) * Real.pi‖ ≤ 6 * Real.sqrt η) := by
  rw [Complex.cos_sub_cos, norm_mul, norm_mul, norm_neg, Complex.norm_two] at h
  set sA := ‖Complex.sin ((a + b) / 2)‖
  set sB := ‖Complex.sin ((a - b) / 2)‖
  have hA0 : 0 ≤ sA := norm_nonneg _
  have hB0 : 0 ≤ sB := norm_nonneg _
  have hs := Real.sq_sqrt hη
  have hs0 := Real.sqrt_nonneg η
  by_cases hB : sB ≤ Real.sqrt η
  · left
    obtain ⟨m, hm⟩ := exists_int_near_of_norm_sin_le_E02_38 _ _ hB
    refine ⟨m, ?_⟩
    have : a - b - 2 * (m:ℂ) * Real.pi = 2 * ((a - b) / 2 - (m:ℂ) * Real.pi) := by ring
    rw [this, norm_mul, Complex.norm_two]
    linarith
  · right
    have hA : sA ≤ Real.sqrt η := by
      by_contra hA
      push Not at hA hB
      nlinarith [mul_lt_mul'' hA hB hs0 hs0]
    obtain ⟨m, hm⟩ := exists_int_near_of_norm_sin_le_E02_38 _ _ hA
    refine ⟨m, ?_⟩
    have : a + b - 2 * (m:ℂ) * Real.pi = 2 * ((a + b) / 2 - (m:ℂ) * Real.pi) := by ring
    rw [this, norm_mul, Complex.norm_two]
    linarith

/-- Continuation along a segment: if `cos f ≈ cos g` on `[0,T]`, `g` stays `ρ` away from `πℤ`, and at
the top `f ≈ g` with `Im g ≥ 1`, then `f ≈ g` on all of `[0,T]`. -/
theorem segment_continuation_E02_38 (f g : ℝ → ℂ) (T η ρ : ℝ) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T)) (hρ0 : 0 < ρ)
    (hρ : ∀ t ∈ Icc 0 T, ∀ m : ℤ, ρ ≤ ‖g t - (m:ℂ) * Real.pi‖)
    (hη : 0 ≤ η) (hε1 : 6 * Real.sqrt η < 1/2) (hερ : 6 * Real.sqrt η ≤ ρ / 2)
    (hcos : ∀ t ∈ Icc 0 T, ‖Complex.cos (f t) - Complex.cos (g t)‖ ≤ η)
    (htop : ‖f T - g T‖ ≤ 1/2) (hgT : 1 ≤ (g T).im) (hfT : 0 ≤ (f T).im) :
    ∀ t ∈ Icc 0 T, ‖f t - g t‖ ≤ 6 * Real.sqrt η := by
  set ε := 6 * Real.sqrt η
  have hε0 : 0 ≤ ε := by positivity
  have hpi := Real.pi_gt_three
  set L := min (2 * Real.pi - ε) (2 * ρ - ε)
  have hLε : ε < L := lt_min (by linarith) (by linarith)
  -- pointwise dichotomy
  have hdich : ∀ t ∈ Icc 0 T, ‖f t - g t‖ ≤ ε ∨ 2 * Real.pi - ε ≤ ‖f t - g t‖ ∨
      ∃ m : ℤ, ‖f t + g t - 2 * (m:ℂ) * Real.pi‖ ≤ ε := by
    intro t ht
    rcases cos_close_dichotomy_E02_38 (f t) (g t) η hη (hcos t ht) with ⟨m, hm⟩ | ⟨m, hm⟩
    · by_cases hm0 : m = 0
      · left; simpa [hm0] using hm
      · right; left
        have h1 : (1:ℝ) ≤ |(m:ℝ)| := by
          have : (1:ℤ) ≤ |m| := Int.one_le_abs hm0
          exact_mod_cast this
        have h2 : ‖2 * (m:ℂ) * Real.pi‖ = 2 * |(m:ℝ)| * Real.pi := by
          rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos]
          simp
        have h3 := norm_sub_norm_le (2 * (m:ℂ) * Real.pi) (f t - g t)
        have h4 : ‖2 * (m:ℂ) * Real.pi - (f t - g t)‖ = ‖f t - g t - 2 * (m:ℂ) * Real.pi‖ := by
          rw [← norm_neg]; ring_nf
        nlinarith
    · right; right; exact ⟨m, hm⟩
  have hsep : ∀ t ∈ Icc 0 T, ‖f t - g t‖ ≤ ε ∨ L ≤ ‖f t - g t‖ := by
    intro t ht
    rcases hdich t ht with h | h | ⟨m, hm⟩
    · exact Or.inl h
    · exact Or.inr (le_trans (min_le_left _ _) h)
    · right
      refine le_trans (min_le_right _ _) ?_
      have hρt := hρ t ht m
      have : f t - g t = (f t + g t - 2 * (m:ℂ) * Real.pi) - 2 * (g t - (m:ℂ) * Real.pi) := by ring
      rw [this]
      have h5 := norm_sub_norm_le (2 * (g t - (m:ℂ) * Real.pi)) (f t + g t - 2 * (m:ℂ) * Real.pi)
      rw [norm_mul, Complex.norm_two] at h5
      rw [← norm_neg]
      have : -((f t + g t - 2 * (m:ℂ) * Real.pi) - 2 * (g t - (m:ℂ) * Real.pi)) =
          2 * (g t - (m:ℂ) * Real.pi) - (f t + g t - 2 * (m:ℂ) * Real.pi) := by ring
      rw [this]
      linarith
  have hTm : T ∈ Icc (0:ℝ) T := ⟨hT, le_rfl⟩
  have htopε : ‖f T - g T‖ ≤ ε := by
    rcases hdich T hTm with h | h | ⟨m, hm⟩
    · exact h
    · exfalso
      linarith
    · exfalso
      have h6 := Complex.abs_im_le_norm (f T + g T - 2 * (m:ℂ) * Real.pi)
      have h7 : (f T + g T - 2 * (m:ℂ) * Real.pi).im = (f T).im + (g T).im := by simp
      rw [h7, abs_of_nonneg (by linarith)] at h6
      linarith
  intro t ht
  rcases hsep t ht with h | h
  · exact h
  exfalso
  have hφ : ContinuousOn (fun s => ‖f s - g s‖) (Icc 0 T) := (hf.sub hg).norm
  have hpc : IsPreconnected ((fun s => ‖f s - g s‖) '' Icc 0 T) :=
    isPreconnected_Icc.image _ hφ
  have hsub := hpc.Icc_subset (mem_image_of_mem _ hTm) (mem_image_of_mem _ ht)
  have hc : (ε + L) / 2 ∈ Icc ‖f T - g T‖ ‖f t - g t‖ := ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hseq⟩ := hsub hc
  simp only at hseq
  rcases hsep s hs with h' | h' <;> linarith

/-- The extension of `k_u` to the closed upper half-plane. -/
def actualQuasimomentumClosedE02_38 (u : PhysicalL2) : ℂ → ℂ :=
  extendFrom {z : ℂ | 0 < z.im} (actualQuasimomentumE02_38 u)

theorem actualQuasimomentumClosed_eq_of_pos_E02_38 (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    actualQuasimomentumClosedE02_38 u z = actualQuasimomentumE02_38 u z := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  exact extendFrom_eq (mem_closure_upperHalfPlane_E02_38 hz.le)
    (((hk.1 z hz).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)

theorem actualQuasimomentumClosed_ofReal_E02_38 (u : PhysicalL2) (x : ℝ) :
    actualQuasimomentumClosedE02_38 u (x:ℂ) = actualQuasimomentumBoundaryE02_38 u x := rfl

theorem actualQuasimomentumClosed_cos_E02_38 (u : PhysicalL2) (z : ℂ) (hz : 0 ≤ z.im) :
    Complex.cos (actualQuasimomentumClosedE02_38 u z) = actualPhysicalUnitHalfTrace32 u z := by
  rcases lt_or_eq_of_le hz with hpos | hzero
  · rw [actualQuasimomentumClosed_eq_of_pos_E02_38 u z hpos]
    exact (isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).2.1 z hpos
  · have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
    rw [hz', actualQuasimomentumClosed_ofReal_E02_38]
    exact actualQuasimomentumBoundaryE02_38_cos u z.re

/-- **E03-cont C2.** Hölder-½ continuity of the boundary quasimomentum in `u` at a real point with
`Δh_{u₀}(x)² ≠ 1`, uniformly on an H¹ ball. -/
theorem actualQuasimomentumBoundary_holder_in_u_E02_38 (u₀ : PhysicalL2)
    (hu₀ : SobolevSquareSummable 1 (physicalFourier u₀)) (B : ℝ) (hB : 1 ≤ B)
    (hu₀B : ‖physicalSobolevL2 1 u₀ hu₀‖ ≤ B) (x : ℝ)
    (hx : actualPhysicalUnitHalfTrace32 u₀ (x:ℂ) ^ 2 ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ (u : PhysicalL2)
      (hu : SobolevSquareSummable 1 (physicalFourier u)), ‖physicalSobolevL2 1 u hu‖ ≤ B →
      ‖u - u₀‖ ≤ δ →
        ‖actualQuasimomentumBoundaryE02_38 u x - actualQuasimomentumBoundaryE02_38 u₀ x‖ ≤
          6 * Real.sqrt (C * ‖u - u₀‖) := by
  obtain ⟨X, hX, hext⟩ := actualQuasimomentum_uniformExterior_E02_38 B hB
  set T : ℝ := X + 2
  have hT0 : 0 ≤ T := by simp only [T]; linarith
  let seg : ℝ → ℂ := fun t => (x:ℂ) + Complex.I * (t:ℂ)
  have hseg_im : ∀ t : ℝ, (seg t).im = t := by intro t; simp [seg]
  have hseg_c : Continuous seg := by fun_prop
  have hseg_norm : ∀ t ∈ Icc (0:ℝ) T, ‖seg t‖ ≤ |x| + T := by
    intro t ht
    calc ‖seg t‖ ≤ ‖(x:ℂ)‖ + ‖Complex.I * (t:ℂ)‖ := norm_add_le _ _
      _ = |x| + |t| := by simp
      _ ≤ |x| + T := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
  have hcont : ∀ v : PhysicalL2,
      ContinuousOn (fun t => actualQuasimomentumClosedE02_38 v (seg t)) (Icc 0 T) := by
    intro v
    refine (continuousOn_extend_actualQuasimomentumE02_38 v).comp hseg_c.continuousOn ?_
    intro t ht
    show 0 ≤ (seg t).im
    rw [hseg_im]; exact ht.1
  set g : ℝ → ℂ := fun t => actualQuasimomentumClosedE02_38 u₀ (seg t)
  -- `sin g ≠ 0` on the segment
  have hsin_ne : ∀ t ∈ Icc (0:ℝ) T, Complex.sin (g t) ≠ 0 := by
    intro t ht hzero
    rcases lt_or_eq_of_le ht.1 with hpos | h0
    · have hpos' : 0 < (seg t).im := by rw [hseg_im]; exact hpos
      obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp hzero
      have him := (isActualQuasimomentumBranch_actualQuasimomentumE02_38 u₀).2.2.1 _ hpos'
      have : (g t).im = 0 := by rw [hm]; simp
      simp only [g] at this
      rw [actualQuasimomentumClosed_eq_of_pos_E02_38 u₀ _ hpos'] at this
      linarith
    · have hc := actualQuasimomentumClosed_cos_E02_38 u₀ (seg t) (by rw [hseg_im]; exact ht.1)
      have hst : seg t = (x:ℂ) := by simp [seg, ← h0]
      rw [hst] at hc
      apply hx
      rw [← hc]
      have h1 := Complex.sin_sq_add_cos_sq (g t)
      simp only [g, hst] at h1 hzero
      rw [hzero] at h1
      linear_combination h1
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
  obtain ⟨C, hC0, hLip⟩ := actualPhysicalUnitHalfTrace_lipschitz_E02_38 (‖u₀‖ + 1) (|x| + T)
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
  have hTpos : 0 < (seg T).im := by rw [hseg_im]; linarith
  have hTX : X ≤ ‖seg T‖ := by
    have := Complex.abs_im_le_norm (seg T)
    rw [hseg_im, abs_of_nonneg hT0] at this
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
      have h0 : 0 ≤ (seg t).im := by rw [hseg_im]; exact ht.1
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
  have hs0 : seg 0 = (x:ℂ) := by simp [seg]
  simp only [f, g, hs0, actualQuasimomentumClosed_ofReal_E02_38] at this
  exact this

end NlsGge.SpectralFoundations
end
