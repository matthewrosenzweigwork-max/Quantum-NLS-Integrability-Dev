import Mathlib
import QuantumNLS.RootEvent
import QuantumNLS.ResolventNeighborhood

/-!
# Nonvanishing of `D = A − e/A` on the neighbourhood of `Γ_N`

Owner: haiku_inventory (round 10c). Source: `window_reconstruction.tex` lines 7 (`D = A − e/A`,
`A = e^{iκG}`, `e = e^{iLz}`) and 26–30 (hypothesis: `|D|` bounded below by a fixed positive number
on the rectangle `Γ_ℓ` with endpoints `±a_ℓ`, heights `±h`), and the PROP-017 statement
(`|D|` has a fixed positive lower bound on the neighbourhood, after decreasing `ρ`).

Proved: if `|D| ≥ d₀` on `Γ_N` (hypothesis `hD`), then `|D| ≥ d₀/2` on `NbhdN a h (ρ/4)`, provided
the explicit smallness conditions `hDs`, `hDlip` hold (the source's "decrease ρ once more").
The Lipschitz step uses the maximum-modulus/Cauchy bound `|G'| ≤ (1/r)/(ρ/2)` on the neighbourhood.
-/

namespace QuantumNLS.NonvanishingD

open MeasureTheory Set Metric
open QuantumNLS.RootEvent QuantumNLS.Extrapolation QuantumNLS.ResolventNeighborhood

/-- Source `D = A − e/A`, `A = e^{iκG}`, `e(z) = e^{iLz}`. -/
noncomputable def Dsrc (κ L : ℝ) (μ : Measure ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)
    - Complex.exp (Complex.I * (L : ℂ) * z) / Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)

/-- Lipschitz constant of `D` on balls of radius `ρ/4` about `Γ_N`. -/
noncomputable def Dlip (κ L a h ρ R δ : ℝ) : ℝ :=
  2 * Real.exp (|κ| * (1 / rNbhd a h ρ R δ))
    * (|κ| * ((1 / rNbhd a h ρ R δ) / (ρ / 2))
      + Real.exp (|L| * h) * (|L| + |κ| * ((1 / rNbhd a h ρ R δ) / (ρ / 2))))

lemma NbhdN_mono {a h s s' : ℝ} {w : ℂ} (hs : s ≤ s') (hw : w ∈ NbhdN a h s) :
    w ∈ NbhdN a h s' := by
  obtain ⟨v, hv, hd⟩ := hw
  exact ⟨v, hv, hd.trans hs⟩

lemma GammaN_subset_NbhdN {a h ρ : ℝ} {w : ℂ} (hw : w ∈ GammaN a h) (hρ : 0 ≤ ρ) :
    w ∈ NbhdN a h ρ :=
  ⟨w, hw, by rw [sub_self, norm_zero]; exact hρ⟩

lemma GammaN_im_abs {a h : ℝ} (hh : 0 ≤ h) {w : ℂ} (hw : w ∈ GammaN a h) : |w.im| ≤ h := by
  rcases hw with ⟨-, hi⟩ | ⟨hi, -⟩
  · exact hi
  · rcases hi with hi | hi
    · rw [hi]
      exact (abs_of_nonneg hh).le
    · rw [hi, abs_neg]
      exact (abs_of_nonneg hh).le

lemma norm_I_mul_mul (c : ℝ) (w : ℂ) : ‖Complex.I * (c : ℂ) * w‖ = |c| * ‖w‖ := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- `G` is differentiable and bounded by `1/r` at points of the neighbourhood. -/
lemma Gfull_props_nbhd {N : ℕ} (q : Fin N → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a h ρ R δ : ℝ} (hr : 0 < rNbhd a h ρ R δ) (ha : 0 < a) (hρ : 0 < ρ)
    (hb0 : 0 < h - 2 * ρ) (hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a|)
    (hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a|) {y : ℂ} (hy : y ∈ NbhdN a h ρ) :
    DifferentiableAt ℂ (Gfull μ) y ∧ ‖Gfull μ y‖ ≤ 1 / rNbhd a h ρ R δ := by
  obtain ⟨hGa, -, -⟩ := nbhd_dist (R := R) q μ ha hρ hb0 hsupp hsuppN hy
  exact ⟨(Gfull_hasDerivAt_of_dist μ hr hGa).differentiableAt, norm_Gfull_le μ y hr hGa⟩

/-- Derivative of `G` on the neighbourhood of radius `ρ/4`, by Cauchy on circles of radius `ρ/2`
(those circles stay in the neighbourhood of radius `ρ`). -/
lemma Gfull_deriv_bound_quarter {N : ℕ} (q : Fin N → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a h ρ R δ : ℝ} (hr : 0 < rNbhd a h ρ R δ) (ha : 0 < a) (hρ : 0 < ρ)
    (hb0 : 0 < h - 2 * ρ) (hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a|)
    (hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a|) {x : ℂ} (hx : x ∈ NbhdN a h (ρ / 4)) :
    ‖deriv (Gfull μ) x‖ ≤ (1 / rNbhd a h ρ R δ) / (ρ / 2) := by
  have hnear : ∀ w : ℂ, ‖w - x‖ ≤ ρ / 2 → w ∈ NbhdN a h ρ := fun w hw =>
    NbhdN_mono (by linarith) (NbhdN_add hx hw)
  have hf : DiffContOnCl ℂ (Gfull μ) (ball x (ρ / 2)) := by
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · have hwd : ‖w - x‖ ≤ ρ / 2 := by
        rw [mem_ball, dist_eq_norm] at hw
        exact hw.le
      exact (Gfull_props_nbhd q μ hr ha hρ hb0 hsupp hsuppN (hnear w hwd)).1.differentiableWithinAt
    · have hwd : ‖w - x‖ ≤ ρ / 2 := by
        have := Metric.closure_ball_subset_closedBall hw
        rw [mem_closedBall, dist_eq_norm] at this
        exact this
      exact (Gfull_props_nbhd q μ hr ha hρ hb0 hsupp hsuppN (hnear w hwd)).1.continuousAt.continuousWithinAt
  have hC : ∀ w ∈ sphere x (ρ / 2), ‖Gfull μ w‖ ≤ 1 / rNbhd a h ρ R δ := by
    intro w hw
    have hwd : ‖w - x‖ ≤ ρ / 2 := by
      rw [mem_sphere, dist_eq_norm] at hw
      exact hw.le
    exact (Gfull_props_nbhd q μ hr ha hρ hb0 hsupp hsuppN (hnear w hwd)).2
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hρ) hf hC

/-- Lipschitz bound for `G` on the closed ball of radius `ρ/4` about a point of `Γ_N`. -/
lemma Gfull_lip_GammaN {N : ℕ} (q : Fin N → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a h ρ R δ : ℝ} (hh : 0 ≤ h) (hr : 0 < rNbhd a h ρ R δ) (ha : 0 < a) (hρ : 0 < ρ)
    (hb0 : 0 < h - 2 * ρ) (hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a|)
    (hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a|) {w0 z : ℂ} (hw0 : w0 ∈ GammaN a h)
    (hz : z ∈ closedBall w0 (ρ / 4)) :
    ‖Gfull μ z - Gfull μ w0‖ ≤ ((1 / rNbhd a h ρ R δ) / (ρ / 2)) * ‖z - w0‖ := by
  have hmem : ∀ x ∈ closedBall w0 (ρ / 4), x ∈ NbhdN a h (ρ / 4) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    exact ⟨w0, hw0, hx⟩
  have hdiff : ∀ x ∈ closedBall w0 (ρ / 4), DifferentiableAt ℂ (Gfull μ) x := by
    intro x hx
    exact (Gfull_props_nbhd q μ hr ha hρ hb0 hsupp hsuppN
      (NbhdN_mono (by linarith) (hmem x hx))).1
  have hbd : ∀ x ∈ closedBall w0 (ρ / 4), ‖deriv (Gfull μ) x‖ ≤ (1 / rNbhd a h ρ R δ) / (ρ / 2) :=
    fun x hx => Gfull_deriv_bound_quarter q μ hr ha hρ hb0 hsupp hsuppN (hmem x hx)
  have hw0c : w0 ∈ closedBall w0 (ρ / 4) := mem_closedBall_self (by linarith)
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd (convex_closedBall _ _) hw0c hz

/-- Lipschitz bound for `D` on the closed ball of radius `ρ/4` about a point of `Γ_N`. -/
lemma Dsrc_lip_GammaN {N : ℕ} (q : Fin N → ℝ) (κ L : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a h ρ R δ : ℝ} (hh : 0 ≤ h) (hr : 0 < rNbhd a h ρ R δ) (ha : 0 < a) (hρ : 0 < ρ)
    (hb0 : 0 < h - 2 * ρ) (hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a|)
    (hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a|)
    (hDs : (|L| + |κ| * ((1 / rNbhd a h ρ R δ) / (ρ / 2))) * (ρ / 4) ≤ 1)
    {w0 z : ℂ} (hw0 : w0 ∈ GammaN a h) (hz : z ∈ closedBall w0 (ρ / 4)) :
    ‖Dsrc κ L μ z - Dsrc κ L μ w0‖ ≤ Dlip κ L a h ρ R δ * ‖z - w0‖ := by
  set r := rNbhd a h ρ R δ with hrdef
  set M1 := (1 / r) / (ρ / 2) with hM1
  set δz := ‖z - w0‖ with hδz
  have hδ0 : 0 ≤ δz := norm_nonneg _
  have hδle : δz ≤ ρ / 4 := by
    rw [mem_closedBall, dist_eq_norm] at hz
    exact hz
  have hM10 : 0 ≤ M1 := div_nonneg (div_nonneg zero_le_one hr.le) (by linarith)
  have hGd : ‖Gfull μ z - Gfull μ w0‖ ≤ M1 * δz :=
    Gfull_lip_GammaN q μ hh hr ha hρ hb0 hsupp hsuppN hw0 hz
  have hw0N : w0 ∈ NbhdN a h ρ := GammaN_subset_NbhdN hw0 hρ.le
  have hGw0 : ‖Gfull μ w0‖ ≤ 1 / r :=
    (Gfull_props_nbhd q μ hr ha hρ hb0 hsupp hsuppN hw0N).2
  -- exponent differences
  set u1 : ℂ → ℂ := fun w => Complex.I * (κ : ℂ) * Gfull μ w with hu1
  set u2 : ℂ → ℂ := fun w => Complex.I * (L : ℂ) * w - Complex.I * (κ : ℂ) * Gfull μ w with hu2
  have hDeq : ∀ w, Dsrc κ L μ w = Complex.exp (u1 w) - Complex.exp (u2 w) := by
    intro w
    simp only [Dsrc, hu1, hu2]
    rw [Complex.exp_sub]
  have hsplit : Dsrc κ L μ z - Dsrc κ L μ w0 =
      (Complex.exp (u1 z) - Complex.exp (u1 w0)) - (Complex.exp (u2 z) - Complex.exp (u2 w0)) := by
    rw [hDeq z, hDeq w0]
    ring
  -- the `u₁` increment
  have hu1d : ‖u1 z - u1 w0‖ ≤ |κ| * M1 * δz := by
    have : u1 z - u1 w0 = Complex.I * (κ : ℂ) * (Gfull μ z - Gfull μ w0) := by
      simp only [hu1]
      ring
    rw [this, norm_I_mul_mul]
    have h1 : |κ| * ‖Gfull μ z - Gfull μ w0‖ ≤ |κ| * (M1 * δz) :=
      mul_le_mul_of_nonneg_left hGd (abs_nonneg _)
    linarith [h1, show |κ| * M1 * δz = |κ| * (M1 * δz) by ring]
  -- the `u₂` increment
  have hu2d : ‖u2 z - u2 w0‖ ≤ (|L| + |κ| * M1) * δz := by
    have : u2 z - u2 w0 = Complex.I * (L : ℂ) * (z - w0)
        - Complex.I * (κ : ℂ) * (Gfull μ z - Gfull μ w0) := by
      simp only [hu2]
      ring
    have hA : ‖Complex.I * (L : ℂ) * (z - w0)‖ = |L| * δz := by
      rw [norm_I_mul_mul]
    have hB : ‖Complex.I * (κ : ℂ) * (Gfull μ z - Gfull μ w0)‖ ≤ |κ| * (M1 * δz) := by
      rw [norm_I_mul_mul]
      exact mul_le_mul_of_nonneg_left hGd (abs_nonneg _)
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [hA]
    nlinarith [hB]
  -- the constants on `Γ_N`
  have hX : ‖Complex.exp (u1 w0)‖ ≤ Real.exp (|κ| * (1 / r)) := by
    have h1 : ‖Complex.exp (u1 w0)‖ ≤ Real.exp (|κ| * |(Gfull μ w0).im|) := by
      simp only [hu1]
      exact norm_exp_I_mul_re κ (Gfull μ w0)
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_left (((Complex.abs_im_le_norm _).trans hGw0)) (abs_nonneg _)
  have hY : ‖Complex.exp (u2 w0)‖ ≤ Real.exp (|L| * h) * Real.exp (|κ| * (1 / r)) := by
    have hfac : Complex.exp (u2 w0)
        = Complex.exp (Complex.I * (L : ℂ) * w0) * Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ w0) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [hu2]
      push_cast
      ring
    rw [hfac, norm_mul]
    have hL : ‖Complex.exp (Complex.I * (L : ℂ) * w0)‖ ≤ Real.exp (|L| * h) := by
      refine (norm_exp_I_mul_re L w0).trans (Real.exp_le_exp.mpr ?_)
      exact mul_le_mul_of_nonneg_left (GammaN_im_abs hh hw0) (abs_nonneg _)
    have hK : ‖Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ w0)‖ ≤ Real.exp (|κ| * (1 / r)) := by
      refine (norm_exp_I_mul_re (-κ) (Gfull μ w0)).trans (Real.exp_le_exp.mpr ?_)
      rw [abs_neg]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hGw0) (abs_nonneg _)
    exact mul_le_mul hL hK (norm_nonneg _) (Real.exp_pos _).le
  -- exponential-difference bounds
  have hE1 : ‖Complex.exp (u1 z) - Complex.exp (u1 w0)‖ ≤ 2 * (|κ| * M1 * δz) * Real.exp (|κ| * (1 / r)) := by
    have hsm : ‖u1 z - u1 w0‖ ≤ 1 := by
      refine hu1d.trans ?_
      have : |κ| * M1 * δz ≤ (|L| + |κ| * M1) * δz := by
        have : |κ| * M1 ≤ |L| + |κ| * M1 := by linarith [abs_nonneg L]
        nlinarith [mul_le_mul_of_nonneg_right this hδ0]
      have hn : (|L| + |κ| * M1) * δz ≤ 1 := by
        have : δz ≤ ρ / 4 := hδle
        nlinarith [mul_le_mul_of_nonneg_left this (add_nonneg (abs_nonneg L) (mul_nonneg (abs_nonneg κ) hM10))]
      linarith
    have h2 := exp_sub_exp_le hsm
    calc ‖Complex.exp (u1 z) - Complex.exp (u1 w0)‖ ≤ 2 * ‖u1 z - u1 w0‖ * ‖Complex.exp (u1 w0)‖ := h2
      _ ≤ 2 * (|κ| * M1 * δz) * Real.exp (|κ| * (1 / r)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu1d (by norm_num)) hX (norm_nonneg _)
            (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (abs_nonneg _) hM10) hδ0))
  have hE2 : ‖Complex.exp (u2 z) - Complex.exp (u2 w0)‖
      ≤ 2 * ((|L| + |κ| * M1) * δz) * (Real.exp (|L| * h) * Real.exp (|κ| * (1 / r))) := by
    have hsm : ‖u2 z - u2 w0‖ ≤ 1 := by
      refine hu2d.trans ?_
      have hn : (|L| + |κ| * M1) * δz ≤ 1 := by
        nlinarith [mul_le_mul_of_nonneg_left hδle (add_nonneg (abs_nonneg L) (mul_nonneg (abs_nonneg κ) hM10))]
      exact hn
    have h2 := exp_sub_exp_le hsm
    calc ‖Complex.exp (u2 z) - Complex.exp (u2 w0)‖ ≤ 2 * ‖u2 z - u2 w0‖ * ‖Complex.exp (u2 w0)‖ := h2
      _ ≤ 2 * ((|L| + |κ| * M1) * δz) * (Real.exp (|L| * h) * Real.exp (|κ| * (1 / r))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu2d (by norm_num)) hY (norm_nonneg _)
            (mul_nonneg (by norm_num)
              (mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hM10)) hδ0))
  -- combine
  rw [hsplit]
  have htri := norm_sub_le (Complex.exp (u1 z) - Complex.exp (u1 w0))
    (Complex.exp (u2 z) - Complex.exp (u2 w0))
  have hD0 : 0 ≤ Dlip κ L a h ρ R δ := by
    unfold Dlip
    rw [← hrdef, ← hM1]
    have hX0 : 0 ≤ Real.exp (|κ| * (1 / r)) := (Real.exp_pos _).le
    have hY0 : 0 ≤ Real.exp (|L| * h) := (Real.exp_pos _).le
    have hm : 0 ≤ |κ| * M1 := mul_nonneg (abs_nonneg _) hM10
    have hm2 : 0 ≤ |L| + |κ| * M1 := add_nonneg (abs_nonneg _) hm
    exact mul_nonneg (mul_nonneg (by norm_num) hX0) (add_nonneg hm (mul_nonneg hY0 hm2))
  have hsumb : 2 * (|κ| * M1 * δz) * Real.exp (|κ| * (1 / r))
      + 2 * ((|L| + |κ| * M1) * δz) * (Real.exp (|L| * h) * Real.exp (|κ| * (1 / r)))
      = Dlip κ L a h ρ R δ * δz := by
    unfold Dlip
    rw [← hrdef, ← hM1]
    ring
  linarith [htri, hE1, hE2, hsumb]

/-- **Nonvanishing of `D` on the neighbourhood of `Γ_N`.** If `|D| ≥ d₀ > 0` on `Γ_N` (source
hypothesis, line 30), and the smallness conditions hold (the source's "decrease ρ once more"), then
`|D| ≥ d₀/2` on `NbhdN a h (ρ/4)`. -/
theorem D_lower_on_nbhd {N : ℕ} (q : Fin N → ℝ) (κ L d0 : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a h ρ R δ : ℝ) (hh : 0 ≤ h) (ha : 0 < a) (hρ : 0 < ρ)
    (hb0 : 0 < h - 2 * ρ) (hρδ : ρ < δ / 4) (hR2ρ : 2 * ρ < R) (hcut : 2 * R ≤ |a|)
    (hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a|)
    (hd0 : 0 < d0) (hD : ∀ w ∈ GammaN a h, d0 ≤ ‖Dsrc κ L μ w‖)
    (hDs : (|L| + |κ| * ((1 / rNbhd a h ρ R δ) / (ρ / 2))) * (ρ / 4) ≤ 1)
    (hDlip : Dlip κ L a h ρ R δ * (ρ / 4) ≤ d0 / 2) :
    ∀ z ∈ NbhdN a h (ρ / 4), d0 / 2 ≤ ‖Dsrc κ L μ z‖ := by
  have hr : 0 < rNbhd a h ρ R δ := by
    have hacut : 2 * R ≤ a := by rwa [abs_of_pos ha] at hcut
    unfold rNbhd
    exact lt_min hb0 (lt_min (by linarith) (by linarith))
  intro z hz
  obtain ⟨w0, hw0, hδ⟩ := hz
  have hLip := Dsrc_lip_GammaN q κ L μ hh hr ha hρ hb0 hsupp hsuppN hDs hw0
    (show z ∈ closedBall w0 (ρ / 4) from by rw [mem_closedBall, dist_eq_norm]; exact hδ)
  have hD0 := hD w0 hw0
  have hDlip0 : 0 ≤ Dlip κ L a h ρ R δ := by
    have hX0 : 0 ≤ Real.exp (|κ| * (1 / rNbhd a h ρ R δ)) := (Real.exp_pos _).le
    have hY0 : 0 ≤ Real.exp (|L| * h) := (Real.exp_pos _).le
    have hM10 : 0 ≤ (1 / rNbhd a h ρ R δ) / (ρ / 2) :=
      div_nonneg (div_nonneg zero_le_one hr.le) (by linarith)
    have hm : 0 ≤ |κ| * ((1 / rNbhd a h ρ R δ) / (ρ / 2)) := mul_nonneg (abs_nonneg _) hM10
    have hm2 : 0 ≤ |L| + |κ| * ((1 / rNbhd a h ρ R δ) / (ρ / 2)) := add_nonneg (abs_nonneg _) hm
    unfold Dlip
    exact mul_nonneg (mul_nonneg (by norm_num) hX0) (add_nonneg hm (mul_nonneg hY0 hm2))
  have hmul : Dlip κ L a h ρ R δ * ‖z - w0‖ ≤ Dlip κ L a h ρ R δ * (ρ / 4) :=
    mul_le_mul_of_nonneg_left hδ hDlip0
  have htri := norm_sub_norm_le (Dsrc κ L μ w0) (Dsrc κ L μ z)
  rw [norm_sub_rev] at htri
  linarith [hLip, hmul, hDlip, hD0, htri]


/-! ## 10. Fixed-scale nonvanishing (quantifier repair)

The constants depend on a fixed scale `s` and a fixed lower bound `rS ≤ rNbhd a h (2s)` only, not on
`ρ`, `a`, `R`. Hence the smallness condition `DlipS·(ρ/4) ≤ d₀/2` is discharged by choosing `ρ`. -/

/-- Lipschitz constant of `D` on the `t`-balls about `Γ_N` (`t ≤ s`), fixed scale `s`. -/
noncomputable def DlipS (κ L h s rS : ℝ) : ℝ :=
  Real.exp (|κ| / rS) * (|κ| * ((1 / rS) / s))
    + Real.exp (|L| * (h + 2 * s) + |κ| / rS) * (|L| + |κ| * ((1 / rS) / s))

lemma DlipS_nonneg {κ L h s rS : ℝ} (hs : 0 < s) (hrS : 0 < rS) : 0 ≤ DlipS κ L h s rS := by
  have hM : 0 ≤ (1 / rS) / s := div_nonneg (div_nonneg zero_le_one hrS.le) hs.le
  unfold DlipS
  exact add_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) hM))
    (mul_nonneg (Real.exp_pos _).le (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hM)))

/-- `|G′| ≤ (1/rS)/s` on `NbhdN a h s` (Cauchy on circles of radius `s` inside `NbhdN a h (2s)`). -/
lemma Gfull_deriv_scale {N : ℕ} (q : Fin N → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a h s R δ rS : ℝ} (hs : 0 < s) (hrS : 0 < rS) (hrS_le : rS ≤ rNbhd a h (2 * s) R δ)
    (ha : 0 < a) (hb0 : 0 < h - 2 * (2 * s))
    (hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a|)
    {x : ℂ} (hx : x ∈ NbhdN a h s) :
    ‖deriv (Gfull μ) x‖ ≤ (1 / rS) / s := by
  have hr2 : 0 < rNbhd a h (2 * s) R δ := lt_of_lt_of_le hrS hrS_le
  have hnear : ∀ w : ℂ, ‖w - x‖ ≤ s → w ∈ NbhdN a h (2 * s) := fun w hw =>
    NbhdN_mono (by linarith) (NbhdN_add hx hw)
  have hprop : ∀ y ∈ NbhdN a h (2 * s),
      DifferentiableAt ℂ (Gfull μ) y ∧ ‖Gfull μ y‖ ≤ 1 / rS := by
    intro y hy
    obtain ⟨h1, h2⟩ := Gfull_props_nbhd q μ hr2 ha (by linarith) hb0 hsupp hsuppN hy
    exact ⟨h1, h2.trans (one_div_le_one_div_of_le hrS hrS_le)⟩
  have hf : DiffContOnCl ℂ (Gfull μ) (ball x s) := by
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · have hwd : ‖w - x‖ ≤ s := by
        rw [mem_ball, dist_eq_norm] at hw
        exact hw.le
      exact (hprop w (hnear w hwd)).1.differentiableWithinAt
    · have hwd : ‖w - x‖ ≤ s := by
        have h1 := Metric.closure_ball_subset_closedBall hw
        rw [mem_closedBall, dist_eq_norm] at h1
        exact h1
      exact (hprop w (hnear w hwd)).1.continuousAt.continuousWithinAt
  have hC : ∀ w ∈ sphere x s, ‖Gfull μ w‖ ≤ 1 / rS := by
    intro w hw
    have hwd : ‖w - x‖ ≤ s := by
      rw [mem_sphere, dist_eq_norm] at hw
      exact hw.le
    exact (hprop w (hnear w hwd)).2
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs hf hC

/-- Lipschitz bound for `G` on `closedBall w₀ t`, `w₀ ∈ Γ_N`, `t ≤ s`, with constant `(1/rS)/s`. -/
lemma Gfull_lip_scale {N : ℕ} (q : Fin N → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a h s R δ rS : ℝ} (hs : 0 < s) (hrS : 0 < rS) (hrS_le : rS ≤ rNbhd a h (2 * s) R δ)
    (ha : 0 < a) (hb0 : 0 < h - 2 * (2 * s))
    (hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a|)
    {w0 z : ℂ} (hw0 : w0 ∈ GammaN a h) {t : ℝ} (ht : t ≤ s) (ht0 : 0 ≤ t)
    (hz : z ∈ closedBall w0 t) :
    ‖Gfull μ z - Gfull μ w0‖ ≤ ((1 / rS) / s) * ‖z - w0‖ := by
  have hmem : ∀ x ∈ closedBall w0 t, x ∈ NbhdN a h s := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    exact ⟨w0, hw0, le_trans hx ht⟩
  have hdiff : ∀ x ∈ closedBall w0 t, DifferentiableAt ℂ (Gfull μ) x := by
    intro x hx
    exact (Gfull_props_nbhd q μ (lt_of_lt_of_le hrS hrS_le) ha (by linarith) hb0 hsupp hsuppN
      (NbhdN_mono (by linarith) (hmem x hx))).1
  have hbd : ∀ x ∈ closedBall w0 t, ‖deriv (Gfull μ) x‖ ≤ (1 / rS) / s := fun x hx =>
    Gfull_deriv_scale q μ hs hrS hrS_le ha hb0 hsupp hsuppN (hmem x hx)
  have hw0c : w0 ∈ closedBall w0 t := mem_closedBall_self ht0
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd (convex_closedBall _ _) hw0c hz

/-- Lipschitz bound for `D` on `closedBall w₀ t`, `w₀ ∈ Γ_N`, `t ≤ s`, with constant `DlipS`. -/
lemma Dsrc_lip_scale {N : ℕ} (q : Fin N → ℝ) (κ L : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a h s R δ rS : ℝ} (hs : 0 < s) (hrS : 0 < rS) (hrS_le : rS ≤ rNbhd a h (2 * s) R δ)
    (ha : 0 < a) (hb0 : 0 < h - 2 * (2 * s))
    (hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a|)
    {w0 z : ℂ} (hw0 : w0 ∈ GammaN a h) {t : ℝ} (ht : t ≤ s) (ht0 : 0 ≤ t)
    (hz : z ∈ closedBall w0 t) :
    ‖Dsrc κ L μ z - Dsrc κ L μ w0‖ ≤ DlipS κ L h s rS * ‖z - w0‖ := by
  set M1 := (1 / rS) / s with hM1
  have hM10 : 0 ≤ M1 := div_nonneg (div_nonneg zero_le_one hrS.le) hs.le
  have hmem : ∀ x ∈ closedBall w0 t, x ∈ NbhdN a h s := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    exact ⟨w0, hw0, le_trans hx ht⟩
  have hw0N : w0 ∈ NbhdN a h s := GammaN_subset_NbhdN hw0 hs.le
  have hzN : z ∈ NbhdN a h s := hmem z hz
  have hb0s : 0 < h - 2 * s := by linarith
  have hGb : ∀ x ∈ NbhdN a h s, ‖Gfull μ x‖ ≤ 1 / rS := fun x hx =>
    ((Gfull_props_nbhd q μ (lt_of_lt_of_le hrS hrS_le) ha (by linarith) hb0 hsupp hsuppN
      (NbhdN_mono (by linarith) hx)).2).trans (one_div_le_one_div_of_le hrS hrS_le)
  have hIm : ∀ x ∈ NbhdN a h s, |x.im| ≤ h + 2 * s := fun x hx =>
    (nbhd_dist (R := R) q μ ha hs hb0s hsupp hsuppN hx).2.2
  have hGd : ‖Gfull μ z - Gfull μ w0‖ ≤ M1 * ‖z - w0‖ :=
    Gfull_lip_scale q μ hs hrS hrS_le ha hb0 hsupp hsuppN hw0 ht ht0 hz
  set δz := ‖z - w0‖ with hδz
  have hδ0 : 0 ≤ δz := norm_nonneg _
  set u1 : ℂ → ℂ := fun x => Complex.I * (κ : ℂ) * Gfull μ x with hu1
  set u2 : ℂ → ℂ := fun x => Complex.I * (L : ℂ) * x - Complex.I * (κ : ℂ) * Gfull μ x with hu2
  have hDeq : ∀ x, Dsrc κ L μ x = Complex.exp (u1 x) - Complex.exp (u2 x) := by
    intro x
    simp only [Dsrc, hu1, hu2]
    rw [Complex.exp_sub]
  have hsplit : Dsrc κ L μ z - Dsrc κ L μ w0 =
      (Complex.exp (u1 z) - Complex.exp (u1 w0)) - (Complex.exp (u2 z) - Complex.exp (u2 w0)) := by
    rw [hDeq z, hDeq w0]
    ring
  have hu1d : ‖u1 z - u1 w0‖ ≤ |κ| * M1 * δz := by
    have e : u1 z - u1 w0 = Complex.I * (κ : ℂ) * (Gfull μ z - Gfull μ w0) := by
      simp only [hu1]
      ring
    rw [e, norm_I_mul_mul]
    have h1 : |κ| * ‖Gfull μ z - Gfull μ w0‖ ≤ |κ| * (M1 * δz) :=
      mul_le_mul_of_nonneg_left hGd (abs_nonneg _)
    linarith [h1, show |κ| * M1 * δz = |κ| * (M1 * δz) by ring]
  have hu2d : ‖u2 z - u2 w0‖ ≤ (|L| + |κ| * M1) * δz := by
    have e : u2 z - u2 w0 = Complex.I * (L : ℂ) * (z - w0)
        - Complex.I * (κ : ℂ) * (Gfull μ z - Gfull μ w0) := by
      simp only [hu2]
      ring
    have hA : ‖Complex.I * (L : ℂ) * (z - w0)‖ = |L| * δz := by
      rw [norm_I_mul_mul]
    have hB : ‖Complex.I * (κ : ℂ) * (Gfull μ z - Gfull μ w0)‖ ≤ |κ| * (M1 * δz) := by
      rw [norm_I_mul_mul]
      exact mul_le_mul_of_nonneg_left hGd (abs_nonneg _)
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [hA]
    nlinarith [hB]
  have hre1 : ∀ x ∈ NbhdN a h s, (u1 x).re ≤ |κ| / rS := by
    intro x hx
    have hre : (u1 x).re = -(κ * (Gfull μ x).im) := by
      simp only [hu1]
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    calc -(κ * (Gfull μ x).im) ≤ |κ * (Gfull μ x).im| := neg_le_abs _
      _ = |κ| * |(Gfull μ x).im| := abs_mul _ _
      _ ≤ |κ| * (1 / rS) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (hGb x hx)) (abs_nonneg _)
      _ = |κ| / rS := by ring
  have hre2 : ∀ x ∈ NbhdN a h s, (u2 x).re ≤ |L| * (h + 2 * s) + |κ| / rS := by
    intro x hx
    have hre : (u2 x).re = -(L * x.im) + κ * (Gfull μ x).im := by
      simp only [hu2]
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hA : -(L * x.im) ≤ |L| * (h + 2 * s) := by
      calc -(L * x.im) ≤ |L * x.im| := neg_le_abs _
        _ = |L| * |x.im| := abs_mul _ _
        _ ≤ |L| * (h + 2 * s) := mul_le_mul_of_nonneg_left (hIm x hx) (abs_nonneg _)
    have hB : κ * (Gfull μ x).im ≤ |κ| / rS := by
      calc κ * (Gfull μ x).im ≤ |κ * (Gfull μ x).im| := le_abs_self _
        _ = |κ| * |(Gfull μ x).im| := abs_mul _ _
        _ ≤ |κ| * (1 / rS) :=
            mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (hGb x hx)) (abs_nonneg _)
        _ = |κ| / rS := by ring
    linarith
  have E1 : ‖Complex.exp (u1 z) - Complex.exp (u1 w0)‖ ≤ Real.exp (|κ| / rS) * (|κ| * M1 * δz) := by
    have key := exp_sub_exp_le_max (u1 z) (u1 w0)
    have hmax : max (u1 z).re (u1 w0).re ≤ |κ| / rS := max_le (hre1 z hzN) (hre1 w0 hw0N)
    exact key.trans (mul_le_mul (Real.exp_le_exp.mpr hmax) hu1d (norm_nonneg _) (Real.exp_pos _).le)
  have E2 : ‖Complex.exp (u2 z) - Complex.exp (u2 w0)‖
      ≤ Real.exp (|L| * (h + 2 * s) + |κ| / rS) * ((|L| + |κ| * M1) * δz) := by
    have key := exp_sub_exp_le_max (u2 z) (u2 w0)
    have hmax : max (u2 z).re (u2 w0).re ≤ |L| * (h + 2 * s) + |κ| / rS :=
      max_le (hre2 z hzN) (hre2 w0 hw0N)
    exact key.trans (mul_le_mul (Real.exp_le_exp.mpr hmax) hu2d (norm_nonneg _) (Real.exp_pos _).le)
  have htot : DlipS κ L h s rS * δz
      = Real.exp (|κ| / rS) * (|κ| * M1 * δz)
        + Real.exp (|L| * (h + 2 * s) + |κ| / rS) * ((|L| + |κ| * M1) * δz) := by
    unfold DlipS
    rw [← hM1]
    ring
  rw [hsplit]
  have htri := norm_sub_le (Complex.exp (u1 z) - Complex.exp (u1 w0))
    (Complex.exp (u2 z) - Complex.exp (u2 w0))
  linarith [htri, E1, E2, htot]

/-- **Nonvanishing of `D` with fixed-scale constants.** If `|D| ≥ d₀` on `Γ_N` and `DlipS·(ρ/4) ≤ d₀/2`,
then `|D| ≥ d₀/2` on `NbhdN a h (ρ/4)`. The smallness is discharged by choosing `ρ`. -/
theorem D_lower_scale {N : ℕ} (q : Fin N → ℝ) (κ L d0 : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a h s R δ rS ρ : ℝ} (hs : 0 < s) (hrS : 0 < rS) (hrS_le : rS ≤ rNbhd a h (2 * s) R δ)
    (ha : 0 < a) (hb0 : 0 < h - 2 * (2 * s)) (hρ : 0 < ρ) (hρs : ρ / 4 ≤ s)
    (hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a|)
    (hd0 : 0 < d0) (hD : ∀ w ∈ GammaN a h, d0 ≤ ‖Dsrc κ L μ w‖)
    (hDlip : DlipS κ L h s rS * (ρ / 4) ≤ d0 / 2) :
    ∀ z ∈ NbhdN a h (ρ / 4), d0 / 2 ≤ ‖Dsrc κ L μ z‖ := by
  intro z hz
  obtain ⟨w0, hw0, hδ⟩ := hz
  have hzball : z ∈ closedBall w0 (ρ / 4) := by
    rw [mem_closedBall, dist_eq_norm]
    exact hδ
  have hLip := Dsrc_lip_scale q κ L μ hs hrS hrS_le ha hb0 hsupp hsuppN hw0 hρs (by linarith) hzball
  have hD0 := hD w0 hw0
  have hDl0 := DlipS_nonneg (κ := κ) (L := L) (h := h) hs hrS
  have hmul : DlipS κ L h s rS * ‖z - w0‖ ≤ DlipS κ L h s rS * (ρ / 4) :=
    mul_le_mul_of_nonneg_left hδ hDl0
  have htri := norm_sub_norm_le (Dsrc κ L μ w0) (Dsrc κ L μ z)
  rw [norm_sub_rev] at htri
  linarith [hLip, hmul, hDlip, hD0, htri]

end QuantumNLS.NonvanishingD
