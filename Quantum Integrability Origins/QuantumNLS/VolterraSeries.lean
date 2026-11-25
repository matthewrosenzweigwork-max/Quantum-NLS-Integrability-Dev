import Mathlib

/-!
# A Volterra series with the exponential kernel, summed in closed form

Source use: `ROOT_spectral_measure.tex`, `prop:root-free`, plane-wave clause: the series `Σ_r (κ/L)^r R_r(L)` of nested alternating-chamber integrals of exponentials is
`Φ(L) = (ρ₂ e^{ρ₁L} − ρ₁ e^{ρ₂L})/(ρ₂ − ρ₁)` with `ρ₁ + ρ₂ = c`, `ρ₁ρ₂ = −λ` (the printed constant-coefficient 2×2 system, derived here with no ODE theorem).

For `c ≠ 0` let `kk c t = (e^{ct} − 1)/c = ∫₀ᵗ e^{cs} ds` and `(T f)(ℓ) = ∫₀^ℓ f(y) kk(ℓ − y) dy`, `R₀ = 1`, `R_{r+1} = T R_r` (`Rr`).
* `norm_Rr_le`: `‖R_r(ℓ)‖ ≤ e^{γℓ} ℓ^{2r}/(2r)!` (any `γ ≥ max(Re c, 0)`);
* `Tk_Phi`: for the closed form `Φ`, `λ T Φ = Φ − 1` (exponential integrals and the relations `ρ₁ + ρ₂ = c`, `ρ₁ρ₂ = −λ`);
* `hasSum_Phi`: `Σ_r λ^r R_r(ℓ) = Φ(ℓ)` for `ℓ ≥ 0` (iterating `Φ = 1 + λTΦ` and the factorial remainder bound);
* `sym_closed`: `Φ_c(L) + e^{cL} Φ_{−c}(L) = e^{ρ₁L} + e^{ρ₂L}` (the plus and minus chamber contributions).
No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped Nat

noncomputable section

namespace QuantumNLS.VolterraSeries

def kk (c : ℂ) (t : ℝ) : ℂ := (Complex.exp (c * t) - 1) / c

theorem continuous_kk (c : ℂ) : Continuous (kk c) := by unfold kk; fun_prop

/-- `(T f)(ℓ) = ∫₀^ℓ f(y) kk(ℓ − y) dy`. -/
def Tk (c : ℂ) (f : ℝ → ℂ) (ℓ : ℝ) : ℂ := ∫ y in (0 : ℝ)..ℓ, f y * kk c (ℓ - y)

/-- `R₀ = 1`, `R_{r+1} = T R_r`. -/
def Rr (c : ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => 1
  | r + 1 => Tk c (Rr c r)

theorem kk_eq_integral {c : ℂ} (hc : c ≠ 0) (t : ℝ) : kk c t = ∫ s in (0 : ℝ)..t, Complex.exp (c * s) := by
  rw [integral_exp_mul_complex hc]
  simp [kk]

theorem norm_exp_le {c : ℂ} {γ : ℝ} (hc : c.re ≤ γ) {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.exp (c * s)‖ ≤ Real.exp (γ * s) := by
  rw [Complex.norm_exp]
  have : (c * (s : ℂ)).re = c.re * s := by simp
  rw [this]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hc hs)

theorem norm_kk_le {c : ℂ} (hc0 : c ≠ 0) {γ : ℝ} (hc : c.re ≤ γ) (hγ : 0 ≤ γ) {t : ℝ} (ht : 0 ≤ t) :
    ‖kk c t‖ ≤ t * Real.exp (γ * t) := by
  rw [kk_eq_integral hc0]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s : ℝ => Complex.exp (c * s)) (C := Real.exp (γ * t)) (fun s hs => by
      rw [uIoc_of_le ht] at hs
      exact (norm_exp_le hc hs.1.le).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hγ)))
  rw [sub_zero, abs_of_nonneg ht] at h
  linarith [mul_comm t (Real.exp (γ * t))]

theorem continuous_Tk {c : ℂ} {f : ℝ → ℂ} (hf : Continuous f) : Continuous (Tk c f) := by
  have : Continuous (fun p : ℝ × ℝ => f p.2 * kk c (p.1 - p.2)) :=
    (hf.comp continuous_snd).mul ((continuous_kk c).comp (continuous_fst.sub continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    (f := fun ℓ y => f y * kk c (ℓ - y)) this continuous_id

theorem intervalIntegrable_conv {c : ℂ} {f : ℝ → ℂ} (hf : Continuous f) (ℓ : ℝ) :
    IntervalIntegrable (fun y => f y * kk c (ℓ - y)) volume 0 ℓ :=
  (hf.mul ((continuous_kk c).comp (continuous_const.sub continuous_id))).intervalIntegrable _ _

theorem Tk_add {c : ℂ} {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (ℓ : ℝ) :
    Tk c (fun y => f y + g y) ℓ = Tk c f ℓ + Tk c g ℓ := by
  unfold Tk
  simp_rw [add_mul]
  exact intervalIntegral.integral_add (intervalIntegrable_conv hf ℓ) (intervalIntegrable_conv hg ℓ)

theorem Tk_smul {c : ℂ} (a : ℂ) (f : ℝ → ℂ) (ℓ : ℝ) :
    Tk c (fun y => a * f y) ℓ = a * Tk c f ℓ := by
  unfold Tk
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  simp only []
  ring

theorem Tk_sub {c : ℂ} {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (ℓ : ℝ) :
    Tk c (fun y => f y - g y) ℓ = Tk c f ℓ - Tk c g ℓ := by
  have h := Tk_add (c := c) (f := f) (g := fun y => -g y) hf hg.neg ℓ
  have h2 : Tk c (fun y => -g y) ℓ = -Tk c g ℓ := by
    have := Tk_smul (c := c) (-1) g ℓ
    simpa using this
  simp only [sub_eq_add_neg]
  rw [h, h2]

theorem continuous_Rr (c : ℂ) (r : ℕ) : Continuous (Rr c r) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih => exact continuous_Tk ih

/-- Partial sums `S_n = Σ_{r<n} λ^r R_r`. -/
def Spart (c lam : ℂ) (n : ℕ) (y : ℝ) : ℂ := ∑ r ∈ Finset.range n, lam ^ r * Rr c r y

theorem continuous_Spart (c lam : ℂ) (n : ℕ) : Continuous (Spart c lam n) := by
  unfold Spart
  exact continuous_finsetSum _ (fun r _ => continuous_const.mul (continuous_Rr c r))

theorem Tk_Spart (c lam : ℂ) (n : ℕ) (ℓ : ℝ) :
    Tk c (Spart c lam n) ℓ = ∑ r ∈ Finset.range n, lam ^ r * Tk c (Rr c r) ℓ := by
  induction n with
  | zero =>
    simp [Spart, Tk]
  | succ n ih =>
    have e : Spart c lam (n + 1) = fun y => Spart c lam n y + lam ^ n * Rr c n y := by
      funext y; simp [Spart, Finset.sum_range_succ]
    rw [e, Tk_add (f := Spart c lam n) (g := fun y => lam ^ n * Rr c n y) (continuous_Spart c lam n)
      (continuous_const.mul (continuous_Rr c n)) ℓ, Tk_smul (lam ^ n) (Rr c n), ih, Finset.sum_range_succ]

theorem Spart_succ (c lam : ℂ) (n : ℕ) (y : ℝ) :
    Spart c lam (n + 1) y = 1 + lam * Tk c (Spart c lam n) y := by
  rw [Tk_Spart, Finset.mul_sum]
  unfold Spart
  rw [Finset.sum_range_succ']
  simp only [Rr, pow_zero, one_mul, pow_succ]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun r _ => ?_)
  ring

/-! ### Bounds -/

theorem integral_y_pow_mul (ℓ : ℝ) (m : ℕ) :
    ∫ y in (0 : ℝ)..ℓ, y ^ m * (ℓ - y) = ℓ ^ (m + 2) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  have h1 : ∀ y : ℝ, y ^ m * (ℓ - y) = ℓ * y ^ m - y ^ (m + 1) := fun y => by ring
  simp_rw [h1]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  push_cast
  field_simp
  ring

theorem Tk_bound {c : ℂ} (hc0 : c ≠ 0) {γ : ℝ} (hγ : 0 ≤ γ) (hcγ : c.re ≤ γ) {f : ℝ → ℂ} (hf : Continuous f)
    {M : ℝ} {m : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hb : ∀ y ∈ Icc 0 ℓ, ‖f y‖ ≤ M * Real.exp (γ * y) * y ^ m / (m ! : ℝ)) :
    ‖Tk c f ℓ‖ ≤ M * Real.exp (γ * ℓ) * ℓ ^ (m + 2) / ((m + 2) ! : ℝ) := by
  unfold Tk
  refine (intervalIntegral.norm_integral_le_integral_norm hℓ).trans ?_
  have hint : ∫ y in (0 : ℝ)..ℓ, M * Real.exp (γ * y) * y ^ m / (m ! : ℝ) * ((ℓ - y) * Real.exp (γ * (ℓ - y))) =
      M * Real.exp (γ * ℓ) * ℓ ^ (m + 2) / ((m + 2) ! : ℝ) := by
    have e : ∀ y : ℝ, M * Real.exp (γ * y) * y ^ m / (m ! : ℝ) * ((ℓ - y) * Real.exp (γ * (ℓ - y))) =
        (M * Real.exp (γ * ℓ) / (m ! : ℝ)) * (y ^ m * (ℓ - y)) := by
      intro y
      have : Real.exp (γ * y) * Real.exp (γ * (ℓ - y)) = Real.exp (γ * ℓ) := by
        rw [← Real.exp_add]; congr 1; ring
      calc _ = M / (m ! : ℝ) * (Real.exp (γ * y) * Real.exp (γ * (ℓ - y))) * (y ^ m * (ℓ - y)) := by ring
        _ = _ := by rw [this]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_y_pow_mul]
    have hfac : ((m + 2) ! : ℝ) = ((m : ℝ) + 2) * (((m : ℝ) + 1) * (m ! : ℝ)) := by
      rw [show m + 2 = (m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hfac]
    have hm : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    field_simp
  rw [← hint]
  refine intervalIntegral.integral_mono_on hℓ ?_ ?_ ?_
  · exact (continuous_norm.comp (hf.mul ((continuous_kk c).comp (continuous_const.sub continuous_id)))).intervalIntegrable _ _
  · apply Continuous.intervalIntegrable
    fun_prop
  · intro y hy
    rw [norm_mul]
    refine mul_le_mul (hb y hy) ?_ (norm_nonneg _) ?_
    · have := norm_kk_le hc0 hcγ hγ (t := ℓ - y) (by linarith [hy.2])
      linarith [mul_comm (ℓ - y) (Real.exp (γ * (ℓ - y)))]
    · have h0 := (norm_nonneg (f y)).trans (hb y hy)
      exact h0

theorem norm_Rr_le {c : ℂ} (hc0 : c ≠ 0) {γ : ℝ} (hγ : 0 ≤ γ) (hcγ : c.re ≤ γ) (r : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ‖Rr c r y‖ ≤ 1 * Real.exp (γ * y) * y ^ (2 * r) / ((2 * r) ! : ℝ) := by
  induction r generalizing y with
  | zero => simpa [Rr] using Real.one_le_exp (mul_nonneg hγ hy)
  | succ r ih =>
    have := Tk_bound hc0 hγ hcγ (continuous_Rr c r) (M := 1) (m := 2 * r) hy
      (fun y' hy' => ih hy'.1)
    simpa [Rr, show 2 * (r + 1) = 2 * r + 2 by ring] using this

/-! ### The closed form -/

theorem Tk_exp {c ρ : ℂ} (hc : c ≠ 0) (hρ : ρ ≠ 0) (hρc : ρ - c ≠ 0) (ℓ : ℝ) :
    Tk c (fun y => Complex.exp (ρ * y)) ℓ =
      ((Complex.exp (ρ * ℓ) - Complex.exp (c * ℓ)) / (ρ - c) - (Complex.exp (ρ * ℓ) - 1) / ρ) / c := by
  unfold Tk kk
  have e : ∀ y : ℝ, Complex.exp (ρ * y) * ((Complex.exp (c * ((ℓ : ℝ) - y : ℝ)) - 1) / c) =
      (Complex.exp (c * ℓ) / c) * Complex.exp ((ρ - c) * y) - (1 / c) * Complex.exp (ρ * y) := by
    intro y
    have : Complex.exp (c * ((ℓ - y : ℝ) : ℂ)) * Complex.exp (ρ * y) =
        Complex.exp (c * ℓ) * Complex.exp ((ρ - c) * y) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    calc _ = (Complex.exp (c * ((ℓ - y : ℝ) : ℂ)) * Complex.exp (ρ * y) - Complex.exp (ρ * y)) / c := by ring
      _ = _ := by rw [this]; ring
  simp_rw [show ∀ y : ℝ, (((ℓ - y : ℝ)) : ℂ) = (ℓ : ℂ) - y from fun y => by push_cast; ring] at e
  have e' : ∀ y : ℝ, Complex.exp (ρ * y) * ((Complex.exp (c * ((ℓ : ℂ) - y)) - 1) / c) =
      (Complex.exp (c * ℓ) / c) * Complex.exp ((ρ - c) * y) - (1 / c) * Complex.exp (ρ * y) := by
    intro y
    have := e y
    simpa [Complex.ofReal_sub] using this
  simp only [Complex.ofReal_sub]
  simp_rw [e']
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_exp_mul_complex hρc, integral_exp_mul_complex hρ]
  have hE : Complex.exp (c * ℓ) * Complex.exp ((ρ - c) * ℓ) = Complex.exp (ρ * ℓ) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp only [mul_zero, Complex.ofReal_zero, Complex.exp_zero]
  generalize Complex.exp ((ρ - c) * ℓ) = X' at hE ⊢
  generalize Complex.exp (c * ℓ) = E at hE ⊢
  rw [← hE]
  field_simp
  try ring

/-- `Φ(ℓ) = (ρ₂ e^{ρ₁ℓ} − ρ₁ e^{ρ₂ℓ})/(ρ₂ − ρ₁)`. -/
def Phi (ρ1 ρ2 : ℂ) (ℓ : ℝ) : ℂ :=
  (ρ2 * Complex.exp (ρ1 * ℓ) - ρ1 * Complex.exp (ρ2 * ℓ)) / (ρ2 - ρ1)

theorem continuous_Phi (ρ1 ρ2 : ℂ) : Continuous (Phi ρ1 ρ2) := by unfold Phi; fun_prop

theorem Tk_Phi {ρ1 ρ2 : ℂ} (h12 : ρ1 ≠ ρ2) (h1 : ρ1 ≠ 0) (h2 : ρ2 ≠ 0) (hc : ρ1 + ρ2 ≠ 0) (ℓ : ℝ) :
    (-(ρ1 * ρ2)) * Tk (ρ1 + ρ2) (Phi ρ1 ρ2) ℓ = Phi ρ1 ρ2 ℓ - 1 := by
  have hd : ρ2 - ρ1 ≠ 0 := sub_ne_zero.2 (Ne.symm h12)
  have e : Phi ρ1 ρ2 = fun y : ℝ => (ρ2 / (ρ2 - ρ1)) * Complex.exp (ρ1 * (y : ℂ)) + (-ρ1 / (ρ2 - ρ1)) * Complex.exp (ρ2 * (y : ℂ)) := by
    funext y; unfold Phi; field_simp; ring
  rw [e, Tk_add (f := fun y : ℝ => (ρ2 / (ρ2 - ρ1)) * Complex.exp (ρ1 * (y : ℂ))) (g := fun y : ℝ => (-ρ1 / (ρ2 - ρ1)) * Complex.exp (ρ2 * (y : ℂ)))
    (by fun_prop) (by fun_prop), Tk_smul, Tk_smul,
    Tk_exp hc h1 (by rw [show ρ1 - (ρ1 + ρ2) = -ρ2 by ring]; exact neg_ne_zero.2 h2),
    Tk_exp hc h2 (by rw [show ρ2 - (ρ1 + ρ2) = -ρ1 by ring]; exact neg_ne_zero.2 h1)]
  rw [show ρ1 - (ρ1 + ρ2) = -ρ2 by ring, show ρ2 - (ρ1 + ρ2) = -ρ1 by ring]
  field_simp
  ring

theorem norm_Phi_le {ρ1 ρ2 : ℂ} (h12 : ρ1 ≠ ρ2) {y : ℝ} (hy : 0 ≤ y) :
    ‖Phi ρ1 ρ2 y‖ ≤ ((‖ρ1‖ + ‖ρ2‖) / ‖ρ2 - ρ1‖) * Real.exp ((‖ρ1‖ + ‖ρ2‖) * y) := by
  have hd : 0 < ‖ρ2 - ρ1‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h12))
  unfold Phi
  rw [norm_div]
  have b1 : ‖Complex.exp (ρ1 * y)‖ ≤ Real.exp ((‖ρ1‖ + ‖ρ2‖) * y) := by
    refine (norm_exp_le (c := ρ1) (γ := ‖ρ1‖ + ‖ρ2‖) ?_ hy)
    exact (Complex.re_le_norm ρ1).trans (by linarith [norm_nonneg ρ2])
  have b2 : ‖Complex.exp (ρ2 * y)‖ ≤ Real.exp ((‖ρ1‖ + ‖ρ2‖) * y) := by
    refine (norm_exp_le (c := ρ2) (γ := ‖ρ1‖ + ‖ρ2‖) ?_ hy)
    exact (Complex.re_le_norm ρ2).trans (by linarith [norm_nonneg ρ1])
  rw [div_le_iff₀ hd]
  calc ‖ρ2 * Complex.exp (ρ1 * y) - ρ1 * Complex.exp (ρ2 * y)‖
      ≤ ‖ρ2 * Complex.exp (ρ1 * y)‖ + ‖ρ1 * Complex.exp (ρ2 * y)‖ := norm_sub_le _ _
    _ ≤ ‖ρ2‖ * Real.exp ((‖ρ1‖ + ‖ρ2‖) * y) + ‖ρ1‖ * Real.exp ((‖ρ1‖ + ‖ρ2‖) * y) := by
        rw [norm_mul, norm_mul]; gcongr
    _ = _ := by have := hd.ne'; field_simp; ring

theorem hasSum_Phi {ρ1 ρ2 : ℂ} (h12 : ρ1 ≠ ρ2) (h1 : ρ1 ≠ 0) (h2 : ρ2 ≠ 0) (hc : ρ1 + ρ2 ≠ 0) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    HasSum (fun r : ℕ => (-(ρ1 * ρ2)) ^ r * Rr (ρ1 + ρ2) r ℓ) (Phi ρ1 ρ2 ℓ) := by
  set c := ρ1 + ρ2 with hcdef
  set lam : ℂ := -(ρ1 * ρ2) with hlam
  set γ : ℝ := ‖ρ1‖ + ‖ρ2‖ with hγdef
  have hγ : 0 ≤ γ := by positivity
  have hcγ : c.re ≤ γ := (Complex.re_le_norm c).trans (norm_add_le _ _)
  set M : ℝ := γ / ‖ρ2 - ρ1‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hEq : ∀ y, Phi ρ1 ρ2 y = 1 + lam * Tk c (Phi ρ1 ρ2) y := fun y => by
    have := Tk_Phi h12 h1 h2 hc y
    rw [← hcdef, ← hlam] at this
    linear_combination -this
  -- remainder bound
  have claim : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y → ‖Phi ρ1 ρ2 y - Spart c lam n y‖ ≤
      ‖lam‖ ^ n * M * Real.exp (γ * y) * y ^ (2 * n) / ((2 * n) ! : ℝ) := by
    intro n
    induction n with
    | zero => intro y hy; simpa [Spart] using norm_Phi_le h12 hy
    | succ n ih =>
      intro y hy
      have hD : Phi ρ1 ρ2 y - Spart c lam (n + 1) y =
          lam * Tk c (fun y => Phi ρ1 ρ2 y - Spart c lam n y) y := by
        rw [Tk_sub (continuous_Phi ρ1 ρ2) (continuous_Spart c lam n), Spart_succ, hEq y]
        ring
      rw [hD, norm_mul]
      have := Tk_bound hc hγ hcγ ((continuous_Phi ρ1 ρ2).sub (continuous_Spart c lam n))
        (M := ‖lam‖ ^ n * M) (m := 2 * n) hy (fun y' hy' => by
          have := ih y' hy'.1
          simpa [mul_assoc] using this)
      calc ‖lam‖ * ‖Tk c (fun y => Phi ρ1 ρ2 y - Spart c lam n y) y‖
          ≤ ‖lam‖ * (‖lam‖ ^ n * M * Real.exp (γ * y) * y ^ (2 * n + 2) / ((2 * n + 2) ! : ℝ)) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = _ := by
            rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_succ]; ring
  -- summability
  have hx : Summable (fun n : ℕ => (Real.sqrt ‖lam‖ * ℓ) ^ (2 * n) / ((2 * n) ! : ℝ)) := by
    have := (Real.summable_pow_div_factorial (Real.sqrt ‖lam‖ * ℓ)).comp_injective
      (i := fun n : ℕ => 2 * n) (fun a b h => by simpa using h)
    simpa [Function.comp_def] using this
  have hxe : ∀ n : ℕ, (Real.sqrt ‖lam‖ * ℓ) ^ (2 * n) = ‖lam‖ ^ n * ℓ ^ (2 * n) := by
    intro n
    rw [mul_pow, pow_mul, Real.sq_sqrt (norm_nonneg _), pow_mul]
  have hterm : ∀ r : ℕ, ‖lam ^ r * Rr c r ℓ‖ ≤ Real.exp (γ * ℓ) * ((Real.sqrt ‖lam‖ * ℓ) ^ (2 * r) / ((2 * r) ! : ℝ)) := by
    intro r
    rw [norm_mul, norm_pow, hxe]
    have := norm_Rr_le hc hγ hcγ r hℓ
    calc ‖lam‖ ^ r * ‖Rr c r ℓ‖ ≤ ‖lam‖ ^ r * (1 * Real.exp (γ * ℓ) * ℓ ^ (2 * r) / ((2 * r) ! : ℝ)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hsum : Summable (fun r : ℕ => lam ^ r * Rr c r ℓ) :=
    Summable.of_norm_bounded (hx.mul_left (Real.exp (γ * ℓ))) hterm
  -- the partial sums converge to Φ
  have hto : Tendsto (fun n : ℕ => Spart c lam n ℓ) atTop (𝓝 (Phi ρ1 ρ2 ℓ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n : ℕ => M * Real.exp (γ * ℓ) * ((Real.sqrt ‖lam‖ * ℓ) ^ (2 * n) / ((2 * n) ! : ℝ))) atTop (𝓝 0) := by
      simpa using (hx.tendsto_atTop_zero).const_mul (M * Real.exp (γ * ℓ))
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hb
    rw [norm_sub_rev]
    refine (claim n ℓ hℓ).trans (le_of_eq ?_)
    rw [hxe]; ring
  have htsum := hsum.hasSum.tendsto_sum_nat
  have : ∑' r, lam ^ r * Rr c r ℓ = Phi ρ1 ρ2 ℓ :=
    tendsto_nhds_unique htsum (by simpa [Spart] using hto)
  rw [← this]
  exact hsum.hasSum

/-- `Φ_c(L) + e^{cL} Φ_{−c}(L) = e^{ρ₁L} + e^{ρ₂L}`. -/
theorem sym_closed {ρ1 ρ2 : ℂ} (h12 : ρ1 ≠ ρ2) (ℓ : ℝ) :
    Phi ρ1 ρ2 ℓ + Complex.exp ((ρ1 + ρ2) * ℓ) * Phi (-ρ1) (-ρ2) ℓ =
      Complex.exp (ρ1 * ℓ) + Complex.exp (ρ2 * ℓ) := by
  have hd : ρ2 - ρ1 ≠ 0 := sub_ne_zero.2 (Ne.symm h12)
  have hd' : -ρ2 - -ρ1 ≠ 0 := by
    intro h; apply hd; linear_combination -h
  unfold Phi
  have e1 : Complex.exp ((ρ1 + ρ2) * ℓ) = Complex.exp (ρ1 * ℓ) * Complex.exp (ρ2 * ℓ) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-ρ1 * ℓ) = (Complex.exp (ρ1 * ℓ))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; ring
  have e3 : Complex.exp (-ρ2 * ℓ) = (Complex.exp (ρ2 * ℓ))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; ring
  rw [e1, e2, e3]
  have n1 : Complex.exp (ρ1 * ℓ) ≠ 0 := Complex.exp_ne_zero _
  have n2 : Complex.exp (ρ2 * ℓ) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  try ring

end QuantumNLS.VolterraSeries

#print axioms QuantumNLS.VolterraSeries.norm_Rr_le
#print axioms QuantumNLS.VolterraSeries.Tk_Phi
#print axioms QuantumNLS.VolterraSeries.hasSum_Phi
#print axioms QuantumNLS.VolterraSeries.sym_closed
