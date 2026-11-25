import Mathlib
import QuantumNLS.RB01MassCell

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-17: the density factor `D_n`, the even part `Ev_n`,
the factor `r_n` and the mass identity on the real slice (source `collective_actions.tex:413-464`:
`χ(s) = arsinh √s / √s = ∫_0^1 (1 + s y²)^{-1/2} dy`, eq. `GB01-D`, the gap identity
`arcosh(|Δ(p_n + w)|/2) = √(t_n² − ζ²) D_n(α_n + ζ)`, eq. `GB01-r`, eq. `GB01-mass-factor`).
Actual DEF-014 objects, `κ > 0`.

**Recorded route choice for `r_n` (integrator acknowledgement, 2026-11-16; statement unchanged).**
`r_n = (4/(πL)) ∫_{−1}^{1} √(1 − s²) Ev_n(τ_n s²) ds`, where
`Ev_n(σ) = (2πi)⁻¹ ∮_{|ξ| = 2d} D_n(α_n + ξ) ξ/(ξ² − σ) dξ` is the even part of `D_n(α_n + ·)`; no square root
of `τ_n` is chosen.  This `r_n` is proved equal to the source's series eq. `GB01-r`,
`(4/(πL)) Σ_j d_{2j,n} τ_n^j β_j`, `β_j = ∫_{−1}^{1} s^{2j} √(1 − s²) ds`, `d_{k,n}` the Taylor coefficients of
`D_n(α_n + ·)` at `0`, with absolute convergence, on the whole disk `|τ| < (2d)²` (`rgen_eq_series`, generic;
`density_slice` (f) on the real slice).

* `chi s = Σ_k binom(−1/2, k) s^k/(2k + 1)` (`Ring.choose`), holomorphic on `|s| < 1` (`hasFPowerSeries_chi`);
  `chi_eq_integral`: `χ(s) = ∫_0^1 (1 + s y²)^{-1/2} dy` for `|s| < 1`; `arsinh_sqrt_eq`: `arsinh √s = √s χ(s)`
  for `0 ≤ s < 1`;
* `Dgen H P w = (√(−H(w))/2) χ(𝒫(w)H(w)/4)` (principal root), `Dn` / `DC` for the real-slice / complexified
  `H_n`, `𝒫_n` (`RB01RootCount.Hn`, `Pn`; `RB01Moments.HC`, `PC`);
* `Ev`, `Ev_sq` (`Ev(ω²) = (G(ω) + G(−ω))/2`), `hasSum_Ev` (`Ev(σ) = Σ_j d_{2j} σ^j`), `rgen`, `rseries`,
  `rgen_eq_series`;
* **`density_slice`** (real slice, hypotheses of `RB01RootCount.factor`) and **`density`** (for every `u₀` there
  are `N`, `ρ > 0` such that for `|n| > N`, `‖u − u₀‖ < ρ`, `t ∈ [0,1]`, `q = t·u`): (a) on `|w| < 5d/2`,
  `|𝒫_n H_n/4| < 1/2`, `−H_n` in the slit plane, `D_n` holomorphic; (b) on the gap `|ζ| ≤ √τ_n`,
  `arcosh(|Δ(p_n + α_n + ζ)|/2) = √(τ_n − ζ²) D_n(α_n + ζ)`, `D_n` real with `2L/5 ≤ D_n ≤ 11L/20`;
  (c) `I_n = (τ_n/(πκ)) ∫_{−1}^{1} √(1 − s²) D_n(α_n + t_n s) ds` (`I_n` = DEF-014 root-indexed mass);
  (d) `r_n = (4/(πL)) ∫_{−1}^{1} √(1 − s²) D_n(α_n + t_n s) ds`; (e) `I_n = (L/(4κ)) τ_n r_n`, `r_n` real,
  `1/2 < r_n < 3/2`; (f) `r_n` = eq. `GB01-r`; (g) `DC`, `rC` at `(q, q̄)` equal `D_n`, `r_n`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped Nat Interval

namespace QuantumNLS.RB01Density

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RB01RootPrep (fn freeF dd ε₀ dd_pos root_prep)
open QuantumNLS.RB01RootCount (bm bp alpha tau Pn Hn Pn_eq lev_eq labels cell_count factor)
open QuantumNLS.RB01Moments (alphaC tauC PC HC real_slice)
open QuantumNLS.RootGapMultiplicity (Dl hreal)
open QuantumNLS.PhysicalContinuousBoundary (boundary)

/-! ## The function `χ` -/

/-- `binom(−1/2, k)/(2k + 1)`. -/
def chiCoef (k : ℕ) : ℂ := Ring.choose (-1 / 2 : ℂ) k / (2 * k + 1)

/-- `χ(s) = Σ_k binom(−1/2, k) s^k/(2k + 1)`, the power series at zero (`|s| < 1`). -/
def chi (s : ℂ) : ℂ := ∑' k : ℕ, chiCoef k * s ^ k

theorem summable_choose {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun k : ℕ => ‖Ring.choose (-1 / 2 : ℂ) k‖ * r ^ k := by
  have h1 : ((r.toNNReal : NNReal) : ENNReal) < (binomialSeries ℂ (-1 / 2 : ℂ)).radius :=
    lt_of_lt_of_le (by rw [ENNReal.coe_lt_one_iff]; exact (Real.toNNReal_lt_iff_lt_coe hr0).2 (by simpa using hr))
      binomialSeries_radius_ge_one
  have h2 := (binomialSeries ℂ (-1 / 2 : ℂ)).summable_norm_mul_pow h1
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ hr0] at h2
  exact h2

theorem norm_chiCoef_le (k : ℕ) : ‖chiCoef k‖ ≤ ‖Ring.choose (-1 / 2 : ℂ) k‖ := by
  unfold chiCoef
  rw [norm_div]
  have e : (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℕ) : ℂ) := by push_cast; ring
  have : ‖(2 * (k : ℂ) + 1)‖ = 2 * k + 1 := by
    rw [e, Complex.norm_natCast]; push_cast; ring
  rw [this]
  exact div_le_self (norm_nonneg _) (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith)

theorem summable_chi {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun k : ℕ => ‖chiCoef k‖ * r ^ k :=
  (summable_choose hr0 hr).of_nonneg_of_le (fun k => by positivity)
    (fun k => mul_le_mul_of_nonneg_right (norm_chiCoef_le k) (pow_nonneg hr0 k))

/-- The power series of `χ`. -/
def chiSeries : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ chiCoef

theorem one_le_radius : (1 : ENNReal) ≤ chiSeries.radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  apply chiSeries.le_radius_of_summable_norm
  simp only [chiSeries, FormalMultilinearSeries.ofScalars_norm]
  have h' : r < 1 := ENNReal.coe_lt_one_iff.1 hr
  exact summable_chi r.2 (by exact_mod_cast h')

theorem chi_eq_sum (s : ℂ) : chi s = chiSeries.sum s := by
  unfold chi FormalMultilinearSeries.sum chiSeries
  congr 1
  ext k
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

theorem hasFPowerSeries_chi : HasFPowerSeriesOnBall chi chiSeries 0 1 := by
  have h := chiSeries.hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one one_le_radius)
  have e : chi = chiSeries.sum := funext chi_eq_sum
  rw [e]
  exact h.mono zero_lt_one one_le_radius

theorem eball_one : Metric.eball (0 : ℂ) 1 = ball (0 : ℂ) 1 := by
  simpa using (Metric.eball_coe (x := (0 : ℂ)) (ε := 1))

theorem differentiableOn_chi : DifferentiableOn ℂ chi (ball 0 1) := by
  rw [← eball_one]
  exact hasFPowerSeries_chi.differentiableOn

/-- `χ(s) = ∫_0^1 (1 + s y²)^{-1/2} dy` for `|s| < 1` (principal power). -/
theorem chi_eq_integral {s : ℂ} (hs : ‖s‖ < 1) :
    chi s = ∫ y in (0 : ℝ)..1, (1 + s * (y : ℂ) ^ 2) ^ (-1 / 2 : ℂ) := by
  have hsum : ∀ y : ℝ, y ∈ Ι (0 : ℝ) 1 →
      HasSum (fun k : ℕ => Ring.choose (-1 / 2 : ℂ) k * s ^ k * (y : ℂ) ^ (2 * k))
        ((1 + s * (y : ℂ) ^ 2) ^ (-1 / 2 : ℂ)) := by
    intro y hy
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hy2 : ‖s * (y : ℂ) ^ 2‖ < 1 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have : |y| ^ 2 ≤ 1 := by rw [sq_abs]; nlinarith [hy.1, hy.2]
      calc ‖s‖ * |y| ^ 2 ≤ ‖s‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hs
    have hm : s * (y : ℂ) ^ 2 ∈ Metric.eball (0 : ℂ) 1 := by rw [eball_one]; simpa using hy2
    have := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℂ))).hasSum hm
    simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul, zero_add] at this
    convert this using 1
    funext k
    ring
  have hint : ∀ k : ℕ, ∫ y in (0 : ℝ)..1, Ring.choose (-1 / 2 : ℂ) k * s ^ k * (y : ℂ) ^ (2 * k) =
      chiCoef k * s ^ k := by
    intro k
    rw [intervalIntegral.integral_const_mul]
    have e1 : ∫ y in (0 : ℝ)..1, (y : ℂ) ^ (2 * k) = ((∫ y in (0 : ℝ)..1, y ^ (2 * k) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      simp only [Complex.ofReal_pow]
    have e2 : ∫ y in (0 : ℝ)..1, y ^ (2 * k) = 1 / (2 * (k : ℝ) + 1) := by
      rw [integral_pow]; simp
    rw [e1, e2]
    unfold chiCoef
    push_cast
    ring
  have hb : ∀ k : ℕ, ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Ι (0 : ℝ) 1 →
      ‖Ring.choose (-1 / 2 : ℂ) k * s ^ k * (y : ℂ) ^ (2 * k)‖ ≤ ‖Ring.choose (-1 / 2 : ℂ) k‖ * ‖s‖ ^ k := by
    intro k
    refine ae_of_all _ fun y hy => ?_
    rw [Set.uIoc_of_le zero_le_one] at hy
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |y| ^ (2 * k) ≤ 1 :=
      pow_le_one₀ (abs_nonneg y) (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2])
    calc ‖Ring.choose (-1 / 2 : ℂ) k‖ * ‖s‖ ^ k * |y| ^ (2 * k)
        ≤ ‖Ring.choose (-1 / 2 : ℂ) k‖ * ‖s‖ ^ k * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := mul_one _
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := (volume : Measure ℝ))
    (a := (0 : ℝ)) (b := 1)
    (F := fun k y => Ring.choose (-1 / 2 : ℂ) k * s ^ k * (y : ℂ) ^ (2 * k))
    (f := fun y => (1 + s * (y : ℂ) ^ 2) ^ (-1 / 2 : ℂ))
    (fun k _ => ‖Ring.choose (-1 / 2 : ℂ) k‖ * ‖s‖ ^ k)
    (fun k => (Continuous.aestronglyMeasurable (by fun_prop)))
    hb (ae_of_all _ fun y _ => summable_choose (norm_nonneg s) hs)
    intervalIntegrable_const (ae_of_all _ hsum)
  have key' : HasSum (fun k : ℕ => chiCoef k * s ^ k)
      (∫ y in (0 : ℝ)..1, (1 + s * (y : ℂ) ^ 2) ^ (-1 / 2 : ℂ)) := by
    convert key using 1
    funext k
    exact (hint k).symm
  rw [chi]
  exact key'.tsum_eq

/-- On the real interval `[0, 1)` the integrand is `(√(1 + x y²))⁻¹`. -/
theorem chi_ofReal {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    chi (x : ℂ) = ((∫ y in (0 : ℝ)..1, (√(1 + x * y ^ 2))⁻¹ : ℝ) : ℂ) := by
  rw [chi_eq_integral (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1),
    ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun y _ => ?_
  have hpos : 0 ≤ 1 + x * y ^ 2 := by positivity
  have e : (1 + (x : ℂ) * (y : ℂ) ^ 2) = ((1 + x * y ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hpos]
  congr 1
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hpos, Real.sqrt_eq_rpow]

theorem continuous_inv_sqrt (c : ℝ) (hc : 0 ≤ c) : Continuous fun y : ℝ => (√(1 + c * y ^ 2))⁻¹ :=
  Continuous.inv₀ (by fun_prop) (fun y => (Real.sqrt_pos.2 (by positivity)).ne')

theorem arsinh_eq {x : ℝ} (hx0 : 0 ≤ x) :
    x * (∫ y in (0 : ℝ)..1, (√(1 + x ^ 2 * y ^ 2))⁻¹) = Real.arsinh x := by
  rcases hx0.eq_or_lt with h | h
  · subst h; simp [Real.arsinh_zero]
  have hsub : ∫ y in (0 : ℝ)..1, (√(1 + x ^ 2 * y ^ 2))⁻¹ =
      x⁻¹ * ∫ t in (0 : ℝ)..x, (√(1 + t ^ 2))⁻¹ := by
    have := intervalIntegral.integral_comp_mul_left (f := fun t : ℝ => (√(1 + t ^ 2))⁻¹) (c := x)
      (a := 0) (b := 1) h.ne'
    simp only [mul_zero, mul_one, smul_eq_mul, mul_pow] at this
    exact this
  have hc : Continuous fun t : ℝ => (√(1 + t ^ 2))⁻¹ := by
    have := continuous_inv_sqrt 1 zero_le_one
    simpa using this
  have hftc : ∫ t in (0 : ℝ)..x, (√(1 + t ^ 2))⁻¹ = Real.arsinh x - Real.arsinh 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => Real.hasDerivAt_arsinh t)
      (hc.intervalIntegrable _ _)
  rw [hsub, hftc, Real.arsinh_zero, sub_zero, ← mul_assoc, mul_inv_cancel₀ h.ne', one_mul]

/-- `arsinh √s = √s χ(s)` for `0 ≤ s < 1`. -/
theorem arsinh_sqrt_eq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (Real.arsinh (√s) : ℂ) = (√s : ℂ) * chi (s : ℂ) := by
  have hq : 0 ≤ √s := Real.sqrt_nonneg s
  have hq2 : (√s) ^ 2 = s := Real.sq_sqrt hs0
  rw [← arsinh_eq hq, chi_ofReal hs0 hs1, hq2]
  exact Complex.ofReal_mul _ _

theorem chiR_bounds {x : ℝ} (hx0 : 0 ≤ x) :
    1 / (1 + x) ≤ ∫ y in (0 : ℝ)..1, (√(1 + x * y ^ 2))⁻¹ ∧
      ∫ y in (0 : ℝ)..1, (√(1 + x * y ^ 2))⁻¹ ≤ 1 := by
  have hc := continuous_inv_sqrt x hx0
  have hlo : ∀ y ∈ Icc (0 : ℝ) 1, 1 / (1 + x) ≤ (√(1 + x * y ^ 2))⁻¹ := by
    intro y hy
    have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
    have h1 : √(1 + x * y ^ 2) ≤ 1 + x := by
      have := Real.sqrt_le_sqrt (show 1 + x * y ^ 2 ≤ (1 + x) ^ 2 by nlinarith [mul_le_mul_of_nonneg_left hy2 hx0])
      rwa [Real.sqrt_sq (by linarith)] at this
    rw [one_div]
    exact inv_anti₀ (Real.sqrt_pos.2 (by positivity)) h1
  have hhi : ∀ y ∈ Icc (0 : ℝ) 1, (√(1 + x * y ^ 2))⁻¹ ≤ 1 := by
    intro y _
    have h1 : 1 ≤ √(1 + x * y ^ 2) := by
      have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + x * y ^ 2 by nlinarith [mul_nonneg hx0 (sq_nonneg y)])
      rwa [Real.sqrt_one] at this
    exact inv_le_one_of_one_le₀ h1
  constructor
  · have := intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_const (μ := volume)) (hc.intervalIntegrable 0 1) hlo
    simpa using this
  · have := intervalIntegral.integral_mono_on zero_le_one (hc.intervalIntegrable 0 1) (intervalIntegrable_const (μ := volume)) hhi
    simpa using this

/-! ## The density factor `D` (eq. `GB01-D`), generic in `H`, `𝒫` -/

/-- eq. `GB01-D`: `D(w) = (√(−H(w))/2) χ(𝒫(w) H(w)/4)` (principal square root). -/
def Dgen (H P : ℂ → ℂ) (w : ℂ) : ℂ := (-H w) ^ (1 / 2 : ℂ) / 2 * chi (P w * H w / 4)

theorem differentiableAt_Dgen {H P : ℂ → ℂ} {w : ℂ} (hH : DifferentiableAt ℂ H w) (hP : DifferentiableAt ℂ P w)
    (hslit : -H w ∈ Complex.slitPlane) (hs : ‖P w * H w / 4‖ < 1) : DifferentiableAt ℂ (Dgen H P) w := by
  unfold Dgen
  have h1 : DifferentiableAt ℂ (fun w => (-H w) ^ (1 / 2 : ℂ)) w :=
    hH.neg.cpow (differentiableAt_const _) hslit
  have h2 : DifferentiableAt ℂ (fun w => chi (P w * H w / 4)) w :=
    (differentiableOn_chi.differentiableAt (isOpen_ball.mem_nhds (by simpa using hs))).comp w
      ((hP.mul hH).div_const 4)
  exact (h1.div_const 2).mul h2

/-- Pointwise gap identity and the bounds for `D` at a real gap point (abstract form). -/
theorem gap_point {L : ℝ} (hL : 0 < L) {Δ Hw Pc : ℂ} {Pw : ℝ} (hPc : Pc = (Pw : ℂ))
    (hΔ : Δ ^ 2 - 4 = Pc * Hw) (hΔim : Δ.im = 0) (hHim : Hw.im = 0)
    (hHb : ‖Hw + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 5) (hP0 : Pw ≤ 0) (hPs : -Pw * L ^ 2 ≤ 1 / 64) :
    2 ≤ ‖Δ‖ ∧
    ((Real.arcosh (‖Δ‖ / 2) : ℝ) : ℂ) = ((√(-Pw) : ℝ) : ℂ) * ((-Hw) ^ (1 / 2 : ℂ) / 2 * chi (Pc * Hw / 4)) ∧
    ((-Hw) ^ (1 / 2 : ℂ) / 2 * chi (Pc * Hw / 4)).im = 0 ∧
    2 * L / 5 ≤ ((-Hw) ^ (1 / 2 : ℂ) / 2 * chi (Pc * Hw / 4)).re ∧
    ((-Hw) ^ (1 / 2 : ℂ) / 2 * chi (Pc * Hw / 4)).re ≤ 11 * L / 20 := by
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = -Hw.re := ⟨_, rfl⟩
  have hHw : Hw = ((-h : ℝ) : ℂ) := by apply Complex.ext <;> simp [hh, hHim]
  have hre : |Hw.re + L ^ 2| ≤ L ^ 2 / 5 := by
    have := Complex.abs_re_le_norm (Hw + (L : ℂ) ^ 2)
    have e : (Hw + (L : ℂ) ^ 2).re = Hw.re + L ^ 2 := by simp [pow_two]
    rw [e] at this
    linarith
  rw [abs_le] at hre
  have hh1 : 4 * L ^ 2 / 5 ≤ h := by rw [hh]; linarith [hre.2]
  have hh2 : h ≤ 6 * L ^ 2 / 5 := by rw [hh]; linarith [hre.1]
  have hL2 : 0 < L ^ 2 := by positivity
  have hhpos : 0 < h := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Δ.re := ⟨_, rfl⟩
  have hΔx : Δ = (x : ℂ) := by apply Complex.ext <;> simp [hx, hΔim]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = -Pw * h / 4 := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by
    rw [hs]
    have : 0 ≤ -Pw := by linarith
    positivity
  have hs1 : s ≤ 1 / 100 := by
    rw [hs]
    have : -Pw * h ≤ -Pw * (6 * L ^ 2 / 5) := mul_le_mul_of_nonneg_left hh2 (by linarith)
    nlinarith
  have hxe : x ^ 2 - 4 = Pw * -h := by
    have h1 := hΔ
    rw [hΔx, hPc, hHw] at h1
    exact_mod_cast h1
  have hx2 : x ^ 2 = 4 + 4 * s := by linear_combination hxe - 4 * hs
  have hnorm : ‖Δ‖ = |x| := by rw [hΔx, Complex.norm_real, Real.norm_eq_abs]
  have hsq : (|x| / 2) ^ 2 = 1 + s := by rw [div_pow, sq_abs, hx2]; ring
  have hhalf : |x| / 2 = √(1 + s) := by rw [← hsq, Real.sqrt_sq (by positivity)]
  have h2le : 2 ≤ ‖Δ‖ := by
    rw [hnorm]
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + s by linarith)
    rw [Real.sqrt_one] at this
    linarith [hhalf]
  have harc : Real.arcosh (|x| / 2) = Real.arsinh (√s) := by
    rw [hhalf]
    unfold Real.arcosh Real.arsinh
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 1 + s by linarith), Real.sq_sqrt hs0, add_sub_cancel_left,
      add_comm (√(1 + s)) (√s)]
  have hsqrt_s : √s = √(-Pw) * √h / 2 := by
    rw [hs, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul (by linarith : (0 : ℝ) ≤ -Pw),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hcpow : (-Hw) ^ (1 / 2 : ℂ) = ((√h : ℝ) : ℂ) := by
    rw [hHw, show -(((-h : ℝ)) : ℂ) = ((h : ℝ) : ℂ) by simp,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hhpos.le, Real.sqrt_eq_rpow]
  have hPH : Pc * Hw / 4 = ((s : ℝ) : ℂ) := by rw [hPc, hHw, hs]; push_cast; ring
  have hs1' : s < 1 := by linarith
  have hchi := chi_ofReal hs0 hs1'
  obtain ⟨hc1, hc2⟩ := chiR_bounds hs0
  obtain ⟨cR, hcR⟩ : ∃ c : ℝ, c = ∫ y in (0 : ℝ)..1, (√(1 + s * y ^ 2))⁻¹ := ⟨_, rfl⟩
  rw [← hcR] at hchi hc1 hc2
  have hD : (-Hw) ^ (1 / 2 : ℂ) / 2 * chi (Pc * Hw / 4) = ((√h / 2 * cR : ℝ) : ℂ) := by
    rw [hcpow, hPH, hchi]; push_cast; ring
  have harsinh := arsinh_sqrt_eq hs0 hs1'
  have hc0 : 0 ≤ cR := by
    have : 0 < 1 / (1 + s) := by positivity
    linarith
  have hcR' : 100 / 101 ≤ cR := by
    have : (100 : ℝ) / 101 ≤ 1 / (1 + s) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    linarith
  have hsqL : 8 * L / 9 ≤ √h := by
    have := Real.sqrt_le_sqrt (show (8 * L / 9) ^ 2 ≤ h by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at this
  have hsqU : √h ≤ 11 * L / 10 := by
    have := Real.sqrt_le_sqrt (show h ≤ (11 * L / 10) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at this
  refine ⟨h2le, ?_, ?_, ?_, ?_⟩
  · rw [hnorm, harc, harsinh, hD, hchi, hsqrt_s]; push_cast; ring
  · rw [hD, Complex.ofReal_im]
  · rw [hD, Complex.ofReal_re]
    nlinarith [mul_le_mul_of_nonneg_right hsqL hc0,
      mul_le_mul_of_nonneg_left hcR' (by positivity : (0 : ℝ) ≤ 8 * L / 9)]
  · rw [hD, Complex.ofReal_re]
    nlinarith [mul_le_mul_of_nonneg_right hsqU hc0, mul_le_mul_of_nonneg_left hc2 (Real.sqrt_nonneg h)]

/-! ## The even part `Ev` and the series eq. `GB01-r`, generic -/

/-- The even part: `Ev(σ) = (2πi)⁻¹ ∮_{|ξ| = R} G(ξ) ξ/(ξ² − σ) dξ`. -/
def Ev (G : ℂ → ℂ) (R : ℝ) (σ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ ξ in C(0, R), (ξ / (ξ ^ 2 - σ)) * G ξ

theorem Ev_sq {G : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hG : DifferentiableOn ℂ G (closedBall 0 R)) {ω : ℂ}
    (hω : ‖ω‖ < R) : Ev G R (ω ^ 2) = (G ω + G (-ω)) / 2 := by
  have hb1 : ω ∈ ball (0 : ℂ) R := by simpa using hω
  have hb2 : -ω ∈ ball (0 : ℂ) R := by simpa using hω
  have hsph : ∀ ξ ∈ sphere (0 : ℂ) R, ξ - ω ≠ 0 ∧ ξ - -ω ≠ 0 := by
    intro ξ hξ
    have hn : ‖ξ‖ = R := by simpa using hξ
    constructor
    · intro h; rw [sub_eq_zero] at h; rw [h] at hn; linarith
    · intro h; rw [sub_eq_zero] at h; rw [h, norm_neg] at hn; linarith
  have hcongr : EqOn (fun ξ => (ξ / (ξ ^ 2 - ω ^ 2)) * G ξ)
      (fun ξ => (2 : ℂ)⁻¹ • ((ξ - ω)⁻¹ • G ξ + (ξ - -ω)⁻¹ • G ξ)) (sphere (0 : ℂ) R) := by
    intro ξ hξ
    obtain ⟨h1, h2⟩ := hsph ξ hξ
    have h2' : ξ + ω ≠ 0 := by rwa [sub_neg_eq_add] at h2
    have h3 : ξ ^ 2 - ω ^ 2 ≠ 0 := by
      have : ξ ^ 2 - ω ^ 2 = (ξ - ω) * (ξ + ω) := by ring
      rw [this]; exact mul_ne_zero h1 h2'
    simp only [smul_eq_mul, sub_neg_eq_add]
    field_simp
    ring
  have hc1 : ContinuousOn (fun ξ : ℂ => (ξ - ω)⁻¹ • G ξ) (sphere (0 : ℂ) R) :=
    ContinuousOn.smul (f := fun ξ : ℂ => (ξ - ω)⁻¹) (g := G)
      (ContinuousOn.inv₀ (f := fun ξ : ℂ => ξ - ω) (by fun_prop) (fun ξ hξ => (hsph ξ hξ).1))
      (hG.continuousOn.mono sphere_subset_closedBall)
  have hc2 : ContinuousOn (fun ξ : ℂ => (ξ - -ω)⁻¹ • G ξ) (sphere (0 : ℂ) R) :=
    ContinuousOn.smul (f := fun ξ : ℂ => (ξ - -ω)⁻¹) (g := G)
      (ContinuousOn.inv₀ (f := fun ξ : ℂ => ξ - -ω) (by fun_prop) (fun ξ hξ => (hsph ξ hξ).2))
      (hG.continuousOn.mono sphere_subset_closedBall)
  unfold Ev
  rw [circleIntegral.integral_congr hR.le hcongr, circleIntegral.integral_smul,
    circleIntegral.integral_add (hc1.circleIntegrable hR.le) (hc2.circleIntegrable hR.le),
    hG.circleIntegral_sub_inv_smul hb1, hG.circleIntegral_sub_inv_smul hb2]
  have : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  simp only [smul_eq_mul]
  field_simp

/-- Taylor coefficients at `0`: `d_k = G^{(k)}(0)/k!`. -/
def dco (G : ℂ → ℂ) (k : ℕ) : ℂ := (k ! : ℂ)⁻¹ * iteratedDeriv k G 0

theorem summable_dco {G : ℂ → ℂ} {R₁ : ℝ} (hG : DifferentiableOn ℂ G (ball 0 R₁)) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < R₁) : Summable fun k : ℕ => ‖dco G k‖ * ρ ^ k := by
  obtain ⟨R', hR'1, hR'2⟩ := exists_between hρ
  have hR'pos : 0 < R' := hρ0.trans_lt hR'1
  set R'' : NNReal := ⟨R', hR'pos.le⟩ with hR''
  have hps : HasFPowerSeriesOnBall G (cauchyPowerSeries G 0 R'') 0 R'' :=
    (hG.mono (closedBall_subset_ball hR'2)).hasFPowerSeriesOnBall (by rw [← NNReal.coe_pos]; exact hR'pos)
  have hco : ∀ k, dco G k = cauchyPowerSeries G 0 R'' k (fun _ => 1) := by
    intro k
    have hne : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
    have := hps.factorial_smul 1 k
    rw [← iteratedDeriv_eq_iteratedFDeriv] at this
    unfold dco
    rw [← this, nsmul_eq_mul, inv_mul_cancel_left₀ hne]
  have hlt : ((ρ.toNNReal : NNReal) : ENNReal) < (cauchyPowerSeries G 0 R'').radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe (p := R'') hρ0).2 hR'1)) hps.r_le
  have hsum := (cauchyPowerSeries G 0 R'').summable_norm_mul_pow hlt
  simp only [Real.coe_toNNReal _ hρ0] at hsum
  refine hsum.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  rw [hco k]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hρ0 k)
  calc ‖cauchyPowerSeries G 0 R'' k (fun _ => 1)‖ ≤ ‖cauchyPowerSeries G 0 R'' k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries G 0 R'' k‖ := by simp

/-- `Ev(σ) = Σ_j d_{2j} σ^j` for `|σ| < R²`. -/
theorem hasSum_Ev {G : ℂ → ℂ} {R R₁ : ℝ} (hR : 0 < R) (hR₁ : R < R₁) (hG : DifferentiableOn ℂ G (ball 0 R₁))
    {σ : ℂ} (hσ : ‖σ‖ < R ^ 2) : HasSum (fun j : ℕ => dco G (2 * j) * σ ^ j) (Ev G R σ) := by
  obtain ⟨ω, rfl⟩ := IsAlgClosed.exists_pow_nat_eq σ (by norm_num : 0 < 2)
  have hωn : ‖ω‖ < R := by
    by_contra hc
    push_neg at hc
    rw [norm_pow] at hσ
    nlinarith [norm_nonneg ω]
  have hGc : DifferentiableOn ℂ G (closedBall 0 R) := hG.mono (closedBall_subset_ball hR₁)
  rw [Ev_sq hR hGc hωn]
  have hb1 : ω ∈ ball (0 : ℂ) R₁ := by rw [mem_ball_zero_iff]; linarith
  have hb2 : -ω ∈ ball (0 : ℂ) R₁ := by rw [mem_ball_zero_iff, norm_neg]; linarith
  have t := ((Complex.hasSum_taylorSeries_on_ball hG hb1).add
    (Complex.hasSum_taylorSeries_on_ball hG hb2)).div_const 2
  set term : ℕ → ℂ := fun k => ((k ! : ℂ)⁻¹ • (ω - 0) ^ k • iteratedDeriv k G 0 +
    (k ! : ℂ)⁻¹ • (-ω - 0) ^ k • iteratedDeriv k G 0) / 2 with hterm
  have hodd : ∀ k ∉ Set.range (fun j : ℕ => 2 * j), term k = 0 := by
    intro k hk
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ho
    · exact absurd ⟨j, by show 2 * j = k; omega⟩ hk
    · simp only [hterm, sub_zero, smul_eq_mul, ho.neg_pow]
      ring
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := fun a b h => by simpa using h
  rw [← hinj.hasSum_iff hodd] at t
  convert t using 1
  funext j
  simp only [Function.comp, hterm, dco, sub_zero, smul_eq_mul, (even_two_mul j).neg_pow, pow_mul]
  ring

/-- `β_j = ∫_{−1}^{1} s^{2j} √(1 − s²) ds`. -/
def betaJ (j : ℕ) : ℝ := ∫ s in (-1 : ℝ)..1, s ^ (2 * j) * √(1 - s ^ 2)

/-- `r` via the even part: `r = (4/(πL)) ∫_{−1}^{1} √(1 − s²) Ev(τ s²) ds`. -/
def rgen (L : ℝ) (G : ℂ → ℂ) (R : ℝ) (τ : ℂ) : ℂ :=
  4 / (Real.pi * L) * ∫ s in (-1 : ℝ)..1, ((√(1 - s ^ 2) : ℝ) : ℂ) * Ev G R (τ * (s : ℂ) ^ 2)

/-- eq. `GB01-r`: `(4/(πL)) Σ_j d_{2j} τ^j β_j`. -/
def rseries (L : ℝ) (G : ℂ → ℂ) (τ : ℂ) : ℂ :=
  4 / (Real.pi * L) * ∑' j : ℕ, dco G (2 * j) * τ ^ j * (betaJ j : ℂ)

/-- The route choice `rgen` equals the source series eq. `GB01-r` (absolutely convergent) for `|τ| < R²`. -/
theorem rgen_eq_series (L : ℝ) {G : ℂ → ℂ} {R R₁ : ℝ} (hR : 0 < R) (hR₁ : R < R₁)
    (hG : DifferentiableOn ℂ G (ball 0 R₁)) {τ : ℂ} (hτ : ‖τ‖ < R ^ 2) :
    Summable (fun j : ℕ => ‖dco G (2 * j)‖ * ‖τ‖ ^ j) ∧ rgen L G R τ = rseries L G τ := by
  have hρ : √‖τ‖ < R₁ := by
    have : √‖τ‖ < R := by
      rw [Real.sqrt_lt' hR]; exact hτ
    linarith
  have hS := (summable_dco hG (Real.sqrt_nonneg _) hρ).comp_injective
    (fun a b h => by simpa using h : Function.Injective (fun j : ℕ => 2 * j))
  have hS' : Summable (fun j : ℕ => ‖dco G (2 * j)‖ * ‖τ‖ ^ j) := by
    convert hS using 1
    funext j
    simp only [Function.comp, pow_mul, Real.sq_sqrt (norm_nonneg τ)]
  refine ⟨hS', ?_⟩
  have hint : ∀ j : ℕ, ∫ s in (-1 : ℝ)..1, ((√(1 - s ^ 2) : ℝ) : ℂ) * (dco G (2 * j) * τ ^ j * (s : ℂ) ^ (2 * j)) =
      dco G (2 * j) * τ ^ j * (betaJ j : ℂ) := by
    intro j
    have e : ∀ s : ℝ, ((√(1 - s ^ 2) : ℝ) : ℂ) * (dco G (2 * j) * τ ^ j * (s : ℂ) ^ (2 * j)) =
        dco G (2 * j) * τ ^ j * ((s ^ (2 * j) * √(1 - s ^ 2) : ℝ) : ℂ) := by
      intro s; push_cast; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    rfl
  have hb : ∀ j : ℕ, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (-1 : ℝ) 1 →
      ‖((√(1 - s ^ 2) : ℝ) : ℂ) * (dco G (2 * j) * τ ^ j * (s : ℂ) ^ (2 * j))‖ ≤ ‖dco G (2 * j)‖ * ‖τ‖ ^ j := by
    intro j
    refine ae_of_all _ fun s hs => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hs
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : √(1 - s ^ 2) ≤ 1 := by
      have := Real.sqrt_le_sqrt (show 1 - s ^ 2 ≤ 1 by nlinarith [sq_nonneg s])
      rwa [Real.sqrt_one] at this
    have h2 : |s| ^ (2 * j) ≤ 1 := by
      rw [pow_mul, sq_abs]; exact pow_le_one₀ (sq_nonneg s) hs2
    have h3 : 0 ≤ ‖dco G (2 * j)‖ * ‖τ‖ ^ j := by positivity
    calc √(1 - s ^ 2) * (‖dco G (2 * j)‖ * ‖τ‖ ^ j * |s| ^ (2 * j))
        ≤ 1 * (‖dco G (2 * j)‖ * ‖τ‖ ^ j * 1) := by
          apply mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 h3) (by positivity) zero_le_one
      _ = _ := by ring
  have hlim : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (-1 : ℝ) 1 →
      HasSum (fun j : ℕ => ((√(1 - s ^ 2) : ℝ) : ℂ) * (dco G (2 * j) * τ ^ j * (s : ℂ) ^ (2 * j)))
        (((√(1 - s ^ 2) : ℝ) : ℂ) * Ev G R (τ * (s : ℂ) ^ 2)) := by
    refine ae_of_all _ fun s hs => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hs
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    have hσ : ‖τ * (s : ℂ) ^ 2‖ < R ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      calc ‖τ‖ * s ^ 2 ≤ ‖τ‖ * 1 := mul_le_mul_of_nonneg_left hs2 (norm_nonneg _)
        _ < R ^ 2 := by rw [mul_one]; exact hτ
    have := (hasSum_Ev hR hR₁ hG hσ).mul_left (((√(1 - s ^ 2) : ℝ) : ℂ))
    convert this using 1
    funext j
    rw [mul_pow, ← pow_mul]
    ring
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := (volume : Measure ℝ))
    (a := (-1 : ℝ)) (b := 1)
    (F := fun j s => ((√(1 - s ^ 2) : ℝ) : ℂ) * (dco G (2 * j) * τ ^ j * (s : ℂ) ^ (2 * j)))
    (f := fun s => ((√(1 - s ^ 2) : ℝ) : ℂ) * Ev G R (τ * (s : ℂ) ^ 2))
    (fun j _ => ‖dco G (2 * j)‖ * ‖τ‖ ^ j)
    (fun j => (Continuous.aestronglyMeasurable (by fun_prop)))
    hb (ae_of_all _ fun _ _ => hS') intervalIntegrable_const hlim
  have key' : HasSum (fun j : ℕ => dco G (2 * j) * τ ^ j * (betaJ j : ℂ))
      (∫ s in (-1 : ℝ)..1, ((√(1 - s ^ 2) : ℝ) : ℂ) * Ev G R (τ * (s : ℂ) ^ 2)) := by
    convert key using 1
    funext j
    exact (hint j).symm
  unfold rgen rseries
  rw [key'.tsum_eq]

/-! ## The real slice -/

variable {L κ : ℝ} [Fact (0 < L)]

/-- `D_n` on the real slice (eq. `GB01-D` with `RB01RootCount.Hn`, `Pn`). -/
def Dn (hκ : 0 < κ) (q : L2T L) (n : ℤ) : ℂ → ℂ := Dgen (Hn hκ q n) (Pn hκ q n)

/-- `D_n` on the complexification (eq. `GB01-D` with `RB01Moments.HC`, `PC`). -/
def DC (κ : ℝ) (u v : L2T L) (n : ℤ) : ℂ → ℂ := Dgen (HC κ u v n) (PC κ u v n)

/-- `r_n` on the real slice (route choice: even part on `|ξ| = 2d`). -/
def rn (hκ : 0 < κ) (q : L2T L) (n : ℤ) : ℂ :=
  rgen L (fun ξ => Dn hκ q n ((alpha hκ q n : ℂ) + ξ)) (2 * dd L) (tau hκ q n)

/-- `r_n` on the complexification. -/
def rC (κ : ℝ) (u v : L2T L) (n : ℤ) : ℂ :=
  rgen L (fun ξ => DC κ u v n (alphaC κ u v n + ξ)) (2 * dd L) (tauC κ u v n)

/-- `H_n` is real on the real segment `|x| < 3d`. -/
theorem Hn_real (hκ : 0 < κ) (q : L2T L) (n : ℤ)
    (hfac : ∀ w : ℂ, ‖w‖ < 3 * dd L → fn κ q n w = Pn hκ q n w * Hn hκ q n w)
    (hdiff : DifferentiableOn ℂ (Hn hκ q n) (ball 0 (3 * dd L))) {x : ℝ} (hx : |x| < 3 * dd L) :
    (Hn hκ q n (x : ℂ)).im = 0 := by
  set p := QuantumNLS.LocalSpectral.pm L n with hp
  have hoff : ∀ y : ℝ, |y| < 3 * dd L → y ≠ bm hκ q n - p → y ≠ bp hκ q n - p →
      (Hn hκ q n (y : ℂ)).im = 0 := by
    intro y hy h1 h2
    have hPne : Pn hκ q n (y : ℂ) ≠ 0 := by
      rw [Pn_eq]
      refine mul_ne_zero (sub_ne_zero.2 fun h => h1 ?_) (sub_ne_zero.2 fun h => h2 ?_) <;> exact_mod_cast h
    have hfy := hfac (y : ℂ) (by rwa [Complex.norm_real, Real.norm_eq_abs])
    have hH : Hn hκ q n (y : ℂ) = fn κ q n (y : ℂ) / Pn hκ q n (y : ℂ) := by
      rw [hfy]; field_simp
    have e : ((p : ℂ) + (y : ℂ)) = ((p + y : ℝ) : ℂ) := by push_cast; ring
    have hr : (L2SpatialTransfer.discriminant κ q ((p + y : ℝ) : ℂ)).im = 0 := hreal κ q (p + y)
    have hr' : (L2SpatialTransfer.discriminant κ q ((p : ℂ) + (y : ℂ))).im = 0 := by rw [e]; exact hr
    have hfr : (fn κ q n (y : ℂ)).im = 0 := by
      show (L2SpatialTransfer.discriminant κ q ((p : ℂ) + (y : ℂ)) ^ 2 - 4).im = 0
      rw [Complex.sub_im, pow_two, Complex.mul_im, hr']
      simp
    have hPr : (Pn hκ q n (y : ℂ)).im = 0 := by
      unfold Pn; simp [pow_two]
    rw [hH, Complex.div_im, hfr, hPr]; simp
  have hcont : ContinuousAt (fun y : ℝ => (Hn hκ q n (y : ℂ)).im) x := by
    have hx' : (x : ℂ) ∈ ball (0 : ℂ) (3 * dd L) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx
    have hc : ContinuousAt (Hn hκ q n) (x : ℂ) :=
      (hdiff.differentiableAt (isOpen_ball.mem_nhds hx')).continuousAt
    exact Complex.continuous_im.continuousAt.comp (hc.comp Complex.continuous_ofReal.continuousAt)
  have hne : ∀ b : ℝ, ∀ᶠ y in 𝓝[≠] x, y ≠ b := by
    intro b
    by_cases hb : b = x
    · subst hb; exact eventually_mem_nhdsWithin.mono fun y hy => hy
    · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hb))
  have hball : ∀ᶠ y in 𝓝 x, |y| < 3 * dd L :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hx
  have hev : ∀ᶠ y : ℝ in 𝓝[≠] x, (Hn hκ q n (y : ℂ)).im = 0 := by
    filter_upwards [nhdsWithin_le_nhds hball, hne (bm hκ q n - p), hne (bp hκ q n - p)] with y hy h1 h2
    exact hoff y hy h1 h2
  have ht : Tendsto (fun y : ℝ => (Hn hκ q n (y : ℂ)).im) (𝓝[≠] x) (𝓝 ((Hn hκ q n (x : ℂ)).im)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hev.mono fun y hy => hy.symm))

/-- The conclusions of RB01Density for one field `q` and one label `n` (see module doc, items (a)-(g)). -/
def DensityFacts (hκ : 0 < κ) (q : L2T L) (n : ℤ) : Prop :=
  (∀ w : ℂ, ‖w‖ < 5 * dd L / 2 → ‖Pn hκ q n w * Hn hκ q n w / 4‖ < 1 / 2 ∧
      -Hn hκ q n w ∈ Complex.slitPlane ∧ DifferentiableAt ℂ (Dn hκ q n) w) ∧
  (∀ ζ : ℝ, |ζ| ≤ √(tau hκ q n) →
      ((Real.arcosh (‖L2SpatialTransfer.discriminant κ q
          ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ((alpha hκ q n + ζ : ℝ) : ℂ))‖ / 2) : ℝ) : ℂ) =
        ((√(tau hκ q n - ζ ^ 2) : ℝ) : ℂ) * Dn hκ q n ((alpha hκ q n + ζ : ℝ) : ℂ) ∧
      (Dn hκ q n ((alpha hκ q n + ζ : ℝ) : ℂ)).im = 0 ∧
      2 * L / 5 ≤ (Dn hκ q n ((alpha hκ q n + ζ : ℝ) : ℂ)).re ∧
      (Dn hκ q n ((alpha hκ q n + ζ : ℝ) : ℂ)).re ≤ 11 * L / 20) ∧
  ((((QuantumNLS.RootIndexedMasses.masses hκ q).1 n : ℝ) : ℂ) =
      (tau hκ q n : ℂ) / (Real.pi * κ) * ∫ s in (-1 : ℝ)..1, ((√(1 - s ^ 2) : ℝ) : ℂ) *
        Dn hκ q n ((alpha hκ q n : ℂ) + ((√(tau hκ q n) : ℝ) : ℂ) * (s : ℂ))) ∧
  (rn hκ q n = 4 / (Real.pi * L) * ∫ s in (-1 : ℝ)..1, ((√(1 - s ^ 2) : ℝ) : ℂ) *
        Dn hκ q n ((alpha hκ q n : ℂ) + ((√(tau hκ q n) : ℝ) : ℂ) * (s : ℂ))) ∧
  ((((QuantumNLS.RootIndexedMasses.masses hκ q).1 n : ℝ) : ℂ) =
      (L / (4 * κ) : ℂ) * (tau hκ q n : ℂ) * rn hκ q n ∧
    (rn hκ q n).im = 0 ∧ 1 / 2 < (rn hκ q n).re ∧ (rn hκ q n).re < 3 / 2) ∧
  (Summable (fun j : ℕ => ‖dco (fun ξ => Dn hκ q n ((alpha hκ q n : ℂ) + ξ)) (2 * j)‖ * ‖(tau hκ q n : ℂ)‖ ^ j) ∧
    rn hκ q n = rseries L (fun ξ => Dn hκ q n ((alpha hκ q n : ℂ) + ξ)) (tau hκ q n)) ∧
  (DC κ q (star q) n = Dn hκ q n ∧ rC κ q (star q) n = rn hκ q n)

/-- **RB01Density on the real slice** (hypotheses of `RB01RootCount.factor`). -/
theorem density_slice (hκ : 0 < κ) (q : L2T L) (n : ℤ)
    (ha : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L → ‖fn κ q n w - freeF L w‖ ≤ 6 * ε₀)
    (hb : ∀ w : ℂ, dd L / 8 ≤ ‖w‖ → ‖w‖ ≤ 4 * dd L → 10 / 65536 ≤ ‖fn κ q n w‖)
    (hlm : (boundary hκ q (QuantumNLS.LocalSpectral.pm L n - dd L)).re ∈
          Ioo (((n : ℝ) - 1) * Real.pi) ((n : ℝ) * Real.pi))
    (hlp : (boundary hκ q (QuantumNLS.LocalSpectral.pm L n + dd L)).re ∈
          Ioo ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi)) :
    DensityFacts hκ q n := by
  have hL : 0 < L := Fact.out
  have hd := dd_pos (L := L)
  have hdL : dd L * L = 1 / 4 := by unfold dd; field_simp
  have hπ := Real.pi_pos
  obtain ⟨hsa, hsb, -, -⟩ := cell_count hκ q n hb hlm hlp
  obtain ⟨hfac, hdiff, hH5, -⟩ := factor hκ q n ha hb hlm hlp
  obtain ⟨hle, -⟩ := lev_eq hκ q n
  obtain ⟨-, -, hαC, -, hτC, hPCe, hHCe⟩ := real_slice hκ q n ha hb hlm hlp
  have hDC : DC κ q (star q) n = Dn hκ q n := by unfold DC Dn; rw [hPCe, hHCe]
  have hrC : rC κ q (star q) n = rn hκ q n := by unfold rC rn; rw [hαC, hτC, hDC]
  have hmass0 := QuantumNLS.RB01MassCell.mass_eq_integral hκ q n
  have hαe : alpha hκ q n = (bm hκ q n + bp hκ q n) / 2 - QuantumNLS.LocalSpectral.pm L n := rfl
  have hτe : tau hκ q n = ((bp hκ q n - bm hκ q n) / 2) ^ 2 := rfl
  unfold DensityFacts
  set p := QuantumNLS.LocalSpectral.pm L n with hp
  set α := alpha hκ q n with hα
  set τ := tau hκ q n with hτ
  set a := bm hκ q n with ha'
  set b := bp hκ q n with hb'
  set t := √τ with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hte : t = (b - a) / 2 := by rw [ht, hτe, Real.sqrt_sq (by linarith)]
  have hτt : τ = t ^ 2 := by rw [ht, Real.sq_sqrt (by rw [hτe]; positivity)]
  rw [abs_lt] at hsa hsb
  have htd : t < dd L / 8 := by rw [hte]; linarith [hsa.1, hsa.2, hsb.1, hsb.2]
  have hαd : |α| < dd L / 8 := by rw [hαe, abs_lt]; constructor <;> linarith [hsa.1, hsa.2, hsb.1, hsb.2]
  -- bounds for `H_n` and `𝒫_n`
  have hL2 : ‖(L : ℂ) ^ 2‖ = L ^ 2 := by rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  have hHnorm : ∀ w : ℂ, ‖w‖ < 3 * dd L → ‖Hn hκ q n w‖ ≤ 6 * L ^ 2 / 5 ∧ (Hn hκ q n w).re < 0 := by
    intro w hw
    have h1 := hH5 w hw
    constructor
    · calc ‖Hn hκ q n w‖ = ‖(Hn hκ q n w + (L : ℂ) ^ 2) - (L : ℂ) ^ 2‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖Hn hκ q n w + (L : ℂ) ^ 2‖ + ‖(L : ℂ) ^ 2‖ := norm_sub_le _ _
        _ ≤ 6 * L ^ 2 / 5 := by rw [hL2]; linarith
    · have h2 := Complex.abs_re_le_norm (Hn hκ q n w + (L : ℂ) ^ 2)
      have e : (Hn hκ q n w + (L : ℂ) ^ 2).re = (Hn hκ q n w).re + L ^ 2 := by simp [pow_two]
      rw [e] at h2
      have := (abs_le.1 (h2.trans h1)).2
      have : 0 < L ^ 2 := by positivity
      linarith
  have hPnorm : ∀ w : ℂ, ∀ r : ℝ, ‖w‖ ≤ r → ‖Pn hκ q n w‖ ≤ (r + dd L / 8) ^ 2 := by
    intro w r hw
    rw [Pn_eq, norm_mul, pow_two]
    have h1 : ‖w - ((a - p : ℝ) : ℂ)‖ ≤ r + dd L / 8 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have : |a - p| ≤ dd L / 8 := abs_le.2 ⟨by linarith [hsa.1], by linarith [hsa.2]⟩
      linarith
    have h2 : ‖w - ((b - p : ℝ) : ℂ)‖ ≤ r + dd L / 8 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have : |b - p| ≤ dd L / 8 := abs_le.2 ⟨by linarith [hsb.1], by linarith [hsb.2]⟩
      linarith
    exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith [norm_nonneg w])
  -- (a)
  have hA : ∀ w : ℂ, ‖w‖ < 5 * dd L / 2 → ‖Pn hκ q n w * Hn hκ q n w / 4‖ < 1 / 2 ∧
      -Hn hκ q n w ∈ Complex.slitPlane ∧ DifferentiableAt ℂ (Dn hκ q n) w := by
    intro w hw
    have hw3 : ‖w‖ < 3 * dd L := by linarith
    obtain ⟨hHn, hHre⟩ := hHnorm w hw3
    have hP := hPnorm w (5 * dd L / 2) hw.le
    have hsmall : ‖Pn hκ q n w * Hn hκ q n w / 4‖ < 1 / 2 := by
      rw [norm_div, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
      have h1 : ‖Pn hκ q n w‖ * ‖Hn hκ q n w‖ ≤ (5 * dd L / 2 + dd L / 8) ^ 2 * (6 * L ^ 2 / 5) :=
        mul_le_mul hP hHn (norm_nonneg _) (by positivity)
      have h2 : (5 * dd L / 2 + dd L / 8) ^ 2 * (6 * L ^ 2 / 5) = 2646 / 5120 := by
        rw [show (5 * dd L / 2 + dd L / 8) ^ 2 * (6 * L ^ 2 / 5) = 441 * 6 / (64 * 5) * (dd L * L) ^ 2 by ring,
          hdL]
        norm_num
      rw [h2] at h1
      linarith
    have hslit : -Hn hκ q n w ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.2 (Or.inl (by rw [Complex.neg_re]; linarith))
    have hHd : DifferentiableAt ℂ (Hn hκ q n) w :=
      hdiff.differentiableAt (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; exact hw3))
    have hPd : DifferentiableAt ℂ (Pn hκ q n) w := by
      show DifferentiableAt ℂ (fun w => (w - (α : ℂ)) ^ 2 - (τ : ℂ)) w
      fun_prop
    exact ⟨hsmall, hslit, differentiableAt_Dgen hHd hPd hslit (by linarith)⟩
  -- (b) the gap
  have hgap : ∀ ζ : ℝ, |ζ| ≤ t →
      2 ≤ ‖L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + ζ : ℝ) : ℂ))‖ ∧
      (L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + ζ : ℝ) : ℂ))).im = 0 ∧
      ((Real.arcosh (‖L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + ζ : ℝ) : ℂ))‖ / 2) : ℝ) : ℂ) =
        ((√(τ - ζ ^ 2) : ℝ) : ℂ) * Dn hκ q n ((α + ζ : ℝ) : ℂ) ∧
      (Dn hκ q n ((α + ζ : ℝ) : ℂ)).im = 0 ∧ 2 * L / 5 ≤ (Dn hκ q n ((α + ζ : ℝ) : ℂ)).re ∧
      (Dn hκ q n ((α + ζ : ℝ) : ℂ)).re ≤ 11 * L / 20 := by
    intro ζ hζ
    have hy : |α + ζ| < 3 * dd L := by
      have := abs_add_le α ζ
      linarith
    have hy' : ‖((α + ζ : ℝ) : ℂ)‖ < 3 * dd L := by rwa [Complex.norm_real, Real.norm_eq_abs]
    have hfy := hfac _ hy'
    have hPc : Pn hκ q n ((α + ζ : ℝ) : ℂ) = ((ζ ^ 2 - τ : ℝ) : ℂ) := by
      show (((α + ζ : ℝ) : ℂ) - (α : ℂ)) ^ 2 - (τ : ℂ) = _
      push_cast; ring
    have hΔ : L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + ζ : ℝ) : ℂ)) ^ 2 - 4 =
        Pn hκ q n ((α + ζ : ℝ) : ℂ) * Hn hκ q n ((α + ζ : ℝ) : ℂ) := hfy
    have hΔim : (L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + ζ : ℝ) : ℂ))).im = 0 := by
      rw [show (p : ℂ) + ((α + ζ : ℝ) : ℂ) = ((p + (α + ζ) : ℝ) : ℂ) by push_cast; try ring]
      exact hreal κ q _
    have hHim := Hn_real hκ q n hfac hdiff hy
    have hζ2 : ζ ^ 2 ≤ τ := by
      rw [hτt]; have := pow_le_pow_left₀ (abs_nonneg ζ) hζ 2; rwa [sq_abs] at this
    have hPs : -(ζ ^ 2 - τ) * L ^ 2 ≤ 1 / 64 := by
      have h1 : -(ζ ^ 2 - τ) * L ^ 2 ≤ τ * L ^ 2 := by nlinarith [mul_nonneg (sq_nonneg ζ) (sq_nonneg L)]
      have h2 : τ * L ^ 2 = (t * L) ^ 2 := by rw [hτt]; ring
      have h3 : t * L < 1 / 32 := by
        have := mul_lt_mul_of_pos_right htd hL
        rw [show dd L / 8 * L = dd L * L / 8 by ring, hdL] at this; linarith
      have h4 : (t * L) ^ 2 < 1 / 64 := by nlinarith [mul_nonneg ht0 hL.le]
      linarith
    obtain ⟨g1, g2, g3, g4, g5⟩ := gap_point hL hPc hΔ hΔim hHim (hH5 _ hy') (by linarith) hPs
    rw [neg_sub] at g2
    exact ⟨g1, hΔim, g2, g3, g4, g5⟩
  -- (c) the mass
  set X := ∫ s in (-1 : ℝ)..1, ((√(1 - s ^ 2) : ℝ) : ℂ) * Dn hκ q n ((α : ℂ) + (t : ℂ) * (s : ℂ)) with hX
  have hts : ∀ s ∈ Icc (-1 : ℝ) 1, |t * s| ≤ t := by
    intro s hs
    rw [abs_mul, abs_of_nonneg ht0]
    have : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
    nlinarith
  have hpt : ∀ s ∈ Icc (-1 : ℝ) 1,
      ((QuantumNLS.RootDensityIdentification.dens κ q (t * s + (p + α)) : ℝ) : ℂ) =
        ((Real.pi : ℂ) * κ)⁻¹ * ((t : ℂ) * (((√(1 - s ^ 2) : ℝ) : ℂ) * Dn hκ q n ((α : ℂ) + (t : ℂ) * (s : ℂ)))) := by
    intro s hs
    obtain ⟨g1, g2, g3, -, -, -⟩ := hgap (t * s) (hts s hs)
    have ex : (((t * s + (p + α) : ℝ)) : ℂ) = (p : ℂ) + ((α + t * s : ℝ) : ℂ) := by push_cast; ring
    have hnre : ‖L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + t * s : ℝ) : ℂ))‖ =
        |(L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + t * s : ℝ) : ℂ))).re| := by
      have e : L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + t * s : ℝ) : ℂ)) =
          (((L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + t * s : ℝ) : ℂ))).re : ℝ) : ℂ) :=
        Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact g2)
      conv_lhs => rw [e]
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hsq : √(τ - (t * s) ^ 2) = t * √(1 - s ^ 2) := by
      rw [hτt, show t ^ 2 - (t * s) ^ 2 = t ^ 2 * (1 - s ^ 2) by ring, Real.sqrt_mul (sq_nonneg t),
        Real.sqrt_sq ht0]
    have e2 : ((α + t * s : ℝ) : ℂ) = (α : ℂ) + (t : ℂ) * (s : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_mul]
    unfold QuantumNLS.RootDensityIdentification.dens
    rw [ex, ← hnre, QuantumNLS.RootDensity.hfun_eq_arcosh_max,
      max_eq_left (show (1 : ℝ) ≤ ‖L2SpatialTransfer.discriminant κ q ((p : ℂ) + ((α + t * s : ℝ) : ℂ))‖ / 2 by
        linarith),
      Complex.ofReal_mul, g3, hsq, e2]
    push_cast
    ring
  have hmassX : (((QuantumNLS.RootIndexedMasses.masses hκ q).1 n : ℝ) : ℂ) = (τ : ℂ) / (Real.pi * κ) * X := by
    rw [hmass0, ← intervalIntegral.integral_ofReal]
    rcases ht0.eq_or_lt with h0 | hpos
    · have hab : b = a := by linarith [hte]
      rw [hab, intervalIntegral.integral_same, hτt, ← h0]
      simp
    · have hsub := intervalIntegral.integral_comp_mul_add
        (f := fun x => ((QuantumNLS.RootDensityIdentification.dens κ q x : ℝ) : ℂ)) (a := -1) (b := 1)
        hpos.ne' (p + α)
      have hlo : t * -1 + (p + α) = a := by rw [hte, hαe]; ring
      have hhi : t * 1 + (p + α) = b := by rw [hte, hαe]; ring
      rw [hlo, hhi] at hsub
      have hcongr : ∫ s in (-1 : ℝ)..1, ((QuantumNLS.RootDensityIdentification.dens κ q (t * s + (p + α)) : ℝ) : ℂ) =
          ((Real.pi : ℂ) * κ)⁻¹ * ((t : ℂ) * X) := by
        rw [intervalIntegral.integral_congr (g := fun s : ℝ => ((Real.pi : ℂ) * κ)⁻¹ * ((t : ℂ) *
          (((√(1 - s ^ 2) : ℝ) : ℂ) * Dn hκ q n ((α : ℂ) + (t : ℂ) * (s : ℂ))))) ?_]
        · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        · intro s hs
          rw [Set.uIcc_of_le (by norm_num)] at hs
          exact hpt s hs
      rw [hcongr] at hsub
      have hB : ∫ x in a..b, ((QuantumNLS.RootDensityIdentification.dens κ q x : ℝ) : ℂ) =
          t • (((Real.pi : ℂ) * κ)⁻¹ * ((t : ℂ) * X)) := by
        rw [hsub, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      rw [hB, Complex.real_smul, hτt]
      push_cast
      ring
  -- (d) `r_n` through the even part
  set G : ℂ → ℂ := fun ξ => Dn hκ q n ((α : ℂ) + ξ) with hGdef
  have hGd : DifferentiableOn ℂ G (ball 0 (19 * dd L / 8)) := by
    intro ξ hξ
    rw [mem_ball_zero_iff] at hξ
    have h1 : ‖(α : ℂ) + ξ‖ < 5 * dd L / 2 := by
      have := norm_add_le (α : ℂ) ξ
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    exact ((hA _ h1).2.2.comp ξ (by fun_prop : DifferentiableAt ℂ (fun y : ℂ => (α : ℂ) + y) ξ)).differentiableWithinAt
  have hnts : ∀ s ∈ Icc (-1 : ℝ) 1, ‖(t : ℂ) * (s : ℂ)‖ ≤ t := by
    intro s hs
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0]
    have : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
    nlinarith
  have hGcont : ContinuousOn (fun s : ℝ => G ((t : ℂ) * (s : ℂ))) (Icc (-1) 1) := by
    refine hGd.continuousOn.comp (by fun_prop : Continuous fun s : ℝ => (t : ℂ) * (s : ℂ)).continuousOn ?_
    intro s hs
    rw [mem_ball_zero_iff]
    linarith [hnts s hs]
  have hGcont' : ContinuousOn (fun s : ℝ => G (-((t : ℂ) * (s : ℂ)))) (Icc (-1) 1) := by
    refine hGd.continuousOn.comp (by fun_prop : Continuous fun s : ℝ => -((t : ℂ) * (s : ℂ))).continuousOn ?_
    intro s hs
    rw [mem_ball_zero_iff, norm_neg]
    linarith [hnts s hs]
  have hsqc : Continuous fun s : ℝ => ((√(1 - s ^ 2) : ℝ) : ℂ) := by fun_prop
  have hint1 : IntervalIntegrable (fun s : ℝ => ((√(1 - s ^ 2) : ℝ) : ℂ) * G ((t : ℂ) * (s : ℂ))) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    exact hsqc.continuousOn.mul hGcont
  have hint2 : IntervalIntegrable (fun s : ℝ => ((√(1 - s ^ 2) : ℝ) : ℂ) * G (-((t : ℂ) * (s : ℂ)))) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    exact hsqc.continuousOn.mul hGcont'
  have hX' : ∫ s in (-1 : ℝ)..1, ((√(1 - s ^ 2) : ℝ) : ℂ) * G ((t : ℂ) * (s : ℂ)) = X := rfl
  have hneg : ∫ s in (-1 : ℝ)..1, ((√(1 - s ^ 2) : ℝ) : ℂ) * G (-((t : ℂ) * (s : ℂ))) = X := by
    have := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
      (f := fun s : ℝ => ((√(1 - s ^ 2) : ℝ) : ℂ) * G ((t : ℂ) * (s : ℂ)))
    simp only [neg_neg, neg_sq, Complex.ofReal_neg, mul_neg] at this
    rw [this, hX']
  have hrn : rn hκ q n = 4 / (Real.pi * L) * X := by
    have hEv : ∀ s ∈ Set.uIcc (-1 : ℝ) 1,
        ((√(1 - s ^ 2) : ℝ) : ℂ) * Ev G (2 * dd L) ((τ : ℂ) * (s : ℂ) ^ 2) =
          ((√(1 - s ^ 2) : ℝ) : ℂ) * G ((t : ℂ) * (s : ℂ)) / 2 +
            ((√(1 - s ^ 2) : ℝ) : ℂ) * G (-((t : ℂ) * (s : ℂ))) / 2 := by
      intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      have hω : ‖(t : ℂ) * (s : ℂ)‖ < 2 * dd L := by linarith [hnts s hs]
      have e : (τ : ℂ) * (s : ℂ) ^ 2 = ((t : ℂ) * (s : ℂ)) ^ 2 := by rw [hτt]; push_cast; ring
      rw [e, Ev_sq (by positivity) (hGd.mono (closedBall_subset_ball (by linarith))) hω]
      ring
    show rgen L G (2 * dd L) (τ : ℂ) = _
    unfold rgen
    rw [intervalIntegral.integral_congr hEv, intervalIntegral.integral_add (hint1.div_const 2) (hint2.div_const 2),
      intervalIntegral.integral_div, intervalIntegral.integral_div, hneg, hX']
    ring
  -- (e) the mass factor and the bounds for `r_n`
  have hDre : ∀ s ∈ Icc (-1 : ℝ) 1, G ((t : ℂ) * (s : ℂ)) = (((G ((t : ℂ) * (s : ℂ))).re : ℝ) : ℂ) ∧
      2 * L / 5 ≤ (G ((t : ℂ) * (s : ℂ))).re ∧ (G ((t : ℂ) * (s : ℂ))).re ≤ 11 * L / 20 := by
    intro s hs
    obtain ⟨-, -, -, g4, g5, g6⟩ := hgap (t * s) (hts s hs)
    have e : G ((t : ℂ) * (s : ℂ)) = Dn hκ q n ((α + t * s : ℝ) : ℂ) := by
      show Dn hκ q n ((α : ℂ) + (t : ℂ) * (s : ℂ)) = _
      rw [Complex.ofReal_add, Complex.ofReal_mul]
    rw [e]
    exact ⟨Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact g4), g5, g6⟩
  have hXr : X = ((∫ s in (-1 : ℝ)..1, √(1 - s ^ 2) * (G ((t : ℂ) * (s : ℂ))).re : ℝ) : ℂ) := by
    rw [← hX', ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    show ((√(1 - s ^ 2) : ℝ) : ℂ) * G ((t : ℂ) * (s : ℂ)) = _
    conv_lhs => rw [(hDre s hs).1]
    push_cast
    ring
  have hcR : ContinuousOn (fun s : ℝ => √(1 - s ^ 2) * (G ((t : ℂ) * (s : ℂ))).re) (Icc (-1) 1) :=
    (by fun_prop : Continuous fun s : ℝ => √(1 - s ^ 2)).continuousOn.mul
      (Complex.continuous_re.comp_continuousOn hGcont)
  have hII : IntervalIntegrable (fun s : ℝ => √(1 - s ^ 2) * (G ((t : ℂ) * (s : ℂ))).re) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le (by norm_num)]; exact hcR)
  have hsqI : IntervalIntegrable (fun s : ℝ => √(1 - s ^ 2)) volume (-1) 1 :=
    (by fun_prop : Continuous fun s : ℝ => √(1 - s ^ 2)).intervalIntegrable _ _
  have hlo : Real.pi / 2 * (2 * L / 5) ≤ ∫ s in (-1 : ℝ)..1, √(1 - s ^ 2) * (G ((t : ℂ) * (s : ℂ))).re := by
    have := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) (hsqI.mul_const (2 * L / 5)) hII
      (fun s hs => mul_le_mul_of_nonneg_left (hDre s hs).2.1 (Real.sqrt_nonneg _))
    rwa [intervalIntegral.integral_mul_const, integral_sqrt_one_sub_sq] at this
  have hhi : ∫ s in (-1 : ℝ)..1, √(1 - s ^ 2) * (G ((t : ℂ) * (s : ℂ))).re ≤ Real.pi / 2 * (11 * L / 20) := by
    have := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hII (hsqI.mul_const (11 * L / 20))
      (fun s hs => mul_le_mul_of_nonneg_left (hDre s hs).2.2 (Real.sqrt_nonneg _))
    rwa [intervalIntegral.integral_mul_const, integral_sqrt_one_sub_sq] at this
  set Xr := ∫ s in (-1 : ℝ)..1, √(1 - s ^ 2) * (G ((t : ℂ) * (s : ℂ))).re with hXrdef
  have hrnR : rn hκ q n = ((4 / (Real.pi * L) * Xr : ℝ) : ℂ) := by
    rw [hrn, hXr]; push_cast; ring
  have hc1 : 4 / (Real.pi * L) * (Real.pi / 2 * (2 * L / 5)) = 4 / 5 := by field_simp; try ring
  have hc2 : 4 / (Real.pi * L) * (Real.pi / 2 * (11 * L / 20)) = 11 / 10 := by field_simp; try ring
  have hk : 0 ≤ 4 / (Real.pi * L) := by positivity
  have hr1 := mul_le_mul_of_nonneg_left hlo hk
  have hr2 := mul_le_mul_of_nonneg_left hhi hk
  rw [hc1] at hr1
  rw [hc2] at hr2
  have hfactor : (((QuantumNLS.RootIndexedMasses.masses hκ q).1 n : ℝ) : ℂ) =
      (L / (4 * κ) : ℂ) * (τ : ℂ) * rn hκ q n := by
    have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    rw [hmassX, hrn]
    field_simp
    try ring
  -- (f) eq. `GB01-r`
  have hτn : ‖(τ : ℂ)‖ < (2 * dd L) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by rw [hτt]; positivity), hτt]
    nlinarith
  obtain ⟨hS, hser⟩ := rgen_eq_series L (by positivity : (0 : ℝ) < 2 * dd L)
    (by linarith : 2 * dd L < 19 * dd L / 8) hGd hτn
  refine ⟨hA, fun ζ hζ => ?_, hmassX, hrn, ⟨hfactor, ?_, ?_, ?_⟩, ⟨hS, hser⟩, hDC, hrC⟩
  · obtain ⟨-, -, g3, g4, g5, g6⟩ := hgap ζ hζ
    exact ⟨g3, g4, g5, g6⟩
  · rw [hrnR, Complex.ofReal_im]
  · rw [hrnR, Complex.ofReal_re]; linarith
  · rw [hrnR, Complex.ofReal_re]; linarith

/-- **RB01Density, packaged**: for every `u₀` there are `N`, `ρ > 0` such that the conclusions hold for every
label `|n| > N`, every `‖u − u₀‖ < ρ` and every `q = t·u`, `t ∈ [0, 1]`. -/
theorem density (hκ : 0 < κ) (u₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ u : L2T L, ‖u - u₀‖ < ρ →
      ∀ t ∈ Icc (0 : ℝ) 1, DensityFacts hκ (t • u) n := by
  obtain ⟨N, ρ, hρ, h⟩ := root_prep κ u₀
  refine ⟨N, ρ, hρ, fun n hn u hu t ht => ?_⟩
  have ep : ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ((dd L : ℝ) : ℂ)) =
      ((QuantumNLS.LocalSpectral.pm L n + dd L : ℝ) : ℂ) := by push_cast; ring
  have em : ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ((-dd L : ℝ) : ℂ)) =
      ((QuantumNLS.LocalSpectral.pm L n - dd L : ℝ) : ℂ) := by push_cast; ring
  have hm : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖Dl κ (s • u) ((QuantumNLS.LocalSpectral.pm L n - dd L : ℝ) : ℂ)‖ < 2 := by
    intro s hs; have := (h n hn u hu s hs).2.2.2.2.1; rw [em] at this; exact this
  have hp : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖Dl κ (s • u) ((QuantumNLS.LocalSpectral.pm L n + dd L : ℝ) : ℂ)‖ < 2 := by
    intro s hs; have := (h n hn u hu s hs).2.2.2.1; rw [ep] at this; exact this
  obtain ⟨hlm, hlp⟩ := labels hκ u n hm hp t ht
  obtain ⟨ha, hb, -, -, -, -⟩ := h n hn u hu t ht
  exact density_slice hκ (t • u) n ha hb hlm hlp

end QuantumNLS.RB01Density

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RB01Density.chi_eq_integral
#print axioms QuantumNLS.RB01Density.arsinh_sqrt_eq
#print axioms QuantumNLS.RB01Density.hasFPowerSeries_chi
#print axioms QuantumNLS.RB01Density.gap_point
#print axioms QuantumNLS.RB01Density.Ev_sq
#print axioms QuantumNLS.RB01Density.hasSum_Ev
#print axioms QuantumNLS.RB01Density.rgen_eq_series
#print axioms QuantumNLS.RB01Density.Hn_real
#print axioms QuantumNLS.RB01Density.density_slice
#print axioms QuantumNLS.RB01Density.density
