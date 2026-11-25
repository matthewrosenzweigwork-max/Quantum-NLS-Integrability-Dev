import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import NlsGge.Weights.Size
import NlsGge.Weights.DerivativeAsymptotics
import NlsGge.Measure.CountableGaussian
import Mathlib.Tactic

/-! L07: D:prop:ALfree (v2 l.2228-2250), free-field convergence and failure at the critical
weight.  Mesh: `L = 2N+1`, `h = 1/L`.  All coordinate-level, W from `NlsGge.Weights.weight`. -/

set_option autoImplicit false
noncomputable section
namespace NlsGge.AblowitzLadik

open NlsGge.Weights NlsGge.Measure NlsGge.Pilot NlsGge.HierarchyRiccati.Core MeasureTheory Filter
open scoped Topology ENNReal

/-- Hypotheses on the coefficients of the weight: `0 < c_- ≤ c_j ≤ c_+`. -/
def AdmissibleWeight38 (lower upper : ℝ) (c : ℕ → ℝ) : Prop :=
  0 < lower ∧ (∀ j : ℕ, lower ≤ c j) ∧ (∀ j : ℕ, c j ≤ upper)

/-- Mesh `h = 1/L`, `L = 2N+1`. -/
def alMeshStep38 (N : ℕ) : ℝ := 1 / (2 * (N : ℝ) + 1)

/-- `ω_{h,k} = 2 sin(π k h)/h` (D:eq:omega), `h = 1/(2N+1)`. -/
def alOmegaFree38 (N : ℕ) (k : ℤ) : ℝ :=
  2 * Real.sin (Real.pi * (k : ℝ) * alMeshStep38 N) / alMeshStep38 N

/-- Continuum rates `a_k = W(2πk)`. -/
def alRateCont38 (c : ℕ → ℝ) (k : ℤ) : ℝ := weight c (2 * Real.pi * (k : ℝ))

/-- Lattice rates `a_{h,k} = W(ω_{h,k}) - h` (D:eq:ALrates). -/
def alRateFree38 (c : ℕ → ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  weight c (alOmegaFree38 N k) - alMeshStep38 N

/-- Lower comparison weight `W(4|k|)`. -/
def alRateComp38 (c : ℕ → ℝ) (k : ℤ) : ℝ := weight c (4 * |(k : ℝ)|)

/-- Fourier coefficients of `U_h = Σ_{|k|≤N} g_k a_{h,k}^{-1/2} e^{2πikx}`. -/
def alUhCoef38 (c : ℕ → ℝ) (N : ℕ) (g : ℤ → ℂ) (k : ℤ) : ℂ :=
  if |k| ≤ (N : ℤ) then g k / (Real.sqrt (alRateFree38 c N k) : ℂ) else 0

/-- Fourier coefficients of `U = Σ_k g_k a_k^{-1/2} e^{2πikx}`. -/
def alUCoef38 (c : ℕ → ℝ) (g : ℤ → ℂ) (k : ℤ) : ℂ :=
  g k / (Real.sqrt (alRateCont38 c k) : ℂ)

/-- `U_h` realized in the ordinary Sobolev space `H^s`. -/
def alUhRealization38 (s : ℝ) (c : ℕ → ℝ) (N : ℕ) (g : ℤ → ℂ) : SobolevHilbert s :=
  seqRealization38 (sobolevModeWeight s) (alUhCoef38 c N g)

/-- `U` realized in `H^s` (totalized: zero if the series is not in `H^s`). -/
def alURealization38 (s : ℝ) (c : ℕ → ℝ) (g : ℤ → ℂ) : SobolevHilbert s :=
  seqRealization38 (sobolevModeWeight s) (alUCoef38 c g)

section Basic

variable {lower upper : ℝ} {c : ℕ → ℝ}

theorem weight_mono_abs38 (hA : AdmissibleWeight38 lower upper c) {r r' : ℝ}
    (h : |r| ≤ |r'|) : weight c r ≤ weight c r' := by
  obtain ⟨hl, hb, hu⟩ := hA
  unfold weight
  refine Summable.tsum_le_tsum (fun j => ?_)
    (weightTerm_summable lower upper c hl hb hu r) (weightTerm_summable lower upper c hl hb hu r')
  rw [weightTerm_eq_fourth_power, weightTerm_eq_fourth_power]
  have hc : 0 ≤ c j := (hl.le).trans (hb j)
  have : Real.sqrt |r| ≤ Real.sqrt |r'| := Real.sqrt_le_sqrt h
  gcongr

theorem alMeshStep_pos38 (N : ℕ) : 0 < alMeshStep38 N := by
  unfold alMeshStep38; positivity

theorem alMeshStep_le38 (N : ℕ) : alMeshStep38 N ≤ 1 / (2 * (N : ℝ) + 1) := le_rfl

theorem alMeshStep_tendsto38 : Tendsto alMeshStep38 atTop (𝓝 0) := by
  unfold alMeshStep38
  have : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  refine (this.inv_tendsto_atTop).congr (fun N => ?_)
  simp [one_div]

/-- Sine bounds `4|k| ≤ |ω_{h,k}| ≤ 2π|k|` for `|k| ≤ N` (the source has `|k|h ≤ 1/2`). -/
theorem alOmega_abs_bounds38 (N : ℕ) (k : ℤ) (hk : |k| ≤ (N : ℤ)) :
    4 * |(k : ℝ)| ≤ |alOmegaFree38 N k| ∧ |alOmegaFree38 N k| ≤ 2 * Real.pi * |(k : ℝ)| := by
  have hh := alMeshStep_pos38 N
  have hkN : |(k : ℝ)| ≤ N := by
    have : ((|k| : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    simpa using this
  have hx0 : 0 ≤ |(k : ℝ)| * alMeshStep38 N := by positivity
  have hx1 : |(k : ℝ)| * alMeshStep38 N ≤ 1 / 2 := by
    unfold alMeshStep38
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hpx : 0 ≤ Real.pi * (|(k : ℝ)| * alMeshStep38 N) := by positivity
  have hpx2 : Real.pi * (|(k : ℝ)| * alMeshStep38 N) ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hs0 : 0 ≤ Real.sin (Real.pi * (|(k : ℝ)| * alMeshStep38 N)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hpx (by linarith [Real.pi_pos])
  have hsin : |Real.sin (Real.pi * (k : ℝ) * alMeshStep38 N)| =
      Real.sin (Real.pi * (|(k : ℝ)| * alMeshStep38 N)) := by
    rcases abs_cases (k : ℝ) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
      have e : Real.pi * (k : ℝ) * alMeshStep38 N = Real.pi * ((k : ℝ) * alMeshStep38 N) := by ring
      rw [e]; exact abs_of_nonneg (by rw [← h1]; exact hs0)
    · rw [h1]
      have e : Real.pi * (k : ℝ) * alMeshStep38 N = -(Real.pi * (-(k : ℝ) * alMeshStep38 N)) := by ring
      rw [e, Real.sin_neg, abs_neg]
      exact abs_of_nonneg (by rw [← h1]; exact hs0)
  have habs : |alOmegaFree38 N k| =
      2 * Real.sin (Real.pi * (|(k : ℝ)| * alMeshStep38 N)) / alMeshStep38 N := by
    unfold alOmegaFree38
    rw [abs_div, abs_mul, hsin, abs_of_pos hh, abs_two]
  rw [habs]
  have hjor := Real.mul_le_sin hpx hpx2
  have hle := Real.sin_le hpx
  constructor
  · rw [le_div_iff₀ hh]
    have : 2 / Real.pi * (Real.pi * (|(k : ℝ)| * alMeshStep38 N)) = 2 * (|(k : ℝ)| * alMeshStep38 N) := by
      field_simp
    nlinarith
  · rw [div_le_iff₀ hh]
    nlinarith

/-- Eventually `a_{h,k} ≥ W(4|k|)/2` for all `|k| ≤ N`. -/
theorem alRateFree_ge38 (hA : AdmissibleWeight38 lower upper c) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℤ, |k| ≤ (N : ℤ) →
      alRateComp38 c k / 2 ≤ alRateFree38 c N k := by
  have hl := hA.1
  filter_upwards [alMeshStep_tendsto38.eventually (gt_mem_nhds (half_pos hl))] with N hN k hk
  obtain ⟨h1, _⟩ := alOmega_abs_bounds38 N k hk
  have hmono : alRateComp38 c k ≤ weight c (alOmegaFree38 N k) := by
    apply weight_mono_abs38 hA
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * |(k : ℝ)|)]
    exact h1
  have hlow := weight_lower lower upper c hl hA.2.1 hA.2.2 (alOmegaFree38 N k)
  unfold alRateFree38
  linarith

end Basic

section Summability

theorem poly_exp_bound38 (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      (1 + x ^ 2) ^ r * (1 + 4 * x) ^ (3 / 4 : ℝ) * x ^ 2 ≤ C * Real.exp (8 * Real.sqrt x) := by
  set m : ℕ := 2 * r + 3 with hm
  refine ⟨2 ^ r * 5 * ((2 * m).factorial : ℝ) / 64 ^ m, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 : (1 + x ^ 2) ^ r ≤ 2 ^ r * x ^ (2 * r) := by
    calc (1 + x ^ 2) ^ r ≤ (2 * x ^ 2) ^ r :=
          pow_le_pow_left₀ (by positivity) (by nlinarith) r
      _ = 2 ^ r * x ^ (2 * r) := by rw [mul_pow, ← pow_mul]
  have h2 : (1 + 4 * x) ^ (3 / 4 : ℝ) ≤ 5 * x := by
    calc (1 + 4 * x) ^ (3 / 4 : ℝ) ≤ (1 + 4 * x) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 1 + 4 * x := Real.rpow_one _
      _ ≤ 5 * x := by linarith
  have h3 : (8 * Real.sqrt x) ^ (2 * m) / ((2 * m).factorial : ℝ) ≤ Real.exp (8 * Real.sqrt x) :=
    Real.pow_div_factorial_le_exp _ (by positivity) _
  have h4 : (8 * Real.sqrt x) ^ (2 * m) = 64 ^ m * x ^ m := by
    rw [pow_mul, mul_pow, Real.sq_sqrt hx0.le]
    norm_num [mul_pow]
  rw [h4] at h3
  have hfac : (0 : ℝ) < ((2 * m).factorial : ℝ) := by positivity
  have h5 : 64 ^ m * x ^ m ≤ ((2 * m).factorial : ℝ) * Real.exp (8 * Real.sqrt x) := by
    rw [div_le_iff₀ hfac] at h3
    linarith
  have h6 : (1 + x ^ 2) ^ r * (1 + 4 * x) ^ (3 / 4 : ℝ) * x ^ 2 ≤ 2 ^ r * 5 * x ^ m := by
    calc (1 + x ^ 2) ^ r * (1 + 4 * x) ^ (3 / 4 : ℝ) * x ^ 2
        ≤ (2 ^ r * x ^ (2 * r)) * (5 * x) * x ^ 2 := by
          gcongr
      _ = 2 ^ r * 5 * x ^ m := by rw [hm]; ring
  calc _ ≤ 2 ^ r * 5 * x ^ m := h6
    _ = (2 ^ r * 5 / 64 ^ m) * (64 ^ m * x ^ m) := by field_simp
    _ ≤ (2 ^ r * 5 / 64 ^ m) * (((2 * m).factorial : ℝ) * Real.exp (8 * Real.sqrt x)) := by
          gcongr
    _ = _ := by ring

theorem alComp_summable38 {lower upper : ℝ} {c : ℕ → ℝ} (hA : AdmissibleWeight38 lower upper c)
    (r : ℕ) : Summable (fun k : ℤ => (1 + (k : ℝ) ^ 2) ^ r / alRateComp38 c k) := by
  obtain ⟨hl, hb, hu⟩ := hA
  have hlu : lower ≤ upper := (hb 0).trans (hu 0)
  obtain ⟨A, B, hA0, hB0, hsize⟩ := weight_two_sided_size lower upper hl hlu
  obtain ⟨C, hC, hpoly⟩ := poly_exp_bound38 r
  have hg : Summable (fun k : ℤ => (C / A) * (1 / (k : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  have : ∀ k : ℤ, k ≠ 0 → ‖(1 + (k : ℝ) ^ 2) ^ r / alRateComp38 c k‖ ≤ (C / A) * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    have hx : 1 ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast this
    set x := |(k : ℝ)| with hxdef
    have hx0 : 0 < x := by linarith
    have hW := (hsize c hb hu (4 * x)).1
    have habs : |4 * x| = 4 * x := abs_of_pos (by positivity)
    rw [habs] at hW
    have hsq : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsq] at hW
    have hk2 : (k : ℝ) ^ 2 = x ^ 2 := (sq_abs _).symm
    have hWpos : 0 < alRateComp38 c k := by
      unfold alRateComp38
      exact weight_pos lower upper c hl hb hu _
    have hWge : A * (1 + 4 * x) ^ (-3 / 4 : ℝ) * Real.exp (4 * (2 * Real.sqrt x)) ≤ alRateComp38 c k := hW
    have hp0 : 0 < (1 + 4 * x) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hneg : (1 + 4 * x) ^ (-3 / 4 : ℝ) = ((1 + 4 * x) ^ (3 / 4 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg (by linarith)]; norm_num
    rw [hneg] at hWge
    have hE : Real.exp (4 * (2 * Real.sqrt x)) = Real.exp (8 * Real.sqrt x) := by ring_nf
    rw [hE] at hWge
    have hpk := hpoly x hx
    rw [Real.norm_of_nonneg (by positivity), hk2, one_div, ← div_eq_mul_inv, div_le_div_iff₀ hWpos (by positivity)]
    have hexp := Real.exp_pos (8 * Real.sqrt x)
    -- (1+x²)^r * x² ≤ (C/A) * W
    have : (1 + x ^ 2) ^ r * x ^ 2 * (1 + 4 * x) ^ (3 / 4 : ℝ) ≤ C * Real.exp (8 * Real.sqrt x) := by
      linarith [hpk, show (1 + x ^ 2) ^ r * (1 + 4 * x) ^ (3 / 4 : ℝ) * x ^ 2 =
        (1 + x ^ 2) ^ r * x ^ 2 * (1 + 4 * x) ^ (3 / 4 : ℝ) by ring]
    have h7 : A * Real.exp (8 * Real.sqrt x) ≤ alRateComp38 c k * (1 + 4 * x) ^ (3 / 4 : ℝ) := by
      calc A * Real.exp (8 * Real.sqrt x) = (A * ((1 + 4 * x) ^ (3 / 4 : ℝ))⁻¹ * Real.exp (8 * Real.sqrt x)) *
            (1 + 4 * x) ^ (3 / 4 : ℝ) := by field_simp
        _ ≤ _ := by gcongr
    have hA' : 0 < A := hA0
    rw [div_mul_eq_mul_div, le_div_iff₀ hA']
    calc (1 + x ^ 2) ^ r * x ^ 2 * A
        = ((1 + x ^ 2) ^ r * x ^ 2 * (1 + 4 * x) ^ (3 / 4 : ℝ)) * A / (1 + 4 * x) ^ (3 / 4 : ℝ) := by
          field_simp
      _ ≤ (C * Real.exp (8 * Real.sqrt x)) * A / (1 + 4 * x) ^ (3 / 4 : ℝ) := by gcongr
      _ = C * (A * Real.exp (8 * Real.sqrt x)) / (1 + 4 * x) ^ (3 / 4 : ℝ) := by ring
      _ ≤ C * (alRateComp38 c k * (1 + 4 * x) ^ (3 / 4 : ℝ)) / (1 + 4 * x) ^ (3 / 4 : ℝ) := by gcongr
      _ = C * alRateComp38 c k := by field_simp
  have hcof : {k : ℤ | k ≠ 0} ∈ cofinite := by
    rw [Filter.mem_cofinite]
    simp
  filter_upwards [hcof] with k hk using this k hk

end Summability


section Sobolev

variable (w : ℤ → ℝ) [hw : Fact (∀ n : ℤ, 0 < w n)]
  [MeasurableSpace (WeightedRealHilbert w)] [BorelSpace (WeightedRealHilbert w)]

/-- Squared Sobolev distance of two realized sequences is the weighted square sum of the difference. -/
theorem seqRealization_dist_sq38 (x y : ℤ → ℂ)
    (hx : Summable (fun n : ℤ => w n * ‖x n‖ ^ 2)) (hy : Summable (fun n : ℤ => w n * ‖y n‖ ^ 2)) :
    ‖(seqRealization38 w x - seqRealization38 w y : WeightedRealHilbert w)‖ ^ 2 =
      ∑' n : ℤ, w n * ‖x n - y n‖ ^ 2 := by
  have h := weightedHilbert_norm_sq w
    (show WeightedHilbert w from (seqRealization38 w x - seqRealization38 w y : WeightedRealHilbert w))
  refine h.trans (tsum_congr (fun n => ?_))
  have e : ((show WeightedHilbert w from
      (seqRealization38 w x - seqRealization38 w y : WeightedRealHilbert w)) : ℤ → ℂ) n =
      x n - y n := by
    have e1 := seqRealization_apply38 w x hx n
    have e2 := seqRealization_apply38 w y hy n
    change ((show WeightedHilbert w from seqRealization38 w x) n) - (show WeightedHilbert w from seqRealization38 w y) n = _
    rw [e1, e2]
  rw [e]

end Sobolev


section RatesLimit

variable {lower upper : ℝ} {c : ℕ → ℝ}

theorem weight_continuous38 (hA : AdmissibleWeight38 lower upper c) : Continuous (weight c) :=
  continuous_iff_continuousAt.2 fun r =>
    (weight_hasDerivAt lower upper c hA.1 hA.2.1 hA.2.2 r).continuousAt

theorem alOmega_tendsto38 (k : ℤ) :
    Tendsto (fun N : ℕ => alOmegaFree38 N k) atTop (𝓝 (2 * Real.pi * (k : ℝ))) := by
  have hd : HasDerivAt (fun t : ℝ => Real.sin (Real.pi * (k : ℝ) * t)) (Real.pi * (k : ℝ)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul (Real.pi * (k : ℝ))).sin
    simpa using this
  have ht := hd.tendsto_slope_zero
  have hmesh : Tendsto alMeshStep38 atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨alMeshStep_tendsto38,
      Eventually.of_forall fun N => (alMeshStep_pos38 N).ne'⟩
  have h2 := (ht.comp hmesh).const_mul 2
  have e : 2 * Real.pi * (k : ℝ) = 2 * (Real.pi * (k : ℝ)) := by ring
  rw [e]
  refine h2.congr (fun N => ?_)
  simp [alOmegaFree38, div_eq_inv_mul]
  ring

theorem alRateFree_tendsto38 (hA : AdmissibleWeight38 lower upper c) (k : ℤ) :
    Tendsto (fun N : ℕ => alRateFree38 c N k) atTop (𝓝 (alRateCont38 c k)) := by
  have h1 := ((weight_continuous38 hA).continuousAt.tendsto.comp (alOmega_tendsto38 k)).sub
    alMeshStep_tendsto38
  simpa [alRateFree38, alRateCont38, Function.comp_def] using h1

theorem alRateComp_le_cont38 (hA : AdmissibleWeight38 lower upper c) (k : ℤ) :
    alRateComp38 c k ≤ alRateCont38 c k := by
  apply weight_mono_abs38 hA
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * |(k : ℝ)|), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  nlinarith [Real.pi_gt_three, abs_nonneg (k : ℝ)]

theorem alRateComp_pos38 (hA : AdmissibleWeight38 lower upper c) (k : ℤ) :
    0 < alRateComp38 c k :=
  weight_pos lower upper c hA.1 hA.2.1 hA.2.2 _

theorem coef_diff_norm_sq38 (z : ℂ) (a b : ℝ) :
    ‖z / (Real.sqrt a : ℂ) - z / (Real.sqrt b : ℂ)‖ ^ 2 =
      ‖z‖ ^ 2 * ((Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹) ^ 2 := by
  have : z / (Real.sqrt a : ℂ) - z / (Real.sqrt b : ℂ) =
      z * (((Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹ : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

theorem coef_norm_sq38 (z : ℂ) (a : ℝ) (ha : 0 ≤ a) :
    ‖z / (Real.sqrt a : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / a := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt ha]

end RatesLimit

section SobolevMain

variable {lower upper : ℝ} {c : ℕ → ℝ}

/-- Deterministic part of the Sobolev convergence `U_h → U` (D:prop:ALfree, first claim):
if `Σ ⟨k⟩^{2s}|g_k|²/W(4|k|) < ∞` then `U_h → U` in `H^s`. -/
theorem alFree_sobolev_tendsto38 (hA : AdmissibleWeight38 lower upper c) (s : ℝ) (g : ℤ → ℂ)
    (hg : Summable (fun k : ℤ => sobolevModeWeight s k * ‖g k‖ ^ 2 / alRateComp38 c k)) :
    Tendsto (fun N : ℕ => alUhRealization38 s c N g) atTop (𝓝 (alURealization38 s c g)) := by
  set w := sobolevModeWeight s with hwdef
  have hwpos : ∀ k, 0 < w k := (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight s n)).out
  have hWc := alRateComp_pos38 hA
  have hak := alRateComp_le_cont38 hA
  have hacpos : ∀ k, 0 < alRateCont38 c k := fun k => (hWc k).trans_le (hak k)
  have hsumU : Summable (fun k => w k * ‖alUCoef38 c g k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hwpos k).le (sq_nonneg _)) (fun k => ?_) hg
    unfold alUCoef38
    rw [coef_norm_sq38 _ _ (hacpos k).le, ← mul_div_assoc]
    exact div_le_div_of_nonneg_left (by have := hwpos k; positivity) (hWc k) (hak k)
  have hsumUh : ∀ N, Summable (fun k => w k * ‖alUhCoef38 c N g k‖ ^ 2) := by
    intro N
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N)
    intro k hk
    have : ¬ |k| ≤ (N : ℤ) := by
      intro h; apply hk; rw [Finset.mem_Icc]; exact abs_le.mp h
    simp [alUhCoef38, this]
  set F : ℕ → ℤ → ℝ := fun N k => w k * ‖alUhCoef38 c N g k - alUCoef38 c g k‖ ^ 2 with hF
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ k, ‖F N k‖ ≤ 3 * (w k * ‖g k‖ ^ 2 / alRateComp38 c k) := by
    filter_upwards [alRateFree_ge38 hA] with N hN k
    have hwk := hwpos k
    have hq : (Real.sqrt (alRateCont38 c k))⁻¹ ^ 2 ≤ (alRateComp38 c k)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (hacpos k).le]
      exact inv_anti₀ (hWc k) (hak k)
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hk : |k| ≤ (N : ℤ)
    · have hah := hN k hk
      have hahpos : 0 < alRateFree38 c N k := lt_of_lt_of_le (half_pos (hWc k)) hah
      have hp : (Real.sqrt (alRateFree38 c N k))⁻¹ ^ 2 ≤ 2 * (alRateComp38 c k)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hahpos.le]
        have : (alRateComp38 c k / 2)⁻¹ = 2 * (alRateComp38 c k)⁻¹ := by field_simp
        rw [← this]
        exact inv_anti₀ (by have := hWc k; positivity) hah
      simp only [hF, alUhCoef38, alUCoef38, hk, ↓reduceIte]
      rw [coef_diff_norm_sq38]
      have hp0 : 0 ≤ (Real.sqrt (alRateFree38 c N k))⁻¹ := by positivity
      have hq0 : 0 ≤ (Real.sqrt (alRateCont38 c k))⁻¹ := by positivity
      have hsq : ((Real.sqrt (alRateFree38 c N k))⁻¹ - (Real.sqrt (alRateCont38 c k))⁻¹) ^ 2 ≤
          3 * (alRateComp38 c k)⁻¹ := by nlinarith [mul_nonneg hp0 hq0]
      calc w k * (‖g k‖ ^ 2 * (((Real.sqrt (alRateFree38 c N k))⁻¹ -
            (Real.sqrt (alRateCont38 c k))⁻¹) ^ 2))
          ≤ w k * (‖g k‖ ^ 2 * (3 * (alRateComp38 c k)⁻¹)) := by gcongr
        _ = 3 * (w k * ‖g k‖ ^ 2 / alRateComp38 c k) := by field_simp
    · simp only [hF, alUhCoef38, alUCoef38, hk, ↓reduceIte, zero_sub, norm_neg]
      rw [coef_norm_sq38 _ _ (hacpos k).le]
      have : w k * (‖g k‖ ^ 2 / alRateCont38 c k) ≤ w k * ‖g k‖ ^ 2 / alRateComp38 c k := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_left (by positivity) (hWc k) (hak k)
      have h0 : 0 ≤ w k * ‖g k‖ ^ 2 / alRateComp38 c k := by have := hWc k; positivity
      linarith
  have hpt : ∀ k, Tendsto (fun N => F N k) atTop (𝓝 0) := by
    intro k
    have hlim : Tendsto (fun N : ℕ => (Real.sqrt (alRateFree38 c N k))⁻¹) atTop
        (𝓝 ((Real.sqrt (alRateCont38 c k))⁻¹)) :=
      ((alRateFree_tendsto38 hA k).sqrt).inv₀ (Real.sqrt_pos.2 (hacpos k)).ne'
    have h2 : Tendsto (fun N : ℕ => w k * (‖g k‖ ^ 2 * (((Real.sqrt (alRateFree38 c N k))⁻¹ -
        (Real.sqrt (alRateCont38 c k))⁻¹) ^ 2))) atTop (𝓝 (w k * (‖g k‖ ^ 2 * ((
          (Real.sqrt (alRateCont38 c k))⁻¹ - (Real.sqrt (alRateCont38 c k))⁻¹) ^ 2)))) :=
      (((hlim.sub_const _).pow 2).const_mul _).const_mul _
    rw [sub_self] at h2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop k.natAbs] with N hN
    have hk : |k| ≤ (N : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hN
    simp only [hF, alUhCoef38, alUCoef38, hk, ↓reduceIte]
    rw [coef_diff_norm_sq38]
  have hT : Tendsto (fun N => ∑' k, F N k) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := F) (g := fun _ => (0 : ℝ))
      (hg.mul_left 3) hpt hdom
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  have hd : ∀ N, dist (alUhRealization38 s c N g) (alURealization38 s c g) =
      Real.sqrt (∑' k, F N k) := by
    intro N
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _)]
    unfold alUhRealization38 alURealization38
    rw [seqRealization_dist_sq38 w _ _ (hsumUh N) hsumU]
  simp_rw [hd]
  simpa using hT.sqrt

end SobolevMain


section AlmostSure

variable {lower upper : ℝ} {c : ℕ → ℝ}

/-- The common probability space: independent standard complex Gaussians `g_k`, `E|g_k|² = 1`. -/
def alFreeLaw38 : Measure (ℤ → ℂ) := countableComplexGaussian (fun _ : ℤ => (1 : ℝ))

instance : IsProbabilityMeasure alFreeLaw38 := by unfold alFreeLaw38; infer_instance

theorem sobolevModeWeight_le_pow38 (s : ℝ) (r : ℕ) (hs : s ≤ r) (k : ℤ) :
    sobolevModeWeight s k ≤ (1 + (k : ℝ) ^ 2) ^ r := by
  unfold sobolevModeWeight japaneseBracket
  have h1 : (1 : ℝ) ≤ Real.sqrt (1 + (k : ℝ) ^ 2) :=
    Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (k : ℝ)])
  calc Real.rpow (Real.sqrt (1 + (k : ℝ) ^ 2)) (2 * s)
      ≤ Real.sqrt (1 + (k : ℝ) ^ 2) ^ (2 * (r : ℝ)) := by
        show Real.sqrt (1 + (k : ℝ) ^ 2) ^ (2 * s) ≤ _
        exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = (1 + (k : ℝ) ^ 2) ^ r := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        have : (1 / 2 : ℝ) * (2 * (r : ℝ)) = (r : ℝ) := by ring
        rw [this, Real.rpow_natCast]

theorem ae_summable_comp38 (hA : AdmissibleWeight38 lower upper c) (r : ℕ) :
    ∀ᵐ g ∂alFreeLaw38,
      Summable (fun k : ℤ => (1 + (k : ℝ) ^ 2) ^ r / alRateComp38 c k * ‖g k‖ ^ 2) := by
  apply ae_sequenceSummable (fun _ => (1 : ℝ)) _ (fun _ => one_pos)
  · intro k; have := alRateComp_pos38 hA k; positivity
  · simpa using alComp_summable38 hA r

/-- D:prop:ALfree, first claim: `U_h → U` almost surely in every fixed ordinary Sobolev space
`H^s`, `s ∈ ℝ`, on the coupling by independent standard complex Gaussians. -/
theorem alFree_sobolev_ae38 (hA : AdmissibleWeight38 lower upper c) :
    ∀ᵐ g ∂alFreeLaw38, ∀ s : ℝ,
      Tendsto (fun N : ℕ => alUhRealization38 s c N g) atTop (𝓝 (alURealization38 s c g)) := by
  have hall : ∀ᵐ g ∂alFreeLaw38, ∀ r : ℕ,
      Summable (fun k : ℤ => (1 + (k : ℝ) ^ 2) ^ r / alRateComp38 c k * ‖g k‖ ^ 2) :=
    ae_all_iff.2 (fun r => ae_summable_comp38 hA r)
  filter_upwards [hall] with g hg s
  apply alFree_sobolev_tendsto38 hA s g
  have hr := hg ⌈s⌉₊
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hr
  · have := alRateComp_pos38 hA k
    have : 0 < sobolevModeWeight s k := (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight s n)).out k
    positivity
  · have hW := alRateComp_pos38 hA k
    have := sobolevModeWeight_le_pow38 s ⌈s⌉₊ (Nat.le_ceil s) k
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this (sq_nonneg _)) hW.le

end AlmostSure


section EdgeRatio

variable {lower upper : ℝ} {c : ℕ → ℝ}

/-- Log-derivative of `t ↦ W(t²)` is `4 + O(t^{-1/2})` (from D:eq:Wderivatives), integrated by the
mean value theorem. -/
theorem log_weight_diff38 (hA : AdmissibleWeight38 lower upper c) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 4 ≤ a → a < b →
      |(Real.log (weight c (b ^ 2)) - Real.log (weight c (a ^ 2))) - 4 * (b - a)| ≤
        C * (b - a) * a ^ (-1 / 2 : ℝ) := by
  obtain ⟨hl, hb, hu⟩ := hA
  have hlu : lower ≤ upper := (hb 0).trans (hu 0)
  obtain ⟨C0, hC0, hder⟩ := weight_uniform_derivative_asymptotics lower upper hl hlu
  refine ⟨2 * C0, by positivity, fun a b ha hab => ?_⟩
  have hder' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.log (weight c (t ^ 2)))
      (deriv (weight c) (t ^ 2) / weight c (t ^ 2) * (2 * t)) t := by
    intro t
    have h1 := (weight_hasDerivAt lower upper c hl hb hu (t ^ 2)).comp t (hasDerivAt_pow 2 t)
    have h2 := h1.log (weight_pos lower upper c hl hb hu (t ^ 2)).ne'
    have e : (∑' j, weightTermDerivative c (t ^ 2) j) = deriv (weight c) (t ^ 2) :=
      (weight_hasDerivAt lower upper c hl hb hu (t ^ 2)).deriv.symm
    rw [e] at h2
    convert h2 using 1
    simp only [Function.comp_apply]
    simp
    ring
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => Real.log (weight c (t ^ 2)))
    (fun t => deriv (weight c) (t ^ 2) / weight c (t ^ 2) * (2 * t)) hab
    (fun t _ => (hder' t).continuousAt.continuousWithinAt) (fun t _ => hder' t)
  obtain ⟨hξa, hξb⟩ := hξ
  have hba : 0 < b - a := by linarith
  have hξ0 : 0 < ξ := by linarith
  have hr : 16 ≤ ξ ^ 2 := by nlinarith
  have e1 : (ξ ^ 2) ^ (-1 / 2 : ℝ) = ξ⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]
    have : ((2 : ℕ) : ℝ) * (-1 / 2) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
  have e2 : (ξ ^ 2) ^ (-3 / 4 : ℝ) = ξ ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]; norm_num
  have hd2 : |deriv (weight c) (ξ ^ 2) / weight c (ξ ^ 2) - 2 * ξ⁻¹| ≤ C0 * ξ ^ (-3 / 2 : ℝ) := by
    simpa [e1, e2] using (hder c hb hu (ξ ^ 2) hr).1
  -- φ'(ξ) - 4 = 2ξ (W'/W - 2/ξ)
  have hξ12 : ξ * ξ ^ (-3 / 2 : ℝ) = ξ ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' hξ0.le (by norm_num)]; norm_num
  have hmono : ξ ^ (-1 / 2 : ℝ) ≤ a ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hξa.le (by norm_num)
  have hdev : |deriv (weight c) (ξ ^ 2) / weight c (ξ ^ 2) * (2 * ξ) - 4| ≤ 2 * C0 * a ^ (-1 / 2 : ℝ) := by
    have : deriv (weight c) (ξ ^ 2) / weight c (ξ ^ 2) * (2 * ξ) - 4 =
        (2 * ξ) * (deriv (weight c) (ξ ^ 2) / weight c (ξ ^ 2) - 2 * ξ⁻¹) := by
      field_simp; ring
    rw [this, abs_mul, abs_of_pos (by positivity : 0 < 2 * ξ)]
    calc 2 * ξ * |_| ≤ 2 * ξ * (C0 * ξ ^ (-3 / 2 : ℝ)) := by gcongr
      _ = 2 * C0 * (ξ * ξ ^ (-3 / 2 : ℝ)) := by ring
      _ = 2 * C0 * ξ ^ (-1 / 2 : ℝ) := by rw [hξ12]
      _ ≤ 2 * C0 * a ^ (-1 / 2 : ℝ) := by gcongr
  have hslope : Real.log (weight c (b ^ 2)) - Real.log (weight c (a ^ 2)) =
      (deriv (weight c) (ξ ^ 2) / weight c (ξ ^ 2) * (2 * ξ)) * (b - a) := by
    rw [hξeq]; field_simp
  rw [hslope]
  have : (deriv (weight c) (ξ ^ 2) / weight c (ξ ^ 2) * (2 * ξ)) * (b - a) - 4 * (b - a) =
      (deriv (weight c) (ξ ^ 2) / weight c (ξ ^ 2) * (2 * ξ) - 4) * (b - a) := by ring
  rw [this, abs_mul, abs_of_pos hba]
  calc _ ≤ (2 * C0 * a ^ (-1 / 2 : ℝ)) * (b - a) := by gcongr
    _ = _ := by ring

end EdgeRatio


section EdgeMode

/-- Edge ratio `a_N / a_{h,N}` of the highest mode `k = N`. -/
def alEdgeRatio38 (c : ℕ → ℝ) (N : ℕ) : ℝ := alRateCont38 c (N : ℤ) / alRateFree38 c N (N : ℤ)

theorem alOmega_edge_eq38 (N : ℕ) :
    alOmegaFree38 N (N : ℤ) =
      2 * (2 * (N : ℝ) + 1) * Real.cos (Real.pi * alMeshStep38 N / 2) := by
  have hh := alMeshStep_pos38 N
  have hNh : Real.pi * (N : ℝ) * alMeshStep38 N =
      Real.pi / 2 - Real.pi * alMeshStep38 N / 2 := by
    unfold alMeshStep38; field_simp; ring
  unfold alOmegaFree38
  push_cast
  rw [hNh, Real.sin_pi_div_two_sub]
  unfold alMeshStep38; field_simp

theorem alOmega_edge_div_tendsto38 :
    Tendsto (fun N : ℕ => alOmegaFree38 N (N : ℤ) / (N : ℝ)) atTop (𝓝 4) := by
  have hc : Tendsto (fun N : ℕ => Real.cos (Real.pi * alMeshStep38 N / 2)) atTop (𝓝 1) := by
    have : Tendsto (fun N : ℕ => Real.pi * alMeshStep38 N / 2) atTop (𝓝 0) := by
      simpa using (alMeshStep_tendsto38.const_mul Real.pi).div_const 2
    have h := (Real.continuous_cos.tendsto 0).comp this
    rw [Real.cos_zero] at h
    exact h
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => 2 * (2 + (N : ℝ)⁻¹) * Real.cos (Real.pi * alMeshStep38 N / 2))
      atTop (𝓝 (2 * (2 + 0) * 1)) := (((hinv.const_add 2).const_mul 2)).mul hc
  have e : (2 * (2 + 0) * 1 : ℝ) = 4 := by norm_num
  rw [e] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [alOmega_edge_eq38]
  field_simp

end EdgeMode


section EdgeAsymptotic

variable {lower upper : ℝ} {c : ℕ → ℝ}

/-- D:eq:edgeratio: `log(a_N/a_{h,N}) = (4√(2π) − 8 + o(1))√N`, as a limit. -/
theorem alEdge_log_asymptotic38 (hA : AdmissibleWeight38 lower upper c) :
    Tendsto (fun N : ℕ => Real.log (alEdgeRatio38 c N) / Real.sqrt (N : ℝ)) atTop
      (𝓝 (4 * Real.sqrt (2 * Real.pi) - 8)) := by
  have hA' := hA
  obtain ⟨hl, hb, hu⟩ := hA'
  obtain ⟨C, hC, hlog⟩ := log_weight_diff38 hA
  set ω : ℕ → ℝ := fun N => alOmegaFree38 N (N : ℤ) with hωdef
  set a : ℕ → ℝ := fun N => Real.sqrt (ω N) with hadef
  set b : ℕ → ℝ := fun N => Real.sqrt (2 * Real.pi) * Real.sqrt (N : ℝ) with hbdef
  have hsq_top : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hωdiv : Tendsto (fun N : ℕ => ω N / (N : ℝ)) atTop (𝓝 4) := alOmega_edge_div_tendsto38
  have hωpos : ∀ᶠ N : ℕ in atTop, 0 < ω N := by
    filter_upwards [hωdiv.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 4)), eventually_ge_atTop 1]
      with N hN h1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast h1
    exact (div_pos_iff_of_pos_right hN0).1 hN
  have hadiv : Tendsto (fun N : ℕ => a N / Real.sqrt (N : ℝ)) atTop (𝓝 2) := by
    have h := hωdiv.sqrt
    have e : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e] at h
    refine h.congr' ?_
    filter_upwards with N
    rw [Real.sqrt_div' _ (Nat.cast_nonneg N)]
  have ha_top : Tendsto a atTop atTop := by
    have := Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 2) hadiv hsq_top
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
    field_simp
  have hbdiv : Tendsto (fun N : ℕ => (b N - a N) / Real.sqrt (N : ℝ)) atTop
      (𝓝 (Real.sqrt (2 * Real.pi) - 2)) := by
    refine (tendsto_const_nhds.sub hadiv).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
    simp only [hbdef]
    field_simp
  have h2lt : (2 : ℝ) < Real.sqrt (2 * Real.pi) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [Real.pi_gt_three]
  have hab : ∀ᶠ N : ℕ in atTop, a N < b N := by
    filter_upwards [hadiv.eventually (gt_mem_nhds h2lt), eventually_ge_atTop 1] with N hN h1
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h1)
    rw [div_lt_iff₀ hs] at hN
    simpa only [hbdef] using hN
  have ha4 : ∀ᶠ N : ℕ in atTop, 4 ≤ a N := ha_top.eventually_ge_atTop 4
  have hmesh : ∀ᶠ N : ℕ in atTop, alMeshStep38 N < lower / 2 :=
    alMeshStep_tendsto38.eventually (gt_mem_nhds (half_pos hl))
  -- the three pieces
  set δ : ℕ → ℝ := fun N => Real.log (1 - alMeshStep38 N / weight c (ω N)) with hδdef
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => alMeshStep38 N / weight c (ω N)) atTop (𝓝 0) := by
      refine squeeze_zero (fun N => ?_) (fun N => ?_) (alMeshStep_tendsto38.div_const lower |>.congr (fun N => rfl) |> fun h => by simpa using h)
      · exact div_nonneg (alMeshStep_pos38 N).le (weight_pos lower upper c hl hb hu _).le
      · exact div_le_div_of_nonneg_left (alMeshStep_pos38 N).le hl (weight_lower lower upper c hl hb hu _)
    have h1 : Tendsto (fun N : ℕ => 1 - alMeshStep38 N / weight c (ω N)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    simpa [hδdef, Function.comp_def] using this
  have hT3 : Tendsto (fun N : ℕ => -δ N / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    have := (hδ.neg).mul (tendsto_inv_atTop_zero.comp hsq_top)
    simpa [div_eq_mul_inv, Function.comp_def] using this
  have hT1 : Tendsto (fun N : ℕ => 4 * ((b N - a N) / Real.sqrt (N : ℝ))) atTop
      (𝓝 (4 * (Real.sqrt (2 * Real.pi) - 2))) := hbdiv.const_mul 4
  have hrpow : Tendsto (fun N : ℕ => a N ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp ha_top
    refine this.congr (fun N => ?_)
    simp only [Function.comp_apply]
    norm_num
  have hbound : Tendsto (fun N : ℕ => C * ((b N - a N) / Real.sqrt (N : ℝ)) * a N ^ (-1 / 2 : ℝ))
      atTop (𝓝 0) := by
    have := (hbdiv.const_mul C).mul hrpow
    simpa using this
  -- exact decomposition
  have hrel : ∀ᶠ N : ℕ in atTop,
      Real.log (alEdgeRatio38 c N) =
        (Real.log (weight c (b N ^ 2)) - Real.log (weight c (a N ^ 2))) - δ N := by
    filter_upwards [hωpos, hmesh, eventually_ge_atTop 1] with N hωN hhN h1
    have hWpos := weight_pos lower upper c hl hb hu (ω N)
    have hWge := weight_lower lower upper c hl hb hu (ω N)
    have hsa : a N ^ 2 = ω N := Real.sq_sqrt hωN.le
    have hsb : b N ^ 2 = 2 * Real.pi * (N : ℝ) := by
      simp only [hbdef]
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg N)]
    have hfree : alRateFree38 c N (N : ℤ) = weight c (ω N) * (1 - alMeshStep38 N / weight c (ω N)) := by
      show weight c (ω N) - alMeshStep38 N = _
      field_simp
    have hq : 0 < 1 - alMeshStep38 N / weight c (ω N) := by
      have : alMeshStep38 N / weight c (ω N) < 1 := by
        rw [div_lt_one hWpos]; linarith
      linarith
    have hcont : alRateCont38 c (N : ℤ) = weight c (b N ^ 2) := by
      rw [hsb]; unfold alRateCont38; push_cast; rfl
    unfold alEdgeRatio38
    rw [hcont, hfree, hsa, Real.log_div (weight_pos lower upper c hl hb hu _).ne'
      (mul_pos hWpos hq).ne', Real.log_mul hWpos.ne' hq.ne']
    simp only [hδdef]
    ring
  have hfinal : Tendsto (fun N : ℕ => 4 * ((b N - a N) / Real.sqrt (N : ℝ)) +
      ((Real.log (weight c (b N ^ 2)) - Real.log (weight c (a N ^ 2))) - 4 * (b N - a N)) /
        Real.sqrt (N : ℝ) + -δ N / Real.sqrt (N : ℝ)) atTop
      (𝓝 (4 * (Real.sqrt (2 * Real.pi) - 2) + 0 + 0)) := by
    have hT2 : Tendsto (fun N : ℕ =>
        ((Real.log (weight c (b N ^ 2)) - Real.log (weight c (a N ^ 2))) - 4 * (b N - a N)) /
          Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hbound
      filter_upwards [hab, ha4, eventually_ge_atTop 1] with N hN h4 h1
      have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h1)
      rw [norm_div, Real.norm_of_nonneg hs.le, div_le_iff₀ hs]
      have := hlog (a N) (b N) h4 hN
      have e : C * ((b N - a N) / Real.sqrt (N : ℝ)) * a N ^ (-1 / 2 : ℝ) * Real.sqrt (N : ℝ) =
          C * (b N - a N) * a N ^ (-1 / 2 : ℝ) := by field_simp
      rw [e]
      exact this
    exact (hT1.add hT2).add hT3
  have e0 : 4 * (Real.sqrt (2 * Real.pi) - 2) + 0 + 0 = 4 * Real.sqrt (2 * Real.pi) - 8 := by ring
  rw [e0] at hfinal
  refine hfinal.congr' ?_
  filter_upwards [hrel, eventually_ge_atTop 1] with N hN h1
  rw [hN]
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h1)
  field_simp
  ring

end EdgeAsymptotic


section Divergence

variable {lower upper : ℝ} {c : ℕ → ℝ}

/-- Squared `E_s` norm of the Fourier sequence of `U_h` (finite support, so no totalization):
`Σ_{|k|≤N} a_k ⟨k⟩^{-2s} |Û_h(k)|²`. -/
def alESqNorm38 (c : ℕ → ℝ) (s : ℝ) (N : ℕ) (g : ℤ → ℂ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    alRateCont38 c k * sobolevModeWeight (-s) k * ‖alUhCoef38 c N g k‖ ^ 2

/-- `‖Û_h‖_{E_s}`. -/
def alENorm38 (c : ℕ → ℝ) (s : ℝ) (N : ℕ) (g : ℤ → ℂ) : ℝ :=
  Real.sqrt (alESqNorm38 c s N g)

theorem tendsto_log_one_add_sq_div38 :
    Tendsto (fun N : ℕ => Real.log (1 + (N : ℝ) ^ 2) / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  have hsq_top : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => Real.log (Real.sqrt (N : ℝ)) / Real.sqrt (N : ℝ)) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hsq_top
  have h2 : Tendsto (fun N : ℕ => Real.log 2 / Real.sqrt (N : ℝ) +
      4 * (Real.log (Real.sqrt (N : ℝ)) / Real.sqrt (N : ℝ))) atTop (𝓝 0) := by
    have := ((tendsto_inv_atTop_zero.comp hsq_top).const_mul (Real.log 2)).add (h1.const_mul 4)
    simpa [div_eq_mul_inv, Function.comp_def] using this
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop 1] with N hN
    apply div_nonneg
    · apply Real.log_nonneg; nlinarith [sq_nonneg (N : ℝ)]
    · exact Real.sqrt_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by linarith)
    rw [div_le_iff₀ hs]
    have hlog : Real.log (1 + (N : ℝ) ^ 2) ≤ Real.log 2 + 4 * Real.log (Real.sqrt (N : ℝ)) := by
      have h4 : Real.log (Real.sqrt (N : ℝ)) = Real.log N / 2 := Real.log_sqrt (Nat.cast_nonneg N)
      calc Real.log (1 + (N : ℝ) ^ 2) ≤ Real.log (2 * (N : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) (by nlinarith)
        _ = Real.log 2 + 2 * Real.log N := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
        _ = _ := by rw [h4]; ring
    calc Real.log (1 + (N : ℝ) ^ 2) ≤ Real.log 2 + 4 * Real.log (Real.sqrt (N : ℝ)) := hlog
      _ = (Real.log 2 / Real.sqrt (N : ℝ) + 4 * (Real.log (Real.sqrt (N : ℝ)) / Real.sqrt (N : ℝ))) *
            Real.sqrt (N : ℝ) := by field_simp

/-- The coefficient of `|g_N|²` in `‖Û_h‖²_{E_s}`: `a_N ⟨N⟩^{-2s}/a_{h,N}`. -/
theorem alEdgeCoeff_tendsto_top38 (hA : AdmissibleWeight38 lower upper c) (s : ℝ) :
    Tendsto (fun N : ℕ => alEdgeRatio38 c N * sobolevModeWeight (-s) (N : ℤ)) atTop atTop := by
  obtain ⟨hl, hb, hu⟩ := hA
  have hA' : AdmissibleWeight38 lower upper c := ⟨hl, hb, hu⟩
  have hsq_top : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  set L : ℝ := 4 * Real.sqrt (2 * Real.pi) - 8 with hL
  have hLpos : 0 < L := by
    have : (2 : ℝ) < Real.sqrt (2 * Real.pi) := by
      apply Real.lt_sqrt_of_sq_lt; nlinarith [Real.pi_gt_three]
    rw [hL]; linarith
  have hlogw : ∀ N : ℕ, Real.log (sobolevModeWeight (-s) (N : ℤ)) = -s * Real.log (1 + (N : ℝ) ^ 2) := by
    intro N
    unfold sobolevModeWeight japaneseBracket
    show Real.log (Real.sqrt (1 + (((N : ℤ) : ℝ)) ^ 2) ^ (2 * -s)) = _
    rw [Real.log_rpow (Real.sqrt_pos.2 (by positivity)), Real.log_sqrt (by positivity)]
    push_cast; ring
  have hq : Tendsto (fun N : ℕ => Real.log (alEdgeRatio38 c N * sobolevModeWeight (-s) (N : ℤ)) /
      Real.sqrt (N : ℝ)) atTop (𝓝 L) := by
    have h1 := (alEdge_log_asymptotic38 hA').add
      ((tendsto_log_one_add_sq_div38).const_mul (-s))
    rw [mul_zero, add_zero] at h1
    refine h1.congr' ?_
    have hpos : ∀ᶠ N : ℕ in atTop, 0 < alEdgeRatio38 c N := by
      filter_upwards [alRateFree_ge38 hA', eventually_ge_atTop 1] with N hN h1
      have hk : |(N : ℤ)| ≤ (N : ℤ) := by simp
      have h2 := hN (N : ℤ) hk
      have h3 := alRateComp_pos38 hA' (N : ℤ)
      have h4 := alRateComp_le_cont38 hA' (N : ℤ)
      unfold alEdgeRatio38
      apply div_pos (h3.trans_le h4)
      linarith
    filter_upwards [hpos] with N hN
    have hwpos : 0 < sobolevModeWeight (-s) (N : ℤ) :=
      (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight (-s) n)).out _
    rw [Real.log_mul hN.ne' hwpos.ne', hlogw]
    ring
  have hlog_top : Tendsto (fun N : ℕ =>
      Real.log (alEdgeRatio38 c N * sobolevModeWeight (-s) (N : ℤ))) atTop atTop := by
    have hge : ∀ᶠ N : ℕ in atTop, L / 2 * Real.sqrt (N : ℝ) ≤
        Real.log (alEdgeRatio38 c N * sobolevModeWeight (-s) (N : ℤ)) := by
      filter_upwards [hq.eventually (lt_mem_nhds (by linarith : L / 2 < L)), eventually_ge_atTop 1]
        with N hN h1
      have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h1)
      rw [lt_div_iff₀ hs] at hN
      exact hN.le
    exact tendsto_atTop_mono' _ hge (hsq_top.const_mul_atTop (by linarith))
  have hpos2 : ∀ᶠ N : ℕ in atTop, 0 < alEdgeRatio38 c N * sobolevModeWeight (-s) (N : ℤ) := by
    filter_upwards [alRateFree_ge38 hA', eventually_ge_atTop 1] with N hN h1
    have hk : |(N : ℤ)| ≤ (N : ℤ) := by simp
    have h2 := hN (N : ℤ) hk
    have h3 := alRateComp_pos38 hA' (N : ℤ)
    have h4 := alRateComp_le_cont38 hA' (N : ℤ)
    have hwpos : 0 < sobolevModeWeight (-s) (N : ℤ) :=
      (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight (-s) n)).out _
    unfold alEdgeRatio38
    exact mul_pos (div_pos (h3.trans_le h4) (by linarith)) hwpos
  refine (Real.tendsto_exp_atTop.comp hlog_top).congr' ?_
  filter_upwards [hpos2] with N hN
  simp only [Function.comp_apply]
  exact Real.exp_log hN

end Divergence


section Probability

variable {lower upper : ℝ} {c : ℕ → ℝ}

/-- `P(|g|² ≤ t) ≤ t` for a standard complex Gaussian (density `≤ 1/π`). -/
theorem complexGaussian_one_ball_le38 (t : ℝ) (ht : 0 ≤ t) :
    complexGaussian 1 {z : ℂ | ‖z‖ ^ 2 ≤ t} ≤ ENNReal.ofReal t := by
  have hS : {z : ℂ | ‖z‖ ^ 2 ≤ t} = Metric.closedBall (0 : ℂ) (Real.sqrt t) := by
    ext z
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h; exact Real.le_sqrt_of_sq_le h
    · intro h
      calc ‖z‖ ^ 2 ≤ (Real.sqrt t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = t := Real.sq_sqrt ht
  rw [hS, complexGaussian_density 1 one_pos, withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  calc ∫⁻ z in Metric.closedBall (0 : ℂ) (Real.sqrt t),
        ENNReal.ofReal ((1 / Real.pi) * Real.exp (-1 * ‖z‖ ^ 2))
      ≤ ∫⁻ z in Metric.closedBall (0 : ℂ) (Real.sqrt t), ENNReal.ofReal (1 / Real.pi) := by
        apply lintegral_mono
        intro z
        apply ENNReal.ofReal_le_ofReal
        have : Real.exp (-1 * ‖z‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖z‖])
        have hp : 0 < 1 / Real.pi := by positivity
        nlinarith
    _ = ENNReal.ofReal (1 / Real.pi) * volume (Metric.closedBall (0 : ℂ) (Real.sqrt t)) := by
        rw [setLIntegral_const]
    _ = ENNReal.ofReal t := by
        rw [Complex.volume_closedBall]
        have hpi : ((NNReal.pi : NNReal) : ENNReal) = ENNReal.ofReal Real.pi := by
          rw [ENNReal.ofReal, ← NNReal.coe_real_pi, Real.toNNReal_coe]
        rw [hpi, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), Real.sq_sqrt ht]
        congr 1
        field_simp

/-- Law of one coordinate. -/
theorem alFreeLaw_coord_ball38 (n : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    alFreeLaw38 {g : ℤ → ℂ | ‖g n‖ ^ 2 ≤ t} ≤ ENNReal.ofReal t := by
  have hm : MeasurableSet {z : ℂ | ‖z‖ ^ 2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have h := countableComplexGaussian_map_eval (fun _ : ℤ => (1 : ℝ)) n
  have h2 : alFreeLaw38 {g : ℤ → ℂ | ‖g n‖ ^ 2 ≤ t} =
      complexGaussian 1 {z : ℂ | ‖z‖ ^ 2 ≤ t} := by
    rw [← h, Measure.map_apply (measurable_pi_apply n) hm]
    rfl
  rw [h2]
  exact complexGaussian_one_ball_le38 t ht

/-- D:prop:ALfree, second claim (D:eq:ALnotcritical): for every `s ∈ ℝ`,
`‖Û_h‖_{E_s} → ∞` in probability: for every `M`, `P(‖Û_h‖_{E_s} ≤ M) → 0`. -/
theorem alFree_ENorm_diverges38 (hA : AdmissibleWeight38 lower upper c) (s M : ℝ) :
    Tendsto (fun N : ℕ => alFreeLaw38 {g : ℤ → ℂ | alENorm38 c s N g ≤ M}) atTop (𝓝 0) := by
  have hr := alEdgeCoeff_tendsto_top38 hA s
  have hbound : ∀ᶠ N : ℕ in atTop, alFreeLaw38 {g : ℤ → ℂ | alENorm38 c s N g ≤ M} ≤
      ENNReal.ofReal (M ^ 2 / (alEdgeRatio38 c N * sobolevModeWeight (-s) (N : ℤ))) := by
    filter_upwards [alRateFree_ge38 hA, hr.eventually_gt_atTop 0] with N hN hrN
    have hk : |(N : ℤ)| ≤ (N : ℤ) := by simp
    have h2 := hN (N : ℤ) hk
    have h3 := alRateComp_pos38 hA (N : ℤ)
    have hfpos : 0 < alRateFree38 c N (N : ℤ) := by linarith
    have hwpos : ∀ k : ℤ, 0 < sobolevModeWeight (-s) k := fun k =>
      (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight (-s) n)).out k
    have hcpos : ∀ k : ℤ, 0 < alRateCont38 c k := fun k =>
      (alRateComp_pos38 hA k).trans_le (alRateComp_le_cont38 hA k)
    set r := alEdgeRatio38 c N * sobolevModeWeight (-s) (N : ℤ) with hrdef
    have hsub : {g : ℤ → ℂ | alENorm38 c s N g ≤ M} ⊆ {g : ℤ → ℂ | ‖g (N : ℤ)‖ ^ 2 ≤ M ^ 2 / r} := by
      intro g hg
      simp only [Set.mem_ofPred_eq] at hg ⊢
      have hnn : 0 ≤ alESqNorm38 c s N g :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg (hcpos k).le (hwpos k).le) (sq_nonneg _))
      have hsq : alESqNorm38 c s N g ≤ M ^ 2 := by
        have h0 : 0 ≤ alENorm38 c s N g := Real.sqrt_nonneg _
        have : alESqNorm38 c s N g = (alENorm38 c s N g) ^ 2 := (Real.sq_sqrt hnn).symm
        rw [this]
        exact pow_le_pow_left₀ h0 hg 2
      have hmem : (N : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        rw [Finset.mem_Icc]; constructor <;> omega
      have hle : alRateCont38 c (N : ℤ) * sobolevModeWeight (-s) (N : ℤ) *
          ‖alUhCoef38 c N g (N : ℤ)‖ ^ 2 ≤ alESqNorm38 c s N g :=
        Finset.single_le_sum (f := fun k : ℤ => alRateCont38 c k * sobolevModeWeight (-s) k *
          ‖alUhCoef38 c N g k‖ ^ 2)
          (fun k _ => mul_nonneg (mul_nonneg (hcpos k).le (hwpos k).le) (sq_nonneg _)) hmem
      have hterm : alRateCont38 c (N : ℤ) * sobolevModeWeight (-s) (N : ℤ) *
          ‖alUhCoef38 c N g (N : ℤ)‖ ^ 2 = r * ‖g (N : ℤ)‖ ^ 2 := by
        simp only [alUhCoef38, hk, ↓reduceIte]
        rw [coef_norm_sq38 _ _ hfpos.le, hrdef]
        unfold alEdgeRatio38
        field_simp
      rw [hterm] at hle
      rw [le_div_iff₀ hrN]
      nlinarith
    calc alFreeLaw38 {g : ℤ → ℂ | alENorm38 c s N g ≤ M}
        ≤ alFreeLaw38 {g : ℤ → ℂ | ‖g (N : ℤ)‖ ^ 2 ≤ M ^ 2 / r} := measure_mono hsub
      _ ≤ _ := alFreeLaw_coord_ball38 _ _ (by positivity)
  have hup : Tendsto (fun N : ℕ =>
      ENNReal.ofReal (M ^ 2 / (alEdgeRatio38 c N * sobolevModeWeight (-s) (N : ℤ)))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop hr (a := M ^ 2))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun N => zero_le) hbound

end Probability


/-- D:prop:ALfree: (i) a.s. convergence `U_h → U` in every `H^s`; (ii) the edge-ratio asymptotic
(D:eq:edgeratio) with positive coefficient `4√(2π) − 8`; (iii) `‖Û_h‖_{E_s} → ∞` in probability,
for every `s ∈ ℝ`. -/
theorem alFree_prop38 {lower upper : ℝ} {c : ℕ → ℝ} (hA : AdmissibleWeight38 lower upper c) :
    (∀ᵐ g ∂alFreeLaw38, ∀ s : ℝ,
      Tendsto (fun N : ℕ => alUhRealization38 s c N g) atTop (𝓝 (alURealization38 s c g))) ∧
    (Tendsto (fun N : ℕ => Real.log (alEdgeRatio38 c N) / Real.sqrt (N : ℝ)) atTop
      (𝓝 (4 * Real.sqrt (2 * Real.pi) - 8)) ∧ 0 < 4 * Real.sqrt (2 * Real.pi) - 8) ∧
    (∀ s M : ℝ, Tendsto (fun N : ℕ => alFreeLaw38 {g : ℤ → ℂ | alENorm38 c s N g ≤ M})
      atTop (𝓝 0)) := by
  refine ⟨alFree_sobolev_ae38 hA, ⟨alEdge_log_asymptotic38 hA, ?_⟩,
    fun s M => alFree_ENorm_diverges38 hA s M⟩
  have : (2 : ℝ) < Real.sqrt (2 * Real.pi) := by
    apply Real.lt_sqrt_of_sq_lt; nlinarith [Real.pi_gt_three]
  linarith

end NlsGge.AblowitzLadik
