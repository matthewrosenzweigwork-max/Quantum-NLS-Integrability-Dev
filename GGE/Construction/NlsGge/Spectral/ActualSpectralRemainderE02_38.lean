import NlsGge.Spectral.ActualConvexMomentInfiniteE02_38
import NlsGge.Spectral.ActualGapLocalizationFinalE02_38
import NlsGge.Spectral.TraceFormulaLowerOrder38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # F04 (B:lem:spectral) Φ-free parts: absolute convergence and nonnegativity of `R_m` (campaign 38)

For convex C² `W` with `|W'(y)| ≤ A(1 + |y|^{2k+1})` (`k ≥ 1`) and `u ∈ H^k`, the gap remainder
`R(u) = Σ_n (2/π)∫_{g_n}[W(2λ) - W(2πn)] v` converges absolutely and is `≥ 0`. For `W = W_m`, `k = m - 1`, this is
v2 B:lem:spectral minus continuity (F04.01–.03 and F04.05), with `|Φ_n|²` read as `I_n` (user decision D2).
Route (ii) of `F04_ROUTE.md`. -/

/-! ## Localization for a bare H¹ field -/

/-- The Schur H¹ carrier of the Fourier coefficients of `u` is `u`. -/
theorem exists_carrier_eq_E02_38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∃ w : WeightedHilbert (sobolevModeWeight (1:ℝ)), physicalH1ComplexCarrierToL2Actual22 w = u := by
  have hmem : Memℓp (weightedCoordinates (sobolevModeWeight 1) (fun n => physicalFourier u n)) 2 := by
    rw [weightedCoordinates_mem_l2_iff (sobolevModeWeight 1)
      (fun n => (Real.rpow_pos_of_pos (japaneseBracket_pos n) (2 * 1)).le)]
    exact hu
  refine ⟨⟨fun n => physicalFourier u n, hmem⟩, ?_⟩
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, physicalH1ComplexCarrierToL2Actual22_fourier]

/-- E03 for a bare H¹ field: `|λ - πn| ≤ K/⟨n⟩` on `\overline{g_n}`. -/
theorem gapLocalization_of_sobolev_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℤ,
      ∀ l ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        |l - (n:ℝ)*Real.pi| ≤ K / japaneseBracket n := by
  obtain ⟨w, hw⟩ := exists_carrier_eq_E02_38 u hu
  obtain ⟨K, hK, hloc⟩ := actualGapLocalization_E02_38 (max 1 ‖w‖) (le_max_left _ _)
  refine ⟨K, hK, fun n l hl => ?_⟩
  have := hloc w (le_max_right _ _) n l
  rw [hw] at this
  exact this hl

/-- Where `v ≠ 0`, `x` lies in a labelled gap `m` with `p(x) = mπ` and `|x - mπ| ≤ K/⟨m⟩`. -/
theorem gap_point_of_ne_zero_E02_38 (u : PhysicalL2) (K : ℝ)
    (hloc : ∀ n : ℤ, ∀ l ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        |l - (n:ℝ)*Real.pi| ≤ K / japaneseBracket n)
    (x : ℝ) (hx : actualGapHeightE02_38 u x ≠ 0) :
    ∃ m : ℤ, actualQuasimomentumRealPartE02_38 u x = m * Real.pi ∧
      |x - m * Real.pi| ≤ K / japaneseBracket m := by
  obtain ⟨m, hm⟩ := realPart_int_mul_pi_of_gapHeight_ne_zero_E02_38 u x hx
  refine ⟨m, hm, hloc m x ?_⟩
  have : x ∈ actualGapLevelSetE02_38 u m := hm
  rwa [(actualGapLevelSet_eq_Icc_E02_38 u m).2] at this

/-! ## Elementary inequalities -/

theorem one_add_pow_le_E02_38 (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (1 + a)^n ≤ 2^n * (1 + a^n) := by
  have h1 : 1 + a ≤ 2 * max 1 a := by
    have := le_max_left 1 a; have := le_max_right 1 a; linarith
  have h2 : (1 + a)^n ≤ (2 * max 1 a)^n := pow_le_pow_left₀ (by linarith) h1 n
  have h3 : (max 1 a)^n ≤ 1 + a^n := by
    rcases le_total 1 a with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ha n]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg ha n]
  rw [mul_pow] at h2
  calc (1 + a)^n ≤ 2^n * (max 1 a)^n := h2
    _ ≤ 2^n * (1 + a^n) := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- Convexity gives `|W b - W a| ≤ |b - a| · max(|W' a|, |W' b|)`. -/
theorem convex_diff_le_E02_38 (W : ℝ → ℝ) (hWd : Differentiable ℝ W) (hconv : ConvexOn ℝ Set.univ W)
    (a b : ℝ) : |W b - W a| ≤ |b - a| * max |deriv W a| |deriv W b| := by
  have htan : ∀ x y : ℝ, W x + deriv W x * (y - x) ≤ W y := by
    intro x y
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · have h' := hconv.deriv_le_slope (Set.mem_univ x) (Set.mem_univ y) hxy (hWd x)
      rw [slope_def_field, le_div_iff₀ (by linarith)] at h'; linarith
    · rw [hxy]; simp
    · have h' := hconv.slope_le_deriv (Set.mem_univ y) (Set.mem_univ x) hxy (hWd x)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at h'; linarith
  have h1 := htan a b
  have h2 := htan b a
  have hm1 := le_max_left |deriv W a| |deriv W b|
  have hm2 := le_max_right |deriv W a| |deriv W b|
  rw [abs_le]
  constructor
  · -- W b - W a ≥ deriv W a * (b - a) ≥ -|b-a| |W' a|
    have : -( |b - a| * |deriv W a|) ≤ deriv W a * (b - a) := by
      have := neg_abs_le (deriv W a * (b - a)); rw [abs_mul] at this; linarith
    have : |b - a| * |deriv W a| ≤ |b - a| * max |deriv W a| |deriv W b| :=
      mul_le_mul_of_nonneg_left hm1 (abs_nonneg _)
    linarith
  · have : deriv W b * (a - b) ≥ -( |b - a| * |deriv W b|) := by
      have := neg_abs_le (deriv W b * (a - b))
      rw [abs_mul, abs_sub_comm a b] at this; linarith
    have : |b - a| * |deriv W b| ≤ |b - a| * max |deriv W a| |deriv W b| :=
      mul_le_mul_of_nonneg_left hm2 (abs_nonneg _)
    linarith

/-! ## The pointwise weight bound (F04.01–.03) -/

/-- On the support of `v`, `|W(2x) - W(2p(x))| ≤ C (1 + (2x)^{2k})`. -/
theorem weight_diff_bound_E02_38 (W : ℝ → ℝ) (hWd : Differentiable ℝ W)
    (hconv : ConvexOn ℝ Set.univ W) (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hW' : ∀ y, |deriv W y| ≤ A * (1 + |y|^(2*k+1))) (u : PhysicalL2) (K : ℝ) (hK : 0 < K)
    (hloc : ∀ n : ℤ, ∀ l ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        |l - (n:ℝ)*Real.pi| ≤ K / japaneseBracket n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, actualGapHeightE02_38 u x ≠ 0 →
      |W (2*x) - W (2 * actualQuasimomentumRealPartE02_38 u x)| ≤ C * (1 + (2*x)^(2*k)) := by
  have hpi := Real.pi_gt_three
  set D : ℝ := 2 * Real.pi + 4 * K
  refine ⟨4 * K * A * (1 + D^(2*k+1)) * ((1 + K)^(2*k) * 2^(2*k)), by positivity, fun x hx => ?_⟩
  obtain ⟨m, hpm, hxm⟩ := gap_point_of_ne_zero_E02_38 u K hloc x hx
  set p := actualQuasimomentumRealPartE02_38 u x
  set s : ℝ := 1 + |(m:ℝ)|
  have hs1 : 1 ≤ s := by simp only [s]; linarith [abs_nonneg (m:ℝ)]
  have hjb : s / 2 ≤ japaneseBracket m := by
    unfold japaneseBracket
    apply Real.le_sqrt_of_sq_le
    have : s^2 ≤ 2 * (1 + (m:ℝ)^2) := by
      simp only [s]; nlinarith [sq_abs (m:ℝ), abs_nonneg (m:ℝ), sq_nonneg (|(m:ℝ)| - 1)]
    nlinarith
  have hjpos : 0 < japaneseBracket m := japaneseBracket_pos m
  have hxp : |x - p| ≤ 2 * K / s := by
    rw [hpm]
    calc |x - m * Real.pi| ≤ K / japaneseBracket m := hxm
      _ ≤ K / (s/2) := div_le_div_of_nonneg_left hK.le (by positivity) hjb
      _ = 2 * K / s := by field_simp
  have hp : |p| = Real.pi * |(m:ℝ)| := by rw [hpm, abs_mul, abs_of_pos Real.pi_pos, mul_comm]
  have hpb : |2 * p| ≤ 2 * Real.pi * s := by
    rw [abs_mul, abs_two, hp]; simp only [s]; nlinarith [abs_nonneg (m:ℝ)]
  have hxb : |2 * x| ≤ D * s := by
    have : |x| ≤ |p| + |x - p| := by
      have := abs_sub_abs_le_abs_sub x p; linarith
    have h2 : |x - p| ≤ 2 * K := le_trans hxp (by rw [div_le_iff₀ (by linarith)]; nlinarith)
    rw [abs_mul, abs_two]
    simp only [D]
    have : 2 * Real.pi * |(m:ℝ)| ≤ 2 * Real.pi * s := by simp only [s]; nlinarith
    nlinarith [abs_nonneg (m:ℝ)]
  -- derivative bound on both points
  have hDs : ∀ y, |y| ≤ D * s → |deriv W y| ≤ A * (1 + (D * s)^(2*k+1)) := by
    intro y hy
    refine (hW' y).trans (mul_le_mul_of_nonneg_left ?_ hA)
    have := pow_le_pow_left₀ (abs_nonneg y) hy (2*k+1)
    linarith
  have hD2p : |2 * p| ≤ D * s := by
    refine hpb.trans ?_
    simp only [D]; nlinarith
  have hmax : max |deriv W (2*p)| |deriv W (2*x)| ≤ A * (1 + (D * s)^(2*k+1)) :=
    max_le (hDs _ hD2p) (hDs _ hxb)
  have hdiff := convex_diff_le_E02_38 W hWd hconv (2*p) (2*x)
  have h2xp : |2*x - 2*p| ≤ 4 * K / s := by
    rw [show 2*x - 2*p = 2 * (x - p) by ring, abs_mul, abs_two]
    calc 2 * |x - p| ≤ 2 * (2 * K / s) := by linarith
      _ = 4 * K / s := by ring
  have step1 : |W (2*x) - W (2*p)| ≤ 4 * K / s * (A * (1 + (D * s)^(2*k+1))) :=
    hdiff.trans (mul_le_mul h2xp hmax (by positivity) (by positivity))
  -- `(1 + (Ds)^{2k+1}) / s ≤ (1 + D^{2k+1}) s^{2k}`
  have hD0 : 0 ≤ D := by positivity
  have step2 : (1 + (D * s)^(2*k+1)) / s ≤ (1 + D^(2*k+1)) * s^(2*k) := by
    rw [div_le_iff₀ (by linarith), mul_pow, pow_succ s (2*k)]
    have : 1 ≤ s^(2*k) * s := by
      have := one_le_pow₀ hs1 (n := 2*k); nlinarith
    nlinarith [pow_nonneg hD0 (2*k+1), pow_nonneg (by linarith : (0:ℝ) ≤ s) (2*k)]
  have hsx : s ≤ (1 + K) * (1 + |x|) := by
    have hm : |(m:ℝ)| * Real.pi ≤ |x| + K := by
      have h1 : |(m:ℝ) * Real.pi| ≤ |x| + |x - m * Real.pi| := by
        have := abs_sub_abs_le_abs_sub (m * Real.pi) x
        rw [abs_sub_comm] at this; linarith [abs_sub_comm x (m * Real.pi)]
      have h2 : |x - m * Real.pi| ≤ K := le_trans hxm (by
        rw [div_le_iff₀ hjpos]; nlinarith [japaneseBracket_one_le m])
      rw [abs_mul, abs_of_pos Real.pi_pos] at h1; linarith
    have hm' : |(m:ℝ)| ≤ |x| + K := by nlinarith [abs_nonneg (m:ℝ)]
    simp only [s]; nlinarith [abs_nonneg x]
  have step3 : s^(2*k) ≤ (1 + K)^(2*k) * 2^(2*k) * (1 + (2*x)^(2*k)) := by
    have h1 : s^(2*k) ≤ ((1 + K) * (1 + |x|))^(2*k) := pow_le_pow_left₀ (by linarith) hsx _
    have h2 := one_add_pow_le_E02_38 |x| (abs_nonneg x) (2*k)
    have h3 : |x|^(2*k) ≤ (2*x)^(2*k) := by
      calc |x|^(2*k) ≤ |2*x|^(2*k) := pow_le_pow_left₀ (abs_nonneg _)
            (by rw [abs_mul, abs_two]; linarith [abs_nonneg x]) _
        _ = (2*x)^(2*k) := (even_two_mul k).pow_abs (2*x)
    rw [mul_pow] at h1
    calc s^(2*k) ≤ (1 + K)^(2*k) * (1 + |x|)^(2*k) := h1
      _ ≤ (1 + K)^(2*k) * (2^(2*k) * (1 + |x|^(2*k))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (1 + K)^(2*k) * (2^(2*k) * (1 + (2*x)^(2*k))) := by gcongr
      _ = _ := by ring
  have e : 4 * K / s * (A * (1 + (D * s)^(2*k+1))) =
      4 * K * A * ((1 + (D * s)^(2*k+1)) / s) := by field_simp
  rw [e] at step1
  calc |W (2*x) - W (2*p)| ≤ 4 * K * A * ((1 + (D * s)^(2*k+1)) / s) := step1
    _ ≤ 4 * K * A * ((1 + D^(2*k+1)) * s^(2*k)) :=
        mul_le_mul_of_nonneg_left step2 (by positivity)
    _ ≤ 4 * K * A * ((1 + D^(2*k+1)) * ((1 + K)^(2*k) * 2^(2*k) * (1 + (2*x)^(2*k)))) := by
        gcongr
    _ = _ := by ring

/-- On the support of `v`, `|2p(x)| ≤ 2|x| + 4K`. -/
theorem abs_two_p_le_E02_38 (u : PhysicalL2) (K : ℝ) (hK : 0 < K)
    (hloc : ∀ n : ℤ, ∀ l ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        |l - (n:ℝ)*Real.pi| ≤ K / japaneseBracket n)
    (x : ℝ) (hx : actualGapHeightE02_38 u x ≠ 0) :
    |2 * actualQuasimomentumRealPartE02_38 u x| ≤ 2 * |x| + 4 * K := by
  obtain ⟨m, hpm, hxm⟩ := gap_point_of_ne_zero_E02_38 u K hloc x hx
  have h2 : |x - m * Real.pi| ≤ K := le_trans hxm (by
    rw [div_le_iff₀ (japaneseBracket_pos m)]; nlinarith [japaneseBracket_one_le m])
  rw [hpm, abs_mul, abs_two]
  have := abs_sub_abs_le_abs_sub (m * Real.pi) x
  rw [abs_sub_comm (m * Real.pi) x] at this
  linarith

/-- Band cuts exist arbitrarily far out (with `d = 1`), by localization. -/
theorem exists_bandCut_E02_38 (u : PhysicalL2) (K : ℝ) (hK : 0 < K)
    (hloc : ∀ n : ℤ, ∀ l ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        |l - (n:ℝ)*Real.pi| ≤ K / japaneseBracket n) (L₀ : ℝ) :
    ∃ L : ℝ, L₀ ≤ L ∧ IsBandCutE02_38 u L 1 := by
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  obtain ⟨N, hN⟩ := exists_nat_gt (max L₀ 0 + 4 * K + 4)
  have hNL : max L₀ 0 + 4 * K + 4 < (N:ℝ) := hN
  refine ⟨Real.pi * ((N:ℝ) + 1/2), ?_, ⟨one_pos, ?_, fun t ht1 ht2 => ?_⟩⟩
  · have := le_max_left L₀ 0; nlinarith [le_max_right L₀ 0]
  · nlinarith [le_max_right L₀ 0]
  by_contra hv
  obtain ⟨m, hpm, hxm⟩ := gap_point_of_ne_zero_E02_38 u K hloc t hv
  -- `|t - mπ| ≥ π/2 - 1`
  set σ : ℝ := if 0 ≤ t then 1 else -1
  have hσt : |t| = σ * t := by
    simp only [σ]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hσ : |σ| = 1 := by simp only [σ]; split_ifs <;> simp
  have hdist : Real.pi / 2 - 1 ≤ |t - m * Real.pi| := by
    have key : ∀ j : ℤ, Real.pi / 2 ≤ |Real.pi * j + Real.pi / 2| := by
      intro j
      rw [show Real.pi * j + Real.pi / 2 = Real.pi * ((j:ℝ) + 1/2) by ring, abs_mul,
        abs_of_pos Real.pi_pos]
      have : (1:ℝ)/2 ≤ |(j:ℝ) + 1/2| := by
        rcases le_or_gt 0 j with hj | hj
        · have : (0:ℝ) ≤ j := by exact_mod_cast hj
          rw [abs_of_nonneg (by linarith)]; linarith
        · have : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
          rw [abs_of_neg (by linarith)]; linarith
      nlinarith
    -- `σ t - σ m π = π (N - σ m) + π/2 + r` with `|r| < 1`
    have hr : |(|t| - Real.pi * ((N:ℝ) + 1/2))| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have hσm : ∃ j : ℤ, σ * (m * Real.pi) = Real.pi * ((N:ℝ) - j) := by
      simp only [σ]; split_ifs
      · exact ⟨N - m, by push_cast; ring⟩
      · exact ⟨N + m, by push_cast; ring⟩
    obtain ⟨j, hj⟩ := hσm
    have e : σ * (t - m * Real.pi) =
        (Real.pi * j + Real.pi / 2) + (|t| - Real.pi * ((N:ℝ) + 1/2)) := by
      rw [mul_sub, ← hσt, hj]; ring
    have h1 : |t - m * Real.pi| = |σ * (t - m * Real.pi)| := by rw [abs_mul, hσ, one_mul]
    rw [h1, e]
    have := abs_sub_abs_le_abs_sub (Real.pi * j + Real.pi / 2) (-(|t| - Real.pi * ((N:ℝ) + 1/2)))
    rw [sub_neg_eq_add, abs_neg] at this
    linarith [key j]
  -- so `⟨m⟩ ≤ 2K`, hence `|m|` small, contradicting `|t| ≈ πN`
  have hm1 : japaneseBracket m ≤ 2 * K := by
    have h := le_trans hdist hxm
    rw [le_div_iff₀ (japaneseBracket_pos m)] at h
    nlinarith [japaneseBracket_pos m]
  have hmabs : |(m:ℝ)| ≤ 2 * K := by
    refine le_trans ?_ hm1
    unfold japaneseBracket
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]; linarith
  have h2 : |t - m * Real.pi| ≤ K := le_trans hxm (by
    rw [div_le_iff₀ (japaneseBracket_pos m)]; nlinarith [japaneseBracket_one_le m])
  have h3 : |t| ≤ |(m:ℝ)| * Real.pi + K := by
    have := abs_sub_abs_le_abs_sub t (m * Real.pi)
    rw [abs_mul, abs_of_pos Real.pi_pos] at this; linarith
  nlinarith [le_max_right L₀ 0]

/-- The remainder integrand `g(x) = (W(2x) - W(2p(x))) v(x)`. -/
def remainderIntegrandE02_38 (W : ℝ → ℝ) (u : PhysicalL2) (x : ℝ) : ℝ :=
  (W (2*x) - W (2 * actualQuasimomentumRealPartE02_38 u x)) * actualGapHeightE02_38 u x

/-- The `n`-th term `(2/π)∫_{g_n} [W(2λ) - W(2πn)] v` of v2 (B:eq:Rm). -/
def gapRemainderTermE02_38 (W : ℝ → ℝ) (u : PhysicalL2) (n : ℤ) : ℝ :=
  (2/Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
    (W (2*x) - W (2*Real.pi*n)) * actualGapHeightE02_38 u x

/-- Standing hypotheses on the weight and the field. -/
structure RemainderHypE02_38 (W : ℝ → ℝ) (k : ℕ) (A : ℝ) (u : PhysicalL2) : Prop where
  hW : ContDiff ℝ 2 W
  conv : ConvexOn ℝ Set.univ W
  hk : 1 ≤ k
  hA : 0 ≤ A
  deriv_bound : ∀ y, |deriv W y| ≤ A * (1 + |y|^(2*k+1))
  sob : SobolevSquareSummable (k:ℝ) (physicalFourier u)

namespace RemainderHypE02_38
variable {W : ℝ → ℝ} {k : ℕ} {A : ℝ} {u : PhysicalL2}

theorem sob1 (h : RemainderHypE02_38 W k A u) : SobolevSquareSummable 1 (physicalFourier u) :=
  sobolevSquareSummable_restrict 1 k (by exact_mod_cast h.hk) _ h.sob

theorem diff (h : RemainderHypE02_38 W k A u) : Differentiable ℝ W :=
  h.hW.differentiable (by norm_num)

theorem integrable_v (h : RemainderHypE02_38 W k A u) : Integrable (actualGapHeightE02_38 u) :=
  (actualGapHeight_integral_eq_normSq_E02_38 u h.sob1).1

theorem integrable_vk (h : RemainderHypE02_38 W k A u) :
    Integrable (fun t => (2*t)^(2*k) * actualGapHeightE02_38 u t) :=
  actualMoment_integrable_of_sobolev38 k h.hk u h.sob

theorem integrable_v1 (h : RemainderHypE02_38 W k A u) :
    Integrable (fun t => (2*t)^(2*1) * actualGapHeightE02_38 u t) :=
  actualMoment_integrable_of_sobolev38 1 le_rfl u (by exact_mod_cast h.sob1)

end RemainderHypE02_38

theorem continuous_remainderIntegrand_E02_38 (W : ℝ → ℝ) (hW : Continuous W) (u : PhysicalL2) :
    Continuous (remainderIntegrandE02_38 W u) := by
  unfold remainderIntegrandE02_38
  exact ((hW.comp (continuous_const.mul continuous_id)).sub (hW.comp (continuous_const.mul
    (continuous_actualQuasimomentumRealPartE02_38 u)))).mul (continuous_actualGapHeightE02_38 u)

/-- **F04.01–.03 (absolute convergence).** The remainder integrand is integrable, the gap terms are
absolutely summable, and they sum to `(2/π)∫ g`. -/
theorem gapRemainder_summable_E02_38 (W : ℝ → ℝ) (k : ℕ) (A : ℝ) (u : PhysicalL2)
    (h : RemainderHypE02_38 W k A u) :
    Integrable (remainderIntegrandE02_38 W u) ∧
    Summable (fun n : ℤ => |gapRemainderTermE02_38 W u n|) ∧
    HasSum (fun n : ℤ => gapRemainderTermE02_38 W u n)
      ((2/Real.pi) * ∫ x, remainderIntegrandE02_38 W u x) := by
  obtain ⟨K, hK, hloc⟩ := gapLocalization_of_sobolev_E02_38 u h.sob1
  obtain ⟨C, hC0, hC⟩ := weight_diff_bound_E02_38 W h.diff h.conv k A h.hA h.deriv_bound u K hK hloc
  set g := remainderIntegrandE02_38 W u
  have hgc : Continuous g := continuous_remainderIntegrand_E02_38 W h.diff.continuous u
  have hv0 := actualGapHeightE02_38_nonneg u
  have hdom : Integrable (fun x => C * (actualGapHeightE02_38 u x +
      (2*x)^(2*k) * actualGapHeightE02_38 u x)) :=
    (h.integrable_v.add h.integrable_vk).const_mul C
  have hgb : ∀ x, ‖g x‖ ≤ C * (actualGapHeightE02_38 u x + (2*x)^(2*k) * actualGapHeightE02_38 u x) := by
    intro x
    simp only [g, remainderIntegrandE02_38]
    by_cases hx : actualGapHeightE02_38 u x = 0
    · simp [hx]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 x)]
    have := hC x hx
    calc _ ≤ C * (1 + (2*x)^(2*k)) * actualGapHeightE02_38 u x :=
          mul_le_mul_of_nonneg_right this (hv0 x)
      _ = _ := by ring
  have hgi : Integrable g := hdom.mono' hgc.aestronglyMeasurable (Eventually.of_forall hgb)
  have hgai : Integrable (fun x => |g x|) := hgi.abs
  -- gap decomposition
  set s : ℤ → Set ℝ := fun n => actualGapLevelSetE02_38 u n
  have hs : ∀ n, s n = Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    fun n => (actualGapLevelSet_eq_Icc_E02_38 u n).2
  have hm : ∀ n, MeasurableSet (s n) := fun n => by rw [hs n]; exact measurableSet_Icc
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun x hxn hxm => hnm ?_
    have e1 : actualQuasimomentumRealPartE02_38 u x = (n:ℝ) * Real.pi := hxn
    have e2 : actualQuasimomentumRealPartE02_38 u x = (m:ℝ) * Real.pi := hxm
    have : (n:ℝ) = m := mul_right_cancel₀ Real.pi_pos.ne' (e1.symm.trans e2)
    exact_mod_cast this
  have hoff : ∀ (f : ℝ → ℝ), (∀ x, actualGapHeightE02_38 u x = 0 → f x = 0) →
      ∫ x in ⋃ n, s n, f x = ∫ x, f x := by
    intro f hf
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hf x ?_
    by_contra hv
    obtain ⟨m, hm'⟩ := realPart_int_mul_pi_of_gapHeight_ne_zero_E02_38 u x hv
    exact hx (Set.mem_iUnion.mpr ⟨m, hm'⟩)
  have hU := hasSum_integral_iUnion hm hd hgi.integrableOn
  rw [hoff g (fun x hx => by simp [g, remainderIntegrandE02_38, hx])] at hU
  have hUa := hasSum_integral_iUnion hm hd hgai.integrableOn
  rw [hoff (fun x => |g x|) (fun x hx => by simp [g, remainderIntegrandE02_38, hx])] at hUa
  have hterm : ∀ n, gapRemainderTermE02_38 W u n = (2/Real.pi) * ∫ x in s n, g x := by
    intro n
    have hab : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
      obtain ⟨y, hy⟩ := (actualGapLevelSet_eq_Icc_E02_38 u n).1
      have hy' : y ∈ s n := hy
      rw [hs n] at hy'; exact le_trans hy'.1 hy'.2
    unfold gapRemainderTermE02_38
    congr 1
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc, ← hs n]
    refine setIntegral_congr_fun (hm n) fun x hx => ?_
    have hpx : actualQuasimomentumRealPartE02_38 u x = (n:ℝ) * Real.pi := hx
    simp only [g, remainderIntegrandE02_38, hpx]
    ring_nf
  refine ⟨hgi, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      (hUa.summable.mul_left (2/Real.pi))
    rw [hterm n, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2/Real.pi)]
    exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (by positivity)
  · convert hU.mul_left (2/Real.pi) using 1
    funext n; exact hterm n

theorem tail_integral_le_E02_38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (L : ℝ) (hL : 0 < L) (hcut : IsBandCutE02_38 u L 1)
    (h2 : Integrable (fun t => (2*t)^(2*1) * actualGapHeightE02_38 u t)) :
    ∫ t, gapTailE02_38 u L t ≤ (∫ t, (2*t)^(2*1) * actualGapHeightE02_38 u t) / (4 * L^2) := by
  have hwi := integrable_gapTailE02_38 u hu L 1 hcut
  have hpos : 0 < 4 * L^2 := by positivity
  rw [← integral_div]
  refine integral_mono hwi (h2.div_const _) fun t => ?_
  have hv0 := actualGapHeightE02_38_nonneg u t
  have e : (2*t)^(2*1) = 4 * t^2 := by ring
  rw [e]
  by_cases ht : L < |t|
  · rw [hcut.tail_eq t ht, le_div_iff₀ hpos]
    have : L^2 ≤ t^2 := by nlinarith [sq_abs t, abs_nonneg t]
    nlinarith
  · push Not at ht
    rw [hcut.tail_eq_zero t (by linarith)]
    exact div_nonneg (mul_nonneg (by positivity) hv0) hpos.le

/-- **F04.05 (nonnegativity), Φ-free.** `∫ (W(2x) - W(2p(x))) v ≥ 0` for every `u ∈ H^k`. -/
theorem remainderIntegral_nonneg_E02_38 (W : ℝ → ℝ) (k : ℕ) (A : ℝ) (u : PhysicalL2)
    (h : RemainderHypE02_38 W k A u) :
    0 ≤ ∫ x, remainderIntegrandE02_38 W u x := by
  obtain ⟨hgi, -, -⟩ := gapRemainder_summable_E02_38 W k A u h
  obtain ⟨K, hK, hloc⟩ := gapLocalization_of_sobolev_E02_38 u h.sob1
  have hpi := Real.pi_pos
  have hv0 := actualGapHeightE02_38_nonneg u
  have hev : ∀ (j : ℕ) (y : ℝ), 0 ≤ y^(2*j) := fun j y => (even_two_mul j).pow_nonneg y
  set M0 := ∫ t, actualGapHeightE02_38 u t
  set Mk := ∫ t, (2*t)^(2*k) * actualGapHeightE02_38 u t
  set M2 := ∫ t, (2*t)^(2*1) * actualGapHeightE02_38 u t
  have hM0 : 0 ≤ M0 := integral_nonneg hv0
  have hMk : 0 ≤ Mk := integral_nonneg fun t => mul_nonneg (hev k _) (hv0 t)
  have hM2 : 0 ≤ M2 := integral_nonneg fun t => mul_nonneg (hev 1 _) (hv0 t)
  set c : ℝ := (1 + 4*K)^(2*k) * 2^(2*k)
  have hc1 : 1 ≤ c := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith))
    (one_le_pow₀ (by norm_num))
  -- derivative of `y ↦ W(2y)`
  have hderiv : ∀ z, deriv (fun y => W (2*y)) z = 2 * deriv W (2*z) := by
    intro z
    rw [deriv_comp_mul_left, smul_eq_mul]
  -- bound on `∫_{[-L,L]} |φ| v`
  have hΦ : ∀ L, 0 ≤ L →
      ∫ x in Icc (-L) L, |deriv (fun y => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)| *
        actualGapHeightE02_38 u x ≤ 2 * A * ((1 + (2*L + 4*K)) * c) * (M0 + Mk) := by
    intro L hL
    have hpt : ∀ x ∈ Icc (-L) L,
        |deriv (fun y => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)| * actualGapHeightE02_38 u x ≤
          2 * A * ((1 + (2*L + 4*K)) * c) *
            (actualGapHeightE02_38 u x + (2*x)^(2*k) * actualGapHeightE02_38 u x) := by
      intro x hx
      by_cases hvx : actualGapHeightE02_38 u x = 0
      · rw [hvx]; simp
      set q := 2 * |x| + 4 * K
      have hq0 : 0 ≤ q := by positivity
      have h2p := abs_two_p_le_E02_38 u K hK hloc x hvx
      have hxL : |x| ≤ L := abs_le.mpr hx
      have hqL : q ≤ 2*L + 4*K := by simp only [q]; linarith
      have hW' := h.deriv_bound (2 * actualQuasimomentumRealPartE02_38 u x)
      have hpow1 : |2 * actualQuasimomentumRealPartE02_38 u x|^(2*k+1) ≤ q^(2*k+1) :=
        pow_le_pow_left₀ (abs_nonneg _) h2p _
      have hpow2 : q^(2*k+1) ≤ (2*L + 4*K) * q^(2*k) := by
        rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_right hqL (by positivity)
      have hpow3 : q^(2*k) ≤ c * (1 + (2*x)^(2*k)) := by
        have h1 : q ≤ (1 + 4*K) * (1 + 2*|x|) := by simp only [q]; nlinarith [abs_nonneg x]
        have h2 : q^(2*k) ≤ ((1 + 4*K) * (1 + 2*|x|))^(2*k) := pow_le_pow_left₀ hq0 h1 _
        have h3 := one_add_pow_le_E02_38 (2*|x|) (by positivity) (2*k)
        have h4 : (2*|x|)^(2*k) = (2*x)^(2*k) := by
          rw [show 2*|x| = |2*x| by rw [abs_mul, abs_two], (even_two_mul k).pow_abs]
        rw [h4] at h3
        rw [mul_pow] at h2
        calc q^(2*k) ≤ (1 + 4*K)^(2*k) * (1 + 2*|x|)^(2*k) := h2
          _ ≤ (1 + 4*K)^(2*k) * (2^(2*k) * (1 + (2*x)^(2*k))) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = c * (1 + (2*x)^(2*k)) := by simp only [c]; ring
      have hd : |deriv (fun y => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)| ≤
          2 * A * ((1 + (2*L + 4*K)) * c) * (1 + (2*x)^(2*k)) := by
        rw [hderiv, abs_mul, abs_two]
        have hx2 : 0 ≤ (2*x)^(2*k) := hev k _
        have e1 : |deriv W (2 * actualQuasimomentumRealPartE02_38 u x)| ≤
            A * (1 + (2*L + 4*K) * (c * (1 + (2*x)^(2*k)))) := by
          refine hW'.trans (mul_le_mul_of_nonneg_left ?_ h.hA)
          have := le_trans hpow1 (le_trans hpow2
            (mul_le_mul_of_nonneg_left hpow3 (by positivity)))
          linarith
        have e2 : A * (1 + (2*L + 4*K) * (c * (1 + (2*x)^(2*k)))) ≤
            A * ((1 + (2*L + 4*K)) * c) * (1 + (2*x)^(2*k)) := by
          apply le_of_sub_nonneg
          have : 0 ≤ A * (c * (1 + (2*x)^(2*k)) - 1) := by
            apply mul_nonneg h.hA; nlinarith
          nlinarith
        linarith
      calc _ ≤ 2 * A * ((1 + (2*L + 4*K)) * c) * (1 + (2*x)^(2*k)) * actualGapHeightE02_38 u x :=
            mul_le_mul_of_nonneg_right hd (hv0 x)
        _ = _ := by ring
    have hint1 : IntegrableOn (fun x => |deriv (fun y => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)| *
        actualGapHeightE02_38 u x) (Icc (-L) L) := by
      refine ContinuousOn.integrableOn_Icc (Continuous.continuousOn ?_)
      have hdc : Continuous (deriv (fun y => W (2*y))) := by
        have h1 : ContDiff ℝ 2 (fun y => W (2*y)) := h.hW.comp (contDiff_const.mul contDiff_id)
        exact h1.continuous_deriv (by norm_num)
      exact (hdc.comp (continuous_actualQuasimomentumRealPartE02_38 u)).abs.mul
        (continuous_actualGapHeightE02_38 u)
    have hint2 : Integrable (fun x => 2 * A * ((1 + (2*L + 4*K)) * c) *
        (actualGapHeightE02_38 u x + (2*x)^(2*k) * actualGapHeightE02_38 u x)) :=
      (h.integrable_v.add h.integrable_vk).const_mul _
    calc _ ≤ ∫ x in Icc (-L) L, 2 * A * ((1 + (2*L + 4*K)) * c) *
          (actualGapHeightE02_38 u x + (2*x)^(2*k) * actualGapHeightE02_38 u x) :=
          setIntegral_mono_on hint1 hint2.integrableOn measurableSet_Icc hpt
      _ ≤ ∫ x, 2 * A * ((1 + (2*L + 4*K)) * c) *
          (actualGapHeightE02_38 u x + (2*x)^(2*k) * actualGapHeightE02_38 u x) :=
          setIntegral_le_integral hint2 (Eventually.of_forall fun x =>
            mul_nonneg (by have := hc1; have := h.hA; positivity)
              (add_nonneg (hv0 x) (mul_nonneg (hev k _) (hv0 x))))
      _ = 2 * A * ((1 + (2*L + 4*K)) * c) * (M0 + Mk) := by
          rw [integral_const_mul, integral_add h.integrable_v h.integrable_vk]
  -- the limit
  set B := 2 * A * c * (M0 + Mk) * M2
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h.hA)
    (by linarith)) (add_nonneg hM0 hMk)) hM2
  have hlimI : Tendsto (fun L : ℝ => ∫ x in (-L)..L, remainderIntegrandE02_38 W u x) atTop
      (𝓝 (∫ x, remainderIntegrandE02_38 W u x)) :=
    intervalIntegral_tendsto_integral hgi tendsto_neg_atTop_atBot tendsto_id
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨L₁, hL₁⟩ := (Metric.tendsto_atTop.mp hlimI) (ε/2) hε2
  set L₀ := max (max L₁ 1) ((1 + 1 + 4*K) * B / (ε/2) + 1)
  obtain ⟨L, hLL₀, hcut⟩ := exists_bandCut_E02_38 u K hK hloc L₀
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL₀
  have hLL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL₀
  have hLB : (1 + 1 + 4*K) * B / (ε/2) + 1 ≤ L := le_trans (le_max_right _ _) hLL₀
  have hL0 : 0 < L := by linarith
  have hconvT := convexTrunc_E02_38 u h.sob1 W h.hW h.conv L 1 hcut
  have hΦL := hΦ L hL0.le
  have htail := tail_integral_le_E02_38 u h.sob1 L hL0 hcut h.integrable_v1
  have hw0 : 0 ≤ ∫ t, gapTailE02_38 u L t := integral_nonneg fun t => (hcut.tail_le t).1
  have hΦ0 : 0 ≤ ∫ x in Icc (-L) L, |deriv (fun y => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)| *
      actualGapHeightE02_38 u x := setIntegral_nonneg measurableSet_Icc fun x _ =>
        mul_nonneg (abs_nonneg _) (hv0 x)
  -- cross term ≤ ε
  have hcross : (1/Real.pi) * (1/1) *
      (∫ x in Icc (-L) L, |deriv (fun y => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)| *
        actualGapHeightE02_38 u x) * (∫ t, gapTailE02_38 u L t) ≤ ε/2 := by
    have hpi1 : 1/Real.pi ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
    have s1 : (∫ x in Icc (-L) L, |deriv (fun y => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)| *
        actualGapHeightE02_38 u x) * (∫ t, gapTailE02_38 u L t) ≤
        (2 * A * ((1 + (2*L + 4*K)) * c) * (M0 + Mk)) * (M2 / (4 * L^2)) :=
      mul_le_mul hΦL htail hw0 (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h.hA)
        (mul_nonneg (by linarith) (by linarith))) (add_nonneg hM0 hMk))
    have s2 : (2 * A * ((1 + (2*L + 4*K)) * c) * (M0 + Mk)) * (M2 / (4 * L^2)) ≤
        (1 + 1 + 4*K) * B / L := by
      have e : (2 * A * ((1 + (2*L + 4*K)) * c) * (M0 + Mk)) * (M2 / (4 * L^2)) =
          B * ((1 + 2*L + 4*K) / (4 * L^2)) := by simp only [B]; field_simp; ring
      rw [e]
      have hq : (1 + 2*L + 4*K) / (4 * L^2) ≤ (1 + 1 + 4*K) / L := by
        rw [div_le_div_iff₀ (by positivity) hL0]
        have hLL : L ≤ L^2 := by nlinarith
        have : K * L ≤ K * L^2 := mul_le_mul_of_nonneg_left hLL hK.le
        nlinarith
      calc B * ((1 + 2*L + 4*K) / (4 * L^2)) ≤ B * ((1 + 1 + 4*K) / L) :=
            mul_le_mul_of_nonneg_left hq hB
        _ = (1 + 1 + 4*K) * B / L := by ring
    have s3 : (1 + 1 + 4*K) * B / L ≤ ε/2 := by
      rw [div_le_iff₀ hL0]
      have := (div_le_iff₀ hε2).mp (by linarith : (1 + 1 + 4*K) * B / (ε/2) ≤ L)
      linarith
    have hprod0 : 0 ≤ (∫ x in Icc (-L) L, |deriv (fun y => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)| *
        actualGapHeightE02_38 u x) * (∫ t, gapTailE02_38 u L t) := mul_nonneg hΦ0 hw0
    calc _ = (1/Real.pi) * ((∫ x in Icc (-L) L, |deriv (fun y => W (2*y))
            (actualQuasimomentumRealPartE02_38 u x)| * actualGapHeightE02_38 u x) *
            (∫ t, gapTailE02_38 u L t)) := by ring
      _ ≤ 1 * ((∫ x in Icc (-L) L, |deriv (fun y => W (2*y))
            (actualQuasimomentumRealPartE02_38 u x)| * actualGapHeightE02_38 u x) *
            (∫ t, gapTailE02_38 u L t)) := mul_le_mul_of_nonneg_right hpi1 hprod0
      _ ≤ ε/2 := by linarith
  have hI : ∫ x in (-L)..L, remainderIntegrandE02_38 W u x =
      ∫ x in Icc (-L) L, (W (2*x) - W (2 * actualQuasimomentumRealPartE02_38 u x)) *
        actualGapHeightE02_38 u x := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]; rfl
  have hclose := hL₁ L hLL1
  rw [Real.dist_eq, hI] at hclose
  have := (abs_lt.mp hclose).2
  linarith

/-- **F04 (Φ-free part) for a general weight**: absolute convergence and `R ≥ 0`. -/
theorem gapRemainder_F04_E02_38 (W : ℝ → ℝ) (k : ℕ) (A : ℝ) (u : PhysicalL2)
    (h : RemainderHypE02_38 W k A u) :
    Summable (fun n : ℤ => |gapRemainderTermE02_38 W u n|) ∧
    0 ≤ ∑' n : ℤ, gapRemainderTermE02_38 W u n := by
  obtain ⟨-, hs, hS⟩ := gapRemainder_summable_E02_38 W k A u h
  refine ⟨hs, ?_⟩
  rw [hS.tsum_eq]
  exact mul_nonneg (by positivity) (remainderIntegral_nonneg_E02_38 W k A u h)

/-! ## The finite-order weight `W_m(r) = Σ_{j≤m} β_j r^{2j}` (v2 B:eq:finitehierarchy) -/

/-- `W_m(r) = Σ_{j=0}^m β_j r^{2j}`. -/
def finiteWeightE02_38 (m : ℕ) (β : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), β j * r^(2*j)

theorem hasDerivAt_finiteWeight_E02_38 (m : ℕ) (β : ℕ → ℝ) (y : ℝ) :
    HasDerivAt (finiteWeightE02_38 m β)
      (∑ j ∈ Finset.range (m + 1), β j * (((2*j : ℕ) : ℝ) * y^(2*j - 1))) y := by
  unfold finiteWeightE02_38
  have := HasDerivAt.sum (u := Finset.range (m + 1))
    (fun j _ => (hasDerivAt_pow (2*j) y).const_mul (β j))
  convert this using 1
  funext x; simp [Finset.sum_apply]

theorem finiteWeight_hyp_E02_38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) :
    ContDiff ℝ 2 (finiteWeightE02_38 m β) ∧ ConvexOn ℝ Set.univ (finiteWeightE02_38 m β) ∧
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y, |deriv (finiteWeightE02_38 m β) y| ≤ A * (1 + |y|^(2*(m-1)+1)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold finiteWeightE02_38
    exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_id.pow _)
  · unfold finiteWeightE02_38
    have hconv : ∀ s : Finset ℕ, s ⊆ Finset.range (m + 1) →
        ConvexOn ℝ Set.univ (fun r : ℝ => ∑ j ∈ s, β j * r^(2*j)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simpa using (convexOn_const (0:ℝ) convex_univ)
      | insert a s ha ih =>
        intro hs
        have hβa : 0 ≤ β a := (hβ a (by
          have := hs (Finset.mem_insert_self a s); simp at this; omega)).le
        have h1 : ConvexOn ℝ Set.univ (fun r : ℝ => β a * r^(2*a)) := by
          have := ((even_two_mul a).convexOn_pow).smul hβa
          simpa [smul_eq_mul] using this
        have h2 := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
        have := h1.add h2
        convert this using 1
        funext r; simp [Finset.sum_insert ha]
    exact hconv _ (subset_refl _)
  · refine ⟨∑ j ∈ Finset.range (m + 1), |β j| * (2*j : ℕ), Finset.sum_nonneg fun j _ => by positivity,
      fun y => ?_⟩
    rw [(hasDerivAt_finiteWeight_E02_38 m β y).deriv, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hjm : j ≤ m := by simp at hj; omega
    rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rcases le_total |y| 1 with hy | hy
    · have : |y|^(2*j-1) ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
      linarith [pow_nonneg (abs_nonneg y) (2*(m-1)+1)]
    · have : |y|^(2*j-1) ≤ |y|^(2*(m-1)+1) := pow_le_pow_right₀ hy (by omega)
      linarith

/-- **F04 (B:lem:spectral), Φ-free part.** For `m ≥ 2`, `β_j > 0` and `u ∈ H^{m-1}`, the series
`R_m(u) = Σ_n (2/π)∫_{g_n(u)} [W_m(2λ) - a_{m,n}] v(λ;u) dλ` (with `a_{m,n} = W_m(2πn)`) converges absolutely
and `R_m(u) ≥ 0`. Continuity on `H^{m-1}` (F04.04) is not claimed here; see `F04_ROUTE.md` (TF-H^k). -/
theorem spectralRemainder_F04_E02_38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (u : PhysicalL2) (hu : SobolevSquareSummable ((m - 1 : ℕ) : ℝ) (physicalFourier u)) :
    Summable (fun n : ℤ => |gapRemainderTermE02_38 (finiteWeightE02_38 m β) u n|) ∧
    0 ≤ ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β) u n := by
  obtain ⟨hW, hconv, A, hA, hd⟩ := finiteWeight_hyp_E02_38 m hm β hβ
  exact gapRemainder_F04_E02_38 _ (m - 1) A u ⟨hW, hconv, by omega, hA, hd, hu⟩

end NlsGge.SpectralFoundations
end
