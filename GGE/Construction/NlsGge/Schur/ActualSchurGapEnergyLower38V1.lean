import NlsGge.Schur.ActualSchurF03Package38V1
import NlsGge.Weights.Regularity
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# NEW-F05 (F:eq:rho, F:eq:rhoproduct): per-gap weighted energy lower bound

* `weight_monotone_ratio38`: log-derivative comparison of `W` on a segment away from zero.
* `weight_gap_lower38`: `W(2λ) ≥ W(2πn) exp(-C |n|^{-1/2} δ)` when `|λ + nπ| ≤ δ ≤ π|n|/2`.
* `actualSchurGapEnergyLower38V1`: the per-gap bound
  `ρ_{n,R} a_n ‖q_n‖² ≤ (2/π) ∫_{λ⁻}^{λ⁺} W(2λ) v(λ) dλ`.
* `rhoTail_real38`: the real-series bound `F:eq:rhoproduct`.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot NlsGge.SpectralFoundations

namespace NlsGge.Schur

/-- `ρ_{n,R}` of `F:eq:rho`. -/
def actualSchurRho38 (C R : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-C * (R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ) + R ^ 4 / (n : ℝ) ^ 2))

/-- `W` is increasing on `(0,∞)` and `log W` has slope `≤ C m^{-1/2}` on `[m,∞)`. -/
theorem weight_log_slope38 (lower upper : ℝ) (hl : 0 < lower) (hlu : lower ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ → ℝ, (∀ j, lower ≤ c j) → (∀ j, c j ≤ upper) →
      ∀ m a b : ℝ, 0 < m → m ≤ a → a ≤ b →
        NlsGge.Weights.weight c a ≤ NlsGge.Weights.weight c b ∧
        NlsGge.Weights.weight c b ≤
          NlsGge.Weights.weight c a * Real.exp (C * m ^ (-1 / 2 : ℝ) * (b - a)) := by
  obtain ⟨C, -, hCpos, hC⟩ := NlsGge.Weights.weight_uniform_logDerivative_constant lower upper hl hlu
  refine ⟨C, hCpos, ?_⟩
  intro c hb hu m a b hm hma hab
  have hapos : 0 < a := hm.trans_le hma
  have hWpos : ∀ x, 0 < NlsGge.Weights.weight c x := fun x =>
    NlsGge.Weights.weight_pos lower upper c hl hb hu x
  rcases hab.eq_or_lt with h | h
  · subst h
    refine ⟨le_rfl, ?_⟩
    simp
  have hder : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun y => Real.log (NlsGge.Weights.weight c y))
      (deriv (NlsGge.Weights.weight c) x / NlsGge.Weights.weight c x) x := by
    intro x _
    have := (NlsGge.Weights.weight_hasDerivAt lower upper c hl hb hu x).log (hWpos x).ne'
    rw [(NlsGge.Weights.weight_hasDerivAt lower upper c hl hb hu x).deriv]
    exact this
  have hcont : ContinuousOn (fun y => Real.log (NlsGge.Weights.weight c y)) (Set.Icc a b) := by
    intro x _
    exact ((NlsGge.Weights.weight_hasDerivAt lower upper c hl hb hu x).continuousAt.log
      (hWpos x).ne').continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope
    (fun y => Real.log (NlsGge.Weights.weight c y))
    (fun x => deriv (NlsGge.Weights.weight c) x / NlsGge.Weights.weight c x) h hcont hder
  have hξpos : 0 < ξ := hapos.trans hξ.1
  obtain ⟨⟨h0, h1⟩, -⟩ := hC c hb hu ξ hξpos
  have hba : 0 < b - a := sub_pos.mpr h
  have hdiff : Real.log (NlsGge.Weights.weight c b) - Real.log (NlsGge.Weights.weight c a) =
      deriv (NlsGge.Weights.weight c) ξ / NlsGge.Weights.weight c ξ * (b - a) := by
    rw [hξeq]; field_simp
  have hmξ : ξ ^ (-1 / 2 : ℝ) ≤ m ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hm (hma.trans hξ.1.le) (by norm_num)
  have hlogmono : 0 ≤ Real.log (NlsGge.Weights.weight c b) - Real.log (NlsGge.Weights.weight c a) := by
    rw [hdiff]; exact mul_nonneg h0 hba.le
  have hlogle : Real.log (NlsGge.Weights.weight c b) - Real.log (NlsGge.Weights.weight c a) ≤
      C * m ^ (-1 / 2 : ℝ) * (b - a) := by
    rw [hdiff]
    exact mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left hmξ hCpos.le)) hba.le
  constructor
  · have := Real.log_le_log_iff (hWpos a) (hWpos b) |>.mp (by linarith)
    exact this
  · have h2 : Real.log (NlsGge.Weights.weight c b) ≤
        Real.log (NlsGge.Weights.weight c a) + C * m ^ (-1 / 2 : ℝ) * (b - a) := by linarith
    calc NlsGge.Weights.weight c b = Real.exp (Real.log (NlsGge.Weights.weight c b)) :=
          (Real.exp_log (hWpos b)).symm
      _ ≤ Real.exp (Real.log (NlsGge.Weights.weight c a) + C * m ^ (-1 / 2 : ℝ) * (b - a)) :=
          Real.exp_le_exp.mpr h2
      _ = _ := by rw [Real.exp_add, Real.exp_log (hWpos a)]

/-- Gap-local lower bound for `W(2λ)`. -/
theorem weight_gap_lower38 (lower upper : ℝ) (hl : 0 < lower) (hlu : lower ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ → ℝ, (∀ j, lower ≤ c j) → (∀ j, c j ≤ upper) →
      ∀ (n : ℤ) (lam δ : ℝ), n ≠ 0 → |lam + n * Real.pi| ≤ δ → 2 * δ ≤ Real.pi * |(n : ℝ)| →
        NlsGge.Weights.weight c (2 * Real.pi * n) *
            Real.exp (-(C * (Real.pi * |(n : ℝ)|) ^ (-1 / 2 : ℝ) * (2 * δ))) ≤
          NlsGge.Weights.weight c (2 * lam) := by
  obtain ⟨C, hCpos, hC⟩ := weight_log_slope38 lower upper hl hlu
  refine ⟨C, hCpos, ?_⟩
  intro c hb hu n lam δ hn hlam hδ
  have hnpos : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hpn : 0 < Real.pi * |(n : ℝ)| := by positivity
  set m := Real.pi * |(n : ℝ)| with hm
  set s := |2 * lam| with hs
  set t := 2 * Real.pi * |(n : ℝ)| with ht
  have hWs : NlsGge.Weights.weight c (2 * lam) = NlsGge.Weights.weight c s := by
    rcases abs_cases (2 * lam) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hs, h]
    · rw [hs, h, NlsGge.Weights.weight_even]
  have hWt : NlsGge.Weights.weight c (2 * Real.pi * n) = NlsGge.Weights.weight c t := by
    rcases abs_cases (n : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [ht, h]
    · rw [ht, h, show 2 * Real.pi * -(n : ℝ) = -(2 * Real.pi * n) by ring,
        NlsGge.Weights.weight_even]
  have hdist : |s - t| ≤ 2 * δ := by
    have h1 : |s - t| ≤ |2 * lam - (-(2 * Real.pi * n))| := by
      have : t = |-(2 * Real.pi * n)| := by
        rw [ht, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      rw [hs, this]; exact abs_abs_sub_abs_le_abs_sub _ _
    have h2 : 2 * lam - (-(2 * Real.pi * n)) = 2 * (lam + n * Real.pi) := by ring
    rw [h2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h1
    linarith
  have hsm : m ≤ s := by
    have := (abs_le.mp hdist).1
    have : t - 2 * δ ≤ s := by linarith
    rw [hm]; nlinarith [ht]
  have htm : m ≤ t := by rw [hm, ht]; nlinarith
  rw [hWs, hWt]
  rcases le_total s t with hst | hts
  · obtain ⟨-, h2⟩ := hC c hb hu m s t hpn hsm hst
    have hexp : Real.exp (C * m ^ (-1 / 2 : ℝ) * (t - s)) ≤
        Real.exp (C * m ^ (-1 / 2 : ℝ) * (2 * δ)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := (abs_le.mp hdist).2
      have := le_abs_self (t - s)
      rw [abs_sub_comm] at hdist; linarith [abs_sub_comm s t]
    have hWspos := NlsGge.Weights.weight_pos lower upper c hl hb hu s
    have hpos := Real.exp_pos (C * m ^ (-1 / 2 : ℝ) * (2 * δ))
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ hpos]
    calc NlsGge.Weights.weight c t ≤ NlsGge.Weights.weight c s * Real.exp (C * m ^ (-1 / 2 : ℝ) * (t - s)) := h2
      _ ≤ NlsGge.Weights.weight c s * Real.exp (C * m ^ (-1 / 2 : ℝ) * (2 * δ)) :=
          mul_le_mul_of_nonneg_left hexp hWspos.le
  · obtain ⟨h1, -⟩ := hC c hb hu m t s hpn htm hts
    have hWtpos := NlsGge.Weights.weight_pos lower upper c hl hb hu t
    have : Real.exp (-(C * m ^ (-1 / 2 : ℝ) * (2 * δ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ δ := by nlinarith [abs_nonneg (lam + n * Real.pi)]
      have : 0 ≤ C * m ^ (-1 / 2 : ℝ) * (2 * δ) := by positivity
      linarith
    calc NlsGge.Weights.weight c t * Real.exp (-(C * m ^ (-1 / 2 : ℝ) * (2 * δ)))
        ≤ NlsGge.Weights.weight c t * 1 := mul_le_mul_of_nonneg_left this hWtpos.le
      _ ≤ _ := by rw [mul_one]; exact h1


theorem continuous_weight_two_mul38 (lower upper : ℝ) (hl : 0 < lower) (c : ℕ → ℝ)
    (hb : ∀ j, lower ≤ c j) (hu : ∀ j, c j ≤ upper) :
    Continuous (fun lam : ℝ => NlsGge.Weights.weight c (2 * lam)) := by
  have : Continuous (NlsGge.Weights.weight c) :=
    continuous_iff_continuousAt.mpr fun x =>
      (NlsGge.Weights.weight_hasDerivAt lower upper c hl hb hu x).continuousAt
  exact this.comp (continuous_const.mul continuous_id)

/-- F05.07 per-gap bound: for `|n| ≥ K R³`, `‖w‖ ≤ R`,
`ρ_{n,R} a_n ‖q_n‖² ≤ (2/π) ∫_{λ⁻}^{λ⁺} W(2λ) v(λ) dλ` with `a_n = W(2πn)`. -/
theorem actualSchurGapEnergyLower38V1 (lower upper : ℝ) (hl : 0 < lower) (hlu : lower ≤ upper) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ c : ℕ → ℝ, (∀ j, lower ≤ c j) → (∀ j, c j ≤ upper) →
      ∀ R : ℝ, 1 ≤ R → ∀ n : ℤ, K * R ^ 3 ≤ |(n : ℝ)| →
      ∀ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)), ‖w‖ ≤ R →
        actualSchurRho38 C R n * NlsGge.Weights.weight c (2 * Real.pi * n) *
            ‖actualSchurQn38 R n (w, actualH1Conj38 w)‖ ^ 2 ≤
          (2 / Real.pi) * ∫ lam in
              actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)..
              actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n),
            NlsGge.Weights.weight c (2 * lam) *
              actualGapHeightE02_38 (physicalH1ComplexCarrierToL2Actual22 w) lam := by
  obtain ⟨Kp, hKp, hp⟩ := actualSchurF03Package38V1
  obtain ⟨Cg, hCg, hg⟩ := weight_gap_lower38 lower upper hl hlu
  set C0 : ℝ := actualSchurGapLocalConstant38 with hC0
  set C2 : ℝ := freeResolventComplementaryInverseUniformConstant22 ^ 2 *
    freeResolventSchurUniformConstant ^ 2 with hC2
  have hC2nn : 0 ≤ C2 := by positivity
  set C1 : ℝ := 2 * Cg * |C0| * Real.pi ^ (-1 / 2 : ℝ) with hC1
  have hC1nn : 0 ≤ C1 := by positivity
  refine ⟨Kp + 1 + |C0|, C1 + 4 * C2 + 1, by positivity, by positivity, ?_⟩
  intro c hb hu R hR n hn w hwR
  have hKn : Kp * R ^ 3 ≤ |(n : ℝ)| := by
    have : 0 ≤ R ^ 3 := by positivity
    nlinarith [abs_nonneg C0]
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hn1 : 1 ≤ |(n : ℝ)| := by
    have : 0 ≤ R ^ 3 := by positivity
    nlinarith [abs_nonneg C0]
  have hC0n : |C0| * R ^ 3 ≤ |(n : ℝ)| := by
    have : 0 ≤ R ^ 3 := by positivity
    nlinarith [abs_nonneg C0]
  have hnpos : 0 < |(n : ℝ)| := by linarith
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hnpos; simp at hnpos
  obtain ⟨⟨lp, lm, hlp, hlm⟩, hrest⟩ := hp R hR n hKn w hwR
  obtain ⟨-, ⟨-, hqgap⟩, ⟨hcl, hcu⟩, hact⟩ :=
    hrest lp lm hlp.1 hlp.2 hlm.1 hlm.2
  set U := physicalH1ComplexCarrierToL2Actual22 w with hU
  set lo := actualGapLowerE02_38 U (-n) with hlo
  set hi := actualGapUpperE02_38 U (-n) with hhi
  set q := actualSchurQn38 R n (w, actualH1Conj38 w) with hq
  set d := actualSchurGapParameter38 R n with hd
  have hd0 : 0 ≤ d := by rw [hd, actualSchurGapParameter38]; positivity
  have hd2 : d = C2 * (R ^ 4 / (n : ℝ) ^ 2) := by
    rw [hd, actualSchurGapParameter38, hC2, sq_abs]; ring
  have hlohi : lo ≤ hi := by
    have h0 : 0 ≤ 2 * ‖q‖ / (1 + 2 * d) := by positivity
    linarith
  set δ : ℝ := |C0| * R ^ 3 / |(n : ℝ)| with hδ
  have hδ2 : 2 * δ ≤ Real.pi * |(n : ℝ)| := by
    have h1 : δ ≤ 1 := by
      rw [hδ, div_le_one hnpos]; exact hC0n
    have := Real.pi_gt_three
    nlinarith
  have hCl : |lo + n * Real.pi| ≤ δ := hcl.trans (by
    rw [hδ]; exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hnpos.le)
  have hCu : |hi + n * Real.pi| ≤ δ := hcu.trans (by
    rw [hδ]; exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hnpos.le)
  -- exponent
  set A : ℝ := Cg * (Real.pi * |(n : ℝ)|) ^ (-1 / 2 : ℝ) * (2 * δ) with hA
  have hAeq : A = C1 * (R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ)) := by
    have h1 : (Real.pi * |(n : ℝ)|) ^ (-1 / 2 : ℝ) =
        Real.pi ^ (-1 / 2 : ℝ) * |(n : ℝ)| ^ (-1 / 2 : ℝ) :=
      Real.mul_rpow Real.pi_pos.le hnpos.le
    have h2 : |(n : ℝ)| ^ (-(3 / 2) : ℝ) = |(n : ℝ)| ^ (-1 / 2 : ℝ) * |(n : ℝ)|⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hnpos]; norm_num
    rw [hA, h1, h2, hC1, hδ]
    field_simp
  have hpoint : ∀ lam ∈ Set.uIcc lo hi,
      NlsGge.Weights.weight c (2 * Real.pi * n) * Real.exp (-A) ≤
        NlsGge.Weights.weight c (2 * lam) := by
    intro lam hlam
    rw [Set.uIcc_of_le hlohi] at hlam
    have hlamδ : |lam + n * Real.pi| ≤ δ := by
      rw [abs_le] at hCl hCu ⊢
      constructor <;> linarith [hlam.1, hlam.2]
    exact hg c hb hu n lam δ hn0 hlamδ hδ2
  have hcont := continuous_weight_two_mul38 lower upper hl c hb hu
  have hh := continuous_actualGapHeightE02_38 U
  have hI1 : IntervalIntegrable (fun lam => NlsGge.Weights.weight c (2 * Real.pi * n) *
      Real.exp (-A) * actualGapHeightE02_38 U lam) MeasureTheory.volume lo hi :=
    (continuous_const.mul hh).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun lam => NlsGge.Weights.weight c (2 * lam) *
      actualGapHeightE02_38 U lam) MeasureTheory.volume lo hi :=
    (hcont.mul hh).intervalIntegrable _ _
  have hmono : ∫ lam in lo..hi, NlsGge.Weights.weight c (2 * Real.pi * n) * Real.exp (-A) *
        actualGapHeightE02_38 U lam ≤
      ∫ lam in lo..hi, NlsGge.Weights.weight c (2 * lam) * actualGapHeightE02_38 U lam := by
    apply intervalIntegral.integral_mono_on hlohi hI1 hI2
    intro lam hlam
    exact mul_le_mul_of_nonneg_right (hpoint lam (by rw [Set.uIcc_of_le hlohi]; exact hlam))
      (actualGapHeightE02_38_nonneg U lam)
  rw [intervalIntegral.integral_const_mul] at hmono
  have hapos : 0 ≤ NlsGge.Weights.weight c (2 * Real.pi * n) :=
    (NlsGge.Weights.weight_pos lower upper c hl hb hu _).le
  have hact' : Real.exp (-4 * d) * ‖q‖ ^ 2 ≤
      (2 / Real.pi) * ∫ x in lo..hi, actualGapHeightE02_38 U x := hact
  have hexpA : 0 ≤ Real.exp (-A) := (Real.exp_pos _).le
  have hexpexp : actualSchurRho38 (C1 + 4 * C2 + 1) R n ≤ Real.exp (-A) * Real.exp (-4 * d) := by
    rw [← Real.exp_add, actualSchurRho38]
    apply Real.exp_le_exp.mpr
    have hT1 : 0 ≤ R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ) := by positivity
    have hT2 : 0 ≤ R ^ 4 / (n : ℝ) ^ 2 := by positivity
    rw [hAeq, hd2]
    nlinarith [mul_nonneg hC1nn hT1, mul_nonneg hC2nn hT2, hT1, hT2]
  have hq2 : 0 ≤ ‖q‖ ^ 2 := by positivity
  calc actualSchurRho38 (C1 + 4 * C2 + 1) R n * NlsGge.Weights.weight c (2 * Real.pi * n) * ‖q‖ ^ 2
      ≤ (Real.exp (-A) * Real.exp (-4 * d)) * NlsGge.Weights.weight c (2 * Real.pi * n) * ‖q‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hq2
        exact mul_le_mul_of_nonneg_right hexpexp hapos
    _ = NlsGge.Weights.weight c (2 * Real.pi * n) * Real.exp (-A) *
          (Real.exp (-4 * d) * ‖q‖ ^ 2) := by ring
    _ ≤ NlsGge.Weights.weight c (2 * Real.pi * n) * Real.exp (-A) *
          ((2 / Real.pi) * ∫ x in lo..hi, actualGapHeightE02_38 U x) :=
        mul_le_mul_of_nonneg_left hact' (mul_nonneg hapos hexpA)
    _ = (2 / Real.pi) * (NlsGge.Weights.weight c (2 * Real.pi * n) * Real.exp (-A) *
          ∫ x in lo..hi, actualGapHeightE02_38 U x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by positivity)


/-- Comparison of a power tail with its integral. -/
theorem rpow_tail_sum_le38 (p : ℝ) (hp : 1 < p) (M : ℝ) (hM : 0 < M) (L : ℕ) :
    ∑ i ∈ Finset.range L, (M + ((i + 1 : ℕ) : ℝ)) ^ (-p) ≤ M ^ (1 - p) / (p - 1) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Icc M (M + L)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hM.trans_le hx.1) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  have hint : ∫ x in M..M + L, x ^ (-p) = ((M + L) ^ (-p + 1) - M ^ (-p + 1)) / (-p + 1) := by
    apply integral_rpow
    right
    refine ⟨by linarith, ?_⟩
    rw [Set.uIcc_of_le (by linarith)]
    intro h0; linarith [h0.1]
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hpos : 0 < (M + L) := by linarith
  have h2 : (M + L) ^ (-p + 1) ≤ M ^ (-p + 1) :=
    Real.rpow_le_rpow_of_nonpos hM (by linarith) (by linarith)
  have hpow : 0 ≤ (M + L) ^ (-p + 1) := (Real.rpow_pos_of_pos hpos _).le
  refine h1.trans ?_
  rw [hint]
  have : 1 - p = -p + 1 := by ring
  rw [this]
  have hne : -p + 1 < 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have heq : ((M + L) ^ (-p + 1) - M ^ (-p + 1)) / (-p + 1) =
      (M ^ (-p + 1) - (M + L) ^ (-p + 1)) / (p - 1) := by
    have h3 : -p + 1 = -(p - 1) := by ring
    rw [h3, div_neg, ← neg_div, neg_sub]
  rw [heq]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)


/-- `F:eq:rhoproduct` (real-series form): for `M ≥ 1`,
`Σ_{|n|>M} (R³|n|^{-3/2} + R⁴ n^{-2}) ≤ 4 (R³ M^{-1/2} + R⁴ M^{-1})`, with summability. -/
theorem rhoTail_real38 (R : ℝ) (hR : 0 ≤ R) (M : ℕ) (hM : 1 ≤ M) :
    Summable (fun n : ℤ => if M < n.natAbs then
        R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ) + R ^ 4 / (n : ℝ) ^ 2 else 0) ∧
    ∑' n : ℤ, (if M < n.natAbs then
        R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ) + R ^ 4 / (n : ℝ) ^ 2 else 0) ≤
      4 * (R ^ 3 * (M : ℝ) ^ (-1 / 2 : ℝ) + R ^ 4 / M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set a : ℕ → ℝ := fun k => if M < k then
    R ^ 3 * (k : ℝ) ^ (-(3 / 2) : ℝ) + R ^ 4 / (k : ℝ) ^ 2 else 0 with ha
  have ha0 : ∀ k, 0 ≤ a k := by
    intro k; simp only [ha]; split_ifs <;> positivity
  have hshift : ∀ i : ℕ, a (i + (M + 1)) =
      R ^ 3 * (M + ((i + 1 : ℕ) : ℝ)) ^ (-(3 / 2) : ℝ) + R ^ 4 * (M + ((i + 1 : ℕ) : ℝ)) ^ (-2 : ℝ) := by
    intro i
    have hlt : M < i + (M + 1) := by omega
    have hc : ((i + (M + 1) : ℕ) : ℝ) = M + ((i + 1 : ℕ) : ℝ) := by push_cast; ring
    simp only [ha, hlt, ite_true, hc]
    have hx : (0 : ℝ) < M + ((i + 1 : ℕ) : ℝ) := by positivity
    have e2' : (M + ((i + 1 : ℕ) : ℝ)) ^ (-2 : ℝ) = ((M + ((i + 1 : ℕ) : ℝ)) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx.le, Real.rpow_two]
    rw [e2']; ring
  have hbound : ∀ L : ℕ, ∑ i ∈ Finset.range L, a (i + (M + 1)) ≤
      2 * (R ^ 3 * (M : ℝ) ^ (-1 / 2 : ℝ)) + R ^ 4 / M := by
    intro L
    simp_rw [hshift]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := rpow_tail_sum_le38 (3 / 2) (by norm_num) M hMpos L
    have h2 := rpow_tail_sum_le38 2 (by norm_num) M hMpos L
    have e1 : (M : ℝ) ^ (1 - 3 / 2 : ℝ) / (3 / 2 - 1) = 2 * (M : ℝ) ^ (-1 / 2 : ℝ) := by
      norm_num; ring
    have e2 : (M : ℝ) ^ (1 - 2 : ℝ) / (2 - 1) = 1 / M := by
      norm_num [Real.rpow_neg_one]
    rw [e1] at h1
    rw [e2] at h2
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ R ^ 3)
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ R ^ 4)
    have e3 : R ^ 4 * (1 / (M:ℝ)) = R ^ 4 / M := by ring
    linarith
  have hsumTail : Summable (fun i : ℕ => a (i + (M + 1))) :=
    summable_of_sum_range_le (fun i => ha0 _) hbound
  have hsum : Summable a := (summable_nat_add_iff (M + 1)).mp hsumTail
  have hT : ∑' k, a k ≤ 2 * (R ^ 3 * (M : ℝ) ^ (-1 / 2 : ℝ)) + R ^ 4 / M := by
    have h0 := hsum.sum_add_tsum_nat_add (M + 1)
    have hz : ∑ i ∈ Finset.range (M + 1), a i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have : ¬ M < i := by simp at hi; omega
      simp [ha, this]
    rw [hz, zero_add] at h0
    rw [← h0]
    exact Real.tsum_le_of_sum_range_le (fun i => ha0 _) hbound
  have hg : (fun n : ℤ => if M < n.natAbs then
        R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ) + R ^ 4 / (n : ℝ) ^ 2 else 0) =
      fun n : ℤ => a n.natAbs := by
    funext n
    have hc : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    simp only [ha]
    rw [hc, sq_abs]
  rw [hg]
  have hn1 : ∀ n : ℕ, a ((n : ℤ)).natAbs = a n := fun n => by rw [Int.natAbs_natCast]
  have hn2 : ∀ n : ℕ, a ((Int.negSucc n)).natAbs = a (n + 1) := fun n => by
    rw [Int.natAbs_negSucc]
  have hneg1 : Summable (fun n : ℕ => a ((n : ℤ)).natAbs) := by
    simp_rw [hn1]; exact hsum
  have hneg2 : Summable (fun n : ℕ => a ((Int.negSucc n)).natAbs) := by
    simp_rw [hn2]; exact (summable_nat_add_iff 1).mpr hsum
  refine ⟨Summable.of_nat_of_neg_add_one hneg1 hneg2, ?_⟩
  have key : ∑' n : ℤ, a n.natAbs =
      ∑' n : ℕ, a ((n : ℤ)).natAbs + ∑' n : ℕ, a ((Int.negSucc n)).natAbs :=
    tsum_of_nat_of_neg_add_one (f := fun n : ℤ => a n.natAbs) hneg1 hneg2
  have key2 : ∑' n : ℕ, a ((n : ℤ)).natAbs = ∑' n : ℕ, a n := tsum_congr hn1
  have key3 : ∑' n : ℕ, a ((Int.negSucc n)).natAbs = ∑' n : ℕ, a (n + 1) := tsum_congr hn2
  rw [key, key2, key3]
  have e3 : ∑' k, a (k + 1) ≤ ∑' k, a k := by
    have := hsum.sum_add_tsum_nat_add 1
    have h0 : a 0 = 0 := by simp [ha]
    rw [Finset.sum_range_one, h0, zero_add] at this
    linarith
  have hnn : 0 ≤ R ^ 3 * (M : ℝ) ^ (-1 / 2 : ℝ) := by positivity
  have hnn2 : 0 ≤ R ^ 4 / M := by positivity
  linarith

end NlsGge.Schur
