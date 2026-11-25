import NlsGge.Weights.LowerGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! Source NEW-F06 scalar tail prerequisites. Concrete spectral/H1 energy
realizations remain separate; this file assumes no target energy conclusion. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

lemma weight_tail_hasSum (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    HasSum (fun j : ℕ => weightTerm c r (j+2))
      (weight c r - coefficient c 0 - coefficient c 1*r^2) := by
  have hs := weightTerm_summable lower upper c hlower hbound hupper r
  have ht : Summable (fun j : ℕ => weightTerm c r (j+2)) :=
    hs.comp_injective (fun a b hab => Nat.add_right_cancel hab)
  have hw := (HasSum.sum_range_add (f := weightTerm c r) (k := 2) ht.hasSum).tsum_eq
  have hp : (∑ j ∈ Finset.range 2, weightTerm c r j) =
      coefficient c 0 + coefficient c 1*r^2 := by
    simp [Finset.sum_range_succ, Finset.sum_range_zero, weightTerm]
  change weight c r = _ at hw
  rw [hp] at hw
  have hv : (∑' j : ℕ, weightTerm c r (j+2)) =
      weight c r - coefficient c 0 - coefficient c 1*r^2 := by linarith [hw]
  exact hv ▸ ht.hasSum

end NlsGge.Weights

open Filter
namespace NlsGge.Weights

lemma weight_uniform_reserved_tail_growth (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ growth H₀ : ℝ, 0 < growth ∧ 0 ≤ H₀ ∧
      ∀ c : ℕ → ℝ, (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ H : ℝ, H₀ ≤ H →
        growth*Real.exp (growth*H^(1/8 : ℝ)) ≤
          weight c (H^(1/4 : ℝ)) - coefficient c 0 - coefficient c 1*Real.sqrt H := by
  obtain ⟨g, hg, hW⟩ := weight_uniform_lower_growth lower upper hlower hlower_upper
  have hu : 0 < upper := hlower.trans_le hlower_upper
  have hev : ∀ᶠ x : ℝ in atTop, upper*(1+x^4) ≤ (g/2)*Real.exp (g*x) := by
    have hlim := tendsto_exp_mul_div_rpow_atTop (4 : ℝ) g hg
    filter_upwards [hlim.eventually (eventually_ge_atTop (4*upper/g)),
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := by linarith
    have hx4 : 1 ≤ x^4 := by simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx1 4
    rw [Real.rpow_ofNat] at hx
    have hm := (le_div_iff₀ (pow_pos hx0 4)).mp hx
    have he : 2*upper*x^4 ≤ (g/2)*Real.exp (g*x) := by
      calc
        2*upper*x^4 = (g/2)*((4*upper/g)*x^4) := by field_simp [hg.ne'] <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
    calc
      upper*(1+x^4) ≤ upper*(2*x^4) := mul_le_mul_of_nonneg_left (by linarith) hu.le
      _ = 2*upper*x^4 := by ring
      _ ≤ _ := he
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  let Y : ℝ := max 4 X
  have hY4 : 4 ≤ Y := le_max_left _ _
  have hY0 : 0 ≤ Y := by linarith
  refine ⟨g/2, Y^8, by positivity, pow_nonneg hY0 8, ?_⟩
  intro c hbound hupper H hH
  have hH0 : 0 ≤ H := (pow_nonneg hY0 8).trans hH
  have hroot : (Y^8)^(1/8 : ℝ) = Y := by
    rw [← Real.rpow_natCast Y 8, ← Real.rpow_mul hY0]
    norm_num
  have hxY := Real.rpow_le_rpow (pow_nonneg hY0 8) hH (by norm_num : (0 : ℝ) ≤ 1/8)
  rw [hroot] at hxY
  have hx4 : 4 ≤ H^(1/8 : ℝ) := hY4.trans hxY
  have hx0 : 0 ≤ H^(1/8 : ℝ) := Real.rpow_nonneg hH0 _
  have harg : (H^(1/8 : ℝ))^2 = H^(1/4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hH0]
    congr 1
    norm_num
  have hsqrt : Real.sqrt (H^(1/4 : ℝ)) = H^(1/8 : ℝ) := by
    rw [← harg, Real.sqrt_sq hx0]
  have hrad : 16 ≤ H^(1/4 : ℝ) := by rw [← harg]; nlinarith
  have hlarge := hW c hbound hupper (H^(1/4 : ℝ)) hrad
  rw [hsqrt] at hlarge
  have hsub := hX (H^(1/8 : ℝ)) ((le_max_right 4 X).trans hxY)
  have hsH : Real.sqrt H = (H^(1/8 : ℝ))^4 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hH0]
    congr 1
    norm_num
  have hc0 : coefficient c 0 ≤ upper := by simpa [coefficient] using hupper 0
  have hc1 : coefficient c 1 ≤ upper := by simpa [coefficient] using hupper 1
  have hbeta : coefficient c 0 + coefficient c 1*Real.sqrt H ≤
      upper*(1+(H^(1/8 : ℝ))^4) := by
    rw [hsH]
    calc
      coefficient c 0 + coefficient c 1*(H^(1/8 : ℝ))^4 ≤ upper+upper*(H^(1/8 : ℝ))^4 :=
        add_le_add hc0 (mul_le_mul_of_nonneg_right hc1 (pow_nonneg hx0 _))
      _ = _ := by ring
  have htlarge : (g/2)*Real.exp (g*H^(1/8 : ℝ)) ≤
      weight c (H^(1/4 : ℝ)) - coefficient c 0 - coefficient c 1*Real.sqrt H := by
    nlinarith [hlarge, hsub, hbeta]
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (by linarith : g/2 ≤ g) hx0)) (by positivity)).trans htlarge

lemma weight_uniform_reserved_tail_norm_growth (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) (a : ℝ) (ha : 0 < a) :
    ∃ growth R₀ : ℝ, 0 < growth ∧ 1 ≤ R₀ ∧
      ∀ c : ℕ → ℝ, (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ R H : ℝ, R₀ ≤ R → a*R^2 ≤ H →
        growth*Real.exp (growth*R^(1/4 : ℝ)) ≤
          weight c (H^(1/4 : ℝ)) - coefficient c 0 - coefficient c 1*Real.sqrt H := by
  obtain ⟨g, H₀, hg, hH₀, htail⟩ := weight_uniform_reserved_tail_growth lower upper hlower hlower_upper
  let growth : ℝ := min g (g*a^(1/8 : ℝ))
  have hgrowth : 0 < growth := lt_min_iff.mpr ⟨hg, mul_pos hg (Real.rpow_pos_of_pos ha _)⟩
  refine ⟨growth, max 1 (Real.sqrt (H₀/a)), hgrowth, le_max_left _ _, ?_⟩
  intro c hbound hupper R H hR hH
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hR0 : 0 ≤ R := by linarith
  have hRroot : Real.sqrt (H₀/a) ≤ R := (le_max_right _ _).trans hR
  have hR2 := pow_le_pow_left₀ (Real.sqrt_nonneg (H₀/a)) hRroot 2
  rw [Real.sq_sqrt (div_nonneg hH₀ ha.le)] at hR2
  have hHthreshold : H₀ ≤ H := by
    have hb := (div_le_iff₀ ha).mp hR2
    nlinarith [hb, hH]
  have hH0 : 0 ≤ H := (mul_nonneg ha.le (sq_nonneg R)).trans hH
  have hm := Real.rpow_le_rpow (mul_nonneg ha.le (sq_nonneg R)) hH (by norm_num : (0 : ℝ) ≤ 1/8)
  have hpR : (R^2)^(1/8 : ℝ) = R^(1/4 : ℝ) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR0]
    congr 1
    norm_num
  rw [Real.mul_rpow ha.le (sq_nonneg R), hpR] at hm
  have he : growth*R^(1/4 : ℝ) ≤ g*H^(1/8 : ℝ) := by
    calc
      growth*R^(1/4 : ℝ) ≤ (g*a^(1/8 : ℝ))*R^(1/4 : ℝ) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hR0 _)
      _ = g*(a^(1/8 : ℝ)*R^(1/4 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm hg.le
  exact (mul_le_mul (min_le_left _ _) (Real.exp_le_exp.mpr he)
    (Real.exp_nonneg _) hg.le).trans (htail c hbound hupper H hHthreshold)

end NlsGge.Weights
