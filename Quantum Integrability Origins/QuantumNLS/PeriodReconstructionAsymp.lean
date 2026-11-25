import QuantumNLS.PeriodReconstructionCore

/-!
# PROP-006 `thm:B3-period-reconstruction`, the asymptotic argument (label_periods.tex:368-442)

Abstract form of the printed proof. Along the filter `atTop ×ˢ 𝓟 Γ` on `(k, z)` (i.e. uniformly for
`z ∈ Γ` as `k → ∞`), for roots `q k` of `N k → ∞` particles with coupling `c = κ/N`, assume
* a common root distance `d > 0` on `Γ`;
* `iκ(G_N − G) → 0` uniformly on `Γ`, `G_N = N⁻¹ Σ_j 1/(z − q_j)`;
* the background is differentiable on `Γ`, `D ≠ 0` near each point of `Γ`, and `|A|, |A⁻¹|, |e^{izL}|`
  are bounded and `|D|` bounded below on `Γ`.
Then **`rem_isBigO`**: `ℓ_N − log a_N + (iκ/N) e^{izL} a_N'/(a_N(a_N² − e^{izL})) = O(N^{-2})`
uniformly on `Γ` (eq:B3-log-reconstruction).

Steps (as printed): `ℓ_N = iκG_N + O(1/N)` (eq:B3-leading-log); `A_N → A`, `s_N → s`, `a_N → A`;
`log(A_N B_N) = c² Σ (z−q_j)^{-2} + O(N^{-2})` and `ic ℓ_N' = c² Σ (z−q_j)^{-2} + O(N^{-2})`
(eq:B3-product-correction), so `A_N B_N = 1 + ic ℓ_N' + O(N^{-2})` (eq:B3-product-expansion);
eq:B3-multiplier-residual gives `ε_N = O(1/N)`; `ℓ_N' = a_N'/a_N + O(1/N)`
(eq:B3-log-derivative-comparison; here by explicit derivative formulas and implicit differentiation of
the quadratic, instead of Cauchy estimates on nested neighbourhoods);
eq:B3-multiplier-first-correction; finally `log(A_N/a_N) = ε_N/a_N + O(N^{-2})` with the branches
identified because both logarithms converge to `iκG`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section

open Complex Filter Topology Asymptotics

namespace QuantumNLS.PeriodReconstructionAsymp

open QuantumNLS.PeriodReconstructionCore

/-! ## 1. Pointwise estimates for one configuration -/

section Pointwise

variable {N : ℕ}

lemma norm_Ic (c : ℝ) : ‖I * (c : ℂ)‖ = |c| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

lemma norm_u_le {c q d : ℝ} {z : ℂ} (hd : 0 < d) (hz : d ≤ ‖z - q‖) :
    ‖I * c / (z - q)‖ ≤ |c| / d := by
  rw [norm_div, norm_Ic]
  exact div_le_div_of_nonneg_left (abs_nonneg c) hd hz

lemma log_lin {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) : ‖log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
  have h := Complex.norm_log_one_add_sub_self_le (z := u) (by linarith)
  have h1 : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc ‖log (1 + u) - u‖ ≤ ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 := h
    _ ≤ ‖u‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖u‖ ^ 2 := by ring

lemma log_quad {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) : ‖log (1 + u) - (u - u ^ 2 / 2)‖ ≤ ‖u‖ ^ 3 := by
  have h := Complex.norm_log_sub_logTaylor_le 2 (z := u) (by linarith)
  have ht : Complex.logTaylor (2 + 1) u = u - u ^ 2 / 2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]; ring
  rw [ht] at h
  have h1 : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc _ ≤ ‖u‖ ^ (2 + 1) * (1 - ‖u‖)⁻¹ / ((2 : ℕ) + 1 : ℝ) := by exact_mod_cast h
    _ ≤ ‖u‖ ^ 3 * 2 / 3 := by push_cast; gcongr; norm_num
    _ ≤ ‖u‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg u) 3]

/-- eq:B3-leading-log: `‖ℓ_N − Σ ic/(z − q_j)‖ ≤ N (|c|/d)²`. -/
lemma ell_lin {c d : ℝ} {q : Fin N → ℝ} {z : ℂ} (hd : 0 < d) (hc : 2 * |c| ≤ d)
    (hz : ∀ j, d ≤ ‖z - q j‖) :
    ‖ellf c q z - ∑ j, I * c / (z - q j)‖ ≤ N * (|c| / d) ^ 2 := by
  unfold ellf
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ j, ‖I * c / (z - q j)‖ ≤ |c| / d := fun j => norm_u_le hd (hz j)
  have hh : |c| / d ≤ 1 / 2 := by rw [div_le_iff₀ hd]; linarith
  calc ∑ j, ‖log (1 + I * c / (z - q j)) - I * c / (z - q j)‖
      ≤ ∑ _j : Fin N, (|c| / d) ^ 2 := Finset.sum_le_sum fun j _ =>
        (log_lin ((hb j).trans hh)).trans (pow_le_pow_left₀ (norm_nonneg _) (hb j) 2)
    _ = N * (|c| / d) ^ 2 := by simp

/-- `‖ℓ_N + ℓ_B − c² Σ (z − q_j)^{-2}‖ ≤ 2N(|c|/d)³`. -/
lemma ell_pair {c d : ℝ} {q : Fin N → ℝ} {z : ℂ} (hd : 0 < d) (hc : 2 * |c| ≤ d)
    (hz : ∀ j, d ≤ ‖z - q j‖) :
    ‖ellf c q z + ellf (-c) q z - ∑ j, ((c : ℂ) ^ 2 / (z - q j) ^ 2)‖ ≤
      2 * N * (|c| / d) ^ 3 := by
  unfold ellf
  have hb : ∀ j, ‖I * c / (z - q j)‖ ≤ |c| / d := fun j => norm_u_le hd (hz j)
  have hh : |c| / d ≤ 1 / 2 := by rw [div_le_iff₀ hd]; linarith
  have key : ∀ j, ‖log (1 + I * c / (z - q j)) + log (1 + I * ((-c : ℝ) : ℂ) / (z - q j)) -
      (c : ℂ) ^ 2 / (z - q j) ^ 2‖ ≤ 2 * (|c| / d) ^ 3 := by
    intro j
    set u := I * c / (z - q j)
    have hu' : I * ((-c : ℝ) : ℂ) / (z - q j) = -u := by simp only [u]; push_cast; ring
    have hu2 : (c : ℂ) ^ 2 / (z - q j) ^ 2 = -u ^ 2 := by
      simp only [u]; rw [div_pow, mul_pow, I_sq]; ring
    rw [hu', hu2]
    have h1 := log_quad ((hb j).trans hh)
    have h2 := log_quad (u := -u) (by rw [norm_neg]; exact (hb j).trans hh)
    rw [norm_neg] at h2
    have e : log (1 + u) + log (1 + -u) - -u ^ 2 =
        (log (1 + u) - (u - u ^ 2 / 2)) + (log (1 + -u) - (-u - (-u) ^ 2 / 2)) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h3 : ‖u‖ ^ 3 ≤ (|c| / d) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hb j) 3
    linarith
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _j : Fin N, 2 * (|c| / d) ^ 3 := Finset.sum_le_sum fun j _ => key j
    _ = 2 * N * (|c| / d) ^ 3 := by simp; ring

lemma sumsq_bound {c d : ℝ} {q : Fin N → ℝ} {z : ℂ} (hd : 0 < d) (hz : ∀ j, d ≤ ‖z - q j‖) :
    ‖∑ j, ((c : ℂ) ^ 2 / (z - q j) ^ 2)‖ ≤ N * (|c| / d) ^ 2 := by
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _j : Fin N, (|c| / d) ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_pow]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hd.le (hz j) 2)
    _ = N * (|c| / d) ^ 2 := by simp

lemma norm_shift_ge {c q d : ℝ} {z : ℂ} (hc : 2 * |c| ≤ d) (hz : d ≤ ‖z - q‖) :
    d / 2 ≤ ‖z - q + I * c‖ := by
  have h4 := norm_sub_norm_le (z - q) (-(I * c))
  rw [sub_neg_eq_add, norm_neg, norm_Ic] at h4
  linarith

lemma term_bound {c d : ℝ} {w a : ℂ} (hd : 0 < d) (hw : d ≤ ‖w‖) (ha : d / 2 ≤ ‖a‖) :
    ‖-(I * c) / (w * a)‖ ≤ 2 * |c| / d ^ 2 := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hd hw
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le (by positivity) ha
  simp only [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  rw [div_le_div_iff₀ (mul_pos hw0 ha0) (by positivity)]
  have : d * (d / 2) ≤ ‖w‖ * ‖a‖ := mul_le_mul hw ha (by positivity) hw0.le
  nlinarith [abs_nonneg c]

/-- `‖ℓ_N'‖ ≤ 2N|c|/d²`. -/
lemma dell_bound {c d : ℝ} {q : Fin N → ℝ} {z : ℂ} (hd : 0 < d) (hc : 2 * |c| ≤ d)
    (hz : ∀ j, d ≤ ‖z - q j‖) : ‖dellf c q z‖ ≤ N * (2 * |c| / d ^ 2) := by
  unfold dellf
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _j : Fin N, 2 * |c| / d ^ 2 :=
        Finset.sum_le_sum fun j _ => term_bound hd (hz j) (norm_shift_ge hc (hz j))
    _ = N * (2 * |c| / d ^ 2) := by simp

/-- eq:B3-product-correction (second line): `‖ic ℓ_N' − c² Σ (z−q_j)^{-2}‖ ≤ 2N|c|³/d³`. -/
lemma Icdell_sub {c d : ℝ} {q : Fin N → ℝ} {z : ℂ} (hd : 0 < d) (hc : 2 * |c| ≤ d)
    (hz : ∀ j, d ≤ ‖z - q j‖) :
    ‖I * c * dellf c q z - ∑ j, ((c : ℂ) ^ 2 / (z - q j) ^ 2)‖ ≤ N * (2 * |c| ^ 3 / d ^ 3) := by
  unfold dellf
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _j : Fin N, 2 * |c| ^ 3 / d ^ 3 := Finset.sum_le_sum fun j _ => by
        have hw := hz j
        have ha := norm_shift_ge hc (hz j)
        have hw0' : 0 < ‖z - q j‖ := lt_of_lt_of_le hd hw
        have ha0' : 0 < ‖z - q j + I * c‖ := lt_of_lt_of_le (by positivity) ha
        have hw0 : z - q j ≠ 0 := norm_pos_iff.1 hw0'
        have ha0 : z - q j + I * c ≠ 0 := norm_pos_iff.1 ha0'
        have e : I * c * (-(I * c) / ((z - q j) * (z - q j + I * c))) -
            (c : ℂ) ^ 2 / (z - q j) ^ 2
            = -(I * c) * (c : ℂ) ^ 2 / ((z - q j) ^ 2 * (z - q j + I * c)) := by
          field_simp; ring_nf; rw [I_sq]; ring
        rw [e]
        simp only [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : d ^ 2 * (d / 2) ≤ ‖z - q j‖ ^ 2 * ‖z - q j + I * c‖ :=
          mul_le_mul (pow_le_pow_left₀ hd.le hw 2) ha (by positivity) (by positivity)
        have h2 : 0 ≤ |c| ^ 3 := pow_nonneg (abs_nonneg c) 3
        have e2 : |c| * |c| ^ 2 = |c| ^ 3 := by ring
        rw [e2]
        nlinarith
    _ = N * (2 * |c| ^ 3 / d ^ 3) := by simp

lemma norm_shift_ge' {c q d : ℝ} {z : ℂ} (hc : 2 * |c| ≤ d) (hz : d ≤ ‖z - q‖) :
    d / 2 ≤ ‖z - q - I * c‖ := by
  have h4 := norm_sub_norm_le (z - q) (I * c)
  rw [norm_Ic] at h4
  linarith

lemma pair_term {c : ℝ} {w : ℂ} (hw0 : w ≠ 0) (ha0 : w + I * c ≠ 0) (hb0 : w - I * c ≠ 0) :
    -(I * c) / (w * (w + I * c)) + -(I * ((-c : ℝ) : ℂ)) / (w * (w + I * ((-c : ℝ) : ℂ))) =
      -2 * (c : ℂ) ^ 2 / (w * (w + I * c) * (w - I * c)) := by
  have e1 : w + I * ((-c : ℝ) : ℂ) = w - I * c := by push_cast; ring
  have e2 : -(I * ((-c : ℝ) : ℂ)) = I * c := by push_cast; ring
  rw [e1, e2]
  rw [div_add_div _ _ (mul_ne_zero hw0 ha0) (mul_ne_zero hw0 hb0), div_eq_div_iff
    (mul_ne_zero (mul_ne_zero hw0 ha0) (mul_ne_zero hw0 hb0))
    (mul_ne_zero (mul_ne_zero hw0 ha0) hb0)]
  ring_nf
  simp only [Complex.I_pow_four, I_sq]
  ring

/-- `‖ℓ_N' + ℓ_B'‖ ≤ 8N c²/d³`. -/
lemma dell_pair {c d : ℝ} {q : Fin N → ℝ} {z : ℂ} (hd : 0 < d) (hc : 2 * |c| ≤ d)
    (hz : ∀ j, d ≤ ‖z - q j‖) : ‖dellf c q z + dellf (-c) q z‖ ≤ N * (8 * |c| ^ 2 / d ^ 3) := by
  unfold dellf
  rw [← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _j : Fin N, 8 * |c| ^ 2 / d ^ 3 := Finset.sum_le_sum fun j _ => by
        have hw := hz j
        have ha := norm_shift_ge hc (hz j)
        have hb := norm_shift_ge' hc (hz j)
        have hw0' : 0 < ‖z - q j‖ := lt_of_lt_of_le hd hw
        have ha0' : 0 < ‖z - q j + I * c‖ := lt_of_lt_of_le (by positivity) ha
        have hb0' : 0 < ‖z - q j - I * c‖ := lt_of_lt_of_le (by positivity) hb
        rw [pair_term (norm_pos_iff.1 hw0') (norm_pos_iff.1 ha0') (norm_pos_iff.1 hb0')]
        simp only [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_ofNat]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : d * (d / 2) * (d / 2) ≤
            ‖z - q j‖ * ‖z - q j + I * c‖ * ‖z - q j - I * c‖ :=
          mul_le_mul (mul_le_mul hw ha (by positivity) hw0'.le) hb (by positivity) (by positivity)
        have h2 : 0 ≤ |c| ^ 2 := pow_nonneg (abs_nonneg c) 2
        nlinarith
    _ = N * (8 * |c| ^ 2 / d ^ 3) := by simp

end Pointwise

end QuantumNLS.PeriodReconstructionAsymp

#print axioms QuantumNLS.PeriodReconstructionAsymp.ell_lin
#print axioms QuantumNLS.PeriodReconstructionAsymp.ell_pair
#print axioms QuantumNLS.PeriodReconstructionAsymp.Icdell_sub
#print axioms QuantumNLS.PeriodReconstructionAsymp.dell_pair
