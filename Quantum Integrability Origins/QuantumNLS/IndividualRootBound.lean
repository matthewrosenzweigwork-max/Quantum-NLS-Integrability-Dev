import Mathlib
import QuantumNLS.ConvolutionComparison
import QuantumNLS.OnShellSpacing

/-!
# REG-002: individual root-label bound (`CC:individual-root-bound`)

Source: `source/chapters/regularity/root_confinement.tex`.
* lines 59--80: the statement. `N ≥ 1`, `L > 0`, `c > 0`, `q_1 < ⋯ < q_N`, `p_1 ≤ ⋯ ≤ p_N` real, and
  `L(q_j − p_j) = 2 Σ_{k≠j} arctan(c/(q_j−q_k))` (principal arctan). Conclusion
  `max_j |q_j − p_j| ≤ 2√(c(N−1)/L)`. The in-particular clause (`CC:mean-field-root-bound`) is
  `|q_j − 2π n_j/L| ≤ 2√((κ/L)(1 − 1/N))` for an actual repulsive Bethe configuration with `c = κ/N`.
* lines 82--140: the printed proof, reproduced in §§1--6 below. It applies `CC:convolution-comparison`
  (REG-001, `ConvolutionComparison.convolution_comparison_bound`), which is imported read-only.

Read-only imports: `QuantumNLS.ConvolutionComparison` (REG-001, accepted, frozen) and
`QuantumNLS.OnShellSpacing` (R-2EF16A1A, supplies `OrderedOnShell` and the accepted-roots bridge
`ordered_onshell_iff_roots`; off-scope, used only as a read-only definition/bridge source).
No frozen file is edited.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace QuantumNLS.IndividualRootBound

/-! ## 1. Exponential means and pair integrals -/

/-- The mean `M(t) = N⁻¹ Σ_j e^{t d_j}` (source line 84). -/
def Mexp {N : ℕ} (d : Fin N → ℝ) (t : ℝ) : ℝ := (N : ℝ)⁻¹ * ∑ j, Real.exp (t * d j)

/-- Its derivative `N⁻¹ Σ_j d_j e^{t d_j}`. -/
def Mexp' {N : ℕ} (d : Fin N → ℝ) (t : ℝ) : ℝ := (N : ℝ)⁻¹ * ∑ j, d j * Real.exp (t * d j)

/-- `I(a,b) = ∫_0^t e^{s a + (t−s) b} ds` (the pair integral of source line 96). -/
def pairInt (t a b : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, Real.exp (s * a + (t - s) * b)

/-- `Ā_{jk} = arctan(c/(q_j−q_k))` for `j ≠ k` and `0` on the diagonal. -/
def Ahat {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (j k : Fin N) : ℝ :=
  if j = k then 0 else Real.arctan (c / (q j - q k))

theorem continuous_Mexp {N : ℕ} (d : Fin N → ℝ) : Continuous (Mexp d) := by
  unfold Mexp
  fun_prop

theorem hasDerivAt_Mexp {N : ℕ} (d : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (Mexp d) (Mexp' d t) t := by
  unfold Mexp Mexp'
  apply HasDerivAt.const_mul
  have hj : ∀ j : Fin N, HasDerivAt (fun s : ℝ => Real.exp (s * d j))
      (d j * Real.exp (t * d j)) t := by
    intro j
    have h := ((hasDerivAt_id' t).mul_const (d j)).exp
    convert h using 1
    ring
  exact HasDerivAt.fun_sum (fun j _ => hj j)

theorem Mexp_zero {N : ℕ} (hN : 1 ≤ N) (d : Fin N → ℝ) : Mexp d 0 = 1 := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold Mexp
  simp only [zero_mul, Real.exp_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hNne

theorem Mexp_pos {N : ℕ} (hN : 1 ≤ N) (d : Fin N → ℝ) (t : ℝ) : 0 < Mexp d t := by
  unfold Mexp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact mul_pos (inv_pos.2 hN0)
    (Finset.sum_pos (fun j _ => Real.exp_pos _) (Finset.univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩))

theorem pairInt_symm (t a b : ℝ) : pairInt t a b = pairInt t b a := by
  unfold pairInt
  have h := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => Real.exp (u * b + (t - u) * a)) (a := (0 : ℝ)) (b := t) t
  simp only [sub_self, sub_zero] at h
  rw [← h]
  congr 1
  funext s
  congr 1
  ring

theorem pairInt_eq {t a b : ℝ} (hab : a ≠ b) :
    pairInt t a b = (Real.exp (t * a) - Real.exp (t * b)) / (a - b) := by
  unfold pairInt
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ => Real.exp (s * a + (t - s) * b) / (a - b))
        (Real.exp (x * a + (t - x) * b)) x := by
    intro x _
    have hlin : HasDerivAt (fun s : ℝ => s * a + (t - s) * b) (a - b) x := by
      have h1 := ((hasDerivAt_id' x).mul_const a).add
        (((hasDerivAt_const x t).sub (hasDerivAt_id' x)).mul_const b)
      convert h1 using 1
      ring
    have h2 := (hlin.exp).div_const (a - b)
    convert h2 using 1
    field_simp
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp (s * a + (t - s) * b)) MeasureTheory.volume
      0 t :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp only [sub_self, zero_mul, add_zero, zero_add, sub_zero]
  rw [div_sub_div_same]

theorem pairInt_self (t a : ℝ) : pairInt t a a = t * Real.exp (t * a) := by
  unfold pairInt
  have h : ∀ s : ℝ, Real.exp (s * a + (t - s) * a) = Real.exp (t * a) := fun s => by
    congr 1
    ring
  simp only [h, intervalIntegral.integral_const, sub_zero, smul_eq_mul]

theorem pairInt_nonneg {t : ℝ} (ht : 0 ≤ t) (a b : ℝ) : 0 ≤ pairInt t a b :=
  intervalIntegral.integral_nonneg ht (fun s _ => (Real.exp_pos _).le)

/-- Pair-term bound (source lines 92--101): for `a − b ≤ x`, `x > 0`,
`(e^{ta} − e^{tb}) arctan(c/x) ≤ c I(a,b)`. -/
theorem pair_term_le {c t a b x : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hx : 0 < x) (hab : a - b ≤ x) :
    (Real.exp (t * a) - Real.exp (t * b)) * Real.arctan (c / x) ≤ c * pairInt t a b := by
  rcases le_or_gt a b with h | h
  · have h1 : Real.exp (t * a) ≤ Real.exp (t * b) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h ht)
    have h2 : 0 ≤ Real.arctan (c / x) := Real.arctan_nonneg.2 (div_nonneg hc.le hx.le)
    have h3 := mul_le_mul_of_nonneg_right (sub_nonpos.2 h1) h2
    have h4 : 0 ≤ c * pairInt t a b := mul_nonneg hc.le (pairInt_nonneg ht a b)
    linarith
  · have hab' : 0 < a - b := by linarith
    have hcx : 0 ≤ c / x := div_nonneg hc.le hx.le
    have h1 : Real.arctan (c / x) ≤ c / x := Real.arctan_le_self hcx
    have h2 : c / x ≤ c / (a - b) := div_le_div_of_nonneg_left hc.le hab' hab
    have h3 : 0 ≤ Real.exp (t * a) - Real.exp (t * b) :=
      sub_nonneg.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h.le ht))
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) h3
    have h5 : (Real.exp (t * a) - Real.exp (t * b)) * (c / (a - b)) =
        c * pairInt t a b := by
      rw [pairInt_eq (sub_pos.1 hab').ne']
      ring
    linarith

/-- The per-pair estimate with the diagonal excluded (source lines 92--101 with `j = k` handled by
`arctan 0 = 0`). -/
theorem term_le {N : ℕ} {c : ℝ} (hc : 0 < c) (q d : Fin N → ℝ) (hq : StrictMono q)
    (hdq : ∀ j k : Fin N, k < j → d j - d k ≤ q j - q k) {t : ℝ} (ht : 0 ≤ t) (j k : Fin N) :
    (Real.exp (t * d j) - Real.exp (t * d k)) * Ahat c q j k ≤
      c * (pairInt t (d j) (d k) - if j = k then pairInt t (d j) (d j) else 0) := by
  by_cases hjk : j = k
  · subst hjk
    simp [Ahat]
  · have hA : Ahat c q j k = Real.arctan (c / (q j - q k)) := by
      unfold Ahat
      exact if_neg hjk
    have key : ∀ j k : Fin N, k < j →
        (Real.exp (t * d j) - Real.exp (t * d k)) * Real.arctan (c / (q j - q k)) ≤
          c * pairInt t (d j) (d k) := by
      intro j k hkj
      exact pair_term_le hc ht (sub_pos.2 (hq hkj)) (hdq j k hkj)
    simp only [if_neg hjk, sub_zero, hA]
    rcases lt_or_gt_of_ne hjk with h | h
    · have h1 := key k j h
      have e : (Real.exp (t * d j) - Real.exp (t * d k)) * Real.arctan (c / (q j - q k)) =
          (Real.exp (t * d k) - Real.exp (t * d j)) * Real.arctan (c / (q k - q j)) := by
        rw [show c / (q k - q j) = -(c / (q j - q k)) by
          rw [show q k - q j = -(q j - q k) by ring, div_neg], Real.arctan_neg]
        ring
      rw [e, pairInt_symm t (d j) (d k)]
      exact h1
    · exact key j k h

/-! ## 2. Sums over pairs -/

theorem Ahat_anti {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (j k : Fin N) :
    Ahat c q k j = -Ahat c q j k := by
  unfold Ahat
  by_cases h : j = k
  · subst h
    simp
  · have h' : k ≠ j := fun e => h e.symm
    rw [if_neg h, if_neg h', show q k - q j = -(q j - q k) by ring, div_neg, Real.arctan_neg]

theorem sum_Ahat_eq {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (j : Fin N) :
    ∑ k, Ahat c q j k = ∑ k ∈ Finset.univ.erase j, Real.arctan (c / (q j - q k)) := by
  rw [← Finset.sum_erase Finset.univ (f := Ahat c q j) (a := j) (by simp [Ahat])]
  exact Finset.sum_congr rfl (fun k hk => by
    unfold Ahat
    rw [if_neg (Finset.ne_of_mem_erase hk).symm])

theorem sum_pair_identity {N : ℕ} (f g : Fin N → ℝ) :
    ∑ j, ∑ k, (f j - f k) * (g j - g k) =
      2 * ((N : ℝ) * ∑ j, f j * g j) - 2 * ((∑ j, f j) * (∑ k, g k)) := by
  have e : ∀ j k, (f j - f k) * (g j - g k) =
      (f j * g j + f k * g k) - (f j * g k + f k * g j) := fun j k => by ring
  have h1 : ∑ j, ∑ k, (f j * g j + f k * g k) = 2 * ((N : ℝ) * ∑ j, f j * g j) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have c1 : ∑ j, ∑ k, f j * g k = (∑ j, f j) * (∑ k, g k) := (Finset.sum_mul_sum _ _ _ _).symm
  have c2 : ∑ j, ∑ k, f k * g j = (∑ j, f j) * (∑ k, g k) := by
    rw [Finset.sum_comm, Finset.sum_mul_sum]
  have h2 : ∑ j, ∑ k, (f j * g k + f k * g j) = 2 * ((∑ j, f j) * (∑ k, g k)) := by
    simp only [Finset.sum_add_distrib]
    rw [c1, c2]
    ring
  calc ∑ j, ∑ k, (f j - f k) * (g j - g k)
      = ∑ j, ∑ k, ((f j * g j + f k * g k) - (f j * g k + f k * g j)) :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => e j k))
    _ = ∑ j, ∑ k, (f j * g j + f k * g k) - ∑ j, ∑ k, (f j * g k + f k * g j) := by
        simp only [Finset.sum_sub_distrib]
    _ = _ := by rw [h1, h2]

theorem sum_pair_nonneg {N : ℕ} (f g : Fin N → ℝ) (hfg : ∀ j k, 0 ≤ (f j - f k) * (g j - g k)) :
    0 ≤ ∑ j, ∑ k, (f j - f k) * (g j - g k) :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hfg j k

/-- Covariance step (source lines 113--121): `M(s)M(t−s) ≤ M(t)` for `0 ≤ s ≤ t`. -/
theorem mean_cov_le {N : ℕ} (hN : 1 ≤ N) (d : Fin N → ℝ) {s t : ℝ} (hs : 0 ≤ s)
    (hu : 0 ≤ t - s) : Mexp d s * Mexp d (t - s) ≤ Mexp d t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmono : ∀ j k : Fin N,
      0 ≤ (Real.exp (s * d j) - Real.exp (s * d k)) * (Real.exp ((t - s) * d j) - Real.exp ((t - s) * d k)) := by
    intro j k
    rcases le_total (d j) (d k) with h | h
    · have h1 : Real.exp (s * d j) ≤ Real.exp (s * d k) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hs)
      have h2 : Real.exp ((t - s) * d j) ≤ Real.exp ((t - s) * d k) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hu)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have h1 : Real.exp (s * d k) ≤ Real.exp (s * d j) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hs)
      have h2 : Real.exp ((t - s) * d k) ≤ Real.exp ((t - s) * d j) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hu)
      exact mul_nonneg (by linarith) (by linarith)
  have hid := sum_pair_nonneg (fun j => Real.exp (s * d j))
    (fun j => Real.exp ((t - s) * d j)) hmono
  rw [sum_pair_identity] at hid
  have hH : ∑ j, Real.exp (s * d j) * Real.exp ((t - s) * d j) = ∑ j, Real.exp (t * d j) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hH] at hid
  unfold Mexp
  have key : (∑ j, Real.exp (s * d j)) * (∑ j, Real.exp ((t - s) * d j)) ≤
      (N : ℝ) * ∑ j, Real.exp (t * d j) := by linarith
  have hNinv : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.2 hN0
  calc ((N : ℝ)⁻¹ * ∑ j, Real.exp (s * d j)) * ((N : ℝ)⁻¹ * ∑ j, Real.exp ((t - s) * d j))
      = (N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ((∑ j, Real.exp (s * d j)) * (∑ j, Real.exp ((t - s) * d j)))) := by
        ring
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ((N : ℝ) * ∑ j, Real.exp (t * d j))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hNinv.le) hNinv.le
    _ = (N : ℝ)⁻¹ * ∑ j, Real.exp (t * d j) := by
        field_simp

/-- `∫_0^t M(s)M(t−s) ds ≤ t M(t)`. -/
theorem int_conv_le {N : ℕ} (hN : 1 ≤ N) (d : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s) ≤ t * Mexp d t := by
  have hc1 : Continuous fun s : ℝ => Mexp d s * Mexp d (t - s) :=
    (continuous_Mexp d).mul ((continuous_Mexp d).comp (continuous_const.sub continuous_id))
  have h := intervalIntegral.integral_mono_on ht
    (hc1.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    (intervalIntegrable_const (μ := MeasureTheory.volume) (c := Mexp d t))
    (fun s hs => mean_cov_le hN d hs.1 (by linarith [hs.2]))
  simpa [intervalIntegral.integral_const, smul_eq_mul] using h

/-! ## 3. The core differential inequality (source lines 84--112) -/

theorem sum_pairInt_eq {N : ℕ} (hN : 1 ≤ N) (d : Fin N → ℝ) {t : ℝ} :
    ∑ j, ∑ k, pairInt t (d j) (d k) =
      (N : ℝ) ^ 2 * ∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hcont : ∀ j k : Fin N, Continuous fun s : ℝ =>
      Real.exp (s * d j + (t - s) * d k) := fun j k => by fun_prop
  calc ∑ j, ∑ k, pairInt t (d j) (d k)
      = ∑ j, ∫ s in (0 : ℝ)..t, ∑ k, Real.exp (s * d j + (t - s) * d k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        unfold pairInt
        exact (intervalIntegral.integral_finsetSum (fun k _ =>
          (hcont j k).intervalIntegrable (μ := MeasureTheory.volume) _ _)).symm
    _ = ∫ s in (0 : ℝ)..t, ∑ j, ∑ k, Real.exp (s * d j + (t - s) * d k) := by
        exact (intervalIntegral.integral_finsetSum (fun j _ => by
          exact (Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by fun_prop) _ _))).symm
    _ = ∫ s in (0 : ℝ)..t, (N : ℝ) ^ 2 * (Mexp d s * Mexp d (t - s)) := by
        refine intervalIntegral.integral_congr (fun s _ => ?_)
        simp only [Real.exp_add]
        unfold Mexp
        rw [← Finset.sum_mul_sum]
        field_simp
    _ = (N : ℝ) ^ 2 * ∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s) :=
        intervalIntegral.integral_const_mul _ _

theorem core_ineq {N : ℕ} (hN : 1 ≤ N) {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (q d : Fin N → ℝ)
    (hq : StrictMono q) (hdq : ∀ j k : Fin N, k < j → d j - d k ≤ q j - q k)
    (hE : ∀ j, L * d j = 2 * ∑ k, Ahat c q j k) {t : ℝ} (ht : 0 ≤ t) :
    L * Mexp' d t ≤
      c * ((N : ℝ) * (∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s)) - t * Mexp d t) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  -- Step 1: L M'(t) = N⁻¹ Σ_j e_j (L d_j), with e_j = e^{t d_j}.
  have s1 : L * Mexp' d t = (N : ℝ)⁻¹ *
      ∑ j, Real.exp (t * d j) * (2 * ∑ k, Ahat c q j k) := by
    unfold Mexp'
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hE j]
    ring
  -- Step 2: symmetrization of the pair sum (Ā antisymmetric).
  have hanti : ∑ j, ∑ k, Real.exp (t * d k) * Ahat c q j k =
      -∑ j, ∑ k, Real.exp (t * d j) * Ahat c q j k := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Ahat_anti]
    ring
  have lhs_eq : ∑ j, Real.exp (t * d j) * (2 * ∑ k, Ahat c q j k) =
      ∑ j, ∑ k, 2 * (Real.exp (t * d j) * Ahat c q j k) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
  have s2 : ∑ j, Real.exp (t * d j) * (2 * ∑ k, Ahat c q j k) =
      ∑ j, ∑ k, (Real.exp (t * d j) - Real.exp (t * d k)) * Ahat c q j k := by
    rw [lhs_eq]
    calc ∑ j, ∑ k, 2 * (Real.exp (t * d j) * Ahat c q j k)
        = ∑ j, ∑ k, Real.exp (t * d j) * Ahat c q j k + ∑ j, ∑ k, Real.exp (t * d j) * Ahat c q j k := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun k _ => by ring)
      _ = ∑ j, ∑ k, Real.exp (t * d j) * Ahat c q j k - ∑ j, ∑ k, Real.exp (t * d k) * Ahat c q j k := by
          rw [hanti]
          ring
      _ = ∑ j, ∑ k, (Real.exp (t * d j) - Real.exp (t * d k)) * Ahat c q j k := by
          simp only [sub_mul, Finset.sum_sub_distrib]
  -- Step 3: termwise bound.
  have s3 : ∑ j, ∑ k, (Real.exp (t * d j) - Real.exp (t * d k)) * Ahat c q j k ≤
      ∑ j, ∑ k, c * (pairInt t (d j) (d k) - if j = k then pairInt t (d j) (d j) else 0) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => term_le hc q d hq hdq ht j k
  -- Step 4: the diagonal subtraction.
  have s4 : ∑ j, ∑ k, c * (pairInt t (d j) (d k) - if j = k then pairInt t (d j) (d j) else 0) =
      c * (∑ j, ∑ k, pairInt t (d j) (d k) - ∑ j, pairInt t (d j) (d j)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum]
  -- Step 5: the diagonal integrals.
  have s6 : ∑ j, pairInt t (d j) (d j) = t * ((N : ℝ) * Mexp d t) := by
    have h : ∀ j, pairInt t (d j) (d j) = t * Real.exp (t * d j) := fun j => pairInt_self t (d j)
    simp only [h]
    rw [← Finset.mul_sum]
    congr 1
    unfold Mexp
    field_simp
  rw [s1, s2]
  calc (N : ℝ)⁻¹ * ∑ j, ∑ k, (Real.exp (t * d j) - Real.exp (t * d k)) * Ahat c q j k
      ≤ (N : ℝ)⁻¹ * ∑ j, ∑ k, c * (pairInt t (d j) (d k) - if j = k then pairInt t (d j) (d j) else 0) :=
        mul_le_mul_of_nonneg_left s3 (inv_nonneg.2 (by positivity))
    _ = (N : ℝ)⁻¹ * (c * ((N : ℝ) ^ 2 * (∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s)) -
          t * ((N : ℝ) * Mexp d t))) := by
        rw [s4, sum_pairInt_eq hN d, s6]
    _ = c * ((N : ℝ) * (∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s)) - t * Mexp d t) := by
        field_simp
        try ring

/-! ## 4. The one-sided bound (source lines 126--129) -/

/-- One-sided bound: `d_j ≤ 2√(c(N−1)/L)` for every `j`, via REG-001. -/
theorem upper_bound_aux {N : ℕ} (hN : 1 ≤ N) {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (q d : Fin N → ℝ) (hq : StrictMono q) (hdq : ∀ j k : Fin N, k < j → d j - d k ≤ q j - q k)
    (hE : ∀ j, L * d j = 2 * ∑ k, Ahat c q j k) (j : Fin N) :
    d j ≤ 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set a : ℝ := c * ((N : ℝ) - 1) / L with ha_def
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hc.le hN1) hL.le
  have hineq : ∀ t, 0 < t → Mexp' d t ≤ a * ∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s) := by
    intro t ht
    have hcore := core_ineq hN hc hL q d hq hdq hE ht.le
    have hconv := int_conv_le hN d ht.le
    have hle : (N : ℝ) * (∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s)) - t * Mexp d t ≤
        ((N : ℝ) - 1) * ∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s) := by
      linarith
    have h2 : L * Mexp' d t ≤ L * (a * ∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s)) := by
      have e : L * (a * ∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s)) =
          c * (((N : ℝ) - 1) * ∫ s in (0 : ℝ)..t, Mexp d s * Mexp d (t - s)) := by
        rw [ha_def]
        field_simp
      rw [e]
      exact hcore.trans (mul_le_mul_of_nonneg_left hle hc.le)
    exact le_of_mul_le_mul_left h2 hL
  have hbound := QuantumNLS.ConvolutionComparison.convolution_comparison_bound a ha (Mexp d) (Mexp' d)
    (continuous_Mexp d).continuousOn (Mexp_zero hN d) (fun t _ => Mexp_pos hN d t)
    (fun t _ => hasDerivAt_Mexp d t) hineq
  by_contra hcon
  push_neg at hcon
  have hδ : 0 < d j - 2 * Real.sqrt a := by linarith
  have htpos : 0 < (N : ℝ) / (d j - 2 * Real.sqrt a) := div_pos hN0 hδ
  have hMt := hbound _ htpos.le
  have hsingle : Real.exp ((N : ℝ) / (d j - 2 * Real.sqrt a) * d j) ≤
      (N : ℝ) * Mexp d ((N : ℝ) / (d j - 2 * Real.sqrt a)) := by
    unfold Mexp
    rw [← mul_assoc, mul_inv_cancel₀ hN0.ne', one_mul]
    exact Finset.single_le_sum (f := fun k => Real.exp ((N : ℝ) / (d j - 2 * Real.sqrt a) * d k))
      (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ j)
  set t : ℝ := (N : ℝ) / (d j - 2 * Real.sqrt a) with ht_def
  have hsplit : Real.exp (t * d j) = Real.exp (t * (d j - 2 * Real.sqrt a)) *
      Real.exp (2 * Real.sqrt a * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpos2 : 0 < Real.exp (2 * Real.sqrt a * t) := Real.exp_pos _
  have hkey : Real.exp (t * (d j - 2 * Real.sqrt a)) ≤ N := by
    have h3 : Real.exp (t * (d j - 2 * Real.sqrt a)) * Real.exp (2 * Real.sqrt a * t) ≤
        (N : ℝ) * Real.exp (2 * Real.sqrt a * t) := by
      rw [← hsplit]
      calc Real.exp (t * d j) ≤ (N : ℝ) * Mexp d t := hsingle
        _ ≤ (N : ℝ) * Real.exp (2 * Real.sqrt a * t) := mul_le_mul_of_nonneg_left hMt hN0.le
    exact le_of_mul_le_mul_right h3 hpos2
  have htδ : t * (d j - 2 * Real.sqrt a) = N := by
    rw [ht_def]
    field_simp
  rw [htδ] at hkey
  have := Real.add_one_le_exp (N : ℝ)
  linarith

/-! ## 5. Reflection for the lower bound (source lines 131--137) -/

theorem reflect_Ahat {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (j k : Fin N) :
    Ahat c (fun i => -q (Fin.rev i)) j k = -Ahat c q (Fin.rev j) (Fin.rev k) := by
  unfold Ahat
  by_cases h : j = k
  · subst h
    simp
  · have h' : Fin.rev j ≠ Fin.rev k := fun e => h (Fin.rev_injective e)
    rw [if_neg h, if_neg h']
    rw [show -q (Fin.rev j) - -q (Fin.rev k) = -(q (Fin.rev j) - q (Fin.rev k)) by ring, div_neg,
      Real.arctan_neg]

/-! ## 6. Main estimate (`CC:individual-root-bound`) -/

/-- **REG-002 (`CC:individual-root-bound`).** For `N ≥ 1`, `L > 0`, `c > 0`, strictly ordered `q`,
nondecreasing `p`, and the principal-arctan Bethe relation `L(q_j − p_j) = 2 Σ_{k≠j} arctan(c/(q_j−q_k))`,
every displacement satisfies `|q_j − p_j| ≤ 2√(c(N−1)/L)` (so the maximum does too). -/
theorem individual_root_bound {N : ℕ} (hN : 1 ≤ N) {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (q p : Fin N → ℝ) (hq : StrictMono q) (hp : Monotone p)
    (hE : ∀ j, L * (q j - p j) = 2 * ∑ k ∈ Finset.univ.erase j, Real.arctan (c / (q j - q k)))
    (j : Fin N) :
    |q j - p j| ≤ 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) := by
  have hE' : ∀ j, L * (q j - p j) = 2 * ∑ k, Ahat c q j k := by
    intro j
    rw [sum_Ahat_eq]
    exact hE j
  -- upper bound
  have hdq : ∀ j k : Fin N, k < j → (q j - p j) - (q k - p k) ≤ q j - q k := by
    intro j k hkj
    have := hp hkj.le
    linarith
  have up := upper_bound_aux hN hc hL q (fun i => q i - p i) hq hdq hE' j
  -- lower bound: reflected arrays q̃_i = −q_{rev i}, p̃_i = −p_{rev i}
  have hqr : StrictMono (fun i => -q (Fin.rev i)) := by
    intro i k hik
    have := hq (Fin.rev_lt_rev.2 hik)
    simp only
    linarith
  have hpr : Monotone (fun i => -p (Fin.rev i)) := by
    intro a b hab
    have := hp (Fin.rev_le_rev.2 hab)
    simp only
    linarith
  have hEr : ∀ i, L * ((-q (Fin.rev i)) - (-p (Fin.rev i))) =
      2 * ∑ k, Ahat c (fun m => -q (Fin.rev m)) i k := by
    intro i
    have hrev := hE' (Fin.rev i)
    have hsum : ∑ k, Ahat c (fun m => -q (Fin.rev m)) i k = -∑ m, Ahat c q (Fin.rev i) m := by
      simp only [reflect_Ahat]
      rw [Finset.sum_neg_distrib]
      congr 1
      have := Equiv.sum_comp Fin.revPerm (fun m => Ahat c q (Fin.rev i) m)
      simpa [Fin.revPerm_apply] using this
    rw [hsum]
    linarith
  have hdqr : ∀ i k : Fin N, k < i →
      ((-q (Fin.rev i)) - (-p (Fin.rev i))) - ((-q (Fin.rev k)) - (-p (Fin.rev k))) ≤
        (-q (Fin.rev i)) - (-q (Fin.rev k)) := by
    intro i k hki
    have := hpr hki.le
    simp only at this ⊢
    linarith
  have lo := upper_bound_aux hN hc hL (fun i => -q (Fin.rev i))
    (fun i => (-q (Fin.rev i)) - (-p (Fin.rev i))) hqr hdqr hEr (Fin.rev j)
  simp only [Fin.rev_rev] at lo
  rw [abs_le]
  constructor
  · linarith
  · exact up

/-! ## 7. In-particular clause: actual repulsive Bethe configurations (`CC:mean-field-root-bound`) -/

/-- **CC:mean-field-root-bound.** For an ordered on-shell configuration (labels `n` nondecreasing and the
printed Bethe equation with `c = κ/N`), `|q_j − 2π n_j/L| ≤ 2√((κ/L)(1 − 1/N))`. -/
theorem mean_field_root_bound {N : ℕ} (hN : 1 ≤ N) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    (n : Fin N → ℤ) (q : Fin N → ℝ)
    (h : QuantumNLS.OnShellSpacing.OrderedOnShell L κ n q) (j : Fin N) :
    |q j - 2 * Real.pi * (n j : ℝ) / L| ≤ 2 * Real.sqrt ((κ / L) * (1 - 1 / (N : ℝ))) := by
  unfold QuantumNLS.OnShellSpacing.OrderedOnShell at h
  obtain ⟨hq, hn, hP⟩ := h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  set p : Fin N → ℝ := fun i => 2 * Real.pi * (n i : ℝ) / L with hpdef
  have hp : Monotone p := by
    intro a b hab
    have hz : (n a : ℝ) ≤ (n b : ℝ) := by exact_mod_cast hn hab
    rw [hpdef]
    exact div_le_div_of_nonneg_right (by gcongr) hL.le
  have hE : ∀ i, L * (q i - p i) = 2 * ∑ k ∈ Finset.univ.erase i,
      Real.arctan ((κ / (N : ℝ)) / (q i - q k)) := by
    intro i
    have e := hP i
    simp only [← div_div] at e
    have e2 : L * p i = 2 * Real.pi * (n i : ℝ) := by
      rw [hpdef]
      field_simp
    rw [mul_sub, e2]
    linarith
  have main := individual_root_bound hN hL (div_pos hκ hN0) q p hq hp hE j
  have hconst : (κ / (N : ℝ)) * ((N : ℝ) - 1) / L = (κ / L) * (1 - 1 / (N : ℝ)) := by
    field_simp
  rw [hconst] at main
  exact main

/-- The accepted-roots form: for `q` the R-4C8D7C9E root vector `BetheSmooth.roots L n (κ/N)` of
nondecreasing corrected integers `n`, the same bound holds. -/
theorem mean_field_root_bound_roots {N : ℕ} (hN : 1 ≤ N) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    (n : Fin N → ℤ) (hn : Monotone n) (j : Fin N) :
    |QuantumNLS.BetheSmooth.roots L n (κ / (N : ℝ)) j - 2 * Real.pi * (n j : ℝ) / L| ≤
      2 * Real.sqrt ((κ / L) * (1 - 1 / (N : ℝ))) := by
  have h := (QuantumNLS.OnShellSpacing.ordered_onshell_iff_roots hN hL hκ n hn
    (QuantumNLS.BetheSmooth.roots L n (κ / (N : ℝ)))).2 rfl
  exact mean_field_root_bound hN hL hκ n _ h j

end QuantumNLS.IndividualRootBound

/-! Axiom audit (every headline and key declaration). -/
#print axioms QuantumNLS.IndividualRootBound.individual_root_bound
#print axioms QuantumNLS.IndividualRootBound.mean_field_root_bound
#print axioms QuantumNLS.IndividualRootBound.mean_field_root_bound_roots
#print axioms QuantumNLS.IndividualRootBound.upper_bound_aux
#print axioms QuantumNLS.IndividualRootBound.core_ineq
#print axioms QuantumNLS.IndividualRootBound.int_conv_le
#print axioms QuantumNLS.IndividualRootBound.mean_cov_le
#print axioms QuantumNLS.IndividualRootBound.term_le
#print axioms QuantumNLS.IndividualRootBound.pair_term_le
#print axioms QuantumNLS.IndividualRootBound.pairInt_eq
#print axioms QuantumNLS.IndividualRootBound.pairInt_symm
#print axioms QuantumNLS.IndividualRootBound.pairInt_self
#print axioms QuantumNLS.IndividualRootBound.sum_pairInt_eq
#print axioms QuantumNLS.IndividualRootBound.sum_pair_identity
#print axioms QuantumNLS.IndividualRootBound.Ahat_anti
#print axioms QuantumNLS.IndividualRootBound.sum_Ahat_eq
#print axioms QuantumNLS.IndividualRootBound.reflect_Ahat
#print axioms QuantumNLS.IndividualRootBound.hasDerivAt_Mexp
#print axioms QuantumNLS.IndividualRootBound.Mexp_pos
