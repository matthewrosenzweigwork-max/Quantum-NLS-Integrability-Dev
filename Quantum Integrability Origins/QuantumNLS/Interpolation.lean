import Mathlib

/-!
# Cauchy-kernel Lagrange remainder (source PROP-015, `Q7A:lem:interp`)

Source: `source/chapters/propagation/window_reconstruction.tex:57`, label `Q7A:lem:interp`,
`\ReportID{PROP-015}`, status `Proved` in the report.

Statement in the report. Let `z_0,…,z_m` be distinct complex numbers with Lagrange basis
polynomials `ℓ_j`. For `q` different from these nodes and from `z`,

  `1/(z-q) - ∑_j ℓ_j(z)/(z_j-q) = (-1)^{m+1} ∏_j (z-z_j) / ((z-q) ∏_j (z_j-q))`.

If `|z-a| ≤ H`, `|z_j-a| ≤ H₁`, `|q| ≤ R` and `2R ≤ |a|`, then for `R` large the right side is
`C_{m,H,H₁} R^{-m-2}`. This file gives the explicit constant `2^{m+2}(H+H₁)^{m+1}`, valid when
`R ≥ 2H` and `R ≥ 2H₁`.

Proof route (follows the report):
1. `P := interpolate univ zs (j ↦ 1/(zs j - q))` is the Lagrange interpolant of `w ↦ 1/(w-q)`.
2. The polynomial identity `1 - (X - q) P = c · nodal(zs)`, `c = 1/∏(q - zs j)`, holds: both
   sides have degree ≤ m+1 and agree on the m+2 distinct points `q, zs 0, …, zs m`.
3. Evaluating at `z` and dividing by `z - q` gives the stated identity.
4. The norm bound follows from explicit lower bounds on `|z-q|` and `|zs j - q|`.

Inputs are injectivity of the nodes and the displayed hypotheses. Nonvanishing of `zs j - q` and
`z - q` is derived, not assumed. The Lagrange basis is Mathlib's `Lagrange.basis univ zs j`,
which is the product `∏_{k ≠ j} (X - z_k)/(z_j - z_k)`, i.e. the source's `ℓ_j`.
-/

namespace QuantumNLS.Interpolation

open Polynomial Finset

noncomputable section

variable {m : ℕ}

/-- The Lagrange basis polynomial `ℓ_j` of the nodes `zs`, evaluated at `z`. -/
def lagrangeValue (zs : Fin (m + 1) → ℂ) (j : Fin (m + 1)) (z : ℂ) : ℂ :=
  (Lagrange.basis univ zs j).eval z

/-- Explicit product form of the source's `ℓ_j(z) = ∏_{k ≠ j} (z - z_k)/(z_j - z_k)`. -/
theorem lagrangeValue_eq_prod (zs : Fin (m + 1) → ℂ) (j : Fin (m + 1)) (z : ℂ) :
    lagrangeValue zs j z = ∏ k ∈ univ.erase j, (z - zs k) / (zs j - zs k) := by
  unfold lagrangeValue Lagrange.basis
  rw [eval_prod]
  refine prod_congr rfl (fun k _ => ?_)
  simp [Lagrange.basisDivisor, div_eq_mul_inv, mul_comm]

/-- The Lagrange interpolant of `w ↦ 1/(w - q)` at the nodes `zs`. -/
def cauchyInterpolant (zs : Fin (m + 1) → ℂ) (q : ℂ) : ℂ[X] :=
  Lagrange.interpolate univ zs (fun j => 1 / (zs j - q))

theorem natDegree_cauchyInterpolant_le (zs : Fin (m + 1) → ℂ) (hz : Function.Injective zs)
    (q : ℂ) : (cauchyInterpolant zs q).natDegree ≤ m := by
  have hvs : Set.InjOn zs (univ : Finset (Fin (m + 1))) := hz.injOn
  have h := Lagrange.degree_interpolate_lt (r := fun j => 1 / (zs j - q)) hvs
  rw [card_univ, Fintype.card_fin] at h
  unfold cauchyInterpolant
  rw [natDegree_le_iff_degree_le]
  exact Order.le_of_lt_succ (by exact_mod_cast h)

theorem eval_cauchyInterpolant_node (zs : Fin (m + 1) → ℂ) (hz : Function.Injective zs)
    (q : ℂ) (j : Fin (m + 1)) : (cauchyInterpolant zs q).eval (zs j) = 1 / (zs j - q) := by
  unfold cauchyInterpolant
  exact Lagrange.eval_interpolate_at_node (fun j => 1 / (zs j - q)) (hz.injOn) (mem_univ j)

theorem eval_cauchyInterpolant_sum (zs : Fin (m + 1) → ℂ) (q z : ℂ) :
    (cauchyInterpolant zs q).eval z = ∑ j, (1 / (zs j - q)) * lagrangeValue zs j z := by
  unfold cauchyInterpolant lagrangeValue
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  simp [eval_mul, eval_C]

/-- Polynomial form of the remainder identity:
`1 - (X - q) · P = c · ∏_j (X - zs j)` with `c = 1 / ∏_j (q - zs j)`. -/
theorem one_sub_mul_cauchyInterpolant (zs : Fin (m + 1) → ℂ) (hz : Function.Injective zs)
    (q : ℂ) (hq : ∀ j, zs j ≠ q) :
    (1 : ℂ[X]) - (X - C q) * cauchyInterpolant zs q
      = C (1 / ∏ j, (q - zs j)) * Lagrange.nodal univ zs := by
  have hne : ∀ j, q - zs j ≠ 0 := fun j => sub_ne_zero.mpr (hq j).symm
  have hprod_ne : ∏ j, (q - zs j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hne j)
  have hqimage : q ∉ univ.image zs := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    intro j hj
    exact hq j hj
  have hcardT : #(insert q (univ.image zs)) = m + 2 := by
    rw [card_insert_of_notMem hqimage, card_image_of_injective _ hz, card_univ,
      Fintype.card_fin]
  have hdeg : ((1 : ℂ[X]) - (X - C q) * cauchyInterpolant zs q
      - C (1 / ∏ j, (q - zs j)) * Lagrange.nodal univ zs).degree
      < ((#(insert q (univ.image zs)) : ℕ) : WithBot ℕ) := by
    have h1 : ((X - C q) * cauchyInterpolant zs q).natDegree ≤ m + 1 :=
      natDegree_mul_le.trans (by rw [natDegree_X_sub_C]; have := natDegree_cauchyInterpolant_le zs hz q; omega)
    have h2 : ((1 : ℂ[X]) - (X - C q) * cauchyInterpolant zs q).natDegree ≤ m + 1 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) h1)
    have h3 : (C (1 / ∏ j, (q - zs j)) * Lagrange.nodal univ zs).natDegree ≤ m + 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [Lagrange.natDegree_nodal, card_univ, Fintype.card_fin]
    have h4 : ((1 : ℂ[X]) - (X - C q) * cauchyInterpolant zs q
        - C (1 / ∏ j, (q - zs j)) * Lagrange.nodal univ zs).natDegree ≤ m + 1 :=
      (natDegree_sub_le _ _).trans (max_le h2 h3)
    have h5 : ((1 : ℂ[X]) - (X - C q) * cauchyInterpolant zs q
        - C (1 / ∏ j, (q - zs j)) * Lagrange.nodal univ zs).degree ≤ ((m + 1 : ℕ) : WithBot ℕ) :=
      degree_le_natDegree.trans (by exact_mod_cast h4)
    refine lt_of_le_of_lt h5 ?_
    rw [hcardT]
    exact_mod_cast (by omega : m + 1 < m + 2)
  refine eq_of_degree_sub_lt_of_eval_finset_eq (insert q (univ.image zs)) hdeg ?_
  intro x hx
  rcases mem_insert.mp hx with hxq | hx'
  · -- the extra node `x = q`
    subst hxq
    simp only [eval_sub, eval_one, eval_mul, eval_X, eval_C, Lagrange.eval_nodal, sub_self,
      zero_mul, sub_zero]
    exact (one_div_mul_cancel hprod_ne).symm
  · -- the nodes `x = zs j`
    obtain ⟨j, -, rfl⟩ := mem_image.mp hx'
    have hzj : zs j - q ≠ 0 := sub_ne_zero.mpr (hq j)
    simp only [eval_sub, eval_one, eval_mul, eval_X, eval_C]
    rw [eval_cauchyInterpolant_node zs hz q j, Lagrange.eval_nodal_at_node (mem_univ j),
      mul_zero, mul_one_div_cancel hzj, sub_self]

/-- Value form of the remainder identity (`Q7A:lem:interp`, eq. `Q7A:eq:interp`). -/
theorem cauchy_remainder (zs : Fin (m + 1) → ℂ) (hz : Function.Injective zs) (q z : ℂ)
    (hq : ∀ j, zs j ≠ q) (hzq : z ≠ q) :
    1 / (z - q) - ∑ j, lagrangeValue zs j z / (zs j - q)
      = (-1) ^ (m + 1) * (∏ j, (z - zs j)) / ((z - q) * ∏ j, (zs j - q)) := by
  have hdq : ∏ j, (q - zs j) = (-1) ^ (m + 1) * ∏ j, (zs j - q) := by
    have h : ∀ j, q - zs j = (-1) * (zs j - q) := fun j => by ring
    simp_rw [h]
    rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ, Fintype.card_fin]
  have hD : ∏ j, (zs j - q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (hq j))
  have hzq' : z - q ≠ 0 := sub_ne_zero.mpr hzq
  have hsgn : (-1 : ℂ) ^ (m + 1) * (-1) ^ (m + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hsgn0 : (-1 : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpoly := one_sub_mul_cauchyInterpolant zs hz q hq
  have hev := congrArg (fun p : ℂ[X] => p.eval z) hpoly
  simp only [eval_sub, eval_one, eval_mul, eval_X, eval_C, Lagrange.eval_nodal] at hev
  rw [eval_cauchyInterpolant_sum, hdq] at hev
  have hinv : (1 : ℂ) / ((-1) ^ (m + 1) * ∏ j, (zs j - q))
      = (-1) ^ (m + 1) / ∏ j, (zs j - q) := by
    rw [div_eq_div_iff (mul_ne_zero hsgn0 hD) hD]
    linear_combination (-(∏ j, (zs j - q))) * hsgn
  rw [hinv] at hev
  have hsum : ∑ j, lagrangeValue zs j z / (zs j - q)
      = ∑ j, (1 / (zs j - q)) * lagrangeValue zs j z :=
    Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum]
  have hL : 1 / (z - q) - ∑ j, (1 / (zs j - q)) * lagrangeValue zs j z
      = (1 - (z - q) * ∑ j, (1 / (zs j - q)) * lagrangeValue zs j z) / (z - q) := by
    rw [sub_div, mul_div_cancel_left₀ _ hzq']
  rw [hL, hev, div_mul_eq_mul_div, mul_comm (z - q) (∏ j, (zs j - q)), ← div_div]

/-- Distance lower bounds from the hypotheses: `‖a - q‖ ≥ R`, hence `‖zs j - q‖ ≥ R/2` and
`‖z - q‖ ≥ R/2`. These give the nonvanishing of `zs j - q` and `z - q` used by the remainder. -/
theorem distance_lower_bounds (zs : Fin (m + 1) → ℂ) (q z a : ℂ) (R H H1 : ℝ)
    (_hR : 0 < R) (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R)
    (hza : ‖z - a‖ ≤ H) (hzsa : ∀ j, ‖zs j - a‖ ≤ H1) (hq : ‖q‖ ≤ R) (ha : 2 * R ≤ ‖a‖) :
    (∀ j, R / 2 ≤ ‖zs j - q‖) ∧ R / 2 ≤ ‖z - q‖ := by
  have haq : R ≤ ‖a - q‖ := by
    have := norm_sub_norm_le a q
    linarith
  have hzsq : ∀ j, R / 2 ≤ ‖zs j - q‖ := by
    intro j
    have h := norm_sub_norm_le (a - q) (a - zs j)
    have e : (a - q) - (a - zs j) = zs j - q := by ring
    rw [e, norm_sub_rev a (zs j)] at h
    linarith [hzsa j]
  have hzq : R / 2 ≤ ‖z - q‖ := by
    have h := norm_sub_norm_le (a - q) (a - z)
    have e : (a - q) - (a - z) = z - q := by ring
    rw [e, norm_sub_rev a z] at h
    linarith
  exact ⟨hzsq, hzq⟩

/-- Explicit norm bound (`Q7A:eq:interp`, second assertion): with `R ≥ 2H`, `R ≥ 2H₁`,
`‖z-a‖ ≤ H`, `‖z_j - a‖ ≤ H₁`, `‖q‖ ≤ R` and `2R ≤ ‖a‖`, the right side has norm at most
`2^{m+2}(H+H₁)^{m+1} / R^{m+2}`. The nonvanishing of `z - q` and `zs j - q` is derived from the
hypotheses (`‖zs j - q‖ ≥ R/2 > 0`), not assumed. -/
theorem cauchy_remainder_bound (zs : Fin (m + 1) → ℂ) (q z a : ℂ) (R H H1 : ℝ)
    (hR : 0 < R) (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R)
    (hza : ‖z - a‖ ≤ H) (hzsa : ∀ j, ‖zs j - a‖ ≤ H1) (hq : ‖q‖ ≤ R) (ha : 2 * R ≤ ‖a‖) :
    ‖(-1 : ℂ) ^ (m + 1) * (∏ j, (z - zs j)) / ((z - q) * ∏ j, (zs j - q))‖
      ≤ 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) := by
  have hH0 : 0 ≤ H := le_trans (norm_nonneg _) hza
  have hH10 : 0 ≤ H1 := le_trans (norm_nonneg _) (hzsa ⟨0, Nat.succ_pos m⟩)
  obtain ⟨hzsq, hzq⟩ := distance_lower_bounds zs q z a R H H1 hR hH hH1 hza hzsa hq ha
  have hnum : ‖(-1 : ℂ) ^ (m + 1) * ∏ j, (z - zs j)‖ ≤ (H + H1) ^ (m + 1) := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod]
    calc ∏ j, ‖z - zs j‖ ≤ ∏ _j : Fin (m + 1), (H + H1) := by
          apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
          intro j _
          have h := norm_sub_le (z - a) (zs j - a)
          have e : (z - a) - (zs j - a) = z - zs j := by ring
          rw [e] at h
          linarith [hza, hzsa j]
      _ = (H + H1) ^ (m + 1) := by rw [Finset.prod_const, card_univ, Fintype.card_fin]
  have hden : (R / 2) * (R / 2) ^ (m + 1) ≤ ‖(z - q) * ∏ j, (zs j - q)‖ := by
    rw [norm_mul, norm_prod]
    have hp : ∏ _j : Fin (m + 1), (R / 2) ≤ ∏ j, ‖zs j - q‖ :=
      Finset.prod_le_prod₀ (fun j _ => by linarith) (fun j _ => hzsq j)
    rw [Finset.prod_const, card_univ, Fintype.card_fin] at hp
    exact mul_le_mul hzq hp (pow_nonneg (by linarith) _) (norm_nonneg _)
  have hrhs : 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2)
      = (H + H1) ^ (m + 1) / ((R / 2) * (R / 2) ^ (m + 1)) := by
    rw [div_pow]
    field_simp
    ring
  rw [hrhs, norm_div]
  exact div_le_div₀ (pow_nonneg (by linarith) _) hnum
    (mul_pos (by linarith) (pow_pos (by linarith) _)) hden

/-- Combined bound (`Q7A:lem:interp` in the form used by `Q7A:lem:extrap`): under the same
hypotheses the remainder `1/(z-q) - ∑_j ℓ_j(z)/(z_j-q)` has norm at most
`2^{m+2}(H+H₁)^{m+1} / R^{m+2}`. Nonvanishing of `z-q` and `zs j - q` is derived. -/
theorem cauchy_remainder_sum_bound (zs : Fin (m + 1) → ℂ) (hz : Function.Injective zs)
    (q z a : ℂ) (R H H1 : ℝ)
    (hR : 0 < R) (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R)
    (hza : ‖z - a‖ ≤ H) (hzsa : ∀ j, ‖zs j - a‖ ≤ H1) (hq : ‖q‖ ≤ R) (ha : 2 * R ≤ ‖a‖) :
    ‖1 / (z - q) - ∑ j, lagrangeValue zs j z / (zs j - q)‖
      ≤ 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) := by
  obtain ⟨hzsq, hzq⟩ := distance_lower_bounds zs q z a R H H1 hR hH hH1 hza hzsa hq ha
  have hqne : ∀ j, zs j ≠ q := fun j hj => by
    have h := hzsq j
    rw [hj, sub_self, norm_zero] at h
    linarith
  have hzne : z ≠ q := fun hj => by
    have h := hzq
    rw [hj, sub_self, norm_zero] at h
    linarith
  rw [cauchy_remainder zs hz q z hqne hzne]
  exact cauchy_remainder_bound zs q z a R H H1 hR hH hH1 hza hzsa hq ha

/-- Deterministic extrapolation core of `Q7A:lem:extrap` (PROP-016). For a finite weighted
measure `∑_i w_i δ_{q_i}` with `w_i ≥ 0`, `∑ w_i ≤ 1` and atoms `|q_i| ≤ R`, the Cauchy transform
satisfies the Lagrange node identity
`G(z) − ∑_k ℓ_k(z) G(z_k) = ∑_i w_i (1/(z−q_i) − ∑_k ℓ_k(z)/(z_k−q_i))`
up to `2^{m+2}(H+H₁)^{m+1}/R^{m+2}` in norm. Nodes, nonvanishing and the remainder bound come from
`cauchy_remainder_sum_bound`. -/
theorem cauchy_transform_extrapolation {N : ℕ} (zs : Fin (m + 1) → ℂ) (hz : Function.Injective zs)
    (qs : Fin N → ℂ) (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i ≤ 1)
    (z a : ℂ) (R H H1 : ℝ) (hR : 0 < R) (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R)
    (hza : ‖z - a‖ ≤ H) (hzsa : ∀ j, ‖zs j - a‖ ≤ H1) (hqs : ∀ i, ‖qs i‖ ≤ R) (ha : 2 * R ≤ ‖a‖) :
    ‖(∑ i, (w i : ℂ) * (1 / (z - qs i)))
        - ∑ k, lagrangeValue zs k z * ∑ i, (w i : ℂ) * (1 / (zs k - qs i))‖
      ≤ 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) := by
  have hH10 : 0 ≤ H1 := le_trans (norm_nonneg _) (hzsa ⟨0, Nat.succ_pos m⟩)
  have hH0 : 0 ≤ H := le_trans (norm_nonneg _) hza
  have hC : 0 ≤ 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) :=
    div_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _)) (pow_nonneg hR.le _)
  have hswap : ∑ k, lagrangeValue zs k z * ∑ i, (w i : ℂ) * (1 / (zs k - qs i))
      = ∑ i, (w i : ℂ) * ∑ k, lagrangeValue zs k z / (zs k - qs i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  have key : (∑ i, (w i : ℂ) * (1 / (z - qs i)))
        - ∑ k, lagrangeValue zs k z * ∑ i, (w i : ℂ) * (1 / (zs k - qs i))
      = ∑ i, (w i : ℂ) * (1 / (z - qs i) - ∑ k, lagrangeValue zs k z / (zs k - qs i)) := by
    rw [hswap, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [key]
  calc ‖∑ i, (w i : ℂ) * (1 / (z - qs i) - ∑ k, lagrangeValue zs k z / (zs k - qs i))‖
      ≤ ∑ i, ‖(w i : ℂ) * (1 / (z - qs i) - ∑ k, lagrangeValue zs k z / (zs k - qs i))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, w i * (2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2)) :=
        Finset.sum_le_sum (fun i _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw i)]
          exact mul_le_mul_of_nonneg_left
            (cauchy_remainder_sum_bound zs hz (qs i) z a R H H1 hR hH hH1 hza hzsa (hqs i) ha)
            (hw i))
    _ = (∑ i, w i) * (2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2)) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * (2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2)) :=
        mul_le_mul_of_nonneg_right hwsum hC
    _ = 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) := one_mul _

end

end QuantumNLS.Interpolation

/-! Axiom check for the headline declarations (compile-log evidence). -/
#print axioms QuantumNLS.Interpolation.one_sub_mul_cauchyInterpolant
#print axioms QuantumNLS.Interpolation.cauchy_remainder
#print axioms QuantumNLS.Interpolation.cauchy_remainder_bound
#print axioms QuantumNLS.Interpolation.lagrangeValue_eq_prod
#print axioms QuantumNLS.Interpolation.cauchy_remainder_sum_bound
#print axioms QuantumNLS.Interpolation.cauchy_transform_extrapolation
