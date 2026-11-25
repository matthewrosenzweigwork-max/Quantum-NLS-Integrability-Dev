import NlsGge.Birkhoff.F11Claim38d

/-! # NEW-F11 (`F:cor:charge`), file 5: uniform integrability and moment convergence (NEW-F11.06), `B`-free

Source: `paper/v2.tex` l.1817-1818: "Weak convergence there and the uniform exponential bound imply convergence
of all of its finite moments by truncation and uniform integrability. The same reasoning applies to finite products
of fixed charges by using a positive coefficient for each one in (F:eq:chargeexp)."

* `tendsto_integral_of_sq_bounded38` (truncation + uniform integrability): `ν_N`, `μ` probability measures,
  `F ≥ 0` measurable, `sup_N ∫ F² dν_N ≤ M`, and weak convergence of the truncations `min(F,R)`, `min(F²,R)`
  (bounded continuous test functions). Then `F, F² ∈ L¹(μ)`, `∫ F² dμ ≤ M`, `F ∈ L¹(ν_N)` and `∫ F dν_N → ∫ F dμ`.
* `prod_sq_le_exp38`: the polynomial-in-charges bound `(∏_i Q_{j_i}^{p_i})² ≤ K exp(Σ_{j≤J} t_j Q_j)` for nonnegative
  `Q_j` and positive `t_j`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory Filter Topology
open scoped ENNReal

section UI

variable {X : Type*} [MeasurableSpace X]

/-- Pointwise: for `0 ≤ F` and `R > 0`: `(F - min F R) R ≤ F²`. -/
theorem sub_min_mul_le38 {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) : (a - min a R) * R ≤ a ^ 2 := by
  rcases le_total a R with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-- Tail estimate under any probability measure with a bounded second moment. -/
theorem tail_integral_le38 (ρ : Measure X) [IsProbabilityMeasure ρ] (F : X → ℝ) (hF0 : ∀ x, 0 ≤ F x)
    (hFm : AEStronglyMeasurable F ρ) (hF2 : Integrable (fun x => F x ^ 2) ρ) {M : ℝ}
    (hM : ∫ x, F x ^ 2 ∂ρ ≤ M) {R : ℝ} (hR : 0 < R) :
    Integrable F ρ ∧ Integrable (fun x => min (F x) R) ρ ∧
      0 ≤ ∫ x, (F x - min (F x) R) ∂ρ ∧ ∫ x, (F x - min (F x) R) ∂ρ ≤ M / R := by
  have hFi : Integrable F ρ := by
    refine (hF2.add (integrable_const (1 : ℝ))).mono' hFm (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
    show F x ≤ F x ^ 2 + 1
    nlinarith [sq_nonneg (F x - 1)]
  have hmin : Integrable (fun x => min (F x) R) ρ := by
    refine (integrable_const R).mono' ((continuous_id.min continuous_const).comp_aestronglyMeasurable hFm)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF0 x) hR.le)]
    exact min_le_right _ _
  refine ⟨hFi, hmin, integral_nonneg fun x => sub_nonneg.2 (min_le_left _ _), ?_⟩
  have h1 : ∫ x, (F x - min (F x) R) ∂ρ ≤ ∫ x, F x ^ 2 / R ∂ρ := by
    refine integral_mono (hFi.sub hmin) (hF2.div_const R) fun x => ?_
    rw [le_div_iff₀ hR]
    exact sub_min_mul_le38 (hF0 x) hR
  rw [integral_div] at h1
  exact h1.trans (div_le_div_of_nonneg_right hM hR.le)

/-- **Truncation + uniform integrability** (NEW-F11.06): uniformly bounded second moments and weak convergence of
the truncations give convergence of the first moments, and `F² ∈ L¹(μ)`, `∫ F² dμ ≤ M`. -/
theorem tendsto_integral_of_sq_bounded38 (ν : ℕ → Measure X) (μ : Measure X)
    (hν : ∀ N, IsProbabilityMeasure (ν N)) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF0 : ∀ x, 0 ≤ F x)
    (hFν : ∀ N, AEStronglyMeasurable F (ν N)) (hFμ : AEStronglyMeasurable F μ)
    (M : ℝ) (hM : ∀ N, Integrable (fun x => F x ^ 2) (ν N) ∧ ∫ x, F x ^ 2 ∂(ν N) ≤ M)
    (hw1 : ∀ R : ℝ, 0 < R →
      Tendsto (fun N => ∫ x, min (F x) R ∂(ν N)) atTop (𝓝 (∫ x, min (F x) R ∂μ)))
    (hw2 : ∀ R : ℝ, 0 < R →
      Tendsto (fun N => ∫ x, min (F x ^ 2) R ∂(ν N)) atTop (𝓝 (∫ x, min (F x ^ 2) R ∂μ))) :
    (Integrable (fun x => F x ^ 2) μ ∧ ∫ x, F x ^ 2 ∂μ ≤ M) ∧ Integrable F μ ∧
      (∀ N, Integrable F (ν N)) ∧
      Tendsto (fun N => ∫ x, F x ∂(ν N)) atTop (𝓝 (∫ x, F x ∂μ)) := by
  have hF2m : AEStronglyMeasurable (fun x => F x ^ 2) μ := hFμ.pow 2
  have hM0 : 0 ≤ M := (integral_nonneg fun x => sq_nonneg (F x)).trans (hM 0).2
  -- Step A: `F² ∈ L¹(μ)` with `∫ F² ≤ M`
  have hbdd : ∀ R : ℝ, 0 < R → Integrable (fun x => min (F x ^ 2) R) μ := fun R hR => by
    refine (integrable_const R).mono' ((continuous_id.min continuous_const).comp_aestronglyMeasurable hF2m)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) hR.le)]
    exact min_le_right _ _
  have hbddν : ∀ N, ∀ R : ℝ, 0 < R → Integrable (fun x => min (F x ^ 2) R) (ν N) := fun N R hR => by
    have := hν N
    refine (integrable_const R).mono' ((continuous_id.min continuous_const).comp_aestronglyMeasurable ((hFν N).pow 2))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) hR.le)]
    exact min_le_right _ _
  have hmuR : ∀ R : ℝ, 0 < R → ∫ x, min (F x ^ 2) R ∂μ ≤ M := fun R hR => by
    refine le_of_tendsto (hw2 R hR) (Filter.Eventually.of_forall fun N => ?_)
    have := hν N
    exact (integral_mono (hbddν N R hR) (hM N).1 fun x => min_le_left _ _).trans (hM N).2
  have hL : ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ ≤ ENNReal.ofReal M := by
    have hsup : ∀ x, ENNReal.ofReal (F x ^ 2) =
        ⨆ k : ℕ, ENNReal.ofReal (min (F x ^ 2) ((k : ℝ) + 1)) := fun x => by
      apply le_antisymm
      · obtain ⟨k, hk⟩ := exists_nat_ge (F x ^ 2)
        refine le_iSup_of_le k ?_
        rw [min_eq_left (by linarith)]
      · exact iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    simp_rw [hsup]
    rw [lintegral_iSup' (fun k => (hbdd _ (by positivity)).1.aemeasurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun x k l hkl =>
        ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by
          have : (k : ℝ) ≤ l := by exact_mod_cast hkl
          linarith)))]
    refine iSup_le fun k => ?_
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [← ofReal_integral_eq_lintegral_ofReal (hbdd _ hkpos)
      (Filter.Eventually.of_forall fun x => le_min (sq_nonneg _) hkpos.le)]
    exact ENNReal.ofReal_le_ofReal (hmuR _ hkpos)
  have hF2μ : Integrable (fun x => F x ^ 2) μ :=
    ⟨hF2m, by
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)]
      exact lt_of_le_of_lt hL ENNReal.ofReal_lt_top⟩
  have hF2μM : ∫ x, F x ^ 2 ∂μ ≤ M := by
    have := (ofReal_integral_eq_lintegral_ofReal hF2μ
      (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm ▸ hL
    exact (ENNReal.ofReal_le_ofReal_iff hM0).1 (by
      rwa [ofReal_integral_eq_lintegral_ofReal hF2μ (Filter.Eventually.of_forall fun x => sq_nonneg _)])
  -- Step B: convergence
  have hμtail := fun (R : ℝ) (hR : 0 < R) => tail_integral_le38 μ F hF0 hFμ hF2μ hF2μM hR
  have hνtail := fun (N : ℕ) (R : ℝ) (hR : 0 < R) => by
    have := hν N
    exact tail_integral_le38 (ν N) F hF0 (hFν N) (hM N).1 (hM N).2 hR
  refine ⟨⟨hF2μ, hF2μM⟩, (hμtail 1 one_pos).1, fun N => (hνtail N 1 one_pos).1, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R : ℝ := 4 * (M + 1) / ε with hRdef
  have hR : 0 < R := by positivity
  have hMR : M / R < ε / 4 := by
    rw [hRdef, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (hw1 R hR) (ε / 2) (by positivity)
  refine ⟨N0, fun N hN => ?_⟩
  have h1 := hN0 N hN
  rw [Real.dist_eq] at h1 ⊢
  obtain ⟨hFiν, hminν, htν0, htν1⟩ := hνtail N R hR
  obtain ⟨hFiμ, hminμ, htμ0, htμ1⟩ := hμtail R hR
  have e1 : ∫ x, F x ∂(ν N) = ∫ x, (F x - min (F x) R) ∂(ν N) + ∫ x, min (F x) R ∂(ν N) := by
    rw [integral_sub hFiν hminν]; ring
  have e2 : ∫ x, F x ∂μ = ∫ x, (F x - min (F x) R) ∂μ + ∫ x, min (F x) R ∂μ := by
    rw [integral_sub hFiμ hminμ]; ring
  rw [e1, e2]
  have : |∫ x, (F x - min (F x) R) ∂(ν N) + ∫ x, min (F x) R ∂(ν N) -
      (∫ x, (F x - min (F x) R) ∂μ + ∫ x, min (F x) R ∂μ)| ≤
      |∫ x, (F x - min (F x) R) ∂(ν N) - ∫ x, (F x - min (F x) R) ∂μ| +
        |∫ x, min (F x) R ∂(ν N) - ∫ x, min (F x) R ∂μ| := by
    have := abs_add_le (∫ x, (F x - min (F x) R) ∂(ν N) - ∫ x, (F x - min (F x) R) ∂μ)
      (∫ x, min (F x) R ∂(ν N) - ∫ x, min (F x) R ∂μ)
    convert this using 2; ring
  have h3 : |∫ x, (F x - min (F x) R) ∂(ν N) - ∫ x, (F x - min (F x) R) ∂μ| ≤ M / R := by
    rw [abs_le]; constructor <;> linarith
  linarith

end UI

section Products

variable {X : Type*}

/-- `x^k ≤ k!/s^k · e^{s x}` for `x ≥ 0`, `s > 0`. -/
theorem pow_le_exp_mul38 {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (k : ℕ) :
    x ^ k ≤ ((k.factorial : ℝ) / s ^ k) * Real.exp (s * x) := by
  have h := NlsGge.Weights.expSeries_term_le (s * x) (mul_nonneg hs.le hx) k
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hf] at h
  have hsk : 0 < s ^ k := pow_pos hs k
  calc x ^ k = (s * x) ^ k / s ^ k := by rw [mul_pow]; field_simp
    _ ≤ (Real.exp (s * x) * k.factorial) / s ^ k := by gcongr
    _ = _ := by ring

/-- `(∏_i Q_{j_i}^{p_i})² ≤ K exp(Σ_{j≤J} t_j Q_j)` for nonnegative `Q_j`, positive `t_j` (`j ≤ J`) and
`j_i ≤ J`. -/
theorem prod_sq_le_exp38 (Q : ℕ → X → ℝ) (J : ℕ) (hQ : ∀ j ≤ J, ∀ x, 0 ≤ Q j x) (t : ℕ → ℝ)
    (ht : ∀ j ≤ J, 0 < t j) (n : ℕ) (jj : Fin n → ℕ) (hjj : ∀ i, jj i ≤ J) (p : Fin n → ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : X, (∏ i, Q (jj i) x ^ p i) ^ 2 ≤
      K * Real.exp (∑ j ∈ Finset.range (J + 1), t j * Q j x) := by
  set s : Fin n → ℝ := fun i => t (jj i) / ((n : ℝ) + 1) with hs
  have hspos : ∀ i, 0 < s i := fun i => div_pos (ht _ (hjj i)) (by positivity)
  refine ⟨∏ i, (((2 * p i).factorial : ℝ) / s i ^ (2 * p i)), Finset.prod_pos fun i _ => by
    have := hspos i
    positivity, fun x => ?_⟩
  set H : ℝ := ∑ j ∈ Finset.range (J + 1), t j * Q j x with hH
  have hterm : ∀ j ∈ Finset.range (J + 1), 0 ≤ t j * Q j x := fun j hj =>
    mul_nonneg (ht j (by simpa [Nat.lt_succ_iff] using hj)).le (hQ j (by simpa [Nat.lt_succ_iff] using hj) x)
  have hH0 : 0 ≤ H := Finset.sum_nonneg hterm
  have hsingle : ∀ i, t (jj i) * Q (jj i) x ≤ H := fun i =>
    Finset.single_le_sum hterm (by simpa [Nat.lt_succ_iff] using hjj i)
  calc (∏ i, Q (jj i) x ^ p i) ^ 2 = ∏ i, Q (jj i) x ^ (2 * p i) := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← pow_mul, mul_comm]
    _ ≤ ∏ i, ((((2 * p i).factorial : ℝ) / s i ^ (2 * p i)) * Real.exp (s i * Q (jj i) x)) :=
        Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hQ _ (hjj i) x) _) fun i _ =>
          pow_le_exp_mul38 (hQ _ (hjj i) x) (hspos i) _
    _ = (∏ i, (((2 * p i).factorial : ℝ) / s i ^ (2 * p i))) *
          Real.exp (∑ i, s i * Q (jj i) x) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
          (Finset.prod_nonneg fun i _ => by have := hspos i; positivity)
        calc ∑ i, s i * Q (jj i) x ≤ ∑ _i : Fin n, H / ((n : ℝ) + 1) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [hs]
              simp only
              rw [div_mul_eq_mul_div]
              exact div_le_div_of_nonneg_right (hsingle i) (by positivity)
          _ = (n : ℝ) / ((n : ℝ) + 1) * H := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
          _ ≤ H := by
              have : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
                rw [div_le_one (by positivity)]; linarith
              nlinarith

end Products

end NlsGge.Birkhoff
end
