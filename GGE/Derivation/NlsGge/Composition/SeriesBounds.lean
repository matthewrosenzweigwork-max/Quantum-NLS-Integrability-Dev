import Mathlib

/-!
# Cauchy-type bounds for formal multilinear series (composition, derivatives, change of origin)

Source: `paper/v2.tex` lines 1455-1462 (uniform bounds `‖D^k F / k!‖ ≤ M ρ^{-k}` near a compact
set), real-analytic route via power-series composition.

* `norm_comp_le` : `‖q.comp p n‖ ≤ M * (2 * max 1 (L / R) / σ) ^ n`.
* `norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall` : `‖D^n f x‖ ≤ n! * ‖p n‖`.
* `norm_iteratedFDerivSeries_le` : `‖p.iteratedFDerivSeries k j‖ ≤ ((j+k)!/j!) * ‖p (j+k)‖`.
* `norm_changeOrigin_le` : uniform bound of `p.changeOrigin z` for `‖z‖ ≤ ρ/4`.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.Composition

open FormalMultilinearSeries

/-! ### (D1) Composition -/

section D1

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Bound for one composition term. -/
theorem norm_compAlongComposition_le (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F)
    {M R L σ : ℝ} (hM : 0 ≤ M) (hR : 0 < R) (hL : 0 ≤ L) (hσ : 0 < σ)
    (hq : ∀ j, ‖q j‖ ≤ M * R⁻¹ ^ j) (hp : ∀ m, 1 ≤ m → ‖p m‖ ≤ L * σ⁻¹ ^ m)
    {n : ℕ} (c : Composition n) :
    ‖q.compAlongComposition p c‖ ≤ M * (max 1 (L / R) / σ) ^ n := by
  have h1 := q.compAlongComposition_norm p c
  have hprod : ∏ i, ‖p (c.blocksFun i)‖ ≤ ∏ i : Fin c.length, L * σ⁻¹ ^ (c.blocksFun i) :=
    Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hp _ (c.one_le_blocksFun i))
  have hprod2 : ∏ i : Fin c.length, L * σ⁻¹ ^ (c.blocksFun i) = L ^ c.length * σ⁻¹ ^ n := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, c.sum_blocksFun]
    simp
  have hLR : 0 ≤ L / R := div_nonneg hL hR.le
  have hmax : 1 ≤ max 1 (L / R) := le_max_left _ _
  have hk : (L / R) ^ c.length ≤ (max 1 (L / R)) ^ n :=
    calc (L / R) ^ c.length ≤ (max 1 (L / R)) ^ c.length :=
          pow_le_pow_left₀ hLR (le_max_right _ _) _
      _ ≤ (max 1 (L / R)) ^ n := pow_le_pow_right₀ hmax c.length_le
  calc ‖q.compAlongComposition p c‖
      ≤ ‖q c.length‖ * ∏ i, ‖p (c.blocksFun i)‖ := h1
    _ ≤ (M * R⁻¹ ^ c.length) * (L ^ c.length * σ⁻¹ ^ n) := by
        rw [← hprod2]
        exact mul_le_mul (hq _) hprod (Finset.prod_nonneg fun i _ => norm_nonneg _)
          (by positivity)
    _ = M * (L / R) ^ c.length * σ⁻¹ ^ n := by
        ring
    _ ≤ M * (max 1 (L / R)) ^ n * σ⁻¹ ^ n := by gcongr
    _ = M * (max 1 (L / R) / σ) ^ n := by
        ring

/-- (D1) Geometric bound for the composition of formal multilinear series. -/
theorem norm_comp_le (q : FormalMultilinearSeries ℝ F G) (p : FormalMultilinearSeries ℝ E F)
    {M R L σ : ℝ} (hM : 0 ≤ M) (hR : 0 < R) (hL : 0 ≤ L) (hσ : 0 < σ)
    (hq : ∀ j, ‖q j‖ ≤ M * R⁻¹ ^ j) (hp : ∀ m, 1 ≤ m → ‖p m‖ ≤ L * σ⁻¹ ^ m) (n : ℕ) :
    ‖q.comp p n‖ ≤ M * (2 * max 1 (L / R) / σ) ^ n := by
  have hterm := fun c : Composition n => norm_compAlongComposition_le q p hM hR hL hσ hq hp c
  have hsum : ‖q.comp p n‖ ≤ ∑ c : Composition n, ‖q.compAlongComposition p c‖ :=
    norm_sum_le _ _
  have hcard : ((Fintype.card (Composition n) : ℕ) : ℝ) ≤ 2 ^ n := by
    rw [composition_card]
    have : 2 ^ (n - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
    exact_mod_cast this
  calc ‖q.comp p n‖ ≤ ∑ c : Composition n, ‖q.compAlongComposition p c‖ := hsum
    _ ≤ ∑ _c : Composition n, M * (max 1 (L / R) / σ) ^ n := Finset.sum_le_sum fun c _ => hterm c
    _ = (Fintype.card (Composition n) : ℝ) * (M * (max 1 (L / R) / σ) ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * (M * (max 1 (L / R) / σ) ^ n) := by
        gcongr
    _ = M * (2 * max 1 (L / R) / σ) ^ n := by
        ring

end D1

/-! ### (D2) Iterated derivative -/

section D2

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- (D2) Norm of the iterated Fréchet derivative of a function given by a power series. -/
theorem norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall [CompleteSpace F]
    {f : E → F} {p : FormalMultilinearSeries ℝ E F} {x : E} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f p x r) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ n.factorial * ‖p n‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [h.iteratedFDeriv_eq_sum_of_completeSpace v]
  calc ‖∑ σ : Equiv.Perm (Fin n), p n (fun i => v (σ i))‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖p n (fun i => v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ := by
        refine Finset.sum_le_sum fun σ _ => ?_
        refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
        rw [Equiv.prod_comp σ (fun i => ‖v i‖)]
    _ = n.factorial * ‖p n‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        ring

end D2

/-! ### (D3) Derivative series -/

section D3

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Norm of the `k`-th `changeOriginSeries` term: binomial coefficient times `‖p (k+l)‖`. -/
theorem norm_changeOriginSeries_le (p : FormalMultilinearSeries ℝ E F) (k l : ℕ) :
    ‖p.changeOriginSeries k l‖ ≤ ((k + l).choose l : ℝ) * ‖p (k + l)‖ := by
  unfold FormalMultilinearSeries.changeOriginSeries
  refine (norm_sum_le (Finset.univ : Finset { s : Finset (Fin (k + l)) // s.card = l })
    (fun t => p.changeOriginSeriesTerm k l t t.2)).trans ?_
  simp_rw [FormalMultilinearSeries.norm_changeOriginSeriesTerm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : Fintype.card { s : Finset (Fin (k + l)) // s.card = l } = (k + l).choose l := by
    rw [Fintype.card_finset_len, Fintype.card_fin]
  rw [this]

/-- Norm of the derivative series. -/
theorem norm_derivSeries_le (p : FormalMultilinearSeries ℝ E F) (j : ℕ) :
    ‖p.derivSeries j‖ ≤ ((j : ℝ) + 1) * ‖p (j + 1)‖ := by
  have h1 : ‖p.derivSeries j‖ ≤ ‖p.changeOriginSeries 1 j‖ := by
    unfold FormalMultilinearSeries.derivSeries
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)
  refine h1.trans ((norm_changeOriginSeries_le p 1 j).trans ?_)
  have hc : ((1 + j).choose j : ℝ) = (j : ℝ) + 1 := by
    rw [add_comm 1 j, Nat.choose_succ_self_right]; push_cast; ring
  rw [hc, add_comm 1 j]

/-- Postcomposition with a linear isometry equivalence does not increase the norm of a
coefficient of a formal multilinear series. -/
theorem norm_compFormalMultilinearSeries_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : F ≃ₗᵢ[ℝ] G) (p : FormalMultilinearSeries ℝ E F) (j : ℕ) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries p j‖
      ≤ ‖p j‖ := by
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

/-- (D3) Norm of the coefficients of the series of the `k`-th derivative. -/
theorem norm_iteratedFDerivSeries_le (p : FormalMultilinearSeries ℝ E F) (k j : ℕ) :
    ‖p.iteratedFDerivSeries k j‖ ≤
      (((j + k).factorial : ℝ) / (j.factorial : ℝ)) * ‖p (j + k)‖ := by
  induction k generalizing j with
  | zero =>
    simp only [FormalMultilinearSeries.iteratedFDerivSeries]
    refine (norm_compFormalMultilinearSeries_le _ p j).trans ?_
    have : ((j.factorial : ℝ)) ≠ 0 := by positivity
    simp [this]
  | succ k ih =>
    simp only [FormalMultilinearSeries.iteratedFDerivSeries]
    refine (norm_compFormalMultilinearSeries_le _ (p.iteratedFDerivSeries k).derivSeries
      j).trans ?_
    have h2 := norm_derivSeries_le (p.iteratedFDerivSeries k) j
    have h3 := ih (j + 1)
    have hidx : j + 1 + k = j + (k + 1) := by omega
    rw [hidx] at h3
    refine h2.trans ?_
    have h4 : ((j : ℝ) + 1) * ‖(p.iteratedFDerivSeries k) (j + 1)‖ ≤
        ((j : ℝ) + 1) * (((j + (k + 1)).factorial : ℝ) / ((j + 1).factorial : ℝ) *
          ‖p (j + (k + 1))‖) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    refine h4.trans (le_of_eq ?_)
    have hj : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hj0 : ((j.factorial : ℝ)) ≠ 0 := by positivity
    rw [hj]
    field_simp

end D3

/-! ### (D4) Change of origin -/

section D4

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A single term of the change-of-origin expansion. -/
theorem norm_changeOriginSeries_apply_le (p : FormalMultilinearSeries ℝ E F) (k l : ℕ) (z : E) :
    ‖p.changeOriginSeries k l (fun _ => z)‖ ≤
      ((k + l).choose l : ℝ) * ‖p (k + l)‖ * ‖z‖ ^ l := by
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact norm_changeOriginSeries_le p k l

/-- (D4) Uniform bound for the change of origin: if `‖p n‖ ≤ C ρ⁻ⁿ` for all `n` and
`‖z‖ ≤ ρ / 4`, then `‖p.changeOrigin z n‖ ≤ 2 C (2/ρ)ⁿ`. The constant `ρ / 4` comes from the crude
estimate `(n+l).choose l ≤ 2^(n+l)`. -/
theorem norm_changeOrigin_le (p : FormalMultilinearSeries ℝ E F) {C ρ : ℝ} (hρ : 0 < ρ)
    (hp : ∀ n, ‖p n‖ ≤ C * ρ⁻¹ ^ n) {z : E} (hz : ‖z‖ ≤ ρ / 4) (n : ℕ) :
    ‖p.changeOrigin z n‖ ≤ 2 * C * (2 / ρ) ^ n := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (p 0)).trans (hp 0)
  have hgeom : HasSum (fun l : ℕ => C * (2 / ρ) ^ n * (1 / 2 : ℝ) ^ l)
      (C * (2 / ρ) ^ n * 2) := by
    have := hasSum_geometric_two.mul_left (C * (2 / ρ) ^ n)
    simpa [one_div] using this
  have hterm : ∀ l : ℕ, ‖p.changeOriginSeries n l (fun _ => z)‖ ≤
      C * (2 / ρ) ^ n * (1 / 2 : ℝ) ^ l := by
    intro l
    refine (norm_changeOriginSeries_apply_le p n l z).trans ?_
    have hch : ((n + l).choose l : ℝ) ≤ 2 ^ (n + l) := by
      exact_mod_cast Nat.choose_le_two_pow (n + l) l
    have hz' : ‖z‖ ^ l ≤ (ρ / 4) ^ l := pow_le_pow_left₀ (norm_nonneg _) hz l
    have h1 : ((n + l).choose l : ℝ) * ‖p (n + l)‖ ≤ 2 ^ (n + l) * (C * ρ⁻¹ ^ (n + l)) :=
      mul_le_mul hch (hp _) (norm_nonneg _) (by positivity)
    calc ((n + l).choose l : ℝ) * ‖p (n + l)‖ * ‖z‖ ^ l
        ≤ (2 ^ (n + l) * (C * ρ⁻¹ ^ (n + l))) * (ρ / 4) ^ l :=
          mul_le_mul h1 hz' (by positivity) (by positivity)
      _ = C * (2 / ρ) ^ n * ((ρ⁻¹ * ρ) ^ l * ((2 : ℝ) * (1 / 4 : ℝ)) ^ l) := by
          rw [div_eq_mul_inv ρ 4, div_eq_mul_inv 2 ρ, mul_pow ρ⁻¹ ρ l, mul_pow 2 (1 / 4 : ℝ) l]
          ring
      _ = C * (2 / ρ) ^ n * (1 / 2 : ℝ) ^ l := by
          rw [inv_mul_cancel₀ hρ.ne']
          norm_num
  have := tsum_of_norm_bounded hgeom hterm
  simpa [FormalMultilinearSeries.changeOrigin, FormalMultilinearSeries.sum, mul_assoc,
    mul_comm, mul_left_comm] using this

end D4

end NlsGge.Composition
