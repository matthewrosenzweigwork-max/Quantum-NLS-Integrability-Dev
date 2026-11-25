import QuantumNLS.AnalyticIdentity

/-!
# DEF-017 (`def:report-17`): real analyticity, literal polynomial-series form

Source: `source-text/chapters/definitions.tex`, lines 103-105 (sha256 `abe7643b…`):

> A Hilbert-space map is real analytic if, near each input, it has a norm-convergent series of
> continuous real homogeneous polynomials, or equivalently a local holomorphic extension after
> complexification. A finite-loss derivative assertion from `h^S` to `H^r` specifies both orders
> and the number of derivatives. It does not imply analyticity from `h^r` to `H^r`.

Graph: `dependency_edges.json` has one incoming edge, `DEF-002 → DEF-017` (definitions ledger,
the `H^s` / `h^s` spaces). It enters only through the finite-loss sentence, which is recorded
as a convention below; no Lean object of DEF-002 is used.

## Realization, clause by clause
* "continuous real homogeneous polynomial of degree `n`": `IsContHomPoly n P` — `P` continuous
  and `P h = A (h, …, h)` for an (algebraic) real `n`-linear `A`. `isContHomPoly_iff`: the same
  as being the diagonal of a *continuous* multilinear map (polarization).
* "near each input, a norm-convergent series": `IsRealAnalyticPoly f x` — there are such `Pₙ` and
  `r > 0` with `∑ₙ Pₙ (y - x) → f y` in the norm of `F` for every `‖y - x‖ < r`;
  `IsRealAnalyticMap f := ∀ x, IsRealAnalyticPoly f x`.
* Bridge (Terra round 53, gap G1): `analyticAt_iff_isRealAnalyticPoly` —
  `AnalyticAt ℝ f x ↔ IsRealAnalyticPoly f x` for real normed `E`, `F` with `E` complete (real
  Hilbert spaces in particular; `F` need not be complete).
  - (⇒) diagonal evaluation; the radius is preserved
    (`isRealAnalyticPoly_of_hasFPowerSeriesOnBall`).
  - (⇐) polarization: `Sym A = (1/n!) ∑_σ A ∘ σ` has `‖Sym A‖ ≤ (nⁿ/n!) · M ≤ eⁿ M` when
    `‖A(h,…,h)‖ ≤ M ‖h‖ⁿ` (`norm_symC_le`). Under a uniform bound `‖Pₙ h‖ ≤ C (‖h‖/R)ⁿ` the
    symmetrized series represents `f` on the ball of radius `R / e`
    (`hasFPowerSeriesOnBall_symSeries`): the radius shrinks by the factor `e`. Under the literal
    pointwise convergence, Baire category on the complete space `E` first produces such a bound
    on some smaller ball whose radius is not controlled by `r`. The conclusion is then only
    `AnalyticAt` (`analyticAt_of_isRealAnalyticPoly`).
  - Reading robustness: with "norm-convergent" read as normal convergence
    (`IsRealAnalyticPolyNormal`), the equivalence holds with no completeness assumption
    (`analyticAt_iff_isRealAnalyticPolyNormal`).
  - Both polarization and the Baire step use one finite-difference identity, `diff_identity`:
    `∑_{T ⊆ [n]} (-1)^{n-|T|} A(y + ∑_{i∈T} xᵢ, …) = ∑_σ A(x_{σ 1}, …, x_{σ n})`.
* Complexification clause: `HasLocalHolomorphicExtension ι ιF f x`. Complexification structure
  maps are `ι : E → EC` and `ιF : F → FC`, with a real part `re`, `re ∘ ιF = id`. The extension is
  `g` with `AnalyticAt ℂ g (ι x)` and `g ∘ ι = ιF ∘ f` near `x`. The direction
  holomorphic-extension ⇒ real analytic is proved for every such datum
  (`analyticAt_of_hasLocalHolomorphicExtension`, `isRealAnalyticPoly_of_hasLocalHolomorphicExtension`).
  Not proved:
  - the converse (real analytic ⇒ extension), which needs a concrete complexification of a real
    Hilbert space and the complex-multilinear extension of each `Sym Aₙ` (absent at the pin);
  - reading "holomorphic" as complex Fréchet differentiability on an open set of a complex Banach
    space, since Mathlib proves holomorphic ⇒ analytic only for domain `ℂ`.
* Finite-loss sentences: recorded as a **convention**, not a mathematical clause. They fix what
  a finite-loss assertion `h^S → H^r` must specify (both orders, the number of derivatives), and
  they forbid reading it as analyticity `h^r → H^r`. They name no map and no quantified
  statement, so there is nothing to formalize as a theorem.
* R-2535E8FD restated with the literal predicate: `identity_of_vanishing_ball_poly` (from the
  frozen `AnalyticIdentity.identity_of_vanishing_ball`, sha256 `6ccae64e…`, read-only, through
  the bridge).

No `sorry`, `admit`, new axioms or `native_decide`.
-/

namespace QuantumNLS.RealAnalyticDef

open Filter Topology Finset

section Combinatorics

/-- Inclusion-exclusion coefficient: `∑_{T ⊇ R} (-1)^{n-|T|} = [R = univ]`. -/
theorem coeff_sum {n : ℕ} (R : Finset (Fin n)) :
    ∑ T : Finset (Fin n), (if R ⊆ T then (-1 : ℝ) ^ (n - T.card) else 0)
      = if R = univ then 1 else 0 := by
  classical
  have h0 : ∑ T : Finset (Fin n), (if R ⊆ T then (-1 : ℝ) ^ (n - T.card) else 0)
      = ∑ V : Finset (Fin n), (if R ⊆ Vᶜ then (-1 : ℝ) ^ (n - Vᶜ.card) else 0) :=
    (Fintype.sum_equiv (compl_involutive.toPerm _) _ _ (fun V => rfl)).symm
  rw [h0]
  have h1 : ∀ V : Finset (Fin n), (if R ⊆ Vᶜ then (-1 : ℝ) ^ (n - Vᶜ.card) else 0)
      = if V ⊆ Rᶜ then (-1 : ℝ) ^ V.card else 0 := by
    intro V
    have hc : n - Vᶜ.card = V.card := by
      rw [card_compl, Fintype.card_fin]
      have := card_le_univ V; rw [Fintype.card_fin] at this; omega
    rw [hc]
    have hiff : R ⊆ Vᶜ ↔ V ⊆ Rᶜ := subset_compl_comm
    simp only [hiff]
  simp_rw [h1]
  rw [← sum_filter]
  have h2 : (univ.filter fun V : Finset (Fin n) => V ⊆ Rᶜ) = Rᶜ.powerset := by
    ext V; simp
  rw [h2]
  have h3 := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card (x := Rᶜ))
  push_cast at h3
  rw [h3]
  simp [compl_eq_empty_iff]


variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Finite-difference identity for an `n`-linear map with an arbitrary base point `y`:
`∑_{T ⊆ [n]} (-1)^{n-|T|} A(y + ∑_{i∈T} xᵢ, …, y + ∑_{i∈T} xᵢ) = ∑_σ A(x_{σ 1}, …, x_{σ n})`. -/
theorem diff_identity {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F) (y : E)
    (x : Fin n → E) :
    ∑ T : Finset (Fin n), ((-1 : ℝ) ^ (n - T.card)) • A (fun _ => y + ∑ i ∈ T, x i)
      = ∑ σ : Equiv.Perm (Fin n), A (fun k => x (σ k)) := by
  classical
  let w : Finset (Fin n) → Option (Fin n) → E := fun T j =>
    Option.elim j y (fun l => if l ∈ T then x l else 0)
  have hw : ∀ T, y + ∑ i ∈ T, x i = ∑ j, w T j := by
    intro T; rw [Fintype.sum_option]; simp [w, Finset.sum_ite_mem]
  have hexp : ∀ T, A (fun _ => y + ∑ i ∈ T, x i)
      = ∑ r : Fin n → Option (Fin n), A (fun k => w T (r k)) := by
    intro T; simp_rw [hw T]; exact A.map_sum (fun _ j => w T j)
  let Rr : (Fin n → Option (Fin n)) → Finset (Fin n) := fun r =>
    univ.filter (fun l => ∃ k, r k = some l)
  obtain ⟨B, hB⟩ : ∃ B : (Fin n → Option (Fin n)) → F,
      ∀ r, B r = A (fun k => w univ (r k)) := ⟨_, fun _ => rfl⟩
  have hterm : ∀ T r, A (fun k => w T (r k))
      = if Rr r ⊆ T then B r else 0 := by
    intro T r
    split_ifs with h
    · rw [hB]; congr 1; funext k
      cases hk : r k with
      | none => simp [w]
      | some l =>
        have : l ∈ T := h (by simp only [Rr, mem_filter, mem_univ, true_and]; exact ⟨k, hk⟩)
        simp [w, this]
    · obtain ⟨l, hl, hlT⟩ := not_subset.mp h
      simp only [Rr, mem_filter, mem_univ, true_and] at hl
      obtain ⟨k, hk⟩ := hl
      exact A.map_coord_zero k (by show w T (r k) = 0; rw [hk]; simp only [w, Option.elim_some, hlT, ite_false])
  simp_rw [hexp, Finset.smul_sum, hterm]
  rw [Finset.sum_comm]
  have hcoef : ∀ r, ∑ T : Finset (Fin n), ((-1 : ℝ) ^ (n - T.card)) •
      (if Rr r ⊆ T then B r else 0)
      = (if Rr r = univ then (1 : ℝ) else 0) • B r := by
    intro r; rw [← coeff_sum (Rr r), Finset.sum_smul]
    refine sum_congr rfl fun T _ => ?_
    split_ifs <;> simp
  simp_rw [hcoef, ite_smul, one_smul, zero_smul]
  rw [← sum_filter]
  symm
  refine sum_bij (fun σ _ => fun k => some (σ k)) ?_ ?_ ?_ ?_
  · intro σ _
    simp only [mem_filter, mem_univ, true_and]
    ext l; simp only [Rr, mem_filter, mem_univ, true_and, iff_true]
    exact ⟨σ.symm l, by simp⟩
  · intro σ _ τ _ h
    exact Equiv.ext fun k => Option.some_injective _ (congrFun h k)
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    have hs : ∀ l, ∃ k, r k = some l := by
      intro l
      have : l ∈ Rr r := by rw [hr]; exact mem_univ l
      simpa [Rr] using this
    choose s hs using hs
    have sinj : Function.Injective s := by
      intro l1 l2 h
      have := (hs l1).symm.trans ((congrArg r h).trans (hs l2))
      exact Option.some_injective _ this
    have sbij : Function.Bijective s := ⟨sinj, Finite.injective_iff_surjective.mp sinj⟩
    refine ⟨(Equiv.ofBijective s sbij).symm, mem_univ _, ?_⟩
    funext k
    have hk : s ((Equiv.ofBijective s sbij).symm k) = k :=
      (Equiv.ofBijective s sbij).apply_symm_apply k
    rw [← hs ((Equiv.ofBijective s sbij).symm k), hk]
  · intro σ _
    rw [hB]; simp [w]

end Combinatorics

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### DEF-017, literal predicates -/

/-- A **continuous real homogeneous polynomial of degree `n`** from `E` to `F`: a continuous map
which is the diagonal `h ↦ A (h, …, h)` of some (algebraic) real `n`-linear map `A`. -/
def IsContHomPoly (n : ℕ) (P : E → F) : Prop :=
  Continuous P ∧ ∃ A : MultilinearMap ℝ (fun _ : Fin n => E) F, ∀ h, P h = A (fun _ => h)

/-- DEF-017, literal form at the input `x`: there are continuous real homogeneous polynomials
`P n` of degree `n` and a radius `r > 0` such that, for every `y` with `‖y - x‖ < r`, the series
`∑ₙ P n (y - x)` converges in the norm of `F` (its partial sums tend to `f y`). -/
def IsRealAnalyticPoly (f : E → F) (x : E) : Prop :=
  ∃ P : ℕ → E → F, (∀ n, IsContHomPoly n (P n)) ∧ ∃ r : ℝ, 0 < r ∧
    ∀ y, ‖y - x‖ < r →
      Tendsto (fun N => ∑ n ∈ range N, P n (y - x)) atTop (𝓝 (f y))

/-- DEF-017: a map is real analytic if it has such a series near each input. -/
def IsRealAnalyticMap (f : E → F) : Prop := ∀ x, IsRealAnalyticPoly f x

/-! ### Homogeneity, symmetrization and polarization -/

theorem diag_smul {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F) (t : ℝ) (h : E) :
    A (fun _ => t • h) = t ^ n • A (fun _ => h) := by
  have := A.map_smul_univ (fun _ => t) (fun _ => h)
  simpa [Finset.prod_const, Finset.card_univ] using this

/-- Polarization (sum form): if `‖A (h,…,h)‖ ≤ M ‖h‖ⁿ` then the permutation sum of `A` is bounded
by `M (∑ ‖mᵢ‖)ⁿ`. Proof: `diff_identity` with base point `-(1/2)∑ mᵢ`. -/
theorem norm_sum_perm_le {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ h, ‖A (fun _ => h)‖ ≤ M * ‖h‖ ^ n) (m : Fin n → E) :
    ‖∑ σ : Equiv.Perm (Fin n), A (fun k => m (σ k))‖ ≤ M * (∑ i, ‖m i‖) ^ n := by
  classical
  rw [← diff_identity A (-((1 / 2 : ℝ) • ∑ i, m i)) m]
  have hpt : ∀ T : Finset (Fin n),
      ‖-((1 / 2 : ℝ) • ∑ i, m i) + ∑ i ∈ T, m i‖ ≤ (1 / 2) * ∑ i, ‖m i‖ := by
    intro T
    have e1 : ∑ i ∈ T, m i = ∑ i, if i ∈ T then m i else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have e2 : -((1 / 2 : ℝ) • ∑ i, m i) + ∑ i ∈ T, m i
        = ∑ i, (if i ∈ T then (1 / 2 : ℝ) else -(1 / 2)) • m i := by
      rw [e1, Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> module
    rw [e2, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_smul]
    split_ifs <;> norm_num
  have hcard : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  calc ‖∑ T : Finset (Fin n), ((-1 : ℝ) ^ (n - T.card)) •
          A (fun _ => -((1 / 2 : ℝ) • ∑ i, m i) + ∑ i ∈ T, m i)‖
      ≤ ∑ T : Finset (Fin n), ‖((-1 : ℝ) ^ (n - T.card)) •
          A (fun _ => -((1 / 2 : ℝ) • ∑ i, m i) + ∑ i ∈ T, m i)‖ := norm_sum_le _ _
    _ ≤ ∑ _T : Finset (Fin n), M * ((1 / 2) * ∑ i, ‖m i‖) ^ n := by
        refine Finset.sum_le_sum fun T _ => ?_
        rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact (hM _).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hpt T) n) hM0)
    _ = M * (∑ i, ‖m i‖) ^ n := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_pow]
        have h2 : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
        push_cast
        calc (2 : ℝ) ^ n * (M * ((1 / 2) ^ n * (∑ i, ‖m i‖) ^ n))
            = M * (∑ i, ‖m i‖) ^ n * ((2 : ℝ) ^ n * (1 / 2) ^ n) := by ring
          _ = M * (∑ i, ‖m i‖) ^ n := by rw [h2, mul_one]

/-- The symmetrization `(1/n!) ∑_σ A ∘ σ` of an algebraic multilinear map. -/
noncomputable def symM {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F) :
    MultilinearMap ℝ (fun _ : Fin n => E) F :=
  ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), A.domDomCongr σ

theorem symM_apply {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F) (m : Fin n → E) :
    symM A m = ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), A (fun k => m (σ k)) := by
  simp [symM, MultilinearMap.domDomCongr_apply]

theorem symM_diag {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F) (h : E) :
    symM A (fun _ => h) = A (fun _ => h) := by
  rw [symM_apply, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- Polarization bound: `‖Sym A (m)‖ ≤ (nⁿ/n!) M ∏ ‖mᵢ‖` when `‖A (h,…,h)‖ ≤ M ‖h‖ⁿ`. -/
theorem norm_symM_le {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ h, ‖A (fun _ => h)‖ ≤ M * ‖h‖ ^ n) (m : Fin n → E) :
    ‖symM A m‖ ≤ ((n : ℝ) ^ n / n.factorial * M) * ∏ i, ‖m i‖ := by
  have hC : 0 ≤ (n : ℝ) ^ n / n.factorial * M := by positivity
  by_cases hz : ∃ i, m i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [(symM A).map_coord_zero i hi, norm_zero]
    exact mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  simp only [not_exists] at hz
  set u : Fin n → E := fun i => ‖m i‖⁻¹ • m i with hu
  have hmu : m = fun i => ‖m i‖ • u i := by
    funext i; simp only [hu, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hz i)), one_smul]
  have hunit : ∀ i, ‖u i‖ = 1 := fun i => by
    simp only [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hz i))]
  have hsu : ‖symM A u‖ ≤ (n : ℝ) ^ n / n.factorial * M := by
    rw [symM_apply, norm_smul, norm_inv, Real.norm_natCast]
    have := norm_sum_perm_le A hM0 hM u
    simp only [hunit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at this
    calc (n.factorial : ℝ)⁻¹ * ‖∑ σ : Equiv.Perm (Fin n), A (fun k => u (σ k))‖
        ≤ (n.factorial : ℝ)⁻¹ * (M * (n : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (n : ℝ) ^ n / n.factorial * M := by ring
  calc ‖symM A m‖ = ‖symM A (fun i => ‖m i‖ • u i)‖ := by rw [← hmu]
    _ = (∏ i, ‖m i‖) * ‖symM A u‖ := by
        rw [(symM A).map_smul_univ, norm_smul, Real.norm_of_nonneg
          (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
    _ ≤ (∏ i, ‖m i‖) * ((n : ℝ) ^ n / n.factorial * M) :=
        mul_le_mul_of_nonneg_left hsu (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

theorem pow_div_factorial_le_exp_one_pow (n : ℕ) :
    (n : ℝ) ^ n / n.factorial ≤ Real.exp 1 ^ n := by
  rw [Real.exp_one_pow]; exact Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg n) n

/-- A homogeneous polynomial bounded by `K` on the ball of radius `δ` about `0` satisfies
`‖A(h,…,h)‖ ≤ K (2/δ)ⁿ ‖h‖ⁿ` everywhere. -/
theorem homog_bound {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F) {δ K : ℝ}
    (hδ : 0 < δ) (hK : ∀ h, ‖h‖ < δ → ‖A (fun _ => h)‖ ≤ K) (h : E) :
    ‖A (fun _ => h)‖ ≤ K * (2 / δ) ^ n * ‖h‖ ^ n := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simpa using hδ))
  by_cases h0 : h = 0
  · subst h0
    cases n with
    | zero => simpa using hK 0 (by simpa using hδ)
    | succ k =>
      rw [A.map_coord_zero (0 : Fin (k + 1)) rfl, norm_zero, norm_zero,
        zero_pow (Nat.succ_ne_zero k), mul_zero]
  · have hh : 0 < ‖h‖ := norm_pos_iff.mpr h0
    set t : ℝ := δ / (2 * ‖h‖) with ht
    have htpos : 0 < t := by positivity
    have hth : ‖t • h‖ < δ := by
      rw [norm_smul, Real.norm_of_nonneg htpos.le, ht]
      field_simp
      linarith
    have key : t ^ n * ‖A (fun _ => h)‖ ≤ K := by
      have := hK _ hth
      rwa [diag_smul, norm_smul, norm_pow, Real.norm_of_nonneg htpos.le] at this
    have htinv : t⁻¹ = 2 / δ * ‖h‖ := by rw [ht]; field_simp
    calc ‖A (fun _ => h)‖ = (t⁻¹) ^ n * (t ^ n * ‖A (fun _ => h)‖) := by
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ htpos.ne', one_pow, one_mul]
      _ ≤ (t⁻¹) ^ n * K := mul_le_mul_of_nonneg_left key (by positivity)
      _ = K * (2 / δ) ^ n * ‖h‖ ^ n := by rw [htinv, mul_pow]; ring

/-- Off-centre bound: a homogeneous polynomial bounded by `K` on a ball `B(h₀, δ)` is bounded by
`K (2e)ⁿ` on `B(0, δ)`. Proof: `diff_identity` with base point `h₀` and increments `h/n`. -/
theorem shifted_bound {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F) {h0 : E}
    {δ K : ℝ} (hK : ∀ z, ‖z - h0‖ < δ → ‖A (fun _ => z)‖ ≤ K) (h : E) (hh : ‖h‖ < δ) :
    ‖A (fun _ => h)‖ ≤ K * (2 * Real.exp 1) ^ n := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK h0 (by simpa using (norm_nonneg h).trans_lt hh))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : (fun _ : Fin 0 => h) = (fun _ => h0) := Subsingleton.elim _ _
    rw [this, pow_zero, mul_one]
    exact hK h0 (by simpa using (norm_nonneg h).trans_lt hh)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hid := diff_identity A h0 (fun _ => (n : ℝ)⁻¹ • h)
  have hrhs : ∑ σ : Equiv.Perm (Fin n), A (fun _ => (n : ℝ)⁻¹ • h)
      = ((n.factorial : ℝ) * ((n : ℝ) ^ n)⁻¹) • A (fun _ => h) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, diag_smul, smul_smul, inv_pow]
  rw [hrhs] at hid
  have hpt : ∀ T : Finset (Fin n), ‖A (fun _ => h0 + ∑ i ∈ T, (n : ℝ)⁻¹ • h)‖ ≤ K := by
    intro T
    apply hK
    rw [add_sub_cancel_left, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      norm_smul]
    have hT : (T.card : ℝ) ≤ n := by
      have := Finset.card_le_univ T; rw [Fintype.card_fin] at this; exact_mod_cast this
    have hc : ‖(T.card : ℝ) * (n : ℝ)⁻¹‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, div_le_one hnR]; exact hT
    calc ‖(T.card : ℝ) * (n : ℝ)⁻¹‖ * ‖h‖ ≤ 1 * ‖h‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < δ := by rwa [one_mul]
  have hcard : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  have hL : ‖((n.factorial : ℝ) * ((n : ℝ) ^ n)⁻¹) • A (fun _ => h)‖ ≤ 2 ^ n * K := by
    rw [← hid]
    calc _ ≤ ∑ T : Finset (Fin n), ‖((-1 : ℝ) ^ (n - T.card)) •
            A (fun _ => h0 + ∑ i ∈ T, (n : ℝ)⁻¹ • h)‖ := norm_sum_le _ _
      _ ≤ ∑ _T : Finset (Fin n), K := by
          refine Finset.sum_le_sum fun T _ => ?_
          rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]; exact hpt T
      _ = 2 ^ n * K := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
  have hfpos : (0 : ℝ) < n.factorial := by positivity
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at hL
  have hmain : ‖A (fun _ => h)‖ ≤ 2 ^ n * K * ((n : ℝ) ^ n / n.factorial) := by
    have hq : 0 < (n.factorial : ℝ) * ((n : ℝ) ^ n)⁻¹ := by positivity
    calc ‖A (fun _ => h)‖
        = ((n.factorial : ℝ) * ((n : ℝ) ^ n)⁻¹)⁻¹ *
            (((n.factorial : ℝ) * ((n : ℝ) ^ n)⁻¹) * ‖A (fun _ => h)‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]
      _ ≤ ((n.factorial : ℝ) * ((n : ℝ) ^ n)⁻¹)⁻¹ * (2 ^ n * K) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 2 ^ n * K * ((n : ℝ) ^ n / n.factorial) := by
          field_simp
  calc ‖A (fun _ => h)‖ ≤ 2 ^ n * K * ((n : ℝ) ^ n / n.factorial) := hmain
    _ ≤ 2 ^ n * K * Real.exp 1 ^ n :=
        mul_le_mul_of_nonneg_left (pow_div_factorial_le_exp_one_pow n) (by positivity)
    _ = K * (2 * Real.exp 1) ^ n := by rw [mul_pow]; ring

/-- Continuous homogeneous polynomials are exactly the diagonals of continuous multilinear
maps (the algebraic multilinear map is replaced by its symmetrization, which is bounded by
polarization). -/
theorem isContHomPoly_iff {n : ℕ} (P : E → F) :
    IsContHomPoly n P ↔
      ∃ A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F, ∀ h, P h = A (fun _ => h) := by
  constructor
  · rintro ⟨hPc, A, hA⟩
    obtain ⟨δ, hδ, hδP⟩ := Metric.continuousAt_iff.mp (hPc.continuousAt (x := 0)) 1 one_pos
    have hK : ∀ h, ‖h‖ < δ → ‖A (fun _ => h)‖ ≤ ‖P 0‖ + 1 := by
      intro h hh
      have := hδP (x := h) (by simpa [dist_eq_norm] using hh)
      rw [dist_eq_norm] at this
      rw [← hA]
      calc ‖P h‖ = ‖(P h - P 0) + P 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖P h - P 0‖ + ‖P 0‖ := norm_add_le _ _
        _ ≤ ‖P 0‖ + 1 := by linarith
    have hM0 : 0 ≤ (‖P 0‖ + 1) * (2 / δ) ^ n := by positivity
    have hM : ∀ h, ‖A (fun _ => h)‖ ≤ ((‖P 0‖ + 1) * (2 / δ) ^ n) * ‖h‖ ^ n :=
      fun h => homog_bound A hδ hK h
    refine ⟨(symM A).mkContinuous _ (norm_symM_le A hM0 hM), fun h => ?_⟩
    rw [MultilinearMap.coe_mkContinuous, symM_diag, hA]
  · rintro ⟨A, hA⟩
    refine ⟨?_, A.toMultilinearMap, fun h => hA h⟩
    have : P = fun h => A (fun _ => h) := funext hA
    rw [this]
    exact A.cont.comp (continuous_pi fun _ => continuous_id)

/-- Symmetrization of a continuous multilinear map. -/
noncomputable def symC {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F :=
  ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), A.domDomCongr σ

theorem symC_apply_eq {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (m : Fin n → E) : symC A m = symM A.toMultilinearMap m := by
  simp [symC, symM_apply, ContinuousMultilinearMap.domDomCongr_apply]

theorem symC_diag {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) (h : E) :
    symC A (fun _ => h) = A (fun _ => h) := by
  rw [symC_apply_eq, symM_diag]; rfl

/-- **Polarization norm bound**: `‖Sym A‖ ≤ (nⁿ/n!) · M` whenever `‖A (h,…,h)‖ ≤ M ‖h‖ⁿ`,
i.e. the symmetric multilinear norm is at most `nⁿ/n! ≤ eⁿ` times the polynomial norm. -/
theorem norm_symC_le {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ h, ‖A (fun _ => h)‖ ≤ M * ‖h‖ ^ n) :
    ‖symC A‖ ≤ (n : ℝ) ^ n / n.factorial * M :=
  ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => by
    rw [symC_apply_eq]; exact norm_symM_le A.toMultilinearMap hM0 hM m

/-- The formal multilinear series of symmetrizations. -/
noncomputable def symSeries (A : ∀ n : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    FormalMultilinearSeries ℝ E F := fun n => symC (A n)

end Normed

section Bridge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem diagC_smul {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) (t : ℝ)
    (h : E) : A (fun _ => t • h) = t ^ n • A (fun _ => h) :=
  diag_smul A.toMultilinearMap t h

/-- (⇒), radius preserved: the diagonals `h ↦ pₙ(h,…,h)` of a power series on the ball of
radius `r` are continuous homogeneous polynomials whose series converges in norm to `f y` for
every `‖y - x‖ < ρ`, for any real `ρ` with `ρ ≤ r`. -/
theorem isRealAnalyticPoly_of_hasFPowerSeriesOnBall {f : E → F}
    {p : FormalMultilinearSeries ℝ E F} {x : E} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f p x r) {ρ : ℝ} (hρ : ENNReal.ofReal ρ ≤ r) :
    (∀ n, IsContHomPoly n (fun h => p n (fun _ => h))) ∧
      ∀ y, ‖y - x‖ < ρ →
        Tendsto (fun N => ∑ n ∈ range N, p n (fun _ => y - x)) atTop (𝓝 (f y)) := by
  refine ⟨fun n => (isContHomPoly_iff _).2 ⟨p n, fun _ => rfl⟩, fun y hy => ?_⟩
  have hmem : y - x ∈ Metric.eball (0 : E) r := by
    rw [Metric.mem_eball]
    refine lt_of_lt_of_le ?_ hρ
    rw [edist_lt_ofReal, dist_zero_right]; exact hy
  have := (hp.hasSum hmem).tendsto_sum_nat
  rwa [add_sub_cancel] at this

/-- DEF-017 bridge, direction (⇒): Mathlib analyticity gives the literal polynomial series. -/
theorem isRealAnalyticPoly_of_analyticAt {f : E → F} {x : E} (hf : AnalyticAt ℝ f x) :
    IsRealAnalyticPoly f x := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨ρ, -, hρ0, hρr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp.r_pos
  have := isRealAnalyticPoly_of_hasFPowerSeriesOnBall hp hρr.le
  exact ⟨fun n h => p n (fun _ => h), this.1, ρ, ENNReal.ofReal_pos.mp hρ0, this.2⟩

/-- Quantitative (⇐) by polarization. If the homogeneous terms `Aₙ(h,…,h)` satisfy the uniform
geometric bound `‖Aₙ(h,…,h)‖ ≤ C (‖h‖/R)ⁿ` and the series converges in norm to `f (x + h)` for
`‖h‖ < R`, then the symmetrized multilinear series represents `f` on the ball of radius `R / e`
(its radius is at least `R / e`, from `‖Sym Aₙ‖ ≤ (nⁿ/n!) C R⁻ⁿ ≤ C (e/R)ⁿ`). -/
theorem hasFPowerSeriesOnBall_symSeries {f : E → F} {x : E}
    (A : ∀ n : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R) (hbound : ∀ n h, ‖A n (fun _ => h)‖ ≤ C * (‖h‖ / R) ^ n)
    (hsum : ∀ h, ‖h‖ < R →
      Tendsto (fun N => ∑ n ∈ range N, A n (fun _ => h)) atTop (𝓝 (f (x + h)))) :
    HasFPowerSeriesOnBall f (symSeries A) x (ENNReal.ofReal (R / Real.exp 1)) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hRe : 0 < R / Real.exp 1 := div_pos hR he
  have hnorm : ∀ n, ‖symSeries A n‖ ≤ C * (Real.exp 1 / R) ^ n := by
    intro n
    have hM : ∀ h, ‖A n (fun _ => h)‖ ≤ (C / R ^ n) * ‖h‖ ^ n := by
      intro h
      calc _ ≤ C * (‖h‖ / R) ^ n := hbound n h
        _ = (C / R ^ n) * ‖h‖ ^ n := by rw [div_pow]; ring
    calc ‖symSeries A n‖ ≤ (n : ℝ) ^ n / n.factorial * (C / R ^ n) :=
          norm_symC_le (A n) (by positivity) hM
      _ ≤ Real.exp 1 ^ n * (C / R ^ n) :=
          mul_le_mul_of_nonneg_right (pow_div_factorial_le_exp_one_pow n) (by positivity)
      _ = C * (Real.exp 1 / R) ^ n := by rw [div_pow]; ring
  refine ⟨?_, ENNReal.ofReal_pos.mpr hRe, fun {y} hy => ?_⟩
  · have : ENNReal.ofReal (R / Real.exp 1) = (((R / Real.exp 1).toNNReal : NNReal) : ENNReal) :=
      rfl
    rw [this]
    refine (symSeries A).le_radius_of_bound C fun n => ?_
    rw [Real.coe_toNNReal _ hRe.le]
    calc ‖symSeries A n‖ * (R / Real.exp 1) ^ n
        ≤ C * (Real.exp 1 / R) ^ n * (R / Real.exp 1) ^ n :=
          mul_le_mul_of_nonneg_right (hnorm n) (by positivity)
      _ = C * ((Real.exp 1 / R) * (R / Real.exp 1)) ^ n := by rw [mul_pow]; ring
      _ = C := by
          rw [div_mul_div_comm, mul_comm (Real.exp 1) R, div_self (by positivity), one_pow,
            mul_one]
  · rw [Metric.mem_eball, edist_lt_ofReal, dist_zero_right] at hy
    have hyR : ‖y‖ < R := hy.trans_le (div_le_self hR.le (by linarith [Real.add_one_le_exp 1]))
    have hdiag : ∀ n, symSeries A n (fun _ => y) = A n (fun _ => y) := fun n => symC_diag _ _
    simp_rw [hdiag]
    have hsumm : Summable fun n => ‖A n (fun _ => y)‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbound n y) ?_
      exact (summable_geometric_of_lt_one (by positivity) ((div_lt_one hR).mpr hyR)).mul_left C
    exact (hasSum_iff_tendsto_nat_of_summable_norm hsumm).mpr (hsum y hyR)

/-- DEF-017 bridge, direction (⇐), for a complete domain: the literal polynomial-series
predicate (pointwise norm convergence on a ball) implies Mathlib analyticity. Baire category
turns pointwise convergence into a geometric bound on a smaller ball (the resulting radius is
not controlled by `r`), and polarization (`hasFPowerSeriesOnBall_symSeries`) concludes. -/
theorem analyticAt_of_isRealAnalyticPoly [CompleteSpace E] {f : E → F} {x : E}
    (hf : IsRealAnalyticPoly f x) : AnalyticAt ℝ f x := by
  obtain ⟨P, hP, r, hr, hconv⟩ := hf
  choose A hA using fun n => (isContHomPoly_iff (P n)).1 (hP n)
  have hbdd : ∀ h : E, ‖h‖ < r → ∃ K : ℝ, ∀ n, ‖P n h‖ ≤ K := by
    intro h hh
    have hS := hconv (x + h) (by rwa [add_sub_cancel_left])
    rw [add_sub_cancel_left] at hS
    have ht : Tendsto (fun n => P n h) atTop (𝓝 0) := by
      have h1 := (hS.comp (tendsto_add_atTop_nat 1)).sub hS
      rw [sub_self] at h1
      refine h1.congr fun n => ?_
      simp [Function.comp, Finset.sum_range_succ]
    obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ ht)
    exact ⟨K, fun n => hK _ ⟨n, rfl⟩⟩
  let S : ℕ × ℕ → Set E := fun km => {h | ∀ n, ‖P n h‖ ≤ (km.1 : ℝ) * (km.2 : ℝ) ^ n}
  have hSc : ∀ km, IsClosed (S km) := by
    intro km
    simp only [S, Set.ofPred_forall]
    exact isClosed_iInter fun n => isClosed_le ((hP n).1.norm) continuous_const
  have hScov : ⋃ km, S km = Set.univ := by
    refine Set.eq_univ_of_forall fun h => Set.mem_iUnion.mpr ?_
    obtain ⟨m, hm⟩ := exists_nat_gt (‖h‖ / r)
    have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    have hh' : ‖(m : ℝ)⁻¹ • h‖ < r := by
      rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hm0]
      rw [div_lt_iff₀ hr] at hm
      linarith [mul_comm (m : ℝ) r]
    obtain ⟨K, hK⟩ := hbdd _ hh'
    obtain ⟨k, hk⟩ := exists_nat_ge K
    refine ⟨(k, m), fun n => ?_⟩
    calc ‖P n h‖ = (m : ℝ) ^ n * ‖P n ((m : ℝ)⁻¹ • h)‖ := by
          rw [hA n ((m : ℝ)⁻¹ • h), diagC_smul, norm_smul, norm_pow, norm_inv,
            Real.norm_natCast, ← hA n h, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hm0.ne',
            one_pow, one_mul]
      _ ≤ (m : ℝ) ^ n * k := mul_le_mul_of_nonneg_left ((hK n).trans hk) (by positivity)
      _ = (k : ℝ) * (m : ℝ) ^ n := by ring
  obtain ⟨⟨k, m⟩, h0, hh0⟩ := nonempty_interior_of_iUnion_of_closed hSc hScov
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hh0)
  have hloc : ∀ n h, ‖h‖ < δ →
      ‖A n (fun _ => h)‖ ≤ ((k : ℝ) * (m : ℝ) ^ n) * (2 * Real.exp 1) ^ n := by
    intro n h hh
    refine shifted_bound (A n).toMultilinearMap (h0 := h0) (fun z hz => ?_) h hh
    have hzS : z ∈ S (k, m) := hball (by rwa [Metric.mem_ball, dist_eq_norm])
    have := hzS n
    rwa [hA] at this
  set q : ℝ := ((m : ℝ) + 1) * (2 * Real.exp 1) * (2 / δ) with hq
  have hq0 : 0 < q := by positivity
  have hglob : ∀ n h, ‖A n (fun _ => h)‖ ≤ (k : ℝ) * (‖h‖ / q⁻¹) ^ n := by
    intro n h
    have h1 := homog_bound (A n).toMultilinearMap hδ (hloc n) h
    calc ‖A n (fun _ => h)‖
        ≤ ((k : ℝ) * (m : ℝ) ^ n) * (2 * Real.exp 1) ^ n * (2 / δ) ^ n * ‖h‖ ^ n := h1
      _ ≤ ((k : ℝ) * ((m : ℝ) + 1) ^ n) * (2 * Real.exp 1) ^ n * (2 / δ) ^ n * ‖h‖ ^ n := by
          gcongr
          linarith
      _ = (k : ℝ) * (‖h‖ / q⁻¹) ^ n := by rw [div_inv_eq_mul, hq]; simp only [mul_pow]; ring
  have hR : 0 < min q⁻¹ r := lt_min (inv_pos.mpr hq0) hr
  have hbound : ∀ n h, ‖A n (fun _ => h)‖ ≤ (k : ℝ) * (‖h‖ / min q⁻¹ r) ^ n := by
    intro n h
    refine (hglob n h).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left (norm_nonneg _) hR (min_le_left _ _)) n) (by positivity))
  have hsum : ∀ h, ‖h‖ < min q⁻¹ r →
      Tendsto (fun N => ∑ n ∈ range N, A n (fun _ => h)) atTop (𝓝 (f (x + h))) := by
    intro h hh
    have := hconv (x + h) (by rw [add_sub_cancel_left]; exact hh.trans_le (min_le_right _ _))
    simp only [add_sub_cancel_left, hA] at this
    exact this
  exact (hasFPowerSeriesOnBall_symSeries A (Nat.cast_nonneg k) hR hbound hsum).analyticAt

/-- **DEF-017 bridge (gap G1)**: for maps between real normed spaces with complete domain
(in particular real Hilbert spaces), Mathlib's `AnalyticAt ℝ` is equivalent to the literal
polynomial-series predicate. -/
theorem analyticAt_iff_isRealAnalyticPoly [CompleteSpace E] (f : E → F) (x : E) :
    AnalyticAt ℝ f x ↔ IsRealAnalyticPoly f x :=
  ⟨isRealAnalyticPoly_of_analyticAt, analyticAt_of_isRealAnalyticPoly⟩

theorem isRealAnalyticMap_iff [CompleteSpace E] (f : E → F) :
    IsRealAnalyticMap f ↔ ∀ x, AnalyticAt ℝ f x :=
  forall_congr' fun x => (analyticAt_iff_isRealAnalyticPoly f x).symm

/-- DEF-017 under the stronger reading "normally convergent": a uniform geometric bound
`‖Pₙ h‖ ≤ C (‖h‖/R)ⁿ` (hence `∑ₙ sup_{‖h‖ ≤ ρ} ‖Pₙ h‖ < ∞` for every `ρ < R`, and absolute
convergence) together with `HasSum` to `f y` for `‖y - x‖ < R`. -/
def IsRealAnalyticPolyNormal (f : E → F) (x : E) : Prop :=
  ∃ P : ℕ → E → F, (∀ n, IsContHomPoly n (P n)) ∧ ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧
    (∀ n h, ‖P n h‖ ≤ C * (‖h‖ / R) ^ n) ∧
    ∀ y, ‖y - x‖ < R → HasSum (fun n => P n (y - x)) (f y)

theorem isRealAnalyticPolyNormal_of_analyticAt {f : E → F} {x : E} (hf : AnalyticAt ℝ f x) :
    IsRealAnalyticPolyNormal f x := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨ρ, -, hρ0, hρr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp.r_pos
  have hρ : 0 < ρ := ENNReal.ofReal_pos.mp hρ0
  have hlt : ((ρ.toNNReal : NNReal) : ENNReal) < p.radius := lt_of_lt_of_le hρr hp.r_le
  obtain ⟨C, hC, hCb⟩ := p.norm_mul_pow_le_of_lt_radius hlt
  simp only [Real.coe_toNNReal _ hρ.le] at hCb
  refine ⟨fun n h => p n (fun _ => h), fun n => (isContHomPoly_iff _).2 ⟨p n, fun _ => rfl⟩,
    C, ρ, hC.le, hρ, fun n h => ?_, fun y hy => ?_⟩
  · calc ‖p n (fun _ => h)‖ ≤ ‖p n‖ * ∏ _i : Fin n, ‖h‖ := (p n).le_opNorm _
      _ = (‖p n‖ * ρ ^ n) * (‖h‖ / ρ) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow]
          field_simp
      _ ≤ C * (‖h‖ / ρ) ^ n := mul_le_mul_of_nonneg_right (hCb n) (by positivity)
  · have hmem : y - x ∈ Metric.eball (0 : E) r := by
      rw [Metric.mem_eball]
      refine lt_of_lt_of_le ?_ hρr.le
      rw [edist_lt_ofReal, dist_zero_right]; exact hy
    have := hp.hasSum hmem
    rwa [add_sub_cancel] at this

theorem analyticAt_of_isRealAnalyticPolyNormal {f : E → F} {x : E}
    (hf : IsRealAnalyticPolyNormal f x) : AnalyticAt ℝ f x := by
  obtain ⟨P, hP, C, R, hC, hR, hb, hs⟩ := hf
  choose A hA using fun n => (isContHomPoly_iff (P n)).1 (hP n)
  refine (hasFPowerSeriesOnBall_symSeries A hC hR (fun n h => by rw [← hA]; exact hb n h)
    (fun h hh => ?_)).analyticAt
  have := hs (x + h) (by rwa [add_sub_cancel_left])
  simp only [add_sub_cancel_left, hA] at this
  exact this.tendsto_sum_nat

/-- Reading-robustness: under the normal-convergence reading of DEF-017 the bridge holds with no
completeness assumption. -/
theorem analyticAt_iff_isRealAnalyticPolyNormal (f : E → F) (x : E) :
    AnalyticAt ℝ f x ↔ IsRealAnalyticPolyNormal f x :=
  ⟨isRealAnalyticPolyNormal_of_analyticAt, analyticAt_of_isRealAnalyticPolyNormal⟩

end Bridge

section Complexification

/-! ### DEF-017, complexification clause (reachable direction)

A complexification datum is recorded by its structure maps: a complex normed space `EC` with a
real-linear continuous embedding `ι : E → EC`, a complex normed space `FC` with a real-linear
continuous embedding `ιF : F → FC`, and a continuous real-linear "real part" `re : FC → F` with
`re ∘ ιF = id`. A local holomorphic extension of `f` near `x` is a map `g : EC → FC` which is
complex analytic at `ι x` (convergent series of continuous complex homogeneous polynomials, the
standard notion of holomorphy on complex Banach spaces) and satisfies `g (ι y) = ιF (f y)` for
`y` near `x`. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {EC FC : Type*} [NormedAddCommGroup EC] [NormedSpace ℂ EC]
  [NormedAddCommGroup FC] [NormedSpace ℂ FC]

/-- `f` has a local holomorphic extension near `x` along the complexification maps `ι`, `ιF`. -/
def HasLocalHolomorphicExtension (ι : E →L[ℝ] EC) (ιF : F →L[ℝ] FC) (f : E → F) (x : E) :
    Prop :=
  ∃ g : EC → FC, AnalyticAt ℂ g (ι x) ∧ ∀ᶠ y in 𝓝 x, g (ι y) = ιF (f y)

/-- Complexification clause, direction (holomorphic extension ⇒ real analytic). -/
theorem analyticAt_of_hasLocalHolomorphicExtension (ι : E →L[ℝ] EC) (ιF : F →L[ℝ] FC)
    (re : FC →L[ℝ] F) (hre : ∀ v, re (ιF v) = v) {f : E → F} {x : E}
    (hf : HasLocalHolomorphicExtension ι ιF f x) : AnalyticAt ℝ f x := by
  obtain ⟨g, hg, hext⟩ := hf
  have h1 : AnalyticAt ℝ (fun y => re (g (ι y))) x :=
    (re.analyticAt _).comp ((hg.restrictScalars (𝕜 := ℝ)).comp (ι.analyticAt x))
  refine h1.congr ?_
  filter_upwards [hext] with y hy
  rw [hy, hre]

/-- The same direction, stated with the literal DEF-017 predicate. -/
theorem isRealAnalyticPoly_of_hasLocalHolomorphicExtension (ι : E →L[ℝ] EC)
    (ιF : F →L[ℝ] FC) (re : FC →L[ℝ] F) (hre : ∀ v, re (ιF v) = v) {f : E → F} {x : E}
    (hf : HasLocalHolomorphicExtension ι ιF f x) : IsRealAnalyticPoly f x :=
  isRealAnalyticPoly_of_analyticAt (analyticAt_of_hasLocalHolomorphicExtension ι ιF re hre hf)

end Complexification

section Identity

/-! ### R-2535E8FD restated with the literal DEF-017 predicate -/

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- R-2535E8FD (`global:analytic-identity`) with "locally real analytic" read literally as
DEF-017 (`IsRealAnalyticPoly` at every point): a map between real Hilbert spaces which is real
analytic everywhere and vanishes on an open ball about zero vanishes identically. Obtained from
the frozen `AnalyticIdentity.identity_of_vanishing_ball` through the bridge. -/
theorem identity_of_vanishing_ball_poly {ρ : ℝ} (A : E → F)
    (hA : ∀ x : E, IsRealAnalyticPoly A x) (hρ : 0 < ρ)
    (hzero : ∀ y ∈ Metric.ball (0 : E) ρ, A y = 0) : ∀ x : E, A x = 0 :=
  AnalyticIdentity.identity_of_vanishing_ball A
    (fun x => analyticAt_of_isRealAnalyticPoly (hA x)) hρ hzero

/-- The same, with the map-level predicate `IsRealAnalyticMap`. -/
theorem identity_of_vanishing_ball_realAnalyticMap {ρ : ℝ} (A : E → F)
    (hA : IsRealAnalyticMap A) (hρ : 0 < ρ)
    (hzero : ∀ y ∈ Metric.ball (0 : E) ρ, A y = 0) : ∀ x : E, A x = 0 :=
  identity_of_vanishing_ball_poly A hA hρ hzero

end Identity

end QuantumNLS.RealAnalyticDef

/-! ### Axiom audit -/
#print axioms QuantumNLS.RealAnalyticDef.coeff_sum
#print axioms QuantumNLS.RealAnalyticDef.diff_identity
#print axioms QuantumNLS.RealAnalyticDef.diag_smul
#print axioms QuantumNLS.RealAnalyticDef.norm_sum_perm_le
#print axioms QuantumNLS.RealAnalyticDef.symM_diag
#print axioms QuantumNLS.RealAnalyticDef.norm_symM_le
#print axioms QuantumNLS.RealAnalyticDef.pow_div_factorial_le_exp_one_pow
#print axioms QuantumNLS.RealAnalyticDef.homog_bound
#print axioms QuantumNLS.RealAnalyticDef.shifted_bound
#print axioms QuantumNLS.RealAnalyticDef.isContHomPoly_iff
#print axioms QuantumNLS.RealAnalyticDef.symC_diag
#print axioms QuantumNLS.RealAnalyticDef.norm_symC_le
#print axioms QuantumNLS.RealAnalyticDef.isRealAnalyticPoly_of_hasFPowerSeriesOnBall
#print axioms QuantumNLS.RealAnalyticDef.isRealAnalyticPoly_of_analyticAt
#print axioms QuantumNLS.RealAnalyticDef.hasFPowerSeriesOnBall_symSeries
#print axioms QuantumNLS.RealAnalyticDef.analyticAt_of_isRealAnalyticPoly
#print axioms QuantumNLS.RealAnalyticDef.analyticAt_iff_isRealAnalyticPoly
#print axioms QuantumNLS.RealAnalyticDef.isRealAnalyticMap_iff
#print axioms QuantumNLS.RealAnalyticDef.isRealAnalyticPolyNormal_of_analyticAt
#print axioms QuantumNLS.RealAnalyticDef.analyticAt_of_isRealAnalyticPolyNormal
#print axioms QuantumNLS.RealAnalyticDef.analyticAt_iff_isRealAnalyticPolyNormal
#print axioms QuantumNLS.RealAnalyticDef.analyticAt_of_hasLocalHolomorphicExtension
#print axioms QuantumNLS.RealAnalyticDef.isRealAnalyticPoly_of_hasLocalHolomorphicExtension
#print axioms QuantumNLS.RealAnalyticDef.identity_of_vanishing_ball_poly
#print axioms QuantumNLS.RealAnalyticDef.identity_of_vanishing_ball_realAnalyticMap
