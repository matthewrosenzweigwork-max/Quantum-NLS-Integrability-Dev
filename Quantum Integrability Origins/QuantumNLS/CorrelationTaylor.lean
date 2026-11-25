import Mathlib
import QuantumNLS.CorrelationDerivatives

/-!
# REG-006 stage (c2): Taylor remainders of the translated correlation (`CC:G04:correlation`)

Source: `source/chapters/regularity/integer_moments.tex`, lines 169--172 and 201--205. The last stage of the
split REG-006 work. For `1 ≤ d ≤ 2k`, with `P_d` the degree-`d` Taylor polynomial of `C = Cfun f` at `0`:

* (i) `C(h) − P_d(h) = o(|h|^d)` as `h → 0`;
* (ii) the global bound `|C(h) − P_d(h)| ≤ C_{k,q,L} |h|^d ∏_j ‖f_j‖_{H^k}` for all `h`.

Route. The Taylor polynomial is the iterated-derivative form `P_d(h) = Σ_{j ≤ d} (1/j!) D^jC(0)(h,…,h)`.
Along the segment `s ↦ C(s h)`, the integral Taylor formula with remainder degree `d − 1` gives
`C(h) − P_d(h) = ∫_0^1 ((1−t)^{d−1}/(d−1)!) (D^dC(th)(h,…,h) − D^dC(0)(h,…,h)) dt`, because
`∫_0^1 (1−t)^{d−1}/(d−1)! dt = 1/d!`. Only the `d`-th derivative and its continuity are used, so the
boundary `d = 2k` needs no `(2k+1)`-th derivative (`C ∈ C^{2k}` suffices). The operator norm of `D^dC` is
bounded through its values on basis tuples (`opNorm_le_of_basis`) and the partial-derivative bound
`partial_derivative_bound` of stage (c1). The little-o statement uses continuity of `D^dC` at `0`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology MeasureTheory intervalIntegral

namespace QuantumNLS.CorrelationTaylor

open QuantumNLS.CorrelationLatticeBound QuantumNLS.CorrelationConstrainedSum
open QuantumNLS.CorrelationConstrainedSumGen QuantumNLS.CorrelationFourierBridge
open QuantumNLS.CorrelationDerivatives QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

/-- Euclidean norm `|h| = (Σ_j h_j²)^{1/2}` on `ℝ^q`. -/
def eucl {q : ℕ} (h : Fin q → ℝ) : ℝ := Real.sqrt (∑ j, h j ^ 2)

theorem norm_le_eucl {q : ℕ} (h : Fin q → ℝ) : ‖h‖ ≤ eucl h := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun j => ?_)
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => h j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)

/-- The degree-`d` Taylor polynomial at `0` in iterated-derivative form:
`P_d(h) = Σ_{j ≤ d} (1/j!) D^jC(0)(h,…,h)`. -/
def taylorPoly {q : ℕ} (C : (Fin q → ℝ) → ℂ) (d : ℕ) (h : Fin q → ℝ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1), ((Nat.factorial j : ℝ)⁻¹) • iteratedFDeriv ℝ j C 0 (fun _ : Fin j => h)

/-- Operator norm of a `d`-linear map on `ℝ^q` from its values on basis tuples:
`‖M‖ ≤ q^d · sup_{js} ‖M(e_{js_1},…,e_{js_d})‖`. -/
theorem opNorm_le_of_basis {d q : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin d => Fin q → ℝ) ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hM : ∀ js : Fin d → Fin q, ‖M (fun i => Pi.single (js i) (1 : ℝ))‖ ≤ B) :
    ‖M‖ ≤ (q : ℝ) ^ d * B := by
  refine M.opNorm_le_bound (by positivity) (fun v => ?_)
  have hv : v = fun i => ∑ j, v i j • (Pi.single j (1 : ℝ) : Fin q → ℝ) := by
    funext i k
    simp [Finset.sum_apply, Pi.single_apply]
  have hMv : M v = ∑ r : Fin d → Fin q,
      (∏ i, v i (r i)) • M (fun i => Pi.single (r i) (1 : ℝ)) := by
    conv_lhs => rw [hv]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ContinuousMultilinearMap.map_smul_univ]
  have hsum : ∀ i, ∑ j, |v i j| ≤ (q : ℝ) * ‖v i‖ := by
    intro i
    calc ∑ j, |v i j| ≤ ∑ _j : Fin q, ‖v i‖ :=
          Finset.sum_le_sum (fun j _ => by
            rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (v i) j)
      _ = (q : ℝ) * ‖v i‖ := by simp [Finset.sum_const, Finset.card_univ]
  calc ‖M v‖ = ‖∑ r : Fin d → Fin q,
        (∏ i, v i (r i)) • M (fun i => Pi.single (r i) (1 : ℝ))‖ := by rw [hMv]
    _ ≤ ∑ r : Fin d → Fin q, ‖(∏ i, v i (r i)) • M (fun i => Pi.single (r i) (1 : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r : Fin d → Fin q, (∏ i, |v i (r i)|) * B :=
        Finset.sum_le_sum fun r _ => by
          rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
          exact mul_le_mul_of_nonneg_left (hM r) (Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ = B * ∏ i, ∑ j, |v i j| := by
        rw [Fintype.prod_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
    _ ≤ B * ∏ i, ((q : ℝ) * ‖v i‖) :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
            (fun i _ => hsum i)) hB
    _ = (q : ℝ) ^ d * B * ∏ i, ‖v i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- Derivative of the segment `s ↦ C(s • h)`: `d^j/ds^j C(s h) = D^jC(s h)(h,…,h)`. -/
theorem iteratedDeriv_line {q : ℕ} {C : (Fin q → ℝ) → ℂ} {N : WithTop ℕ∞} (hC : ContDiff ℝ N C)
    (h : Fin q → ℝ) {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ N) (t : ℝ) :
    iteratedDeriv j (fun s : ℝ => C (s • h)) t =
      iteratedFDeriv ℝ j C (t • h) (fun _ : Fin j => h) := by
  set L1 : ℝ →L[ℝ] (Fin q → ℝ) := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h with hL1
  have hL : ∀ s : ℝ, L1 s = s • h := fun s => by simp [hL1]
  have hfun : (fun s : ℝ => C (s • h)) = C ∘ L1 := funext fun s => by
    rw [Function.comp_apply, hL]
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right L1 hC t hj,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [hL, one_smul]

/-- `∫_0^1 (1−t)^n/n! dt = 1/(n+1)!`. -/
theorem integral_one_sub_pow_div (n : ℕ) :
    ∫ t in (0 : ℝ)..1, (1 - t) ^ n / (Nat.factorial n : ℝ) = ((Nat.factorial (n + 1) : ℝ))⁻¹ := by
  simp only [intervalIntegral.integral_div]
  have h1 : ∫ t in (0 : ℝ)..1, (1 - t) ^ n = ∫ t in (0 : ℝ)..1, t ^ n := by
    have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) (1 : ℝ) (a := 0) (b := 1)
    simpa using this
  rw [h1, integral_pow]
  rw [Nat.factorial_succ]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  norm_num

/-- The segment integral Taylor formula with remainder degree `n`, for `C(h)` at the point `h`. -/
theorem taylor_identity {q : ℕ} {C : (Fin q → ℝ) → ℂ} {N : WithTop ℕ∞} (hC : ContDiff ℝ N C)
    {n : ℕ} (hdN : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ N) (h : Fin q → ℝ) :
    C h - taylorPoly C (n + 1) h =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ n / (Nat.factorial n : ℝ)) •
        (iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h) -
          iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h)) := by
  have hgc : ∀ j : ℕ, (j : WithTop ℕ∞) ≤ N → ContDiff ℝ j (fun s : ℝ => C (s • h)) :=
    fun j hj => (hC.comp (contDiff_id.smul contDiff_const)).of_le hj
  have hgk : ∀ j : ℕ, (j : WithTop ℕ∞) ≤ N → ∀ t : ℝ,
      iteratedDeriv j (fun s : ℝ => C (s • h)) t =
        iteratedFDeriv ℝ j C (t • h) (fun _ : Fin j => h) :=
    fun j hj t => iteratedDeriv_line hC h hj t
  have huniq : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc zero_ne_one
  have hT := taylor_integral_remainder (f := fun s : ℝ => C (s • h)) (x := (1 : ℝ)) (x₀ := (0 : ℝ))
    (n := n) ((hgc (n + 1) hdN).contDiffOn.mono (Set.subset_univ _))
  have hT' : C h - taylorWithinEval (fun s : ℝ => C (s • h)) n (Set.uIcc 0 1) 0 1 =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ n / (Nat.factorial n : ℝ)) •
        iteratedDerivWithin (n + 1) (fun s : ℝ => C (s • h)) (Set.uIcc 0 1) t := by
    have := hT
    simp only [one_smul] at this
    exact this
  have hIt : ∀ t ∈ Set.uIcc (0 : ℝ) 1, iteratedDerivWithin (n + 1) (fun s : ℝ => C (s • h)) (Set.uIcc 0 1) t =
      iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h) := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq (hgc (n + 1) hdN).contDiffAt ht, hgk (n + 1) hdN t]
  have hTW : taylorWithinEval (fun s : ℝ => C (s • h)) n (Set.uIcc 0 1) 0 1 =
      ∑ j ∈ Finset.range (n + 1), ((Nat.factorial j : ℝ)⁻¹) •
        iteratedFDeriv ℝ j C 0 (fun _ : Fin j => h) := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjN : ((j : ℕ) : WithTop ℕ∞) ≤ N :=
      le_trans (by exact_mod_cast (show j ≤ n + 1 by have := Finset.mem_range.mp hj; omega)) hdN
    have hval : iteratedDerivWithin j (fun s : ℝ => C (s • h)) (Set.uIcc 0 1) 0 =
        iteratedFDeriv ℝ j C 0 (fun _ : Fin j => h) := by
      rw [iteratedDerivWithin_eq_iteratedDeriv huniq (hgc j hjN).contDiffAt
        (Set.left_mem_uIcc), hgk j hjN 0, zero_smul]
    rw [hval]
    simp
  have hsplit : taylorPoly C (n + 1) h =
      ∑ j ∈ Finset.range (n + 1), ((Nat.factorial j : ℝ)⁻¹) •
        iteratedFDeriv ℝ j C 0 (fun _ : Fin j => h) +
      ((Nat.factorial (n + 1) : ℝ)⁻¹) • iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h) := by
    unfold taylorPoly
    rw [Finset.sum_range_succ]
  have hcst : ∫ t in (0 : ℝ)..1, ((1 - t) ^ n / (Nat.factorial n : ℝ)) •
      iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h) =
      ((Nat.factorial (n + 1) : ℝ))⁻¹ • iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h) := by
    rw [intervalIntegral.integral_smul_const, integral_one_sub_pow_div]
  have hcI : Continuous (iteratedFDeriv ℝ (n + 1) C) := hC.continuous_iteratedFDeriv hdN
  have hcontG : Continuous (fun t : ℝ => iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h)) :=
    (continuous_eval_const _).comp (hcI.comp (continuous_id.smul continuous_const))
  have hcontw : Continuous (fun t : ℝ => (1 - t) ^ n / (Nat.factorial n : ℝ)) :=
    ((continuous_const.sub continuous_id).pow n).div_const _
  calc C h - taylorPoly C (n + 1) h
      = (C h - taylorWithinEval (fun s : ℝ => C (s • h)) n (Set.uIcc 0 1) 0 1) -
          ((Nat.factorial (n + 1) : ℝ))⁻¹ • iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h) := by
        rw [hsplit, hTW]
        abel
    _ = (∫ t in (0 : ℝ)..1, ((1 - t) ^ n / (Nat.factorial n : ℝ)) •
          iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h)) -
          ((Nat.factorial (n + 1) : ℝ))⁻¹ • iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h) := by
        rw [hT']
        congr 1
        exact intervalIntegral.integral_congr (fun t ht => by rw [hIt t ht])
    _ = (∫ t in (0 : ℝ)..1, ((1 - t) ^ n / (Nat.factorial n : ℝ)) •
          iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h)) -
          ∫ t in (0 : ℝ)..1, ((1 - t) ^ n / (Nat.factorial n : ℝ)) •
            iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h) := by
        rw [hcst]
    _ = ∫ t in (0 : ℝ)..1, (((1 - t) ^ n / (Nat.factorial n : ℝ)) •
          iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h) -
          ((1 - t) ^ n / (Nat.factorial n : ℝ)) •
            iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h)) :=
        (intervalIntegral.integral_sub
          ((hcontw.smul hcontG).intervalIntegrable 0 1)
          ((hcontw.smul continuous_const).intervalIntegrable 0 1)).symm
    _ = ∫ t in (0 : ℝ)..1, ((1 - t) ^ n / (Nat.factorial n : ℝ)) •
          (iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h) -
            iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h)) :=
        intervalIntegral.integral_congr (fun t _ => by rw [smul_sub])

/-- **Taylor remainder, uniform form.** If `‖D^{d}C(th)(h,…,h) − D^{d}C(0)(h,…,h)‖ ≤ M` on `[0,1]`, then
`‖C(h) − P_{d}(h)‖ ≤ M/d!` with `d = n+1`. -/
theorem taylor_bound_of {q : ℕ} {C : (Fin q → ℝ) → ℂ} {N : WithTop ℕ∞} (hC : ContDiff ℝ N C)
    {n : ℕ} (hdN : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ N) (h : Fin q → ℝ) {M : ℝ}
    (hM : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h) -
        iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h)‖ ≤ M) :
    ‖C h - taylorPoly C (n + 1) h‖ ≤ M / (Nat.factorial (n + 1) : ℝ) := by
  rw [taylor_identity hC hdN h]
  have hw : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ (1 - t) ^ n / (Nat.factorial n : ℝ) := fun t ht =>
    div_nonneg (pow_nonneg (by linarith [ht.2]) _) (Nat.cast_nonneg _)
  have hcont : Continuous (fun t : ℝ => M * ((1 - t) ^ n / (Nat.factorial n : ℝ))) :=
    continuous_const.mul (((continuous_const.sub continuous_id).pow n).div_const _)
  calc ‖∫ t in (0 : ℝ)..1, ((1 - t) ^ n / (Nat.factorial n : ℝ)) •
        (iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h) -
          iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h))‖
      ≤ ∫ t in (0 : ℝ)..1, M * ((1 - t) ^ n / (Nat.factorial n : ℝ)) := by
        apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        · refine Filter.Eventually.of_forall (fun t ht => ?_)
          rw [norm_smul, Real.norm_of_nonneg (hw t ht)]
          have hMt := hM t (by rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self ht)
          calc (1 - t) ^ n / (Nat.factorial n : ℝ) * ‖iteratedFDeriv ℝ (n + 1) C (t • h) (fun _ : Fin (n + 1) => h) -
                  iteratedFDeriv ℝ (n + 1) C 0 (fun _ : Fin (n + 1) => h)‖
              ≤ (1 - t) ^ n / (Nat.factorial n : ℝ) * M :=
                mul_le_mul_of_nonneg_left hMt (hw t ht)
            _ = M * ((1 - t) ^ n / (Nat.factorial n : ℝ)) := mul_comm _ _
        · exact hcont.intervalIntegrable 0 1
    _ = M / (Nat.factorial (n + 1) : ℝ) := by
        rw [intervalIntegral.integral_const_mul, integral_one_sub_pow_div]
        ring

/-! ## The printed constant and the two Taylor statements -/

/-- The printed constant with the Hölder factor: exactly the right-hand side of
`partial_derivative_bound` (stage c1), with `C_k = (Σ_x W(x)^{−2k})^{1/2}`. -/
def Bfull {m k : ℕ} (f : Fin (m + 2) → Hk L k) : ℝ :=
  (max 1 (2 * Real.pi / L)) ^ (2 * k) * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) *
    (((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2)) *
    ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ ^ (m + 2) * ∏ j, ‖f j‖

theorem Bfull_nonneg {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) : 0 ≤ Bfull f :=
  (norm_nonneg _).trans (partial_derivative_bound hk f (Nat.zero_le _) (fun i => i.elim0) 0)

/-- Operator-norm bound on `D^dC(x)` (uniform in `x`), from the basis bound of stage (c1). -/
theorem iteratedFDeriv_le {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {d : ℕ}
    (hd : d ≤ 2 * k) (x : Fin (m + 2) → ℝ) :
    ‖iteratedFDeriv ℝ d (fun y => Cfun f y) x‖ ≤ ((m + 2 : ℕ) : ℝ) ^ d * Bfull f :=
  opNorm_le_of_basis _ (Bfull f) (Bfull_nonneg hk f)
    (fun js => partial_derivative_bound hk f hd js x)

/-- Evaluation bound: `‖D^dC(x)(h,…,h)‖ ≤ q^d · B · ‖h‖^d`. -/
theorem iteratedFDeriv_apply_le {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {d : ℕ}
    (hd : d ≤ 2 * k) (x h : Fin (m + 2) → ℝ) :
    ‖iteratedFDeriv ℝ d (fun y => Cfun f y) x (fun _ : Fin d => h)‖ ≤
      ((m + 2 : ℕ) : ℝ) ^ d * Bfull f * ‖h‖ ^ d := by
  calc ‖iteratedFDeriv ℝ d (fun y => Cfun f y) x (fun _ : Fin d => h)‖
      ≤ ‖iteratedFDeriv ℝ d (fun y => Cfun f y) x‖ * ∏ _i : Fin d, ‖h‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ (((m + 2 : ℕ) : ℝ) ^ d * Bfull f) * ∏ _i : Fin d, ‖h‖ :=
        mul_le_mul_of_nonneg_right (iteratedFDeriv_le hk f hd x)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = ((m + 2 : ℕ) : ℝ) ^ d * Bfull f * ‖h‖ ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Stage (c2), part (ii): global Taylor bound.** For `1 ≤ d = n + 1 ≤ 2k`, `q = m + 2 ≥ 2`, `k ≥ 1`,
and every `h ∈ ℝ^q`:
`|C(h) − P_d(h)| ≤ 2 (m+2)^{2k} · B_{k,q,L} · |h|^d · ∏_j ‖f_j‖_{H^k}`. -/
theorem taylor_remainder_bound {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {n : ℕ}
    (hdN : n + 1 ≤ 2 * k) (h : Fin (m + 2) → ℝ) :
    ‖Cfun f h - taylorPoly (Cfun f) (n + 1) h‖ ≤
      2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * Bfull f) * eucl h ^ (n + 1) := by
  have hC := contDiff_Cfun hk f
  have hdN' : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ ((2 * k : ℕ) : WithTop ℕ∞) := by exact_mod_cast hdN
  have hB0 := Bfull_nonneg hk f
  have hq1 : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 2 by omega)
  have hbd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) (t • h) (fun _ : Fin (n + 1) => h) -
        iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) 0 (fun _ : Fin (n + 1) => h)‖ ≤
        2 * (((m + 2 : ℕ) : ℝ) ^ (n + 1) * Bfull f) * ‖h‖ ^ (n + 1) := by
    intro t _
    refine (norm_sub_le _ _).trans ?_
    have h1 := iteratedFDeriv_apply_le hk f (d := n + 1) (by omega) (t • h) h
    have h2 := iteratedFDeriv_apply_le hk f (d := n + 1) (by omega) 0 h
    linarith
  have hR := taylor_bound_of hC hdN' h hbd
  have hfact : (1 : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) := Nat.one_le_cast.2 (Nat.factorial_pos _)
  have hM0 : 0 ≤ 2 * (((m + 2 : ℕ) : ℝ) ^ (n + 1) * Bfull f) * ‖h‖ ^ (n + 1) := by
    have := pow_nonneg (norm_nonneg h) (n + 1)
    have := pow_nonneg (le_trans zero_le_one hq1) (n + 1)
    positivity
  calc ‖Cfun f h - taylorPoly (Cfun f) (n + 1) h‖
      ≤ 2 * (((m + 2 : ℕ) : ℝ) ^ (n + 1) * Bfull f) * ‖h‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := hR
    _ ≤ 2 * (((m + 2 : ℕ) : ℝ) ^ (n + 1) * Bfull f) * ‖h‖ ^ (n + 1) :=
        div_le_self hM0 hfact
    _ ≤ 2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * Bfull f) * eucl h ^ (n + 1) := by
        have hqd : ((m + 2 : ℕ) : ℝ) ^ (n + 1) ≤ ((m + 2 : ℕ) : ℝ) ^ (2 * k) :=
          pow_le_pow_right₀ hq1 hdN
        have hnorm : ‖h‖ ^ (n + 1) ≤ eucl h ^ (n + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_le_eucl h) _
        have hqB : 0 ≤ ((m + 2 : ℕ) : ℝ) ^ (n + 1) * Bfull f :=
          mul_nonneg (pow_nonneg (le_trans zero_le_one hq1) _) hB0
        calc 2 * (((m + 2 : ℕ) : ℝ) ^ (n + 1) * Bfull f) * ‖h‖ ^ (n + 1)
            ≤ 2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * Bfull f) * ‖h‖ ^ (n + 1) := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqd hB0) (by norm_num)
          _ ≤ 2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * Bfull f) * eucl h ^ (n + 1) := by
              apply mul_le_mul_of_nonneg_left hnorm
              have : 0 ≤ ((m + 2 : ℕ) : ℝ) ^ (2 * k) * Bfull f :=
                mul_nonneg (pow_nonneg (le_trans zero_le_one hq1) _) hB0
              positivity

/-- **Stage (c2), part (i): little-o Taylor remainder.** For `1 ≤ d = n + 1 ≤ 2k`:
`C(h) − P_d(h) = o(|h|^d)` as `h → 0`, with `|h|` the Euclidean norm. -/
theorem taylor_remainder_isLittleO {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {n : ℕ}
    (hdN : n + 1 ≤ 2 * k) :
    (fun h : Fin (m + 2) → ℝ => Cfun f h - taylorPoly (Cfun f) (n + 1) h) =o[𝓝 0]
      (fun h => eucl h ^ (n + 1)) := by
  have hC := contDiff_Cfun hk f
  have hdN' : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ ((2 * k : ℕ) : WithTop ℕ∞) := by exact_mod_cast hdN
  have hcont : Continuous (iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y)) :=
    hC.continuous_iteratedFDeriv hdN'
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hfact : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  obtain ⟨δ, hδ, hD⟩ := Metric.continuousAt_iff.1
    (hcont.continuousAt (x := (0 : Fin (m + 2) → ℝ))) (c * (Nat.factorial (n + 1) : ℝ))
    (mul_pos hc hfact)
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : Fin (m + 2) → ℝ) hδ) (fun h hh => ?_)
  have hh' : ‖h‖ < δ := by simpa [dist_zero_right] using hh
  have hbd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) (t • h) (fun _ : Fin (n + 1) => h) -
        iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) 0 (fun _ : Fin (n + 1) => h)‖ ≤
        (c * (Nat.factorial (n + 1) : ℝ)) * ‖h‖ ^ (n + 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have ht1 : ‖t • h‖ < δ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht.2) hh'
    have hD' := hD (x := t • h) (by rw [dist_zero_right]; exact ht1)
    rw [dist_eq_norm] at hD'
    calc ‖iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) (t • h) (fun _ : Fin (n + 1) => h) -
          iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) 0 (fun _ : Fin (n + 1) => h)‖
        = ‖(iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) (t • h) -
            iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) 0) (fun _ : Fin (n + 1) => h)‖ := by
          rw [ContinuousMultilinearMap.sub_apply]
      _ ≤ ‖iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) (t • h) -
            iteratedFDeriv ℝ (n + 1) (fun y => Cfun f y) 0‖ * ∏ _i : Fin (n + 1), ‖h‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (c * (Nat.factorial (n + 1) : ℝ)) * ∏ _i : Fin (n + 1), ‖h‖ :=
          mul_le_mul_of_nonneg_right hD'.le (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = (c * (Nat.factorial (n + 1) : ℝ)) * ‖h‖ ^ (n + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hR := taylor_bound_of hC hdN' h hbd
  have hval : (c * (Nat.factorial (n + 1) : ℝ)) * ‖h‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) =
      c * ‖h‖ ^ (n + 1) := by
    field_simp
  have hnorm : ‖eucl h ^ (n + 1)‖ = eucl h ^ (n + 1) :=
    Real.norm_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [hnorm]
  calc ‖Cfun f h - taylorPoly (Cfun f) (n + 1) h‖
      ≤ (c * (Nat.factorial (n + 1) : ℝ)) * ‖h‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := hR
    _ = c * ‖h‖ ^ (n + 1) := hval
    _ ≤ c * eucl h ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_le_eucl h) _) hc.le

end QuantumNLS.CorrelationTaylor

/-! Axiom audit (chunk 2). -/
#print axioms QuantumNLS.CorrelationTaylor.opNorm_le_of_basis
#print axioms QuantumNLS.CorrelationTaylor.iteratedDeriv_line
#print axioms QuantumNLS.CorrelationTaylor.taylor_identity
#print axioms QuantumNLS.CorrelationTaylor.taylor_bound_of
#print axioms QuantumNLS.CorrelationTaylor.integral_one_sub_pow_div
#print axioms QuantumNLS.CorrelationTaylor.Bfull_nonneg
#print axioms QuantumNLS.CorrelationTaylor.iteratedFDeriv_le
#print axioms QuantumNLS.CorrelationTaylor.iteratedFDeriv_apply_le
#print axioms QuantumNLS.CorrelationTaylor.taylor_remainder_bound
#print axioms QuantumNLS.CorrelationTaylor.taylor_remainder_isLittleO
#print axioms QuantumNLS.CorrelationTaylor.norm_le_eucl
#print axioms QuantumNLS.CorrelationTaylor.taylorPoly
