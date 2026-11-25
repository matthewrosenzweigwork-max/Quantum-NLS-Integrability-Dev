import Mathlib

/-!
# CC:F02:ordered-response (R-2536C7A6): strict order of the inverse-Jacobian response

Source: `source-text/chapters/root_response/F02.tex`.
* Standing assumptions (chapter opening): `L > 0`, `N ≥ 1`, `c > 0`; the vector `q` is strictly ordered.
* Matrix `CC:F02:matrix`: `(B f)_i = L f_i + ∑_{j ≠ i} w_ij (f_i - f_j)` with
  `w_ij = 2c/(c^2 + (q_i - q_j)^2)`.
* Lemma `CC:F02:ordered-response`: for strictly ordered `q`, `f = B^{-1} q` is strictly increasing
  in its index when `N > 1`.

Lean indices are zero-based (`Fin N`); the source's `i` is `i` here.

Route (printed proof, with the deviations recorded in the review record):
* invertibility of `B` from the quadratic form `fᵀ B f = L|f|^2 + (1/2) ∑∑ w_ij (f_i - f_j)^2 ≥ L|f|^2`;
* `v(t) = f - exp(-tB) f` solves `v' = q - B v`, `v(0) = 0`, with `B f = q`;
* first-crossing argument for the adjacent differences `v_{i+1} - v_i` (`first_crossing`);
* `v(t) → f` from the energy estimate for `g(t) = exp(-tB) f` (`energy_decay`, `gsol_tendsto`);
* strictness from the same sign comparison applied to `f` (`sign_lemma`).

No `sorry`, no `admit`, no `native_decide`, no axioms.
-/

noncomputable section
open scoped BigOperators
open Finset Matrix Filter Topology

namespace QuantumNLS.OrderedResponse

variable {N : ℕ}

/-- Pair weight `w_ij = 2c/(c^2 + (q_i - q_j)^2)`, written as a function of the two labels. -/
def wt (c x y : ℝ) : ℝ := 2 * c / (c ^ 2 + (x - y) ^ 2)

/-- The matrix `B` of `CC:F02:matrix` with entries in `L`, `c`, `q`:
`B_ii = L + ∑_{j ≠ i} w_ij` and `B_ik = -w_ik` for `k ≠ i`. -/
def Bmat (L c : ℝ) (q : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i k =>
    if i = k then L + ∑ j ∈ univ.erase i, wt c (q i) (q j) else -wt c (q i) (q k)

/-- The response vector `f = B^{-1} q`. -/
def respF (L c : ℝ) (q : Fin N → ℝ) : Fin N → ℝ := (Bmat L c q)⁻¹ *ᵥ q

lemma wt_comm (c x y : ℝ) : wt c x y = wt c y x := by
  unfold wt
  rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]

lemma wt_pos {c : ℝ} (hc : 0 < c) (x y : ℝ) : 0 < wt c x y := by
  unfold wt
  have h1 : 0 < c ^ 2 + (x - y) ^ 2 := by
    have := pow_pos hc 2
    nlinarith [sq_nonneg (x - y)]
  exact div_pos (by linarith) h1

lemma wt_le_of_sq_le {c a b : ℝ} (hc : 0 < c) (h : a ^ 2 ≤ b ^ 2) :
    2 * c / (c ^ 2 + b ^ 2) ≤ 2 * c / (c ^ 2 + a ^ 2) := by
  have h1 : 0 < c ^ 2 + a ^ 2 := by
    have := pow_pos hc 2
    nlinarith [sq_nonneg a]
  apply div_le_div_of_nonneg_left (by linarith) h1
  linarith

/-- The printed action `(Bf)_i = L f_i + ∑_{j ≠ i} w_ij (f_i - f_j)`, from the matrix entries. -/
lemma mulVec_Bmat_eq (L c : ℝ) (q u : Fin N → ℝ) (i : Fin N) :
    (Bmat L c q *ᵥ u) i = L * u i + ∑ j ∈ univ.erase i, wt c (q i) (q j) * (u i - u j) := by
  simp only [Matrix.mulVec, dotProduct, Bmat, Matrix.of_apply]
  rw [← Finset.add_sum_erase univ _ (mem_univ i), if_pos rfl]
  have h2 : ∀ k ∈ univ.erase i,
      (if i = k then L + ∑ j ∈ univ.erase i, wt c (q i) (q j) else -wt c (q i) (q k)) * u k
        = -(wt c (q i) (q k) * u k) := by
    intro k hk
    rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hk))]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
  have h3 : ∑ j ∈ univ.erase i, wt c (q i) (q j) * (u i - u j)
      = (∑ j ∈ univ.erase i, wt c (q i) (q j)) * u i
        - ∑ j ∈ univ.erase i, wt c (q i) (q j) * u j := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h3]
  ring

lemma cs_lt_s {n : ℕ} (i : Fin n) : i.castSucc < i.succ := Fin.castSucc_lt_succ

/-- Same action written over all indices (the `j = i` term vanishes). -/
lemma mulVec_Bmat_full (L c : ℝ) (q u : Fin N → ℝ) (i : Fin N) :
    (Bmat L c q *ᵥ u) i = L * u i + ∑ j, wt c (q i) (q j) * (u i - u j) := by
  rw [mulVec_Bmat_eq]
  congr 1
  exact (Finset.sum_erase (a := i) (f := fun j => wt c (q i) (q j) * (u i - u j)) univ
    (by simp))

lemma two_mul_sum_eq (c : ℝ) (q u : Fin N → ℝ) :
    2 * ∑ i, ∑ j, wt c (q i) (q j) * (u i * (u i - u j))
      = ∑ i, ∑ j, wt c (q i) (q j) * (u i - u j) ^ 2 := by
  have hS : ∑ i, ∑ j, wt c (q i) (q j) * (u i * (u i - u j))
      = ∑ i, ∑ j, wt c (q i) (q j) * (u j * (u j - u i)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [wt_comm c (q j) (q i)]
  rw [two_mul]
  nth_rewrite 1 [hS]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Quadratic-form bound `uᵀ B u ≥ L |u|^2` (the Hessian bound of the printed Lemma). -/
lemma quad_ge {L c : ℝ} (hc : 0 < c) (q u : Fin N → ℝ) :
    L * ∑ i, u i ^ 2 ≤ ∑ i, u i * (Bmat L c q *ᵥ u) i := by
  have h1 : ∀ i, u i * (Bmat L c q *ᵥ u) i
      = L * u i ^ 2 + ∑ j, wt c (q i) (q j) * (u i * (u i - u j)) := by
    intro i
    rw [mulVec_Bmat_full, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  have key : ∑ i, u i * (Bmat L c q *ᵥ u) i
      = L * ∑ i, u i ^ 2 + ∑ i, ∑ j, wt c (q i) (q j) * (u i * (u i - u j)) := by
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hnonneg : 0 ≤ ∑ i, ∑ j, wt c (q i) (q j) * (u i * (u i - u j)) := by
    have h2 := two_mul_sum_eq c q u
    have h3 : 0 ≤ ∑ i, ∑ j, wt c (q i) (q j) * (u i - u j) ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
        (fun j _ => mul_nonneg (wt_pos hc _ _).le (sq_nonneg _)))
    linarith
  rw [key]
  linarith

/-- Injectivity of `B` for `L > 0`, `c > 0`. -/
lemma Bmat_injective {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) :
    Function.Injective (Bmat L c q).mulVec := by
  intro u v huv
  have hx : Bmat L c q *ᵥ (u - v) = 0 := by
    have huv' : Bmat L c q *ᵥ u = Bmat L c q *ᵥ v := huv
    rw [Matrix.mulVec_sub, huv', sub_self]
  have hq := quad_ge (L := L) hc q (u - v)
  rw [hx] at hq
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hq
  have hS : ∑ i, (u - v) i ^ 2 ≤ 0 := by nlinarith
  have hS0 : ∑ i, (u - v) i ^ 2 = 0 :=
    le_antisymm hS (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hz : ∀ i, (u - v) i = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((u - v) i))).1 hS0 i
      (Finset.mem_univ i)
    exact (pow_eq_zero_iff two_ne_zero).1 this
  funext i
  exact sub_eq_zero.1 (hz i)

/-- `B` is invertible (`det B` is a unit), for `L > 0`, `c > 0`. -/
lemma Bmat_isUnit_det {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) :
    IsUnit (Bmat L c q).det :=
  (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_injective_iff_isUnit.1 (Bmat_injective hL hc q))

/-- `B f = q` for `f = B^{-1} q`. -/
lemma Bmat_respF {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) :
    Bmat L c q *ᵥ respF L c q = q := by
  unfold respF
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Bmat_isUnit_det hL hc q),
    Matrix.one_mulVec]

/-- Sign comparison (printed proof): if `u` is nondecreasing and `u_i = u_j` with `i < j`, then
`(B u)_j ≤ (B u)_i`. The weights satisfy `w_jk ≤ w_ik` for `k ≤ i` and `w_ik ≤ w_jk` for `k ≥ j`. -/
lemma sign_lemma (L c : ℝ) (hc : 0 < c) (q : Fin N → ℝ) (hq : StrictMono q)
    {i j : Fin N} (hij : i < j) (u : Fin N → ℝ) (hu : Monotone u) (heq : u i = u j) :
    (Bmat L c q *ᵥ u) j ≤ (Bmat L c q *ᵥ u) i := by
  rw [mulVec_Bmat_full, mulVec_Bmat_full]
  have hdiff : (L * u j + ∑ k, wt c (q j) (q k) * (u j - u k))
      - (L * u i + ∑ k, wt c (q i) (q k) * (u i - u k))
      = ∑ k, (wt c (q j) (q k) - wt c (q i) (q k)) * (u j - u k) := by
    rw [heq]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hterm : ∑ k, (wt c (q j) (q k) - wt c (q i) (q k)) * (u j - u k) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k _
    by_cases hki : k ≤ i
    · have hk1 : u k ≤ u i := hu hki
      have hw : wt c (q j) (q k) ≤ wt c (q i) (q k) := by
        unfold wt
        apply wt_le_of_sq_le hc
        nlinarith [hq hij, hq.monotone hki]
      have hu' : 0 ≤ u j - u k := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hu'
    · by_cases hkj : j ≤ k
      · have hk2 : u j ≤ u k := hu hkj
        have hw : wt c (q i) (q k) ≤ wt c (q j) (q k) := by
          unfold wt
          apply wt_le_of_sq_le hc
          nlinarith [hq hij, hq.monotone hkj]
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      · push_neg at hki hkj
        have hk1 : u i ≤ u k := hu hki.le
        have hk2 : u k ≤ u j := hu hkj.le
        have hkeq : u k = u j := by linarith
        simp [hkeq]
  linarith [hdiff, hterm]

/-- Local increase from a positive derivative at the base point (mean value theorem). -/
lemma local_increase {d e : ℝ → ℝ} (hd : ∀ y, HasDerivAt d (e y) y) {x0 : ℝ}
    (he : ContinuousAt e x0) (hpos : 0 < e x0) :
    ∃ η > 0, ∀ s t, x0 - η < s → s < t → t < x0 + η → d s < d t := by
  have hev : ∀ᶠ y in 𝓝 x0, 0 < e y := he.tendsto.eventually (lt_mem_nhds hpos)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨η, hη, fun s t hs hst ht => ?_⟩
  obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope d e hst
    (fun y _ => (hd y).continuousAt.continuousWithinAt) (fun y _ => hd y)
  have hcpos : 0 < e c := by
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hc.1, hc.2]
  have hts : 0 < t - s := sub_pos.2 hst
  have h3 : d t - d s = e c * (t - s) := by
    rw [hce, div_mul_cancel₀ _ (ne_of_gt hts)]
  nlinarith [mul_pos hcpos hts]

/-- First-crossing argument (printed proof): for `v' = q - B v`, `v(0) = 0` and strictly ordered
`q`, every adjacent difference `v_{i+1} - v_i` is strictly positive for all `t > 0`. -/
lemma first_crossing {n : ℕ} {L c : ℝ} (hc : 0 < c) (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (v : ℝ → Fin (n + 1) → ℝ)
    (hv : ∀ t i, HasDerivAt (fun s => v s i) (q i - (Bmat L c q *ᵥ v t) i) t)
    (hv0 : v 0 = 0) :
    ∀ t, 0 < t → ∀ i : Fin n, v t i.castSucc < v t i.succ := by
  have hcont : ∀ k, Continuous (fun s => v s k) := fun k =>
    continuous_iff_continuousAt.2 fun x => (hv x k).continuousAt
  have hBcont : ∀ j, Continuous (fun s => (Bmat L c q *ᵥ v s) j) := by
    intro j
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul (hcont k))
  set d : Fin n → ℝ → ℝ := fun i s => v s i.succ - v s i.castSucc with hd_def
  set e : Fin n → ℝ → ℝ := fun i s =>
    (q i.succ - (Bmat L c q *ᵥ v s) i.succ) - (q i.castSucc - (Bmat L c q *ᵥ v s) i.castSucc)
    with he_def
  have hd : ∀ i y, HasDerivAt (d i) (e i y) y := fun i y =>
    (hv y i.succ).sub (hv y i.castSucc)
  have hdc : ∀ i, Continuous (d i) := fun i =>
    continuous_iff_continuousAt.2 fun y => (hd i y).continuousAt
  have hec : ∀ i, Continuous (e i) := fun i =>
    (continuous_const.sub (hBcont i.succ)).sub (continuous_const.sub (hBcont i.castSucc))
  have hδ : ∀ i : Fin n, 0 < q i.succ - q i.castSucc := fun i => by
    have := hq (cs_lt_s i)
    linarith
  have he0 : ∀ i, 0 < e i 0 := by
    intro i
    have h : e i 0 = q i.succ - q i.castSucc := by simp [he_def, hv0]
    rw [h]
    exact hδ i
  have hA : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < d i t := by
    intro i
    obtain ⟨η, hη, hinc⟩ := local_increase (hd i) (hec i).continuousAt (he0 i)
    have h0 : d i 0 = 0 := by simp [hd_def, hv0]
    filter_upwards [Ioo_mem_nhdsGT hη] with t ht
    have := hinc 0 t (by linarith) ht.1 (by linarith [ht.2])
    linarith
  have hAll : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, 0 < d i t := Filter.eventually_all.2 hA
  obtain ⟨η, hη, hP⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hAll)
  have hlocal : ∀ t, 0 < t → t < η → ∀ i, 0 < d i t := by
    intro t ht1 ht2
    have hdist : dist t 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht1]
      exact ht2
    exact hP hdist ht1
  have hall : ∀ t, 0 < t → ∀ i, 0 < d i t := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t0, ht0, i0, hi0⟩ := hcon
    set C : Set ℝ := {t | η / 2 ≤ t ∧ ∃ i, d i t ≤ 0} with hC_def
    have ht0C : t0 ∈ C := by
      show η / 2 ≤ t0 ∧ ∃ i, d i t0 ≤ 0
      refine ⟨?_, i0, hi0⟩
      by_contra hlt
      push_neg at hlt
      have := hlocal t0 ht0 (by linarith) i0
      linarith
    have hCclosed : IsClosed C := by
      have hCeq : C = {t | η / 2 ≤ t} ∩ ⋃ i, {t | d i t ≤ 0} := by
        ext t
        simp only [C, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion]
      rw [hCeq]
      exact (isClosed_le continuous_const continuous_id).inter
        (isClosed_iUnion_of_finite fun i => isClosed_le (hdc i) continuous_const)
    have hbdd : BddBelow C := ⟨0, fun t ht => by
      have ht1 : η / 2 ≤ t := ht.1
      linarith⟩
    obtain ⟨τ, hτdef⟩ : ∃ τ, sInf C = τ := ⟨_, rfl⟩
    have hτC : τ ∈ C := by
      rw [← hτdef]
      exact hCclosed.csInf_mem ⟨t0, ht0C⟩ hbdd
    have hτC' : η / 2 ≤ τ ∧ ∃ i, d i τ ≤ 0 := hτC
    have hτpos : 0 < τ := by linarith [hτC'.1]
    have hbefore : ∀ t, 0 < t → t < τ → ∀ i, 0 < d i t := by
      intro t ht1 ht2 i
      by_cases htη : t < η
      · exact hlocal t ht1 htη i
      · push_neg at htη
        by_contra hneg
        push_neg at hneg
        have hmem : t ∈ C := by
          show η / 2 ≤ t ∧ ∃ i, d i t ≤ 0
          exact ⟨by linarith, i, hneg⟩
        have hle := csInf_le hbdd hmem
        rw [hτdef] at hle
        linarith
    have hnonneg : ∀ i, 0 ≤ d i τ := by
      intro i
      have hlim : Tendsto (d i) (𝓝[<] τ) (𝓝 (d i τ)) :=
        ((hdc i).tendsto τ).mono_left nhdsWithin_le_nhds
      exact ge_of_tendsto hlim
        (Filter.eventually_of_mem (Ioo_mem_nhdsLT hτpos) (fun t ht => (hbefore t ht.1 ht.2 i).le))
    have hmono : Monotone (v τ) := by
      rw [Fin.monotone_iff_le_succ]
      intro i
      have h1 := hnonneg i
      simp only [hd_def] at h1
      linarith
    obtain ⟨i1, hi1⟩ := hτC'.2
    have hd0 : d i1 τ = 0 := le_antisymm hi1 (hnonneg i1)
    have heq : v τ i1.castSucc = v τ i1.succ := by
      have h2 : v τ i1.succ - v τ i1.castSucc = 0 := by
        simpa [hd_def] using hd0
      linarith
    have hsign := sign_lemma L c hc q hq (cs_lt_s i1) (v τ) hmono heq
    have hpos : 0 < e i1 τ := by
      have h3 : e i1 τ = (q i1.succ - (Bmat L c q *ᵥ v τ) i1.succ)
          - (q i1.castSucc - (Bmat L c q *ᵥ v τ) i1.castSucc) := rfl
      rw [h3]
      linarith [hδ i1]
    obtain ⟨η', hη', hinc⟩ := local_increase (hd i1) (hec i1).continuousAt hpos
    have hm : 0 < min η' τ := lt_min hη' hτpos
    have hmτ : min η' τ ≤ τ := min_le_right _ _
    have hmη : min η' τ ≤ η' := min_le_left _ _
    have hs := hinc (τ - min η' τ / 2) τ (by linarith) (by linarith) (by linarith)
    have hs_pos := hbefore (τ - min η' τ / 2) (by linarith) (by linarith) i1
    linarith [hd0]
  intro t ht i
  have h := hall t ht i
  simp only [hd_def] at h
  linarith

/-- The matrix `B` as a continuous linear map of `Fin N → ℝ`. -/
def Acl (L c : ℝ) (q : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Bmat L c q))

lemma Acl_apply (L c : ℝ) (q u : Fin N → ℝ) : Acl L c q u = Bmat L c q *ᵥ u := by
  simp [Acl, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]

/-- `t ↦ exp(-tB) f`: the solution of `g' = -B g` with `g(0) = f = B^{-1} q`. -/
def gsol (L c : ℝ) (q : Fin N → ℝ) (t : ℝ) : Fin N → ℝ :=
  NormedSpace.exp (t • (-Acl L c q)) (respF L c q)

lemma gsol_zero (L c : ℝ) (q : Fin N → ℝ) : gsol L c q 0 = respF L c q := by
  simp [gsol, NormedSpace.exp_zero]

lemma hasDerivAt_gsol (L c : ℝ) (q : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    HasDerivAt (fun s => gsol L c q s i) (-(Bmat L c q *ᵥ gsol L c q t) i) t := by
  have h1 := hasDerivAt_exp_smul_const' (-Acl L c q) t
  have h2 := h1.clm_apply (hasDerivAt_const t (respF L c q))
  refine (hasDerivAt_pi.1 h2 i).congr_deriv ?_
  simp [gsol, Acl_apply]

lemma hasDerivAt_energy (L c : ℝ) (q : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∑ i, gsol L c q s i ^ 2)
      (∑ i, 2 * gsol L c q t i * (-(Bmat L c q *ᵥ gsol L c q t) i)) t := by
  have h : ∀ i ∈ (univ : Finset (Fin N)),
      HasDerivAt (fun s => gsol L c q s i ^ 2)
        (2 * gsol L c q t i * (-(Bmat L c q *ᵥ gsol L c q t) i)) t := by
    intro i _
    have h1 := (hasDerivAt_gsol L c q i t).pow 2
    convert h1 using 1
    norm_num
  exact HasDerivAt.fun_sum h

/-- Energy estimate: `E(t) exp(2Lt) ≤ E(0) = |f|^2` for `t ≥ 0`, with `E(t) = |g(t)|^2`. -/
lemma energy_decay {L c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ i, gsol L c q t i ^ 2) * Real.exp (2 * L * t) ≤ ∑ i, respF L c q i ^ 2 := by
  have hH : ∀ s, HasDerivAt (fun x => (∑ i, gsol L c q x i ^ 2) * Real.exp (2 * L * x))
      ((∑ i, 2 * gsol L c q s i * (-(Bmat L c q *ᵥ gsol L c q s) i)) * Real.exp (2 * L * s)
        + (∑ i, gsol L c q s i ^ 2) * (Real.exp (2 * L * s) * (2 * L * 1))) s := by
    intro s
    have h2 : HasDerivAt (fun x => Real.exp (2 * L * x))
        (Real.exp (2 * L * s) * (2 * L * 1)) s :=
      ((hasDerivAt_id' s).const_mul (2 * L)).exp
    exact (hasDerivAt_energy L c q s).mul h2
  have hanti : Antitone (fun x => (∑ i, gsol L c q x i ^ 2) * Real.exp (2 * L * x)) := by
    apply antitone_of_deriv_nonpos
    · exact fun x => (hH x).differentiableAt
    · intro x
      rw [(hH x).deriv]
      have hsum : ∑ i, 2 * gsol L c q x i * (-(Bmat L c q *ᵥ gsol L c q x) i)
          = -2 * ∑ i, gsol L c q x i * (Bmat L c q *ᵥ gsol L c q x) i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hsum]
      have hq := quad_ge (L := L) hc q (gsol L c q x)
      have hexp : 0 < Real.exp (2 * L * x) := Real.exp_pos _
      nlinarith [mul_nonneg hexp.le (sub_nonneg.2 hq)]
  have h2 : (∑ i, gsol L c q t i ^ 2) * Real.exp (2 * L * t)
      ≤ (∑ i, gsol L c q 0 i ^ 2) * Real.exp (2 * L * 0) := hanti ht
  have h1 : (∑ i, gsol L c q 0 i ^ 2) * Real.exp (2 * L * 0) = ∑ i, respF L c q i ^ 2 := by
    simp [gsol_zero]
  linarith

/-- Pointwise decay: `|g_j(t)| ≤ √(|f|^2) exp(-Lt)`. -/
lemma gsol_bound {L c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (j : Fin N) (t : ℝ)
    (ht : 0 ≤ t) :
    |gsol L c q t j| ≤ Real.sqrt (∑ i, respF L c q i ^ 2) * Real.exp (-(L * t)) := by
  have hp : 0 < Real.exp (L * t) := Real.exp_pos _
  have hpm : Real.exp (L * t) * Real.exp (-(L * t)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : gsol L c q t j ^ 2 ≤ ∑ i, gsol L c q t i ^ 2 :=
    Finset.single_le_sum (f := fun i => gsol L c q t i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h5 : (0 : ℝ) ≤ Real.exp (2 * L * t) := (Real.exp_pos _).le
  have h4 : Real.exp (2 * L * t) = Real.exp (L * t) * Real.exp (L * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkey : gsol L c q t j ^ 2 * (Real.exp (L * t) * Real.exp (L * t))
      ≤ ∑ i, respF L c q i ^ 2 := by
    have h1 := energy_decay (L := L) hc q t ht
    have h3 := mul_le_mul_of_nonneg_right h2 h5
    rw [← h4]
    linarith
  have hsq : (gsol L c q t j * Real.exp (L * t)) ^ 2 ≤ ∑ i, respF L c q i ^ 2 := by
    calc (gsol L c q t j * Real.exp (L * t)) ^ 2
        = gsol L c q t j ^ 2 * (Real.exp (L * t) * Real.exp (L * t)) := by ring
      _ ≤ ∑ i, respF L c q i ^ 2 := hkey
  have habs : |gsol L c q t j * Real.exp (L * t)| ≤ Real.sqrt (∑ i, respF L c q i ^ 2) :=
    Real.abs_le_sqrt hsq
  have hmul : |gsol L c q t j| * Real.exp (L * t) * Real.exp (-(L * t)) = |gsol L c q t j| := by
    rw [mul_assoc, hpm, mul_one]
  calc |gsol L c q t j|
      = |gsol L c q t j| * Real.exp (L * t) * Real.exp (-(L * t)) := hmul.symm
    _ = |gsol L c q t j * Real.exp (L * t)| * Real.exp (-(L * t)) := by
        rw [abs_mul, abs_of_pos hp]
    _ ≤ Real.sqrt (∑ i, respF L c q i ^ 2) * Real.exp (-(L * t)) :=
        mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le

/-- `v(t) → f`: the deviation `g(t) = exp(-tB) f` tends to zero coordinatewise. -/
lemma gsol_tendsto {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) (j : Fin N) :
    Tendsto (fun t => gsol L c q t j) atTop (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(L * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hL))
  have hb : Tendsto (fun t : ℝ => Real.sqrt (∑ i, respF L c q i ^ 2) * Real.exp (-(L * t)))
      atTop (𝓝 0) := by
    simpa using hexp.const_mul (Real.sqrt (∑ i, respF L c q i ^ 2))
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [Real.norm_eq_abs]
  exact gsol_bound hc q j t ht

/-- **CC:F02:ordered-response.** For strictly ordered `q`, `L > 0`, `c > 0` and `N > 1`, the vector
`f = B^{-1} q` (with `B` the matrix `CC:F02:matrix`) is strictly increasing in its index. -/
theorem ordered_response {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (hN : 1 < N)
    (q : Fin N → ℝ) (hq : StrictMono q) :
    StrictMono (respF L c q) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hBf : Bmat L c q *ᵥ respF L c q = q := Bmat_respF hL hc q
  set f := respF L c q with hf_def
  let v : ℝ → Fin (n + 1) → ℝ := fun t => f - gsol L c q t
  have hv : ∀ t i, HasDerivAt (fun s => v s i) (q i - (Bmat L c q *ᵥ v t) i) t := by
    intro t i
    refine ((hasDerivAt_const t (f i)).sub (hasDerivAt_gsol L c q i t)).congr_deriv ?_
    simp only [v, Matrix.mulVec_sub, hBf, Pi.sub_apply]
    ring
  have hv0 : v 0 = 0 := by
    funext i
    simp [v, gsol_zero, hf_def]
  have hcross := first_crossing (L := L) hc q hq v hv hv0
  have hadj : ∀ i : Fin n, f i.castSucc ≤ f i.succ := by
    intro i
    have hlim : Tendsto (fun t => gsol L c q t i.succ - gsol L c q t i.castSucc) atTop (𝓝 0) := by
      have := (gsol_tendsto hL hc q i.succ).sub (gsol_tendsto hL hc q i.castSucc)
      simpa using this
    have hle : ∀ᶠ t in atTop,
        gsol L c q t i.succ - gsol L c q t i.castSucc ≤ f i.succ - f i.castSucc := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      have h := hcross t ht i
      simp only [v, Pi.sub_apply] at h
      linarith
    have := le_of_tendsto hlim hle
    linarith
  have hmono : Monotone f := Fin.monotone_iff_le_succ.2 hadj
  refine Fin.strictMono_iff_lt_succ.2 (fun i => ?_)
  by_contra hcon
  push_neg at hcon
  have heq : f i.castSucc = f i.succ := le_antisymm (hadj i) hcon
  have hsign := sign_lemma L c hc q hq (cs_lt_s i) f hmono heq
  have h1 : (Bmat L c q *ᵥ f) i.succ = q i.succ := congrFun hBf _
  have h2 : (Bmat L c q *ᵥ f) i.castSucc = q i.castSucc := congrFun hBf _
  have h3 := hq (cs_lt_s i)
  linarith

end QuantumNLS.OrderedResponse

end

#print axioms QuantumNLS.OrderedResponse.wt_comm
#print axioms QuantumNLS.OrderedResponse.wt_pos
#print axioms QuantumNLS.OrderedResponse.wt_le_of_sq_le
#print axioms QuantumNLS.OrderedResponse.mulVec_Bmat_eq
#print axioms QuantumNLS.OrderedResponse.mulVec_Bmat_full
#print axioms QuantumNLS.OrderedResponse.cs_lt_s
#print axioms QuantumNLS.OrderedResponse.two_mul_sum_eq
#print axioms QuantumNLS.OrderedResponse.quad_ge
#print axioms QuantumNLS.OrderedResponse.Bmat_injective
#print axioms QuantumNLS.OrderedResponse.Bmat_isUnit_det
#print axioms QuantumNLS.OrderedResponse.Bmat_respF
#print axioms QuantumNLS.OrderedResponse.sign_lemma
#print axioms QuantumNLS.OrderedResponse.local_increase
#print axioms QuantumNLS.OrderedResponse.first_crossing
#print axioms QuantumNLS.OrderedResponse.Acl_apply
#print axioms QuantumNLS.OrderedResponse.gsol_zero
#print axioms QuantumNLS.OrderedResponse.hasDerivAt_gsol
#print axioms QuantumNLS.OrderedResponse.hasDerivAt_energy
#print axioms QuantumNLS.OrderedResponse.energy_decay
#print axioms QuantumNLS.OrderedResponse.gsol_bound
#print axioms QuantumNLS.OrderedResponse.gsol_tendsto
#print axioms QuantumNLS.OrderedResponse.ordered_response
