import QuantumNLS.BetheLabels
import QuantumNLS.RootDisplacement

/-!
# F05:root-comparison (R-7A6567D6): contraction and order of the rapidities

Source: `source/chapters/foundations/F05.tex`, Proposition `F05:root-comparison` (lines 14-34) and its
proof (lines 36-84); the section convention (lines 9-10) `p_n = 2πn/L`, coupling `c > 0`; the
Bethe equation `eq:root-bose-Bethe` of `source/chapters/foundations/ROOT_occupation_compactness.tex`
(lines 9-21): for strictly ordered real `q_1 < ⋯ < q_N` and nondecreasing integer labels
`n_1 ≤ ⋯ ≤ n_N`,  `L q_j = 2π n_j + 2 Σ_{k≠j} arctan (c / (q_j - q_k))`, `c > 0`,
principal arctangent. The torus length is `L > 0` (DEF-001).

**Indexing.** Lean indices are `j : Fin N`, zero based; the source's `j` is `j.val + 1`.

## Formal content
* `IsActualConfig L c n q` (an "actual repulsive Bethe configuration"): `c > 0`, `q` strictly
  increasing, `n` nondecreasing, and the literal printed equation `BoseBethe L c n q`.
* Bridge to the accepted roots (R-4C8D7C9E via DEF-006 `BetheLabels`): `isActual_iff_eq_roots`,
  `isActual_iff_solves`, `rapidityEq_iff_isActual`, `isActual_roots`.
* The printed proof: `Tmap` (the map `T`), `arctan_div_add_arctan_div` (principal-branch identity),
  `sum_sign_erase`, `log_equation` (`F05:log-equation`), `Tmap_hasFDerivAt`/`jacobian_symm`/
  `jacobian_quadratic` (`F05:jacobian`), `Bavg` (`B = ∫_0^1 DT(q+td) dt`, entrywise),
  `Bavg_apply` (`B = L·Id + graph Laplacian` with the printed weights `wAvg`), `Bavg_response`
  and `averaged_response` (`F05:averaged-response`), `Bavg_quad`, `Bavg_nonneg_of_nonneg` and
  `Bavg_inv_nonneg` (inverse positivity), `Bavg_inv_row_sum`/`Bavg_inv_col_sum` (completeness remark).
* The proposition: `finite_contraction` (`F05:finite-contraction`), `order_of_labels`,
  `total_response` (`F05:total-response`), assembled in `root_comparison`; the same for the
  accepted root vectors in `root_comparison_roots`.

## Recorded deviations from the printed proof (none changes the statement)
* `B = ∫_0^1 DT(q+td) dt` is formed entrywise with interval integrals of the Gaudin-matrix entries
  (`Bavg`, `Bavg_eq_integral_jacobian`); no Bochner integral of matrices is used. Its graph-Laplacian
  form (`Bavg_apply`, printed second paragraph) is proved first, and `B d = T(q̃) - T(q)` then follows
  pairwise from the fundamental theorem of calculus for `t ↦ 2 arctan ((a + tδ)/c)` (`wInt_ftc`).
* Inverse positivity is proved as the printed minimum principle (`Bx = y`, `y ≥ 0` ⇒ `x ≥ 0`) and
  applied directly to `F05:averaged-response`; `Bavg_inv_nonneg` additionally records `B⁻¹ ≥ 0`.
* Cauchy–Schwarz is used in squared form `⟨d, e⟩² ≤ |d|²|e|²` (no square roots).
* `L > 0` (DEF-001) is an explicit hypothesis; `1/N` is Lean's real division (the case `N = 0` is
  vacuous: both sums are empty).
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace QuantumNLS.RootContraction

open QuantumNLS.BetheAdmission QuantumNLS.BetheRoots QuantumNLS.BetheSmooth QuantumNLS.BetheLabels
open QuantumNLS.OrderedResponse
open scoped Matrix

variable {N : ℕ}

/-! ## 1. Definitions: `p_n`, the printed Bethe equation, actual configurations, the map `T` -/

/-- Section convention of F05: `p_n = 2πn/L`. -/
def pLab (L : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * n / L

/-- `eq:root-bose-Bethe`, literally: `L q_j = 2π n_j + 2 Σ_{k ≠ j} arctan (c / (q_j - q_k))`
(principal `Real.arctan`). -/
def BoseBethe (L c : ℝ) (n : Fin N → ℤ) (q : Fin N → ℝ) : Prop :=
  ∀ j, L * q j = 2 * Real.pi * (n j : ℝ) + 2 * ∑ k ∈ univ.erase j, Real.arctan (c / (q j - q k))

/-- An **actual repulsive Bethe configuration** with ordered bosonic labels: `c > 0`, strictly
ordered real rapidities `q_1 < ⋯ < q_N`, nondecreasing integer labels `n_1 ≤ ⋯ ≤ n_N`, solving
`eq:root-bose-Bethe`. -/
structure IsActualConfig (L c : ℝ) (n : Fin N → ℤ) (q : Fin N → ℝ) : Prop where
  c_pos : 0 < c
  sorted : StrictMono q
  labels_sorted : Monotone n
  bethe : BoseBethe L c n q

/-- The printed map `T_j(x) = L x_j + 2 Σ_{k ≠ j} arctan ((x_j - x_k)/c)` on `ℝ^N`. -/
def Tmap (L c : ℝ) (x : Fin N → ℝ) (j : Fin N) : ℝ :=
  L * x j + 2 * ∑ k ∈ univ.erase j, Real.arctan ((x j - x k) / c)

/-- `T` is the accepted globally smooth logarithmic Bethe map `BetheAdmission.logMap`. -/
theorem Tmap_eq_logMap (L c : ℝ) : Tmap (N := N) L c = logMap L c := by
  funext x j
  rw [logMap_erase]
  rfl

/-! ## 2. The principal-branch identity and `F05:log-equation` -/

/-- Principal-branch identity: `arctan (c/d) + arctan (d/c) = (π/2) sgn d` for `d ≠ 0`, `c > 0`. -/
theorem arctan_div_add_arctan_div {c d : ℝ} (hc : 0 < c) (hd : d ≠ 0) :
    Real.arctan (c / d) + Real.arctan (d / c) = Real.pi / 2 * Real.sign d := by
  rw [show c / d = (d / c)⁻¹ from (inv_div d c).symm]
  rcases lt_or_gt_of_ne hd with h | h
  · have hdc : d / c < 0 := div_neg_of_neg_of_pos h hc
    rw [Real.arctan_inv_of_neg hdc, Real.sign_of_neg h]
    ring
  · have hdc : 0 < d / c := div_pos h hc
    rw [Real.arctan_inv_of_pos hdc, Real.sign_of_pos h]
    ring

/-- "The sum of the signs of `q_j - q_k` is `2j - N - 1`" (one-based `j = i.val + 1`). -/
theorem sum_sign_erase {q : Fin N → ℝ} (hq : StrictMono q) (i : Fin N) :
    ∑ k ∈ univ.erase i, Real.sign (q i - q k) = 2 * ((i.val : ℝ) + 1) - (N : ℝ) - 1 := by
  have h1 : ∀ k ∈ univ.erase i, Real.sign (q i - q k) =
      (if k < i then (1 : ℝ) else 0) - (if i < k then (1 : ℝ) else 0) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rcases lt_or_gt_of_ne hki with h | h
    · have h' : q k < q i := hq h
      have hnlt : ¬ i < k := not_lt.mpr h.le
      rw [Real.sign_of_pos (by linarith), ite_eq_left h, ite_eq_right hnlt]
      ring
    · have h' : q i < q k := hq h
      have hnl : ¬ k < i := not_lt.mpr h.le
      rw [Real.sign_of_neg (by linarith), ite_eq_right hnl, ite_eq_left h]
      ring
  have hA : ∑ k : Fin N, (if k < i then (1 : ℝ) else 0) = (i.val : ℝ) := by
    rw [Finset.sum_boole]
    have hset : (Finset.univ.filter fun k : Fin N => k < i) = Finset.Iio i := by
      ext k; simp
    rw [hset, Fin.card_Iio]
  have hB : ∑ k : Fin N, (if i < k then (1 : ℝ) else 0) = (N : ℝ) - 1 - (i.val : ℝ) := by
    rw [Finset.sum_boole]
    have hset : (Finset.univ.filter fun k : Fin N => i < k) = Finset.Ioi i := by
      ext k; simp
    rw [hset, Fin.card_Ioi]
    have hi := i.isLt
    have h1 : i.val ≤ N - 1 := by omega
    have h2 : 1 ≤ N := by omega
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_erase_eq_sub (Finset.mem_univ i),
    Finset.sum_sub_distrib, hA, hB]
  have hdiag : ((if i < i then (1 : ℝ) else 0) - (if i < i then (1 : ℝ) else 0)) = 0 :=
    sub_self _
  rw [hdiag]
  ring

/-- For strictly ordered `q` and `c > 0`, the printed pair sum in terms of `T`'s pair sum. -/
theorem pair_sum_eq {c : ℝ} (hc : 0 < c) {q : Fin N → ℝ} (hq : StrictMono q) (j : Fin N) :
    ∑ k ∈ univ.erase j, Real.arctan (c / (q j - q k)) =
      Real.pi / 2 * (2 * ((j.val : ℝ) + 1) - (N : ℝ) - 1) -
        ∑ k ∈ univ.erase j, Real.arctan ((q j - q k) / c) := by
  have hs : ∀ k ∈ univ.erase j, Real.arctan (c / (q j - q k)) =
      Real.pi / 2 * Real.sign (q j - q k) - Real.arctan ((q j - q k) / c) := by
    intro k hk
    have hne : q j - q k ≠ 0 :=
      sub_ne_zero.mpr (hq.injective.ne (Finset.ne_of_mem_erase hk).symm)
    have := arctan_div_add_arctan_div hc hne
    linarith
  rw [Finset.sum_congr rfl hs, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_sign_erase hq j]

/-- `eq:root-bose-Bethe` ⇔ `F05:log-equation` `T_j(q) = 2π (n_j + j - (N+1)/2)` (one-based `j`),
for strictly ordered `q` and `c > 0`. -/
theorem boseBethe_iff_log {L c : ℝ} (hc : 0 < c) {q : Fin N → ℝ} (hq : StrictMono q)
    (n : Fin N → ℤ) :
    BoseBethe L c n q ↔ ∀ j, Tmap L c q j =
      2 * Real.pi * ((n j : ℝ) + ((j.val : ℝ) + 1) - ((N : ℝ) + 1) / 2) := by
  unfold BoseBethe Tmap
  refine forall_congr' fun j => ?_
  rw [pair_sum_eq hc hq j]
  constructor <;> intro h <;> linarith

/-- **`F05:log-equation`** for an actual configuration. -/
theorem log_equation {L c : ℝ} {n : Fin N → ℤ} {q : Fin N → ℝ} (h : IsActualConfig L c n q)
    (j : Fin N) :
    Tmap L c q j = 2 * Real.pi * ((n j : ℝ) + ((j.val : ℝ) + 1) - ((N : ℝ) + 1) / 2) :=
  (boseBethe_iff_log h.c_pos h.sorted n).1 h.bethe j

/-- The log-equation is the accepted system `Solves` (labels `quantumNumbers n`). -/
theorem log_iff_solves (L c : ℝ) (n : Fin N → ℤ) (q : Fin N → ℝ) :
    (∀ j, Tmap L c q j =
      2 * Real.pi * ((n j : ℝ) + ((j.val : ℝ) + 1) - ((N : ℝ) + 1) / 2)) ↔ Solves L c n q := by
  rw [Tmap_eq_logMap]
  unfold Solves quantumNumbers
  refine forall_congr' fun j => ?_
  rw [show (n j : ℝ) + ((j.val : ℝ) + 1) - ((N : ℝ) + 1) / 2 =
    (n j : ℝ) + (j.val : ℝ) - ((N : ℝ) - 1) / 2 by ring]

/-! ## 3. Bridge to the accepted roots (R-4C8D7C9E) and DEF-006 labels -/

/-- An actual configuration is exactly a sorted-label solution of the accepted system. -/
theorem isActual_iff_solves {L c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Monotone n)
    (q : Fin N → ℝ) (hL : 0 < L) : IsActualConfig L c n q ↔ Solves L c n q := by
  constructor
  · intro h
    exact (log_iff_solves L c n q).1 (log_equation h)
  · intro hs
    have hsorted := roots_strictMono hL hc ⟨n, hn⟩ hs
    exact ⟨hc, hsorted, hn, (boseBethe_iff_log hc hsorted n).2 ((log_iff_solves L c n q).2 hs)⟩

/-- **Identification with the accepted root vector**: for `L, c > 0` and nondecreasing integer
labels `n`, the actual configuration with labels `n` is exactly `BetheSmooth.roots L n c`. -/
theorem isActual_iff_eq_roots {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ}
    (hn : Monotone n) (q : Fin N → ℝ) : IsActualConfig L c n q ↔ q = roots L n c := by
  rw [isActual_iff_solves hc hn q hL]
  constructor
  · intro hs
    exact BetheConvexity.eq_root hL hc (funext hs)
  · rintro rfl
    exact roots_solves hL hc n

/-- Actual configurations exist for every nondecreasing integer label vector (accepted roots). -/
theorem isActual_roots {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Monotone n) :
    IsActualConfig L c n (roots L n c) :=
  (isActual_iff_eq_roots hL hc hn _).2 rfl

/-- **DEF-006 bridge** (`BetheLabels`): with the logarithmic labels `I = labelsOf n`
(`I_j = n_j + j - (N+1)/2`), the DEF-006 rapidity equation is exactly an actual configuration. -/
theorem rapidityEq_iff_isActual {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ}
    (hn : Monotone n) (q : Fin N → ℝ) :
    RapidityEq L c (labelsOf ⟨n, hn⟩).I q ↔ IsActualConfig L c n q := by
  have hcorr : correctedInt (labelsOf ⟨n, hn⟩) = n :=
    congrArg Subtype.val (labelsEquivCorrected.right_inv ⟨n, hn⟩)
  rw [rapidityEq_iff_roots hL hc, hcorr, isActual_iff_eq_roots hL hc hn]

/-! ## 4. `F05:jacobian`: the derivative of `T` -/

/-- `T` is differentiable with derivative the accepted Gaudin map. -/
theorem Tmap_hasFDerivAt (L : ℝ) {c : ℝ} (hc : 0 < c) (x : Fin N → ℝ) :
    HasFDerivAt (Tmap L c) (gaudin L c x) x := by
  rw [Tmap_eq_logMap]
  exact logMap_hasFDerivAt L hc x

/-- Matrix entries of `DT(x)`: `(DT(x) e_k)_i = Bmat L c x i k`. -/
theorem jacobian_entry (L c : ℝ) (x : Fin N → ℝ) (i k : Fin N) :
    gaudin L c x (Pi.single k 1) i = Bmat L c x i k :=
  (RootDisplacement.Bmat_apply_eq_gaudin L c x i k).symm

/-- "The Jacobian of `T` is symmetric." -/
theorem jacobian_symm (L c : ℝ) (x : Fin N → ℝ) : (Bmat L c x).transpose = Bmat L c x := by
  ext i k
  simp only [Matrix.transpose_apply, Bmat, Matrix.of_apply]
  by_cases h : i = k
  · subst h; rfl
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, wt_comm]

/-- Symmetric off-diagonal double sums: `Σ_{i,k} f = 2 Σ_{i<k} f` when `f` is symmetric and vanishes
on the diagonal. -/
theorem sum_sum_eq_two_mul_lt (f : Fin N → Fin N → ℝ) (hf : ∀ i k, f i k = f k i)
    (hd : ∀ i, f i i = 0) :
    ∑ i, ∑ k, f i k = 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), f i k := by
  have hsplit : ∀ i k, f i k = (if i < k then f i k else 0) + (if k < i then f i k else 0) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h.le)]; ring
    · subst h; simp [hd]
    · rw [ite_eq_right (not_lt.mpr h.le), ite_eq_left h]; ring
  have hswap : ∑ i, ∑ k, (if k < i then f i k else 0) = ∑ i, ∑ k, (if i < k then f i k else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hf k i]
  calc ∑ i, ∑ k, f i k
      = ∑ i, ∑ k, ((if i < k then f i k else 0) + (if k < i then f i k else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsplit i k
    _ = ∑ i, ∑ k, (if i < k then f i k else 0) + ∑ i, ∑ k, (if k < i then f i k else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), f i k := by
        rw [hswap, ← two_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_filter _ _).symm

/-- **`F05:jacobian`**: `hᵀ DT(x) h = L Σ_j h_j² + Σ_{j<k} 2c/(c²+(x_j-x_k)²) (h_j-h_k)²
≥ L Σ_j h_j²`. -/
theorem jacobian_quadratic (L : ℝ) {c : ℝ} (hc : 0 < c) (x h : Fin N → ℝ) :
    (∑ j, h j * gaudin L c x h j = L * ∑ j, h j ^ 2 +
      ∑ j, ∑ k ∈ univ.filter (fun k => j < k),
        2 * c / (c ^ 2 + (x j - x k) ^ 2) * (h j - h k) ^ 2) ∧
    L * ∑ j, h j ^ 2 ≤ ∑ j, h j * gaudin L c x h j := by
  refine ⟨?_, gaudin_lower_bound L hc x h⟩
  rw [gaudin_quadratic]
  have := sum_sum_eq_two_mul_lt (fun j k => edgeWeight c x j k * (h j - h k) ^ 2)
    (fun j k => by rw [edgeWeight_symm c x j k]; ring) (fun j => by simp)
  rw [this]
  simp only [edgeWeight]
  ring

/-! ## 5. The averaged matrix `B = ∫_0^1 DT(q+td) dt` -/

/-- The integrand `2c/(c² + (a + tδ)²)`. -/
def wInt (c a δ t : ℝ) : ℝ := 2 * c / (c ^ 2 + (a + t * δ) ^ 2)

theorem wInt_den_pos {c : ℝ} (hc : 0 < c) (a δ t : ℝ) : 0 < c ^ 2 + (a + t * δ) ^ 2 :=
  add_pos_of_pos_of_nonneg (pow_pos hc 2) (sq_nonneg _)

theorem wInt_continuous {c : ℝ} (hc : 0 < c) (a δ : ℝ) : Continuous (wInt c a δ) := by
  unfold wInt
  exact Continuous.div continuous_const (by fun_prop) (fun t => (wInt_den_pos hc a δ t).ne')

theorem wInt_pos {c : ℝ} (hc : 0 < c) (a δ t : ℝ) : 0 < wInt c a δ t :=
  div_pos (by linarith) (wInt_den_pos hc a δ t)

/-- The printed weights `w_jk = ∫_0^1 2c/(c² + (q_j - q_k + t(d_j - d_k))²) dt`. -/
def wAvg (c : ℝ) (q d : Fin N → ℝ) (j k : Fin N) : ℝ :=
  ∫ t in (0 : ℝ)..1, 2 * c / (c ^ 2 + (q j - q k + t * (d j - d k)) ^ 2)

theorem wAvg_eq (c : ℝ) (q d : Fin N → ℝ) (j k : Fin N) :
    wAvg c q d j k = ∫ t in (0 : ℝ)..1, wInt c (q j - q k) (d j - d k) t := rfl

/-- The weights are positive. -/
theorem wAvg_pos {c : ℝ} (hc : 0 < c) (q d : Fin N → ℝ) (j k : Fin N) : 0 < wAvg c q d j k := by
  rw [wAvg_eq]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((wInt_continuous hc _ _).intervalIntegrable 0 1) (fun t _ => wInt_pos hc _ _ t) zero_lt_one

/-- The weights are symmetric. -/
theorem wAvg_symm (c : ℝ) (q d : Fin N → ℝ) (j k : Fin N) : wAvg c q d j k = wAvg c q d k j := by
  unfold wAvg
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [show (q j - q k + t * (d j - d k)) ^ 2 = (q k - q j + t * (d k - d j)) ^ 2 by ring]

/-- Fundamental theorem of calculus for one pair. -/
theorem wInt_ftc {c : ℝ} (hc : 0 < c) (a δ : ℝ) :
    δ * ∫ t in (0 : ℝ)..1, wInt c a δ t =
      2 * (Real.arctan ((a + δ) / c) - Real.arctan (a / c)) := by
  rw [← intervalIntegral.integral_const_mul]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => 2 * Real.arctan ((a + t * δ) / c)) (δ * wInt c a δ t) t := by
    intro t _
    have h1 : HasDerivAt (fun t => (a + t * δ) / c) (δ / c) t := by
      have := (((hasDerivAt_id t).mul_const δ).const_add a).div_const c
      simpa using this
    have h2 := (h1.arctan).const_mul 2
    convert h2 using 1
    unfold wInt
    have hc' : c ≠ 0 := hc.ne'
    have hden := (wInt_den_pos hc a δ t).ne'
    have hden2 : 1 + ((a + t * δ) / c) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (wInt_continuous hc a δ)).intervalIntegrable 0 1)]
  simp only [one_mul, zero_mul, add_zero]
  ring

/-- `w_jk (d_j - d_k) = 2 [arctan ((q̃_j - q̃_k)/c) - arctan ((q_j - q_k)/c)]` with `q̃ = q + d`. -/
theorem wAvg_pair {c : ℝ} (hc : 0 < c) (q d : Fin N → ℝ) (j k : Fin N) :
    wAvg c q d j k * (d j - d k) =
      2 * (Real.arctan ((q j + d j - (q k + d k)) / c) - Real.arctan ((q j - q k) / c)) := by
  rw [mul_comm, wAvg_eq, wInt_ftc hc]
  rw [show q j - q k + (d j - d k) = q j + d j - (q k + d k) by ring]

/-- **The averaged Jacobian** `B = ∫_0^1 DT(q + t d) dt`, entrywise (`Bmat = DT`, see
`jacobian_entry`). -/
def Bavg (L c : ℝ) (q d : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i k => ∫ t in (0 : ℝ)..1, Bmat L c (fun j => q j + t * d j) i k

/-- `B_ik = ∫_0^1 (DT(q + t d) e_k)_i dt`, literally. -/
theorem Bavg_eq_integral_jacobian (L c : ℝ) (q d : Fin N → ℝ) (i k : Fin N) :
    Bavg L c q d i k =
      ∫ t in (0 : ℝ)..1, gaudin L c (fun j => q j + t * d j) (Pi.single k 1) i := by
  simp only [Bavg, Matrix.of_apply, jacobian_entry]

theorem wt_path (c : ℝ) (q d : Fin N → ℝ) (t : ℝ) (i l : Fin N) :
    wt c (q i + t * d i) (q l + t * d l) = wInt c (q i - q l) (d i - d l) t := by
  unfold wt wInt
  rw [show q i + t * d i - (q l + t * d l) = q i - q l + t * (d i - d l) by ring]

/-- **`B` is `L` times the identity plus a graph Laplacian with the printed weights `w_jk`.** -/
theorem Bavg_apply {L c : ℝ} (hc : 0 < c) (q d : Fin N → ℝ) (i k : Fin N) :
    Bavg L c q d i k =
      if i = k then L + ∑ l ∈ univ.erase i, wAvg c q d i l else -wAvg c q d i k := by
  by_cases h : i = k
  · subst h
    simp only [Bavg, Bmat, Matrix.of_apply, ite_true, wt_path]
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((continuous_finsetSum _ fun l _ => wInt_continuous hc _ _).intervalIntegrable 0 1),
      intervalIntegral.integral_finsetSum
        (fun l _ => (wInt_continuous hc _ _).intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    rfl
  · simp only [Bavg, Bmat, Matrix.of_apply, h, ite_false, wt_path]
    rw [intervalIntegral.integral_neg]
    rfl

/-- `(B x)_i = L x_i + Σ_{l ≠ i} w_il (x_i - x_l)`. -/
theorem Bavg_mulVec {L c : ℝ} (hc : 0 < c) (q d x : Fin N → ℝ) (i : Fin N) :
    (Bavg L c q d *ᵥ x) i = L * x i + ∑ l ∈ univ.erase i, wAvg c q d i l * (x i - x l) := by
  simp only [Matrix.mulVec, dotProduct, Bavg_apply hc]
  rw [← Finset.add_sum_erase univ _ (mem_univ i), ite_eq_left rfl]
  have h2 : ∀ k ∈ univ.erase i,
      (if i = k then L + ∑ l ∈ univ.erase i, wAvg c q d i l else -wAvg c q d i k) * x k
        = -(wAvg c q d i k * x k) := by
    intro k hk
    rw [ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hk))]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
  have h3 : ∑ l ∈ univ.erase i, wAvg c q d i l * (x i - x l)
      = (∑ l ∈ univ.erase i, wAvg c q d i l) * x i
        - ∑ l ∈ univ.erase i, wAvg c q d i l * x l := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [h3]
  ring

/-- **`F05:averaged-response`, general form**: `B d = T(q + d) - T(q)`. -/
theorem Bavg_response {L c : ℝ} (hc : 0 < c) (q d : Fin N → ℝ) (i : Fin N) :
    (Bavg L c q d *ᵥ d) i = Tmap L c (fun j => q j + d j) i - Tmap L c q i := by
  rw [Bavg_mulVec hc]
  simp only [Tmap]
  rw [Finset.sum_congr rfl (fun l _ => wAvg_pair hc q d i l), ← Finset.mul_sum,
    Finset.sum_sub_distrib]
  ring

/-- `B` is symmetric. -/
theorem Bavg_transpose {L c : ℝ} (hc : 0 < c) (q d : Fin N → ℝ) :
    (Bavg L c q d).transpose = Bavg L c q d := by
  ext i k
  rw [Matrix.transpose_apply, Bavg_apply hc, Bavg_apply hc]
  by_cases h : i = k
  · subst h; rfl
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, wAvg_symm]

/-- Graph-Laplacian positivity for symmetric nonnegative weights. -/
theorem laplacian_nonneg (W : Fin N → Fin N → ℝ) (hW : ∀ i k, W i k = W k i)
    (hpos : ∀ i k, 0 ≤ W i k) (x : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ k, W i k * (x i * (x i - x k)) := by
  have hS : ∑ i, ∑ k, W i k * (x i * (x i - x k)) = ∑ i, ∑ k, W i k * (x k * (x k - x i)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hW k i]
  have h2 : 2 * ∑ i, ∑ k, W i k * (x i * (x i - x k)) = ∑ i, ∑ k, W i k * (x i - x k) ^ 2 := by
    rw [two_mul]
    nth_rewrite 1 [hS]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have h3 : 0 ≤ ∑ i, ∑ k, W i k * (x i - x k) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => mul_nonneg (hpos i k) (sq_nonneg _)))
  linarith

/-- The averaged form of `F05:jacobian`: `xᵀ B x ≥ L |x|²`. -/
theorem Bavg_quad {L c : ℝ} (hc : 0 < c) (q d x : Fin N → ℝ) :
    L * ∑ i, x i ^ 2 ≤ ∑ i, x i * (Bavg L c q d *ᵥ x) i := by
  have h1 : ∀ i, x i * (Bavg L c q d *ᵥ x) i
      = L * x i ^ 2 + ∑ k, wAvg c q d i k * (x i * (x i - x k)) := by
    intro i
    rw [Bavg_mulVec hc, mul_add, Finset.mul_sum]
    rw [Finset.sum_erase (f := fun k => x i * (wAvg c q d i k * (x i - x k))) univ (by simp)]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun k _ => by ring)
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  have := laplacian_nonneg (wAvg c q d) (wAvg_symm c q d) (fun i k => (wAvg_pos hc q d i k).le) x
  linarith

/-- **Inverse positivity (minimum principle)**: if `B x = y` with `y ≥ 0`, then `x ≥ 0`. -/
theorem Bavg_nonneg_of_nonneg {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q d x : Fin N → ℝ)
    (hy : ∀ i, 0 ≤ (Bavg L c q d *ᵥ x) i) : ∀ i, 0 ≤ x i := by
  intro k
  by_contra hk
  push Not at hk
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image univ x ⟨k, mem_univ k⟩
  have hxi : x i < 0 := lt_of_le_of_lt (hi k (mem_univ k)) hk
  have hterm : ∑ l ∈ univ.erase i, wAvg c q d i l * (x i - x l) ≤ 0 := by
    refine Finset.sum_nonpos (fun l _ => ?_)
    have hw := (wAvg_pos hc q d i l).le
    have hl : x i - x l ≤ 0 := by linarith [hi l (mem_univ l)]
    nlinarith
  have hyi := hy i
  rw [Bavg_mulVec hc] at hyi
  nlinarith

/-- `B` is injective (from the quadratic bound). -/
theorem Bavg_injective {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q d : Fin N → ℝ) :
    Function.Injective (Bavg L c q d).mulVec := by
  intro u v huv
  have hx : Bavg L c q d *ᵥ (u - v) = 0 := by
    have huv' : Bavg L c q d *ᵥ u = Bavg L c q d *ᵥ v := huv
    rw [Matrix.mulVec_sub, huv', sub_self]
  have hq := Bavg_quad (L := L) hc q d (u - v)
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

/-- "It is invertible by `F05:jacobian`." -/
theorem Bavg_isUnit_det {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q d : Fin N → ℝ) :
    IsUnit (Bavg L c q d).det :=
  (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_injective_iff_isUnit.1 (Bavg_injective hL hc q d))

/-- "Its inverse has nonnegative entries." -/
theorem Bavg_inv_nonneg {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q d : Fin N → ℝ) (i k : Fin N) :
    0 ≤ (Bavg L c q d)⁻¹ i k := by
  have hu := Bavg_isUnit_det hL hc q d
  have hcol : (Bavg L c q d)⁻¹ *ᵥ Pi.single k 1 = fun i => (Bavg L c q d)⁻¹ i k := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hB : Bavg L c q d *ᵥ ((Bavg L c q d)⁻¹ *ᵥ Pi.single k 1) = Pi.single k 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hnn : ∀ j, 0 ≤ (Bavg L c q d *ᵥ ((Bavg L c q d)⁻¹ *ᵥ Pi.single k 1)) j := by
    rw [hB]
    intro j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  have := Bavg_nonneg_of_nonneg hL hc q d _ hnn i
  rwa [hcol] at this

/-- `B 1 = L 1`. -/
theorem Bavg_mulVec_one {L c : ℝ} (hc : 0 < c) (q d : Fin N → ℝ) :
    Bavg L c q d *ᵥ (fun _ => (1 : ℝ)) = fun _ => L := by
  funext i
  rw [Bavg_mulVec hc]
  simp

/-- Completeness remark: every row of `B⁻¹` sums to `1/L`. -/
theorem Bavg_inv_row_sum {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q d : Fin N → ℝ) (i : Fin N) :
    ∑ k, (Bavg L c q d)⁻¹ i k = 1 / L := by
  have hu := Bavg_isUnit_det hL hc q d
  have h1 : (Bavg L c q d)⁻¹ *ᵥ (fun _ => L) = fun _ => (1 : ℝ) := by
    rw [← Bavg_mulVec_one hc q d, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec]
  have h2 := congrFun h1 i
  simp only [Matrix.mulVec, dotProduct] at h2
  rw [← Finset.sum_mul] at h2
  field_simp
  linarith

/-- Completeness remark: every column of `B⁻¹` sums to `1/L` (by symmetry). -/
theorem Bavg_inv_col_sum {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q d : Fin N → ℝ) (k : Fin N) :
    ∑ i, (Bavg L c q d)⁻¹ i k = 1 / L := by
  have hT : ((Bavg L c q d)⁻¹).transpose = (Bavg L c q d)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Bavg_transpose hc]
  rw [← Bavg_inv_row_sum hL hc q d k]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hT, Matrix.transpose_apply, hT]

/-! ## 6. The proposition -/

section Proposition

variable {L c : ℝ} {n nt : Fin N → ℤ} {q qt : Fin N → ℝ}

/-- **`F05:averaged-response`**: with `d = q̃ - q`, `B d = 2π (ñ - n)`; the rank shifts cancel. -/
theorem averaged_response (h : IsActualConfig L c n q) (h' : IsActualConfig L c nt qt) :
    Bavg L c q (fun j => qt j - q j) *ᵥ (fun j => qt j - q j) =
      fun j => 2 * Real.pi * ((nt j : ℝ) - n j) := by
  funext i
  rw [Bavg_response h.c_pos]
  have e : (fun j => q j + (qt j - q j)) = qt := by funext j; ring
  rw [e, log_equation h' i, log_equation h i]
  ring

/-- **`F05:finite-contraction`**:
`(1/N) Σ_j |q_j - q̃_j|² ≤ (1/N) Σ_j |p_{n_j} - p_{ñ_j}|²`. -/
theorem finite_contraction (hL : 0 < L) (h : IsActualConfig L c n q)
    (h' : IsActualConfig L c nt qt) :
    (1 / (N : ℝ)) * ∑ j, |q j - qt j| ^ 2 ≤
      (1 / (N : ℝ)) * ∑ j, |pLab L (n j) - pLab L (nt j)| ^ 2 := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hquad := Bavg_quad (L := L) h.c_pos q (fun j => qt j - q j) (fun j => qt j - q j)
  rw [averaged_response h h'] at hquad
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => qt j - q j)
    (fun j => 2 * Real.pi * ((nt j : ℝ) - n j))
  have hA : ∑ j, |q j - qt j| ^ 2 = ∑ j, (qt j - q j) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [sq_abs]; ring
  have hB : ∑ j, |pLab L (n j) - pLab L (nt j)| ^ 2 =
      (∑ j, (2 * Real.pi * ((nt j : ℝ) - n j)) ^ 2) / L ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sq_abs]
    simp only [pLab]
    field_simp
    ring
  rw [hA, hB]
  simp only at hquad hcs
  have hA0 : 0 ≤ ∑ j, (qt j - q j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB0 : 0 ≤ ∑ j, (2 * Real.pi * ((nt j : ℝ) - n j)) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  generalize ∑ j, (qt j - q j) ^ 2 = A at hquad hcs hA0 ⊢
  generalize ∑ j, (2 * Real.pi * ((nt j : ℝ) - n j)) ^ 2 = B at hcs hB0 ⊢
  generalize ∑ j, (qt j - q j) * (2 * Real.pi * ((nt j : ℝ) - n j)) = S at hquad hcs
  rw [le_div_iff₀ (by positivity)]
  rcases hA0.eq_or_lt with h0 | hpos
  · -- `d = 0`: the contraction is immediate.
    rw [← h0]; simpa using hB0
  · -- otherwise: `L|d|² ≤ ⟨B d, d⟩ = 2π⟨ñ - n, d⟩ ≤ 2π|ñ - n||d|`; divide and square.
    have h1 : (L * A) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (mul_nonneg hL.le hA0) hquad 2
    have h2 : L ^ 2 * A * A ≤ B * A := by nlinarith
    have := le_of_mul_le_mul_right h2 hpos
    linarith

/-- **Order**: if `n_j ≤ ñ_j` for every `j`, then `q_j ≤ q̃_j` for every `j`
(inverse positivity of `B` applied to `F05:averaged-response`). -/
theorem order_of_labels (hL : 0 < L) (h : IsActualConfig L c n q) (h' : IsActualConfig L c nt qt)
    (hle : ∀ j, n j ≤ nt j) : ∀ j, q j ≤ qt j := by
  intro j
  have hnn : ∀ i, 0 ≤ (Bavg L c q (fun j => qt j - q j) *ᵥ (fun j => qt j - q j)) i := by
    intro i
    rw [averaged_response h h']
    have hi : (n i : ℝ) ≤ nt i := by exact_mod_cast hle i
    have := Real.pi_pos
    dsimp only
    nlinarith
  have := Bavg_nonneg_of_nonneg hL h.c_pos q (fun j => qt j - q j) _ hnn j
  linarith

/-- Summing `F05:log-equation`: the pair terms cancel, `Σ_j T_j(q) = L Σ_j q_j`. -/
theorem sum_log_equation (h : IsActualConfig L c n q) :
    L * ∑ j, q j =
      ∑ j : Fin N, 2 * Real.pi * ((n j : ℝ) + ((j.val : ℝ) + 1) - ((N : ℝ) + 1) / 2) := by
  rw [← sum_logMap L c q, ← Tmap_eq_logMap]
  exact Finset.sum_congr rfl fun j _ => log_equation h j

/-- **`F05:total-response`**: `Σ_j (q̃_j - q_j) = (2π/L) Σ_j (ñ_j - n_j)`; the rank shifts cancel. -/
theorem total_response (hL : 0 < L) (h : IsActualConfig L c n q) (h' : IsActualConfig L c nt qt) :
    ∑ j, (qt j - q j) = 2 * Real.pi / L * ∑ j, ((nt j : ℝ) - n j) := by
  have hdiff : L * ∑ j, (qt j - q j) = 2 * Real.pi * ∑ j, ((nt j : ℝ) - n j) := by
    rw [Finset.sum_sub_distrib, mul_sub, sum_log_equation h', sum_log_equation h,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [div_mul_eq_mul_div, eq_div_iff hL.ne', ← hdiff]
  ring

/-- **Proposition `F05:root-comparison` (R-7A6567D6)**, contraction and order of the rapidities.
For two actual repulsive Bethe configurations `q`, `q̃` with the same `N, L, c` and ordered bosonic
labels `n`, `ñ`:
`(1/N) Σ_j |q_j - q̃_j|² ≤ (1/N) Σ_j |p_{n_j} - p_{ñ_j}|²`; if `n_j ≤ ñ_j` for every `j` then
`q_j ≤ q̃_j` for every `j`; and `Σ_j (q̃_j - q_j) = (2π/L) Σ_j (ñ_j - n_j)`.
Only the two given solutions are used (no existence theorem). -/
theorem root_comparison (hL : 0 < L) (h : IsActualConfig L c n q)
    (h' : IsActualConfig L c nt qt) :
    (1 / (N : ℝ)) * ∑ j, |q j - qt j| ^ 2 ≤
        (1 / (N : ℝ)) * ∑ j, |pLab L (n j) - pLab L (nt j)| ^ 2 ∧
      ((∀ j, n j ≤ nt j) → ∀ j, q j ≤ qt j) ∧
      ∑ j, (qt j - q j) = 2 * Real.pi / L * ∑ j, ((nt j : ℝ) - n j) :=
  ⟨finite_contraction hL h h', order_of_labels hL h h', total_response hL h h'⟩

/-- The proposition for the accepted root vectors `BetheSmooth.roots` (R-4C8D7C9E). -/
theorem root_comparison_roots (hL : 0 < L) (hc : 0 < c) (hn : Monotone n) (hnt : Monotone nt) :
    (1 / (N : ℝ)) * ∑ j, |roots L n c j - roots L nt c j| ^ 2 ≤
        (1 / (N : ℝ)) * ∑ j, |pLab L (n j) - pLab L (nt j)| ^ 2 ∧
      ((∀ j, n j ≤ nt j) → ∀ j, roots L n c j ≤ roots L nt c j) ∧
      ∑ j, (roots L nt c j - roots L n c j) = 2 * Real.pi / L * ∑ j, ((nt j : ℝ) - n j) :=
  root_comparison hL (isActual_roots hL hc hn) (isActual_roots hL hc hnt)

end Proposition

end QuantumNLS.RootContraction
