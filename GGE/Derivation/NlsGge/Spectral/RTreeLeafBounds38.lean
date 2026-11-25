import NlsGge.Spectral.R3cPlaneSobolev38
import NlsGge.Spectral.R3cResolventCore38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # Resolvent trees, piece T4: plane leaf bounds for general `k`

Generalization of `R3cPlaneSobolev38` (which treats `∂⁰` and `∂¹` in sup norm) to leaf orders `d`
up to `k`. The leaf function `leafU38 N z d` of the design is `planeReal N ((derivativePlane N)^[d] z)`;
it is NOT defined here (it belongs to `RTreeCore38`), so every statement is written out on
`planeReal N ((derivativePlane N)^[d] z)`, which is its definition. The complex conjugate leaf
`fun x => star (...)` has the same norm (`norm_star`), see `l2sq38_star_leaf` below.

With `S_j(z) = ∑ i, (1 + (modeIndex N i)^2)^j * ‖z i‖^2`:
* sup bound for `d + 1 ≤ k`: `‖∂^d U‖_∞ ≤ (2π)^d √K √S_{d+1}(z)`, `K = bracketSumE02_38`;
* `L²` bound for any `d`: `‖∂^d U‖₂ ≤ (2π)^d √S_d(z)`.

`leafOrderBound38 k N z d` is the explicit per-leaf bound (`L²` at order exactly `k`, sup at orders `< k`);
`leafBound_le` gives the uniform bound of a product of leaf bounds under `S_k ≤ B²`. -/

/-- coordinates of the `d`-fold derivative plane: squared norms -/
theorem iterate_derivativePlane_norm_sq38 (N : ℕ) (z : FourierPlane N) (d : ℕ)
    (i : Fin (2 * N + 1)) :
    ‖((derivativePlane N)^[d] z) i‖ ^ 2 =
      ‖z i‖ ^ 2 * ((2 * Real.pi) ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ d := by
  rw [iterate_derivativePlane_apply_r3c, norm_mul, norm_pow, mul_pow, ← pow_mul,
    mul_comm d 2, pow_mul]
  congr 2
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_intCast]
  rw [mul_pow, mul_pow, sq_abs]

/-- Sobolev sums of the `d`-fold derivative plane: `S_j(∂^d z) ≤ (2π)^{2d} S_{j+d}(z)`. -/
theorem iterate_derivativePlane_S_le38 (N : ℕ) (z : FourierPlane N) (j d : ℕ) :
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j *
        ‖((derivativePlane N)^[d] z) i‖ ^ 2 ≤
      (2 * Real.pi) ^ (2 * d) *
        ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ (j + d) * ‖z i‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [iterate_derivativePlane_norm_sq38]
  have hm : ((modeIndex N i : ℤ) : ℝ) ^ 2 ≤ 1 + ((modeIndex N i : ℤ) : ℝ) ^ 2 := by
    have := sq_nonneg ((modeIndex N i : ℤ) : ℝ); linarith
  have h2 : ((2 * Real.pi) ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ d ≤
      (2 * Real.pi) ^ (2 * d) * (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ d := by
    rw [mul_pow, ← pow_mul]
    gcongr
  calc (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j *
        (‖z i‖ ^ 2 * ((2 * Real.pi) ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ d)
      ≤ (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j *
        (‖z i‖ ^ 2 * ((2 * Real.pi) ^ (2 * d) * (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ d)) := by
        gcongr
    _ = (2 * Real.pi) ^ (2 * d) * ((1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ (j + d) * ‖z i‖ ^ 2) := by
        rw [pow_add]; ring

/-- Sup bound of the `d`-th plane derivative by `S_{d+1}`. -/
theorem plane_iter_sup_le38 (N : ℕ) (z : FourierPlane N) (d : ℕ) (x : ℝ) :
    ‖planeReal N ((derivativePlane N)^[d] z) x‖ ≤
      (2 * Real.pi) ^ d * Real.sqrt bracketSumE02_38 *
        Real.sqrt (∑ i : Fin (2 * N + 1),
          (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ (d + 1) * ‖z i‖ ^ 2) := by
  refine (plane_sup_le_r3c N ((derivativePlane N)^[d] z) x).trans ?_
  have h := Real.sqrt_le_sqrt (iterate_derivativePlane_S_le38 N z 1 d)
  have e2 : (2 * Real.pi) ^ (2 * d) = ((2 * Real.pi) ^ d) ^ 2 := pow_mul' _ 2 d
  rw [e2] at h
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at h
  have hK : 0 ≤ Real.sqrt bracketSumE02_38 := Real.sqrt_nonneg _
  calc Real.sqrt bracketSumE02_38 * _ ≤ Real.sqrt bracketSumE02_38 * _ :=
        mul_le_mul_of_nonneg_left h hK
    _ = _ := by ring_nf

/-- `L²` bound of the `d`-th plane derivative, squared form (restatement of `plane_l2_le_r3c`). -/
theorem plane_iter_l2sq_le38 (N : ℕ) (z : FourierPlane N) (d : ℕ) :
    l2sq38 (planeReal N ((derivativePlane N)^[d] z)) ≤
      (2 * Real.pi) ^ (2 * d) *
        ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ d * ‖z i‖ ^ 2 :=
  plane_l2_le_r3c N z d

/-- `L²` bound of the `d`-th plane derivative. -/
theorem plane_iter_l2_le38 (N : ℕ) (z : FourierPlane N) (d : ℕ) :
    Real.sqrt (l2sq38 (planeReal N ((derivativePlane N)^[d] z))) ≤
      (2 * Real.pi) ^ d *
        Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ d * ‖z i‖ ^ 2) := by
  have h := Real.sqrt_le_sqrt (plane_iter_l2sq_le38 N z d)
  rw [Real.sqrt_mul (by positivity)] at h
  have e : Real.sqrt ((2 * Real.pi) ^ (2 * d)) = (2 * Real.pi) ^ d := by
    rw [pow_mul', Real.sqrt_sq (by positivity)]
  rwa [e] at h

/-- conjugate leaves have the same `L²` norm -/
theorem l2sq38_star_leaf (f : ℝ → ℂ) : l2sq38 (fun x => star (f x)) = l2sq38 f := by
  simp [l2sq38]

/-- Per-leaf norm bound: `L²` bound `(2π)^k √S_k` at order exactly `k`, sup bound
`(2π)^d √K √S_{d+1}` at orders `d ≠ k` (used for `d < k`). -/
def leafOrderBound38 (k : ℕ) (N : ℕ) (z : FourierPlane N) (d : ℕ) : ℝ :=
  if d = k then
    (2 * Real.pi) ^ k * Real.sqrt (∑ i : Fin (2 * N + 1),
      (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2)
  else
    (2 * Real.pi) ^ d * Real.sqrt bracketSumE02_38 * Real.sqrt (∑ i : Fin (2 * N + 1),
      (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ (d + 1) * ‖z i‖ ^ 2)

theorem leafOrderBound38_nonneg (k N : ℕ) (z : FourierPlane N) (d : ℕ) :
    0 ≤ leafOrderBound38 k N z d := by
  unfold leafOrderBound38
  split_ifs <;> positivity

/-- sup bound of a leaf of order `d < k` -/
theorem leaf_sup_le38 (k N : ℕ) (z : FourierPlane N) {d : ℕ} (hd : d < k) (x : ℝ) :
    ‖planeReal N ((derivativePlane N)^[d] z) x‖ ≤ leafOrderBound38 k N z d := by
  simp only [leafOrderBound38, hd.ne, ite_false]
  exact plane_iter_sup_le38 N z d x

/-- sup bound of a conjugate leaf of order `d < k` -/
theorem leaf_star_sup_le38 (k N : ℕ) (z : FourierPlane N) {d : ℕ} (hd : d < k) (x : ℝ) :
    ‖star (planeReal N ((derivativePlane N)^[d] z) x)‖ ≤ leafOrderBound38 k N z d := by
  rw [norm_star]; exact leaf_sup_le38 k N z hd x

/-- `L²` bound of a leaf of order exactly `k` -/
theorem leaf_l2_le38 (k N : ℕ) (z : FourierPlane N) :
    Real.sqrt (l2sq38 (planeReal N ((derivativePlane N)^[k] z))) ≤ leafOrderBound38 k N z k := by
  simp only [leafOrderBound38, ite_true]
  exact plane_iter_l2_le38 N z k

/-- `L²` bound of a conjugate leaf of order exactly `k` -/
theorem leaf_star_l2_le38 (k N : ℕ) (z : FourierPlane N) :
    Real.sqrt (l2sq38 (fun x => star (planeReal N ((derivativePlane N)^[k] z) x))) ≤
      leafOrderBound38 k N z k := by
  rw [l2sq38_star_leaf]; exact leaf_l2_le38 k N z

/-- Uniform bound of a product of leaf bounds (one factor per leaf order in the list `l`; the leaf
orders of a tree `T` with `T.maxd ≤ k` form such a list of length `T.nodes`, one leaf per node).
Under `S_k(z) ≤ B²` every factor is at most `C(k,B)`, independent of `N` and `z`. -/
theorem leafBound_le (k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 ≤ B ^ 2 →
      ∀ l : List ℕ, (∀ d ∈ l, d ≤ k) →
        (l.map (leafOrderBound38 k N z)).prod ≤ C ^ l.length := by
  have hK0 : 0 ≤ bracketSumE02_38 :=
    tsum_nonneg fun n => Real.rpow_nonneg (japaneseBracket_pos n).le _
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨(2 * Real.pi) ^ k * (1 + Real.sqrt bracketSumE02_38) * |B|, by positivity, ?_⟩
  intro N z hS l hl
  -- each factor is at most C
  have hsq : ∀ j, 1 ≤ j → j ≤ k →
      Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j * ‖z i‖ ^ 2) ≤
        |B| := by
    intro j _ hjk
    have h1 := (plane_S_mono_r3c N z hjk).trans hS
    calc _ ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt h1
      _ = |B| := Real.sqrt_sq_eq_abs B
  have hfac : ∀ d ∈ l, leafOrderBound38 k N z d ≤
      (2 * Real.pi) ^ k * (1 + Real.sqrt bracketSumE02_38) * |B| := by
    intro d hd
    have hdk := hl d hd
    have hpd : (2 * Real.pi) ^ d ≤ (2 * Real.pi) ^ k := pow_le_pow_right₀ hpi hdk
    have hsK : 0 ≤ Real.sqrt bracketSumE02_38 := Real.sqrt_nonneg _
    unfold leafOrderBound38
    split_ifs with h
    · subst h
      have := hsq d (by omega) le_rfl
      have hp0 : 0 ≤ (2 * Real.pi) ^ d := by positivity
      have hB0 := abs_nonneg B
      have h3 : (2 * Real.pi) ^ d * Real.sqrt (∑ i : Fin (2 * N + 1),
          (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ d * ‖z i‖ ^ 2) ≤ (2 * Real.pi) ^ d * |B| :=
        mul_le_mul_of_nonneg_left this hp0
      have h4 : (2 * Real.pi) ^ d * |B| ≤
          (2 * Real.pi) ^ d * (1 + Real.sqrt bracketSumE02_38) * |B| := by
        have : 0 ≤ (2 * Real.pi) ^ d * Real.sqrt bracketSumE02_38 * |B| := by positivity
        nlinarith
      exact h3.trans h4
    · have hd' : d + 1 ≤ k := by omega
      have := hsq (d + 1) (by omega) hd'
      have hB0 := abs_nonneg B
      have h3 : (2 * Real.pi) ^ d * Real.sqrt bracketSumE02_38 * Real.sqrt (∑ i : Fin (2 * N + 1),
          (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ (d + 1) * ‖z i‖ ^ 2) ≤
          (2 * Real.pi) ^ k * Real.sqrt bracketSumE02_38 * |B| := by
        gcongr
      have h4 : (2 * Real.pi) ^ k * Real.sqrt bracketSumE02_38 * |B| ≤
          (2 * Real.pi) ^ k * (1 + Real.sqrt bracketSumE02_38) * |B| := by
        have : 0 ≤ (2 * Real.pi) ^ k * |B| := by positivity
        nlinarith
      exact h3.trans h4
  clear hS hsq
  induction l with
  | nil => simp
  | cons d l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    have h1 := hfac d (List.mem_cons_self)
    have h2 := ih (fun e he => hl e (List.mem_cons_of_mem _ he))
      (fun e he => hfac e (List.mem_cons_of_mem _ he))
    have h0 := leafOrderBound38_nonneg k N z d
    calc leafOrderBound38 k N z d * (l.map (leafOrderBound38 k N z)).prod
        ≤ _ * _ := by
          apply mul_le_mul h1 h2 (List.prod_nonneg ?_) (by positivity)
          intro a ha
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha
          exact leafOrderBound38_nonneg k N z e
      _ = _ := by ring

end NlsGge.SpectralFoundations
