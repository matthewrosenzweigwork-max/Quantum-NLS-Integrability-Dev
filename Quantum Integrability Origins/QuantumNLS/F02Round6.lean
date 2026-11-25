import QuantumNLS.F02Square

/-! F02 finite pair estimate and its cardinality. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace QuantumNLS.F02Round6
open BetheRoots RootContraction F02Square

/-- The unordered pairs have cardinality N(N-1)/2, with real casts. -/
theorem pair_count (N : ℕ) :
    (2 : ℝ) * (∑ i : Fin N, ∑ j ∈ univ.filter (fun j => i < j), (1 : ℝ)) =
    (N : ℝ) * ((N : ℝ) - 1) := by
  have h := sum_sum_eq_two_mul_lt (N := N) (fun i j => if i = j then (0 : ℝ) else 1)
    (fun i j => by by_cases hij : i = j <;> simp [hij, eq_comm]) (fun i => by simp)
  have hd : (∑ i : Fin N, ∑ j : Fin N, (if i = j then (0 : ℝ) else 1)) =
      (N : ℝ) * ((N : ℝ) - 1) := by
    have hrow (i : Fin N) : (∑ j : Fin N, (if i = j then (0 : ℝ) else 1)) = (N : ℝ) - 1 := by
      calc
        _ = ∑ j : Fin N, (1 - if i = j then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> norm_num
        _ = (N : ℝ) - 1 := by simp [Finset.sum_sub_distrib]
    simp_rw [hrow]
    simp
    ring
  rw [hd] at h
  have hp : (∑ i : Fin N, ∑ j ∈ univ.filter (fun j => i < j),
      (if i = j then (0 : ℝ) else 1)) =
      ∑ i : Fin N, ∑ j ∈ univ.filter (fun j => i < j), (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    simp [(Finset.mem_filter.mp hj).2.ne]
  rw [hp] at h
  linarith

/-- Each pair contributes at most 2c to the right hand side of the square identity. -/
theorem edge_square_le {c x : ℝ} (hc : 0 < c) :
    2 * c / (c^2 + x^2) * x^2 ≤ 2 * c := by
  have hd : 0 < c^2 + x^2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg hc.le (sq_nonneg c)]

/-- The literal F02 quadratic estimate follows from the source square identity. -/
theorem quadratic_bound {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (q z : Fin N → ℝ)
    (hz : gaudin L c q z = gaudin L c q q - L • q) :
    ∑ i, z i ^ 2 ≤ c * (N : ℝ) * ((N : ℝ) - 1) / (4 * L) := by
  have hs := square_identity hc q z hz
  have hn : 0 ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
      edgeWeight c q i j * (z i - z j - (q i - q j) / 2)^2 := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (edgeWeight_pos hc q i j).le (sq_nonneg _)
  have hp : (∑ i, ∑ j ∈ univ.filter (fun j => i < j),
      edgeWeight c q i j * (q i - q j)^2) ≤
      ∑ i : Fin N, ∑ j ∈ univ.filter (fun j => i < j), 2 * c := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact edge_square_le hc
  have hcard := pair_count N
  have hconst : (∑ i : Fin N, ∑ j ∈ univ.filter (fun j => i < j), 2 * c) =
      (2 * c) * (∑ i : Fin N, ∑ j ∈ univ.filter (fun j => i < j), (1 : ℝ)) := by
    simp only [Finset.mul_sum, mul_one]
  rw [hconst] at hp
  apply (le_div_iff₀ (by positivity : 0 < 4 * L)).2
  nlinarith [congrArg (fun t : ℝ => c * t) hcard]
end QuantumNLS.F02Round6



/-! R-864F39DE, source F02 coupling derivative. Index i is zero based. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace QuantumNLS.F02Round6Derivative
open BetheAdmission BetheRoots BetheSmooth Ext025A6 F02Square F02Round6

/-- F02: the actual ordered real-label roots, their joint analytic dependence,
Gaudin derivative and inverse identities, square identity and quadratic bound. -/
theorem coupling_derivative {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {ν : Fin N → ℝ} (hν : Monotone ν) :
    let q := root L (realLabelForce ν) c
    let z := c • deriv (root L (realLabelForce ν)) c
    StrictMono q ∧
    (∀ i, L * q i + 2 * ∑ j ∈ univ.erase i,
      Real.arctan ((q i - q j) / c) =
        2 * Real.pi * ν i + Real.pi * (2 * (i : ℝ) + 1 - N)) ∧
    (∀ p : Fin N → ℝ, (∀ i, L * p i + 2 * ∑ j ∈ univ.erase i,
      Real.arctan ((p i - p j) / c) =
        2 * Real.pi * ν i + Real.pi * (2 * (i : ℝ) + 1 - N)) → p = q) ∧
    AnalyticAt ℝ (fun p : ℝ × (Fin N → ℝ) =>
      root L (realLabelForce p.2) p.1) (c, ν) ∧
    (∀ d : ℝ, 0 < d → ∀ μ : Fin N → ℝ, StrictMono (realLabelForce μ) →
      StrictMono (root L (realLabelForce μ) d)) ∧
    gaudin L c q z = gaudin L c q q - L • q ∧
    (gaudin L c q).inverse q = L⁻¹ • (q - z) ∧
    L * ∑ i, z i ^ 2 +
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
        edgeWeight c q i j * (z i - z j - (q i - q j) / 2)^2 =
      (1 / 4 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
        edgeWeight c q i j * (q i - q j)^2 ∧
    ∑ i, z i ^ 2 ≤ c * (N : ℝ) * ((N : ℝ) - 1) / (4 * L) := by
  dsimp only
  have hforce : StrictMono (realLabelForce ν) := by
    intro i j hij
    have hi : (i : ℝ) < j := by exact_mod_cast hij
    have hn := hν hij.le
    have hp := Real.pi_pos
    dsimp [realLabelForce]
    nlinarith
  have horder : StrictMono (root L (realLabelForce ν) c) := by
    intro i j hij
    by_contra hq
    have hm := logMap_coordinate_mono hL.le hc (root L (realLabelForce ν) c)
      (le_of_not_gt hq)
    rw [root_solves hL hc] at hm
    exact (not_le_of_gt (hforce hij)) hm
  have hz := root_scaled_derivative_equation hL hc (realLabelForce ν)
  refine ⟨horder, f02_roots_solve hL hc ν, ?_,
    f02_roots_joint_analyticAt hL hc ν, ?_, hz, ?_, square_identity hc _ _ hz,
    quadratic_bound hL hc _ _ hz⟩
  · intro p hp
    apply eq_root hL hc
    ext i
    simpa only [logMap_erase, realLabelForce] using hp i
  · intro d hd μ hm i j hij
    by_contra hq
    have h := logMap_coordinate_mono hL.le hd (root L (realLabelForce μ) d)
      (le_of_not_gt hq)
    rw [root_solves hL hd] at h
    exact (not_le_of_gt (hm hij)) h
  · have hz' := root_scaled_deriv_eq hL hc (realLabelForce ν)
    rw [hz', sub_sub_cancel, smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
end QuantumNLS.F02Round6Derivative

#print axioms QuantumNLS.F02Round6.pair_count
#print axioms QuantumNLS.F02Round6.edge_square_le
#print axioms QuantumNLS.F02Round6.quadratic_bound
#print axioms QuantumNLS.F02Round6Derivative.coupling_derivative
