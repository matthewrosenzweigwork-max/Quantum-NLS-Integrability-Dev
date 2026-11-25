import QuantumNLS.F07ContinuityR6

/-! The F07 step-function integral is the normalized finite scalar product. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Set MeasureTheory
namespace QuantumNLS.F07StepsR6

def cell {N : ℕ} (i : Fin N) : Set ℝ :=
  Ioc ((i : ℝ) / N) (((i : ℝ) + 1) / N)

def step {N : ℕ} (v : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (cell i).indicator (fun _ => v i) x

theorem cell_subset {N : ℕ} (hN : 0 < N) (i : Fin N) : cell i ⊆ Ioc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hi : (0 : ℝ) ≤ i := by positivity
  have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  intro x hx
  dsimp [cell] at hx
  constructor
  · exact lt_of_le_of_lt (div_nonneg hi hNr.le) hx.1
  · have h := div_le_div_of_nonneg_right hiN hNr.le
    simpa [ne_of_gt hNr] using hx.2.trans h

theorem cells_disjoint {N : ℕ} (hN : 0 < N) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (cell i) (cell j) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rw [Set.disjoint_left]
  intro x hi hj
  dsimp [cell] at hi hj
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hk : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    have := div_le_div_of_nonneg_right hk hNr.le
    linarith [hi.2, hj.1]
  · have hk : (j : ℝ) + 1 ≤ i := by exact_mod_cast hgt
    have := div_le_div_of_nonneg_right hk hNr.le
    linarith [hj.2, hi.1]

theorem step_mul {N : ℕ} (hN : 0 < N) (v w : Fin N → ℝ) (x : ℝ) :
    step v x * step w x = ∑ i, (cell i).indicator (fun _ => v i * w i) x := by
  simp only [step, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x ∈ cell i
  · rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : x ∉ cell j := by
        intro hx
        exact (Set.disjoint_left.mp (cells_disjoint hN hji.symm)) hi hx
      simp [hj]
    · simp
  · simp [hi]

theorem step_product_integral {N : ℕ} (hN : 0 < N) (v w : Fin N → ℝ) :
    (∫ x in Ioc (0 : ℝ) 1, step v x * step w x) =
      (N : ℝ)⁻¹ * ∑ i, v i * w i := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsupport : (Ioc (0 : ℝ) 1).indicator (fun x => step v x * step w x) =
      fun x => step v x * step w x := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · simp [hx]
    · have hc (i : Fin N) : x ∉ cell i := fun hi => hx (cell_subset hN i hi)
      simp [hx, step, hc]
  rw [← integral_indicator measurableSet_Ioc, hsupport]
  simp_rw [step_mul hN]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [cell]
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le]
    · simp only [intervalIntegral.integral_const, smul_eq_mul]
      have hn : (N : ℝ) ≠ 0 := ne_of_gt hNr
      field_simp
      ring
    · exact div_le_div_of_nonneg_right (by linarith) hNr.le
  · intro i _
    exact (integrableOn_const (C := v i * w i) (by simp [cell] : volume (cell i) ≠ ⊤)).integrable_indicator measurableSet_Ioc


/-- F07 finite response in the printed step-function form. -/
theorem finite_coupling_response {N : ℕ} (hN : 0 < N) {L K : ℝ}
    (hL : 0 < L) (hK : 0 < K) (b : Fin N → ℝ) :
    let q := BetheSmooth.root L b (K/N)
    let B := BetheRoots.gaudin L (K/N) q
    K * deriv (F07EnergyR6.intensiveEnergy L b) K =
      2 * F07EnergyR6.intensiveEnergy L b K -
        2 * L * (∫ x in Ioc (0 : ℝ) 1, step q x * step (B.inverse q) x) ∧
    0 ≤ K * deriv (F07EnergyR6.intensiveEnergy L b) K ∧
    K * deriv (F07EnergyR6.intensiveEnergy L b) K ≤ 2 * F07EnergyR6.intensiveEnergy L b K := by
  dsimp only
  rw [step_product_integral hN]
  exact F07EnergyR6.intensive_response hN hL hK b

/-- The F07 contraction in the usual Euclidean length. -/
theorem label_contraction {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (p p' : Fin N → ℝ) :
    Real.sqrt (∑ i, (BetheSmooth.root L (F07Round6.freeForce L p') c i -
      BetheSmooth.root L (F07Round6.freeForce L p) c i)^2) ≤
    Real.sqrt (∑ i, (p' i - p i)^2) :=
  Real.sqrt_le_sqrt (F07Round6.label_contraction_sq hL hc p p')

end QuantumNLS.F07StepsR6
#print axioms QuantumNLS.F07StepsR6.cell_subset
#print axioms QuantumNLS.F07StepsR6.cells_disjoint
#print axioms QuantumNLS.F07StepsR6.step_mul
#print axioms QuantumNLS.F07StepsR6.step_product_integral

#print axioms QuantumNLS.F07StepsR6.finite_coupling_response
#print axioms QuantumNLS.F07StepsR6.label_contraction
