import QuantumNLS.F02Round6

/-! Source F07: general real-label contraction and the pointwise coupling estimate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Finset
namespace QuantumNLS.F07Round6
open BetheAdmission BetheRoots BetheSmooth Ext025A6 RootContraction F02Round6

/-- Force written in terms of ordered free momenta, with the rank correction. -/
def freeForce {N : ℕ} (L : ℝ) (p : Fin N → ℝ) : Fin N → ℝ :=
  fun i => L * p i + Real.pi * (2 * (i : ℝ) + 1 - N)

/-- The exact finite label contraction holds for arbitrary real free labels. -/
theorem label_contraction_sq {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (p p' : Fin N → ℝ) :
    ∑ i, (root L (freeForce L p') c i - root L (freeForce L p) c i)^2 ≤
      ∑ i, (p' i - p i)^2 := by
  let q := root L (freeForce L p) c
  let q' := root L (freeForce L p') c
  let d : Fin N → ℝ := fun i => q' i - q i
  have hr : Bavg L c q d *ᵥ d = fun i => L * (p' i - p i) := by
    funext i
    rw [Bavg_response hc]
    have he : (fun i => q i + d i) = q' := by
      funext i
      dsimp [d]
      ring
    rw [he, Tmap_eq_logMap, root_solves hL hc, root_solves hL hc]
    dsimp [freeForce]
    ring
  have hquad := Bavg_quad (L := L) hc q d d
  rw [hr] at hquad
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ d (fun i => L * (p' i - p i))
  have hB : (∑ i, (L * (p' i - p i))^2) = L^2 * ∑ i, (p' i - p i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hB] at hcs
  have hA0 : 0 ≤ ∑ i, d i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hP0 : 0 ≤ ∑ i, (p' i - p i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  change (∑ i, d i ^ 2) ≤ ∑ i, (p' i - p i)^2
  generalize ∑ i, d i ^ 2 = A at hquad hcs hA0 ⊢
  generalize ∑ i, (p' i - p i)^2 = P at hcs hP0 ⊢
  generalize ∑ i, d i * (L * (p' i - p i)) = S at hquad hcs
  rcases hA0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hP0
  · have h1 : (L * A)^2 ≤ S^2 := pow_le_pow_left₀ (mul_nonneg hL.le hA0) hquad 2
    have h2 : L^2 * A * A ≤ L^2 * P * A := by nlinarith
    have h3 := le_of_mul_le_mul_right h2 hpos
    nlinarith [sq_pos_of_pos hL]

/-- Pointwise F07 bound at contact K/N, before integrating the root path. -/
theorem coupling_response_bound {N : ℕ} (hN : 0 < N) {L K : ℝ}
    (hL : 0 < L) (hK : 0 < K) (b : Fin N → ℝ) :
    ∑ i, ((K / N) * deriv (root L b) (K / N) i)^2 ≤
      K * N / (4 * L) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < K / N := div_pos hK hNr
  have h := quadratic_bound hL hc (root L b (K / N))
    ((K / N) • deriv (root L b) (K / N))
    (root_scaled_derivative_equation hL hc b)
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have hbound : (K / N) * (N : ℝ) * ((N : ℝ) - 1) / (4 * L) ≤
      K * N / (4 * L) := by
    have hn : (N : ℝ) ≠ 0 := ne_of_gt hNr
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 4 * L)).2
    field_simp
    nlinarith
  exact le_trans h hbound

end QuantumNLS.F07Round6
#print axioms QuantumNLS.F07Round6.label_contraction_sq
#print axioms QuantumNLS.F07Round6.coupling_response_bound
