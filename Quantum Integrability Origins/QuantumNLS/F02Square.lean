import QuantumNLS.Ext025A6BetheAnalytic
import QuantumNLS.RootContraction

/-! Finite pair algebra for the source F02 coupling derivative. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace QuantumNLS.F02Square
open BetheAdmission BetheRoots BetheSmooth Ext025A6 RootContraction

/-- The symmetric pair polarization of the Gaudin interaction. -/
theorem pair_cross {N : ℕ} (c : ℝ) (q z : Fin N → ℝ) :
    (∑ i, z i * ∑ j, edgeWeight c q i j * (q i - q j)) =
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
      edgeWeight c q i j * (z i - z j) * (q i - q j) := by
  have hswap : (∑ i, ∑ j, z j * (edgeWeight c q i j * (q i - q j))) =
      -(∑ i, ∑ j, z i * (edgeWeight c q i j * (q i - q j))) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [edgeWeight_symm c q i j]
    ring
  have hpair := sum_sum_eq_two_mul_lt
    (fun i j => edgeWeight c q i j * (z i - z j) * (q i - q j))
    (fun i j => by rw [edgeWeight_symm c q i j]; ring) (fun i => by simp)
  have hexp : (∑ i, ∑ j, edgeWeight c q i j * (z i - z j) * (q i - q j)) =
      2 * (∑ i, z i * ∑ j, edgeWeight c q i j * (q i - q j)) := by
    simp only [Finset.mul_sum]
    have hp (i j : Fin N) : edgeWeight c q i j * (z i - z j) * (q i - q j) =
      z i * (edgeWeight c q i j * (q i - q j)) -
      z j * (edgeWeight c q i j * (q i - q j)) := by ring
    simp_rw [hp, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum]
    simp only [← Finset.mul_sum] at hswap
    linarith
  linarith

/-- Square completion for the actual Gaudin equation, valid for any vectors. -/
theorem square_identity {N : ℕ} {L c : ℝ} (hc : 0 < c)
    (q z : Fin N → ℝ)
    (hz : gaudin L c q z = gaudin L c q q - L • q) :
    L * ∑ i, z i ^ 2 +
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
        edgeWeight c q i j * (z i - z j - (q i - q j) / 2)^2 =
    (1 / 4 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
      edgeWeight c q i j * (q i - q j)^2 := by
  have hq := (jacobian_quadratic L hc q z).1
  have hcross := pair_cross c q z
  have hcoord : ∀ i, gaudin L c q z i =
      ∑ j, edgeWeight c q i j * (q i - q j) := by
    intro i
    have h := congrFun hz i
    simpa only [gaudin_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      add_sub_cancel_left] using h
  simp_rw [hcoord] at hq
  rw [hcross] at hq
  have hexp (i j : Fin N) :
      edgeWeight c q i j * (z i - z j - (q i - q j) / 2)^2 =
      edgeWeight c q i j * (z i - z j)^2 -
      edgeWeight c q i j * (z i - z j) * (q i - q j) +
      (1 / 4 : ℝ) * (edgeWeight c q i j * (q i - q j)^2) := by ring
  simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [edgeWeight] at hq ⊢
  linarith

#print axioms QuantumNLS.F02Square.pair_cross
#print axioms QuantumNLS.F02Square.square_identity
