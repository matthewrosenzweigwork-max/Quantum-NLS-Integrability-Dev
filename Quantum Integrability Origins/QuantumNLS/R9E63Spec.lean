import QuantumNLS.F02FiniteGap
/-! integrator-authored trusted spec for R-9E63B373 CC:F02:finite-gap (review record r16 FULL ACCEPT): headline statement(s) copied verbatim from F02FiniteGap (QuantumNLS.F02FiniteGap). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators Matrix ContDiff
open Finset
namespace QuantumNLS.R9E63Spec
open QuantumNLS.F02FiniteGap
open QuantumNLS.BetheLabels QuantumNLS.BetheSmooth QuantumNLS.AdjacentResponse
open QuantumNLS.BetheRoots QuantumNLS.GaudinResponse QuantumNLS.RootDisplacement
open QuantumNLS.OrderedResponse QuantumNLS.RootContraction
open QuantumNLS.Ext025A6 (realLabelForce f02_roots_joint_analyticAt f02_roots_solve)
open QuantumNLS.RootDisplacementEstimate (pair_identity count_erase)
variable {N : ℕ}
variable {L c : ℝ}

set_option maxHeartbeats 8000000 in
theorem finite_gap_spec (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ}
    (hab : b < a) :
    (∑ i, arrRoots L c (transfer η hb a) i ^ 2 - ∑ i, arrRoots L c η i ^ 2 =
      4 * Real.pi * ∑ k ∈ Finset.Ico b a,
        ∫ s in (0 : ℝ)..1, atRank η k (responseVec L c (qPath L c η hb a s))) ∧
    (∑ i, arrRoots L c (transfer η hb a) i ^ 2 - ∑ i, arrRoots L c η i ^ 2 =
      (4 * Real.pi / L) * ∑ k ∈ Finset.Ico b a, ∫ s in (0 : ℝ)..1,
        atRank η k (fun i => qPath L c η hb a s i -
          c * deriv (root L (realLabelForce (nuPath η hb a s))) c i)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ k ∈ Finset.Ico b a, ∀ i : Fin N, (i.val : ℤ) + 1 = Ccum η k →
      (2 * Real.pi * b / L - 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) -
          Real.sqrt (c * N * ((N : ℝ) - 1) / (4 * L * (η.1 b : ℝ)))) / L ≤
        responseVec L c (qPath L c η hb a s) i ∧
      responseVec L c (qPath L c η hb a s) i ≤
        (2 * Real.pi * a / L + 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) +
          Real.sqrt (c * N * ((N : ℝ) - 1) / (4 * L * ((η.1 a : ℝ) + 1)))) / L) := by
  exact QuantumNLS.F02FiniteGap.finite_gap hL hc η hb hab

end QuantumNLS.R9E63Spec
#print axioms QuantumNLS.R9E63Spec.finite_gap_spec
