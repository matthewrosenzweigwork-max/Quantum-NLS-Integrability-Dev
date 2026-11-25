import QuantumNLS.Ext006NumberPhase
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Analytic product estimate in the proof of PROP-023. This module proves
bounds for the displayed scalar products. It does not identify them with a
physical quasifree vacuum's number law or assert FIN-CORE-BD-02. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped ENNReal
namespace QuantumNLS.Prop023ProductBounds
variable {ι : Type*}

/-- The one-mode factor printed in Q7B:lem:moments, expressed by real powers. -/
def modeFactor (Q q : ℝ) : ℝ :=
  (1 + q * (1 - Real.exp (1 / (8 * Q)))) ^ (-1 / 2 : ℝ)

lemma exponential_increment {Q : ℝ} (hQ : 1 ≤ Q) :
    0 ≤ Real.exp (1 / (8 * Q)) - 1 ∧
      Real.exp (1 / (8 * Q)) - 1 ≤ 1 / (4 * Q) := by
  have hQ0 : 0 < Q := by linarith
  have ha : 0 ≤ 1 / (8 * Q) := by positivity
  have ha1 : 1 / (8 * Q) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have he := Real.exp_le_two_add_div_two_sub ha (by linarith : 1 / (8 * Q) < 2)
  have hb : Real.exp (1 / (8 * Q)) ≤ 1 + 2 * (1 / (8 * Q)) := by
    apply he.trans
    apply (div_le_iff₀ (by linarith : 0 < 2 - 1 / (8 * Q))).2
    nlinarith
  constructor
  · exact sub_nonneg.mpr (Real.one_le_exp ha)
  · have hi : 2 * (1 / (8 * Q)) = 1 / (4 * Q) := by ring
    linarith

lemma negative_half_log {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 4) :
    0 ≤ -(Real.log (1-x)) / 2 ∧ -(Real.log (1-x)) / 2 ≤ x := by
  have hp : 0 < 1-x := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hi : (1-x)⁻¹ ≤ 1+2*x := by
    rw [← one_div]
    apply (div_le_iff₀ hp).2
    nlinarith
  have hn := Real.log_nonpos (by linarith : 0 ≤ 1-x) (by linarith : 1-x ≤ 1)
  constructor <;> linarith

lemma mode_log_bounds {Q q : ℝ} (hQ : 1 ≤ Q) (hq : 0 ≤ q) (hqQ : q ≤ Q) :
    0 < modeFactor Q q ∧ 0 ≤ Real.log (modeFactor Q q) ∧
      Real.log (modeFactor Q q) ≤ q * (Real.exp (1/(8*Q))-1) := by
  have hQ0 : 0 < Q := by linarith
  let x := q * (Real.exp (1/(8*Q))-1)
  have he := exponential_increment hQ
  have hx : 0 ≤ x := mul_nonneg hq he.1
  have hx' : x ≤ 1/4 := by
    calc
      x ≤ Q * (1 / (4 * Q)) := mul_le_mul hqQ he.2 he.1 (by positivity)
      _ = 1/4 := by field_simp
  have hb : 1 + q * (1 - Real.exp (1/(8*Q))) = 1-x := by dsimp [x]; ring
  have hp : 0 < 1-x := by linarith
  have hm : modeFactor Q q = Real.exp (-(Real.log (1-x))/2) := by
    rw [modeFactor, hb, Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [hm, Real.log_exp]
  exact ⟨Real.exp_pos _, (negative_half_log hx hx').1, (negative_half_log hx hx').2⟩

/-- All finite products have the report's dimension-independent bound. -/
theorem finite_product_bound (s : Finset ι) (Q : ℝ) (hQ : 1 ≤ Q)
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hbudget : ∑ i ∈ s, q i ≤ Q-1) :
    ∏ i ∈ s, modeFactor Q (q i) ≤ Real.exp (1/4 : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have hterm : ∀ i ∈ s, q i ≤ Q := by
    intro i hi
    have hs := Finset.single_le_sum (fun a _ => hq a) hi
    linarith
  have he := exponential_increment hQ
  calc
    ∏ i ∈ s, modeFactor Q (q i) =
        Real.exp (∑ i ∈ s, Real.log (modeFactor Q (q i))) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i hi
      exact (Real.exp_log (mode_log_bounds hQ (hq i) (hterm i hi)).1).symm
    _ ≤ Real.exp ((∑ i ∈ s, q i) * (Real.exp (1/(8*Q))-1)) := by
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => (mode_log_bounds hQ (hq i) (hterm i hi)).2.2
    _ ≤ Real.exp (1/4 : ℝ) := by
      apply Real.exp_le_exp.mpr
      calc
        (∑ i ∈ s, q i) * (Real.exp (1/(8*Q))-1) ≤
            Q * (1/(4*Q)) := mul_le_mul (by linarith) he.2 he.1 (by positivity)
        _ = 1/4 := by field_simp

/-- The full scalar product actually converges, and obeys the same bound.
The input is a summable sequence of nonnegative means, not a number-law
hypothesis or an assumed quasifree representation. -/
theorem infinite_product_bound (Q : ℝ) (hQ : 1 ≤ Q) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hs : Summable q) (hbudget : ∑' i, q i ≤ Q-1) :
    Multipliable (fun i => modeFactor Q (q i)) ∧
      ∏' i, modeFactor Q (q i) ≤ Real.exp (1/4 : ℝ) := by
  have hterm : ∀ i, q i ≤ Q := by
    intro i
    have hi := hs.le_tsum i (fun j _ => hq j)
    linarith
  have hlog : Summable (fun i => Real.log (modeFactor Q (q i))) := by
    apply Summable.of_nonneg_of_le (fun i => (mode_log_bounds hQ (hq i) (hterm i)).2.1)
      (fun i => (mode_log_bounds hQ (hq i) (hterm i)).2.2)
    exact hs.mul_right _
  have hp := Real.multipliable_of_summable_log
    (fun i => (mode_log_bounds hQ (hq i) (hterm i)).1) hlog
  refine ⟨hp, hp.tprod_le_of_prod_le fun s => ?_⟩
  apply finite_product_bound s Q hQ q hq
  exact (hs.sum_le_tsum s (fun i _ => hq i)).trans hbudget

/-- The ENNReal supremum used when passing from finite-mode expectations
has the same constant, without any finiteness assumption on the index set. -/
theorem supremum_product_bound (Q : ℝ) (hQ : 1 ≤ Q) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hs : Summable q) (hbudget : ∑' i, q i ≤ Q-1) :
    (⨆ s : Finset ι, ENNReal.ofReal (∏ i ∈ s, modeFactor Q (q i))) ≤
      ENNReal.ofReal (Real.exp (1/4 : ℝ)) := by
  apply iSup_le
  intro s
  exact ENNReal.ofReal_le_ofReal
    (finite_product_bound s Q hQ q hq ((hs.sum_le_tsum s (fun i _ => hq i)).trans hbudget))

end QuantumNLS.Prop023ProductBounds

#print axioms QuantumNLS.Prop023ProductBounds.exponential_increment
#print axioms QuantumNLS.Prop023ProductBounds.negative_half_log
#print axioms QuantumNLS.Prop023ProductBounds.mode_log_bounds
#print axioms QuantumNLS.Prop023ProductBounds.finite_product_bound
#print axioms QuantumNLS.Prop023ProductBounds.infinite_product_bound
#print axioms QuantumNLS.Prop023ProductBounds.supremum_product_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop023ProductBounds." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
