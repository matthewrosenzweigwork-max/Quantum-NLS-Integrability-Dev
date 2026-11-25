import QuantumNLS.FiniteCellOmissions

/-! R-D8BB052C: exact printed norm bound and final scalar finite-cell theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical ComplexConjugate
namespace QuantumNLS.FiniteCellFinal
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport FiniteCellPartition
  FiniteCellPaths FiniteCellGauge FiniteCellTransport FiniteCellEstimate FiniteCellInternal
  FiniteCellCoefficientLaw FiniteCellTotalVariation FiniteCellEvents FiniteCellResidues FiniteCellOmissions
variable {N : ℕ}

/-- The exact printed remainder under the square root. -/
def boundaryBound (I : Finset ℤ) (ell : ℕ) (delta eta : ℝ) : ℝ :=
  (16 * (I.card : ℝ) + 9) * (ell : ℝ) ^ 2 * delta ^ 2 + 8 / (ell : ℝ) +
    (4 * (ell : ℝ) + 2) * Real.sqrt (2 * eta)

/-- The exponent r/2 is a REAL power, exactly as printed. -/
def printedBound (I : Finset ℤ) (ell : ℕ) (delta eta : ℝ) : ℝ :=
  2 * Real.sqrt (I.card : ℝ) * (ell : ℝ) ^ ((I.card : ℝ) / 2) * eta +
    Real.sqrt (boundaryBound I ell delta eta)

/-- Clause 4, forward bound, solely from actual action and completed-operator residuals. -/
theorem forward_bound (I : Finset ℤ) (ell : ℕ) (hI : 2 ≤ I.card) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : SelectedSeeds I N) (t : ℤ → Phase) (v : ℤ → ℝ) (g : H N) (hg : ‖g‖ = 1)
    (delta eta : ℝ) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (herr : ∀ j ∈ I, ‖E N j j g - (v j : ℂ) • g‖ ≤ delta)
    (hres : (∑ p : Pairs (I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ v j)),
      ‖pairResidual (extendSeeds I c) t (I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ v j)) g p‖ ^ 2) ≤ eta ^ 2)
    (a b : ↥I) (hab : a.1 ≠ b.1) (ha : 4 / (ell : ℝ) ≤ v a.1) (hb : 4 / (ell : ℝ) ≤ v b.1) :
    ‖W (q_N I ell c) a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g‖ ≤ printedBound I ell delta eta := by
  let G := I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ v j)
  let Q := q_N I ell c
  let R := W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g
  let A := ∑' m : Internal (N := N) I G (threshold N ell) ell a.1 b.1,
    ‖R (destination N a.1 b.1 m.1)‖ ^ 2
  let B := boundaryBound I ell delta eta
  have hkeep := kept_energy_le_internal I G (threshold N ell) ell a b hab Q t g
  have homit := omitted_boundary_bound I ell hell hN v delta eta hdelta heta Q (extendSeeds I c) t g hg herr hres a b hab ha hb
  have hpart := residual_energy_partition I G (threshold N ell) ell a b hab Q t g
  have hinternal := internal_energy_norm_bound (extendSeeds I c) t I G (threshold N ell) ell
    (by omega) (by omega) a.1 b.1 a.2 b.2 hab g eta heta hres
  have hfull : ‖R‖ ^ 2 ≤ A + B := by
    change _ ≤ A at hkeep
    change _ ≤ B at homit
    change ‖R‖ ^ 2 = _ at hpart
    linarith
  have hA : 0 ≤ A := tsum_nonneg (fun _ => sq_nonneg _)
  have hB : 0 ≤ B := by dsimp [B,boundaryBound]; positivity
  have hnorm : ‖R‖ ≤ Real.sqrt A + Real.sqrt B := by
    have hAs := Real.sq_sqrt hA
    have hBs := Real.sq_sqrt hB
    have hc : 0 ≤ Real.sqrt A * Real.sqrt B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [norm_nonneg R, Real.sqrt_nonneg A, Real.sqrt_nonneg B]
  change ‖R‖ ≤ _
  exact hnorm.trans (add_le_add hinternal.2 le_rfl)

/-- Clause 4, adjoint bound, from the reversed tested pair and frozen W_adjoint. -/
theorem adjoint_bound (I : Finset ℤ) (ell : ℕ) (hI : 2 ≤ I.card) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : SelectedSeeds I N) (t : ℤ → Phase) (v : ℤ → ℝ) (g : H N) (hg : ‖g‖ = 1)
    (delta eta : ℝ) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (herr : ∀ j ∈ I, ‖E N j j g - (v j : ℂ) • g‖ ≤ delta)
    (hres : (∑ p : Pairs (I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ v j)),
      ‖pairResidual (extendSeeds I c) t (I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ v j)) g p‖ ^ 2) ≤ eta ^ 2)
    (a b : ↥I) (hab : a.1 ≠ b.1) (ha : 4 / (ell : ℝ) ≤ v a.1) (hb : 4 / (ell : ℝ) ≤ v b.1) :
    ‖(W (q_N I ell c) a.1 b.1).adjoint g - conj ((t a.1).1 * conj (t b.1).1) • g‖ ≤ printedBound I ell delta eta := by
  rw [W_adjoint _ _ _ hab, map_mul, starRingEnd_self_apply, mul_comm (conj (t a.1).1)]
  exact forward_bound I ell hI hell hN c t v g hg delta eta hdelta heta herr hres b a hab.symm hb ha

/-- An arbitrary finite target is extended only for notation; its selected values are unchanged. -/
def target (I : Finset ℤ) (w : ↥I → ℂ) (j : ℤ) : ℂ := if h : j ∈ I then w ⟨j,h⟩ else 0

theorem target_selected (I : Finset ℤ) (w : ↥I → ℂ) (j : ↥I) : target I w j.1 = w j := by
  simp only [target, dite_eq_left j.2]

def actions (I : Finset ℤ) (w : ↥I → ℂ) (j : ℤ) : ℝ := ‖target I w j‖ ^ 2

def phases (I : Finset ℤ) (w : ↥I → ℂ) (j : ℤ) : Phase := completePhase (target I w j)

def good (I : Finset ℤ) (ell : ℕ) (w : ↥I → ℂ) : Finset ℤ :=
  I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ actions I w j)

theorem actions_selected (I : Finset ℤ) (w : ↥I → ℂ) (j : ↥I) : actions I w j.1 = ‖w j‖ ^ 2 := by
  rw [actions, target_selected]

theorem phases_selected (I : Finset ℤ) (w : ↥I → ℂ) (j : ↥I) : phases I w j.1 = completePhase (w j) := by
  rw [phases, target_selected]

/-- The actual nested printed residual sum equals the proved ordered-pair energy. -/
theorem actual_residual_sum (I : Finset ℤ) (ell : ℕ) (c : SelectedSeeds I N) (w : ↥I → ℂ) (g : H N) :
    (∑ p : Pairs (good I ell w), ‖pairResidual (extendSeeds I c) (phases I w) (good I ell w) g p‖ ^ 2) =
    ∑ a : ↥(good I ell w), ∑ b : ↥((good I ell w).erase a.1),
      ‖seedTransfer (extendSeeds I c) a.1 b.1 (Finset.mem_erase.mp b.2).1.symm g -
        ((phases I w a.1).1 * conj (phases I w b.1).1) • g‖ ^ 2 := by
  simp only [pairResidual]
  exact sum_pairs _ (fun a b hab => ‖residual (extendSeeds I c) (phases I w) a b hab g‖ ^ 2)

/-- Final testing clause, binding both nonnegative tolerances explicitly and
allowing arbitrary finite target coordinates with no mass normalization. -/
theorem finite_target_bounds (I : Finset ℤ) (ell : ℕ) (hI : 2 ≤ I.card) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : SelectedSeeds I N) (g : H N) (w : ↥I → ℂ) (delta eta : ℝ)
    (hdelta : 0 ≤ delta) (heta : 0 ≤ eta) (hg : ‖g‖ = 1)
    (herr : ∀ j : ↥I, ‖E N j.1 j.1 g - ((‖w j‖ ^ 2 : ℝ) : ℂ) • g‖ ≤ delta)
    (hres : (∑ a : ↥(good I ell w), ∑ b : ↥((good I ell w).erase a.1),
      ‖seedTransfer (extendSeeds I c) a.1 b.1 (Finset.mem_erase.mp b.2).1.symm g -
        ((phases I w a.1).1 * conj (phases I w b.1).1) • g‖ ^ 2) ≤ eta ^ 2)
    (a b : ↥I) (hab : a.1 ≠ b.1) (ha : 4 / (ell : ℝ) ≤ ‖w a‖ ^ 2) (hb : 4 / (ell : ℝ) ≤ ‖w b‖ ^ 2) :
    ‖W (q_N I ell c) a.1 b.1 g - ((completePhase (w a)).1 * conj (completePhase (w b)).1) • g‖ ≤
      printedBound I ell delta eta ∧
    ‖(W (q_N I ell c) a.1 b.1).adjoint g -
      conj ((completePhase (w a)).1 * conj (completePhase (w b)).1) • g‖ ≤ printedBound I ell delta eta := by
  have herr' : ∀ j ∈ I, ‖E N j j g - (actions I w j : ℂ) • g‖ ≤ delta := by
    intro j hj
    have h := herr ⟨j,hj⟩
    rwa [← actions_selected I w ⟨j,hj⟩] at h
  have hres' : (∑ p : Pairs (good I ell w), ‖pairResidual (extendSeeds I c) (phases I w) (good I ell w) g p‖ ^ 2) ≤ eta ^ 2 := by
    rwa [actual_residual_sum]
  have ha' : 4 / (ell : ℝ) ≤ actions I w a.1 := by rwa [actions_selected]
  have hb' : 4 / (ell : ℝ) ≤ actions I w b.1 := by rwa [actions_selected]
  have hf := forward_bound I ell hI hell hN c (phases I w) (actions I w) g hg delta eta hdelta heta herr' hres' a b hab ha' hb'
  have hadj := adjoint_bound I ell hI hell hN c (phases I w) (actions I w) g hg delta eta hdelta heta herr' hres' a b hab ha' hb'
  rw [phases_selected I w a, phases_selected I w b] at hf hadj
  exact ⟨hf,hadj⟩

/-- The literal printed symbol on positive tested endpoints. -/
def symbol (z w : ℂ) : ℂ := z * conj w / (‖z * w‖ : ℂ)

theorem completePhase_symbol (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    (completePhase z).1 * conj (completePhase w).1 = symbol z w := by
  rw [completePhase_nonzero z hz, completePhase_nonzero w hw, map_div₀,
    Complex.conj_ofReal, div_mul_div_comm, symbol, norm_mul, Complex.ofReal_mul]

theorem tested_nonzero (ell : ℕ) (hell : 2 ≤ ell) (z : ℂ) (h : 4 / (ell : ℝ) ≤ ‖z‖ ^ 2) : z ≠ 0 := by
  have he : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have hp : 0 < (4 : ℝ) / ell := by positivity
  intro hz
  simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  linarith

/-- Testing with the literal symbol w_a conjugate(w_b)/|w_a w_b|. -/
theorem finite_target_symbol_bounds (I : Finset ℤ) (ell : ℕ) (hI : 2 ≤ I.card) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : SelectedSeeds I N) (g : H N) (w : ↥I → ℂ) (delta eta : ℝ)
    (hdelta : 0 ≤ delta) (heta : 0 ≤ eta) (hg : ‖g‖ = 1)
    (herr : ∀ j : ↥I, ‖E N j.1 j.1 g - ((‖w j‖ ^ 2 : ℝ) : ℂ) • g‖ ≤ delta)
    (hres : (∑ a : ↥(good I ell w), ∑ b : ↥((good I ell w).erase a.1),
      ‖seedTransfer (extendSeeds I c) a.1 b.1 (Finset.mem_erase.mp b.2).1.symm g -
        ((phases I w a.1).1 * conj (phases I w b.1).1) • g‖ ^ 2) ≤ eta ^ 2)
    (a b : ↥I) (hab : a.1 ≠ b.1) (ha : 4 / (ell : ℝ) ≤ ‖w a‖ ^ 2) (hb : 4 / (ell : ℝ) ≤ ‖w b‖ ^ 2) :
    ‖W (q_N I ell c) a.1 b.1 g - symbol (w a) (w b) • g‖ ≤ printedBound I ell delta eta ∧
    ‖(W (q_N I ell c) a.1 b.1).adjoint g - conj (symbol (w a) (w b)) • g‖ ≤ printedBound I ell delta eta := by
  have h := finite_target_bounds I ell hI hell hN c g w delta eta hdelta heta hg herr hres a b hab ha hb
  rw [completePhase_symbol (w a) (w b) (tested_nonzero ell hell (w a) ha) (tested_nonzero ell hell (w b) hb)] at h
  exact h

-- Retain the required explicit assumption names inside the universal testing clause.
set_option linter.unusedVariables false in
/-- R-D8BB052C, all clauses. The SAME canonical full-array scalar Q is selected
before the vector, arbitrary finite target and both explicit nonnegative tolerances.
The only testing assumptions are the printed actual action and nested completed
operator residual errors and the two tested endpoint lower bounds. -/
theorem scalar_finite_cell_gauge (I : Finset ℤ) (ell : ℕ) (hI : 2 ≤ I.card) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : SelectedSeeds I N) :
    ∃ Q : Arr N → Phase, Q = q_N I ell c ∧
      (∀ m, ‖(Q m).1‖ = 1) ∧
      (∀ m, Q (root I (threshold N ell) ell m).1 = phaseOne) ∧
      (∀ a b, ‖W Q a b‖ ≤ 1) ∧
      (∀ a b, a ≠ b → (W Q a b).adjoint = W Q b a) ∧
      (∀ a b, (W Q a b).adjoint ∘L W Q a b = support a) ∧
      (∀ a b, a ≠ b → W Q a b ∘L (W Q a b).adjoint = support b) ∧
      (∀ m n p, (ratio Q m n).1 * (ratio Q n p).1 = (ratio Q m p).1) ∧
      (∀ m vertices, pathProduct Q m (vertices ++ [m]) = 1) ∧
      (∀ (g : H N) (w : ↥I → ℂ) (delta eta : ℝ)
        (hdelta : 0 ≤ delta) (heta : 0 ≤ eta) (hg : ‖g‖ = 1),
        (∀ j : ↥I, ‖E N j.1 j.1 g - ((‖w j‖ ^ 2 : ℝ) : ℂ) • g‖ ≤ delta) →
        (∑ a : ↥(good I ell w), ∑ b : ↥((good I ell w).erase a.1),
          ‖seedTransfer (extendSeeds I c) a.1 b.1 (Finset.mem_erase.mp b.2).1.symm g -
            ((phases I w a.1).1 * conj (phases I w b.1).1) • g‖ ^ 2) ≤ eta ^ 2 →
        ∀ (a b : ↥I), a.1 ≠ b.1 → 4 / (ell : ℝ) ≤ ‖w a‖ ^ 2 → 4 / (ell : ℝ) ≤ ‖w b‖ ^ 2 →
          ‖W Q a.1 b.1 g - symbol (w a) (w b) • g‖ ≤ printedBound I ell delta eta ∧
          ‖(W Q a.1 b.1).adjoint g - conj (symbol (w a) (w b)) • g‖ ≤ printedBound I ell delta eta) := by
  refine ⟨q_N I ell c, rfl, q_N_unit I ell c,
    q_root (extendSeeds I c) I (threshold N ell) ell,?_,?_,?_,?_,?_,?_,?_⟩
  · exact W_norm_le (q_N I ell c)
  · exact W_adjoint (q_N I ell c)
  · intro a b
    exact W_initial_projection (q_N I ell c) a b
  · intro a b hab
    exact W_final_projection (q_N I ell c) a b hab
  · exact ratio_trans (q_N I ell c)
  · exact closed_path (q_N I ell c)
  · intro g w delta eta hdelta heta hg herr hres a b hab ha hb
    exact finite_target_symbol_bounds I ell hI hell hN c g w delta eta hdelta heta hg herr hres a b hab ha hb

end QuantumNLS.FiniteCellFinal

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellFinal.boundaryBound
#print axioms QuantumNLS.FiniteCellFinal.printedBound
#print axioms QuantumNLS.FiniteCellFinal.forward_bound
#print axioms QuantumNLS.FiniteCellFinal.adjoint_bound
#print axioms QuantumNLS.FiniteCellFinal.target
#print axioms QuantumNLS.FiniteCellFinal.target_selected
#print axioms QuantumNLS.FiniteCellFinal.actions
#print axioms QuantumNLS.FiniteCellFinal.phases
#print axioms QuantumNLS.FiniteCellFinal.good
#print axioms QuantumNLS.FiniteCellFinal.actions_selected
#print axioms QuantumNLS.FiniteCellFinal.phases_selected
#print axioms QuantumNLS.FiniteCellFinal.actual_residual_sum
#print axioms QuantumNLS.FiniteCellFinal.finite_target_bounds
#print axioms QuantumNLS.FiniteCellFinal.symbol
#print axioms QuantumNLS.FiniteCellFinal.completePhase_symbol
#print axioms QuantumNLS.FiniteCellFinal.tested_nonzero
#print axioms QuantumNLS.FiniteCellFinal.finite_target_symbol_bounds
#print axioms QuantumNLS.FiniteCellFinal.scalar_finite_cell_gauge

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellFinal.boundaryBound,
    ``QuantumNLS.FiniteCellFinal.printedBound,
    ``QuantumNLS.FiniteCellFinal.forward_bound,
    ``QuantumNLS.FiniteCellFinal.adjoint_bound,
    ``QuantumNLS.FiniteCellFinal.target,
    ``QuantumNLS.FiniteCellFinal.target_selected,
    ``QuantumNLS.FiniteCellFinal.actions,
    ``QuantumNLS.FiniteCellFinal.phases,
    ``QuantumNLS.FiniteCellFinal.good,
    ``QuantumNLS.FiniteCellFinal.actions_selected,
    ``QuantumNLS.FiniteCellFinal.phases_selected,
    ``QuantumNLS.FiniteCellFinal.actual_residual_sum,
    ``QuantumNLS.FiniteCellFinal.finite_target_bounds,
    ``QuantumNLS.FiniteCellFinal.symbol,
    ``QuantumNLS.FiniteCellFinal.completePhase_symbol,
    ``QuantumNLS.FiniteCellFinal.tested_nonzero,
    ``QuantumNLS.FiniteCellFinal.finite_target_symbol_bounds,
    ``QuantumNLS.FiniteCellFinal.scalar_finite_cell_gauge]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Abstract finite-cell proof reached EXT-001: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"FiniteCellFinal aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
