import QuantumNLS.FiniteCellPaths

/-! R-D8BB052C group D. Canonical scalar selection on EVERY complete array,
from completed seeds and deterministic paths alone, before all test data.
This module does not assert the quantitative residual bound. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate Classical
namespace QuantumNLS.FiniteCellGauge
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport FiniteCellPartition FiniteCellPaths
variable {N : ℕ}

def phaseOne : Phase := ⟨1, norm_one⟩
def phaseMul (z w : Phase) : Phase := ⟨z.1 * w.1, by rw [norm_mul, z.2, w.2, one_mul]⟩

theorem next_labels_ne (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) :
    firstAbove I K ell m n hc hne ≠ firstBelow I K ell m n hc hne := by
  have ha := (firstAbove_spec I K ell m n hc hne).2
  have hb := (firstBelow_spec I K ell m n hc hne).2
  intro he
  rw [he] at ha
  omega

/-- The actual coefficient on the prescribed next seed edge. -/
def stepPhase (c : OrderedSeeds N) (I : Finset ℤ) (K ell : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) (hne : m ≠ n) : Phase :=
  seedPhase c (firstAbove I K ell m n hc hne) (firstBelow I K ell m n hc hne)
    (next_labels_ne I K ell m n hc hne)
    ⟨m, by have h := (firstAbove_spec I K ell m n hc hne).2; unfold DonorOK; omega⟩

/-- Product of the completed seed coefficients along the computed walk. -/
def walkPhase (c : OrderedSeeds N) (I : Finset ℤ) (K ell : ℕ) :
    ℕ → (m n : Arr N) → SameCell I K ell m n → Phase
  | 0, _, _, _ => phaseOne
  | fuel + 1, m, n, hc =>
      if he : m = n then phaseOne
      else phaseMul (stepPhase c I K ell m n hc he)
        (walkPhase c I K ell fuel (next I K ell m n hc he) n (next_sameCell I K ell m n hc he))

/-- The same scalar exists on every complete array; no test vector/target is an argument. -/
def q (c : OrderedSeeds N) (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : Phase :=
  walkPhase c I K ell (distance I (root I K ell m).1 m) m (root I K ell m).1 (root I K ell m).2

theorem q_unit (c : OrderedSeeds N) (I : Finset ℤ) (K ell : ℕ) (m : Arr N) :
    ‖(q c I K ell m).1‖ = 1 := (q c I K ell m).2

theorem walkPhase_of_eq (c : OrderedSeeds N) (I : Finset ℤ) (K ell : ℕ) (fuel : ℕ)
    (m n : Arr N) (hc : SameCell I K ell m n) (he : m = n) :
    walkPhase c I K ell fuel m n hc = phaseOne := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [walkPhase, dite_eq_left he]

theorem q_root (c : OrderedSeeds N) (I : Finset ℤ) (K ell : ℕ) (m : Arr N) :
    q c I K ell (root I K ell m).1 = phaseOne :=
  walkPhase_of_eq c I K ell _ _ _ _ (root_eq_of_sameCell I K ell (root I K ell m).2)

/-- Only one raw seed per unordered SELECTED pair is required from the caller. -/
abbrev SelectedSeeds (I : Finset ℤ) (N : ℕ) :=
  ∀ (a b : ℤ), a ∈ I → b ∈ I → a < b → Donor N a → ℂ

/-- Unused nonselected coefficients have a fixed deterministic zero extension. -/
def extendSeeds (I : Finset ℤ) (c : SelectedSeeds I N) : OrderedSeeds N :=
  fun a b hab m => if ha : a ∈ I then if hb : b ∈ I then c a b ha hb hab m else 0 else 0

theorem extendSeeds_selected (I : Finset ℤ) (c : SelectedSeeds I N) (a b : ℤ)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a < b) (m : Donor N a) :
    extendSeeds I c a b hab m = c a b ha hb hab m := by
  simp only [extendSeeds, dite_eq_left ha, dite_eq_left hb]

/-- The printed threshold K=ceil(N/ell), as a natural number. -/
def threshold (N ell : ℕ) : ℕ := Nat.ceil ((N : ℝ) / (ell : ℝ))

/-- The proposition's scalar needs exactly the selected seed data and fixed order. -/
def q_N (I : Finset ℤ) (ell : ℕ) (c : SelectedSeeds I N) : Arr N → Phase :=
  q (extendSeeds I c) I (threshold N ell) ell

theorem q_N_unit (I : Finset ℤ) (ell : ℕ) (c : SelectedSeeds I N) (m : Arr N) :
    ‖(q_N I ell c m).1‖ = 1 := (q_N I ell c m).2

theorem q_N_eq_walkPhase (I : Finset ℤ) (ell : ℕ) (c : SelectedSeeds I N) (m : Arr N) :
    q_N I ell c m =
      walkPhase (extendSeeds I c) I (threshold N ell) ell
        (distance I (root I (threshold N ell) ell m).1 m)
        m (root I (threshold N ell) ell m).1 (root I (threshold N ell) ell m).2 := rfl

/-- Every pair ratio is defined from one scalar, including labels outside I. -/
def ratio (Q : Arr N → Phase) (m n : Arr N) : Phase :=
  ⟨(Q m).1 * conj (Q n).1, by rw [norm_mul, Complex.norm_conj, (Q m).2, (Q n).2, one_mul]⟩

theorem ratio_self (Q : Arr N → Phase) (m : Arr N) : (ratio Q m m).1 = 1 := by
  change (Q m).1 * conj (Q m).1 = 1
  rw [mul_comm, phase_conj_mul]

theorem ratio_trans (Q : Arr N → Phase) (m n p : Arr N) :
    (ratio Q m n).1 * (ratio Q n p).1 = (ratio Q m p).1 := by
  change ((Q m).1 * conj (Q n).1) * ((Q n).1 * conj (Q p).1) = _
  calc
    _ = (Q m).1 * (conj (Q n).1 * (Q n).1) * conj (Q p).1 := by ring
    _ = (ratio Q m p).1 := by rw [phase_conj_mul, mul_one]; rfl

theorem ratio_reverse (Q : Arr N → Phase) (m n : Arr N) :
    (ratio Q n m).1 = conj (ratio Q m n).1 := by
  simp only [ratio, map_mul, starRingEnd_self_apply]
  ring

/-- Product along an arbitrary finite vertex path; no flatness of seeds is used. -/
def pathProduct (Q : Arr N → Phase) (m : Arr N) : List (Arr N) → ℂ
  | [] => 1
  | n :: tail => (ratio Q m n).1 * pathProduct Q n tail

theorem pathProduct_telescope (Q : Arr N → Phase) (m n : Arr N) (vertices : List (Arr N)) :
    pathProduct Q m (vertices ++ [n]) = (ratio Q m n).1 := by
  induction vertices generalizing m with
  | nil => simp only [List.nil_append, pathProduct, mul_one]
  | cons v tail ih =>
    simp only [List.cons_append, pathProduct, ih, ratio_trans]

theorem closed_path (Q : Arr N → Phase) (m : Arr N) (vertices : List (Arr N)) :
    pathProduct Q m (vertices ++ [m]) = 1 := by
  rw [pathProduct_telescope, ratio_self]

/-- Literal FOA1 edge phases on the complete donor domain. -/
def edgePhase (Q : Arr N → Phase) (a b : ℤ) (m : Donor N a) : Phase :=
  ratio Q m.1 (destination N a b m)

/-- Complete-array partial shift, zero on an empty donor, without exterior cutoff. -/
def W (Q : Arr N → Phase) (a b : ℤ) : H N →L[ℂ] H N :=
  transfer a b (edgePhase Q a b)

theorem W_basis (Q : Arr N → Phase) (a b : ℤ) (m : Arr N) :
    W Q a b (lp.single 2 m 1) =
      if hd : DonorOK a m.1 then
        (ratio Q m (shiftArr a b m hd)).1 • lp.single 2 (shiftArr a b m hd) 1 else 0 :=
  transfer_basis a b (edgePhase Q a b) m

theorem W_norm_le (Q : Arr N → Phase) (a b : ℤ) : ‖W Q a b‖ ≤ 1 :=
  transfer_norm_le a b (edgePhase Q a b)

theorem edgePhase_reverse (Q : Arr N → Phase) (a b : ℤ) (hab : a ≠ b) :
    reversePhase a b hab (edgePhase Q a b) = edgePhase Q b a := by
  funext d
  apply Subtype.ext
  have he : destination N a b ((donorEquiv a b hab).symm d) = d.1 :=
    congrArg Subtype.val ((donorEquiv a b hab).apply_symm_apply d)
  change conj (ratio Q ((donorEquiv a b hab).symm d).1
    (destination N a b ((donorEquiv a b hab).symm d))).1 =
    (ratio Q d.1 (destination N b a d)).1
  rw [he, ← ratio_reverse]
  rfl

theorem W_adjoint (Q : Arr N → Phase) (a b : ℤ) (hab : a ≠ b) :
    (W Q a b).adjoint = W Q b a := by
  change (transfer a b (edgePhase Q a b)).adjoint = transfer b a (edgePhase Q b a)
  rw [transfer_adjoint a b hab, edgePhase_reverse]

theorem W_star (Q : Arr N → Phase) (a b : ℤ) (hab : a ≠ b) :
    star (W Q a b) = W Q b a :=
  (ContinuousLinearMap.star_eq_adjoint _).trans (W_adjoint Q a b hab)

/-- Actual operator transport along two allowed edges has the telescoped scalar. -/
theorem W_two_step (Q : Arr N → Phase) (a b c d : ℤ) (m : Arr N)
    (ha : DonorOK a m.1) (hc : DonorOK c (shiftArr a b m ha).1) :
    W Q c d (W Q a b (lp.single 2 m 1)) =
      (ratio Q m (shiftArr c d (shiftArr a b m ha) hc)).1 •
        lp.single 2 (shiftArr c d (shiftArr a b m ha) hc) 1 := by
  rw [W_basis, dite_eq_left ha, map_smul, W_basis, dite_eq_left hc,
    smul_smul, ratio_trans]

theorem W_initial_projection (Q : Arr N → Phase) (a b : ℤ) :
    (W Q a b).adjoint ∘L W Q a b = support a :=
  transfer_initial_projection a b (edgePhase Q a b)

theorem W_final_projection (Q : Arr N → Phase) (a b : ℤ) (hab : a ≠ b) :
    W Q a b ∘L (W Q a b).adjoint = support b :=
  transfer_final_projection a b hab (edgePhase Q a b)

/-- Clauses concerning existence, unit modulus and exact ratios, without testing hypotheses. -/
theorem canonical_gauge_exact (I : Finset ℤ) (ell : ℕ) (c : SelectedSeeds I N) :
    ∃ Q : Arr N → Phase, Q = q_N I ell c ∧
      (∀ m, ‖(Q m).1‖ = 1) ∧
      (∀ m, Q (root I (threshold N ell) ell m).1 = phaseOne) ∧
      (∀ a b, ‖W Q a b‖ ≤ 1) ∧
      (∀ a b, a ≠ b → (W Q a b).adjoint = W Q b a) ∧
      (∀ m n p, (ratio Q m n).1 * (ratio Q n p).1 = (ratio Q m p).1) ∧
      (∀ m vertices, pathProduct Q m (vertices ++ [m]) = 1) :=
  ⟨q_N I ell c, rfl, q_N_unit I ell c, q_root (extendSeeds I c) I (threshold N ell) ell,
    W_norm_le _, W_adjoint _, ratio_trans _, closed_path _⟩

end QuantumNLS.FiniteCellGauge

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellGauge.phaseOne
#print axioms QuantumNLS.FiniteCellGauge.phaseMul
#print axioms QuantumNLS.FiniteCellGauge.next_labels_ne
#print axioms QuantumNLS.FiniteCellGauge.stepPhase
#print axioms QuantumNLS.FiniteCellGauge.walkPhase
#print axioms QuantumNLS.FiniteCellGauge.q
#print axioms QuantumNLS.FiniteCellGauge.q_unit
#print axioms QuantumNLS.FiniteCellGauge.walkPhase_of_eq
#print axioms QuantumNLS.FiniteCellGauge.q_root
#print axioms QuantumNLS.FiniteCellGauge.SelectedSeeds
#print axioms QuantumNLS.FiniteCellGauge.extendSeeds
#print axioms QuantumNLS.FiniteCellGauge.extendSeeds_selected
#print axioms QuantumNLS.FiniteCellGauge.threshold
#print axioms QuantumNLS.FiniteCellGauge.q_N
#print axioms QuantumNLS.FiniteCellGauge.q_N_unit
#print axioms QuantumNLS.FiniteCellGauge.q_N_eq_walkPhase
#print axioms QuantumNLS.FiniteCellGauge.ratio
#print axioms QuantumNLS.FiniteCellGauge.ratio_self
#print axioms QuantumNLS.FiniteCellGauge.ratio_trans
#print axioms QuantumNLS.FiniteCellGauge.ratio_reverse
#print axioms QuantumNLS.FiniteCellGauge.pathProduct
#print axioms QuantumNLS.FiniteCellGauge.pathProduct_telescope
#print axioms QuantumNLS.FiniteCellGauge.closed_path
#print axioms QuantumNLS.FiniteCellGauge.edgePhase
#print axioms QuantumNLS.FiniteCellGauge.W
#print axioms QuantumNLS.FiniteCellGauge.W_basis
#print axioms QuantumNLS.FiniteCellGauge.W_norm_le
#print axioms QuantumNLS.FiniteCellGauge.edgePhase_reverse
#print axioms QuantumNLS.FiniteCellGauge.W_adjoint
#print axioms QuantumNLS.FiniteCellGauge.W_star
#print axioms QuantumNLS.FiniteCellGauge.W_two_step
#print axioms QuantumNLS.FiniteCellGauge.W_initial_projection
#print axioms QuantumNLS.FiniteCellGauge.W_final_projection
#print axioms QuantumNLS.FiniteCellGauge.canonical_gauge_exact

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellGauge.phaseOne,
    ``QuantumNLS.FiniteCellGauge.phaseMul,
    ``QuantumNLS.FiniteCellGauge.next_labels_ne,
    ``QuantumNLS.FiniteCellGauge.stepPhase,
    ``QuantumNLS.FiniteCellGauge.walkPhase,
    ``QuantumNLS.FiniteCellGauge.q,
    ``QuantumNLS.FiniteCellGauge.q_unit,
    ``QuantumNLS.FiniteCellGauge.walkPhase_of_eq,
    ``QuantumNLS.FiniteCellGauge.q_root,
    ``QuantumNLS.FiniteCellGauge.SelectedSeeds,
    ``QuantumNLS.FiniteCellGauge.extendSeeds,
    ``QuantumNLS.FiniteCellGauge.extendSeeds_selected,
    ``QuantumNLS.FiniteCellGauge.threshold,
    ``QuantumNLS.FiniteCellGauge.q_N,
    ``QuantumNLS.FiniteCellGauge.q_N_unit,
    ``QuantumNLS.FiniteCellGauge.q_N_eq_walkPhase,
    ``QuantumNLS.FiniteCellGauge.ratio,
    ``QuantumNLS.FiniteCellGauge.ratio_self,
    ``QuantumNLS.FiniteCellGauge.ratio_trans,
    ``QuantumNLS.FiniteCellGauge.ratio_reverse,
    ``QuantumNLS.FiniteCellGauge.pathProduct,
    ``QuantumNLS.FiniteCellGauge.pathProduct_telescope,
    ``QuantumNLS.FiniteCellGauge.closed_path,
    ``QuantumNLS.FiniteCellGauge.edgePhase,
    ``QuantumNLS.FiniteCellGauge.W,
    ``QuantumNLS.FiniteCellGauge.W_basis,
    ``QuantumNLS.FiniteCellGauge.W_norm_le,
    ``QuantumNLS.FiniteCellGauge.edgePhase_reverse,
    ``QuantumNLS.FiniteCellGauge.W_adjoint,
    ``QuantumNLS.FiniteCellGauge.W_star,
    ``QuantumNLS.FiniteCellGauge.W_two_step,
    ``QuantumNLS.FiniteCellGauge.W_initial_projection,
    ``QuantumNLS.FiniteCellGauge.W_final_projection,
    ``QuantumNLS.FiniteCellGauge.canonical_gauge_exact]
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
  Lean.logInfo m!"FiniteCellGauge aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
