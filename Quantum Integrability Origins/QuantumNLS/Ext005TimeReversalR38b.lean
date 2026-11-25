import QuantumNLS.Ext005ForwardContractR37b

/-! Exact analytic data under t ↦ -t. This module does NOT assert that the
one-sided source hypotheses are invariant. The missing reverse coercivity
and opposite commutator estimates remain explicit mathematical obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005TimeReversalR38b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b
open Ext005AlgebraicFormR114 Ext005FormEmbeddingR114
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)

lemma reflected_mem (t : ℝ) (ht : t ∈ Icc (-b) (-a)) : -t ∈ Icc a b := by
  constructor <;> linarith [ht.1, ht.2]

/-- The sign is forced by the Schrödinger equation. -/
def reversedHamiltonian (t : ℝ) : RawForm (FormDomain A) := -S.hamiltonian (-t)

@[simp] lemma reversedHamiltonian_apply (t : ℝ) (u v : FormDomain A) :
    reversedHamiltonian A a b S t u v = -S.hamiltonian (-t) u v := rfl

lemma reversed_symmetric (t : ℝ) (ht : t ∈ Icc (-b) (-a)) :
    Hermitian (reversedHamiltonian A a b S t) := by
  intro u v
  simp only [reversedHamiltonian_apply, map_neg,
    S.symmetric (-t) (reflected_mem a b t ht) u v]

/-- The already derived TWO-SIDED form bound survives sign reversal. -/
lemma reversed_diagonal_bound (t : ℝ) (ht : t ∈ Icc (-b) (-a)) (u : FormDomain A) :
    |(reversedHamiltonian A a b S t u u).re| ≤ finiteBound A a b S * ‖u‖ ^ 2 := by
  simpa only [reversedHamiltonian_apply, Complex.neg_re, abs_neg] using
    source_diagonal_bound A a b S (-t) (reflected_mem a b t ht) u

/-- Double negation cancels in the diagonal time derivative. No derivative
of the diagonalDerivative itself is assumed or used. -/
lemma reversed_derivative (u : FormDomain A) (t : ℝ) (ht : t ∈ Icc (-b) (-a)) :
    HasDerivWithinAt (fun r => (reversedHamiltonian A a b S r u u).re)
      (S.diagonalDerivative (-t) u) (Icc (-b) (-a)) t := by
  have hn : HasDerivWithinAt (fun r : ℝ => -r) (-1) (Icc (-b) (-a)) t :=
    (hasDerivAt_id t).neg.hasDerivWithinAt
  have hd := (S.derivative u (-t) (reflected_mem a b t ht)).comp t hn
    (fun r hr => reflected_mem a b r hr)
  convert! hd.neg using 1
  simp

lemma reversed_derivative_bound (u : FormDomain A) (t : ℝ)
    (ht : t ∈ Icc (-b) (-a)) :
    |S.diagonalDerivative (-t) u| ≤ S.C * ‖u‖ ^ 2 :=
  S.derivative_bound u (-t) (reflected_mem a b t ht)

/-- Algebraic identity: the commutator changes sign, even though the time
scalar derivative above does not. In particular the inherited upper bound
cannot be reused as the required reversed upper bound. -/
lemma reversed_commutator (t : ℝ) (u v : FormDomain A) :
    (Complex.I * (reversedHamiltonian A a b S t v u -
      reversedHamiltonian A a b S t u v)).re =
    -(Complex.I * (S.hamiltonian (-t) v u - S.hamiltonian (-t) u v)).re := by
  simp only [reversedHamiltonian_apply, neg_sub_neg, mul_sub, Complex.sub_re]
  ring

/-- What the source actually implies is a LOWER bound for the reversed
commutator. All actual B-domain premises are retained. -/
lemma reversed_commutator_lower (t : ℝ) (ht : t ∈ Icc (-b) (-a))
    (u : FormDomain A) (hu : inclusion A u ∈ S.B.op.domain) (v : FormDomain A)
    (hv : inclusion A v = S.B.op ⟨inclusion A u, hu⟩) :
    -(S.C * ‖u‖ ^ 2) ≤
      (Complex.I * (reversedHamiltonian A a b S t v u -
        reversedHamiltonian A a b S t u v)).re := by
  rw [reversed_commutator]
  linarith [S.commutator (-t) (reflected_mem a b t ht) u hu v hv]

/-- Exact remaining lower-coercivity obligation with unchanged B.
This equivalence is proved, not the inequality on either side. -/
lemma reversed_lower_iff (K t : ℝ) (u : FormDomain A) :
    (K⁻¹ * ‖u‖ ^ 2 - K * comparisonEnergy A S.B S.domain u ≤
      (reversedHamiltonian A a b S t u u).re) ↔
    (S.hamiltonian (-t) u u).re ≤
      K * comparisonEnergy A S.B S.domain u - K⁻¹ * ‖u‖ ^ 2 := by
  simp only [reversedHamiltonian_apply, Complex.neg_re]
  constructor <;> intro h <;> linarith

/-- If B has zero form energy on a nonzero vector and the original diagonal
is nonnegative there, no positive constant repairs this reversed lower
bound while keeping B. This does not rule out another choice of B. -/
lemma reversed_lower_impossible_at_zero_comparison (t : ℝ) (u : FormDomain A)
    (hu : u ≠ 0) (hB : comparisonEnergy A S.B S.domain u = 0)
    (hH : 0 ≤ (S.hamiltonian (-t) u u).re) :
    ¬ ∃ K : ℝ, 0 < K ∧
      K⁻¹ * ‖u‖ ^ 2 - K * comparisonEnergy A S.B S.domain u ≤
        (reversedHamiltonian A a b S t u u).re := by
  rintro ⟨K, hK, hb⟩
  have hn : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hp : 0 < K⁻¹ * ‖u‖ ^ 2 := mul_pos (inv_pos.mpr hK) hn
  simp only [hB, mul_zero, sub_zero, reversedHamiltonian_apply, Complex.neg_re] at hb
  linarith

/-- Scalar trace coefficients for the analytic half-line diagnostic below:
for any proposed constant K the reverse trace 1 exceeds K times the form
energy (3ε+7ε³)/4 for some 0<ε<1. This is solely a scalar algebra lemma;
no Sobolev/operator identification is claimed as a Lean conclusion. -/
lemma trace_energy_no_uniform_bound (K : ℝ) :
    ∃ e : ℝ, 0 < e ∧ e < 1 ∧ K * ((3 * e + 7 * e ^ 3) / 4) < 1 := by
  let e : ℝ := (10 * (|K| + 1))⁻¹
  have he : 0 < e := by dsimp [e]; positivity
  have heq : 10 * (|K| + 1) * e = 1 := by
    dsimp [e]
    exact mul_inv_cancel₀ (by positivity)
  have he1 : e < 1 := by nlinarith [abs_nonneg K]
  have he3 : e ^ 3 ≤ e := by nlinarith [sq_nonneg e, mul_nonneg he.le (sq_nonneg (1-e))]
  have hk : K ≤ |K| := le_abs_self K
  have hE : 0 ≤ (3 * e + 7 * e ^ 3) / 4 := by positivity
  refine ⟨e, he, he1, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hk hE
  have hc := mul_le_mul_of_nonneg_left he3 (abs_nonneg K)
  nlinarith [abs_nonneg K]

end QuantumNLS.Ext005TimeReversalR38b
#print axioms QuantumNLS.Ext005TimeReversalR38b.reversed_derivative
#print axioms QuantumNLS.Ext005TimeReversalR38b.reversed_commutator_lower
#print axioms QuantumNLS.Ext005TimeReversalR38b.reversed_lower_impossible_at_zero_comparison
#print axioms QuantumNLS.Ext005TimeReversalR38b.trace_energy_no_uniform_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005TimeReversalR38b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005TimeReversalR38b." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R38b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
