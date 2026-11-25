import QuantumNLS.Ext005CoreDensityR36b
import QuantumNLS.Ext005LimitRegularityR35b

/-! Epsilon-independent forward bounds derived from the literal source
hypotheses. No core density, evolution or uniform energy premise remains. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005SourceBoundsR36b
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005RegularizedR33b
open Ext005ComplexForceR113 Ext005ComplexRieszR113 Ext005SourceIntervalR32b
open Ext005ComparisonEnergyR34b Ext005SourceEnergyR34b
open Ext005CoreDensityR36b Ext005ForwardEstimateR35b
open Ext005LimitRegularityR35b
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- Unconditional source forward Gronwall estimate for the actual smoothed
regularized solution. The estimate does not assert an uncut form bound. -/
theorem source_uniform_forward_regularized (e : ℝ) (he : 0 < e)
    (s : ℝ) (hs : s ∈ Icc a b) (u₀ : FormDomain A) :
    ∃ u : ℝ → FormDomain A, u s = u₀ ∧ Continuous u ∧
      (∀ t ∈ Icc a b, HasDerivAt u
        (generator ((inclusion A).restrictScalars ℝ) e he
          (forceMap (formOperator (sourceForm A a b S t))) (u t)) t) ∧
      (∀ t, ‖inclusion A (u t)‖ = ‖inclusion A u₀‖) ∧
      (∀ t ∈ Icc s b,
        modifiedEnergy A a b S e he u t ≤ finiteBound A a b S * ‖u₀‖^2 *
          Real.exp ((S.C^2 + S.C^3) * (t - s))) ∧
      (∀ t ∈ Icc s b,
        ‖cutoff ((inclusion A).restrictScalars ℝ) e he (u t)‖ ^ 2 ≤
          S.C * finiteBound A a b S * ‖u₀‖^2 *
            Real.exp ((S.C^2 + S.C^3) * (t - s))) := by
  exact source_uniform_forward_regularized_of_core A a b S e he
    (cutoffOperatorCore_dense A S.B S.commute e he) s hs u₀

/-- Explicit form radius on the whole forward interval, independent of n. -/
def forwardRadius (u₀ : FormDomain A) : ℝ :=
  Real.sqrt (S.C * finiteBound A a b S * ‖u₀‖^2 *
    Real.exp ((S.C^2 + S.C^3) * (b-a)))

lemma forwardRadius_nonneg (u₀ : FormDomain A) : 0 ≤ forwardRadius A a b S u₀ :=
  Real.sqrt_nonneg _

/-- One actual sequence of approximate solutions, with uniform smoothed
Q(A) bounds and uniform antidual time modulus, constructed from SourceOn. -/
theorem source_bounded_approximate_sequence (hab : a ≤ b) (u₀ : FormDomain A) :
    ∃ u : ℕ → ℝ → FormDomain A,
      (∀ n, u n a = u₀) ∧ (∀ n, Continuous (u n)) ∧
      (∀ n t, t ∈ Icc a b → HasDerivAt (u n)
        (generator ((inclusion A).restrictScalars ℝ) (epsilon n) (epsilon_pos n)
          (forceMap (formOperator (sourceForm A a b S t))) (u n t)) t) ∧
      (∀ n t, ‖inclusion A (u n t)‖ = ‖inclusion A u₀‖) ∧
      (∀ n t, t ∈ Icc a b →
        ‖C ((inclusion A).restrictScalars ℝ) n (u n t)‖ ≤ forwardRadius A a b S u₀) ∧
      (∀ n s, s ∈ Icc a b → ∀ t, t ∈ Icc a b →
        ‖gram ((inclusion A).restrictScalars ℝ) (C ((inclusion A).restrictScalars ℝ) n (u n t)) -
          gram ((inclusion A).restrictScalars ℝ) (C ((inclusion A).restrictScalars ℝ) n (u n s))‖ ≤
          finiteBound A a b S * forwardRadius A a b S u₀ * ‖t-s‖) := by
  have hex (n : ℕ) := source_uniform_forward_regularized A a b S
    (epsilon n) (epsilon_pos n) a ⟨le_rfl, hab⟩ u₀
  choose u hu0 hc hd hn hE hQ using hex
  have hb (n : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖C ((inclusion A).restrictScalars ℝ) n (u n t)‖ ≤ forwardRadius A a b S u₀ := by
    apply Real.le_sqrt_of_sq_le
    apply (hQ n t ht).trans
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (mul_nonneg S.constant_pos.le (finiteBound_nonneg A a b S)) (sq_nonneg _))
    apply Real.exp_le_exp.mpr
    have hC := S.constant_pos.le
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (by positivity)
  refine ⟨u, hu0, hc, hd, hn, hb, ?_⟩
  intro n
  exact smoothed_antidual_time_bound ((inclusion A).restrictScalars ℝ)
    (epsilon n) (epsilon_pos n) a b (u n)
    (fun t => forceMap (formOperator (sourceForm A a b S t)))
    (finiteBound A a b S) (forwardRadius A a b S u₀) (finiteBound_nonneg A a b S)
    (hd n) (fun t ht => by rw [force_norm]; exact coefficient_bound A a b S t ht) (hb n)

end QuantumNLS.Ext005SourceBoundsR36b
#print axioms QuantumNLS.Ext005SourceBoundsR36b.source_uniform_forward_regularized
#print axioms QuantumNLS.Ext005SourceBoundsR36b.source_bounded_approximate_sequence

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005SourceBoundsR36b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005SourceBoundsR36b." then
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
  Lean.logInfo m!"R36b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
