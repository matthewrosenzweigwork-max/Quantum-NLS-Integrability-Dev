import QuantumNLS.Ext005RegularizedR33b
import QuantumNLS.Ext005SourceIntervalR32b

/-! Bounded regularized evolutions constructed from the literal source record.
The equation below has cutoffs on both form arguments. It does not assert
that a regularized curve solves the unregularized source equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005SourceRegularizedR33b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b Ext005ComplexRieszR113
open Ext005ComplexForceR113 Ext005GramResolventR112 Ext005RegularizedR33b
open Ext005HilbertEnergyR112
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (a b : ℝ) (hab : a ≤ b) (S : SourceOn A a b)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- A continuous extension in time, using only values on the source interval. -/
def clampedForce (t : ℝ) : FormDomain A →L[ℝ] FormDomain A :=
  forceMap (formOperator (sourceForm A a b S (projIcc a b hab t)))

lemma clampedForce_continuous : Continuous (clampedForce A a b hab S) := by
  apply forceMap.continuous.comp
  exact (coefficient_continuous A a b S).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc a b hab t).property)

lemma clampedForce_bound (t : ℝ) :
    ‖clampedForce A a b hab S t‖ ≤ finiteBound A a b S := by
  rw [clampedForce, force_norm]
  exact coefficient_bound A a b S _ (projIcc a b hab t).property

lemma clampedForce_diagonal (t : ℝ) (u : FormDomain A) :
    (⟪u, clampedForce A a b hab S t u⟫_ℂ).re = 0 := by
  exact force_diagonal _ (form_symmetric _
    (sourceForm_symmetric A a b S _ (projIcc a b hab t).property)) u

lemma clampedForce_eq (t : ℝ) (ht : t ∈ Icc a b) :
    clampedForce A a b hab S t = forceMap (formOperator (sourceForm A a b S t)) := by
  simp only [clampedForce, projIcc_of_mem hab ht]

/-- The regularized source solution, constructed for every positive epsilon.
The norm conservation and finite-interval form bound are conclusions. The
bound depends on epsilon, and therefore does not yet permit a D3 limit. -/
theorem source_regularized_exists (e : ℝ) (he : 0 < e)
    (s : ℝ) (hs : s ∈ Icc a b) (u₀ : FormDomain A) :
    let i := (inclusion A).restrictScalars ℝ
    let K := ‖inverse i e he‖ * finiteBound A a b S
    ∃ u : ℝ → FormDomain A, u s = u₀ ∧ Continuous u ∧
      (∀ t ∈ Icc a b, HasDerivAt u
        (generator i e he (forceMap (formOperator (sourceForm A a b S t))) (u t)) t) ∧
      (∀ t, ‖inclusion A (u t)‖ = ‖inclusion A u₀‖) ∧
      (∀ t ∈ Icc a b, ‖u t‖ ≤ ‖u₀‖ * Real.exp (K * (b - a))) ∧
      EnergyBounded i (Icc a b) (fun t => inclusion A (u t)) ∧
      (∀ t ∈ Icc a b, ∀ v : FormDomain A,
        HasDerivAt (fun r => (⟪inclusion A v, inclusion A (u r)⟫_ℂ).re)
          (S.hamiltonian t (cutoff i e he (u t)) (cutoff i e he v)).im t) := by
  dsimp only
  have hab : a ≤ b := hs.1.trans hs.2
  let i := (inclusion A).restrictScalars ℝ
  let K := ‖inverse i e he‖ * finiteBound A a b S
  obtain ⟨u, hu0, hud, hun, hub⟩ := exists_regularized i e he
    (clampedForce A a b hab S) (clampedForce_continuous A a b hab S)
    (clampedForce_diagonal A a b hab S) (finiteBound A a b S)
    (clampedForce_bound A a b hab S) s u₀
  have hc : Continuous u := continuous_iff_continuousAt.mpr (fun t => (hud t).continuousAt)
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg _) (finiteBound_nonneg A a b S)
  have hb (t : ℝ) (ht : t ∈ Icc a b) :
      ‖u t‖ ≤ ‖u₀‖ * Real.exp (K * (b - a)) := by
    apply (hub t).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hK
    exact abs_le.mpr ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩
  refine ⟨u, hu0, hc, ?_, hun, hb, ?_, ?_⟩
  · intro t ht
    simpa only [clampedForce_eq A a b hab S t ht] using hud t
  · refine ⟨‖u₀‖ * Real.exp (K * (b - a)), by positivity, ?_⟩
    exact ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ⟨u t, rfl, hb t ht⟩)
  · intro t ht v
    have hi := i.hasFDerivAt.comp_hasDerivAt t (hud t)
    have hp := (innerSL ℝ (i v)).hasFDerivAt.comp_hasDerivAt t hi
    change HasDerivAt (fun r => ⟪i v, i (u r)⟫_ℝ)
      (S.hamiltonian t (cutoff i e he (u t)) (cutoff i e he v)).im t
    simpa only [Function.comp_def, innerSL_apply_apply, generator_pair,
      clampedForce_eq A a b hab S t ht, force_pair, form_pair,
      sourceForm_apply A a b S t ht] using hp

end QuantumNLS.Ext005SourceRegularizedR33b
#print axioms QuantumNLS.Ext005SourceRegularizedR33b.source_regularized_exists

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005SourceRegularizedR33b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005SourceRegularizedR33b." then
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
  Lean.logInfo m!"R33b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
