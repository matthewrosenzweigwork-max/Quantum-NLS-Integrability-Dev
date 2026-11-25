import QuantumNLS.Ext005CoreCommutationR35b
import Mathlib.Analysis.ODE.Gronwall

/-! Forward Gronwall estimates for the already constructed source curves.
The sole extra source bridge is density of the explicit invariant B core.
It is not discharged here. Bounds concern P_e u_e, never a relabeled u_e.
The source commutator remains one-sided; no reverse estimate is inferred. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005ForwardEstimateR35b
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
open Ext005GramResolventR112 Ext005RegularizedR33b Ext005ComplexForceR113
open Ext005ComplexRieszR113 Ext005SourceIntervalR32b Ext005ComparisonEnergyR34b
open Ext005SourceEnergyR34b Ext005SourceRegularizedR33b
open Ext005CommutatorCoreR35b Ext005CoreCommutationR35b
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- Coercivity for the actual modified energy follows from the proven
comparison contraction. Density of the invariant operator core is explicit. -/
lemma smoothed_energy_control (e : ℝ) (he : 0 < e)
    (hd : Dense (cutoffOperatorCore A S.B e he))
    (u : ℝ → FormDomain A) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖cutoff ((inclusion A).restrictScalars ℝ) e he (u t)‖ ^ 2 ≤
      S.C * modifiedEnergy A a b S e he u t := by
  have hc := comparison_cutoff_contraction_of_core A S.B S.domain e he hd e he (u t)
  have hl := modified_energy_lower A a b S e he u t ht
  dsimp only at hl
  have hh : S.C⁻¹ * ‖cutoff ((inclusion A).restrictScalars ℝ) e he (u t)‖ ^ 2 ≤
      modifiedEnergy A a b S e he u t := by
    nlinarith [mul_nonneg S.constant_pos.le (sub_nonneg.mpr hc)]
  have hh' := mul_le_mul_of_nonneg_left hh S.constant_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ S.constant_pos.ne', one_mul] at hh'
  exact hh'

/-- The differential inequality is a conclusion of the literal source
bounds, the actual energy identities and invariant-core density. -/
lemma modified_energy_derivative_le (e : ℝ) (he : 0 < e)
    (hd : Dense (cutoffOperatorCore A S.B e he))
    (u : ℝ → FormDomain A) (t : ℝ) (ht : t ∈ Icc a b) :
    let K := comparison A (plusOne S.B) S.domain
    let P := cutoff ((inclusion A).restrictScalars ℝ) e he
    let g := generator ((inclusion A).restrictScalars ℝ) e he
      (forceMap (formOperator (sourceForm A a b S t))) (u t)
    S.diagonalDerivative t (P (u t)) + S.C * (2 * (⟪K (u t), K g⟫_ℂ).re) ≤
      (S.C^2 + S.C^3) * modifiedEnergy A a b S e he u t := by
  dsimp only
  have hB := source_comparison_derivative_bound A a b S e he hd t ht (u t)
  have hD := (le_abs_self (S.diagonalDerivative t
    (cutoff ((inclusion A).restrictScalars ℝ) e he (u t)))).trans
      (S.derivative_bound _ t ht)
  have hQ := smoothed_energy_control A a b S e he hd u t ht
  have hBc := mul_le_mul_of_nonneg_left hB S.constant_pos.le
  have hC := S.constant_pos
  have hQc := mul_le_mul_of_nonneg_left hQ
    (show 0 ≤ S.C + S.C^2 by positivity)
  nlinarith

/-- Conditional FORWARD estimate with an actual constructed curve and a
constant independent of epsilon. The invariant-core density is an algebraic
source bridge, not an assumed solution or an assumed energy conclusion. -/
theorem source_uniform_forward_regularized_of_core (e : ℝ) (he : 0 < e)
    (hd : Dense (cutoffOperatorCore A S.B e he))
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
  obtain ⟨u, hu0, hcont, hderiv, hnorm, _⟩ :=
    source_regularized_energy_exists A a b S e he s hs u₀
  let E := modifiedEnergy A a b S e he u
  let D := fun t => S.diagonalDerivative t
    (cutoff ((inclusion A).restrictScalars ℝ) e he (u t)) + S.C *
      (2 * (⟪comparison A (plusOne S.B) S.domain (u t),
        comparison A (plusOne S.B) S.domain
          (generator ((inclusion A).restrictScalars ℝ) e he
            (forceMap (formOperator (sourceForm A a b S t))) (u t))⟫_ℂ).re)
  have hE (t : ℝ) (ht : t ∈ Icc a b) : HasDerivWithinAt E (D t) (Icc a b) t :=
    modified_energy_derivative A a b S e he u t ht (hderiv t ht)
  have hecont : ContinuousOn E (Icc s b) := by
    intro t ht
    exact ((hE t ⟨hs.1.trans ht.1, ht.2⟩).continuousWithinAt).mono
      (Icc_subset_Icc hs.1 le_rfl)
  have heinit : E s ≤ finiteBound A a b S * ‖u₀‖^2 := by
    have h := modified_energy_upper A a b S e he u s hs
    simpa only [hu0] using h
  have hegron : ∀ t ∈ Icc s b, E t ≤ finiteBound A a b S * ‖u₀‖^2 *
      Real.exp ((S.C^2 + S.C^3) * (t - s)) := by
    have hg := le_gronwallBound_of_liminf_deriv_right_le (f := E) (f' := D)
      (K := S.C^2 + S.C^3) (ε := 0) hecont (fun t ht r hr =>
        ((hE t ⟨hs.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨hs.1.trans ht.1, ht.2⟩)).liminf_right_slope_le hr)
      heinit (fun t ht => by
        simpa only [add_zero] using modified_energy_derivative_le A a b S e he hd u t
          ⟨hs.1.trans ht.1, ht.2.le⟩)
    simpa only [gronwallBound_ε0] using hg
  refine ⟨u, hu0, hcont, hderiv, hnorm, hegron, ?_⟩
  intro t ht
  have hq := smoothed_energy_control A a b S e he hd u t ⟨hs.1.trans ht.1, ht.2⟩
  have hg := mul_le_mul_of_nonneg_left (hegron t ht) S.constant_pos.le
  exact hq.trans (by simpa only [mul_assoc] using hg)

end QuantumNLS.Ext005ForwardEstimateR35b
#print axioms QuantumNLS.Ext005ForwardEstimateR35b.source_uniform_forward_regularized_of_core

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ForwardEstimateR35b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ForwardEstimateR35b." then
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
  Lean.logInfo m!"R35b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
