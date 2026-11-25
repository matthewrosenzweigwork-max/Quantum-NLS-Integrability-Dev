import QuantumNLS.Ext005QuadraticChainR34b

/-! Actual cutoff Hamiltonian energy identity from SourceOn.
This does not assume or assert the still missing comparison-B evolution estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005SourceEnergyR34b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b Ext005ComplexRieszR113
open Ext005GramResolventR112 Ext005ComplexForceR113 Ext005RegularizedR33b
open Ext005SourceRegularizedR33b Ext005ComplexGramR34b Ext005QuadraticChainR34b
open Ext005FormEmbeddingR114
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- Energy of the smoothed vector, rather than an incorrectly uncut energy. -/
def cutoffEnergy (e : ℝ) (he : 0 < e) (u : ℝ → FormDomain A) (t : ℝ) : ℝ :=
  let w := cutoff ((inclusion A).restrictScalars ℝ) e he (u t)
  (S.hamiltonian t w w).re

/-- The source has only scalar diagonal derivatives. The moving-vector
chain rule supplies the rest, and the constructed complex Gram inverse
cancels the actual R33b generator term. -/
theorem cutoff_energy_derivative (e : ℝ) (he : 0 < e) (u : ℝ → FormDomain A)
    (t : ℝ) (ht : t ∈ Icc a b)
    (hu : HasDerivAt u
      (generator ((inclusion A).restrictScalars ℝ) e he
        (forceMap (formOperator (sourceForm A a b S t))) (u t)) t) :
    HasDerivWithinAt (cutoffEnergy A a b S e he u)
      (S.diagonalDerivative t (cutoff ((inclusion A).restrictScalars ℝ) e he (u t)))
      (Icc a b) t := by
  let : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
  let i := (inclusion A).restrictScalars ℝ
  let P := cutoff i e he
  let L := fun r => formOperator (sourceForm A a b S r)
  let w := fun r => P (u r)
  let w' := P (generator i e he (forceMap (L t)) (u t))
  have hw : HasDerivWithinAt w w' (Icc a b) t :=
    (P.hasFDerivAt.comp_hasDerivAt t hu).hasDerivWithinAt
  have hLc : ContinuousWithinAt (fun r => (L r).restrictScalars ℝ) (Icc a b) t := by
    exact ((ContinuousLinearMap.restrictScalarsIsometry ℝ (𝕜 := ℂ)
      (E := FormDomain A) (Fₗ := FormDomain A) (𝕜'' := ℝ)).continuous.continuousAt).comp_continuousWithinAt
        (coefficient_continuous A a b S t ht)
  have hsym (r : ℝ) (hr : r ∈ Icc a b) : ((L r).restrictScalars ℝ).IsSymmetric := by
    intro v z
    exact congrArg Complex.re (form_symmetric _ (sourceForm_symmetric A a b S r hr) v z)
  have hd : HasDerivWithinAt (fun r => (⟪w t, (L r) (w t)⟫_ℂ).re)
      (S.diagonalDerivative t (w t)) (Icc a b) t := by
    simpa only [L, form_pair] using sourceForm_derivative A a b S (w t) t ht
  have h := quadratic_chain (fun r => (L r).restrictScalars ℝ) w (Icc a b) t w'
    (S.diagonalDerivative t (w t)) hLc hsym hw hd
  change HasDerivWithinAt (fun r => (⟪w r, L r (w r)⟫_ℂ).re)
    (S.diagonalDerivative t (w t) + 2 * (⟪w', L t (w t)⟫_ℂ).re) (Icc a b) t at h
  have hz : (⟪w', L t (w t)⟫_ℂ).re = 0 := by
    have hr := congrArg Complex.re (inner_conj_symm (L t (w t)) w')
    simp only [Complex.conj_re] at hr
    exact hr.trans (cutoff_hamiltonian_cancel (inclusion A) e he (L t) (u t))
  simp only [hz, mul_zero, add_zero] at h
  apply h.congr_of_mem _ ht
  intro r hr
  change (S.hamiltonian r (w r) (w r)).re = (⟪w r, L r (w r)⟫_ℂ).re
  rw [show ⟪w r, L r (w r)⟫_ℂ = sourceForm A a b S r (w r) (w r) from form_pair _ _ _,
    sourceForm_apply A a b S r hr]

/-- The source lower bound yields the precise inhomogeneous energy
inequality. The B term is displayed, not discarded or presumed bounded. -/
theorem source_diagonal_energy_bound (t : ℝ) (ht : t ∈ Icc a b) (w : FormDomain A) :
    |S.diagonalDerivative t w| ≤
      S.C ^ 2 * (S.hamiltonian t w w).re +
        S.C ^ 3 * comparisonEnergy A S.B S.domain w := by
  have h := mul_le_mul_of_nonneg_left (S.lower t ht w) S.constant_pos.le
  have hc : S.C * S.C⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt S.constant_pos)
  rw [mul_sub, ← mul_assoc S.C S.C⁻¹, hc, one_mul] at h
  have hh := mul_le_mul_of_nonneg_left h S.constant_pos.le
  have hd := S.derivative_bound w t ht
  nlinarith

/-- No regularized evolution is a premise: inherit its Dyson construction
and add the newly derived actual Hamiltonian energy identity. -/
theorem source_regularized_energy_exists (e : ℝ) (he : 0 < e)
    (s : ℝ) (hs : s ∈ Icc a b) (u₀ : FormDomain A) :
    ∃ u : ℝ → FormDomain A, u s = u₀ ∧ Continuous u ∧
      (∀ t ∈ Icc a b, HasDerivAt u
        (generator ((inclusion A).restrictScalars ℝ) e he
          (forceMap (formOperator (sourceForm A a b S t))) (u t)) t) ∧
      (∀ t, ‖inclusion A (u t)‖ = ‖inclusion A u₀‖) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt (cutoffEnergy A a b S e he u)
        (S.diagonalDerivative t (cutoff ((inclusion A).restrictScalars ℝ) e he (u t)))
        (Icc a b) t) := by
  obtain ⟨u, hi, hc, hd, hn, _, _, _⟩ := source_regularized_exists A a b S e he s hs u₀
  exact ⟨u, hi, hc, hd, hn, fun t ht => cutoff_energy_derivative A a b S e he u t ht (hd t ht)⟩

end QuantumNLS.Ext005SourceEnergyR34b
#print axioms QuantumNLS.Ext005SourceEnergyR34b.cutoff_energy_derivative
#print axioms QuantumNLS.Ext005SourceEnergyR34b.source_regularized_energy_exists

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005SourceEnergyR34b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005SourceEnergyR34b." then
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
  Lean.logInfo m!"R34b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
