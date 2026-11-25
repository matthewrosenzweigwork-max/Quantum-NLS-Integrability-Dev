import QuantumNLS.Ext005SourceEnergyR34b

/-! Exact comparison-energy bookkeeping for the constructed regularization.
The residual comparison term remains explicit until a source commutation
argument supplies its sign and its commutator bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005ComparisonEnergyR34b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b Ext005ComplexRieszR113
open Ext005GramResolventR112 Ext005ComplexForceR113 Ext005RegularizedR33b
open Ext005SourceEnergyR34b Ext005FormEmbeddingR114 Ext005ShiftR114
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- B is left uncut in this modified energy. This choice avoids the false
replacement of a regularized B/H commutator by the bare source commutator. -/
def modifiedEnergy (e : ℝ) (he : 0 < e) (u : ℝ → FormDomain A) (t : ℝ) : ℝ :=
  cutoffEnergy A a b S e he u t + S.C * comparisonEnergy A S.B S.domain (u t)

/-- A uniform initial upper bound follows from the actual source upper
inequality, the constructed comparison map and cutoff contractivity. -/
theorem modified_energy_upper (e : ℝ) (he : 0 < e) (u : ℝ → FormDomain A)
    (t : ℝ) (ht : t ∈ Icc a b) :
    modifiedEnergy A a b S e he u t ≤ finiteBound A a b S * ‖u t‖ ^ 2 := by
  let P := cutoff ((inclusion A).restrictScalars ℝ) e he
  have hp : ‖P (u t)‖ ^ 2 ≤ ‖u t‖ ^ 2 := by
    have h := cutoff_norm_le ((inclusion A).restrictScalars ℝ) e he (u t)
    nlinarith [norm_nonneg (P (u t)), norm_nonneg (u t)]
  have hh := S.upper t ht (P (u t))
  have hb := comparisonEnergy_bound A S.B S.domain (u t)
  have hc := S.constant_pos.le
  dsimp [modifiedEnergy, cutoffEnergy, finiteBound]
  nlinarith

/-- Precise lower bound. The difference between uncut and cut B energies
has not been silently declared nonnegative. -/
theorem modified_energy_lower (e : ℝ) (he : 0 < e) (u : ℝ → FormDomain A)
    (t : ℝ) (ht : t ∈ Icc a b) :
    let w := cutoff ((inclusion A).restrictScalars ℝ) e he (u t)
    S.C⁻¹ * ‖w‖ ^ 2 + S.C *
      (comparisonEnergy A S.B S.domain (u t) - comparisonEnergy A S.B S.domain w) ≤
        modifiedEnergy A a b S e he u t := by
  dsimp only [modifiedEnergy, cutoffEnergy]
  linarith [S.lower t ht (cutoff ((inclusion A).restrictScalars ℝ) e he (u t))]

/-- Exact derivative of B's actual form, derived from its completed
comparison embedding and the actual regularized ODE. -/
theorem comparison_energy_derivative (e : ℝ) (he : 0 < e) (u : ℝ → FormDomain A)
    (t : ℝ) (ht : t ∈ Icc a b)
    (hu : HasDerivAt u
      (generator ((inclusion A).restrictScalars ℝ) e he
        (forceMap (formOperator (sourceForm A a b S t))) (u t)) t) :
    let K := comparison A (plusOne S.B) S.domain
    let g := generator ((inclusion A).restrictScalars ℝ) e he
      (forceMap (formOperator (sourceForm A a b S t))) (u t)
    HasDerivAt (fun r => comparisonEnergy A S.B S.domain (u r))
      (2 * (⟪K (u t), K g⟫_ℂ).re) t := by
  let : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
  let : InnerProductSpace ℝ (FormDomain (plusOne S.B)) :=
    InnerProductSpace.rclikeToReal ℂ (FormDomain (plusOne S.B))
  let K := comparison A (plusOne S.B) S.domain
  let i := (inclusion A).restrictScalars ℝ
  let L := formOperator (sourceForm A a b S t)
  let g := generator i e he (forceMap L) (u t)
  have hk := ((K.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu).norm_sq
  have hi := (i.hasFDerivAt.comp_hasDerivAt t hu).norm_sq
  have hz : ⟪i (u t), i g⟫_ℝ = 0 := by
    rw [generator_pair]
    exact force_diagonal L (form_symmetric _ (sourceForm_symmetric A a b S t ht)) _
  change HasDerivAt (fun r => ‖K (u r)‖ ^ 2 - ‖inclusion A (u r)‖ ^ 2)
    (2 * (⟪K (u t), K g⟫_ℂ).re) t
  have h := hk.sub hi
  change HasDerivAt (fun r => ‖K (u r)‖ ^ 2 - ‖inclusion A (u r)‖ ^ 2)
    (2 * (⟪K (u t), K g⟫_ℂ).re - 2 * ⟪i (u t), i g⟫_ℝ) t at h
  simpa only [hz, mul_zero, sub_zero] using h

/-- Exact modified-energy derivative; the remaining comparison term is
visible, rather than supplied as a desired Gronwall conclusion. -/
theorem modified_energy_derivative (e : ℝ) (he : 0 < e) (u : ℝ → FormDomain A)
    (t : ℝ) (ht : t ∈ Icc a b)
    (hu : HasDerivAt u
      (generator ((inclusion A).restrictScalars ℝ) e he
        (forceMap (formOperator (sourceForm A a b S t))) (u t)) t) :
    let K := comparison A (plusOne S.B) S.domain
    let w := cutoff ((inclusion A).restrictScalars ℝ) e he (u t)
    let g := generator ((inclusion A).restrictScalars ℝ) e he
      (forceMap (formOperator (sourceForm A a b S t))) (u t)
    HasDerivWithinAt (modifiedEnergy A a b S e he u)
      (S.diagonalDerivative t w + S.C * (2 * (⟪K (u t), K g⟫_ℂ).re))
      (Icc a b) t := by
  exact (cutoff_energy_derivative A a b S e he u t ht hu).add
    ((comparison_energy_derivative A a b S e he u t ht hu).const_mul S.C).hasDerivWithinAt

end QuantumNLS.Ext005ComparisonEnergyR34b
#print axioms QuantumNLS.Ext005ComparisonEnergyR34b.modified_energy_upper
#print axioms QuantumNLS.Ext005ComparisonEnergyR34b.modified_energy_derivative

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ComparisonEnergyR34b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ComparisonEnergyR34b." then
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
