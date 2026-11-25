import QuantumNLS.Ext005AssociatedOperatorR113
import QuantumNLS.Ext005AntidualWeakR113
import QuantumNLS.Ext005TimeFormR113

/-! D3 uniqueness on the constructed operator form/antidual scale, for
continuous complex forms with the scalar source time-derivative estimate.
The energy-bounded solution class is exactly norm continuity, local essential
Q(A) bounds and the weak equation. Literal source hypotheses still have to
supply continuous representability of their quadratic forms; no source-node
closure, existence or application estimates are claimed by this theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005OperatorD3R113
open Ext005OperatorFormR113 Ext005ComplexRieszR113 Ext005ComplexForceR113
open Ext005AntidualWeakR113 Ext005TimeFormR113 Ext005HilbertEnergyR112
open Ext005HilbertD3R112
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- D3's three requirements on a competitor. In particular, pointwise domain
preservation alone is not used as a substitute for the essential energy bound. -/
def EnergyWeakSolution (S : PositiveOperator H) (b : ℝ → Form (FormDomain S))
    (x : ℝ → H) : Prop :=
  letI : InnerProductSpace ℝ (FormDomain S) := InnerProductSpace.rclikeToReal ℂ (FormDomain S)
  let i := (inclusion S).restrictScalars ℝ
  ContinuousOn x (Ico 0 1) ∧
    (∀ T ∈ Ioo (0 : ℝ) 1, EnergyBounded i (Icc 0 T) x) ∧
    AntidualWeakOn (Ioo 0 1) (fun t => ambient (inclusion S) (x t))
      (fun t => (-Complex.I) • b t (lift i (x t)))

/-- EXT-005/D3 uniqueness for continuous symmetric forms on the constructed
Q(A). All force conditions are derived from symmetry and the scalar derivative
estimate; none is an assumed uniqueness or energy-identity conclusion. -/
theorem EXT005_D3_continuous_form_unique (S : PositiveOperator H)
    (b : ℝ → Form (FormDomain S)) (d : ℝ → FormDomain S → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hsym : ∀ t ∈ Ico (0 : ℝ) 1, ∀ u v : FormDomain S,
      starRingEnd ℂ (b t u v) = b t v u)
    (hd : ∀ u t, t ∈ Ico (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => (b s u u).re) (d t u) (Ico 0 1) t)
    (hdb : ∀ u t, t ∈ Ico (0 : ℝ) 1 → |d t u| ≤ C * ‖u‖ ^ 2)
    (x y : ℝ → H) (hx : EnergyWeakSolution S b x) (hy : EnergyWeakSolution S b y)
    (hinit : x 0 = y 0) : ∀ t ∈ Ico (0 : ℝ) 1, x t = y t := by
  let : InnerProductSpace ℝ (FormDomain S) := InnerProductSpace.rclikeToReal ℂ (FormDomain S)
  let i := (inclusion S).restrictScalars ℝ
  let L := fun t => formOperator (b t)
  have hsymL : ∀ t ∈ Ico (0 : ℝ) 1, (L t).IsSymmetric :=
    fun t ht => form_symmetric (b t) (hsym t ht)
  have hdL : ∀ u t, t ∈ Ico (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => (⟪u, L s u⟫_ℂ).re) (d t u) (Ico 0 1) t := by
    intro u t ht
    simpa only [L, form_pair] using hd u t ht
  obtain ⟨hLm, hLb⟩ := time_coefficient_hypotheses L d C hC hsymL hdL hdb
  rcases hx with ⟨hxc, hxe, hxw⟩
  rcases hy with ⟨hyc, hye, hyw⟩
  apply energy_unique_source_interval i (inclusion_injective S) (inclusion_dense S)
    x y (fun t => forceMap (L t)) hxc hyc hxe hye (force_measurable L _ hLm)
  · intro T hT
    obtain ⟨M, hM, hb⟩ := hLb T hT
    exact ⟨M, hM, force_local_bound L (Icc 0 T) M hb⟩
  · exact Filter.Eventually.of_forall fun t ht u => force_diagonal (L t) (hsymL t ht) u
  · exact (schrodinger_weak_iff (Ioo 0 1) (inclusion S) b x (fun t => lift i (x t))).mp hxw
  · exact (schrodinger_weak_iff (Ioo 0 1) (inclusion S) b y (fun t => lift i (y t))).mp hyw
  · exact hinit

end QuantumNLS.Ext005OperatorD3R113
#print axioms QuantumNLS.Ext005OperatorD3R113.EXT005_D3_continuous_form_unique

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005OperatorD3R113." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005OperatorD3R113." then
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
  Lean.logInfo m!"R113 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
