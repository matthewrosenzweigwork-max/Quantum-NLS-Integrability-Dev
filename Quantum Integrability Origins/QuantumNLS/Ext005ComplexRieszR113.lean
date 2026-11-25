import QuantumNLS.Ext005AntidualR113

/-! Construct the complex-linear Riesz representation of actual continuous
sesquilinear forms, then prove symmetry and the Schrodinger-force pairing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005ComplexRieszR113
open Ext005AntidualR113 Ext005ComplexForceR113
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
local instance : InnerProductSpace ℝ Q := InnerProductSpace.rclikeToReal ℂ Q

lemma coordinates_complex_pair (f : Antidual Q) (v : Q) :
    ⟪v, coordinates f⟫_ℂ = f v :=
  congrArg (fun k : Antidual Q => k v) (antidual_riesz f)

/-- The inverse complex Riesz map on continuous antilinear functionals. -/
def complexRiesz : Antidual Q →L[ℂ] Q :=
  LinearMap.mkContinuous
    { toFun := coordinates
      map_add' := coordinates.map_add
      map_smul' := by
        intro c f
        apply ext_inner_left ℂ
        intro v
        rw [coordinates_complex_pair, inner_smul_right, coordinates_complex_pair]
        rfl }
    1 (by
      intro f
      change ‖coordinates f‖ ≤ 1 * ‖f‖
      rw [coordinates_norm, one_mul])

abbrev Form (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] :=
  Q →L[ℂ] Antidual Q

def formOperator (b : Form Q) : Q →L[ℂ] Q := complexRiesz.comp b

lemma form_pair (b : Form Q) (u v : Q) : ⟪v, formOperator b u⟫_ℂ = b u v :=
  coordinates_complex_pair (b u) v

lemma form_symmetric (b : Form Q)
    (hs : ∀ u v : Q, starRingEnd ℂ (b u v) = b v u) : (formOperator b).IsSymmetric := by
  intro u v
  calc
    ⟪formOperator b u, v⟫_ℂ = starRingEnd ℂ (b u v) := by
      rw [← inner_conj_symm, form_pair]
    _ = b v u := hs u v
    _ = ⟪u, formOperator b v⟫_ℂ := (form_pair b v u).symm

lemma form_force_coordinates (b : Form Q) (u : Q) :
    coordinates ((-Complex.I) • b u) = forceMap (formOperator b) u := by
  apply ext_inner_left ℝ
  intro v
  rw [coordinates_pair, force_pair, form_pair]
  simp [Complex.mul_re]

end QuantumNLS.Ext005ComplexRieszR113
#print axioms QuantumNLS.Ext005ComplexRieszR113.form_symmetric
#print axioms QuantumNLS.Ext005ComplexRieszR113.form_force_coordinates

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ComplexRieszR113." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ComplexRieszR113." then
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
