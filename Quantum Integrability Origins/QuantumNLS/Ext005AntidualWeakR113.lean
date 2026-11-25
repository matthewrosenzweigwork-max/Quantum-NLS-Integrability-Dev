import QuantumNLS.Ext005ComplexRieszR113

/-! Native weak equations in the actual complex antidual, and their exact
real-coordinate equivalence. Real tests against all complex vectors also
recover the imaginary scalar distributional equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005AntidualWeakR113
open Ext005AntidualR113 Ext005ComplexRieszR113 Ext005ComplexForceR113
open Ext005IntervalChainR111
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ Q := InnerProductSpace.rclikeToReal ℂ Q
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- The antidual distributional equation, using real time tests.
Testing every complex v encodes both real and imaginary components. -/
def AntidualWeakOn (U : Set ℝ) (f g : ℝ → Antidual Q) : Prop :=
  ∀ (v : Q) (p : ℝ → ℝ), ContDiff ℝ ∞ p → HasCompactSupport p → tsupport p ⊆ U →
    ∫ t, deriv p t * (f t v).re = -(∫ t, p t * (g t v).re)

omit [CompleteSpace Q] in
lemma weak_imag {U : Set ℝ} {f g : ℝ → Antidual Q} (hw : AntidualWeakOn U f g)
    (v : Q) (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hc : HasCompactSupport p)
    (hs : tsupport p ⊆ U) :
    ∫ t, deriv p t * (f t v).im = -(∫ t, p t * (g t v).im) := by
  simpa [Complex.mul_re] using hw (Complex.I • v) p hp hc hs

/-- The actual antidual equation and the R112 weak equation are equivalent. -/
lemma weak_coordinates_iff (U : Set ℝ) (f g : ℝ → Antidual Q) :
    AntidualWeakOn U f g ↔
      WeakDerivativeOn U (fun t => coordinates (f t)) (fun t => coordinates (g t)) := by
  constructor <;> intro h v p hp hc hs <;>
    simpa only [coordinates_pair] using h v p hp hc hs

/-- The ambient antidual embedding is the actual complex pairing against i(v). -/
def ambient (i : Q →L[ℂ] H) : H →L[ℂ] Antidual Q :=
  (innerSLFlip ℂ).comp i.adjoint

lemma ambient_apply (i : Q →L[ℂ] H) (x : H) (v : Q) :
    ambient i x v = ⟪i v, x⟫_ℂ := i.adjoint_inner_right v x

lemma ambient_coordinates (i : Q →L[ℂ] H) (x : H) :
    coordinates (ambient i x) = (i.restrictScalars ℝ).adjoint x := by
  apply ext_inner_left ℝ
  intro v
  rw [coordinates_pair, ambient_apply, ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- Exact weak-equation bridge for the Schrodinger sign x'=-i H(t)x.
No integral equation, norm identity or uniqueness conclusion is a premise. -/
theorem schrodinger_weak_iff (U : Set ℝ) (i : Q →L[ℂ] H)
    (b : ℝ → Form Q) (x : ℝ → H) (u : ℝ → Q) :
    AntidualWeakOn U (fun t => ambient i (x t)) (fun t => (-Complex.I) • b t (u t)) ↔
      WeakDerivativeOn U (fun t => (i.restrictScalars ℝ).adjoint (x t))
        (fun t => forceMap (formOperator (b t)) (u t)) := by
  rw [weak_coordinates_iff]
  simp only [ambient_coordinates, form_force_coordinates]

end QuantumNLS.Ext005AntidualWeakR113
#print axioms QuantumNLS.Ext005AntidualWeakR113.weak_imag
#print axioms QuantumNLS.Ext005AntidualWeakR113.schrodinger_weak_iff

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005AntidualWeakR113." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005AntidualWeakR113." then
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
