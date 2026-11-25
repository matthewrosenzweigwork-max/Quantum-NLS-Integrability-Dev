import QuantumNLS.Ext025B6PVM
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! GP-08: bounded commuting operators preserve the arbitrary-PVM form
integral; commuting isometries preserve the full scalar spectral measure.
This derives the common-resolution form law directly from the defining PVM
laws. Construction of an operator B from an arbitrary Borel symbol remains
separate; no spectral representation is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped ENNReal
namespace QuantumNLS.Ext025B7PVMForms
open BetheChargeResolution Ext025B6PVM
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

def Commutes (B : E →L[ℂ] E) : Prop := ∀ s, MeasurableSet s → Commute B (P.toFun s)

def energy (w : ℝ → ℝ≥0∞) (x : E) : ℝ≥0∞ := ∫⁻ t, w t ∂scalarMeasure P x

def FormDomain (w : ℝ → ℝ≥0∞) (x : E) : Prop := energy P w x ≠ ⊤

/-- The measure estimate is derived on every measurable spectral set. -/
theorem scalarMeasure_bounded (B : E →L[ℂ] E) (hB : Commutes P B) (x : E) :
    scalarMeasure P (B x) ≤ ENNReal.ofReal (‖B‖^2) • scalarMeasure P x := by
  apply Measure.le_iff.mpr
  intro s hs
  have he : P.toFun s (B x) = B (P.toFun s x) :=
    (congrArg (fun T : E →L[ℂ] E => T x) (hB s hs).eq).symm
  rw [scalarMeasure_apply P (B x) s hs,he,Measure.smul_apply,
    scalarMeasure_apply P x s hs,smul_eq_mul,
    ← ENNReal.ofReal_mul (sq_nonneg _),← mul_pow]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2)

/-- No unbounded form preservation is asserted: B is a bounded operator. -/
theorem bounded_energy (B : E →L[ℂ] E) (hB : Commutes P B) (w : ℝ → ℝ≥0∞) (x : E) :
    energy P w (B x) ≤ ENNReal.ofReal (‖B‖^2) * energy P w x := by
  have h := lintegral_mono' (scalarMeasure_bounded P B hB x) (le_refl w)
  simpa only [energy,lintegral_smul_measure,smul_eq_mul] using h

theorem bounded_form_domain (B : E →L[ℂ] E) (hB : Commutes P B) (w : ℝ → ℝ≥0∞)
    (x : E) (hx : FormDomain P w x) : FormDomain P w (B x) := by
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx)
    (bounded_energy P B hB w x)

/-- A commuting linear isometry preserves the actual scalar spectral measure,
including every finite or infinite spectral moment. Surjectivity is unnecessary. -/
theorem scalarMeasure_isometry (U : E →ₗᵢ[ℂ] E)
    (hU : ∀ s, MeasurableSet s → ∀ x, U (P.toFun s x) = P.toFun s (U x)) (x : E) :
    scalarMeasure P (U x) = scalarMeasure P x := by
  apply Measure.ext
  intro s hs
  rw [scalarMeasure_apply P (U x) s hs,scalarMeasure_apply P x s hs,← hU s hs x,U.norm_map]

theorem isometry_energy (U : E →ₗᵢ[ℂ] E)
    (hU : ∀ s, MeasurableSet s → ∀ x, U (P.toFun s x) = P.toFun s (U x))
    (w : ℝ → ℝ≥0∞) (x : E) : energy P w (U x) = energy P w x := by
  simp only [energy,scalarMeasure_isometry P U hU x]

theorem isometry_domain_iff (U : E →ₗᵢ[ℂ] E)
    (hU : ∀ s, MeasurableSet s → ∀ x, U (P.toFun s x) = P.toFun s (U x))
    (w : ℝ → ℝ≥0∞) (x : E) : FormDomain P w (U x) ↔ FormDomain P w x := by
  simp only [FormDomain,isometry_energy P U hU w x]

/-- Every measurable spectral cutoff is a bounded common-resolution operator. -/
theorem projection_commutes (s : Set ℝ) (hs : MeasurableSet s) : Commutes P (P.toFun s) := by
  intro t ht
  show P.toFun s*P.toFun t = P.toFun t*P.toFun s
  rw [P.inter s t hs ht,P.inter t s ht hs,Set.inter_comm]

theorem projection_form_domain (s : Set ℝ) (hs : MeasurableSet s) (w : ℝ → ℝ≥0∞)
    (x : E) (hx : FormDomain P w x) : FormDomain P w (P.toFun s x) :=
  bounded_form_domain P (P.toFun s) (projection_commutes P s hs) w x hx

end QuantumNLS.Ext025B7PVMForms

#print axioms QuantumNLS.Ext025B7PVMForms.Commutes
#print axioms QuantumNLS.Ext025B7PVMForms.energy
#print axioms QuantumNLS.Ext025B7PVMForms.FormDomain
#print axioms QuantumNLS.Ext025B7PVMForms.scalarMeasure_bounded
#print axioms QuantumNLS.Ext025B7PVMForms.bounded_energy
#print axioms QuantumNLS.Ext025B7PVMForms.bounded_form_domain
#print axioms QuantumNLS.Ext025B7PVMForms.scalarMeasure_isometry
#print axioms QuantumNLS.Ext025B7PVMForms.isometry_energy
#print axioms QuantumNLS.Ext025B7PVMForms.isometry_domain_iff
#print axioms QuantumNLS.Ext025B7PVMForms.projection_commutes
#print axioms QuantumNLS.Ext025B7PVMForms.projection_form_domain

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B7PVMForms." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Ext025B7PVMForms audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
