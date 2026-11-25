import QuantumNLS.Ext025B3PhysicalSectors
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
EXT-006 / FIN-CORE-BD-02, phase clause only.  Author: sol_multi.
The carrier is the repository's completed physical bosonic Fock space.
All number weights are allowed, including unbounded weights; expectations
take values in ENNReal.  This file does not assert the squeezed-vacuum
existence, determinant normalization, or diagonalization clauses.
-/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006NumberPhase
open Ext025B3PhysicalSectors
variable {L : ℝ} [Fact (0 < L)]

/-- Spectral expectation of a nonnegative function of the full number operator.
The value may be infinite, so phase invariance has no moment-domain premise. -/
def numberExpectation (w : ℕ → ℝ≥0∞) (x : Fock L) : ℝ≥0∞ :=
  ∑' n, w n * ENNReal.ofReal (‖x n‖ ^ 2)

theorem sector_norm_phase (c : ℂ) (hc : ‖c‖ = 1) (x : Fock L) (n : ℕ) :
    ‖(c • x) n‖ = ‖x n‖ := by
  change ‖c • x n‖ = _
  rw [norm_smul, hc, one_mul]

/-- Literal phase-independence clause of FIN-CORE-BD-02, for every nonnegative
spectral number observable on the actual physical Fock space. -/
theorem «FIN-CORE-BD-02-phase» (c : ℂ) (hc : ‖c‖ = 1)
    (x : Fock L) (w : ℕ → ℝ≥0∞) :
    numberExpectation w (c • x) = numberExpectation w x := by
  unfold numberExpectation
  simp only [sector_norm_phase c hc]

/-- Domain preservation for any maximal direct sum of bounded sector maps.
In particular this applies to all powers/functions of particle number. -/
theorem blockDomain_phase_iff
    (A : ∀ n, BetheCoefficientTransform.HN L n →L[ℂ] BetheCoefficientTransform.HN L n)
    (c : ℂ) (hc : ‖c‖ = 1) (x : Fock L) :
    c • x ∈ (block A).domain ↔ x ∈ (block A).domain := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  constructor
  · intro h
    have hh := (block A).domain.smul_mem c⁻¹ h
    simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using hh
  · exact (block A).domain.smul_mem c

/-- Equality of the actual unbounded block-operator norms, with both domains
constructed from the same maximal domain. -/
theorem block_norm_phase
    (A : ∀ n, BetheCoefficientTransform.HN L n →L[ℂ] BetheCoefficientTransform.HN L n)
    (c : ℂ) (hc : ‖c‖ = 1) (x : (block A).domain) :
    ‖block A ⟨c • x.val, (block A).domain.smul_mem c x.property⟩‖ = ‖block A x‖ := by
  have he : block A ⟨c • x.val, (block A).domain.smul_mem c x.property⟩ =
      c • block A x := by
    apply lp.ext
    funext n
    change A n (c • x.val n) = c • A n (x.val n)
    exact map_smul _ _ _
  rw [he, norm_smul, hc, one_mul]

/-- The exact exponential weight used in PROP-023. -/
def exponentialMoment (Q : ℝ) (x : Fock L) : ℝ≥0∞ :=
  numberExpectation (fun n => ENNReal.ofReal (Real.exp ((n : ℝ) / (16 * Q)))) x

/-- Squared norm of (N+j)^(j/2) as a nonnegative spectral series.
Finiteness is the form-domain condition; it is not assumed here. -/
def polynomialMoment (j : ℕ) (x : Fock L) : ℝ≥0∞ :=
  numberExpectation (fun n => ENNReal.ofReal (((n : ℝ) + j) ^ j)) x

/-- The literal spectral multiplier (N+j)^(j/2) from PROP-023. -/
def polynomialRootFamily (j n : ℕ) :
    BetheCoefficientTransform.HN L n →L[ℂ] BetheCoefficientTransform.HN L n :=
  ((Real.rpow ((n : ℝ)+j) ((j : ℝ)/2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ _

def polynomialRoot (j : ℕ) : Fock L →ₗ.[ℂ] Fock L :=
  block (polynomialRootFamily (L := L) j)

/-- Exact preservation of the norm in the second displayed PROP-023 bound. -/
theorem polynomialRoot_norm_phase (j : ℕ) (c : ℂ) (hc : ‖c‖ = 1)
    (x : (polynomialRoot (L := L) j).domain) :
    ‖polynomialRoot j ⟨c • x.val, (polynomialRoot j).domain.smul_mem c x.property⟩‖ =
      ‖polynomialRoot j x‖ :=
  block_norm_phase (polynomialRootFamily j) c hc x

/-- PROP-023's precise phase-removal wrapper.  It transports BOTH displayed
moment inequalities, with their constants unchanged, as equivalences.
No squeezed-state representation or moment bound is supplied as a premise. -/
theorem «PROP-023-phase-wrapper» (c : ℂ) (hc : ‖c‖ = 1)
    (x : Fock L) (Q : ℝ) (j : ℕ) :
    (exponentialMoment Q (c • x) ≤ ENNReal.ofReal (Real.exp (1/4 : ℝ)) ∧
      polynomialMoment j (c • x) ≤ ENNReal.ofReal ((32 * Q * j) ^ j)) ↔
    (exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1/4 : ℝ)) ∧
      polynomialMoment j x ≤ ENNReal.ofReal ((32 * Q * j) ^ j)) := by
  simp only [exponentialMoment, polynomialMoment, «FIN-CORE-BD-02-phase» c hc]

/-- The report's expected-number hypothesis is itself phase independent. -/
theorem expectedNumber_phase (c : ℂ) (hc : ‖c‖ = 1) (x : Fock L) :
    numberExpectation (fun n => n) (c • x) = numberExpectation (fun n => n) x :=
  «FIN-CORE-BD-02-phase» c hc x _

/-- PROP-023's two displayed bounds in their original expectation/norm form.
Only the phase-removal operation is proved; neither bound is presumed true. -/
theorem «PROP-023-phase-norm-wrapper» (c : ℂ) (hc : ‖c‖ = 1)
    (Q : ℝ) (j : ℕ) (x : (polynomialRoot (L := L) j).domain) :
    (exponentialMoment Q (c • x.val) ≤ ENNReal.ofReal (Real.exp (1/4 : ℝ)) ∧
      ‖polynomialRoot j ⟨c • x.val, (polynomialRoot j).domain.smul_mem c x.property⟩‖ ≤
        Real.rpow (32 * Q * j) ((j : ℝ)/2)) ↔
    (exponentialMoment Q x.val ≤ ENNReal.ofReal (Real.exp (1/4 : ℝ)) ∧
      ‖polynomialRoot j x‖ ≤ Real.rpow (32 * Q * j) ((j : ℝ)/2)) := by
  rw [polynomialRoot_norm_phase j c hc]
  simp only [exponentialMoment, «FIN-CORE-BD-02-phase» c hc]

end QuantumNLS.Ext006NumberPhase

#print axioms QuantumNLS.Ext006NumberPhase.«FIN-CORE-BD-02-phase»
#print axioms QuantumNLS.Ext006NumberPhase.blockDomain_phase_iff
#print axioms QuantumNLS.Ext006NumberPhase.block_norm_phase
#print axioms QuantumNLS.Ext006NumberPhase.«PROP-023-phase-wrapper»

-- COMPLETE NAMESPACE AUDIT
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006NumberPhase." then
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
  Lean.logInfo m!"Ext006NumberPhase audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
