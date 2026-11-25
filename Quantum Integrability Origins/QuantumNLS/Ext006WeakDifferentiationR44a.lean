import QuantumNLS.Ext006ExponentialDerivativeR43a
import QuantumNLS.Ext006ExponentialGraphR43a
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Weak differentiation of bounded exponential commutation. The bounded
operator is arbitrary and no invariance of an unbounded domain is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006WeakDifferentiationR44a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006BoundedExponentialR43a
open Ext006SeriesIdentificationR43a Ext006ExponentialDerivativeR43a
open Ext006IdentityCyclicR35a

def CommutesExponential (T : Fock →L[ℂ] Fock) : Prop :=
  ∀ (h : H) (t : ℝ) (x : Fock), T (unitary h t x) = unitary h t (T x)

/-- Differentiation at zero is valid even if T sends a core vector outside
all known field domains. It gives a weak identity, not domain invariance. -/
theorem commutes_field_weak (T : Fock →L[ℂ] Fock) (hT : CommutesExponential T)
    {N M : ℕ} (h : H) (v w : D)
    (hv : ParticleBound N v.1) (hw : ParticleBound M w.1) :
    inner ℂ (field h v).1 (T w.1) = inner ℂ v.1 (T (field h w).1) := by
  have hdv := (unitary_hasDerivAt h v hv (-(0 : ℝ))).scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hdw := (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (unitary_hasDerivAt h w hw 0)
  have dl := hdv.inner ℂ (hasDerivAt_const 0 (T w.1))
  have dr := (hasDerivAt_const 0 v.1).inner ℂ hdw
  have he : (fun t : ℝ => inner ℂ (unitary h (-t) v.1) (T w.1)) =
      (fun t : ℝ => inner ℂ v.1 (T (unitary h t w.1))) := by
    funext t
    rw [hT h t w.1]
    exact (evolution_adjoint h t v.1 (T w.1)).symm
  have de := dl.unique (he ▸ dr)
  simp only [neg_zero,unitary_zero,inner_zero_left,inner_zero_right,zero_add,add_zero,
    neg_one_smul] at de
  change inner ℂ (-(Complex.I • (field h v).1)) (T w.1) =
    inner ℂ v.1 (T (Complex.I • (field h w).1)) at de
  simp only [inner_neg_left,inner_smul_left,map_smul,inner_smul_right,
    Complex.conj_I,neg_mul,neg_neg] at de
  exact mul_left_cancel₀ Complex.I_ne_zero de


end QuantumNLS.Ext006WeakDifferentiationR44a
#print axioms QuantumNLS.Ext006WeakDifferentiationR44a.commutes_field_weak

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006WeakDifferentiationR44a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Round44a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
