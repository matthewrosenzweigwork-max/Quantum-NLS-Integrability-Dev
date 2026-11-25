import QuantumNLS.Ext005PhysicalStaticR121
import Mathlib.Topology.Instances.RealVectorSpace

/-! The physical scalar time derivative, obtained by applying a constructed
continuous real linear functional to the proved C1 coefficient trajectory. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 50000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap
namespace QuantumNLS.Ext005PhysicalTimeR121
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005MomentDomainR33b Ext005OperatorFormR113 Ext005PhysicalStaticR121
open Ext005PhysicalNumberFormR114 Ext005PhysicalSymmetryR114 Prop022FormContinuityR119
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
open Prop022ActualProfileR117 Prop022CoefficientTimeR117
variable {L : ℝ} [Fact (0 < L)]

local instance (priority := 1200) opNormed : NormedAddCommGroup (HN L 1 →L[ℂ] HN L 1) :=
  inferInstance
local instance (priority := 1200) opGroup : AddCommGroup (HN L 1 →L[ℂ] HN L 1) :=
  (opNormed (L := L)).toAddCommGroup
local instance (priority := 1200) opTopology : TopologicalSpace (HN L 1 →L[ℂ] HN L 1) :=
  (opNormed (L := L)).toUniformSpace.toTopologicalSpace
local instance (priority := 1200) opRealNS : NormedSpace ℝ (HN L 1 →L[ℂ] HN L 1) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance (priority := 1200) opRealModule : Module ℝ (HN L 1 →L[ℂ] HN L 1) :=
  (opRealNS (L := L)).toModule
local instance (priority := 1200) opRealSMul : SMul ℝ (HN L 1 →L[ℂ] HN L 1) :=
  (opRealNS (L := L)).toSMul
local instance : NormedSpace ℝ (HN L 2) := NormedSpace.restrictScalars ℝ ℂ _

abbrev Coefficients (L : ℝ) [Fact (0 < L)] :=
  (HN L 1 →L[ℂ] HN L 1) × HN L 2

def diagonal (w : Fock L) (c : Coefficients L) : ℝ :=
  (quadraticContinuous c.1 c.2 w w).re

lemma diagonal_sub (w : Fock L) (c d : Coefficients L) :
    diagonal w (c-d) = diagonal w c - diagonal w d := by
  change (quadraticContinuous (c.1-d.1) (c.2-d.2) w w).re = _
  rw [quadraticContinuous_sub]
  rfl

lemma diagonal_zero (w : Fock L) : diagonal w (0 : Coefficients L) = 0 := by
  simpa only [sub_self] using diagonal_sub w (0 : Coefficients L) 0

def diagonalAdd (w : Fock L) : Coefficients L →+ ℝ where
  toFun := diagonal w
  map_zero' := diagonal_zero w
  map_add' c d := by
    have h := diagonal_sub w (c+d) d
    rw [add_sub_cancel_right] at h
    linarith

lemma diagonal_bound (w : Fock L) (c : Coefficients L) :
    |diagonal w c| ≤ (‖c.1‖ + ‖c.2‖) * ‖w‖ ^ 2 :=
  (Complex.abs_re_le_norm _).trans (quadraticContinuous_diagonal_bound _ _ w)

def diagonalMap (w : Fock L) : Coefficients L →L[ℝ] ℝ :=
  (diagonalAdd w).toRealLinearMap (AddMonoidHomClass.continuous_of_bound
    (diagonalAdd w) (2 * ‖w‖ ^ 2) (fun c => by
      change |diagonal w c| ≤ _
      apply (diagonal_bound w c).trans
      have ha := _root_.norm_fst_le c
      have hb := _root_.norm_snd_le c
      nlinarith [sq_nonneg ‖w‖]))

/-- Explicit finite bound for both actual coefficient derivatives. -/
def derivativeMajorant (M A : ℝ) : ℝ :=
  (2 * (M * ∑' n, weight 1 A (n+1)) * M) *
    ((∑' r, weight 3 A (r+1)) + ∑' r, weight 3 A (r+2))

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
local notation "a" => (fun t => numberCoefficient B (profile B M A hA hB hs u₀ t))
local notation "b" => (fun t => pairCoefficient B (profile B M A hA hB hs u₀ t))

def diagonalDerivative (j : ℕ) (hj : 1 ≤ j) (t : ℝ)
    (u : FormDomain (momentPositive (L := L) j)) : ℝ :=
  diagonalMap (firstRoot j hj u) (deriv a t, deriv b t)

include hM in
lemma actual_derivative (j : ℕ) (hj : 1 ≤ j)
    (u : FormDomain (momentPositive (L := L) j)) (t : ℝ) :
    HasDerivAt (fun s => (physicalForm j hj (a s) (b s) u u).re)
      (diagonalDerivative B M A hA hB hs u₀ j hj t u) t := by
  have h := actual_coefficients_C1 B M A hM hA hB hs u₀
  have ha : HasDerivAt a (deriv a t) t :=
    (h.1.differentiable (by norm_num) t).hasDerivAt
  have hb : HasDerivAt b (deriv b t) t :=
    (h.2.1.differentiable (by norm_num) t).hasDerivAt
  have hc : HasDerivAt (fun r : ℝ => (a r, b r)) (deriv a t, deriv b t) t := ha.prodMk hb
  change HasDerivAt (fun r => diagonalMap (firstRoot j hj u) (a r, b r))
    (diagonalMap (firstRoot j hj u) (deriv a t, deriv b t)) t
  exact (diagonalMap (firstRoot j hj u)).hasFDerivAt.comp_hasDerivAt t hc

include hM in
lemma actual_derivative_bound (j : ℕ) (hj : 1 ≤ j)
    (u : FormDomain (momentPositive (L := L) j)) (t : ℝ) :
    |diagonalDerivative B M A hA hB hs u₀ j hj t u| ≤ derivativeMajorant M A * ‖u‖ ^ 2 := by
  have h := actual_coefficients_C1 B M A hM hA hB hs u₀
  have hb : ‖deriv a t‖ + ‖deriv b t‖ ≤ derivativeMajorant M A := by
    have h1 := h.2.2.2.2.1 t
    have h2 := h.2.2.2.2.2 t
    simpa only [derivativeMajorant, mul_add] using add_le_add h1 h2
  have hpos : 0 ≤ derivativeMajorant M A :=
    (add_nonneg (norm_nonneg (deriv a t)) (norm_nonneg (deriv b t))).trans hb
  change |diagonal (firstRoot j hj u) (deriv a t, deriv b t)| ≤ _
  apply (diagonal_bound (firstRoot j hj u) _).trans
  calc
    _ ≤ derivativeMajorant M A * ‖firstRoot j hj u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (firstRoot_bound j hj u) 2) hpos

end QuantumNLS.Ext005PhysicalTimeR121
#print axioms QuantumNLS.Ext005PhysicalTimeR121.actual_derivative
#print axioms QuantumNLS.Ext005PhysicalTimeR121.actual_derivative_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalTimeR121." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalTimeR121." then
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
  Lean.logInfo m!"R121 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
