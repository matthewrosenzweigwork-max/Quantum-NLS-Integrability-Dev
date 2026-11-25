import QuantumNLS.Def021ChartR41b
import QuantumNLS.RootScalarUniquenessR28
import QuantumNLS.Q07IntegratedHessiansR16
import QuantumNLS.WindowPhaseR44b
import QuantumNLS.Reg015Setting

open scoped NNReal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

/-! R-E59628C9: the actual window contour Hamiltonian depends only on all
indexed actions of the accepted chart. This is a proved consequence of the
accepted scalar uniqueness theorem, including zero actions. No regular-cut
or sector-changing monodromy assertion is used by this argument. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Reg015Setting QuantumNLS.WindowPhaseR44b
namespace QuantumNLS.WindowActionInvariantR44b
variable {L κ : ℝ} [Fact (0 < L)]

/-- The whole scalar measure, not just its total mass, is fixed on a
modulus torus of the actual accepted chart. -/
theorem measure_of_moduli (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (x y : Seq) (h : ∀ n, ‖x n‖ = ‖y n‖) :
    PhysicalQuantumMeasure.measure hκ (C.Ψ x) = PhysicalQuantumMeasure.measure hκ (C.Ψ y) := by
  apply (RootScalarUniquenessR28.root_scalar_uniqueness hκ).1
  intro n
  rw [← C.actions,← C.actions,C.right_inverse,C.right_inverse,h n]

/-- The printed full-mass logarithm is identical on equal action fibres. -/
theorem logarithm_of_moduli (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (x y : Seq) (h : ∀ n, ‖x n‖ = ‖y n‖) (ξ : ℂ) :
    Q07LogDifferentialsR16.logarithm hκ ξ (C.Ψ x) =
      Q07LogDifferentialsR16.logarithm hκ ξ (C.Ψ y) := by
  unfold Q07LogDifferentialsR16.logarithm RootCauchyFullBracketR8.G
  rw [measure_of_moduli hκ C x y h]

/-- The actual contour functional has the same full-action invariance. -/
theorem contour_of_moduli (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (x y : Seq) (h : ∀ n, ‖x n‖ = ‖y n‖) (r : ℕ) (a b : ℝ) :
    Q07IntegratedHessiansR16.windowContour hκ r a b (C.Ψ x) =
      Q07IntegratedHessiansR16.windowContour hκ r a b (C.Ψ y) := by
  unfold Q07IntegratedHessiansR16.windowContour
  congr 1
  funext ξ
  rw [logarithm_of_moduli hκ C x y h ξ]

/-- Every coordinate rotation, with zero coordinates retained, preserves
the window Hamiltonian in h^s for all fixed s>=0. -/
theorem contour_rotation (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (s : ℝ) (hs : 0 ≤ s) (z : h02 L s) (α : ℤ → ℝ)
    (r : ℕ) (a b : ℝ) :
    Q07IntegratedHessiansR16.windowContour hκ r a b (C.Ψ (toBase s hs (rotate α z))) =
      Q07IntegratedHessiansR16.windowContour hκ r a b (C.Ψ (toBase s hs z)) := by
  apply contour_of_moduli hκ C _ _ _ r a b
  intro n
  rw [toBase_apply,toBase_apply,rotate_val,norm_mul,Circle.norm_coe,one_mul]

end QuantumNLS.WindowActionInvariantR44b

#print axioms QuantumNLS.WindowActionInvariantR44b.measure_of_moduli
#print axioms QuantumNLS.WindowActionInvariantR44b.contour_rotation

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowActionInvariantR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowActionInvariantR44b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"R44b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
