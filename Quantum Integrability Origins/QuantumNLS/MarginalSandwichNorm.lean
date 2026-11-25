import QuantumNLS.LinearTailKineticError
import QuantumNLS.TensorPlacements

/-! Positive-sandwich errors are the literal vector norms of placed kernels.
Individual placements are kept on the full tensor space before sector compression. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Topology Set
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.MarginalSandwichNorm
open TensorCarrier TensorPlacements TraceClass LinearTailKineticError
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- Naturality of the actual reduced-density definition under a first-factor operator. -/
theorem sandwich_reducedDensity (S : X →L[ℂ] X) (ψ : HilbertTensor ℂ X Y) :
    S * reducedDensity ψ * S.adjoint =
      reducedDensity (htmap S (ContinuousLinearMap.id ℂ Y) ψ) := by
  let A := htmap S (ContinuousLinearMap.id ℂ Y)
  have hi (x y : X) :
      ⟪reducedDensity (A ψ) x, y⟫_ℂ =
        ⟪reducedDensity ψ (S.adjoint x), S.adjoint y⟫_ℂ := by
    have he : (A.adjoint ∘L htmap (InnerProductSpace.rankOne ℂ y x)
        (ContinuousLinearMap.id ℂ Y)) ∘L A =
        htmap (InnerProductSpace.rankOne ℂ (S.adjoint y) (S.adjoint x))
          (ContinuousLinearMap.id ℂ Y) := by
      dsimp [A]
      rw [adjoint_htmap, ContinuousLinearMap.adjoint_id, ← htmap_comp, ← htmap_comp]
      rw [InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp]
      simp
    rw [inner_reducedDensity_left, inner_reducedDensity_left]
    rw [← ContinuousLinearMap.adjoint_inner_right A ψ]
    change ⟪ψ, ((A.adjoint ∘L htmap (InnerProductSpace.rankOne ℂ y x)
      (ContinuousLinearMap.id ℂ Y)) ∘L A) ψ⟫_ℂ = _
    rw [he]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [hi]
  change ⟪S (reducedDensity ψ (S.adjoint x)), y⟫_ℂ =
    ⟪reducedDensity ψ (S.adjoint x), S.adjoint y⟫_ℂ
  exact (ContinuousLinearMap.adjoint_inner_right S _ _).symm

/-- The source quadratic error is exactly the norm of the first-factor action. -/
theorem quadraticError_reducedDensity (S : X →L[ℂ] X) (ψ : HilbertTensor ℂ X Y) :
    quadraticError S (reducedDensity ψ) =
      ‖htmap S (ContinuousLinearMap.id ℂ Y) ψ‖ := by
  unfold quadraticError
  rw [sandwich_reducedDensity, traceNorm_of_isPositive (reducedDensity_isPositive _),
    posTrace, traceIn_reducedDensity, ENNReal.toReal_ofReal (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Exact first-placement interpretation on the actual completed tensor powers. -/
theorem firstPlacement_norm {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)
    (ψ : HilbertTensorPower ℂ H (p + q)) :
    ‖firstPlacement (q := q) A ψ‖ = quadraticError (extendSymKernel A) (reducedDensityPower p q ψ) := by
  rw [reducedDensityPower, quadraticError_reducedDensity]
  simp only [firstPlacement, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.norm_map]

omit [CompleteSpace H] in
/-- Every literal subset placement has that same vector norm on a symmetric state. -/
theorem subsetPlacement_norm {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)
    (ψ : HilbertTensorPower ℂ H (p + q)) (hψ : ψ ∈ SymSector ℂ H (p + q))
    (S : PlacementSubset p q) :
    ‖subsetPlacement S A ψ‖ = quadraticError (extendSymKernel A) (reducedDensityPower p q ψ) := by
  rw [← firstPlacement_norm A ψ]
  change ‖(permRep ℂ H (p + q) (subsetRepresentative S) : HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q))
    (firstPlacement (q := q) A
      ((permRep ℂ H (p + q) (subsetRepresentative S)⁻¹ : HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)) ψ))‖ = _
  rw [(mem_fixedSubmodule.mp hψ) ((subsetRepresentative S)⁻¹), permRep_apply]
  exact (permHilbertIsometry (𝕜 := ℂ) (E := H) (subsetRepresentative S)).norm_map _

end QuantumNLS.MarginalSandwichNorm

#print axioms QuantumNLS.MarginalSandwichNorm.sandwich_reducedDensity
#print axioms QuantumNLS.MarginalSandwichNorm.quadraticError_reducedDensity
#print axioms QuantumNLS.MarginalSandwichNorm.firstPlacement_norm
#print axioms QuantumNLS.MarginalSandwichNorm.subsetPlacement_norm

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.MarginalSandwichNorm." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
