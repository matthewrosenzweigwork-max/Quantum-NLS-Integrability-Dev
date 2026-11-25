import QuantumNLS.Local006CoefficientLiftE

/-! LOCAL-006: the degree-one term of S - 1 is exactly zero. This is a
source-operator coefficient calculation, using the accepted LOCAL-005 identity.
In particular this is stronger than estimating it by a linear majorant. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
open scoped ENNReal BigOperators InnerProductSpace

namespace QuantumNLS.Local006.FirstCoefficientE
open QuantumNLS.LocalSpectral QuantumNLS.Local005 QuantumNLS.Local005.SourceC
  QuantumNLS.Local005.SourceD QuantumNLS.ResetFreeResolventLOCAL001
  QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

lemma contour_projection_one (L r : ℝ) (n : ℤ) (q : Fin (1 - 1) → ℤ) :
    contourScalar L r .projection (k := 1) n q = 0 := by
  have hi : (fun z : ℂ => (z - (pm L n : ℂ))⁻¹ ^ 2) =
      (fun z : ℂ => (z - (pm L n : ℂ)) ^ (-2 : ℤ)) := by
    funext z
    simp [zpow_neg, inv_pow]
  have hprod (z : ℂ) :
      (∏ i : Fin (1 - 1), (z - (pm L (sourceMode n (q i)) : ℂ))⁻¹) = 1 := by
    exact Finset.prod_eq_one (fun i _ => Fin.elim0 i)
  simp only [contourScalar, endpointOrder, hprod, mul_one]
  rw [hi, circleIntegral.integral_sub_zpow_of_ne (by norm_num), smul_zero]

/-- The absolute Fourier majorant itself vanishes, so there is no loss of the
degree-two start when the coefficientwise absolute values are taken. -/
theorem projection_one_majorant_zero (L r κ : ℝ) (u : Fin 1 → ℤ → ℂ) (n : ℤ) :
    contourMajorant L r κ .projection 1 u n = 0 := by
  simp only [contourMajorant, contourAbsTerm, contour_projection_one, norm_zero,
    mul_zero, tsum_zero]

theorem projection_one_coefficient_zero (L r κ : ℝ) (u : Fin 1 → ℤ → ℂ)
    (n : ℤ) (i j : Fin 2) : coefficientEntry L r κ .projection 1 u n i j = 0 := by
  simp only [coefficientEntry, pathCoefficient, contour_projection_one, mul_zero,
    tsum_zero, ite_self]

variable {L κ r : ℝ} [Fact (0 < L)]

/-- The actual source S has zero first ordered coefficient, for every physical
input and both free components. No smallness or Fourier-support premise occurs. -/
theorem first_projection_coefficient_zero (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (u : Fin 1 → ScalarInterval L) (n : ℤ) (i j : Fin 2) :
    entryFunctional n i j
      (orderedSourceWord hL hκ hr hsmall .projection (extendInputs u) n 1) = 0 ∧
      physicalMajorant L r κ .projection 1 (extendInputs u) n = 0 := by
  constructor
  · rw [orderedSourceWord_entry_posdegree hL hκ hr hsmall n (extendInputs u) (by omega)]
    exact projection_one_coefficient_zero _ _ _ _ _ _ _
  · exact projection_one_majorant_zero _ _ _ _ _

end QuantumNLS.Local006.FirstCoefficientE

#print axioms QuantumNLS.Local006.FirstCoefficientE.contour_projection_one
#print axioms QuantumNLS.Local006.FirstCoefficientE.projection_one_majorant_zero
#print axioms QuantumNLS.Local006.FirstCoefficientE.first_projection_coefficient_zero

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.FirstCoefficientE." ||
        n.toString.startsWith "_private.QuantumNLS.Local006FirstCoefficientE" then
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
  Lean.logInfo m!"Local006FirstCoefficientE audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
