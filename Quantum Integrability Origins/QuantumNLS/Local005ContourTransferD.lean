import QuantumNLS.Local005SourcePathD

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Metric
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Local005.SourceD
open QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.Local002

variable {L r κ : ℝ} [Fact (0 < L)]

/-- The actual matrix entry on the two free source modes. -/
def entryFunctional (n : ℤ) (i j : Fin 2) : Op L →L[ℂ] ℂ :=
  (innerSL ℂ (chi L n i)).comp (ContinuousLinearMap.apply ℂ (H2 L) (chi L n j))

def functionalContour (n : ℤ) (T : Op L →L[ℂ] ℂ) (F : ContourOp L r n) :
    ScalarContour L r n := ⟨fun z => T (F z), T.continuous.comp F.continuous⟩

set_option backward.isDefEq.respectTransparency false in
theorem functional_circleIntegral (T : Op L →L[ℂ] ℂ) (F : ℂ → Op L)
    (c : ℂ) (r : ℝ) (hF : CircleIntegrable F c r) :
    T (∮ z in C(c, r), F z) = ∮ z in C(c, r), T (F z) := by
  unfold circleIntegral
  simpa only [map_smul, RingHom.id_apply] using
    (T.intervalIntegral_comp_comm hF.out).symm

theorem functional_contourJ (hr : 0 < r) (n : ℤ) (T : Op L →L[ℂ] ℂ)
    (F : ContourOp L r n) :
    T (contourJ hr n F) = scalarJ hr n (functionalContour n T F) := by
  rw [contourJ_apply, map_smul, functional_circleIntegral T _ _ _
    ((continuousOn_extC F).circleIntegrable hr.le)]
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (∮ z in C(center L n, r), T (extC F z)) =
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (∮ z in C(center L n, r), scalarExtend (functionalContour n T F) z)
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  change T (extC F z) = scalarExtend (functionalContour n T F) z
  rw [extC_apply _ hz, scalarExtend_apply _ hz]
  rfl

/-- The two free source projections are the proved orthogonal projection E E*. -/
theorem source_freeProj_eq (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) :
    freeProj L κ n r = embed L n ∘L (embed L n).adjoint := by
  apply Local002Free.freeProj_eq hL hr
  · convert hsmall using 1 <;> unfold spacing <;> ring
  · intro z hz
    exact ⟨free L κ n z, free_isResolvent hL hr hsmall n hz,
      by simpa only [one_div, free] using sourceResolvent_norm_le hL κ n hr hsmall hz⟩

theorem source_freeProj_chi (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (j : Fin 2) :
    freeProj L κ n r (chi L n j) = chi L n j := by
  rw [source_freeProj_eq hL hr hsmall n, ContinuousLinearMap.comp_apply]
  simpa using Local002Free.EEadj_chi hL (n := n) rfl j

theorem source_freeProj_adjoint (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) :
    (freeProj L κ n r).adjoint = freeProj L κ n r := by
  simp only [source_freeProj_eq hL hr hsmall n, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem entry_free_compression (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (i j : Fin 2) (A : Op L) :
    entryFunctional n i j (freeProj L κ n r * A * freeProj L κ n r) =
      entryFunctional n i j A := by
  change ⟪chi L n i, (freeProj L κ n r * A * freeProj L κ n r) (chi L n j)⟫_ℂ = _
  simp only [ContinuousLinearMap.mul_apply, source_freeProj_chi hL hr hsmall n]
  rw [← ContinuousLinearMap.adjoint_inner_left, source_freeProj_adjoint hL hr hsmall n,
    source_freeProj_chi hL hr hsmall n]
  rfl

/-- Matrix entries pass through the source contour functional and both free projections. -/
theorem compressed_contour_entry (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (i j : Fin 2) (F : ContourOp L r n) :
    entryFunctional n i j (freeProj L κ n r * contourJ hr n F * freeProj L κ n r) =
      scalarJ hr n (functionalContour n (entryFunctional n i j) F) := by
  rw [entry_free_compression hL hr hsmall n i j, functional_contourJ]

#print axioms functional_contourJ
#print axioms source_freeProj_eq
#print axioms entry_free_compression
#print axioms compressed_contour_entry
end QuantumNLS.Local005.SourceD

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local005.SourceD." ||
        n.toString.startsWith "_private.QuantumNLS.Local005" then
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
  Lean.logInfo m!"Local005ContourTransferD audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
