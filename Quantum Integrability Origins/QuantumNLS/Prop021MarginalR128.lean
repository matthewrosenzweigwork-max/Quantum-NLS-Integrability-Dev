import QuantumNLS.MarginalPureState
import QuantumNLS.Fidelity

/-! PROP-021: trace geometry of the actual normalized partial trace and the
prepared-state error. No physical depletion-to-marginal identity is assumed.
The k-particle union bound remains a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop021MarginalR128
open TensorCarrier PhysicalTensor TraceClass
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma traceNorm_neg (k : ℕ) (T : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k) :
    traceNorm (-T) = traceNorm T := by simpa using traceNorm_smul (-1:ℂ) T

/-- Normalization of the actual DEF-030 partial trace. -/
theorem marginal_traceNorm (N k : ℕ) (hk : k ≤ N)
    (ψ : HilbertTensorPower ℂ E N) :
    traceNorm (reducedDensityN N k hk ψ) = ENNReal.ofReal (‖ψ‖^2) := by
  unfold reducedDensityN
  rw [traceNorm_reducedDensityPower,LinearIsometryEquiv.norm_map]

/-- The exact pure-target fidelity step in the printed proof. -/
theorem marginal_fidelity (N k : ℕ) (hk : k ≤ N)
    (ψ : HilbertTensorPower ℂ E N) (hψ : ‖ψ‖ = 1) (u : E) (hu : ‖u‖ = 1) :
    traceNorm (reducedDensityN N k hk ψ -
      InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ E k) (htpow k u)) ≤
    ENNReal.ofReal (2 * Real.sqrt (1-
      (⟪(htpow k u : HilbertTensorPower ℂ E k),
        reducedDensityN N k hk ψ (htpow k u)⟫_ℂ).re)) := by
  have hp := reducedDensityN_isPositive N k hk ψ
  have hn : traceNorm (reducedDensityN N k hk ψ) = 1 := by
    rw [marginal_traceNorm,hψ]; norm_num
  have htr : posTrace (reducedDensityN N k hk ψ) = 1 := by
    rwa [traceNorm_of_isPositive hp] at hn
  apply Fidelity.fidelity _ hp _ htr _ _
  · rw [IsTraceClass,hn]; exact ENNReal.one_lt_top
  · rw [norm_htpow,hu,one_pow]

/-- Two normalized marginals have trace distance at most two. -/
theorem marginal_distance_le_two (N k : ℕ) (hk : k ≤ N)
    (ψ φ : HilbertTensorPower ℂ E N) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (reducedDensityN N k hk ψ-reducedDensityN N k hk φ) ≤ 2 := by
  have h := traceNorm_add_le (reducedDensityN N k hk ψ) (-reducedDensityN N k hk φ)
  rw [traceNorm_neg,marginal_traceNorm,marginal_traceNorm,hψ,hφ] at h
  simpa only [sub_eq_add_neg,one_pow,ENNReal.ofReal_one,one_add_one_eq_two] using h

/-- The exact additional error for any normalized initial preparation, under
an arbitrary sector isometry (in particular the actual unitary evolution). -/
theorem preparation_error (N k : ℕ) (hk : k ≤ N)
    (U : SymSector ℂ E N →ₗᵢ[ℂ] SymSector ℂ E N)
    (ψ φ : SymSector ℂ E N) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (reducedDensityN N k hk (U φ).val - reducedDensityN N k hk (U ψ).val) ≤
      ENNReal.ofReal (2 * ‖φ-ψ‖) := by
  have h := MarginalPureState.traceNorm_reducedDensityN_sub_le N k hk (U φ).val (U ψ).val
  have h1 : ‖(U φ).val‖ = 1 := (U.norm_map φ).trans hφ
  have h2 : ‖(U ψ).val‖ = 1 := (U.norm_map ψ).trans hψ
  have hd : ‖(U φ).val-(U ψ).val‖ = ‖φ-ψ‖ := by
    change ‖U φ-U ψ‖ = ‖φ-ψ‖
    rw [← map_sub,U.norm_map]
  rw [h1,h2,hd] at h
  convert h using 2
  ring

/-- Add the prepared-state error to any proved target comparison. -/
theorem preparation_target (N k : ℕ) (hk : k ≤ N)
    (U : SymSector ℂ E N →ₗᵢ[ℂ] SymSector ℂ E N)
    (ψ φ : SymSector ℂ E N) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (R : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k) :
    traceNorm (reducedDensityN N k hk (U φ).val-R) ≤
      traceNorm (reducedDensityN N k hk (U ψ).val-R)+
      ENNReal.ofReal (2 * ‖φ-ψ‖) := by
  have he : reducedDensityN N k hk (U φ).val-R =
      (reducedDensityN N k hk (U φ).val-reducedDensityN N k hk (U ψ).val)+
      (reducedDensityN N k hk (U ψ).val-R) := by abel
  rw [he]
  exact (traceNorm_add_le _ _).trans (by
    have h := add_le_add (preparation_error N k hk U ψ φ hψ hφ)
      (le_rfl : traceNorm (reducedDensityN N k hk (U ψ).val-R) ≤ _)
    simpa only [add_comm] using h)
end QuantumNLS.Prop021MarginalR128
#print axioms QuantumNLS.Prop021MarginalR128.marginal_fidelity
#print axioms QuantumNLS.Prop021MarginalR128.preparation_target

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021MarginalR128"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R128 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
