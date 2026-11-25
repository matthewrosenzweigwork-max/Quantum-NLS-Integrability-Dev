import QuantumNLS.BetheBasisOrthogonality

/-! The one-particle Fourier endpoint, without the held continuity port. -/
noncomputable section
open Set
open scoped BigOperators InnerProductSpace NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheBasisOneParticle
open PhysicalTensor BetheFreeFamily BetheContinuityInputs BetheWaveContinuity
open BetheWavefunctions BetheBasisOrthogonality

/-- With one particle the actual logarithmic root is the free root for any
positive coupling; the interaction sum is empty. -/
theorem one_root (L : ℝ) [Fact (0 < L)] {c : ℝ} (hc : 0 < c)
    (n : Fin 1 → ℤ) : BetheSmooth.sourceRoots L n c = freeRoots L n := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hs := congrFun (BetheSmooth.sourceRoots_solves (Fact.out : 0 < L) hc n) 0
  simp only [BetheAdmission.logMap, Fin.sum_univ_one, sub_self, zero_div,
    Real.arctan_zero, mul_zero, add_zero, BetheSmooth.sourceNumbers,
    Nat.cast_one, Fin.val_zero, Nat.cast_zero, sub_zero] at hs
  dsimp only [freeRoots]
  apply mul_right_cancel₀ (ne_of_gt (Fact.out : 0 < L))
  calc
    BetheSmooth.sourceRoots L n c 0 * L = 2 * Real.pi * (n 0 : ℝ) := by nlinarith [hs]
    _ = (2 * Real.pi / L * (n 0 : ℝ)) * L := by
      field_simp [ne_of_gt (Fact.out : 0 < L)]

/-- The original one-particle coordinate vector is the original free
Fourier sum, not a newly chosen eigenvector or a rescaled vector. -/
theorem one_wave (L : ℝ) [Fact (0 < L)] (c : ℝ≥0) (n : Label 1) :
    wave (L := L) c n = freeSym (L := L) n := by
  by_cases hc : 0 < (c : ℝ)
  · rw [wave_pos hc]
    apply Subtype.ext
    change (BetheH1.waveH1 (L := L) hc n.property).val = freeVector L n.val
    rw [← vector_eq_wave hc n.property, one_root L hc n.val]
    congr 1
    funext σ
    simp only [coefficient]
    apply Finset.prod_eq_one
    intro i _
    apply Finset.prod_eq_one
    intro j hj
    exact False.elim ((ne_of_lt (Finset.mem_filter.mp hj).2) (Fin.ext (by omega)))
  · have hc0 : c = 0 := NNReal.coe_eq_zero.mp (le_antisymm (not_lt.mp hc) c.property)
    rw [hc0, wave_zero]

/-- One-particle density is Fourier completeness, independently of EXT-001. -/
theorem one_dense (L : ℝ) [Fact (0 < L)] (c : ℝ≥0) :
    (Submodule.span ℂ (range (wave (L := L) c : Label 1 → ContactOperator.SymL2 L 1))).topologicalClosure = ⊤ := by
  have he : (wave (L := L) c : Label 1 → ContactOperator.SymL2 L 1) = freeSym (L := L) :=
    funext (one_wave L c)
  rw [he]
  exact free_family_complete

/-- The normalized one-particle vectors are a complete orthonormal family. -/
theorem one_complete_orthonormal (L : ℝ) [Fact (0 < L)] {c : ℝ≥0}
    (hc : 0 < (c : ℝ)) :
    Orthonormal ℂ (unitWave (L := L) c : Label 1 → ContactOperator.SymL2 L 1) ∧
    (Submodule.span ℂ (range (unitWave (L := L) c : Label 1 → ContactOperator.SymL2 L 1))).topologicalClosure = ⊤ := by
  refine ⟨unitWave_orthonormal L hc, ?_⟩
  rw [span_unitWave L c]
  exact one_dense L c

/-- The proved orthonormal-family clauses apply at the exact mean-field
coupling kappa/N for every positive particle number. -/
theorem meanField_orthonormal (L : ℝ) [Fact (0 < L)] (N : ℕ)
    {κ : ℝ} (hκ : 0 < κ) :
    Orthonormal ℂ (unitWave (L := L)
      (⟨κ / (N+1), (div_pos hκ (by positivity)).le⟩ : ℝ≥0) :
        Label (N+1) → ContactOperator.SymL2 L (N+1)) :=
  unitWave_orthonormal L (div_pos hκ (by positivity))

end QuantumNLS.BetheBasisOneParticle

#print axioms QuantumNLS.BetheBasisOneParticle.one_root
#print axioms QuantumNLS.BetheBasisOneParticle.one_wave
#print axioms QuantumNLS.BetheBasisOneParticle.one_dense
#print axioms QuantumNLS.BetheBasisOneParticle.one_complete_orthonormal
#print axioms QuantumNLS.BetheBasisOneParticle.meanField_orthonormal

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheBasisOneParticle.one_root,
    ``QuantumNLS.BetheBasisOneParticle.one_wave,
    ``QuantumNLS.BetheBasisOneParticle.one_dense,
    ``QuantumNLS.BetheBasisOneParticle.one_complete_orthonormal,
    ``QuantumNLS.BetheBasisOneParticle.meanField_orthonormal]
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
            throwError "Basis one particle nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheSpectralContinuity.transfer_source_all,
    ``QuantumNLS.BetheSpectralContinuity.spectralValue_entire,
    ``QuantumNLS.TransferSeparationRepairBridge.separation_cofinite,
    ``QuantumNLS.BethePhysicalTransfer.realTransfer_isSelfAdjoint,
    ``QuantumNLS.BethePhysicalTransfer.transfer_adjoint,
    ``QuantumNLS.BetheVandermonde.valSym_ne_zero,
    ``QuantumNLS.BetheContinuityInputs.norm_unitWave] do
    unless seen.contains n do
      throwError "Basis one particle missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.NormalizedTransfer." ||
        n.toString.startsWith "QuantumNLS.TransferSeparationLiteral." ||
        n.toString.startsWith "QuantumNLS.TransferSeparationOnShell." ||
        n.toString.startsWith "QuantumNLS.TransferSeparation.separation" then
      throwError "Basis one particle forbidden dependency: {n}"
  Lean.logInfo m!"Basis one particle aggregate audit PASS: {seen.size} transitive constants. One-particle Fourier equality, unconditional one-particle density, complete orthonormal family and exact positive-particle mean-field normalization; no external completeness premise."
