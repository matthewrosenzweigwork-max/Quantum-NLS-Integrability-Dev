import QuantumNLS.Fidelity

/-! Finite-rank matrix compressions admit finite nets in the literal trace
norm. This supplies the finite-dimensional part of kinetic compactness. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.FiniteTraceCompression
open TraceClass Fidelity
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℂ H) (s : Finset ι)

/-- Finite orthogonal basis projection. -/
def proj : H →L[ℂ] H := ∑ i ∈ s, InnerProductSpace.rankOne ℂ (b i) (b i)

omit [CompleteSpace H] in
theorem proj_apply (x : H) : proj b s x = ∑ i ∈ s, ⟪b i, x⟫_ℂ • b i := by
  simp [proj, InnerProductSpace.rankOne_apply]

omit [CompleteSpace H] in
theorem proj_basis {i : ι} (hi : i ∈ s) : proj b s (b i) = b i := by
  classical
  rw [proj_apply]
  simp [orthonormal_iff_ite.mp b.orthonormal, hi]

omit [CompleteSpace H] in
theorem proj_inner (x y : H) : ⟪x, proj b s y⟫_ℂ = ⟪proj b s x, y⟫_ℂ := by
  simp only [proj_apply, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
    inner_conj_symm]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem norm_proj_le : ‖proj b s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, proj_apply] using norm_sum_inner_smul_le b s x

omit [CompleteSpace H] in
/-- Exact matrix expansion of a two-sided finite compression. -/
theorem matrix_expansion (A : H →L[ℂ] H) :
    proj b s * A * proj b s = ∑ i ∈ s, ∑ j ∈ s,
      ⟪b i, A (b j)⟫_ℂ • InnerProductSpace.rankOne ℂ (b i) (b j) := by
  ext x
  simp only [mul_apply_eq_comp, proj_apply, map_sum, map_smul,
    sum_apply, smul_apply, InnerProductSpace.rankOne_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1; ring

/-- Operator norm controls trace norm on a fixed finite compression space. -/
theorem traceNorm_compression_le (A : H →L[ℂ] H) :
    traceNorm (proj b s * A * proj b s) ≤ ENNReal.ofReal ((s.card : ℝ) ^ 2 * ‖A‖) := by
  rw [matrix_expansion]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, traceNorm
        (⟪b i, A (b j)⟫_ℂ • InnerProductSpace.rankOne ℂ (b i) (b j)) :=
      (traceNorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => traceNorm_sum_le _ _)
    _ ≤ ∑ _i ∈ s, ∑ _j ∈ s, ENNReal.ofReal ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [traceNorm_smul]
      have hn : ‖⟪b i, A (b j)⟫_ℂ‖ ≤ ‖A‖ := by
        calc
          _ ≤ ‖b i‖ * ‖A (b j)‖ := norm_inner_le_norm _ _
          _ ≤ ‖A‖ := by rw [b.orthonormal.norm_eq_one, one_mul]; simpa [b.orthonormal.norm_eq_one] using A.le_opNorm (b j)
      have hr : traceNorm (InnerProductSpace.rankOne ℂ (b i) (b j)) ≤ 1 := by
        simpa [b.orthonormal.norm_eq_one] using traceNorm_rankOne_le (b i) (b j)
      calc
        _ ≤ ENNReal.ofReal ‖A‖ * 1 := by gcongr
        _ = _ := mul_one _
    _ = _ := by simp [nsmul_eq_mul, pow_two, ENNReal.ofReal_mul, mul_assoc]

/-- The space of matrices supported in s×s. -/
def matrixSpace : Submodule ℂ (H →L[ℂ] H) :=
  Submodule.span ℂ (Set.range (fun ij : s × s =>
    InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2)))

instance : FiniteDimensional ℂ (matrixSpace b s) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

omit [CompleteSpace H] in
theorem compression_mem (A : H →L[ℂ] H) : proj b s * A * proj b s ∈ matrixSpace b s := by
  rw [matrix_expansion]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩)

omit [CompleteSpace H] in
theorem compression_eq_self {A : H →L[ℂ] H} (hA : A ∈ matrixSpace b s) :
    proj b s * A * proj b s = A := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hA
    ext x
    simp only [mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      proj_inner, proj_basis b s j.property, map_smul, proj_basis b s i.property]
  | zero => simp
  | add A B _ _ hA hB => simp only [mul_add, add_mul, hA, hB]
  | smul c A _ hA => simp only [mul_smul_comm, smul_mul_assoc, hA]

/-- Finite-dimensional compactness expressed as finite trace-norm nets.
The centers are themselves finite-rank operators. -/
theorem finite_trace_net {M ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (H →L[ℂ] H), ∀ A : H →L[ℂ] H, A ∈ matrixSpace b s → ‖A‖ ≤ M →
      ∃ C ∈ S, traceNorm (A - C) ≤ ENNReal.ofReal ε := by
  classical
  let δ : ℝ := ε / ((s.card : ℝ) ^ 2 + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨u, hu, hfin, hcov⟩ := (isCompact_closedBall (0 : matrixSpace b s) M).finite_cover_balls hδ
  refine ⟨hfin.toFinset.image (fun (C : matrixSpace b s) => (C : H →L[ℂ] H)), ?_⟩
  intro A hA hAM
  have hAm : (⟨A, hA⟩ : matrixSpace b s) ∈ Metric.closedBall 0 M := by simpa using hAM
  obtain ⟨C, hCu, hAC⟩ := Set.mem_iUnion₂.mp (hcov hAm)
  refine ⟨C, Finset.mem_image.mpr ⟨C, hfin.mem_toFinset.mpr hCu, rfl⟩, ?_⟩
  have he : proj b s * (A - C) * proj b s = A - C := compression_eq_self b s
    ((matrixSpace b s).sub_mem hA C.property)
  rw [← he]
  refine (traceNorm_compression_le b s (A - C)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hd : ‖A - (C : H →L[ℂ] H)‖ < δ := by simpa [dist_eq_norm] using hAC
  have hm : (s.card : ℝ) ^ 2 * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (s.card : ℝ) ^ 2 + 1)).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left hd.le (sq_nonneg _)).trans hm

end QuantumNLS.FiniteTraceCompression

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FiniteTraceCompression.proj
#print axioms QuantumNLS.FiniteTraceCompression.proj_apply
#print axioms QuantumNLS.FiniteTraceCompression.proj_basis
#print axioms QuantumNLS.FiniteTraceCompression.proj_inner
#print axioms QuantumNLS.FiniteTraceCompression.norm_proj_le
#print axioms QuantumNLS.FiniteTraceCompression.matrix_expansion
#print axioms QuantumNLS.FiniteTraceCompression.traceNorm_compression_le
#print axioms QuantumNLS.FiniteTraceCompression.matrixSpace
#print axioms QuantumNLS.FiniteTraceCompression.compression_mem
#print axioms QuantumNLS.FiniteTraceCompression.compression_eq_self
#print axioms QuantumNLS.FiniteTraceCompression.finite_trace_net

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.FiniteTraceCompression." then
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
