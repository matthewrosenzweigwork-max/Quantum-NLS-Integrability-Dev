import QuantumNLS.PhysicalPlacementError
import QuantumNLS.PlacementCommutatorL2

/-! Source Cauchy–Schwarz estimate on full, uncompressed placements. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.SourcePlacementCommutator
open TensorCarrier TensorPlacements KernelDefinition PhysicalTensor PlacementGrouping
open PlacementUnionReindex RootOverlapCommutator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Cauchy–Schwarz needs selfadjointness only of the small kernel. -/
theorem pair_bound (T J : H →L[ℂ] H) (hT : IsSelfAdjoint T) (v : H) :
    ‖⟪v, (T * J - J * T) v⟫_ℂ‖ ≤ 2 * ‖T v‖ * ‖J‖ * ‖v‖ := by
  have ht : ⟪v, T (J v)⟫_ℂ = ⟪T v, J v⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, show T.adjoint = T from hT]
  change ‖⟪v, T (J v) - J (T v)⟫_ℂ‖ ≤ _
  rw [inner_sub_right, ht]
  calc
    _ ≤ ‖⟪T v, J v⟫_ℂ‖ + ‖⟪v, J (T v)⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ ‖T v‖ * ‖J v‖ + ‖v‖ * ‖J (T v)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left (J.le_opNorm v) (norm_nonneg (T v)),
        mul_le_mul_of_nonneg_left (J.le_opNorm (T v)) (norm_nonneg v)]

/-- Isometric conjugation preserves selfadjointness. -/
theorem conjugate_selfadjoint {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (e : H ≃ₗᵢ[ℂ] K)
    (T : K →L[ℂ] K) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (e.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
      e.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪e.symm (T (e x)), y⟫_ℂ = ⟪x, e.symm (T (e y))⟫_ℂ
  rw [← e.inner_map_map, ← e.inner_map_map x]
  simp only [e.apply_symm_apply]
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) (e x) (e y)
  change ⟪T (e x), e y⟫_ℂ = ⟪e x, T (e y)⟫_ℂ at hs
  exact hs

/-- Zero extension respects the actual adjoint. -/
theorem extend_adjoint {p : ℕ} (A : BoundedSymmetricKernel H p) :
    (extendSymKernel A).adjoint = extendSymKernel A.adjoint := by
  have hp : symProjToSector (H := H) p = (SymSector ℂ H p).orthogonalProjectionOnto := by
    ext x
    change symProj ℂ H p x = (SymSector ℂ H p).starProjection x
    rw [symProj_eq_starProjection]
  simp only [extendSymKernel, hp, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    ContinuousLinearMap.comp_assoc]

/-- Literal single placements of a selfadjoint kernel are selfadjoint. -/
theorem raw_selfadjoint (N p : ℕ) (hp : p ≤ N)
    (A : BoundedSymmetricKernel H p) (hA : IsSelfAdjoint A)
    (S : PlacementSubset p (N - p)) : IsSelfAdjoint (rawSubsetPlacement N p hp S A) := by
  have he : IsSelfAdjoint (extendSymKernel A) := by
    change (extendSymKernel A).adjoint = extendSymKernel A
    rw [extend_adjoint, show A.adjoint = A from hA]
  have hf : IsSelfAdjoint (firstPlacement (q := N - p) A) := by
    apply conjugate_selfadjoint (splitIsometry p (N - p))
    change (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _)).adjoint = _
    rw [adjoint_htmap, ContinuousLinearMap.adjoint_id, show (extendSymKernel A).adjoint = _ from he]
  have hs : IsSelfAdjoint (subsetPlacement S A) := by
    let e := permHilbertIsometry (𝕜 := ℂ) (E := H) (subsetRepresentative S)⁻¹
    convert conjugate_selfadjoint e (firstPlacement (q := N - p) A) hf using 1
    apply ContinuousLinearMap.ext
    intro x
    change _ = e.symm (firstPlacement A (e x))
    simp only [subsetPlacement, permutedPlacement, ContinuousLinearMap.comp_apply, permRep_apply]
    have hei : permHilbertIsometry (𝕜 := ℂ) (E := H) (subsetRepresentative S) = e.symm := by
      change permHom ℂ H _ (subsetRepresentative S) = (permHom ℂ H _ ((subsetRepresentative S)⁻¹))⁻¹
      rw [map_inv, inv_inv]
    rw [hei]
  unfold rawSubsetPlacement
  have hc {m n : ℕ} (h : m = n) (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m)
      (ht : IsSelfAdjoint T) : IsSelfAdjoint (PlacementFusion.castTensorOperator h T) := by
    cases h
    exact ht
  exact hc _ _ hs

/-- The actual overlap fraction multiplies the vector error, rather than the
operator norm. Both averages are expanded before restriction to Sym^N. -/
theorem average_bound (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (hN : 1 ≤ N)
    (A : BoundedSymmetricKernel H p) (hA : IsSelfAdjoint A)
    (J : BoundedSymmetricKernel H q) (v : HilbertTensorPower ℂ H N)
    {e : ℝ} (he : 0 ≤ e)
    (hv : ∀ S : PlacementSubset p (N - p), ‖rawSubsetPlacement N p hp S A v‖ ≤ e) :
    ‖⟪v, (rawSubsetAverage N p hp A * rawSubsetAverage N q hq J -
      rawSubsetAverage N q hq J * rawSubsetAverage N p hp A) v⟫_ℂ‖ ≤
        2 * e * ‖J‖ * ‖v‖ * ((p * q : ℝ) / N) := by
  classical
  let V := fun z : ActualPairPlacement N p q =>
    ⟪v, (rawSubsetPlacement N p hp z.1 A * rawSubsetPlacement N q hq z.2 J -
      rawSubsetPlacement N q hq z.2 J * rawSubsetPlacement N p hp z.1 A) v⟫_ℂ
  let bad := fun z : ActualPairPlacement N p q => ¬Disjoint (leftSlots hp z) (rightSlots hq z)
  have hpair (z : ActualPairPlacement N p q) : ‖V z‖ ≤ if bad z then 2 * e * ‖J‖ * ‖v‖ else 0 := by
    by_cases hz : bad z
    · rw [ite_eq_left hz]
      exact (pair_bound _ _ (raw_selfadjoint N p hp A hA z.1) v).trans (by
        gcongr
        · exact hv z.1
        · exact norm_rawSubsetPlacement_le N q hq z.2 J)
    · rw [ite_eq_right hz]
      dsimp [V]
      rw [show rawSubsetPlacement N p hp z.1 A * rawSubsetPlacement N q hq z.2 J =
        rawSubsetPlacement N q hq z.2 J * rawSubsetPlacement N p hp z.1 A from
        rawPlacement_commute_of_disjoint N p q hp hq A J z (not_not.mp hz), sub_self]
      simp
  have hsum : ‖∑ z, V z‖ ≤ ((Finset.univ.filter bad).card : ℝ) * (2 * e * ‖J‖ * ‖v‖) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun z _ => hpair z).trans (le_of_eq ?_))
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hn : ‖((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹)‖ =
      ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ := by
    simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_inv]
  change ‖⟪v, ((rawSubsetAverage N p hp A).comp (rawSubsetAverage N q hq J) -
    (rawSubsetAverage N q hq J).comp (rawSubsetAverage N p hp A)) v⟫_ℂ‖ ≤ _
  rw [average_commutator_eq]
  simp only [smul_apply, sum_apply, inner_smul_right, inner_sum]
  rw [norm_mul, hn]
  have hprod : (∑ S : PlacementSubset p (N - p), ∑ T : PlacementSubset q (N - q),
    ⟪v, ((rawSubsetPlacement N p hp S A).comp (rawSubsetPlacement N q hq T J) -
      (rawSubsetPlacement N q hq T J).comp (rawSubsetPlacement N p hp S A)) v⟫_ℂ) = ∑ z, V z :=
    (Fintype.sum_prod_type (f := V)).symm
  rw [hprod]
  calc
    _ ≤ ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ *
      (((N.choose p : ℝ) * (N.choose q : ℝ) * ((p * q : ℝ) / N)) * (2 * e * ‖J‖ * ‖v‖)) := by
      gcongr
      exact hsum.trans (mul_le_mul_of_nonneg_right (card_badPairs_le hp hq hN) (by positivity))
    _ = _ := by
      have hcp : (N.choose p : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hp
      have hcq : (N.choose q : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hq
      field_simp [hcp, hcq]

end QuantumNLS.SourcePlacementCommutator

-- AUTHOR AUDITS
#print axioms QuantumNLS.SourcePlacementCommutator.pair_bound
#print axioms QuantumNLS.SourcePlacementCommutator.conjugate_selfadjoint
#print axioms QuantumNLS.SourcePlacementCommutator.extend_adjoint
#print axioms QuantumNLS.SourcePlacementCommutator.raw_selfadjoint
#print axioms QuantumNLS.SourcePlacementCommutator.average_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SourcePlacementCommutator." then
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
