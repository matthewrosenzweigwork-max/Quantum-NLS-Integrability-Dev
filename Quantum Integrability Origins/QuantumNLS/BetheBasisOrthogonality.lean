import QuantumNLS.BetheBasisBinding
import QuantumNLS.BetheContinuityInputs
import QuantumNLS.TransferSeparationRepairBridge

/-! Orthogonality and normalization on the original periodic Hilbert space.
The scalar separation repair and all physical modules are used read-only. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheBasisOrthogonality
open TensorCarrier PhysicalTensor BethePhysicalTransfer BetheHigherPlacement
open BetheSpectralContinuity BetheFreeFamily BetheContinuityInputs

/-- Exact carrier identification with the source Hamiltonian vector. -/
theorem source_position (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    symmetricPosition L (N+1) (sourceVector L hc hn) =
      ContactOperator.valSym (BetheH1.waveH1Sym (L := L) hc hn) := by
  rw [sourceVector_eq_physicalWave]
  exact (symmetricPosition L (N+1)).apply_symm_apply _

theorem source_ne_zero (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    sourceVector L hc hn ≠ 0 := by
  intro h
  have he := source_position L hc hn
  rw [h, map_zero] at he
  exact BetheVandermonde.valSym_ne_zero hc hn he.symm

/-- Distinct sorted labels give distinct rapidity multisets. -/
theorem roots_multiset_ne (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n m : Fin N → ℤ} (hn : Antitone n)
    (hm : Antitone m) (hne : n ≠ m) :
    TransferSeparation.msOf (BetheSmooth.sourceRoots L n c) ≠
      TransferSeparation.msOf (BetheSmooth.sourceRoots L m c) := by
  intro he
  apply hne
  apply BetheEigenGlobal.sourceRoots_label_injective (Fact.out : 0 < L) hc
  have hp : List.Perm (List.ofFn (BetheSmooth.sourceRoots L n c))
      (List.ofFn (BetheSmooth.sourceRoots L m c)) := by
    apply Multiset.coe_eq_coe.mp
    simpa only [TransferSeparation.msOf, Fin.univ_val_map] using he
  exact List.ofFn_injective (hp.eq_of_sortedGE
    (BetheSmooth.sourceRoots_strictAnti (Fact.out : 0 < L) hc hn).antitone.sortedGE_ofFn
    (BetheSmooth.sourceRoots_strictAnti (Fact.out : 0 < L) hc hm).antitone.sortedGE_ofFn)

/-- Entire BSC1 eigenvalues differ somewhere on the real axis. The identity
 theorem is applied on the whole complex plane to the actual continuations. -/
theorem real_spectral_separation (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n m : Fin N → ℤ} (hn : Antitone n)
    (hm : Antitone m) (hne : n ≠ m) :
    ∃ x : ℝ, spectralValue L hc hn x ≠ spectralValue L hc hm x := by
  by_contra h
  push Not at h
  have hf : ∃ᶠ x : ℝ in 𝓝[≠] 0,
      spectralValue L hc hn (x : ℂ) = spectralValue L hc hm (x : ℂ) :=
    (Eventually.of_forall h).frequently
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact fun he => hx (Complex.ofReal_injective he)
  have hap : AnalyticOnNhd ℂ (spectralValue L hc hn) univ :=
    fun z _ => (spectralValue_entire L hc hn).analyticAt z
  have haq : AnalyticOnNhd ℂ (spectralValue L hc hm) univ :=
    fun z _ => (spectralValue_entire L hc hm).analyticAt z
  have he := hap.eqOn_of_preconnected_of_frequently_eq haq isPreconnected_univ
    (mem_univ (0 : ℂ)) (ht.frequently hf)
  apply roots_multiset_ne L hc hn hm hne
  apply TransferSeparationRepairBridge.separation_cofinite (Fact.out : 0 < L) hc
    (BetheSmooth.sourceRoots L n c) (BetheSmooth.sourceRoots L m c) ∅
  intro z hz
  have hz' : z ∉ TransferSeparationContinuityRepair.poles
      (BetheSmooth.sourceRoots L n c) (BetheSmooth.sourceRoots L m c) := by simpa using hz
  obtain ⟨hnz,hmz⟩ := TransferSeparationContinuityRepair.not_mem_poles hz'
  rw [← spectralValue_nonpole L hc hn z hnz,
    ← spectralValue_nonpole L hc hm z hmz]
  exact he (mem_univ z)

/-- The half-phase gauge retains exactly the BSC1 eigenvectors. -/
theorem realTransfer_source (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) (x : ℝ) :
    realTransfer L N c x (sourceVector L hc hn) =
      (Complex.exp (-Complex.I * L * x / 2) * spectralValue L hc hn x) •
        sourceVector L hc hn := by
  simp only [realTransfer, smul_apply, transfer_source_all, smul_smul]

/-- Elementary self-adjoint eigenvector orthogonality, without completeness. -/
theorem inner_zero_of_selfAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : E →L[ℂ] E)
    (hT : IsSelfAdjoint T) {u v : E} {a b : ℂ} (hu : u ≠ 0)
    (ha : T u = a • u) (hb : T v = b • v) (hne : a ≠ b) : ⟪u,v⟫_ℂ = 0 := by
  have hr := hT.isSymmetric u u
  change ⟪T u, u⟫_ℂ = ⟪u, T u⟫_ℂ at hr
  rw [ha, inner_smul_left, inner_smul_right] at hr
  have hc : conj a = a := mul_right_cancel₀ (inner_self_ne_zero.mpr hu) hr
  have he := hT.isSymmetric u v
  change ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ at he
  rw [ha, hb, inner_smul_left, inner_smul_right, hc] at he
  exact (mul_eq_zero.mp (by rw [sub_mul, he, sub_self] : (a-b)*⟪u,v⟫_ℂ = 0)).resolve_left
    (sub_ne_zero.mpr hne)

/-- Orthogonality of the actual physical vectors for distinct labels. -/
theorem source_orthogonal (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n m : Fin (N+1) → ℤ} (hn : Antitone n)
    (hm : Antitone m) (hne : n ≠ m) :
    ⟪sourceVector L hc hn, sourceVector L hc hm⟫_ℂ = 0 := by
  obtain ⟨x,hx⟩ := real_spectral_separation L hc hn hm hne
  exact inner_zero_of_selfAdjoint (realTransfer L (N+1) c x)
    (realTransfer_isSelfAdjoint L (N+1) c x) (source_ne_zero L hc hn)
    (realTransfer_source L hc hn x) (realTransfer_source L hc hm x)
    (fun he => hx (mul_left_cancel₀ (Complex.exp_ne_zero _) he))

/-- The same orthogonality in the original symmetric periodic L² space. -/
theorem wave_orthogonal (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ≥0} (hc : 0 < (c : ℝ)) {n m : Label (N+1)} (hne : n ≠ m) :
    ⟪wave (L := L) c n, wave (L := L) c m⟫_ℂ = 0 := by
  rw [wave_pos hc, wave_pos hc, ← source_position L hc n.property,
    ← source_position L hc m.property]
  rw [(symmetricPosition L (N+1)).inner_map_map]
  exact source_orthogonal L hc n.property m.property (fun he => hne (Subtype.ext he))

/-- Normalizing the unchanged source family gives an orthonormal family.
No positive-c dense-span assertion is used. -/
theorem unitWave_orthonormal (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ≥0} (hc : 0 < (c : ℝ)) :
    Orthonormal ℂ (unitWave (L := L) c : Label (N+1) → ContactOperator.SymL2 L (N+1)) := by
  refine ⟨norm_unitWave c, ?_⟩
  intro n m hne
  change ⟪unitWave c n, unitWave c m⟫_ℂ = 0
  change ⟪((‖wave (L := L) c n‖ : ℂ)⁻¹) • wave (L := L) c n,
    ((‖wave (L := L) c m‖ : ℂ)⁻¹) • wave (L := L) c m⟫_ℂ = 0
  rw [inner_smul_left (wave (L := L) c n)
    (((‖wave (L := L) c m‖ : ℂ)⁻¹) • wave (L := L) c m)
    ((‖wave (L := L) c n‖ : ℂ)⁻¹)]
  rw [inner_smul_right (wave (L := L) c n) (wave (L := L) c m)
    ((‖wave (L := L) c m‖ : ℂ)⁻¹)]
  rw [wave_orthogonal L hc hne, mul_zero, mul_zero]

/-- Normalization preserves the algebraic span and hence its closure. -/
theorem span_unitWave (L : ℝ) [Fact (0 < L)] {N : ℕ} (c : ℝ≥0) :
    Submodule.span ℂ (range (unitWave (L := L) c : Label (N+1) → ContactOperator.SymL2 L (N+1))) =
      Submodule.span ℂ (range (wave (L := L) c : Label (N+1) → ContactOperator.SymL2 L (N+1))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    have hne : (‖wave (L := L) c n‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (wave_ne_zero c n))
    have he : (‖wave (L := L) c n‖ : ℂ) • unitWave (L := L) c n = wave (L := L) c n := by
      simp only [unitWave, smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [← he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n,rfl⟩)

end QuantumNLS.BetheBasisOrthogonality

#print axioms QuantumNLS.BetheBasisOrthogonality.source_position
#print axioms QuantumNLS.BetheBasisOrthogonality.source_ne_zero
#print axioms QuantumNLS.BetheBasisOrthogonality.roots_multiset_ne
#print axioms QuantumNLS.BetheBasisOrthogonality.real_spectral_separation
#print axioms QuantumNLS.BetheBasisOrthogonality.realTransfer_source
#print axioms QuantumNLS.BetheBasisOrthogonality.inner_zero_of_selfAdjoint
#print axioms QuantumNLS.BetheBasisOrthogonality.source_orthogonal
#print axioms QuantumNLS.BetheBasisOrthogonality.wave_orthogonal
#print axioms QuantumNLS.BetheBasisOrthogonality.unitWave_orthonormal

#print axioms QuantumNLS.BetheBasisOrthogonality.span_unitWave

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheBasisOrthogonality.span_unitWave,
    ``QuantumNLS.BetheBasisOrthogonality.source_position,
    ``QuantumNLS.BetheBasisOrthogonality.source_ne_zero,
    ``QuantumNLS.BetheBasisOrthogonality.roots_multiset_ne,
    ``QuantumNLS.BetheBasisOrthogonality.real_spectral_separation,
    ``QuantumNLS.BetheBasisOrthogonality.realTransfer_source,
    ``QuantumNLS.BetheBasisOrthogonality.inner_zero_of_selfAdjoint,
    ``QuantumNLS.BetheBasisOrthogonality.source_orthogonal,
    ``QuantumNLS.BetheBasisOrthogonality.wave_orthogonal,
    ``QuantumNLS.BetheBasisOrthogonality.unitWave_orthonormal]
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
            throwError "Basis orthogonality nonstandard dependency: {n}"
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
      throwError "Basis orthogonality missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.NormalizedTransfer." ||
        n.toString.startsWith "QuantumNLS.TransferSeparationLiteral." ||
        n.toString.startsWith "QuantumNLS.TransferSeparationOnShell." ||
        n.toString.startsWith "QuantumNLS.TransferSeparation.separation" then
      throwError "Basis orthogonality forbidden dependency: {n}"
  Lean.logInfo m!"Basis orthogonality aggregate audit PASS: {seen.size} transitive constants. Actual physical self-adjoint gauge, entire BSC1 scalar, frozen repaired separation, original coordinate vector, nonvanishing and normalization; no completeness premise."
