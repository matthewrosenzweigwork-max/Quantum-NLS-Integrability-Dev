import QuantumNLS.BetheWaveContinuity

/-!
Printed free-family argument, periodic_basis.tex:294–299.
Symmetrize the ordinary torus Fourier modes, retaining all permutation
multiplicities. No interacting completeness or Bethe U5 premise is used.
-/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open Filter MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.BetheWavefunctions QuantumNLS.BetheWaveContinuity
  QuantumNLS.BetheWeakGradient QuantumNLS.BetheExtension
  QuantumNLS.ProductWeakDerivatives QuantumNLS.CollisionTrace

namespace QuantumNLS.BetheFreeFamily
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The factor converting normalized Fourier products to literal plane waves. -/
def scale (L : ℝ) (N : ℕ) : ℂ := (Real.sqrt L : ℂ) ^ N

theorem scale_ne_zero : scale L N ≠ 0 :=
  pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (Fact.out : 0 < L)).ne')

/-- The ordinary normalized Fourier product has exactly the physical volume factor. -/
theorem modes_plane (w : Fin N → ℤ) (x : Fin N → AddCircle L) :
    scale L N * (∏ j, QuantumNLS.Fourier.mode L (w j) (x j)) =
      planeWave (freeRoots L w) (representatives L x) := by
  have hm (j : Fin N) : QuantumNLS.Fourier.mode L (w j) (x j) =
      ((Real.sqrt L : ℂ)⁻¹) * Complex.exp
        (Complex.I * ((2 * Real.pi / L * (w j : ℝ) * representatives L x j : ℝ) : ℂ)) := by
    have h := QuantumNLS.Fourier.mode_coe L (w j) (representatives L x j)
    rw [show ((representatives L x j : ℝ) : AddCircle L) = x j from AddCircle.coe_equivIco] at h
    rw [h]
    push_cast
    congr 2
    ring
  simp only [hm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, scale]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (Fact.out : 0 < L)).ne'), one_pow, one_mul,
    ← Complex.exp_sum]
  unfold planeWave freeRoots
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]

/-- The free endpoint is the symmetrized ordinary torus Fourier family,
with the literal permutation multiplicities and physical volume factor. -/
theorem freeVector_eq_modes (n : Fin N → ℤ) :
    freeVector L n = scale L N • ∑ σ : Equiv.Perm (Fin N), prodMode L N (n ∘ σ) := by
  apply Lp.ext
  have hp (σ : Equiv.Perm (Fin N)) := coeFn_prodMode (L := L) (n ∘ σ)
  filter_upwards [coe_freeVector (L := L) n,
    Lp.coeFn_smul (scale L N) (∑ σ : Equiv.Perm (Fin N), prodMode L N (n ∘ σ)),
    Lp.coeFn_finsetSum Finset.univ (fun σ : Equiv.Perm (Fin N) => prodMode L N (n ∘ σ)),
    Filter.eventually_all.2 hp] with x hx hs hsum hprod
  rw [hx, hs, Pi.smul_apply, smul_eq_mul, hsum]
  simp only [Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hprod σ, modes_plane]
  rfl

/-- The free vector is symmetric, as a literal L² class. -/
theorem freeVector_mem_sym (n : Fin N → ℤ) : freeVector L n ∈ ContactOperator.SymL2 L N := by
  rw [ContactOperator.mem_SymL2_iff, isSymm_iff_coeff]
  intro τ w
  rw [freeVector_eq_modes, map_smul, map_sum]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sum, Finset.sum_apply,
    momUnitary_prodMode, lp.single_apply, Pi.single_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight τ.symm)
  intro σ
  have he : w ∘ τ = n ∘ σ ↔ w = n ∘ (σ * τ.symm) := by
    constructor <;> intro h <;> funext j
    · simpa using congrFun h (τ.symm j)
    · simpa using congrFun h (τ j)
  simp only [he]
  rfl

/-- A symmetric vector pairs with the finite symmetrization as the
nonzero number of permutations times its Fourier coefficient. -/
theorem inner_free_symmetric (n : Fin N → ℤ) {F : L2TN L N}
    (hF : F ∈ ContactOperator.SymL2 L N) :
    ⟪freeVector L n, F⟫_ℂ = (star (scale L N) * (Fintype.card (Equiv.Perm (Fin N)) : ℂ)) *
      (momUnitary L N F : (Fin N → ℤ) → ℂ) n := by
  rw [freeVector_eq_modes, inner_smul_left, sum_inner]
  simp only [← momUnitary_apply_eq_inner,
    (isSymm_iff_coeff F).1 ((ContactOperator.mem_SymL2_iff F).1 hF),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [starRingEnd_apply]
  ring

/-- A repeated free momentum contributes its positive integer orbit multiplicity. -/
theorem freeVector_ne_zero (n : Fin N → ℤ) : freeVector L n ≠ 0 := by
  intro hz
  have he := congrArg (fun F : L2TN L N => (momUnitary L N F : (Fin N → ℤ) → ℂ) n) hz
  rw [freeVector_eq_modes, map_smul, map_sum, map_zero] at he
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sum, Finset.sum_apply,
    momUnitary_prodMode, lp.single_apply, Pi.single_apply, lp.coeFn_zero, Pi.zero_apply] at he
  have hp : (0 : ℝ) < ∑ σ : Equiv.Perm (Fin N), if n = n ∘ σ then (1 : ℝ) else 0 := by
    apply Finset.sum_pos' (fun σ _ => by split_ifs <;> norm_num)
    refine ⟨Equiv.refl _, Finset.mem_univ _, ?_⟩
    simp
  have hne : (∑ σ : Equiv.Perm (Fin N), if n = n ∘ σ then (1 : ℂ) else 0) ≠ 0 := by
    exact_mod_cast hp.ne'
  exact (mul_ne_zero (scale_ne_zero (L := L) (N := N)) hne) he

/-- Different decreasing labels have disjoint permutation orbits. -/
theorem labels_of_permutation {n m : Fin N → ℤ} (hn : Antitone n) (hm : Antitone m)
    (σ : Equiv.Perm (Fin N)) (he : n = m ∘ σ) : n = m := by
  have hd := congrArg (fun x : Fin N → ℤ => x ∘ Tuple.sort (α := ℤᵒᵈ) x) he
  have hns : (n ∘ Tuple.sort (α := ℤᵒᵈ) n) = n :=
    Tuple.unique_antitone (σ := Tuple.sort (α := ℤᵒᵈ) n) (τ := Equiv.refl _)
      (Tuple.monotone_sort (α := ℤᵒᵈ) n) hn
  have hms : (m ∘ Tuple.sort (α := ℤᵒᵈ) m) = m :=
    Tuple.unique_antitone (σ := Tuple.sort (α := ℤᵒᵈ) m) (τ := Equiv.refl _)
      (Tuple.monotone_sort (α := ℤᵒᵈ) m) hm
  have hperm := Tuple.comp_perm_comp_sort_eq_comp_sort (α := ℤᵒᵈ) (f := m) (σ := σ)
  exact hns.symm.trans (hd.trans (hperm.trans hms))

/-- Orthogonality follows from disjoint Fourier permutation orbits. -/
theorem freeVector_orthogonal {n m : Fin N → ℤ} (hn : Antitone n) (hm : Antitone m)
    (hne : n ≠ m) : ⟪freeVector L n, freeVector L m⟫_ℂ = 0 := by
  rw [inner_free_symmetric n (freeVector_mem_sym m), freeVector_eq_modes, map_smul, map_sum]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sum, Finset.sum_apply,
    momUnitary_prodMode, lp.single_apply, Pi.single_apply]
  have hh (σ : Equiv.Perm (Fin N)) : n ≠ m ∘ σ := fun he => hne (labels_of_permutation hn hm σ he)
  simp [hh]

/-- A symmetric vector orthogonal to all decreasing free sums is zero:
sort each frequency, then recover every ordinary Fourier coefficient. -/
theorem free_family_total (F : ContactOperator.SymL2 L N)
    (hF : ∀ n : Fin N → ℤ, Antitone n → ⟪freeVector L n, (F : L2TN L N)⟫_ℂ = 0) : F = 0 := by
  apply Subtype.ext
  apply (momUnitary L N).injective
  apply lp.ext
  funext w
  let τ := Tuple.sort (α := ℤᵒᵈ) w
  let n := w ∘ τ
  have hn : Antitone n := Tuple.monotone_sort (α := ℤᵒᵈ) w
  have hz := hF n hn
  rw [inner_free_symmetric n F.property] at hz
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hstar : star (scale L N) ≠ 0 := star_ne_zero.mpr scale_ne_zero
  have hc0 := (mul_eq_zero.1 hz).resolve_left (mul_ne_zero hstar hc)
  have hs := (isSymm_iff_coeff (F : L2TN L N)).1
    ((ContactOperator.mem_SymL2_iff (F : L2TN L N)).1 F.property) τ w
  change (momUnitary L N (F : L2TN L N) : (Fin N → ℤ) → ℂ) w =
    (momUnitary L N (0 : L2TN L N) : (Fin N → ℤ) → ℂ) w
  rw [map_zero]
  simpa only [lp.coeFn_zero, Pi.zero_apply] using hs.symm.trans hc0

/-- The source label set of all decreasing integer tuples. -/
abbrev Label (N : ℕ) := {n : Fin N → ℤ // Antitone n}

/-- The same literal free vector in the original symmetric periodic Hilbert space. -/
def freeSym (n : Label N) : ContactOperator.SymL2 L N :=
  ⟨freeVector L n.val, freeVector_mem_sym n.val⟩

theorem freeSym_ne_zero (n : Label N) : freeSym (L := L) n ≠ 0 := by
  intro h
  exact freeVector_ne_zero n.val (congrArg (fun F : ContactOperator.SymL2 L N => (F : L2TN L N)) h)

theorem freeSym_orthogonal {n m : Label N} (hne : n ≠ m) :
    ⟪freeSym (L := L) n, freeSym (L := L) m⟫_ℂ = 0 :=
  freeVector_orthogonal n.property m.property (fun he => hne (Subtype.ext he))

/-- Completeness of the unnormalized free sums follows by symmetrizing the
ordinary Fourier basis, with repeated frequencies retained. -/
theorem free_family_complete :
    (Submodule.span ℂ (Set.range (freeSym (L := L) : Label N → ContactOperator.SymL2 L N))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro F hF
  apply free_family_total F
  intro n hn
  exact (Submodule.mem_orthogonal _ _).1 hF (freeSym (L := L) ⟨n, hn⟩)
    (Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩)

/-- Norm continuity on the full source parameter half-line, including its endpoint. -/
theorem continuedWave_continuousOn {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ContinuousOn (continuedWave (L := L) n hn) (Ici 0) := by
  have hpos : ContinuousOn (continuedWave (L := L) n hn) (Ioi 0) :=
    continuousOn_iff_continuous_domRestrict.2 (norm_continuous_extension (L := L) hn).1
  intro c hc
  change (0 : ℝ) ≤ c at hc
  rcases hc.eq_or_lt with h | h
  · subst c
    have hlim : ContinuousWithinAt (continuedWave (L := L) n hn) (Ioi 0) 0 := by
      rw [ContinuousWithinAt, continuedWave_zero]
      exact continuedWave_zero_limit hn
    have he : Ici (0 : ℝ) = insert 0 (Ioi 0) := by
      ext t
      simp only [mem_Ici, mem_insert_iff, mem_Ioi]
      constructor
      · intro ht
        rcases ht.eq_or_lt with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      · rintro (rfl | h)
        · exact le_rfl
        · exact h.le
    rw [he]
    exact hlim.insert
  · exact (hpos.continuousAt (Ioi_mem_nhds h)).continuousWithinAt

/-- Full R-7597E2D2 for every positive particle number. The interacting
nonvanishing/independence uses the printed separating-line Vandermonde
proof. Norm continuity uses the printed root/coefficient limits. The free
endpoint is given by `coe_freeVector`; its family is orthogonal and complete
by ordinary Fourier symmetrization in the original periodic Hilbert space. -/
theorem independence_and_free_limit :
    (∀ c : ℝ, ∀ hc : 0 < c,
      (∀ n : Label (N+1), (BetheH1.waveH1 (L := L) hc n.property).val ≠ 0) ∧
      LinearIndependent ℂ (fun n : Label (N+1) => (BetheH1.waveH1 (L := L) hc n.property).val)) ∧
    (∀ n : Label (N+1),
      ContinuousOn (continuedWave (L := L) n.val n.property) (Ici 0) ∧
      continuedWave (L := L) n.val n.property 0 = freeVector L n.val ∧
      Tendsto (continuedWave (L := L) n.val n.property) (𝓝[>] 0) (𝓝 (freeVector L n.val))) ∧
    (∀ n : Label (N+1), freeSym (L := L) n ≠ 0) ∧
    (∀ n m : Label (N+1), n ≠ m → ⟪freeSym (L := L) n, freeSym (L := L) m⟫_ℂ = 0) ∧
    (Submodule.span ℂ (Set.range (freeSym (L := L) : Label (N+1) → ContactOperator.SymL2 L (N+1)))).topologicalClosure = ⊤ := by
  refine ⟨?_, ?_, freeSym_ne_zero, ?_, free_family_complete⟩
  · intro c hc
    exact ⟨fun n => BetheVandermonde.wave_ne_zero hc n.property,
      BetheVandermonde.waves_independent hc⟩
  · intro n
    exact ⟨continuedWave_continuousOn n.property, continuedWave_zero n.property,
      continuedWave_zero_limit n.property⟩
  · intro n m hne
    exact freeSym_orthogonal hne

end QuantumNLS.BetheFreeFamily

#print axioms QuantumNLS.BetheFreeFamily.scale
#print axioms QuantumNLS.BetheFreeFamily.scale_ne_zero
#print axioms QuantumNLS.BetheFreeFamily.modes_plane
#print axioms QuantumNLS.BetheFreeFamily.freeVector_eq_modes
#print axioms QuantumNLS.BetheFreeFamily.freeVector_mem_sym
#print axioms QuantumNLS.BetheFreeFamily.inner_free_symmetric
#print axioms QuantumNLS.BetheFreeFamily.freeVector_ne_zero
#print axioms QuantumNLS.BetheFreeFamily.labels_of_permutation
#print axioms QuantumNLS.BetheFreeFamily.freeVector_orthogonal
#print axioms QuantumNLS.BetheFreeFamily.free_family_total
#print axioms QuantumNLS.BetheFreeFamily.Label
#print axioms QuantumNLS.BetheFreeFamily.freeSym
#print axioms QuantumNLS.BetheFreeFamily.freeSym_ne_zero
#print axioms QuantumNLS.BetheFreeFamily.freeSym_orthogonal
#print axioms QuantumNLS.BetheFreeFamily.free_family_complete
#print axioms QuantumNLS.BetheFreeFamily.continuedWave_continuousOn
#print axioms QuantumNLS.BetheFreeFamily.independence_and_free_limit

/- Full-node proof-route inspection, with no new mathematical premise. -/
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let forbidden : Array Lean.Name := #[
    ``QuantumNLS.BetheEigenGlobal.planeCharacter,
    ``QuantumNLS.BetheEigenGlobal.planeCharacters_independent,
    ``QuantumNLS.BetheEigenGlobal.analyticAt_coordinateAnsatz,
    ``QuantumNLS.BetheEigenGlobal.coordinateAnsatz_chamber_nonzero,
    ``QuantumNLS.BetheEigenGlobal.wave_ne_zero,
    ``QuantumNLS.BetheEigenGlobal.chamber_ansatz_independent,
    ``QuantumNLS.BetheEigenGlobal.waves_independent,
    ``linearIndependent_monoidHom]
  let mut pending := #[``QuantumNLS.BetheFreeFamily.independence_and_free_limit,
    ``QuantumNLS.BetheWaveContinuity.coe_freeVector]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if forbidden.contains n then
        throwError "Free-family route reached forbidden alternate independence proof: {n}"
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheVandermonde.separating_direction,
      ``Matrix.det_vandermonde,
      ``QuantumNLS.BetheWaveContinuity.coefficient_tendsto_one,
      ``QuantumNLS.BetheZeroLimitLiteral.first_limit_literal,
      ``QuantumNLS.BetheFreeFamily.freeVector_eq_modes,
      ``QuantumNLS.PhysicalEnergy.momUnitary,
      ``QuantumNLS.CollisionTrace.momUnitary_prodMode,
      ``QuantumNLS.BetheFreeFamily.free_family_total,
      ``QuantumNLS.BetheFreeFamily.labels_of_permutation,
      ``QuantumNLS.BetheFreeFamily.continuedWave_continuousOn] do
    unless seen.contains n do
      throwError "Full R7597 route missed required step: {n}"
  Lean.logInfo m!"Free-family route PASS: {seen.size} transitive constants; printed Vandermonde, root limits, half-line norm continuity, literal symmetrized Fourier modes, disjoint orbits and dense span reached; eight alternate independence declarations excluded."
