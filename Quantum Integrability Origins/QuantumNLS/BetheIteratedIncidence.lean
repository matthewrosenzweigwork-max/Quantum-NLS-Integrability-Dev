import QuantumNLS.BetheMultipleIncidence

/-! Pointwise enumeration allowing repeated values inside either input block.
The multiplicity divides out value-preserving within-block permutations.
This applies to tuples after endpoint substitutions; it does not identify
which incidences occur in the iterated physical integral. -/
noncomputable section
open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheIteratedIncidence
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts BetheRectangleIncidence

abbrev Preserving {k : ℕ} (x : Fin k → ℝ) :=
  {π : Equiv.Perm (Fin k) // x ∘ π = x}

abbrev Sorting {k : ℕ} (x : Fin k → ℝ) :=
  {σ : Equiv.Perm (Fin k) // Antitone (x ∘ σ.symm)}

/-- Sorting permutations have exactly the full value stabilizer multiplicity,
including repeated moving and repeated spectator labels. -/
theorem card_sorting {k : ℕ} (x : Fin k → ℝ) :
    Fintype.card (Sorting x) = Fintype.card (Preserving x) := by
  classical
  let τ := (Tuple.sort (α := ℝᵒᵈ) x).symm
  have hτ : Antitone (x ∘ τ.symm) := BetheExtension.decreasing_antitone x
  let f : Sorting x → Preserving x := fun σ =>
    ⟨τ.symm * σ.1, by
      ext i
      have he := congrFun (Tuple.unique_antitone hτ σ.2) (σ.1 i)
      simpa only [Function.comp_apply, Equiv.Perm.mul_apply,
        Equiv.symm_apply_apply] using he⟩
  apply Fintype.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro a b h
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val h)
  · intro π
    have hh : Antitone (x ∘ (τ * π.1).symm) := by
      have he : x ∘ (τ * π.1).symm = x ∘ τ.symm := by
        ext i
        change x (π.1.symm (τ.symm i)) = _
        have hv := congrFun π.2 (π.1.symm (τ.symm i))
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hv.symm
      rw [he]
      exact hτ
    refine ⟨⟨τ * π.1, hh⟩, ?_⟩
    apply Subtype.ext
    change τ.symm * (τ * π.1) = π.1
    exact inv_mul_cancel_left τ π.1

/-- A chart's within-block value stabilizers give all its sorting
permutations. The constructor retains both original input blocks. -/
def assemble {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ) :
    ({S : PlacementSubset m q // y ∈ chartSet S s} ×
      (Preserving y × Preserving s)) → Sorting (Fin.append y s) := fun a =>
  ⟨mergePermutation a.1.1 * blockPerm a.2.1.1 a.2.2.1, by
    have he : Fin.append y s ∘
        (mergePermutation a.1.1 * blockPerm a.2.1.1 a.2.2.1).symm =
        mergeChart a.1.1 y s := by
      ext i
      let j := (mergePermutation a.1.1).symm i
      change Fin.append y s ((blockPerm a.2.1.1 a.2.2.1).symm j) = Fin.append y s j
      have hy (t : Fin m) : y (a.2.1.1.symm t) = y t := by
        have h := congrFun a.2.1.2 (a.2.1.1.symm t)
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h.symm
      have hs (t : Fin q) : s (a.2.2.1.symm t) = s t := by
        have h := congrFun a.2.2.2 (a.2.2.1.symm t)
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h.symm
      change Fin.append y s ((blockPerm a.2.1.1 a.2.2.1)⁻¹ j) = _
      rw [blockPerm_inv]
      refine Fin.addCases (fun t => ?_) (fun t => ?_) j <;> simpa using (by first | exact hy _ | exact hs _)
    rw [he]
    exact a.1.2⟩

/-- Every sorting permutation yields an actual incident shuffle even for
weakly ordered blocks. Repeated-value permutations are proved to preserve
the blocks; they are not counted as additional charts. -/
theorem sorting_factorization {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : Antitone y) (hs : Antitone s) (σ : Sorting (Fin.append y s)) :
    ∃ S : {S : PlacementSubset m q // y ∈ chartSet S s},
      ∃ π : Preserving y, ∃ ρ : Preserving s,
        σ.1 = mergePermutation S.1 * blockPerm π.1 ρ.1 := by
  classical
  let S := placementSubsetOfPerm (p := m) (q := q) σ.1
  have hm : (firstPositions (p := m) (q := q)).map (mergePermutation S).toEmbedding =
      (firstPositions (p := m) (q := q)).map σ.1.toEmbedding :=
    congrArg Subtype.val (mergePermutation_image S)
  obtain ⟨π,ρ,hσ⟩ := exists_rightBlock_of_same_firstImage (mergePermutation S) σ.1 hm
  have hl (i : Fin m) : σ.1.symm (mergePermutation S (Fin.castAdd q i)) = Fin.castAdd q (π.symm i) := by
    rw [hσ]
    change (blockPerm π ρ)⁻¹ ((mergePermutation S).symm (mergePermutation S (Fin.castAdd q i))) = _
    simp [blockPerm_inv]
  have hr (i : Fin q) : σ.1.symm (mergePermutation S (Fin.natAdd m i)) = Fin.natAdd m (ρ.symm i) := by
    rw [hσ]
    change (blockPerm π ρ)⁻¹ ((mergePermutation S).symm (mergePermutation S (Fin.natAdd m i))) = _
    simp [blockPerm_inv]
  have hπa : Antitone (y ∘ π.symm) := by
    intro i j hij
    have h := σ.2 (show mergePermutation S (Fin.castAdd q i) ≤ mergePermutation S (Fin.castAdd q j) by
      simpa only [mergePermutation_selected, OrderEmbedding.le_iff_le] using hij)
    simpa only [Function.comp_apply, hl, Fin.append_left] using h
  have hρa : Antitone (s ∘ ρ.symm) := by
    intro i j hij
    have h := σ.2 (show mergePermutation S (Fin.natAdd m i) ≤ mergePermutation S (Fin.natAdd m j) by
      simpa only [mergePermutation_spectator, OrderEmbedding.le_iff_le] using hij)
    simpa only [Function.comp_apply, hr, Fin.append_right] using h
  have hp : y ∘ π.symm = y := Tuple.unique_antitone hπa (show Antitone (y ∘ Equiv.refl _) from hy)
  have hρ : s ∘ ρ.symm = s := Tuple.unique_antitone hρa (show Antitone (s ∘ Equiv.refl _) from hs)
  have hp' : y ∘ π = y := by
    ext i
    have h := congrFun hp (π i)
    simpa using h.symm
  have hρ' : s ∘ ρ = s := by
    ext i
    have h := congrFun hρ (ρ i)
    simpa using h.symm
  have he : Fin.append y s ∘ σ.1.symm = mergeChart S y s := by
    ext i
    obtain ⟨j,rfl⟩ := (mergePermutation S).surjective i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · simp only [Function.comp_apply, hl, Fin.append_left, mergeChart, Equiv.symm_apply_apply]
      exact congrFun hp a
    · simp only [Function.comp_apply, hr, Fin.append_right, mergeChart, Equiv.symm_apply_apply]
      exact congrFun hρ a
  exact ⟨⟨S, by change Antitone (mergeChart S y s); rw [← he]; exact σ.2⟩,
    ⟨π,hp'⟩,⟨ρ,hρ'⟩,hσ⟩

/-- Complete enumeration, with the exact repeated-label multiplicity. -/
theorem assemble_bijective {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : Antitone y) (hs : Antitone s) : Function.Bijective (assemble y s) := by
  classical
  constructor
  · rintro ⟨S,π,ρ⟩ ⟨T,π',ρ'⟩ he
    have hv := congrArg Subtype.val he
    change mergePermutation S.1 * blockPerm π.1 ρ.1 =
      mergePermutation T.1 * blockPerm π'.1 ρ'.1 at hv
    have him (U : PlacementSubset m q) (a : Equiv.Perm (Fin m)) (b : Equiv.Perm (Fin q)) :
        placementSubsetOfPerm (mergePermutation U * blockPerm a b) = U := by
      apply Subtype.ext
      change (firstPositions (p := m) (q := q)).map (mergePermutation U * blockPerm a b).toEmbedding = U.1
      rw [show (mergePermutation U * blockPerm a b).toEmbedding =
        (blockPerm a b).toEmbedding.trans (mergePermutation U).toEmbedding by rfl,
        ← Finset.map_map, firstPositions_map_blockPerm]
      exact congrArg Subtype.val (mergePermutation_image U)
    have hST : S = T := Subtype.ext ((him S.1 π.1 ρ.1).symm.trans
      ((congrArg (placementSubsetOfPerm (p := m) (q := q)) hv).trans (him T.1 π'.1 ρ'.1)))
    subst T
    have hb := mul_left_cancel hv
    have hp : π = π' := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      apply Fin.castAdd_injective m q
      simpa only [blockPerm_castAdd] using congrArg (fun e : Equiv.Perm (Fin (m+q)) => e (Fin.castAdd q i)) hb
    have hr : ρ = ρ' := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      apply (Fin.natAddEmb m).injective
      simpa only [blockPerm_natAdd, Fin.natAddEmb_apply] using congrArg (fun e : Equiv.Perm (Fin (m+q)) => e (Fin.natAdd m i)) hb
    subst π'; subst ρ'; rfl
  · intro σ
    obtain ⟨S,π,ρ,he⟩ := sorting_factorization y s hy hs σ
    exact ⟨(S,π,ρ),Subtype.ext he.symm⟩

/-- General factorial ratio, stated without division: actual chart count
multiplied by both within-block stabilizer sizes is the full stabilizer.
Unlike 2^k this includes moving/moving and higher multiple collisions. -/
theorem card_incidentCharts_with_repetitions {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : Antitone y) (hs : Antitone s) :
    (incidentCharts y s).card *
      (∏ v ∈ Finset.univ.image y, (Fintype.card {i : Fin m // y i = v}).factorial) *
      (∏ v ∈ Finset.univ.image s, (Fintype.card {j : Fin q // s j = v}).factorial) =
      ∏ v ∈ Finset.univ.image (Fin.append y s),
        (Fintype.card {i : Fin (m+q) // Fin.append y s i = v}).factorial := by
  classical
  have he := Fintype.card_congr (Equiv.ofBijective (assemble y s) (assemble_bijective y s hy hs))
  rw [card_sorting] at he
  simp only [Fintype.card_prod, Preserving] at he
  rw [DomMulAct.stabilizer_card', DomMulAct.stabilizer_card',
    DomMulAct.stabilizer_card'] at he
  simpa only [Fintype.card_subtype, incidentCharts, mul_assoc] using he

/-- The exact chart multiplicity is an integer factorial ratio. Positivity
of factorials proves that the denominator never vanishes. -/
theorem card_incidentCharts_ratio {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : Antitone y) (hs : Antitone s) :
    (incidentCharts y s).card =
      (∏ v ∈ Finset.univ.image (Fin.append y s),
        (Fintype.card {i : Fin (m+q) // Fin.append y s i = v}).factorial) /
      ((∏ v ∈ Finset.univ.image y, (Fintype.card {i : Fin m // y i = v}).factorial) *
        ∏ v ∈ Finset.univ.image s, (Fintype.card {j : Fin q // s j = v}).factorial) := by
  classical
  apply Nat.eq_div_of_mul_eq_right
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun _ _ => Nat.factorial_ne_zero _))
      (Finset.prod_ne_zero_iff.mpr (fun _ _ => Nat.factorial_ne_zero _)))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    card_incidentCharts_with_repetitions y s hy hs

/-- Weakly ordered blocks always have an incident chart, even on corners. -/
theorem exists_chart_weak {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : Antitone y) (hs : Antitone s) : ∃ S, y ∈ chartSet S s := by
  let σ : Sorting (Fin.append y s) :=
    ⟨(Tuple.sort (α := ℝᵒᵈ) (Fin.append y s)).symm, BetheExtension.decreasing_antitone _⟩
  obtain ⟨S,_,_,_⟩ := sorting_factorization y s hy hs σ
  exact ⟨S.1,S.2⟩

/-- In a fully coincident cluster every shuffle is incident. Its binomial
multiplicity replaces the strict-block 2^k formula. -/
theorem card_incidentCharts_constant (m q : ℕ) (v : ℝ) :
    (incidentCharts (fun _ : Fin m => v) (fun _ : Fin q => v)).card =
      Nat.choose (m+q) m := by
  classical
  have ha (S : PlacementSubset m q) :
      (fun _ : Fin m => v) ∈ chartSet S (fun _ : Fin q => v) := by
    intro i j _
    change Fin.append (fun _ : Fin m => v) (fun _ : Fin q => v) _ ≤
      Fin.append (fun _ : Fin m => v) (fun _ : Fin q => v) _
    have hc (k : Fin (m+q)) : Fin.append (fun _ : Fin m => v) (fun _ : Fin q => v) k = v := by
      refine Fin.addCases (fun _ => by simp) (fun _ => by simp) k
    rw [hc,hc]
  have he : incidentCharts (fun _ : Fin m => v) (fun _ : Fin q => v) = Finset.univ := by
    ext S
    simp [incidentCharts,ha S]
  rw [he,Finset.card_univ,card_placementSubset]

end QuantumNLS.BetheIteratedIncidence

#print axioms QuantumNLS.BetheIteratedIncidence.Preserving
#print axioms QuantumNLS.BetheIteratedIncidence.Sorting
#print axioms QuantumNLS.BetheIteratedIncidence.card_sorting
#print axioms QuantumNLS.BetheIteratedIncidence.assemble
#print axioms QuantumNLS.BetheIteratedIncidence.sorting_factorization
#print axioms QuantumNLS.BetheIteratedIncidence.assemble_bijective
#print axioms QuantumNLS.BetheIteratedIncidence.card_incidentCharts_with_repetitions
#print axioms QuantumNLS.BetheIteratedIncidence.card_incidentCharts_ratio
#print axioms QuantumNLS.BetheIteratedIncidence.exists_chart_weak
#print axioms QuantumNLS.BetheIteratedIncidence.card_incidentCharts_constant

