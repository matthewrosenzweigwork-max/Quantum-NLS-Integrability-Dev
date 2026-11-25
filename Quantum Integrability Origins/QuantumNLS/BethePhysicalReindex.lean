import QuantumNLS.BetheFaceEnumeration

/-! Remove the two inner averages in the actual physical source action.
This is a measure/permutation calculation; no face cancellation is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BethePhysicalReindex
open TensorCarrier TensorPlacements PhysicalTensor BetheIntegralOperator
open BetheCompressedKernel BetheBlockSlice BetheHigherPlacement
open BetheGeneralSliceEndpoints BetheFaceEnumeration
variable (L : ℝ) [Fact (0 < L)]

theorem append_block {m q : ℕ} {α : Type*} (t : Fin m → α) (s : Fin q → α)
    (π : Equiv.Perm (Fin m)) (ρ : Equiv.Perm (Fin q)) :
    Fin.append t s ∘ blockPerm π ρ = Fin.append (t ∘ π) (s ∘ ρ) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem slice_weighted {m q : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (k : ι → Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ)) (x : Fin (m+q) → AddCircle L) :
    slice L m q (weightedKernel a k) F x = ∑ i, a i * slice L m q (k i) F x := by
  unfold slice weightedKernel
  simp only [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_slice L m q (k i) F x).const_mul (a i))]
  simp only [integral_const_mul]

/-- Both changes of integration variables use the actual mass-L product
measure. Symmetry is a property of the input, not an action premise. -/
theorem slice_permuted {m q : ℕ} (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ))
    (hF : ∀ y (π : Equiv.Perm (Fin (m+q))), F (y ∘ π) = F y)
    (σ τ : Equiv.Perm (Fin m)) (x : Fin (m+q) → AddCircle L) :
    slice L m q (permutedKernel L m k σ τ) F x =
      slice L m q k F (coordPerm (blockPerm σ 1) x) := by
  let s : Fin q → AddCircle L := fun i => x (Fin.natAdd m i)
  have he (t : Fin m → AddCircle L) :
      F (Fin.append (t ∘ τ.symm) s) = F (Fin.append t s) := by
    simpa only [append_block, Equiv.Perm.coe_one, Function.comp_id] using
      hF (Fin.append t s) (blockPerm τ.symm 1)
  have hm := (measurePreserving_coordPerm (L := L) τ).integral_comp'
    (fun t => k.fn ((fun i => x (Fin.castAdd q (σ i))),t) *
      F (Fin.append (t ∘ τ.symm) s))
  have hc (t : Fin m → AddCircle L) : (coordPerm τ t) ∘ τ.symm = t := by
    ext i
    simp only [Function.comp_apply, coordPerm_apply, Equiv.apply_symm_apply]
  simp only [hc, he, torusPiMeasure, ← volume_pi] at hm
  change (∫ t, k.fn ((fun i => x (Fin.castAdd q (σ i))), coordPerm τ t) * F (Fin.append t s) ∂torusPiMeasure L m) = _
  simpa only [slice, coordPerm_apply, blockPerm_castAdd,
    blockPerm_natAdd, Equiv.Perm.one_apply, s, torusPiMeasure, ← volume_pi] using hm

theorem slice_inputAverage {m q : ℕ} (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ))
    (hF : ∀ y (π : Equiv.Perm (Fin (m+q))), F (y ∘ π) = F y)
    (x : Fin (m+q) → AddCircle L) :
    slice L m q (inputAverage L m k) F x = slice L m q k F x := by
  classical
  rw [inputAverage, slice_weighted]
  simp_rw [slice_permuted L k F hF]
  have hx : coordPerm (blockPerm (1 : Equiv.Perm (Fin m)) (1 : Equiv.Perm (Fin q))) x = x := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [coordPerm_apply]
  rw [hx]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have hn : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

theorem slice_compressed {m q : ℕ}
    (F : C(Fin (m+q) → AddCircle L, ℂ))
    (hF : ∀ y (π : Equiv.Perm (Fin (m+q))), F (y ∘ π) = F y)
    (z : ℂ) (x : Fin (m+q) → AddCircle L) :
    slice L m q (compressedKernel L m z) F x =
      (m.factorial : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin m),
        slice L m q (BetheTensorSlice.sumKernel
          (BetheTransferOperators.plusKernel L m z)
          (BetheTransferOperators.minusKernel L m z)) F
            (coordPerm (blockPerm σ 1) x) := by
  rw [compressedKernel, outputAverage, slice_weighted]
  simp_rw [slice_permuted L _ F hF, slice_inputAverage L _ F hF]
  rw [Finset.mul_sum]

omit [Fact (0 < L)] in
theorem coordPerm_block_comp {m q : ℕ} (π : Equiv.Perm (Fin (m+q)))
    (σ : Equiv.Perm (Fin m)) (x : Fin (m+q) → AddCircle L) :
    coordPerm (blockPerm σ (1 : Equiv.Perm (Fin q))) (coordPerm π x) =
      coordPerm (π * blockPerm σ 1) x := rfl

/-- The outer full permutation sum absorbs the output P_m average, with
its exact 1/m!. The input P_m was removed by measure preservation above. -/
theorem sum_compressed {m q : ℕ}
    (F : C(Fin (m+q) → AddCircle L, ℂ))
    (hF : ∀ y (π : Equiv.Perm (Fin (m+q))), F (y ∘ π) = F y)
    (z : ℂ) (x : Fin (m+q) → AddCircle L) :
    (∑ π : Equiv.Perm (Fin (m+q)),
      slice L m q (compressedKernel L m z) F (coordPerm π x)) =
      ∑ π : Equiv.Perm (Fin (m+q)),
        slice L m q (BetheTensorSlice.sumKernel
          (BetheTransferOperators.plusKernel L m z)
          (BetheTransferOperators.minusKernel L m z)) F (coordPerm π x) := by
  classical
  simp_rw [slice_compressed L F hF, coordPerm_block_comp]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs (σ : Equiv.Perm (Fin m)) :
      (∑ π : Equiv.Perm (Fin (m+q)), slice L m q (BetheTensorSlice.sumKernel
        (BetheTransferOperators.plusKernel L m z)
        (BetheTransferOperators.minusKernel L m z)) F (coordPerm (π * blockPerm σ 1) x)) =
      ∑ π : Equiv.Perm (Fin (m+q)), slice L m q (BetheTensorSlice.sumKernel
        (BetheTransferOperators.plusKernel L m z)
        (BetheTransferOperators.minusKernel L m z)) F (coordPerm π x) :=
    Equiv.sum_comp (Equiv.mulRight (blockPerm σ 1))
      (fun π => slice L m q (BetheTensorSlice.sumKernel
        (BetheTransferOperators.plusKernel L m z)
        (BetheTransferOperators.minusKernel L m z)) F (coordPerm π x))
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have hn : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

/-- The literal sum of the two uncompressed physical kernels. -/
def rawBlock (m : ℕ) (z : ℂ) : Kernel (torusPiMeasure L m) :=
  BetheTensorSlice.sumKernel (BetheTransferOperators.plusKernel L m z)
    (BetheTransferOperators.minusKernel L m z)

/-- Coercion of the actual completed-tensor permutation sum. -/
theorem coe_permutation_sum {m q : ℕ} (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ)) :
    (∑ π : Equiv.Perm (Fin (m+q)), physPerm π (sliceMap L m q k F))
      =ᵐ[torusPiMeasure L (m+q)]
      fun x => ∑ π : Equiv.Perm (Fin (m+q)), slice L m q k F (coordPerm π x) := by
  have ha : ∀ᵐ x ∂torusPiMeasure L (m+q), ∀ π : Equiv.Perm (Fin (m+q)),
      physPerm π (sliceMap L m q k F) x = slice L m q k F (coordPerm π x) := by
    rw [ae_all_iff]
    intro π
    filter_upwards [coeFn_physPerm π (sliceMap L m q k F),
      (measurePreserving_coordPerm (L := L) π).quasiMeasurePreserving.ae
        (coe_sliceMap L m q k F)] with x hx hy
    exact hx.trans hy
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun π => physPerm π (sliceMap L m q k F)), ha] with x hx hy
  rw [hx]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun π _ => hy π)

/-- Actual source transfer term with both P_m averages eliminated. The exact
remaining coefficient is c^m/q!, before restricting to ordered fibers. -/
theorem source_transferTerm_raw_ae (m q : ℕ) (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {n : Fin (m+q) → ℤ} (hn : Antitone n) (z : ℂ) :
    physUnitary ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,by omega⟩
      (sourceVector L hc hn)).1) =ᵐ[torusPiMeasure L (m+q)]
      fun x => ((c : ℂ)^m * (q.factorial : ℂ)⁻¹) *
        ∑ π : Equiv.Perm (Fin (m+q)),
          slice L m q (rawBlock L m z) (sourceInput L hc hn) (coordPerm π x) := by
  rw [source_transferTerm L m q hm hc hn z, smul_smul, coefficient_normalization]
  filter_upwards [Lp.coeFn_smul ((c : ℂ)^m * (q.factorial : ℂ)⁻¹)
    (∑ π : Equiv.Perm (Fin (m+q)), physPerm π
      (sliceMap L m q (compressedKernel L m z) (sourceInput L hc hn))),
    coe_permutation_sum L (compressedKernel L m z) (sourceInput L hc hn)] with x hx hy
  rw [hx, Pi.smul_apply, smul_eq_mul, hy]
  congr 1
  exact sum_compressed L (sourceInput L hc hn)
    (fun y π => BetheExtension.torusExtension_permute L c n y π) z x

/-- Spectator permutations leave every raw slice unchanged. -/
theorem slice_spectator {m q : ℕ} (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ))
    (hF : ∀ y (π : Equiv.Perm (Fin (m+q))), F (y ∘ π) = F y)
    (ρ : Equiv.Perm (Fin q)) (x : Fin (m+q) → AddCircle L) :
    slice L m q k F (coordPerm (blockPerm (1 : Equiv.Perm (Fin m)) ρ) x) =
      slice L m q k F x := by
  unfold slice
  apply integral_congr_ae
  filter_upwards with t
  simp only [coordPerm_apply, blockPerm_castAdd, blockPerm_natAdd, Equiv.Perm.one_apply]
  congr 1
  have he := hF (Fin.append t (fun i : Fin q => x (Fin.natAdd m i))) (blockPerm 1 ρ)
  rw [append_block] at he
  exact he

open BetheTransferKernelAdjoint BetheWeakGradient

/-- Strict support in either raw branch forces the output block order. -/
theorem rawBlock_zero_of_not_strictAnti {m : ℕ} (z : ℂ)
    (x y : Fin m → AddCircle L) (hx : ¬ StrictAnti (representatives L x)) :
    (rawBlock L m z).fn (x,y) = 0 := by
  classical
  have hp : ¬ PlusOrder L (representatives L x) (representatives L y) := by
    intro h
    exact hx (BetheFiniteNAction.minusOrder_input_strictAnti h)
  have hm : ¬ MinusOrder L (representatives L x) (representatives L y) := by
    intro h
    exact hx (BetheFiniteNAction.plusOrder_input_strictAnti h)
  simp only [rawBlock, BetheTensorSlice.sumKernel, BetheTransferOperators.plusKernel,
    BetheTransferOperators.minusKernel, rawPlus, rawMinus, hp, hm, ↓reduceIte, add_zero]

/-- On the physical output chamber, every unsorted selected output contributes
exactly zero, before any integral is evaluated. -/
theorem rawSlice_zero_of_not_ordered {m q : ℕ} (z : ℂ)
    (F : C(Fin (m+q) → AddCircle L, ℂ)) (x : Fin (m+q) → AddCircle L)
    (hx : StrictAnti (representatives L x)) (π : Equiv.Perm (Fin (m+q)))
    (hπ : ¬ StrictMono (fun i : Fin m => π (Fin.castAdd q i))) :
    slice L m q (rawBlock L m z) F (coordPerm π x) = 0 := by
  have ho : ¬ StrictAnti (representatives L (fun i : Fin m => coordPerm π x (Fin.castAdd q i))) := by
    intro h
    apply hπ
    intro i j hij
    by_contra hn
    have hb := hx.antitone (le_of_not_gt hn)
    exact (not_le_of_gt (h hij)) hb
  unfold slice
  simp_rw [rawBlock_zero_of_not_strictAnti L z _ _ ho, zero_mul]
  exact integral_zero _ _

/-- Every ordered fiber evaluates to the same raw integral. This is the
geometric spectator reindexing behind its q! multiplicity. -/
theorem rawSlice_orderedFiber {m q : ℕ} (z : ℂ)
    (F : C(Fin (m+q) → AddCircle L, ℂ))
    (hF : ∀ y (π : Equiv.Perm (Fin (m+q))), F (y ∘ π) = F y)
    (x : Fin (m+q) → AddCircle L) (S : PlacementSubset m q) (π : OrderedFiber S) :
    slice L m q (rawBlock L m z) F (coordPerm π.1.1 x) =
      slice L m q (rawBlock L m z) F (coordPerm (mergePermutation S) x) := by
  obtain ⟨ρ, rfl⟩ := (orderedFiberEquiv S).surjective π
  change slice L m q (rawBlock L m z) F
    (coordPerm (mergePermutation S * blockPerm 1 ρ) x) = _
  exact slice_spectator L (rawBlock L m z) F hF ρ (coordPerm (mergePermutation S) x)

/-- Reindex the actual raw output permutation sum on a strict physical
chamber. Each selected subset occurs exactly q! times, with no m! left. -/
theorem sum_raw_by_subset {m q : ℕ} (z : ℂ)
    (F : C(Fin (m+q) → AddCircle L, ℂ))
    (hF : ∀ y (π : Equiv.Perm (Fin (m+q))), F (y ∘ π) = F y)
    (x : Fin (m+q) → AddCircle L) (hx : StrictAnti (representatives L x)) :
    (∑ π : Equiv.Perm (Fin (m+q)), slice L m q (rawBlock L m z) F (coordPerm π x)) =
      (q.factorial : ℂ) * ∑ S : PlacementSubset m q,
        slice L m q (rawBlock L m z) F (coordPerm (mergePermutation S) x) := by
  classical
  rw [← Fintype.sum_fiberwise (placementSubsetOfPerm (p := m) (q := q)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun π : PlacementFiber S => StrictMono (fun i : Fin m => π.1 (Fin.castAdd q i)))
    (fun π : PlacementFiber S => slice L m q (rawBlock L m z) F (coordPerm π.1 x))]
  have hz : (∑ π : {π : PlacementFiber S // ¬ StrictMono (fun i : Fin m => π.1 (Fin.castAdd q i))},
      slice L m q (rawBlock L m z) F (coordPerm π.1.1 x)) = 0 := by
    apply Finset.sum_eq_zero
    intro π _
    exact rawSlice_zero_of_not_ordered L z F x hx π.1.1 π.2
  rw [hz, add_zero]
  simp_rw [rawSlice_orderedFiber L z F hF]
  exact sum_orderedFiber_face S _

/-- Actual positive-c source action in every positive transfer degree,
restricted almost everywhere to the strict physical output chamber. -/
theorem source_transferTerm_subset_ae (m q : ℕ) (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {n : Fin (m+q) → ℤ} (hn : Antitone n) (z : ℂ) :
    ∀ᵐ x ∂torusPiMeasure L (m+q), StrictAnti (representatives L x) →
      physUnitary ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,by omega⟩
        (sourceVector L hc hn)).1) x = (c : ℂ)^m *
        ∑ S : PlacementSubset m q,
          slice L m q (rawBlock L m z) (sourceInput L hc hn) (coordPerm (mergePermutation S) x) := by
  filter_upwards [source_transferTerm_raw_ae L m q hm hc hn z] with x he hx
  rw [he, sum_raw_by_subset L z (sourceInput L hc hn)
    (fun y π => BetheExtension.torusExtension_permute L c n y π) x hx]
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  field_simp

/-- Literal real-coordinate raw slice, retaining every spectator and the
original, unnormalized positive-c Bethe source. -/
def sourceRawCube {m q : ℕ} {c : ℝ} (_hc : 0 < c) {n : Fin (m+q) → ℤ}
    (_hn : Antitone n) (z : ℂ) (x : Fin (m+q) → ℝ) : ℂ :=
  ∫ y, rawKernel L z (fun i : Fin m => x (Fin.castAdd q i)) y *
    BetheExtension.symmetricExtension L c n (Fin.append y (fun i : Fin q => x (Fin.natAdd m i)))
    ∂cubeMeasure m L

/-- Exact torus-to-cube conversion for every degree and every spectator
configuration. The measure has mass L^m, with no probability rescaling. -/
theorem rawSlice_source_cube {m q : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin (m+q) → ℤ} (hn : Antitone n) (z : ℂ) (x : Fin (m+q) → AddCircle L) :
    slice L m q (rawBlock L m z) (sourceInput L hc hn) x =
      sourceRawCube L hc hn z (representatives L x) := by
  let X : Fin m → ℝ := fun i => representatives L x (Fin.castAdd q i)
  let s : Fin q → ℝ := fun i => representatives L x (Fin.natAdd m i)
  have he (t : Fin m → AddCircle L) :
      sourceInput L hc hn (Fin.append t (fun i : Fin q => x (Fin.natAdd m i))) =
      BetheExtension.symmetricExtension L c n (Fin.append (representatives L t) s) := by
    change BetheExtension.symmetricExtension L c n _ = _
    congr 1
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [representatives, s]
  have hm : Measurable (fun y : Fin m → ℝ => rawKernel L z X y *
      BetheExtension.symmetricExtension L c n (Fin.append y s)) :=
    (((BetheTransferOperators.measurable_rawPlus m L z).add
      (BetheTransferOperators.measurable_rawMinus m L z)).comp
        (measurable_const.prodMk measurable_id)).mul
      ((BetheExtension.continuous_symmetricExtension L c n).comp (by fun_prop)).measurable
  unfold slice
  simp only [rawBlock, BetheTensorSlice.sumKernel, BetheTransferOperators.plusKernel,
    BetheTransferOperators.minusKernel, he]
  change (∫ y, rawKernel L z X (representatives L y) *
    BetheExtension.symmetricExtension L c n (Fin.append (representatives L y) s)) = _
  rw [volume_pi]
  exact BetheFiniteNAction.integral_representatives L _ hm

/-- The physical degree-m action as the actual real-cube subset integrals,
with exactly c^m per subset, at almost every ordered output. -/
theorem source_transferTerm_cube_ae (m q : ℕ) (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {n : Fin (m+q) → ℤ} (hn : Antitone n) (z : ℂ) :
    ∀ᵐ x ∂torusPiMeasure L (m+q), StrictAnti (representatives L x) →
      physUnitary ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,by omega⟩
        (sourceVector L hc hn)).1) x = (c : ℂ)^m *
        ∑ S : PlacementSubset m q,
          sourceRawCube L hc hn z (representatives L (coordPerm (mergePermutation S) x)) := by
  filter_upwards [source_transferTerm_subset_ae L m q hm hc hn z] with x he hx
  rw [he hx]
  simp_rw [rawSlice_source_cube L hc hn]

end QuantumNLS.BethePhysicalReindex

#print axioms QuantumNLS.BethePhysicalReindex.append_block
#print axioms QuantumNLS.BethePhysicalReindex.slice_weighted
#print axioms QuantumNLS.BethePhysicalReindex.slice_permuted
#print axioms QuantumNLS.BethePhysicalReindex.slice_inputAverage
#print axioms QuantumNLS.BethePhysicalReindex.slice_compressed
#print axioms QuantumNLS.BethePhysicalReindex.coordPerm_block_comp
#print axioms QuantumNLS.BethePhysicalReindex.sum_compressed
#print axioms QuantumNLS.BethePhysicalReindex.rawBlock
#print axioms QuantumNLS.BethePhysicalReindex.coe_permutation_sum
#print axioms QuantumNLS.BethePhysicalReindex.source_transferTerm_raw_ae
#print axioms QuantumNLS.BethePhysicalReindex.slice_spectator
#print axioms QuantumNLS.BethePhysicalReindex.rawBlock_zero_of_not_strictAnti
#print axioms QuantumNLS.BethePhysicalReindex.rawSlice_zero_of_not_ordered
#print axioms QuantumNLS.BethePhysicalReindex.rawSlice_orderedFiber
#print axioms QuantumNLS.BethePhysicalReindex.sum_raw_by_subset
#print axioms QuantumNLS.BethePhysicalReindex.source_transferTerm_subset_ae
#print axioms QuantumNLS.BethePhysicalReindex.sourceRawCube
#print axioms QuantumNLS.BethePhysicalReindex.rawSlice_source_cube
#print axioms QuantumNLS.BethePhysicalReindex.source_transferTerm_cube_ae
