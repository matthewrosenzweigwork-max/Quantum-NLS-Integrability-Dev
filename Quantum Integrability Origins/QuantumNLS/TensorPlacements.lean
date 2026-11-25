/-
QuantumNLS.TensorPlacements — bounded normalized placements (DEF-041).

Source: chapters/local/quantum_periods.tex:15, pinned PR11 source commit
3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f.

This module imports the completed Hilbert tensor powers, symmetric sectors,
permutation representation, split isometry, and completed tensor maps from
TensorCarrier.  It first constructs the zero extension of a bounded kernel on
Sym^p H, then its placement in the first p slots.  The permutation average
uses 1/N!; each p-subset has multiplicity p! (N-p)!, so this is the
permutation-average form of the source's binomial normalization.  The
subset-fiber count and equality with the literal binomial subset average are
proved below.
-/
import QuantumNLS.TensorCarrier
import Mathlib.Data.Nat.Choose.Basic

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace QuantumNLS.TensorPlacements

open QuantumNLS.TensorCarrier





variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The orthogonal projection from the completed p-fold tensor power into
`Sym^p H`, with the symmetric subspace retained as the codomain. -/
def symProjToSector (p : ℕ) : HilbertTensorPower ℂ H p →L[ℂ] SymSector ℂ H p :=
  (symProj ℂ H p).codRestrict (SymSector ℂ H p) (by
    intro x
    rw [symProj_eq_starProjection]
    exact Submodule.starProjection_apply_mem _ _)

/-- Extend a bounded operator on `Sym^p H` by zero on its orthogonal complement.
This is `A ∘ P_p`, followed by the sector inclusion. -/
def extendSymKernel {p : ℕ} (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p :=
  (SymSector ℂ H p).subtypeL.comp (A.comp (symProjToSector p))

theorem norm_extendSymKernel_le {p : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    ‖extendSymKernel A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) ?_
  intro x
  have hproj : ‖symProjToSector (H := H) p x‖ ≤ ‖x‖ := by
    change ‖symProj ℂ H p x‖ ≤ ‖x‖
    rw [symProj_eq_starProjection]
    exact (SymSector ℂ H p).norm_starProjection_apply_le x
  calc
    ‖extendSymKernel A x‖ = ‖A (symProjToSector p x)‖ := rfl
    _ ≤ ‖A‖ * ‖symProjToSector p x‖ := A.le_opNorm _
    _ ≤ ‖A‖ * ‖x‖ := by
      exact mul_le_mul_of_nonneg_left hproj (norm_nonneg A)

/-- A zero-extended symmetric kernel is unchanged by permutations of its own
`p` tensor slots. The output lies in the symmetric sector, while the input is
first projected onto that sector. -/
theorem permRep_comp_extendSymKernel_eq {p : ℕ}
    (π : Equiv.Perm (Fin p)) (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    (permRep ℂ H p π : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p).comp
        (extendSymKernel A) = extendSymKernel A := by
  ext x
  change (permRep ℂ H p π : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p)
      ((SymSector ℂ H p).subtypeL (A (symProjToSector p x))) = _
  exact (A (symProjToSector p x)).property π

/-- The zero-extended symmetric kernel is also invariant on its input under
permutations of the first `p` slots, since the symmetrizing projection is a
group average. -/
theorem extendSymKernel_comp_permRep_eq {p : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) (π : Equiv.Perm (Fin p)) :
    (extendSymKernel A).comp
        (permRep ℂ H p π : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p) =
      extendSymKernel A := by
  ext x
  apply congrArg (fun y : SymSector ℂ H p => (SymSector ℂ H p).subtypeL (A y))
  apply Subtype.ext
  have h := congrArg (fun f : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p => f x)
    (groupAverage_mul_rep (permRep ℂ H p) π)
  change symProj ℂ H p
      ((permRep ℂ H p π : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p) x) =
        symProj ℂ H p x
  simpa [symProj, ContinuousLinearMap.mul_apply] using h

/-- Apply the zero-extended kernel to the first p factors and the identity to
the remaining q factors, transported across the completed tensor split. -/
def firstPlacement {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q) :=
  let e : HilbertTensorPower ℂ H (p + q) ≃ₗᵢ[ℂ]
      HilbertTensor ℂ (HilbertTensorPower ℂ H p) (HilbertTensorPower ℂ H q) :=
    splitIsometry p q
  e.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((htmap (𝕜 := ℂ) (extendSymKernel A) (ContinuousLinearMap.id ℂ
      (HilbertTensorPower ℂ H q))).comp
      e.toLinearIsometry.toContinuousLinearMap)

/-- A permutation acting separately on the first `p` and final `q` positions. -/
def blockPerm {p q : ℕ} (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin q)) :
    Equiv.Perm (Fin (p + q)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr π ρ)).trans finSumFinEquiv

@[simp] theorem blockPerm_castAdd {p q : ℕ} (π : Equiv.Perm (Fin p))
    (ρ : Equiv.Perm (Fin q)) (i : Fin p) :
    blockPerm π ρ (Fin.castAdd q i) = Fin.castAdd q (π i) := by
  simp [blockPerm]

@[simp] theorem blockPerm_natAdd {p q : ℕ} (π : Equiv.Perm (Fin p))
    (ρ : Equiv.Perm (Fin q)) (i : Fin q) :
    blockPerm π ρ (Fin.natAdd p i) = Fin.natAdd p (ρ i) := by
  simp [blockPerm]

@[simp] theorem blockPerm_symm {p q : ℕ} (π : Equiv.Perm (Fin p))
    (ρ : Equiv.Perm (Fin q)) :
    (blockPerm π ρ).symm = blockPerm π.symm ρ.symm := by
  ext i
  simp [blockPerm]

@[simp] theorem blockPerm_inv {p q : ℕ} (π : Equiv.Perm (Fin p))
    (ρ : Equiv.Perm (Fin q)) :
    (blockPerm π ρ)⁻¹ = blockPerm π⁻¹ ρ⁻¹ := by
  ext i
  simp [blockPerm]

/-- The distinguished subset consisting of the first `p` tensor positions. -/
def firstPositions {p q : ℕ} : Finset (Fin (p + q)) :=
  Finset.univ.map (Fin.castAddEmb q)

@[simp] theorem mem_firstPositions {p q : ℕ} (x : Fin (p + q)) :
    x ∈ firstPositions (p := p) (q := q) ↔ ∃ i : Fin p, Fin.castAdd q i = x := by
  simp [firstPositions]

theorem card_firstPositions (p q : ℕ) :
    (firstPositions (p := p) (q := q)).card = p := by
  simp [firstPositions]

/-- The finite type of `p`-element subsets of the `p+q` tensor positions. -/
abbrev PlacementSubset (p q : ℕ) := {s : Finset (Fin (p + q)) // s.card = p}

theorem card_placementSubset (p q : ℕ) :
    Fintype.card (PlacementSubset p q) = Nat.choose (p + q) p := by
  simpa using (Fintype.card_finset_len (α := Fin (p + q)) p)

/-- The subset of positions selected by a permutation of the distinguished
first `p`-slot block. -/
def placementSubsetOfPerm {p q : ℕ} (σ : Equiv.Perm (Fin (p + q))) : PlacementSubset p q :=
  ⟨(firstPositions (p := p) (q := q)).map σ.toEmbedding, by
    rw [Finset.card_map, card_firstPositions]⟩

theorem firstPositions_map_blockPerm {p q : ℕ}
    (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin q)) :
    (firstPositions (p := p) (q := q)).map (blockPerm π ρ).toEmbedding =
      firstPositions (p := p) (q := q) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := (mem_firstPositions (p := p) (q := q) y).mp hy
    exact (mem_firstPositions (p := p) (q := q) _).2 ⟨π i, by simp⟩
  · intro hx
    obtain ⟨i, rfl⟩ := (mem_firstPositions (p := p) (q := q) x).mp hx
    refine Finset.mem_map.mpr ⟨Fin.castAdd q (π⁻¹ i), ?_, ?_⟩
    · exact (mem_firstPositions (p := p) (q := q) _).2 ⟨π⁻¹ i, rfl⟩
    · simp

/-- Every `p`-element subset is the image of the first `p` positions under a
permutation. -/
theorem exists_perm_for_placementSubset {p q : ℕ} (S : PlacementSubset p q) :
    ∃ σ : Equiv.Perm (Fin (p + q)), placementSubsetOfPerm σ = S := by
  have hc : (firstPositions (p := p) (q := q)).card = S.1.card := by
    rw [card_firstPositions, S.2]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (firstPositions (p := p) (q := q)) S.1 hc
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  exact hσ

/-- A fixed representative permutation for each subset; stabilizer invariance
below makes its placement independent of this choice. -/
noncomputable def subsetRepresentative {p q : ℕ} (S : PlacementSubset p q) :
    Equiv.Perm (Fin (p + q)) := Classical.choose (exists_perm_for_placementSubset S)

theorem subsetRepresentative_maps {p q : ℕ} (S : PlacementSubset p q) :
    placementSubsetOfPerm (subsetRepresentative S) = S :=
  Classical.choose_spec (exists_perm_for_placementSubset S)

/-- Every permutation preserving the first `p` positions is uniquely a pair
of permutations within the `p` and `q` blocks. -/
theorem exists_blockPerm_of_firstPositions_stable {p q : ℕ}
    (σ : Equiv.Perm (Fin (p + q)))
    (hσ : (firstPositions (p := p) (q := q)).map σ.toEmbedding =
      firstPositions (p := p) (q := q)) :
    ∃ π : Equiv.Perm (Fin p), ∃ ρ : Equiv.Perm (Fin q), σ = blockPerm π ρ := by
  classical
  have hleft (i : Fin p) : ∃ j : Fin p, σ (Fin.castAdd q i) = Fin.castAdd q j := by
    have hs : σ (Fin.castAdd q i) ∈ firstPositions (p := p) (q := q) := by
      rw [← hσ]
      exact Finset.mem_map.mpr ⟨Fin.castAdd q i,
        (mem_firstPositions (p := p) (q := q) _).2 ⟨i, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := (mem_firstPositions (p := p) (q := q) _).mp hs
    exact ⟨j, hj.symm⟩
  let f : Fin p → Fin p := fun i => Classical.choose (hleft i)
  have hf (i : Fin p) : σ (Fin.castAdd q i) = Fin.castAdd q (f i) := by
    exact Classical.choose_spec (hleft i)
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hout : σ (Fin.castAdd q i) = σ (Fin.castAdd q j) := by rw [hf i, hf j, hij]
    exact (Fin.castAdd_injective p q) (σ.injective hout)
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  let π : Equiv.Perm (Fin p) := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hnot (j : Fin q) : σ (Fin.natAdd p j) ∉ firstPositions (p := p) (q := q) := by
    intro hs
    obtain ⟨i, hi⟩ := (mem_firstPositions (p := p) (q := q) _).mp hs
    obtain ⟨k, hk⟩ := hf_surj i
    have heq : σ (Fin.castAdd q k) = σ (Fin.natAdd p j) := by
      rw [hf k, hk]
      exact hi
    have hbad := congrArg Fin.val (σ.injective heq)
    simp at hbad
    omega
  have hright (j : Fin q) : ∃ k : Fin q, σ (Fin.natAdd p j) = Fin.natAdd p k := by
    obtain ⟨s, hs⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective
      (σ (Fin.natAdd p j))
    cases s with
    | inl i =>
        exfalso
        apply hnot j
        rw [← hs]
        exact (mem_firstPositions (p := p) (q := q) _).2 ⟨i, by simp⟩
    | inr k => exact ⟨k, by simpa using hs.symm⟩
  let g : Fin q → Fin q := fun j => Classical.choose (hright j)
  have hg (j : Fin q) : σ (Fin.natAdd p j) = Fin.natAdd p (g j) :=
    Classical.choose_spec (hright j)
  have hg_inj : Function.Injective g := by
    intro i j hij
    have hout : σ (Fin.natAdd p i) = σ (Fin.natAdd p j) := by rw [hg i, hg j, hij]
    exact (Fin.natAddEmb p).injective (σ.injective hout)
  have hg_surj : Function.Surjective g := Finite.injective_iff_surjective.mp hg_inj
  let ρ : Equiv.Perm (Fin q) := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  refine ⟨π, ρ, ?_⟩
  apply Equiv.ext
  intro x
  obtain ⟨s, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective x
  cases s with
  | inl i =>
      simp only [finSumFinEquiv_apply_left]
      rw [blockPerm_castAdd]
      change σ (Fin.castAdd q i) = Fin.castAdd q (f i)
      exact hf i
  | inr j =>
      simp only [finSumFinEquiv_apply_right]
      rw [blockPerm_natAdd]
      change σ (Fin.natAdd p j) = Fin.natAdd p (g j)
      exact hg j

private theorem finset_map_perm_mul {α : Type*} [DecidableEq α] (s : Finset α)
    (σ τ : Equiv.Perm α) :
    s.map (σ * τ).toEmbedding = (s.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  congr 1

/-- Equal subset images differ by a permutation internal to the two blocks. -/
theorem exists_rightBlock_of_same_firstImage {p q : ℕ}
    (σ τ : Equiv.Perm (Fin (p + q)))
    (h : (firstPositions (p := p) (q := q)).map σ.toEmbedding =
      (firstPositions (p := p) (q := q)).map τ.toEmbedding) :
    ∃ π : Equiv.Perm (Fin p), ∃ ρ : Equiv.Perm (Fin q), τ = σ * blockPerm π ρ := by
  let I := firstPositions (p := p) (q := q)
  let δ := σ⁻¹ * τ
  have hstable : I.map δ.toEmbedding = I := by
    calc
      I.map δ.toEmbedding = (I.map τ.toEmbedding).map σ⁻¹.toEmbedding := by
        rw [finset_map_perm_mul]
      _ = (I.map σ.toEmbedding).map σ⁻¹.toEmbedding := by rw [h]
      _ = I := by
        calc
          (I.map σ.toEmbedding).map σ⁻¹.toEmbedding = I.map (σ⁻¹ * σ).toEmbedding :=
            (finset_map_perm_mul I σ⁻¹ σ).symm
          _ = I := by
            rw [inv_mul_cancel]
            have he : (1 : Equiv.Perm (Fin (p + q))).toEmbedding =
                Function.Embedding.refl _ := by
              ext x
              simp
            rw [he, Finset.map_refl]
  obtain ⟨π, ρ, hδ⟩ := exists_blockPerm_of_firstPositions_stable δ hstable
  refine ⟨π, ρ, ?_⟩
  calc
    τ = σ * δ := by dsimp [δ]; group
    _ = σ * blockPerm π ρ := by rw [hδ]

/-- The completed split intertwines a block permutation with the tensor
product of the two block permutation unitaries. -/
theorem splitIsometry_blockPerm_apply {p q : ℕ} (π : Equiv.Perm (Fin p))
    (ρ : Equiv.Perm (Fin q)) (x : HilbertTensorPower ℂ H (p + q)) :
    splitIsometry p q (permHilbertIsometry (blockPerm π ρ) x) =
      htmap (𝕜 := ℂ)
        (permRep ℂ H p π : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p)
        (permRep ℂ H q ρ : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H q)
        (splitIsometry p q x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((splitIsometry p q).continuous.comp (permHilbertIsometry (blockPerm π ρ)).continuous)
        ((htmap (𝕜 := ℂ)
          (permRep ℂ H p π : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p)
          (permRep ℂ H q ρ : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H q)).continuous.comp
          (splitIsometry p q).continuous)
  | ih z =>
      induction z using AlgTensorPower.induction_on with
      | smul_ptprod c f =>
          let a : Fin p → H := fun i => f (Fin.castAdd q i)
          let b : Fin q → H := fun i => f (Fin.natAdd p i)
          have hf : f = Fin.append a b := by
            funext i
            refine Fin.addCases ?_ ?_ i
            · intro i
              simp [a]
            · intro i
              simp [b]
          have hperm : permLinearEquiv (blockPerm π ρ) (ptprod (Fin.append a b) :
              AlgTensorPower ℂ H (p + q)) =
              ptprod (Fin.append (fun i => a (π.symm i)) (fun i => b (ρ.symm i))) := by
            rw [permLinearEquiv_ptprod]
            congr 1
            funext i
            refine Fin.addCases ?_ ?_ i
            · intro i
              simp [blockPerm]
            · intro i
              simp [blockPerm]
          rw [hf]
          simp only [UniformSpace.Completion.coe_smul, permHilbertIsometry_coe,
            LinearEquiv.map_smul, map_smul, hperm]
          rw [splitIsometry_ptprod_append]
          rw [splitIsometry_ptprod_append]
          simp [htmap_htmul, permRep_apply, permHilbertIsometry_coe, permLinearEquiv_ptprod]
      | add z w hz hw =>
          simp only [UniformSpace.Completion.coe_add, map_add, hz, hw]

/-- Conjugating the tensor product placement by the two block unitaries leaves
it unchanged: the first block uses the symmetric-kernel invariance and the
second block carries the identity. -/
theorem blockTensor_conj_firstPlacement {p q : ℕ}
    (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin q))
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    let U := (permRep ℂ H p π : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p)
    let V := (permRep ℂ H q ρ : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H q)
    (htmap (𝕜 := ℂ) U V).comp
        ((htmap (𝕜 := ℂ) (extendSymKernel A)
          (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q))).comp
          (htmap (𝕜 := ℂ) (permRep ℂ H p π⁻¹)
            (permRep ℂ H q ρ⁻¹))) =
      htmap (𝕜 := ℂ) (extendSymKernel A)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q)) := by
  dsimp
  let U : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p := permRep ℂ H p π
  let V : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H q := permRep ℂ H q ρ
  let Ui : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p := permRep ℂ H p π⁻¹
  let Vi : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H q := permRep ℂ H q ρ⁻¹
  let E : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p := extendSymKernel A
  let I : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H q :=
    ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q)
  have hfirst : (U.comp E).comp Ui = E := by
    rw [permRep_comp_extendSymKernel_eq, extendSymKernel_comp_permRep_eq]
  have hsecond : (V.comp I).comp Vi = I := by
    ext x
    change permHilbertIsometry ρ (permHilbertIsometry ρ⁻¹ x) = x
    have hm := map_mul (permHom ℂ H q) ρ ρ⁻¹
    have hmul : permHilbertIsometry ρ (permHilbertIsometry ρ⁻¹ x) =
        permHilbertIsometry 1 x := by
      simpa [permHom] using (congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) hm).symm
    have hone : permHilbertIsometry (𝕜 := ℂ) (E := H) (1 : Equiv.Perm (Fin q)) = 1 := by
      simpa [permHom] using (map_one (permHom ℂ H q))
    rw [hmul, hone]
    rfl
  calc
    (htmap (𝕜 := ℂ) U V).comp
        ((htmap (𝕜 := ℂ) E I).comp (htmap (𝕜 := ℂ) Ui Vi)) =
      ((htmap (𝕜 := ℂ) U V).comp (htmap (𝕜 := ℂ) E I)).comp
        (htmap (𝕜 := ℂ) Ui Vi) := by
          rw [← ContinuousLinearMap.comp_assoc]
    _ = (htmap (𝕜 := ℂ) (U.comp E) (V.comp I)).comp
        (htmap (𝕜 := ℂ) Ui Vi) := by rw [← htmap_comp U E V I]
    _ = htmap (𝕜 := ℂ) ((U.comp E).comp Ui) ((V.comp I).comp Vi) := by
          rw [← htmap_comp (U.comp E) Ui (V.comp I) Vi]
    _ = htmap (𝕜 := ℂ) E I := by rw [hfirst, hsecond]

/-- The tensor permutation associated to a block permutation is represented,
under the completed split, by the tensor product of its block unitaries. -/
theorem permRep_blockPerm_apply {p q : ℕ} (π : Equiv.Perm (Fin p))
    (ρ : Equiv.Perm (Fin q)) (x : HilbertTensorPower ℂ H (p + q)) :
    (permRep ℂ H (p + q) (blockPerm π ρ) :
      HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)) x =
      ((splitIsometry p q).symm
        (htmap (𝕜 := ℂ)
          (permRep ℂ H p π : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p)
          (permRep ℂ H q ρ : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H q)
          ((splitIsometry p q) x))) := by
  change permHilbertIsometry (blockPerm π ρ) x = _
  apply (splitIsometry p q).injective
  rw [splitIsometry_blockPerm_apply]
  simp

theorem norm_firstPlacement_le {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    ‖firstPlacement (q := q) A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) ?_
  intro x
  let e : HilbertTensorPower ℂ H (p + q) ≃ₗᵢ[ℂ]
      HilbertTensor ℂ (HilbertTensorPower ℂ H p) (HilbertTensorPower ℂ H q) :=
    splitIsometry (𝕜 := ℂ) (E := H) p q
  have hA := norm_extendSymKernel_le (H := H) A
  have hmap : ‖htmap (𝕜 := ℂ) (extendSymKernel A)
      (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q))‖ ≤ ‖A‖ := by
    calc
      _ ≤ ‖extendSymKernel A‖ * ‖ContinuousLinearMap.id ℂ
            (HilbertTensorPower ℂ H q)‖ :=
          norm_htmap_le (𝕜 := ℂ) (extendSymKernel A)
            (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q))
      _ ≤ ‖A‖ * 1 := by
        calc
          _ ≤ ‖A‖ * ‖ContinuousLinearMap.id ℂ
                (HilbertTensorPower ℂ H q)‖ :=
              mul_le_mul_of_nonneg_right hA
                (norm_nonneg (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q)))
          _ ≤ ‖A‖ * 1 := by
            exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg A)
      _ = ‖A‖ := by simp
  calc
    ‖firstPlacement (q := q) A x‖ = ‖htmap (𝕜 := ℂ) (extendSymKernel A)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q)) (e x)‖ := by
          change ‖e.symm (htmap (𝕜 := ℂ) (extendSymKernel A)
            (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q)) (e x))‖ = _
          exact e.symm.norm_map _
    _ ≤ ‖htmap (𝕜 := ℂ) (extendSymKernel A)
          (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q))‖ * ‖e x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * ‖e x‖ := mul_le_mul_of_nonneg_right hmap (norm_nonneg _)
    _ = ‖A‖ * ‖x‖ := by rw [e.norm_map]

/-- The placement obtained by moving the first p positions according to a
permutation.  The conjugation convention agrees with the permutation action
`U_σ (A ⊗ 1) U_σ⁻¹` in DEF-041. -/
def permutedPlacement {p q : ℕ} (σ : Equiv.Perm (Fin (p + q)))
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q) :=
  ((permRep ℂ H (p + q) σ :
      HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)).comp
    (firstPlacement A)).comp
    (permRep ℂ H (p + q) σ⁻¹ :
      HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q))

theorem norm_permutedPlacement_le {p q : ℕ} (σ : Equiv.Perm (Fin (p + q)))
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    ‖permutedPlacement σ A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) ?_
  intro x
  let u := permHilbertIsometry (𝕜 := ℂ) (E := H) σ
  let ui := permHilbertIsometry (𝕜 := ℂ) (E := H) σ⁻¹
  have hfirst := norm_firstPlacement_le (H := H) (q := q) A
  calc
    ‖permutedPlacement σ A x‖ = ‖(permRep ℂ H (p + q) σ :
        HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q))
        (firstPlacement (q := q) A ((permRep ℂ H (p + q) σ⁻¹ :
        HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)) x))‖ := rfl
    _ = ‖firstPlacement (q := q) A (ui x)‖ := by
      rw [permRep_apply]
      rw [permRep_apply]
      exact u.norm_map _
    _ ≤ ‖firstPlacement (q := q) A‖ * ‖ui x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * ‖ui x‖ := mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)
    _ = ‖A‖ * ‖x‖ := by rw [ui.norm_map]

/-- A permutation preserving the first `p` and last `q` blocks does not change
the placement. This is the stabilizer invariance needed for subset indexing. -/
theorem permutedPlacement_blockPerm_eq {p q : ℕ}
    (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin q))
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    permutedPlacement (blockPerm π ρ) A = firstPlacement A := by
  let e := splitIsometry (𝕜 := ℂ) (E := H) p q
  let U := (permRep ℂ H p π : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p)
  let V := (permRep ℂ H q ρ : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H q)
  let Ui := (permRep ℂ H p π⁻¹ : HilbertTensorPower ℂ H p →L[ℂ] HilbertTensorPower ℂ H p)
  let Vi := (permRep ℂ H q ρ⁻¹ : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H q)
  let K := htmap (𝕜 := ℂ) (extendSymKernel A)
    (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q))
  have hfirst (y : HilbertTensorPower ℂ H (p + q)) :
      e (firstPlacement (q := q) A y) = K (e y) := by
    simp [firstPlacement, e, K, ContinuousLinearMap.comp_apply]
  ext x
  apply e.injective
  change e ((permRep ℂ H (p + q) (blockPerm π ρ) : _ →L[ℂ] _) (
      firstPlacement (q := q) A ((permRep ℂ H (p + q) (blockPerm π ρ)⁻¹ : _ →L[ℂ] _) x))) =
    e (firstPlacement (q := q) A x)
  rw [permRep_blockPerm_apply π ρ, blockPerm_inv, permRep_blockPerm_apply π⁻¹ ρ⁻¹]
  rw [hfirst, hfirst]
  simp [e]
  have h := congrArg (fun f : _ →L[ℂ] _ => f (e x))
    (blockTensor_conj_firstPlacement π ρ A)
  simpa [U, V, Ui, Vi, K, ContinuousLinearMap.comp_apply] using h

private theorem permHilbertIsometry_mul_apply {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (x : HilbertTensorPower ℂ H n) :
    permHilbertIsometry (𝕜 := ℂ) (E := H) σ
        (permHilbertIsometry (𝕜 := ℂ) (E := H) τ x) =
      permHilbertIsometry (𝕜 := ℂ) (E := H) (σ * τ) x := by
  have h := map_mul (permHom ℂ H n) σ τ
  simpa [permHom] using (congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) h).symm

/-- Conjugation covariance: left multiplication of the permutation index
matches right multiplication of the input permutation. -/
private theorem permutedPlacement_covariant {p q : ℕ}
    (τ σ : Equiv.Perm (Fin (p + q)))
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    (permRep ℂ H (p + q) τ :
      HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)).comp
        (permutedPlacement σ A) =
      (permutedPlacement (τ * σ) A).comp
        (permRep ℂ H (p + q) τ :
          HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, permutedPlacement, permRep_apply]
  rw [permHilbertIsometry_mul_apply]
  congr 2
  rw [permHilbertIsometry_mul_apply]
  simp [mul_assoc]

/-- Right multiplication by a permutation of either block preserves the
placement, so the operator is constant on each permutation fiber over a
`p`-element subset. -/
theorem permutedPlacement_rightBlock_eq {p q : ℕ}
    (σ : Equiv.Perm (Fin (p + q))) (π : Equiv.Perm (Fin p)) (ρ : Equiv.Perm (Fin q))
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    permutedPlacement (σ * blockPerm π ρ) A = permutedPlacement σ A := by
  let U : HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q) :=
    permRep ℂ H (p + q) σ
  let Ui : HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q) :=
    permRep ℂ H (p + q) σ⁻¹
  have hunit : U.comp Ui = ContinuousLinearMap.id ℂ _ := by
    ext x
    change permHilbertIsometry σ (permHilbertIsometry σ⁻¹ x) = x
    rw [permHilbertIsometry_mul_apply]
    have hone : permHilbertIsometry (𝕜 := ℂ) (E := H)
        (1 : Equiv.Perm (Fin (p + q))) = 1 := by
      simpa [permHom] using (map_one (permHom ℂ H (p + q)))
    rw [mul_inv_cancel]
    rw [hone]
    rfl
  have hcov := permutedPlacement_covariant σ (blockPerm π ρ) A
  rw [permutedPlacement_blockPerm_eq] at hcov
  have hcancel := congrArg (fun f : _ →L[ℂ] _ => f.comp Ui) hcov.symm
  calc
    permutedPlacement (σ * blockPerm π ρ) A =
        (permutedPlacement (σ * blockPerm π ρ) A).comp (U.comp Ui) := by
          rw [hunit]
          simp
    _ = ((permutedPlacement (σ * blockPerm π ρ) A).comp U).comp Ui := by
          ext x
          rfl
    _ = (U.comp (firstPlacement (q := q) A)).comp Ui := hcancel
    _ = permutedPlacement σ A := rfl

/-- Placement depends only on the subset of positions, not on its ordering. -/
theorem permutedPlacement_eq_of_same_firstImage {p q : ℕ}
    (σ τ : Equiv.Perm (Fin (p + q)))
    (h : (firstPositions (p := p) (q := q)).map σ.toEmbedding =
      (firstPositions (p := p) (q := q)).map τ.toEmbedding)
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    permutedPlacement σ A = permutedPlacement τ A := by
  obtain ⟨π, ρ, hτ⟩ := exists_rightBlock_of_same_firstImage σ τ h
  rw [hτ]
  exact (permutedPlacement_rightBlock_eq σ π ρ A).symm

/-- Permutations producing a fixed subset image. -/
abbrev PlacementFiber {p q : ℕ} (S : PlacementSubset p q) :=
  {σ : Equiv.Perm (Fin (p + q)) // placementSubsetOfPerm σ = S}

/-- The block permutations act freely and transitively on each subset fiber. -/
noncomputable def placementFiberEquiv {p q : ℕ} (S : PlacementSubset p q) :
    (Equiv.Perm (Fin p) × Equiv.Perm (Fin q)) ≃ PlacementFiber S := by
  classical
  let rep := subsetRepresentative S
  let f : Equiv.Perm (Fin p) × Equiv.Perm (Fin q) → PlacementFiber S := fun z =>
    ⟨rep * blockPerm z.1 z.2, by
      apply Subtype.ext
      change (firstPositions (p := p) (q := q)).map
          (rep * blockPerm z.1 z.2).toEmbedding = S.1
      rw [finset_map_perm_mul, firstPositions_map_blockPerm]
      exact congrArg Subtype.val (subsetRepresentative_maps S)⟩
  have h_inj : Function.Injective f := by
    intro a b hab
    have hval : rep * blockPerm a.1 a.2 = rep * blockPerm b.1 b.2 :=
      congrArg Subtype.val hab
    have hblock : blockPerm a.1 a.2 = blockPerm b.1 b.2 := mul_left_cancel hval
    have hp : a.1 = b.1 := by
      apply Equiv.ext
      intro i
      apply (Fin.castAdd_injective p q)
      have hi := congrArg (fun e : Equiv.Perm (Fin (p + q)) => e (Fin.castAdd q i)) hblock
      simpa only [blockPerm_castAdd] using hi
    have hq : a.2 = b.2 := by
      apply Equiv.ext
      intro i
      apply (Fin.natAddEmb p).injective
      have hi := congrArg (fun e : Equiv.Perm (Fin (p + q)) => e (Fin.natAdd p i)) hblock
      simpa only [blockPerm_natAdd, Fin.natAddEmb_apply] using hi
    exact Prod.ext hp hq
  have h_surj : Function.Surjective f := by
    rintro ⟨τ, hτ⟩
    have hrep : placementSubsetOfPerm rep = S := subsetRepresentative_maps S
    have hsame := (congrArg Subtype.val hrep).trans (congrArg Subtype.val hτ).symm
    obtain ⟨π, ρ, hrel⟩ := exists_rightBlock_of_same_firstImage rep τ hsame
    refine ⟨(π, ρ), ?_⟩
    apply Subtype.ext
    exact hrel.symm
  exact Equiv.ofBijective f ⟨h_inj, h_surj⟩

/-- Each subset fiber contains exactly `p! q!` permutations. -/
theorem card_placementFiber {p q : ℕ} (S : PlacementSubset p q) :
    Fintype.card (PlacementFiber S) = p.factorial * q.factorial := by
  calc
    Fintype.card (PlacementFiber S) =
        Fintype.card (Equiv.Perm (Fin p) × Equiv.Perm (Fin q)) :=
      (Fintype.card_congr (placementFiberEquiv S)).symm
    _ = p.factorial * q.factorial := by simp [Fintype.card_perm]

/-- The placement is constant on a subset fiber, with the representative
definition agreeing with its value. -/
def subsetPlacement {p q : ℕ} (S : PlacementSubset p q)
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q) :=
  permutedPlacement (subsetRepresentative S) A

theorem permutedPlacement_eq_subsetPlacement {p q : ℕ}
    (σ : Equiv.Perm (Fin (p + q))) (S : PlacementSubset p q)
    (h : placementSubsetOfPerm σ = S) (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    permutedPlacement σ A = subsetPlacement S A := by
  apply permutedPlacement_eq_of_same_firstImage σ (subsetRepresentative S) ?_ A
  exact (congrArg Subtype.val h).trans (congrArg Subtype.val (subsetRepresentative_maps S)).symm

/-- Summing over the permutations with a fixed p-subset image contributes
exactly the block-stabilizer multiplicity `p! q!`. -/
theorem sum_placementFiber {p q : ℕ} (S : PlacementSubset p q)
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    (∑ σ : PlacementFiber S, permutedPlacement σ.1 A) =
      ((p.factorial * q.factorial : ℕ) : ℂ) • subsetPlacement S A := by
  calc
    (∑ σ : PlacementFiber S, permutedPlacement σ.1 A) =
        ∑ _σ : PlacementFiber S, subsetPlacement S A := by
          apply Fintype.sum_congr
          intro σ
          exact permutedPlacement_eq_subsetPlacement σ.1 S σ.2 A
    _ = (Fintype.card (PlacementFiber S) : ℕ) • subsetPlacement S A := by simp
    _ = ((p.factorial * q.factorial : ℕ) : ℂ) • subsetPlacement S A := by
          rw [card_placementFiber]
          exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

/-- Literal DEF-041 average over all p-element subsets of the tensor slots. -/
def subsetPlacementAverage {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q) :=
  ((Nat.choose (p + q) p : ℂ)⁻¹) •
    ∑ S : PlacementSubset p q, subsetPlacement S A

def emptyPlacementSubset (q : ℕ) : PlacementSubset 0 q := ⟨∅, by simp⟩

theorem placementSubset_zero_eq_empty {q : ℕ} (S : PlacementSubset 0 q) :
    S = emptyPlacementSubset q := by
  apply Subtype.ext
  exact Finset.card_eq_zero.mp S.2

/-- At p=0 the subset family is a singleton, so its literal average reduces
to the placement associated with the empty set. -/
theorem subsetPlacementAverage_zero {q : ℕ}
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    subsetPlacementAverage (p := 0) (q := q) A =
      subsetPlacement (emptyPlacementSubset q) A := by
  letI : Unique (PlacementSubset 0 q) := {
    default := emptyPlacementSubset q
    uniq := placementSubset_zero_eq_empty
  }
  simp [subsetPlacementAverage, Unique.eq_default]

theorem subsetPlacement_empty_eq_firstPlacement {q : ℕ}
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    subsetPlacement (emptyPlacementSubset q) A = firstPlacement (q := q) A := by
  let σ0 : Equiv.Perm (Fin (0 + q)) := 1
  have h : placementSubsetOfPerm (p := 0) (q := q) σ0 =
      emptyPlacementSubset q := by
    apply Subtype.ext
    simp [placementSubsetOfPerm, firstPositions, emptyPlacementSubset]
  calc
    subsetPlacement (emptyPlacementSubset q) A =
        permutedPlacement σ0 A :=
      (permutedPlacement_eq_subsetPlacement σ0
        (emptyPlacementSubset q) h A).symm
    _ = firstPlacement (q := q) A := by
      let π : Equiv.Perm (Fin 0) := Equiv.refl _
      let ρ : Equiv.Perm (Fin q) := Equiv.refl _
      have hb : σ0 = blockPerm π ρ := by
        ext i
        simp [σ0, π, ρ, blockPerm]
      rw [hb]
      exact permutedPlacement_blockPerm_eq π ρ A

/-- The average of a finite family of bounded operators has norm at most the
largest common bound.  The coefficient is the reciprocal of the cardinality,
so no hidden unnormalized sum enters the placement estimate. -/
theorem norm_complexAverage_le {ι X : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : ι → X →L[ℂ] X) (C : ℝ)
    (hT : ∀ i, ‖T i‖ ≤ C) :
    ‖((Fintype.card ι : ℂ)⁻¹) • ∑ i, T i‖ ≤ C := by
  let n : ℝ := Fintype.card ι
  have hn : n ≠ 0 := by
    dsimp [n]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hnpos : 0 < n := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hn)
  have hsum : ‖∑ i, T i‖ ≤ ∑ i, ‖T i‖ := norm_sum_le _ _
  have hTsum : ∑ i, ‖T i‖ ≤ n * C := by
    calc
      _ ≤ ∑ _i : ι, C := Finset.sum_le_sum (fun i _ => hT i)
      _ = n * C := by simp [n, nsmul_eq_mul]
  calc
    _ = n⁻¹ * ‖∑ i, T i‖ := by
      simp [n, norm_smul, norm_inv]
    _ ≤ n⁻¹ * ∑ i, ‖T i‖ :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (le_of_lt hnpos))
    _ ≤ n⁻¹ * (n * C) :=
      mul_le_mul_of_nonneg_left hTsum (inv_nonneg.mpr (le_of_lt hnpos))
    _ = C := by field_simp [hn]

/-- DEF-041 symmetrized placement on the full completed tensor power, written
as an average over all permutations with coefficient `1/(p+q)!`. -/
def symmetrizedPlacement {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q) :=
  ((Fintype.card (Equiv.Perm (Fin (p + q))) : ℂ)⁻¹) •
    ∑ σ : Equiv.Perm (Fin (p + q)), permutedPlacement σ A

/-- Scalar normalization identity behind the DEF-041 permutation average:
`1/(p+q)!` times the `p! q!` permutations in one subset fiber equals
`1/binom(p+q,p)`. This proves the factorial factor; the finite subset-fiber
equivalence is a separate combinatorial statement. -/
theorem permutation_binomial_normalization (p q : ℕ) :
    ((p + q).factorial : ℂ)⁻¹ * (p.factorial : ℂ) * (q.factorial : ℂ) =
      (Nat.choose (p + q) p : ℂ)⁻¹ := by
  have hNat : Nat.choose (p + q) p * p.factorial * q.factorial = (p + q).factorial := by
    simpa [Nat.add_sub_cancel_left] using
      (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right p q))
  have h : (Nat.choose (p + q) p : ℂ) * (p.factorial : ℂ) * (q.factorial : ℂ) =
      ((p + q).factorial : ℂ) := by
    exact_mod_cast hNat
  have hc : (Nat.choose (p + q) p : ℂ) ≠ 0 := by
    have hp : 0 < Nat.choose (p + q) p := Nat.choose_pos (Nat.le_add_right p q)
    have hn : Nat.choose (p + q) p ≠ 0 := by omega
    exact_mod_cast hn
  rw [← h]
  field_simp [hc, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)]

/-- The preceding scalar identity with the actual cardinality of the permutation
group used by `symmetrizedPlacement`. -/
theorem fullPermutation_binomial_normalization (p q : ℕ) :
    ((Fintype.card (Equiv.Perm (Fin (p + q))) : ℂ)⁻¹) *
        (p.factorial : ℂ) * (q.factorial : ℂ) =
      (Nat.choose (p + q) p : ℂ)⁻¹ := by
  simpa [Fintype.card_perm, Fintype.card_fin] using permutation_binomial_normalization p q

/-- Grouping the permutation average by its p-element subset image gives
exactly the literal binomial subset average in DEF-041. -/
theorem symmetrizedPlacement_eq_subsetPlacementAverage {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    symmetrizedPlacement (q := q) A = subsetPlacementAverage (q := q) A := by
  have hgroup :
      (∑ σ : Equiv.Perm (Fin (p + q)), permutedPlacement σ A) =
        ∑ S : PlacementSubset p q,
          ∑ σ : PlacementFiber S, permutedPlacement σ.1 A := by
    simpa only [PlacementFiber] using
      (Fintype.sum_fiberwise
        (placementSubsetOfPerm (p := p) (q := q))
        (fun σ => permutedPlacement σ A)).symm
  calc
    symmetrizedPlacement (q := q) A =
        ((Fintype.card (Equiv.Perm (Fin (p + q))) : ℂ)⁻¹) •
          ∑ S : PlacementSubset p q,
            ∑ σ : PlacementFiber S, permutedPlacement σ.1 A := by
          simp only [symmetrizedPlacement]
          rw [hgroup]
    _ = subsetPlacementAverage (q := q) A := by
          simp_rw [sum_placementFiber]
          rw [← Finset.smul_sum, smul_smul, subsetPlacementAverage]
          congr 1
          calc
            (Fintype.card (Equiv.Perm (Fin (p + q))) : ℂ)⁻¹ *
                ((p.factorial * q.factorial : ℕ) : ℂ) =
              (Fintype.card (Equiv.Perm (Fin (p + q))) : ℂ)⁻¹ *
                (p.factorial : ℂ) * (q.factorial : ℂ) := by
                  push_cast
                  ring
            _ = (Nat.choose (p + q) p : ℂ)⁻¹ :=
              fullPermutation_binomial_normalization p q

theorem symmetrizedPlacement_zero_eq_firstPlacement {q : ℕ}
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    symmetrizedPlacement (p := 0) (q := q) A = firstPlacement (q := q) A := by
  rw [symmetrizedPlacement_eq_subsetPlacementAverage, subsetPlacementAverage_zero,
    subsetPlacement_empty_eq_firstPlacement]

theorem norm_symmetrizedPlacement_le {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    ‖symmetrizedPlacement (q := q) A‖ ≤ ‖A‖ := by
  apply norm_complexAverage_le (fun σ : Equiv.Perm (Fin (p + q)) => permutedPlacement σ A)
    ‖A‖
  intro σ
  exact norm_permutedPlacement_le σ A

/-- The permutation average commutes with every tensor permutation, because
permutations reindex its conjugated summands. -/
theorem permRep_commutes_symmetrizedPlacement {p q : ℕ}
    (τ : Equiv.Perm (Fin (p + q)))
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    (permRep ℂ H (p + q) τ :
      HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)).comp
        (symmetrizedPlacement (q := q) A) =
      (symmetrizedPlacement (q := q) A).comp
        (permRep ℂ H (p + q) τ :
          HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)) := by
  ext x
  let U := (permRep ℂ H (p + q) τ :
    HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q))
  let c := ((Fintype.card (Equiv.Perm (Fin (p + q))) : ℂ)⁻¹)
  have hsum : ∑ σ : Equiv.Perm (Fin (p + q)), U (permutedPlacement σ A x) =
      ∑ σ : Equiv.Perm (Fin (p + q)), permutedPlacement (τ * σ) A (U x) := by
    apply Finset.sum_congr rfl
    intro σ _
    have h := congrArg (fun F : _ →L[ℂ] _ => F x) (permutedPlacement_covariant τ σ A)
    simpa [U, ContinuousLinearMap.comp_apply] using h
  have hreindex :
      (∑ σ : Equiv.Perm (Fin (p + q)), permutedPlacement (τ * σ) A (U x)) =
      ∑ σ : Equiv.Perm (Fin (p + q)), permutedPlacement σ A (U x) :=
    Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)
  have hmap : U (∑ σ : Equiv.Perm (Fin (p + q)), permutedPlacement σ A x) =
      ∑ σ : Equiv.Perm (Fin (p + q)), U (permutedPlacement σ A x) := by
    exact map_sum U (fun σ => permutedPlacement σ A x) Finset.univ
  change U (symmetrizedPlacement (q := q) A x) =
    symmetrizedPlacement (q := q) A (U x)
  simp only [symmetrizedPlacement, smul_apply]
  rw [map_smul, sum_apply, sum_apply, hmap]
  exact congrArg (fun y : HilbertTensorPower ℂ H (p + q) => c • y) (hsum.trans hreindex)

/-- The symmetrized placement preserves the symmetric sector, since it
commutes with every tensor permutation. -/
theorem symmetrizedPlacement_apply_mem {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)
    (x : SymSector ℂ H (p + q)) :
    symmetrizedPlacement (q := q) A x.1 ∈ SymSector ℂ H (p + q) := by
  intro τ
  have hcomm :
      (permRep ℂ H (p + q) τ :
        HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q))
          (symmetrizedPlacement (q := q) A x.1) =
      symmetrizedPlacement (q := q) A
        ((permRep ℂ H (p + q) τ :
          HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)) x.1) := by
    have h := congrArg (fun f : _ →L[ℂ] _ => f x.1)
      (permRep_commutes_symmetrizedPlacement τ A)
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    (permRep ℂ H (p + q) τ :
      HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q))
        (symmetrizedPlacement (q := q) A x.1) =
      symmetrizedPlacement (q := q) A x.1 := by rw [hcomm, x.2 τ]
    _ = symmetrizedPlacement (q := q) A x.1 := rfl

theorem subsetPlacementAverage_apply_mem {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)
    (x : SymSector ℂ H (p + q)) :
    subsetPlacementAverage (q := q) A x.1 ∈ SymSector ℂ H (p + q) := by
  rw [← symmetrizedPlacement_eq_subsetPlacementAverage A]
  exact symmetrizedPlacement_apply_mem A x

/-- DEF-041's normalized placement average, restricted to `Sym^(p+q) H`.
The particle count is expressed as `p+q` to retain the completed tensor split. -/
def Q_N_p {p q : ℕ} (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    SymSector ℂ H (p + q) →L[ℂ] SymSector ℂ H (p + q) :=
  ((symmetrizedPlacement (q := q) A).comp
    (SymSector ℂ H (p + q)).subtypeL).codRestrict (SymSector ℂ H (p + q))
      (symmetrizedPlacement_apply_mem A)

/-- On the symmetric sector, `Q_N_p` is exactly the literal binomial subset
average from DEF-041. -/
theorem Q_N_p_eq_subsetPlacementAverage {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    Q_N_p (q := q) A =
      ((subsetPlacementAverage (q := q) A).comp
        (SymSector ℂ H (p + q)).subtypeL).codRestrict (SymSector ℂ H (p + q))
        (subsetPlacementAverage_apply_mem A) := by
  ext x
  exact congrArg (fun T : HilbertTensorPower ℂ H (p + q) →L[ℂ]
      HilbertTensorPower ℂ H (p + q) => T x)
    (symmetrizedPlacement_eq_subsetPlacementAverage A)

/-- At `p=0`, the averaged operator reduces to the placement of the empty
subset, represented by the first zero-factor block. -/
theorem Q_N_0_eq_firstPlacement {q : ℕ}
    (A : SymSector ℂ H 0 →L[ℂ] SymSector ℂ H 0) :
    Q_N_p (p := 0) (q := q) A =
      ((firstPlacement (q := q) A).comp
        (SymSector ℂ H (0 + q)).subtypeL).codRestrict (SymSector ℂ H (0 + q)) (by
          intro x
          rw [← symmetrizedPlacement_zero_eq_firstPlacement]
          exact symmetrizedPlacement_apply_mem A x) := by
  ext x
  exact congrArg (fun T : HilbertTensorPower ℂ H (0 + q) →L[ℂ]
      HilbertTensorPower ℂ H (0 + q) => T x)
    (symmetrizedPlacement_zero_eq_firstPlacement A)

theorem norm_Q_N_p_le {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    ‖Q_N_p (q := q) A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) ?_
  intro x
  have hQ := norm_symmetrizedPlacement_le (H := H) (q := q) A
  calc
    ‖Q_N_p (q := q) A x‖ =
        ‖symmetrizedPlacement (q := q) A (x : HilbertTensorPower ℂ H (p + q))‖ := rfl
    _ ≤ ‖symmetrizedPlacement (q := q) A‖ *
          ‖(x : HilbertTensorPower ℂ H (p + q))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * ‖x‖ := by
        exact mul_le_mul hQ (le_of_eq rfl)
          (norm_nonneg (x : HilbertTensorPower ℂ H (p + q))) (norm_nonneg A)

end QuantumNLS.TensorPlacements

#print axioms QuantumNLS.TensorPlacements.norm_firstPlacement_le
#print axioms QuantumNLS.TensorPlacements.norm_symmetrizedPlacement_le
#print axioms QuantumNLS.TensorPlacements.permRep_commutes_symmetrizedPlacement
#print axioms QuantumNLS.TensorPlacements.norm_Q_N_p_le
#print axioms QuantumNLS.TensorPlacements.permutation_binomial_normalization
#print axioms QuantumNLS.TensorPlacements.fullPermutation_binomial_normalization
#print axioms QuantumNLS.TensorPlacements.exists_blockPerm_of_firstPositions_stable
#print axioms QuantumNLS.TensorPlacements.permutedPlacement_blockPerm_eq
#print axioms QuantumNLS.TensorPlacements.permutedPlacement_rightBlock_eq
#print axioms QuantumNLS.TensorPlacements.permutedPlacement_eq_of_same_firstImage
#print axioms QuantumNLS.TensorPlacements.placementFiberEquiv
#print axioms QuantumNLS.TensorPlacements.card_placementFiber
#print axioms QuantumNLS.TensorPlacements.sum_placementFiber
#print axioms QuantumNLS.TensorPlacements.symmetrizedPlacement_eq_subsetPlacementAverage
#print axioms QuantumNLS.TensorPlacements.Q_N_p_eq_subsetPlacementAverage
#print axioms QuantumNLS.TensorPlacements.subsetPlacementAverage_zero
#print axioms QuantumNLS.TensorPlacements.symmetrizedPlacement_zero_eq_firstPlacement
#print axioms QuantumNLS.TensorPlacements.Q_N_0_eq_firstPlacement
