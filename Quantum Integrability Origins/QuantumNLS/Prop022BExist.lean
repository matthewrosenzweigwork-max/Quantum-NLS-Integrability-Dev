import Mathlib
import QuantumNLS.Prop022GHilbert

/-! PROP-022 route A, finite-dimensional case, stage B5a: two existence facts for a finite-dimensional
complex Hilbert space `H` and the carrier `L2T L` (infinite-dimensional, separable).

* `exists_isometry_fin`: there is a linear isometry `J : H →ₗᵢ[ℂ] L2T L` (an orthonormal basis of `H` is sent to
  Fourier modes);
* `exists_unitary_fixing`: any two linear isometries `J, J' : H →ₗᵢ[ℂ] L2T L` differ by a unitary `R` of
  `L2T L`: `R (J v) = J' v` (extend the orthonormal families `J ∘ b`, `J' ∘ b` to Hilbert bases and match the
  countably infinite complements). -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace

namespace QuantumNLS.Prop022BExist
open PhysicalTensor BetheCoefficientTransform Prop022GHilbert

variable {L : ℝ} [Fact (0 < L)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sep : TopologicalSpace.SeparableSpace (L2T L) := by
  let φ := Ext006KernelHilbertSchmidt.physicalBasis L
  have h1 : TopologicalSpace.IsSeparable
      ((Submodule.span ℂ (Set.range φ) : Submodule ℂ (L2T L)) : Set (L2T L)) :=
    (Set.countable_range φ).isSeparable.span
  have h2 := h1.closure
  have h3 : closure ((Submodule.span ℂ (Set.range φ) : Submodule ℂ (L2T L)) : Set (L2T L)) =
      Set.univ := by
    rw [← Submodule.topologicalClosure_coe, φ.dense_span]
    rfl
  rw [h3] at h2
  exact TopologicalSpace.isSeparable_univ_iff.mp h2

theorem exists_isometry_fin (hH : FiniteDimensional ℂ H) (L : ℝ) [Fact (0 < L)] :
    Nonempty (H →ₗᵢ[ℂ] L2T L) := by
  classical
  set d := Module.finrank ℂ H
  let b := stdOrthonormalBasis ℂ H
  let φ := Ext006KernelHilbertSchmidt.physicalBasis L
  let g : Fin d → L2T L := fun i => φ ((i : ℕ) : ℤ)
  have hginj : Function.Injective (fun i : Fin d => (((i : ℕ) : ℤ))) := by
    intro i j h
    have h' : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := h
    exact Fin.ext (by exact_mod_cast h')
  have hg : Orthonormal ℂ g := φ.orthonormal.comp _ hginj
  let T : H →ₗ[ℂ] L2T L := b.toBasis.constr ℂ g
  have hTb : ∀ i, T (b i) = g i := fun i => by
    have := b.toBasis.constr_basis ℂ g i
    simpa only [OrthonormalBasis.coe_toBasis] using this
  have hTx : ∀ x, T x = ∑ i, ⟪b i, x⟫_ℂ • g i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, hTb, OrthonormalBasis.repr_apply_apply]
  have h1 : ∀ i, ⟪g i, g i⟫_ℂ = 1 := fun i => by
    rw [inner_self_eq_norm_sq_to_K, hg.1 i]; simp
  refine ⟨(T.isometryOfInner (fun x y => ?_))⟩
  rw [hTx x, hTx y, sum_inner, ← b.sum_inner_mul_inner x y]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_smul_left, inner_sum]
  simp only [inner_smul_right]
  rw [Finset.sum_eq_single i]
  · rw [h1 i, mul_one, inner_conj_symm]
  · intro j _ hji
    rw [hg.2 (Ne.symm hji), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem exists_unitary_fixing (hH : FiniteDimensional ℂ H) [CompleteSpace H] (J J' : H →ₗᵢ[ℂ] L2T L) :
    ∃ R : L2T L ≃ₗᵢ[ℂ] L2T L, ∀ v, R (J v) = J' v := by
  classical
  haveI := sep (L := L)
  set d := Module.finrank ℂ H
  let b := stdOrthonormalBasis ℂ H
  let f : Fin d → L2T L := fun i => J (b i)
  let f' : Fin d → L2T L := fun i => J' (b i)
  have hf : Orthonormal ℂ f := (LinearIsometry.orthonormal_comp_iff J).mpr b.orthonormal
  have hf' : Orthonormal ℂ f' := (LinearIsometry.orthonormal_comp_iff J').mpr b.orthonormal
  have hfi : Function.Injective f := hf.linearIndependent.injective
  have hfi' : Function.Injective f' := hf'.linearIndependent.injective
  obtain ⟨w, B, hsw, hB⟩ := ((orthonormal_subtype_range hfi).mpr hf).exists_hilbertBasis_extension
  obtain ⟨w', B', hsw', hB'⟩ :=
    ((orthonormal_subtype_range hfi').mpr hf').exists_hilbertBasis_extension
  have hon : Orthonormal ℂ (fun x : w => (x : L2T L)) := by
    have := B.orthonormal
    rwa [hB] at this
  have hon' : Orthonormal ℂ (fun x : w' => (x : L2T L)) := by
    have := B'.orthonormal
    rwa [hB'] at this
  haveI : Countable w := orthonormal_countable hon
  haveI : Countable w' := orthonormal_countable hon'
  haveI : Infinite w := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    haveI := Fintype.ofFinite w
    exact L2T_not_finiteDimensional L (Module.Finite.of_basis B.toOrthonormalBasis.toBasis)
  haveI : Infinite w' := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    haveI := Fintype.ofFinite w'
    exact L2T_not_finiteDimensional L (Module.Finite.of_basis B'.toOrthonormalBasis.toBasis)
  let p : w → Prop := fun x => (x : L2T L) ∈ Set.range f
  let p' : w' → Prop := fun x => (x : L2T L) ∈ Set.range f'
  let g : Fin d → {x : w // p x} := fun i => ⟨⟨f i, hsw ⟨i, rfl⟩⟩, ⟨i, rfl⟩⟩
  let g' : Fin d → {x : w' // p' x} := fun i => ⟨⟨f' i, hsw' ⟨i, rfl⟩⟩, ⟨i, rfl⟩⟩
  have hg : Function.Bijective g := by
    refine ⟨fun i j h => hfi (congrArg (fun x : {x : w // p x} => (x.1 : L2T L)) h), ?_⟩
    rintro ⟨⟨x, hx⟩, ⟨i, hi⟩⟩
    exact ⟨i, Subtype.ext (Subtype.ext hi)⟩
  have hg' : Function.Bijective g' := by
    refine ⟨fun i j h => hfi' (congrArg (fun x : {x : w' // p' x} => (x.1 : L2T L)) h), ?_⟩
    rintro ⟨⟨x, hx⟩, ⟨i, hi⟩⟩
    exact ⟨i, Subtype.ext (Subtype.ext hi)⟩
  haveI : Finite {x : w // p x} := Finite.of_surjective g hg.2
  haveI : Finite {x : w' // p' x} := Finite.of_surjective g' hg'.2
  haveI : Infinite {x : w // ¬ p x} := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    haveI : Finite ({x : w // p x} ⊕ {x : w // ¬ p x}) := inferInstance
    haveI : Finite w := Finite.of_equiv _ (Equiv.sumCompl p)
    exact not_finite w
  haveI : Infinite {x : w' // ¬ p' x} := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    haveI : Finite ({x : w' // p' x} ⊕ {x : w' // ¬ p' x}) := inferInstance
    haveI : Finite w' := Finite.of_equiv _ (Equiv.sumCompl p')
    exact not_finite w'
  obtain ⟨e⟩ : Nonempty ({x : w // ¬ p x} ≃ {x : w' // ¬ p' x}) := nonempty_equiv_of_countable
  let τ : {x : w // p x} ≃ {x : w' // p' x} :=
    (Equiv.ofBijective g hg).symm.trans (Equiv.ofBijective g' hg')
  let σ : w ≃ w' := (Equiv.sumCompl p).symm.trans ((Equiv.sumCongr τ e).trans (Equiv.sumCompl p'))
  have hσ : ∀ i, σ ⟨f i, hsw ⟨i, rfl⟩⟩ = ⟨f' i, hsw' ⟨i, rfl⟩⟩ := by
    intro i
    have h1 : (Equiv.sumCompl p).symm (⟨f i, hsw ⟨i, rfl⟩⟩ : w) = Sum.inl (g i) :=
      Equiv.sumCompl_symm_apply_of_pos (p := p) ⟨i, rfl⟩
    have h2 : τ (g i) = g' i := by
      change (Equiv.ofBijective g' hg') ((Equiv.ofBijective g hg).symm (g i)) = g' i
      have : (Equiv.ofBijective g hg).symm (g i) = i := by
        rw [Equiv.symm_apply_eq]; rfl
      rw [this]; rfl
    simp only [σ, Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inl, h2]
    rfl
  let R : L2T L ≃ₗᵢ[ℂ] L2T L := (reindexBasis σ B).repr.trans B'.repr.symm
  have hR : ∀ x : w, R (x : L2T L) = (σ x : L2T L) := by
    intro x
    have hbx : (x : L2T L) = reindexBasis σ B (σ x) := by
      rw [reindexBasis_apply, Equiv.symm_apply_apply]
      exact (congrFun hB x).symm
    have hb'x : (σ x : L2T L) = B' (σ x) := (congrFun hB' (σ x)).symm
    rw [hbx, hb'x]
    change B'.repr.symm ((reindexBasis σ B).repr (reindexBasis σ B (σ x))) = B' (σ x)
    rw [HilbertBasis.repr_self, HilbertBasis.repr_symm_single]
  refine ⟨R, fun v => ?_⟩
  have hRf : ∀ i, R (J (b i)) = J' (b i) := by
    intro i
    have := hR ⟨f i, hsw ⟨i, rfl⟩⟩
    rw [hσ i] at this
    exact this
  conv_lhs => rw [← b.sum_repr' v]
  conv_rhs => rw [← b.sum_repr' v]
  simp only [map_sum, map_smul, hRf]

end QuantumNLS.Prop022BExist

#print axioms QuantumNLS.Prop022BExist.exists_isometry_fin
#print axioms QuantumNLS.Prop022BExist.exists_unitary_fixing
