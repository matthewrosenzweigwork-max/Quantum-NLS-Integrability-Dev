import QuantumNLS.HighMomentsDerivative
import QuantumNLS.BetheSpectralContinuity
import QuantumNLS.BetheConditionalBasis

/-!
# PROP-008 normality bridge: `S_N(z)` is diagonal in any supplied complete Bethe basis

Terra r106/r114 accepted the actual-transfer moment applications of PROP-008
(`HighMomentsTransfer.transfer_moments`, `HighMomentsDerivative.transfer_moments_deriv`) under the
premise `hnormal` that `S_N(z)` and its spectral-parameter derivatives `∂_z^k S_N(z)` are normal.
The source obtains normality by diagonalization in the complete Bethe basis.

Here, for **any supplied** complete Bethe basis — a Hilbert basis `b` of `Sym^N L²(𝕋_L)` indexed by
the DEF-006 occupation arrays (`BetheCoefficientTransform.BetheBasis`, as in DEF-007), each of whose
vectors is a scalar multiple of the source Bethe vector (`BetheHigherPlacement.sourceVector`, the
original unnormalized `ψ_{n,c}`) with the label `n` attached to `m` by Sol's exact label
correspondence `BetheConditionalBasis.labelArr`, at the mean-field coupling `c = κ/N` (`IsBetheBasis`)
— we prove:
* `transfer_basis`: `S_N(z) b_m = Λ_m(z) b_m` for every complex `z`, where `Λ_m` is the Bethe
  transfer eigenvalue (BSC1 `spectralValue`, the entire continuation of the on-shell product);
* `deriv_basis`: `∂_z^k S_N(z) b_m = Λ_m^{(k)}(z) b_m`;
* `normal_deriv`: every `∂_z^k S_N(z)` (including `k = 0`) is normal, and `commute_deriv`: all of
  them commute with each other (any `z, w, k, l`);
* `transfer_moments_bethe`, `transfer_moments_deriv_bethe`: the PROP-008 actual-transfer moment
  theorems with `hnormal` discharged relative to the supplied basis.

No completeness of the actual Bethe family is proved or used (EXT-001 / R-9BF8373D is not touched):
completeness is part of the supplied basis `b`. Imports, read-only: BSC1 `BetheSpectralContinuity`
(`f6772092…`/freeze `13df1ebf…`), HMD1 `HighMomentsDerivative` (`ffd49bf6…`), DEF-048
`NormalizedTransfer`, `BetheConditionalBasis` (only `labelArr`; its EXT-001 premise is not used).
-/

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.NormalityBridge

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.HighMomentsRank QuantumNLS.NormalizedTransfer QuantumNLS.HighMomentsTransfer
  QuantumNLS.HighMomentsDerivative QuantumNLS.BetheCoefficientTransform QuantumNLS.HighMomentsOps
  QuantumNLS.HighMomentsFinal

/-! ## 1. Operators diagonal in a Hilbert basis -/

section Diag

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (b : HilbertBasis ι ℂ E)

omit [CompleteSpace E] in
/-- Two bounded operators agreeing on a Hilbert basis are equal. -/
theorem clm_ext_basis {T T' : E →L[ℂ] E} (h : ∀ i, T (b i) = T' (b i)) : T = T' := by
  ext ψ
  have hs := b.hasSum_repr ψ
  have h1 := hs.mapL T
  have h2 := hs.mapL T'
  simp only [map_smul, h] at h1
  simp only [map_smul] at h2
  exact h1.unique h2

/-- `T` is diagonal in `b`. -/
def IsDiag (T : E →L[ℂ] E) : Prop := ∀ i, ∃ a : ℂ, T (b i) = a • b i

variable {b}

theorem IsDiag.adjoint {T : E →L[ℂ] E} (hT : IsDiag b T) :
    IsDiag b (ContinuousLinearMap.adjoint T) := by
  intro i
  obtain ⟨a, ha⟩ := hT i
  refine ⟨conj a, b.repr.injective (lp.ext (funext fun j => ?_))⟩
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
    ContinuousLinearMap.adjoint_inner_right, inner_smul_right]
  obtain ⟨aj, haj⟩ := hT j
  rw [haj, inner_smul_left]
  by_cases hij : j = i
  · subst hij
    have : aj = a := by
      have e : aj • b j = a • b j := haj.symm.trans ha
      exact smul_left_injective ℂ (b.orthonormal.ne_zero j) e
    rw [this]
  · rw [b.orthonormal.inner_eq_zero hij, mul_zero, mul_zero]

omit [CompleteSpace E] in
theorem IsDiag.commute {A B : E →L[ℂ] E} (hA : IsDiag b A) (hB : IsDiag b B) : Commute A B := by
  show A * B = B * A
  refine clm_ext_basis b fun i => ?_
  obtain ⟨a, ha⟩ := hA i
  obtain ⟨c, hc⟩ := hB i
  show A (B (b i)) = B (A (b i))
  rw [hc, map_smul, ha, map_smul, hc, smul_smul, smul_smul, mul_comm]

/-- A diagonal operator is normal. -/
theorem IsDiag.normal {T : E →L[ℂ] E} (hT : IsDiag b T) :
    Commute (ContinuousLinearMap.adjoint T) T :=
  hT.adjoint.commute hT

end Diag

/-! ## 2. Supplied complete Bethe bases -/

variable {L : ℝ} [Fact (0 < L)]

lemma cpos {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) : 0 < κ / (N : ℝ) :=
  div_pos hκ (Nat.cast_pos.2 hN)

/-- The source label `n = (labelArr)⁻¹ m` (antitone integers) of the occupation array `m`. -/
abbrev label {N : ℕ} (m : QuantumNLS.BetheLabels.MArr N) :
    QuantumNLS.BetheFreeFamily.Label N :=
  (QuantumNLS.BetheConditionalBasis.labelArr N).symm m

/-- **A supplied complete Bethe basis at mean-field coupling `κ/N`**: a Hilbert basis of
`Sym^N L²(𝕋_L)` indexed by the occupation arrays whose `m`-th vector is a scalar multiple of the
source Bethe vector `ψ_{n,κ/N}` with label `n = (labelArr)⁻¹ m`. -/
def IsBetheBasis (κ : ℝ) (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (b : BetheBasis L N) : Prop :=
  ∀ m, ∃ a : ℂ, (b m : SymSector ℂ (L2T L) N) =
    a • QuantumNLS.BetheHigherPlacement.sourceVector L (cpos hκ hN) (label m).2

/-- The Bethe transfer eigenvalue `Λ_m(z)` of label `m` (BSC1). -/
def eigen (κ : ℝ) (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : QuantumNLS.BetheLabels.MArr N) : ℂ → ℂ :=
  QuantumNLS.BetheSpectralContinuity.spectralValue L (cpos hκ hN) (label m).2

lemma eigen_differentiable (κ : ℝ) (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (m : QuantumNLS.BetheLabels.MArr N) : Differentiable ℂ (eigen (L := L) κ hκ hN m) :=
  (QuantumNLS.BetheSpectralContinuity.basis_eigenvalue L (cpos hκ hN) (label m).2).1

section Bridge

variable {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {b : BetheBasis L N}
  (hb : IsBetheBasis κ hκ hN b)
include hb

/-- **`S_N(z)` is diagonal in the supplied Bethe basis**, with the Bethe transfer eigenvalue, for
every complex `z`. -/
theorem transfer_basis (z : ℂ) (m : QuantumNLS.BetheLabels.MArr N) :
    normalizedTransfer L κ N z (b m) = eigen (L := L) κ hκ hN m z • b m := by
  obtain ⟨a, ha⟩ := hb m
  have he := (QuantumNLS.BetheSpectralContinuity.basis_eigenvalue L (cpos hκ hN)
    (label m).2).2.2.2 z
  show normalizedTransfer L κ N z (b m : SymSector ℂ (L2T L) N) =
    eigen (L := L) κ hκ hN m z • (b m : SymSector ℂ (L2T L) N)
  rw [ha, map_smul, normalizedTransfer_eq_transfer, he, smul_comm]
  rfl

omit hb in
lemma differentiable_normalizedTransfer :
    Differentiable ℂ (fun w => normalizedTransfer L κ N w) := by
  have hfun : (fun w => normalizedTransfer L κ N w) = fun w =>
      Lam0 (H := L2T L) N (1 + Complex.exp (Complex.I * w * L)) +
        ∑ j : Fin N, LamJ (H := L2T L) N j (Afam L κ w (j.val + 1)) := by
    funext w
    rw [normalizedTransfer_eq_Xop, Xop_eq_lin]
    rfl
  rw [hfun]
  have d1 : Differentiable ℂ (fun w => Lam0 (H := L2T L) N (1 + Complex.exp (Complex.I * w * L))) :=
    Differentiable.comp (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      (G := SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N)
      (Lam0 (H := L2T L) N).differentiable (by fun_prop)
  have hf3 : ContDiff ℂ 1 (fun w => ∑ j : Fin N, LamJ (H := L2T L) N j (Afam L κ w (j.val + 1))) := by
    have hf2 : ∀ j ∈ (Finset.univ : Finset (Fin N)),
        ContDiff ℂ 1 (fun w => LamJ (H := L2T L) N j (Afam L κ w (j.val + 1))) := by
      intro j _
      have d0 : Differentiable ℂ (fun w => LamJ (H := L2T L) N j (Afam L κ w (j.val + 1))) :=
        Differentiable.comp (𝕜 := ℂ) (E := ℂ) (F := BoundedSymmetricKernel (L2T L) (j.val + 1))
          (G := SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N)
          (LamJ (H := L2T L) N j).differentiable (differentiable_Afam κ (j.val + 1))
      exact d0.contDiff
    exact ContDiff.sum hf2
  exact (ContDiff.add (F := SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N)
    (d1.contDiff (n := 1)) hf3).differentiable one_ne_zero

/-- **Spectral derivatives are diagonal**: `∂_z^k S_N(z) b_m = Λ_m^{(k)}(z) b_m`. -/
theorem deriv_basis (k : ℕ) (z : ℂ) (m : QuantumNLS.BetheLabels.MArr N) :
    iteratedDeriv k (fun w => normalizedTransfer L κ N w) z (b m) =
      iteratedDeriv k (eigen (L := L) κ hκ hN m) z • b m := by
  have hS := differentiable_normalizedTransfer (L := L) (κ := κ) (N := N)
  have c1 := congrFun (iteratedDeriv_clm
    (ContinuousLinearMap.apply ℂ (SymSector ℂ (L2T L) N) (b m : SymSector ℂ (L2T L) N)) hS k) z
  simp only [ContinuousLinearMap.apply_apply] at c1
  rw [← c1]
  have hfun : (fun w => normalizedTransfer L κ N w (b m : SymSector ℂ (L2T L) N)) =
      fun w => ((ContinuousLinearMap.id ℂ ℂ).smulRight (b m : SymSector ℂ (L2T L) N))
        (eigen (L := L) κ hκ hN m w) := by
    funext w
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    exact transfer_basis hκ hN hb w m
  rw [hfun, iteratedDeriv_clm _ (eigen_differentiable κ hκ hN m) k]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]

theorem isDiag_deriv (k : ℕ) (z : ℂ) :
    IsDiag b (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z) :=
  fun m => ⟨_, deriv_basis hκ hN hb k z m⟩

/-- **Normality of every spectral derivative** (`hnormal`, relative to the supplied basis). -/
theorem normal_deriv (k : ℕ) (z : ℂ) :
    Commute (ContinuousLinearMap.adjoint (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z))
      (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z) :=
  (isDiag_deriv hκ hN hb k z).normal

/-- `S_N(z)` itself is normal. -/
theorem normal_transfer (z : ℂ) :
    Commute (ContinuousLinearMap.adjoint (normalizedTransfer L κ N z)) (normalizedTransfer L κ N z) := by
  have h := normal_deriv hκ hN hb 0 z
  simpa only [iteratedDeriv_zero] using h

/-- **All spectral derivatives, at all spectral parameters, commute.** -/
theorem commute_deriv (k l : ℕ) (z w : ℂ) :
    Commute (iteratedDeriv k (fun v => normalizedTransfer L κ N v) z)
      (iteratedDeriv l (fun v => normalizedTransfer L κ N v) w) :=
  (isDiag_deriv hκ hN hb k z).commute (isDiag_deriv hκ hN hb l w)

/-- **PROP-008 actual-transfer moments with `hnormal` discharged** by the supplied Bethe basis. -/
theorem transfer_moments_bethe {b' : ℝ} (hb' : 0 ≤ b') (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ)
    (hz : -b' ≤ z.im) {p : ℕ} (hp : 1 ≤ p) :
    ⟪wvec N u, ((ContinuousLinearMap.adjoint (normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : BoundedSymmetricKernel (L2T L) N)) *
        (normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : BoundedSymmetricKernel (L2T L) N))) ^ p) (wvec N u)⟫_ℂ =
      ((‖((normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 : ℝ) : ℂ) ∧
    ‖((normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 ≤
      Cunif L κ b' p / (N : ℝ) ^ p :=
  transfer_moments hκ.le hb' u hu z hz hN (normal_transfer hκ hN hb z) hp

/-- **PROP-008 spectral-parameter derivative clause with `hnormal` discharged** by the supplied
Bethe basis. -/
theorem transfer_moments_deriv_bethe {b' R : ℝ} (hb' : 0 ≤ b') (hR : 0 < R) (u : L2T L)
    (hu : ‖u‖ = 1) (z : ℂ) (hz : -b' ≤ z.im) (k : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    ⟪wvec N u, ((ContinuousLinearMap.adjoint
        (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
          iteratedDeriv k (fun w => productSymbol L κ u w) z •
            (1 : BoundedSymmetricKernel (L2T L) N)) *
        (iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
          iteratedDeriv k (fun w => productSymbol L κ u w) z •
            (1 : BoundedSymmetricKernel (L2T L) N))) ^ p) (wvec N u)⟫_ℂ =
      ((‖((iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
          iteratedDeriv k (fun w => productSymbol L κ u w) z •
            (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 : ℝ) : ℂ) ∧
    ‖((iteratedDeriv k (fun w => normalizedTransfer L κ N w) z -
        iteratedDeriv k (fun w => productSymbol L κ u w) z •
          (1 : BoundedSymmetricKernel (L2T L) N)) ^ p) (wvec N u)‖ ^ 2 ≤
      Cder L κ b' R k p / (N : ℝ) ^ p :=
  transfer_moments_deriv hκ.le hb' hR u hu z hz hN k (normal_deriv hκ hN hb k z) hp

end Bridge

#print axioms transfer_basis
#print axioms deriv_basis
#print axioms normal_deriv
#print axioms normal_transfer
#print axioms commute_deriv
#print axioms transfer_moments_bethe
#print axioms transfer_moments_deriv_bethe

end QuantumNLS.NormalityBridge
