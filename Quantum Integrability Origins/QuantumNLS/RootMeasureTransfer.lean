import Mathlib
import QuantumNLS.RootMeasureComplex
import QuantumNLS.BulkResponseActual
import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.RootPlacementBound
import QuantumNLS.NormalizedTransfer
import QuantumNLS.ExactDensity
import QuantumNLS.HighMomentsTransfer

/-!
# R-09E1EAE9 `thm:root-measure`: the transfer eigenvalue as a random variable, and its first two moments

Source: `ROOT_spectral_measure.tex` (`eq:root-quantum-input`, `lem:root-placement` R-FFA8D3F2, `eq:root-symbol`,
`eq:root-transfer-estimates`).  This module identifies the on-shell eigenvalue of the accepted physical basis with the printed
product `s_N(z) = ∏(1 + iκ/(N(z−q_j))) + e^{izL}∏(1 − iκ/(N(z−q_j)))` over the DEF-006 roots `q = arrRoots L (κ/N) m`
(`eigen_eq_sProd`), and the spectral expectation identities of a diagonal operator on a Hilbert basis (`hasSum_inner_diag`,
`hasSum_norm_sq_diag`).  Imports read-only: UBB1 (`UnconditionalBetheBasis`), `NormalityBridge.eigen`, DEF-006
`BetheLabels`, `RootPlacementBound.lem_root_placement`, `NormalizedTransfer`.  No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.RootMeasureTransfer

section Spectral

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem adjoint_diag [DecidableEq ι] (b : HilbertBasis ι ℂ E) (S : E →L[ℂ] E) (lam : ι → ℂ)
    (hS : ∀ i, S (b i) = lam i • b i) (k : ι) :
    ContinuousLinearMap.adjoint S (b k) = conj (lam k) • b k := by
  refine b.repr.injective (lp.ext (funext fun i => ?_))
  rw [HilbertBasis.repr_apply_apply, map_smul, lp.coeFn_smul, Pi.smul_apply,
    HilbertBasis.repr_apply_apply, ContinuousLinearMap.adjoint_inner_right, hS i, inner_smul_left,
    smul_eq_mul]
  by_cases hik : i = k
  · subst hik; rfl
  · rw [b.orthonormal.inner_eq_zero hik]; simp

/-- A diagonal operator acts on the coordinates `⟨b_k, ·⟩` by the eigenvalue. -/
theorem inner_diag_apply [DecidableEq ι] (b : HilbertBasis ι ℂ E) (S : E →L[ℂ] E) (lam : ι → ℂ)
    (hS : ∀ i, S (b i) = lam i • b i) (x : E) (k : ι) :
    ⟪b k, S x⟫_ℂ = lam k * ⟪b k, x⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_diag b S lam hS k, inner_smul_left]
  simp

/-- **Spectral expectation**: `⟨x, S x⟩ = ∑ᵢ |⟨bᵢ, x⟩|² λᵢ` for a diagonal `S`. -/
theorem hasSum_inner_diag [DecidableEq ι] (b : HilbertBasis ι ℂ E) (S : E →L[ℂ] E) (lam : ι → ℂ)
    (hS : ∀ i, S (b i) = lam i • b i) (x : E) :
    HasSum (fun i => ((‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) * lam i) ⟪x, S x⟫_ℂ := by
  have h := b.hasSum_inner_mul_inner x (S x)
  convert h using 1
  funext i
  rw [inner_diag_apply b S lam hS x i, ← inner_conj_symm (𝕜 := ℂ) x (b i)]
  have hc : (starRingEnd ℂ) ⟪b i, x⟫_ℂ * ⟪b i, x⟫_ℂ = ((‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  calc ((‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) * lam i = ((starRingEnd ℂ) ⟪b i, x⟫_ℂ * ⟪b i, x⟫_ℂ) * lam i := by
        rw [hc]
    _ = _ := by ring

end Spectral


section SpectralNorm

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem hasSum_norm_sq (b : HilbertBasis ι ℂ E) (y : E) :
    HasSum (fun i => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  have h := QuantumNLS.ExactDensity.lp_sq_hasSum (b.repr y)
  simpa [HilbertBasis.repr_apply_apply] using h

/-- **Spectral variance**: `‖(S − a)x‖² = ∑ᵢ |⟨bᵢ, x⟩|² |λᵢ − a|²` for a diagonal `S`. -/
theorem hasSum_norm_sq_diag [DecidableEq ι] (b : HilbertBasis ι ℂ E) (S : E →L[ℂ] E) (lam : ι → ℂ)
    (hS : ∀ i, S (b i) = lam i • b i) (a : ℂ) (x : E) :
    HasSum (fun i => ‖⟪b i, x⟫_ℂ‖ ^ 2 * ‖lam i - a‖ ^ 2) (‖(S - a • (1 : E →L[ℂ] E)) x‖ ^ 2) := by
  have hT : ∀ i, (S - a • (1 : E →L[ℂ] E)) (b i) = (lam i - a) • b i := by
    intro i; simp [hS i, sub_smul]
  have h := hasSum_norm_sq b ((S - a • (1 : E →L[ℂ] E)) x)
  convert h using 1
  funext i
  rw [inner_diag_apply b _ (fun i => lam i - a) hT x i, norm_mul, mul_pow, mul_comm]

end SpectralNorm

section Physical

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.NormalityBridge (eigen label cpos)
open QuantumNLS.RootMeasureComplex (sProd GN fz HighHalf)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)

theorem label_val (m : MArr N) :
    (label m).1 = QuantumNLS.BetheLabels.srcOf
      (QuantumNLS.BetheLabels.correctedInt (QuantumNLS.BetheLabels.labelsEquivArr.symm m)) := by
  have h1 : (label m).1 = QuantumNLS.BetheLabels.srcOf
      (QuantumNLS.BetheLabels.correctedEquivArr.symm m).1 := rfl
  rw [h1]
  congr 1
  have h2 := QuantumNLS.BetheLabels.labelsEquivCorrected.apply_symm_apply
    (QuantumNLS.BetheLabels.correctedEquivArr.symm m)
  have h3 : QuantumNLS.BetheLabels.labelsEquivArr.symm m =
      QuantumNLS.BetheLabels.labelsEquivCorrected.symm
        (QuantumNLS.BetheLabels.correctedEquivArr.symm m) := rfl
  rw [h3]
  exact (congrArg Subtype.val h2).symm

/-- **The on-shell eigenvalue is the printed product** (`eq:root-quantum-input`): for `Im z > 0`, the eigenvalue of the physical
Bethe vector of label `m` is `∏(1 + iκ/(N(z−q_j))) + e^{izL}∏(1 − iκ/(N(z−q_j)))` over the DEF-006 roots. -/
theorem eigen_eq_sProd (m : MArr N) (z : ℂ) (hz : 0 < z.im) :
    eigen (L := L) κ hκ hN m z = sProd L κ N (arrRoots L (κ / N) m) z := by
  have hc : 0 < κ / (N : ℝ) := cpos hκ hN
  have hL : 0 < L := Fact.out
  unfold eigen
  rw [QuantumNLS.BetheSpectralContinuity.spectralValue_nonpole L hc (label m).2 z (by
    intro k hk
    have := congrArg Complex.im hk
    simp at this; linarith)]
  unfold QuantumNLS.TransferSeparation.sFun sProd
  have hroot : ∀ i, QuantumNLS.BetheSmooth.sourceRoots L (label m).1 (κ / N) i =
      arrRoots L (κ / N) m (Fin.rev i) := by
    intro i
    rw [label_val]
    exact QuantumNLS.BetheLabels.sourceRoots_eq_roots_rev hL hc _ i
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have e1 : ∀ i, (Complex.I * ((κ / N : ℝ) : ℂ) / (z - (QuantumNLS.BetheSmooth.sourceRoots L (label m).1 (κ / N) i : ℂ))) =
      Complex.I * κ / (N * (z - (arrRoots L (κ / N) m (Fin.rev i) : ℂ))) := by
    intro i
    rw [hroot i]; push_cast; field_simp
  simp only [e1]
  have p1 := Equiv.prod_comp Fin.revPerm
    (fun j => (1 + Complex.I * κ / (N * (z - (arrRoots L (κ / N) m j : ℂ)))))
  have p2 := Equiv.prod_comp Fin.revPerm
    (fun j => (1 - Complex.I * κ / (N * (z - (arrRoots L (κ / N) m j : ℂ)))))
  simp only [Fin.revPerm_apply] at p1 p2
  rw [p1, p2]
  congr 2
  ring_nf

end Physical

section Variance

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.NormalityBridge (eigen)
open QuantumNLS.RootMeasureComplex (sProd)
open QuantumNLS.NormalizedTransfer (normalizedTransfer productSymbol)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis transfer_physicalBasis)
open QuantumNLS.HighMomentsOps (wvec)
open QuantumNLS.HighMomentsTransfer (Cunif)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)

/-- **`E|s_N(z) − s(z;u)|² = ‖(S_N(z) − s(z;u)) u^{⊗N}‖²`** under the Born law of the physical basis. -/
theorem hasSum_born_variance (u : L2T L) (z : ℂ) (hz : 0 < z.im) :
    HasSum (fun m : MArr N => bornLaw (meanField_physicalBasis L N hN hκ) u m *
        ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ^ 2)
      (‖(normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) (wvec N u)‖ ^ 2) := by
  classical
  have h := hasSum_norm_sq_diag (meanField_physicalBasis L N hN hκ) (normalizedTransfer L κ N z)
    (fun m => eigen (L := L) κ hκ hN m z) (fun m => transfer_physicalBasis hκ hN z m)
    (productSymbol L κ u z) (wvec N u)
  convert h using 1
  funext m
  rw [eigen_eq_sProd hκ hN m z hz]
  rfl

/-- **PROP-008 physical moment bound, `p = 1`**: `E|s_N(z) − s(z;u)|² ≤ C/N`, `C = C₁(0)` independent of `z` (`Im z ≥ 0`),
`u` and `N`. -/
theorem born_variance_le (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ) (hz : 0 < z.im) :
    ∑' m : MArr N, bornLaw (meanField_physicalBasis L N hN hκ) u m *
        ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ^ 2 ≤
      Cunif L κ 0 1 / N := by
  rw [(hasSum_born_variance hκ hN u z hz).tsum_eq]
  have h := (QuantumNLS.UnconditionalBetheBasis.transfer_moments_physical hκ hN (b' := 0) le_rfl u hu z
    (by simpa using hz.le) (p := 1) le_rfl).2
  simpa using h

end Variance

end QuantumNLS.RootMeasureTransfer

#print axioms QuantumNLS.RootMeasureTransfer.hasSum_inner_diag
#print axioms QuantumNLS.RootMeasureTransfer.hasSum_norm_sq_diag
#print axioms QuantumNLS.RootMeasureTransfer.eigen_eq_sProd
#print axioms QuantumNLS.RootMeasureTransfer.hasSum_born_variance
#print axioms QuantumNLS.RootMeasureTransfer.born_variance_le
