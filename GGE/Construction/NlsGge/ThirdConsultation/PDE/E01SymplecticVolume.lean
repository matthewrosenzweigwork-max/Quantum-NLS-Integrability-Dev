import Mathlib
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6014
import NlsGge.Atomic.G6.G6028
import NlsGge.ThirdConsultation.PDE.ActualEnsemble
import NlsGge.Birkhoff.S04FiniteGapInvariance38
import NlsGge.Measure.FiniteGaussian

                                                                            
                                                                              
                                                                            
                                                                            
                                                                   

set_option autoImplicit false

open MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped BigOperators ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- The actual zero extension into square-summable complex sequences, as a
continuous linear map. No off-domain branch is needed on this finite carrier. -/
def E01_finiteInclusion (Λ : Finset ℤ) :
    (Λ → ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  ∑ n : Λ,
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).comp
      (ContinuousLinearMap.proj n)

theorem E01_finiteInclusion_apply (Λ : Finset ℤ) (z : Λ → ℂ) (n : ℤ) :
    E01_finiteInclusion Λ z n = extZero38 Λ z n := by
  classical
  simp only [E01_finiteInclusion, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, lp.singleContinuousLinearMap_apply,
    lp.coeFn_sum, Finset.sum_apply]
  by_cases hn : n ∈ Λ
  · rw [Finset.sum_eq_single (⟨n, hn⟩ : Λ)]
    · rw [lp.single_apply_self, extZero38_apply_of_mem z hn]
    · intro i _ hi
      exact lp.single_apply_ne _ _ _ (fun h => hi (Subtype.ext h.symm))
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · rw [extZero38_apply_of_not_mem z hn]
    apply Finset.sum_eq_zero
    intro i _
    exact lp.single_apply_ne _ _ _ (fun h => hn (h.symm ▸ i.property))

/-- Identification with the existing chart, rather than a new inverse chart. -/
theorem E01_finiteGapField_eq (Λ : Finset ℤ) :
    NlsGge.ThirdConsultation.PDE.finiteGapField Λ =
      physicalInverseBirkhoff ∘ E01_finiteInclusion Λ := by
  funext z
  unfold NlsGge.ThirdConsultation.PDE.finiteGapField
    BirkhoffTop38.finiteGapField38
  rw [NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_cleanPhiInv _
    (extZero38_mem_zero Λ z)]
  change physicalInverseBirkhoff (seqToLp38 _ _) =
    physicalInverseBirkhoff (E01_finiteInclusion Λ z)
  congr 1
  ext n
  exact (E01_finiteInclusion_apply Λ z n).symm

/-- Differentiate the genuine right inverse identity on the whole lp carrier. -/
theorem E01_inverseBirkhoff_fderiv_right
    (w h : lp (fun _ : ℤ => ℂ) 2) :
    fderiv ℝ physicalBirkhoff (physicalInverseBirkhoff w)
      (fderiv ℝ physicalInverseBirkhoff w h) = h := by
  have hΦ := (G6014.2.2.1 (physicalInverseBirkhoff w) (Set.mem_univ _)).differentiableAt
  have hΨ := (G6014.2.2.2.1 w (Set.mem_univ _)).differentiableAt
  have hid : physicalBirkhoff ∘ physicalInverseBirkhoff = id :=
    funext G6013.2.2.2.2.2
  have hd := hΦ.hasFDerivAt.comp w hΨ.hasFDerivAt
  rw [hid] at hd
  have he := hd.unique (hasFDerivAt_id w)
  exact congrArg (fun L : (lp (fun _ : ℤ => ℂ) 2) →L[ℝ]
    lp (fun _ : ℤ => ℂ) 2 => L h) he

/-- Differentiate the genuine left inverse identity on PhysicalL2 as well. -/
theorem E01_inverseBirkhoff_fderiv_left (u h : PhysicalL2) :
    fderiv ℝ physicalInverseBirkhoff (physicalBirkhoff u)
      (fderiv ℝ physicalBirkhoff u h) = h := by
  have hΦ := (G6014.2.2.1 u (Set.mem_univ _)).differentiableAt
  have hΨ := (G6014.2.2.2.1 (physicalBirkhoff u) (Set.mem_univ _)).differentiableAt
  have hid : physicalInverseBirkhoff ∘ physicalBirkhoff = id :=
    funext G6013.2.2.2.2.1
  have hd := hΨ.hasFDerivAt.comp u hΦ.hasFDerivAt
  rw [hid] at hd
  have he := hd.unique (hasFDerivAt_id u)
  exact congrArg (fun L : PhysicalL2 →L[ℝ] PhysicalL2 => L h) he

theorem E01_finiteGapField_hasFDerivAt (Λ : Finset ℤ) (z : Λ → ℂ) :
    HasFDerivAt (NlsGge.ThirdConsultation.PDE.finiteGapField Λ)
      ((fderiv ℝ physicalInverseBirkhoff (E01_finiteInclusion Λ z)).comp
        ((E01_finiteInclusion Λ).restrictScalars ℝ)) z := by
  rw [E01_finiteGapField_eq]
  exact ((G6014.2.2.2.1 _ (Set.mem_univ _)).differentiableAt.hasFDerivAt).comp z
    ((E01_finiteInclusion Λ).restrictScalars ℝ).hasFDerivAt

/-- Finite support proves summability before the infinite form is evaluated. -/
theorem E01_finiteInclusion_symplectic (Λ : Finset ℤ) (h k : Λ → ℂ) :
    inner ℝ ((Complex.I : ℂ) • E01_finiteInclusion Λ h)
      (E01_finiteInclusion Λ k) =
        ∑ n : Λ, (starRingEnd ℂ (h n) * k n).im := by
  classical
  rw [← NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.stdSymplectic38_lp]
  unfold stdSymplectic38
  simp_rw [E01_finiteInclusion_apply]
  have hs : HasSum
      (fun n : ℤ => (starRingEnd ℂ (extZero38 Λ h n) * extZero38 Λ k n).im)
      (∑ n ∈ Λ, (starRingEnd ℂ (extZero38 Λ h n) * extZero38 Λ k n).im) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      rw [extZero38_apply_of_not_mem h hn, extZero38_apply_of_not_mem k hn]
      simp)
  rw [hs.tsum_eq, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro n _
  rw [extZero38_apply_of_mem h n.property, extZero38_apply_of_mem k n.property]

/-- The literal physical pullback along the actual finite-gap chart. This form
is written without the factor two; the Gram matrix below restores that factor. -/
theorem E01_finiteGap_symplectic_pullback
    (Λ : Finset ℤ) (z h k : Λ → ℂ) :
    DifferentiableAt ℝ (NlsGge.ThirdConsultation.PDE.finiteGapField Λ) z ∧
    inner ℝ
      ((Complex.I : ℂ) •
        fderiv ℝ (NlsGge.ThirdConsultation.PDE.finiteGapField Λ) z h)
      (fderiv ℝ (NlsGge.ThirdConsultation.PDE.finiteGapField Λ) z k) =
        ∑ n : Λ, (starRingEnd ℂ (h n) * k n).im := by
  have hD := E01_finiteGapField_hasFDerivAt Λ z
  refine ⟨hD.differentiableAt, ?_⟩
  rw [hD.fderiv]
  have hS := G6028.2.2.1 (physicalInverseBirkhoff (E01_finiteInclusion Λ z))
    (fderiv ℝ physicalInverseBirkhoff (E01_finiteInclusion Λ z)
      (E01_finiteInclusion Λ h))
    (fderiv ℝ physicalInverseBirkhoff (E01_finiteInclusion Λ z)
      (E01_finiteInclusion Λ k))
  rw [E01_inverseBirkhoff_fderiv_right, E01_inverseBirkhoff_fderiv_right] at hS
  exact hS.symm.trans (E01_finiteInclusion_symplectic Λ h k)

/-- Standard real coordinate vectors: true is the real direction and false is
the imaginary direction. The order only changes the orientation sign. -/
def E01_finiteGapRealFrame (Λ : Finset ℤ) (i : Λ × Bool) (n : Λ) : ℂ :=
  if n = i.1 then (if i.2 then 1 else Complex.I) else 0

/-- Orthonormality for the ordinary Euclidean real scalar product on the
finite product of planes, written as a finite sum rather than a sup norm. -/
theorem E01_finiteGapRealFrame_orthonormal (Λ : Finset ℤ) (i j : Λ × Bool) :
    (∑ n : Λ, (starRingEnd ℂ (E01_finiteGapRealFrame Λ i n) *
      E01_finiteGapRealFrame Λ j n).re) = if i = j then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single i.1]
  · rcases i with ⟨a, b⟩
    rcases j with ⟨a', c⟩
    by_cases haa : a = a'
    · subst a'
      cases b <;> cases c <;> simp [E01_finiteGapRealFrame]
    · cases b <;> cases c <;>
        simp [E01_finiteGapRealFrame, haa, Prod.ext_iff]
  · intro n _ hni
    simp [E01_finiteGapRealFrame, hni]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

/-- Every coordinate vector has its usual real-and-imaginary expansion in
this frame. Together with orthonormality, this verifies the real basis. -/
theorem E01_finiteGapRealFrame_spanning (Λ : Finset ℤ) (z : Λ → ℂ) :
    (∑ n : Λ,
      ((z n).re • E01_finiteGapRealFrame Λ (n, true) +
       (z n).im • E01_finiteGapRealFrame Λ (n, false))) = z := by
  classical
  funext m
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single m]
  · simpa [E01_finiteGapRealFrame, Algebra.smul_def] using Complex.re_add_im (z m)
  · intro n _ hnm
    simp [E01_finiteGapRealFrame, Ne.symm hnm]
  · intro hm
    exact (hm (Finset.mem_univ _)).elim

/-- Gram matrix of the literal pulled-back physical two-form, with the factor
two required by the Poisson convention in v2:194. -/
def E01_finiteGapSymplecticGram (Λ : Finset ℤ) (z : Λ → ℂ) :
    Matrix (Λ × Bool) (Λ × Bool) ℝ :=
  fun i j => 2 * inner ℝ
    ((Complex.I : ℂ) • fderiv ℝ
      (NlsGge.ThirdConsultation.PDE.finiteGapField Λ) z (E01_finiteGapRealFrame Λ i))
    (fderiv ℝ (NlsGge.ThirdConsultation.PDE.finiteGapField Λ) z
      (E01_finiteGapRealFrame Λ j))

def E01_symplecticPlaneBlock : Matrix Bool Bool ℝ :=
  fun b c => if b then (if c then 0 else 2) else (if c then -2 else 0)

theorem E01_finiteGapSymplecticGram_apply
    (Λ : Finset ℤ) (z : Λ → ℂ) (i j : Λ × Bool) :
    E01_finiteGapSymplecticGram Λ z i j =
      if i.1 = j.1 then E01_symplecticPlaneBlock i.2 j.2 else 0 := by
  classical
  unfold E01_finiteGapSymplecticGram
  rw [(E01_finiteGap_symplectic_pullback Λ z
    (E01_finiteGapRealFrame Λ i) (E01_finiteGapRealFrame Λ j)).2]
  rw [Finset.sum_eq_single i.1]
  · rcases i with ⟨a, b⟩
    rcases j with ⟨a', c⟩
    by_cases haa : a = a'
    · subst a'
      cases b <;> cases c <;>
        simp [E01_finiteGapRealFrame, E01_symplecticPlaneBlock]
    · cases b <;> cases c <;>
        simp [E01_finiteGapRealFrame, E01_symplecticPlaneBlock, haa]
  · intro n _ hni
    simp [E01_finiteGapRealFrame, hni]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

theorem E01_symplecticPlaneBlock_det : E01_symplecticPlaneBlock.det = 4 := by
  calc
    E01_symplecticPlaneBlock.det =
        (Matrix.reindex finTwoEquiv.symm finTwoEquiv.symm E01_symplecticPlaneBlock).det :=
      (Matrix.det_reindex_self finTwoEquiv.symm E01_symplecticPlaneBlock).symm
    _ = 4 := by
      rw [Matrix.det_fin_two]
      norm_num [Matrix.reindex_apply, Matrix.submatrix_apply,
        E01_symplecticPlaneBlock, finTwoEquiv]

theorem E01_finiteGapSymplecticGram_det (Λ : Finset ℤ) (z : Λ → ℂ) :
    (E01_finiteGapSymplecticGram Λ z).det = (4 : ℝ) ^ Λ.card := by
  classical
  have hA : E01_finiteGapSymplecticGram Λ z =
      Matrix.reindex (Equiv.prodComm Bool Λ) (Equiv.prodComm Bool Λ)
        (Matrix.blockDiagonal (fun _ : Λ => E01_symplecticPlaneBlock)) := by
    ext i j
    rw [E01_finiteGapSymplecticGram_apply]
    rfl
  rw [hA, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp only [E01_symplecticPlaneBlock_det, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe]

theorem E01_finiteGapSymplecticGram_density (Λ : Finset ℤ) (z : Λ → ℂ) :
    Real.sqrt |(E01_finiteGapSymplecticGram Λ z).det| = (2 : ℝ) ^ Λ.card := by
  rw [E01_finiteGapSymplecticGram_det,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)]
  have hpow : (4 : ℝ) ^ Λ.card = (2 : ℝ) ^ Λ.card * (2 : ℝ) ^ Λ.card := by
    rw [← mul_pow]
    norm_num
  rw [hpow, Real.sqrt_mul_self (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]

theorem E01_finiteGap_volume_constant_pos (Λ : Finset ℤ) :
    0 < (2 : ℝ) ^ Λ.card :=
  pow_pos (by norm_num) _

/-- Determinant formulation of the genuine Liouville density in the standard
real coordinates of the actual inverse chart. See the accompanying report for
the exterior-power justification of the square-root determinant formula. -/
theorem E01_finiteGap_symplectic_volume (Λ : Finset ℤ) :
    let κ : (Λ → ℂ) → PhysicalL2 :=
      NlsGge.ThirdConsultation.PDE.finiteGapField Λ
    let e : (Λ × Bool) → (Λ → ℂ) :=
      fun i n => if n = i.1 then (if i.2 then 1 else Complex.I) else 0
    let A : (Λ → ℂ) → Matrix (Λ × Bool) (Λ × Bool) ℝ :=
      fun z i j => 2 * inner ℝ
        ((Complex.I : ℂ) • fderiv ℝ κ z (e i))
        (fderiv ℝ κ z (e j))
    (∀ z : Λ → ℂ, DifferentiableAt ℝ κ z ∧
      Real.sqrt |Matrix.det (A z)| = (2 : ℝ) ^ Λ.card) ∧
    (NlsGge.Measure.finiteComplexVolume Λ).withDensity
      (fun z => ENNReal.ofReal (Real.sqrt |Matrix.det (A z)|)) =
        ENNReal.ofReal ((2 : ℝ) ^ Λ.card) •
          NlsGge.Measure.finiteComplexVolume Λ := by
  change (∀ z : Λ → ℂ,
      DifferentiableAt ℝ (NlsGge.ThirdConsultation.PDE.finiteGapField Λ) z ∧
        Real.sqrt |(E01_finiteGapSymplecticGram Λ z).det| = (2 : ℝ) ^ Λ.card) ∧
    (NlsGge.Measure.finiteComplexVolume Λ).withDensity
      (fun z => ENNReal.ofReal (Real.sqrt |(E01_finiteGapSymplecticGram Λ z).det|)) =
        ENNReal.ofReal ((2 : ℝ) ^ Λ.card) • NlsGge.Measure.finiteComplexVolume Λ
  constructor
  · intro z
    exact ⟨(E01_finiteGapField_hasFDerivAt Λ z).differentiableAt,
      E01_finiteGapSymplecticGram_density Λ z⟩
  · simp_rw [E01_finiteGapSymplecticGram_density]
    exact MeasureTheory.withDensity_const _

end
end NlsGge.GKDefinitionDesign
