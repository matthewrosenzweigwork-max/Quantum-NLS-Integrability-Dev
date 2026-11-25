import LiebLiniger.FixedPeriod.Quantum.Q4001FirstContractionReal
import LiebLiniger.FixedPeriod.Atomic.EXT.R2b1
import LiebLiniger.FixedPeriod.Atomic.EXT.R2a
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul

/-! # Physical finite-gap Liouville measure

The actual physical form is twice the normalized form preserved in R2a.
Darboux normalization, rather than the desired volume equality, defines the
coordinate Liouville measure. The actual global finite-gap chart transports
that form-derived measure to the physical finite-gap range.
-/
set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open Module MeasureTheory MeasureTheory.Measure
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.PDE
open LiebLiniger.FixedPeriod.Conditional
open scoped ComplexConjugate

/-- The physical real symplectic form `2 inner ℝ (i • h) k` on physical L².
The doubling is dual to the half factor in the physical Poisson bracket. -/
def physicalSymplecticForm38 : PhysicalL2 →ₗ[ℝ] PhysicalL2 →ₗ[ℝ] ℝ :=
  (2 : ℝ) • (innerₗ PhysicalL2).comp (Complex.I • LinearMap.id)

@[simp] theorem physicalSymplecticForm38_apply (h k : PhysicalL2) :
    physicalSymplecticForm38 h k = 2 * inner ℝ (Complex.I • h) k := rfl

/-- Pull back the physical form by the derivative of the SAME actual
global finite-gap embedding, at every point of the entire finite plane. -/
def pullPhysForm38 (Λ : Finset ℤ) (w : Λ → ℂ) :
    (Λ → ℂ) →ₗ[ℝ] (Λ → ℂ) →ₗ[ℝ] ℝ :=
  physicalSymplecticForm38.compl₁₂
    (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w).toLinearMap
    (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w).toLinearMap

/-- The physical coordinate form, obtained by finite insertion into genuine
ℓ² with its normalized symplectic pairing, multiplied by two. -/
def finitePhysicalForm38 (Λ : Finset ℤ) :
    (Λ → ℂ) →ₗ[ℝ] (Λ → ℂ) →ₗ[ℝ] ℝ :=
  ((2 : ℝ) • (innerₗ LLFPBirkhoffCoordinates).comp (Complex.I • LinearMap.id)).compl₁₂
    (finiteSeqCLM38 Λ).toLinearMap (finiteSeqCLM38 Λ).toLinearMap

@[simp] theorem finitePhysicalForm38_apply (Λ : Finset ℤ) (h k : Λ → ℂ) :
    finitePhysicalForm38 Λ h k = 2 * ∑ i : Λ, (conj (h i) * k i).im := by
  change 2 * inner ℝ (Complex.I • finiteSeqCLM38 Λ h) (finiteSeqCLM38 Λ k) = _
  rw [finiteSeqCLM38_normalized_symplectic]

/-- Actual canonicity proves that the variable pulled-back form is constant
on the whole coordinate plane. No stratum or nonzero action is removed. -/
theorem pullPhysForm38_eq (Λ : Finset ℤ) (w : Λ → ℂ) :
    pullPhysForm38 Λ w = finitePhysicalForm38 Λ := by
  apply LinearMap.ext
  intro h
  apply LinearMap.ext
  intro k
  exact (actual_finiteGap_physical_symplectic_pullback Λ w h k).trans
    (finitePhysicalForm38_apply Λ h k).symm

/-- Cartesian real coordinates of the finite complex plane, with the
real components first and imaginary components second. -/
def finiteCartesianEquiv38 (Λ : Finset ℤ) :
    ((Λ → ℝ) × (Λ → ℝ)) ≃ₗ[ℝ] (Λ → ℂ) where
  toFun p := fun i => ⟨p.1 i, p.2 i⟩
  invFun w := (fun i => (w i).re, fun i => (w i).im)
  left_inv := by intro p; rfl
  right_inv := by intro w; rfl
  map_add' := by intro p q; rfl
  map_smul' := by
    intro r p
    funext i
    apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im]

/-- The ordinary real Cartesian basis, before physical Darboux rescaling. -/
def finiteCartesianBasis38 (Λ : Finset ℤ) : Basis (Λ ⊕ Λ) ℝ (Λ → ℂ) :=
  ((Pi.basisFun ℝ Λ).prod (Pi.basisFun ℝ Λ)).map (finiteCartesianEquiv38 Λ)

@[simp] theorem finiteCartesianBasis38_inl (Λ : Finset ℤ) (i : Λ) :
    finiteCartesianBasis38 Λ (Sum.inl i) = Pi.single i (1 : ℂ) := by
  ext j
  simp [finiteCartesianBasis38, Basis.prod_apply, finiteCartesianEquiv38,
    Pi.basisFun_apply, Pi.single_apply]
  split_ifs <;> rfl

@[simp] theorem finiteCartesianBasis38_inr (Λ : Finset ℤ) (i : Λ) :
    finiteCartesianBasis38 Λ (Sum.inr i) = Pi.single i Complex.I := by
  ext j
  simp [finiteCartesianBasis38, Basis.prod_apply, finiteCartesianEquiv38,
    Pi.basisFun_apply, Pi.single_apply]
  split_ifs <;> rfl

private theorem physicalDarbouxWeight_unit38 (Λ : Finset ℤ) :
    ∀ a : Λ ⊕ Λ, IsUnit (Sum.elim (fun _ => (1 : ℝ)) (fun _ => (1 / 2 : ℝ)) a) := by
  intro a
  cases a <;> norm_num

/-- Physical Darboux vectors are `pᵢ=eₓᵢ` and `qᵢ=eᵧᵢ/2`. This is a real
basis of the full plane, including its unique zero-dimensional case. -/
def physicalDarbouxVectors38 (Λ : Finset ℤ) : Basis (Λ ⊕ Λ) ℝ (Λ → ℂ) :=
  (finiteCartesianBasis38 Λ).isUnitSMul (physicalDarbouxWeight_unit38 Λ)

@[simp] theorem physicalDarbouxVectors38_inl (Λ : Finset ℤ) (i : Λ) :
    physicalDarbouxVectors38 Λ (Sum.inl i) = Pi.single i (1 : ℂ) := by
  simp [physicalDarbouxVectors38, Basis.isUnitSMul_apply]

@[simp] theorem physicalDarbouxVectors38_inr (Λ : Finset ℤ) (i : Λ) :
    physicalDarbouxVectors38 Λ (Sum.inr i) = Pi.single i (Complex.I / 2) := by
  simp only [physicalDarbouxVectors38, Basis.isUnitSMul_apply, Sum.elim_inr,
    finiteCartesianBasis38_inr]
  ext j
  by_cases hj : i = j <;> simp [Pi.single_apply, hj, Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Evaluation on coordinate-supported vectors, used to check the Darboux matrix. -/
theorem finitePhysicalForm38_single (Λ : Finset ℤ) (i j : Λ) (a b : ℂ) :
    finitePhysicalForm38 Λ (Pi.single i a) (Pi.single j b) =
      if i = j then 2 * (conj a * b).im else 0 := by
  classical
  rw [finitePhysicalForm38_apply, Finset.sum_eq_single j]
  · by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · intro l _ hlj
    simp [Pi.single_apply, hlj]
  · simp

/-- The explicit physically normalized basis is Darboux for the coordinate
form: its real matrix is `[0,1;-1,0]`. -/
def physicalDarbouxBasis38 (Λ : Finset ℤ) :
    DarbouxBasis38 (ι := Λ) (finitePhysicalForm38 Λ) where
  basis := physicalDarbouxVectors38 Λ
  matrix_eq := by
    ext (i | i) (j | j) <;>
      simp only [LinearMap.toMatrix₂_apply, physicalDarbouxVectors38_inl,
        physicalDarbouxVectors38_inr, finitePhysicalForm38_single]
    all_goals
      by_cases hij : i = j <;>
        norm_num [hij, Matrix.J, Matrix.fromBlocks, Matrix.one_apply,
          Complex.div_re, Complex.div_im, map_ofNat]

private theorem basisFun_addHaar38 (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).addHaar = (volume : Measure (ι → ℝ)) := by
  rw [Basis.addHaar_def, Basis.parallelepiped_basisFun, addHaarMeasure_eq_volume_pi]

/-- Real and imaginary coordinate assembly preserves ordinary product
Lebesgue volume; this fixes the ordinary planar normalization. -/
theorem finiteCartesianEquiv38_measurePreserving (Λ : Finset ℤ) :
    MeasurePreserving (finiteCartesianEquiv38 Λ)
      ((volume : Measure (Λ → ℝ)).prod volume) (NlsGge.Measure.finiteComplexVolume Λ) := by
  have h₁ := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ Λ).symm
  have h₂ := measurePreserving_pi
    (fun _ : Λ => (volume : Measure (ℝ × ℝ)))
    (fun _ : Λ => (volume : Measure ℂ))
    (fun _ => Complex.volume_preserving_equiv_real_prod.symm)
  convert h₂.comp h₁ using 1 <;> rfl

/-- The Cartesian basis Haar measure is exactly the existing ordinary
product of planar complex Lebesgue measures. -/
theorem finiteCartesianBasis38_addHaar (Λ : Finset ℤ) :
    (finiteCartesianBasis38 Λ).addHaar = NlsGge.Measure.finiteComplexVolume Λ := by
  have hm := (Module.Basis.map_addHaar
    ((Pi.basisFun ℝ Λ).prod (Pi.basisFun ℝ Λ))
    (finiteCartesianEquiv38 Λ).toContinuousLinearEquiv).symm
  simp only [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv,
    LinearEquiv.coe_toContinuousLinearEquiv'] at hm
  rw [finiteCartesianBasis38, hm, Basis.prod_addHaar,
    basisFun_addHaar38]
  exact (finiteCartesianEquiv38_measurePreserving Λ).map_eq

/-- The physical Darboux parallelepiped has ordinary coordinate volume
`2^(-|Λ|)`, with the empty product equal to one. -/
theorem physicalDarbouxVectors38_coordinateVolume (Λ : Finset ℤ) :
    NlsGge.Measure.finiteComplexVolume Λ
        (_root_.parallelepiped (physicalDarbouxVectors38 Λ)) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ Λ.card) := by
  rw [← finiteCartesianBasis38_addHaar, Measure.addHaar_parallelepiped,
    physicalDarbouxVectors38, Basis.det_isUnitSMul]
  simp [Fintype.prod_sum_type, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)]

/-- The same explicit Darboux basis for the actual variable pulled-back
physical form; its validity is earned from the actual canonicity theorem. -/
def pullPhysDarbouxBasis38 (Λ : Finset ℤ) (w : Λ → ℂ) :
    DarbouxBasis38 (ι := Λ) (pullPhysForm38 Λ w) where
  basis := physicalDarbouxVectors38 Λ
  matrix_eq := by
    rw [pullPhysForm38_eq]
    exact (physicalDarbouxBasis38 Λ).matrix_eq

/-- Physical coordinate Liouville measure, constructed from the actual
pulled-back physical form by intrinsic Darboux/Haar normalization.
The form is constant by `pullPhysForm38_eq`; the origin is only the base
point used to represent that constant form, and `muPullPhys_at` proves the
same construction at every coordinate point. -/
def muPullPhys (Λ : Finset ℤ) : Measure (Λ → ℂ) :=
  liouvilleMeasure38 (pullPhysForm38 Λ 0) ⟨pullPhysDarbouxBasis38 Λ 0⟩

/-- The intrinsic normalization works at every point of the actual chart. -/
theorem muPullPhys_at (Λ : Finset ℤ) (w : Λ → ℂ) :
    muPullPhys Λ =
      liouvilleMeasure38 (pullPhysForm38 Λ w) ⟨pullPhysDarbouxBasis38 Λ w⟩ := by
  rw [muPullPhys,
    liouvilleMeasure38_eq _ _ (pullPhysDarbouxBasis38 Λ 0),
    liouvilleMeasure38_eq _ _ (pullPhysDarbouxBasis38 Λ w)]
  rfl

/-- The pulled-back Liouville measure is characterized by translation
invariance and mass one on any Darboux parallelepiped at any chart point. -/
theorem muPullPhys_characterization (Λ : Finset ℤ) (w : Λ → ℂ)
    (b : DarbouxBasis38 (ι := Λ) (pullPhysForm38 Λ w))
    (μ : Measure (Λ → ℂ)) [SigmaFinite μ] [IsAddLeftInvariant μ] :
    muPullPhys Λ = μ ↔ μ b.basis.parallelepiped = 1 := by
  rw [muPullPhys_at Λ w]
  exact liouvilleMeasure38_characterization _ _ b μ

/-- Exact physical coordinate density, obtained from Darboux normalization.
This includes the empty plane, all zero coordinates, and the zero mode. -/
theorem muPullPhys_eq (Λ : Finset ℤ) :
    muPullPhys Λ = ENNReal.ofReal ((2 : ℝ) ^ Λ.card) •
      NlsGge.Measure.finiteComplexVolume Λ := by
  haveI : SigmaFinite (NlsGge.Measure.finiteComplexVolume Λ) := by
    unfold NlsGge.Measure.finiteComplexVolume
    infer_instance
  haveI : IsAddLeftInvariant (NlsGge.Measure.finiteComplexVolume Λ) := by
    unfold NlsGge.Measure.finiteComplexVolume
    infer_instance
  haveI : SigmaFinite (ENNReal.ofReal ((2 : ℝ) ^ Λ.card) •
      NlsGge.Measure.finiteComplexVolume Λ) := by
    change SigmaFinite (Real.toNNReal ((2 : ℝ) ^ Λ.card) •
      NlsGge.Measure.finiteComplexVolume Λ)
    infer_instance
  apply (muPullPhys_characterization Λ 0 (pullPhysDarbouxBasis38 Λ 0) _).2
  change (ENNReal.ofReal ((2 : ℝ) ^ Λ.card) • NlsGge.Measure.finiteComplexVolume Λ)
    (_root_.parallelepiped (physicalDarbouxVectors38 Λ)) = 1
  rw [Measure.smul_apply, smul_eq_mul, physicalDarbouxVectors38_coordinateVolume,
    ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _), ← mul_pow]
  norm_num

/-- The Hamiltonian vector represented by a real gradient under the
physical convention `i_X omegaPhys = dH`. -/
def physicalHamiltonianVector38 (g : PhysicalL2) : PhysicalL2 :=
  (-1 / 2 : ℝ) • (Complex.I • g)

/-- The inverse tensor of twice the normalized form is exactly the negative
half complex structure used in the existing physical Poisson definition. -/
theorem physicalHamiltonianVector38_contraction (g h : PhysicalL2) :
    physicalSymplecticForm38 (physicalHamiltonianVector38 g) h = inner ℝ g h := by
  have hv : Complex.I • physicalHamiltonianVector38 g = (1 / 2 : ℝ) • g := by
    unfold physicalHamiltonianVector38
    rw [smul_comm Complex.I (-1 / 2 : ℝ), smul_smul, Complex.I_mul_I,
      neg_one_smul, smul_neg]
    norm_num
  rw [physicalSymplecticForm38_apply, hv, real_inner_smul_left]
  ring

/-- Direct compatibility with the literal existing -1/2 canonical Poisson
bracket, for both real components of the represented derivative. -/
theorem physicalPoisson38_eq (f g : PhysicalL2 → ℂ) (u : PhysicalL2) :
    LiebLiniger.FixedPeriod.Quantum.q4001CanonicalRealPoisson spatialMeasure f g u =
      fderiv ℝ f u (physicalHamiltonianVector38
        (LiebLiniger.FixedPeriod.Quantum.q4001RealGradientRe spatialMeasure g u)) +
      Complex.I * fderiv ℝ f u (physicalHamiltonianVector38
        (LiebLiniger.FixedPeriod.Quantum.q4001RealGradientIm spatialMeasure g u)) := by
  unfold LiebLiniger.FixedPeriod.Quantum.q4001CanonicalRealPoisson
    physicalHamiltonianVector38
  simp only [map_smul, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- Contraction against the actual represented real derivative, not an
independently chosen gradient or Poisson tensor. -/
theorem physicalPoisson38_real_contraction (g : PhysicalL2 → ℂ) (u h : PhysicalL2) :
    physicalSymplecticForm38 (physicalHamiltonianVector38
      (LiebLiniger.FixedPeriod.Quantum.q4001RealGradientRe spatialMeasure g u)) h =
        (fderiv ℝ g u h).re := by
  rw [physicalHamiltonianVector38_contraction,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  letI : InnerProductSpace ℝ PhysicalL2 := ClosedSubmodule.instInnerProductSpaceReal
  rw [← real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  unfold LiebLiniger.FixedPeriod.Quantum.q4001RealGradientRe
  rw [LiebLiniger.FixedPeriod.Quantum.q4001_rieszRe_literal]
  exact InnerProductSpace.toDual_symm_apply

/-- Liouville measure of the restricted physical form on the ACTUAL range,
using the global chart and the intrinsic pulled-back form density. -/
def finiteGapRangePhysicalLiouville38 (Λ : Finset ℤ) :
    Measure (Set.range (actualBirkhoffTop38.finiteGapField38 Λ)) :=
  (muPullPhys Λ).map (actualFiniteGapChart38 Λ)

/-- The induced physical finite-gap Liouville measure as an ambient L²
measure: include the range carrying its chart-transported physical density. -/
def inducedFiniteGapPhysicalLiouville38 (Λ : Finset ℤ) : Measure PhysicalL2 :=
  (finiteGapRangePhysicalLiouville38 Λ).map Subtype.val

/-- The range measure pulls back under the genuine inverse chart to the
intrinsic coordinate density. -/
theorem finiteGapRangePhysicalLiouville38_pullback (Λ : Finset ℤ) :
    (finiteGapRangePhysicalLiouville38 Λ).map (actualFiniteGapChart38 Λ).symm =
      muPullPhys Λ := by
  unfold finiteGapRangePhysicalLiouville38
  rw [Measure.map_map (actualFiniteGapChart38 Λ).symm.continuous.measurable
    (actualFiniteGapChart38 Λ).continuous.measurable]
  simp only [Homeomorph.symm_comp_self, Measure.map_id]

/-- Ambient representation of the form-derived chart transport. -/
theorem inducedFiniteGapPhysicalLiouville38_eq_map (Λ : Finset ℤ) :
    inducedFiniteGapPhysicalLiouville38 Λ =
      (muPullPhys Λ).map (actualBirkhoffTop38.finiteGapField38 Λ) := by
  unfold inducedFiniteGapPhysicalLiouville38 finiteGapRangePhysicalLiouville38
  rw [Measure.map_map measurable_subtype_coe (actualFiniteGapChart38 Λ).continuous.measurable]
  rfl

/-- Concentration on the whole actual finite-gap range, with no removed
zero-coordinate stratum. -/
theorem inducedFiniteGapPhysicalLiouville38_concentrated (Λ : Finset ℤ) :
    inducedFiniteGapPhysicalLiouville38 Λ
      (Set.range (actualBirkhoffTop38.finiteGapField38 Λ))ᶜ = 0 := by
  rw [inducedFiniteGapPhysicalLiouville38_eq_map,
    Measure.map_apply (actual_finiteGapField_measurableEmbedding Λ).measurable
      (actual_finiteGapField_measurableSet_range Λ).compl]
  simp

/-- Pullback characterization on coordinate sets. The embedding permits
this equality even for nonmeasurable sets, interpreted by the outer measures. -/
theorem inducedFiniteGapPhysicalLiouville38_image (Λ : Finset ℤ)
    (s : Set (Λ → ℂ)) :
    inducedFiniteGapPhysicalLiouville38 Λ
      (actualBirkhoffTop38.finiteGapField38 Λ '' s) = muPullPhys Λ s := by
  rw [inducedFiniteGapPhysicalLiouville38_eq_map,
    (actual_finiteGapField_measurableEmbedding Λ).map_apply]
  rw [Set.preimage_image_eq _ (actual_finiteGapField_measurableEmbedding Λ).injective]

/-- The asserted physical finite-gap symplectic volume identification,
with its exact dimension-dependent normalization and the actual embedding. -/
theorem actual_finiteGap_physical_liouville_eq (Λ : Finset ℤ) :
    inducedFiniteGapPhysicalLiouville38 Λ = ENNReal.ofReal ((2 : ℝ) ^ Λ.card) •
      (NlsGge.Measure.finiteComplexVolume Λ).map
        (actualBirkhoffTop38.finiteGapField38 Λ) := by
  rw [inducedFiniteGapPhysicalLiouville38_eq_map, muPullPhys_eq,
    Measure.map_smul _ (actual_finiteGapField_measurableEmbedding Λ).measurable.aemeasurable]

end LiebLiniger.FixedPeriod.EXT
