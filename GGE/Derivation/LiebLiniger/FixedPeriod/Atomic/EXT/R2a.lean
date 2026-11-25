import NlsGge.Atomic.G6.G6028
import NlsGge.Atomic.G6.G6014
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.Birkhoff.S04FiniteGapInvariance38
import LiebLiniger.FixedPeriod.Conditional.BirkhoffContract

/-! # The actual finite-gap chart and its symplectic pullback

The finite plane is the entire complex coordinate plane indexed by an arbitrary
finite set of integer modes. Insertion is literal extension by zero into genuine
ℓ², and the field map uses the existing physical inverse Birkhoff map.
The chart is a real analytic closed embedding with the actual coordinate inverse.
Its normalized and physical symplectic pullbacks retain all finite coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Birkhoff NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.PDE
open scoped ComplexConjugate
open LiebLiniger.FixedPeriod.Conditional

/-- Literal extension by zero from the finite complex plane into genuine ℓ²,
viewed as a real continuous linear map. Finite support proves ℓ² membership. -/
def finiteSeqCLM38 (Λ : Finset ℤ) :
    (Λ → ℂ) →L[ℝ] LLFPBirkhoffCoordinates :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => seqToLp38 (extZero38 Λ w) (extZero38_mem_zero Λ w)
      map_add' := by
        intro w v
        apply lp.ext
        funext n
        change extZero38 Λ (w + v) n = extZero38 Λ w n + extZero38 Λ v n
        by_cases hn : n ∈ Λ
        · rw [extZero38_apply_of_mem _ hn, extZero38_apply_of_mem _ hn,
            extZero38_apply_of_mem _ hn]
          rfl
        · rw [extZero38_apply_of_not_mem _ hn, extZero38_apply_of_not_mem _ hn,
            extZero38_apply_of_not_mem _ hn, add_zero]
      map_smul' := by
        intro c w
        apply lp.ext
        funext n
        change extZero38 Λ (c • w) n = c • extZero38 Λ w n
        by_cases hn : n ∈ Λ
        · rw [extZero38_apply_of_mem _ hn, extZero38_apply_of_mem _ hn]
          rfl
        · rw [extZero38_apply_of_not_mem _ hn, extZero38_apply_of_not_mem _ hn,
            smul_zero] }

/-- The insertion has exactly the prescribed coordinate at every integer,
including zero outside the finite set. -/
theorem finiteSeqCLM38_coord (Λ : Finset ℤ) (w : Λ → ℂ) (n : ℤ) :
    (finiteSeqCLM38 Λ w) n = extZero38 Λ w n := rfl

/-- Insertion loses no finite coordinate, including when the finite set is empty. -/
theorem finiteSeqCLM38_injective (Λ : Finset ℤ) :
    Function.Injective (finiteSeqCLM38 Λ) := by
  intro w v h
  funext i
  have hi := congrArg (fun z : LLFPBirkhoffCoordinates => z i) h
  simpa only [finiteSeqCLM38_coord, extZero38_apply_of_mem _ i.property] using hi

/-- The actual finite-gap field is the same physical inverse evaluated on
literal finite-coordinate insertion; no raw off-domain inverse is differentiated. -/
theorem actual_finiteGapField_eq_inverse (Λ : Finset ℤ) (w : Λ → ℂ) :
    actualBirkhoffTop38.finiteGapField38 Λ w =
      physicalInverseBirkhoff (finiteSeqCLM38 Λ w) := by
  rw [BirkhoffTop38.finiteGapField38,
    actualBirkhoffTop38_cleanPhiInv _ (extZero38_mem_zero Λ w)]
  rfl

/-- The actual finite-gap field is real analytic at every finite-plane point,
including points with zero coordinates and the unique point of the empty plane. -/
theorem actual_finiteGapField_analytic (Λ : Finset ℤ) :
    AnalyticOnNhd ℝ (actualBirkhoffTop38.finiteGapField38 Λ) Set.univ := by
  have heq : actualBirkhoffTop38.finiteGapField38 Λ =
      fun w => physicalInverseBirkhoff (finiteSeqCLM38 Λ w) :=
    funext (actual_finiteGapField_eq_inverse Λ)
  rw [heq]
  intro w _
  exact (G6014.2.2.2.1 _ (Set.mem_univ _)).comp ((finiteSeqCLM38 Λ).analyticAt w)

/-- The forward physical map recovers the full inserted ℓ² element, not only
its coordinates on the finite set. -/
theorem physicalBirkhoff_actual_finiteGapField (Λ : Finset ℤ) (w : Λ → ℂ) :
    physicalBirkhoff (actualBirkhoffTop38.finiteGapField38 Λ w) = finiteSeqCLM38 Λ w := by
  rw [actual_finiteGapField_eq_inverse]
  exact G6013.2.2.2.2.2 _

/-- Restricting the actual physical Birkhoff map to the finite coordinates
is a left inverse for the entire finite-gap field map. -/
theorem actual_finiteGapField_leftInverse (Λ : Finset ℤ) :
    Function.LeftInverse (fun u : PhysicalL2 => fun i : Λ => physicalBirkhoff u i)
      (actualBirkhoffTop38.finiteGapField38 Λ) := by
  intro w
  funext i
  change physicalBirkhoff (actualBirkhoffTop38.finiteGapField38 Λ w) (i : ℤ) = w i
  rw [physicalBirkhoff_actual_finiteGapField, finiteSeqCLM38_coord,
    extZero38_apply_of_mem _ i.property]

private theorem continuous_finiteBirkhoffCoordinates38 (Λ : Finset ℤ) :
    Continuous (fun u : PhysicalL2 => fun i : Λ => physicalBirkhoff u i) :=
  continuous_pi fun i =>
    (lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 (i : ℤ)).continuous.comp G6014.2.2.1.continuous

/-- The actual finite-gap map is a closed topological embedding, with its
continuous left inverse given by finite restriction of physicalBirkhoff. -/
theorem actual_finiteGapField_isClosedEmbedding (Λ : Finset ℤ) :
    Topology.IsClosedEmbedding (actualBirkhoffTop38.finiteGapField38 Λ) :=
  (actual_finiteGapField_leftInverse Λ).isClosedEmbedding
    (continuous_finiteBirkhoffCoordinates38 Λ) (actual_finiteGapField_analytic Λ).continuous

/-- The actual finite-gap locus is a Borel subset of the physical Hilbert space. -/
theorem actual_finiteGapField_measurableSet_range (Λ : Finset ℤ) :
    MeasurableSet (Set.range (actualBirkhoffTop38.finiteGapField38 Λ)) :=
  (actual_finiteGapField_isClosedEmbedding Λ).isClosed_range.measurableSet

/-- The actual finite-gap chart is a measurable embedding into the physical
Hilbert space, so subsequent measure transport can use its genuine range. -/
theorem actual_finiteGapField_measurableEmbedding (Λ : Finset ℤ) :
    MeasurableEmbedding (actualBirkhoffTop38.finiteGapField38 Λ) :=
  (actual_finiteGapField_isClosedEmbedding Λ).measurableEmbedding

/-- Global chart of the actual finite-gap range. Its inverse is literally the
restriction of the same physicalBirkhoff map to the finite coordinates. -/
def actualFiniteGapChart38 (Λ : Finset ℤ) :
    (Λ → ℂ) ≃ₜ Set.range (actualBirkhoffTop38.finiteGapField38 Λ) where
  toFun w := ⟨actualBirkhoffTop38.finiteGapField38 Λ w, ⟨w, rfl⟩⟩
  invFun u := fun i => physicalBirkhoff u.val i
  left_inv := actual_finiteGapField_leftInverse Λ
  right_inv := by
    rintro ⟨u, w, rfl⟩
    apply Subtype.ext
    change actualBirkhoffTop38.finiteGapField38 Λ
      ((fun u : PhysicalL2 => fun i : Λ => physicalBirkhoff u i)
        (actualBirkhoffTop38.finiteGapField38 Λ w)) = _
    rw [actual_finiteGapField_leftInverse Λ w]
  continuous_toFun := (actual_finiteGapField_analytic Λ).continuous.subtype_mk _
  continuous_invFun := (continuous_finiteBirkhoffCoordinates38 Λ).comp continuous_subtype_val

/-- The global chart inverse is the actual coordinate restriction, on every
point of the range and every finite mode. -/
theorem actualFiniteGapChart38_symm_coord (Λ : Finset ℤ)
    (u : Set.range (actualBirkhoffTop38.finiteGapField38 Λ)) (i : Λ) :
    (actualFiniteGapChart38 Λ).symm u i = physicalBirkhoff u.val i := rfl

/-- The chain rule for the actual field map gives precisely finite insertion.
Both differentiated maps are real analytic on their genuine Hilbert carriers. -/
theorem actual_finiteGapField_derivative (Λ : Finset ℤ) (w : Λ → ℂ) :
    (fderiv ℝ physicalBirkhoff (actualBirkhoffTop38.finiteGapField38 Λ w)).comp
      (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w) = finiteSeqCLM38 Λ := by
  have hB := (G6014.2.2.1 (actualBirkhoffTop38.finiteGapField38 Λ w)
    (Set.mem_univ _)).differentiableAt
  have hF := (actual_finiteGapField_analytic Λ w (Set.mem_univ w)).differentiableAt
  have heq : physicalBirkhoff ∘ actualBirkhoffTop38.finiteGapField38 Λ = finiteSeqCLM38 Λ :=
    funext (physicalBirkhoff_actual_finiteGapField Λ)
  calc
    _ = fderiv ℝ (physicalBirkhoff ∘ actualBirkhoffTop38.finiteGapField38 Λ) w :=
      (fderiv_comp w hB hF).symm
    _ = finiteSeqCLM38 Λ := by rw [heq]; exact (finiteSeqCLM38 Λ).fderiv

/-- The derivative of the actual finite-gap embedding is injective at every
point, as follows from its exact derivative left inverse. -/
theorem actual_finiteGapField_derivative_injective (Λ : Finset ℤ) (w : Λ → ℂ) :
    Function.Injective (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w) := by
  intro h k heq
  apply finiteSeqCLM38_injective Λ
  have he := congrArg (fderiv ℝ physicalBirkhoff (actualBirkhoffTop38.finiteGapField38 Λ w)) heq
  simpa only [← ContinuousLinearMap.comp_apply, actual_finiteGapField_derivative] using he

/-- The normalized symplectic pairing of two inserted finite tangent vectors
is the ordinary sum of Im(conj(hᵢ) kᵢ), with no nonzero-coordinate premise. -/
theorem finiteSeqCLM38_normalized_symplectic (Λ : Finset ℤ) (h k : Λ → ℂ) :
    inner ℝ (Complex.I • finiteSeqCLM38 Λ h) (finiteSeqCLM38 Λ k) =
      ∑ i : Λ, (conj (h i) * k i).im := by
  rw [lp.inner_eq_tsum]
  have hz : ∀ n ∉ Λ,
      inner ℝ ((Complex.I • finiteSeqCLM38 Λ h) n) ((finiteSeqCLM38 Λ k) n) = 0 := by
    intro n hn
    change inner ℝ (Complex.I * extZero38 Λ h n) (extZero38 Λ k n) = 0
    rw [extZero38_apply_of_not_mem _ hn, mul_zero, inner_zero_left]
  rw [tsum_eq_sum hz, ← Finset.sum_coe_sort Λ]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (Complex.I * extZero38 Λ h (i : ℤ)) (extZero38 Λ k (i : ℤ)) = _
  rw [extZero38_apply_of_mem _ i.property, extZero38_apply_of_mem _ i.property,
    Complex.inner]
  simp only [map_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Normalized symplectic pullback for the actual finite-gap embedding:
omega₀(v₁,v₂) = inner ℝ (i • v₁) v₂ pulls back to sum dxᵢ ∧ dyᵢ. -/
theorem actual_finiteGap_symplectic_pullback (Λ : Finset ℤ) (w h k : Λ → ℂ) :
    inner ℝ (Complex.I • (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w h))
      (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w k) =
        ∑ i : Λ, (conj (h i) * k i).im := by
  have hs := G6028.2.2.1 (actualBirkhoffTop38.finiteGapField38 Λ w)
    (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w h)
    (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w k)
  have hd := actual_finiteGapField_derivative Λ w
  have hh := congrArg (fun A : (Λ → ℂ) →L[ℝ] LLFPBirkhoffCoordinates => A h) hd
  have hk := congrArg (fun A : (Λ → ℂ) →L[ℝ] LLFPBirkhoffCoordinates => A k) hd
  change fderiv ℝ physicalBirkhoff (actualBirkhoffTop38.finiteGapField38 Λ w)
    (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w h) = finiteSeqCLM38 Λ h at hh
  change fderiv ℝ physicalBirkhoff (actualBirkhoffTop38.finiteGapField38 Λ w)
    (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w k) = finiteSeqCLM38 Λ k at hk
  rw [hh, hk] at hs
  rw [← hs]
  exact finiteSeqCLM38_normalized_symplectic Λ h k

/-- Physical symplectic pullback for the actual finite-gap embedding, with
omegaPhys = 2 omega₀ and the factor two retained on both sides. -/
theorem actual_finiteGap_physical_symplectic_pullback (Λ : Finset ℤ) (w h k : Λ → ℂ) :
    2 * inner ℝ (Complex.I • (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w h))
      (fderiv ℝ (actualBirkhoffTop38.finiteGapField38 Λ) w k) =
        2 * ∑ i : Λ, (conj (h i) * k i).im := by
  rw [actual_finiteGap_symplectic_pullback]

end LiebLiniger.FixedPeriod.EXT
