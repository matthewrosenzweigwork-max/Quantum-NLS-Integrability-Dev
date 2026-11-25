import Mathlib
import NlsGge.Atomic.LIB.LIB036
import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.ResonantParityPairBasisAction

                                                                                                                                
                                                                                                          
                                                                                            
                                                                                                             
                                                                                                                                
                                                                                                                     
                                                                             

set_option autoImplicit false
open NlsGge.Atomic.LIB036 NlsGge.Schur

namespace NlsGge.ClaudeH1.S002

lemma repr_resonant (n : ℤ) (y : ParityPair n) :
    parityPairRepr n (resonantParityPair n y) = resonantSquare n (parityPairRepr n y) := by
  unfold resonantParityPair
  simp

lemma expand_resonant (n : ℤ) (z : SectorSquare n) (hz : ∀ i : Bool × Sector n, i.2 ≠ resonantIndex n → z i = 0) :
    z = ∑ b : Bool, z (b, resonantIndex n) • lp.single 2 (b, resonantIndex n) (1 : ℂ) := by
  apply lp.ext
  funext j
  simp only [lp.coeFn_sum, lp.coeFn_smul, lp.coeFn_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  by_cases hj : j.2 = resonantIndex n
  · obtain ⟨b, k⟩ := j
    simp only at hj
    subst hj
    cases b <;> simp [Fintype.sum_bool]
  · have hne : ∀ b : Bool, j ≠ (b, resonantIndex n) := fun b h => hj (by rw [h])
    simp [hz j hj, hne, Fintype.sum_bool]

lemma resonant_range_eq (n : ℤ) :
    LinearMap.range ((resonantParityPair n : ParityPair n →L[ℂ] ParityPair n) :
      ParityPair n →ₗ[ℂ] ParityPair n) =
    Submodule.span ℂ (Set.range (fun b : Bool => parityPairVector n (b, resonantIndex n))) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun b => parityPairRepr n (resonantParityPair n y) (b, resonantIndex n), ?_⟩
    apply (parityPairRepr n).injective
    have hz : ∀ i : Bool × Sector n, i.2 ≠ resonantIndex n →
        parityPairRepr n (resonantParityPair n y) i = 0 := by
      intro i hi
      rw [repr_resonant, resonantSquare_apply, if_neg hi]
    rw [map_sum]
    simp only [map_smul, parityPairRepr_vector]
    exact (expand_resonant n _ hz).symm
  · intro hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
    refine ⟨∑ b, c b • parityPairVector n (b, resonantIndex n), ?_⟩
    simp [map_sum, map_smul, resonantParityPair_apply_basis]

lemma resonant_finrank (n : ℤ) :
    Module.finrank ℂ (LinearMap.range ((resonantParityPair n : ParityPair n →L[ℂ] ParityPair n) :
      ParityPair n →ₗ[ℂ] ParityPair n)) = 2 := by
  rw [resonant_range_eq]
  have hli : LinearIndependent ℂ (fun b : Bool => parityPairVector n (b, resonantIndex n)) :=
    (parityPairVector_orthonormal n).linearIndependent.comp _ (fun b c h => by
      simpa using congrArg Prod.fst h)
  rw [finrank_span_eq_card hli]
  simp

theorem S002_main : ((
  (∀ n : ℤ, Orthonormal ℂ (parityBasis n)) ∧
  (∀ (n : ℤ) (i : Bool × Sector n), parityBasis n i = sourcePairVector n (i.1, negateIndex n i.2)) ∧
  (∀ m : ℤ, ∀ x : ℝ,
    (-Complex.I) * deriv (fun y : ℝ => Complex.exp (Complex.I * (Real.pi * m) * y)) x =
      (Real.pi * m : ℂ) * Complex.exp (Complex.I * (Real.pi * m) * x) ∧
    Complex.I * deriv (fun y : ℝ => Complex.exp (-(Complex.I * (Real.pi * m)) * y)) x =
      (Real.pi * m : ℂ) * Complex.exp (-(Complex.I * (Real.pi * m)) * x)) ∧
  (∀ n : ℤ, IsIdempotentElem (resonantParityPair n) ∧
    Module.finrank ℂ (LinearMap.range ((resonantParityPair n : ParityPair n →L[ℂ] ParityPair n) :
      ParityPair n →ₗ[ℂ] ParityPair n)) = 2 ∧
    IsIdempotentElem (ContinuousLinearMap.id ℂ (ParityPair n) - resonantParityPair n))
  : Prop)) := by
  have key : ∀ (c : ℂ) (x : ℝ),
      HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (Complex.exp (c * (x : ℂ)) * c) x := by
    intro c x
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) (Complex.exp (c * (x : ℂ)) * c) (x : ℂ) := by
      have := ((hasDerivAt_id (x : ℂ)).const_mul c).cexp
      simpa [mul_comm] using this
    exact h1.comp_ofReal
  refine ⟨fun n => (parityBasis n).orthonormal, fun n i => parityBasis_eq n i, fun m x => ?_, fun n => ?_⟩
  · have hu := key (Complex.I * ((Real.pi : ℂ) * (m : ℂ))) x
    have hl := key (-(Complex.I * ((Real.pi : ℂ) * (m : ℂ)))) x
    refine ⟨?_, ?_⟩
    · rw [hu.deriv]
      linear_combination (-((Real.pi : ℂ) * (m : ℂ)) *
        Complex.exp (Complex.I * ((Real.pi : ℂ) * (m : ℂ)) * (x : ℂ))) * Complex.I_mul_I
    · rw [hl.deriv]
      linear_combination (-((Real.pi : ℂ) * (m : ℂ)) *
        Complex.exp (-(Complex.I * ((Real.pi : ℂ) * (m : ℂ))) * (x : ℂ))) * Complex.I_mul_I
  · have hP : IsIdempotentElem (resonantParityPair n) := by
      have hI : ∀ x : SectorSquare n, resonantSquare n (resonantSquare n x) = resonantSquare n x :=
        fun x => congrArg (fun T : SectorSquare n →L[ℂ] SectorSquare n => T x) (resonantSquare_idempotent n)
      unfold IsIdempotentElem resonantParityPair
      ext f : 1
      simp [ContinuousLinearMap.mul_apply, hI]
    refine ⟨hP, ?_, ?_⟩
    · exact resonant_finrank n
    · have hPx : ∀ x : ParityPair n, resonantParityPair n (resonantParityPair n x) = resonantParityPair n x :=
        fun x => congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T x) hP
      rw [← ContinuousLinearMap.one_def]
      unfold IsIdempotentElem
      ext x
      simp [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, hPx]

end NlsGge.ClaudeH1.S002
