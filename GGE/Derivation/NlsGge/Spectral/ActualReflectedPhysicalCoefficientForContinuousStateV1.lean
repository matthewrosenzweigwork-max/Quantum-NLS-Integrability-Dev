import NlsGge.Spectral.ActualSourceEigenvectorReflectedDerivativeClassesV1
import NlsGge.Spectral.ActualPhysicalL2ZsSubintervalACUniquenessV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Class-level reflection realizes the original (-u,-z) coefficient on
every state, without a pointwise identity of arbitrary Lp representatives. -/
theorem actualReflectedPhysicalCoefficient_ae_continuousState
    (u : PhysicalL2) (z : ℂ) (F : ℝ → Fin 2 → ℂ) (b : Bool) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 →
      (zsCoefficientComplex
        (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) (-z) t *ᵥ F t)
        (if b then 0 else 1) =
      actualContinuousReflectedDiracDerivativeRepresentative u z
        (fun s => F s 0) (fun s => F s 1) b t := by
  have hn := (ae_restrict_iff' measurableSet_Ioc).mp
    (naturalPhysicalCoverL2_neg_source_ae u)
  have hs := (ae_restrict_iff' measurableSet_Ioc).mp
    (actualPhysicalL2SourcePotential_star_ae u (star u) rfl)
  have hzero : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  filter_upwards [hn, hs, hzero] with t hnt hst ht0
  intro ht
  have htcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have hti : t ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne htcc.1 (Ne.symm ht0), htcc.2⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte,
      actualContinuousReflectedDiracDerivativeRepresentative,
      zsCoefficientComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    change (-Complex.I * star (naturalPhysicalCoverL2 (-u) (t : SpectralCircle))) * F t 0 +
      (Complex.I * (-z)) * F t 1 = _
    rw [hnt hti, hst hti]
    simp only [star_neg]
    ring
  · simp only [↓reduceIte,
      actualContinuousReflectedDiracDerivativeRepresentative,
      zsCoefficientComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    change (-Complex.I * (-z)) * F t 0 +
      (Complex.I * naturalPhysicalCoverL2 (-u) (t : SpectralCircle)) * F t 1 = _
    rw [hnt hti]
    ring

/-- Vector AC uniqueness is proved from the already checked matrix uniqueness
by inserting the state as one actual column and a zero second column. -/
theorem actualPhysicalL2Zs_vector_AC_same_initial_unique
    (u : PhysicalL2) (z : ℂ) (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 2)
    (F G : ℝ → Fin 2 → ℂ) (hinit : F 0 = G 0)
    (hF : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => F t i) 0 T)
    (hG : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => G t i) 0 T)
    (hFODE : ∀ i : Fin 2, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) T →
      HasDerivAt (fun s => F s i)
        ((zsCoefficientComplex
          (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t *ᵥ F t) i) t)
    (hGODE : ∀ i : Fin 2, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) T →
      HasDerivAt (fun s => G s i)
        ((zsCoefficientComplex
          (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t *ᵥ G t) i) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, F t = G t := by
  let FM : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t i j => if j = 0 then F t i else 0
  let GM : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t i j => if j = 0 then G t i else 0
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : ℂ)) 0 T := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    refine ⟨1, by norm_num, ?_⟩
    intro E hE hlen
    simpa using hε
  have hFM (i j : Fin 2) : AbsolutelyContinuousOnInterval (fun t => FM t i j) 0 T := by
    by_cases hj : j = 0
    · simpa only [FM, hj, ↓reduceIte] using hF i
    · simpa only [FM, hj, ↓reduceIte] using hconst
  have hGM (i j : Fin 2) : AbsolutelyContinuousOnInterval (fun t => GM t i j) 0 T := by
    by_cases hj : j = 0
    · simpa only [GM, hj, ↓reduceIte] using hG i
    · simpa only [GM, hj, ↓reduceIte] using hconst
  have hFMODE (i j : Fin 2) : ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) T →
      HasDerivAt (fun s => FM s i j)
        ((zsCoefficientComplex
          (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t * FM t) i j) t := by
    by_cases hj : j = 0
    · filter_upwards [hFODE i] with t hd
      intro ht
      simpa only [FM, hj, ↓reduceIte, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hd ht
    · filter_upwards [] with t
      intro ht
      simpa only [FM, hj, ↓reduceIte, Matrix.mul_apply, mul_zero, Finset.sum_const_zero] using
        (hasDerivAt_const t (0 : ℂ))
  have hGMODE (i j : Fin 2) : ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) T →
      HasDerivAt (fun s => GM s i j)
        ((zsCoefficientComplex
          (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t * GM t) i j) t := by
    by_cases hj : j = 0
    · filter_upwards [hGODE i] with t hd
      intro ht
      simpa only [GM, hj, ↓reduceIte, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hd ht
    · filter_upwards [] with t
      intro ht
      simpa only [GM, hj, ↓reduceIte, Matrix.mul_apply, mul_zero, Finset.sum_const_zero] using
        (hasDerivAt_const t (0 : ℂ))
  have hm := actualPhysicalL2Zs_subinterval_AC_same_initial_unique u z T hT FM GM
    (by simp only [FM, GM, hinit]) hFM hGM hFMODE hGMODE
  intro t ht
  funext i
  have hi := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i 0) (hm t ht)
  simpa only [FM, GM, ↓reduceIte] using hi

end NlsGge.SpectralFoundations
end
