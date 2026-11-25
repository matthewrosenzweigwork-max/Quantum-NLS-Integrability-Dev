import Mathlib
import NlsGge.Ramer.LinearDecomposition

                                                                                                                                                   
                                                                                                                                 
                                                                                                                                              
                                                                                                                                                    
                                                                                                                                               
                                                                                                
set_option autoImplicit false
open Filter
open scoped Topology

namespace NlsGge.ThirdConsultation.R
noncomputable section

def FiniteRankCorrection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : E → E) : Prop :=
  ∃ V : Submodule ℝ E, FiniteDimensional ℝ V ∧ ∀ x : E, K x ∈ V

def LinearSmallTailFactor
    {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (i : H →L[ℝ] E) (P : ℕ → H →L[ℝ] H)
    (A : E →L[ℝ] H) (q : ℝ) (N : ℕ) (S : E ≃L[ℝ] E) : Prop :=
  ‖((ContinuousLinearMap.id ℝ H - P N).comp A).comp i‖ < q ∧
    ∀ x : E,
      S x = x + i ((ContinuousLinearMap.id ℝ H - P N) (A x))


theorem linear_decomposition
    {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {ι : Type*} (i : H →L[ℝ] E) (b : HilbertBasis ι ℝ H)
    (hi : Summable (fun p : ι => ‖i (b p)‖ ^ 2))
    (P : ℕ → H →L[ℝ] H)
    (hP : ∀ (N : ℕ) (h : H), ‖P N h‖ ≤ ‖h‖)
    (hPfinite : ∀ N : ℕ,
      FiniteDimensional ℝ (LinearMap.range (P N).toLinearMap))
    (hPlim : ∀ h : H, Tendsto (fun N : ℕ => P N h) atTop (𝓝 h))
    (A : E →L[ℝ] H)
    (hA : IsUnit (ContinuousLinearMap.id ℝ E + i.comp A)) :
    ∃ (q : ℝ) (N : ℕ) (S Pi : E ≃L[ℝ] E),
      0 < q ∧ q < (1 : ℝ) / 3 ∧
      LinearSmallTailFactor i P A q N S ∧
      Pi.toContinuousLinearMap =
        (ContinuousLinearMap.id ℝ E + i.comp A).comp
          S.symm.toContinuousLinearMap ∧
      (∀ x : E,
        Pi x - x = i (P N (A (S.symm x)))) ∧
      FiniteRankCorrection (fun x : E => Pi x - x) ∧
      ContinuousLinearMap.id ℝ E + i.comp A =
        Pi.toContinuousLinearMap.comp S.toContinuousLinearMap := by
  classical
  obtain ⟨u, hu⟩ := hA
  let T : E ≃L[ℝ] E := ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.id ℝ E + i.comp A)
    (↑u⁻¹ : E →L[ℝ] E)
    (fun x => by
      have h := congrArg (fun L : E →L[ℝ] E => L x) (Units.inv_mul u)
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
      rw [hu] at h
      exact h)
    (fun x => by
      have h := congrArg (fun L : E →L[ℝ] E => L x) (Units.mul_inv u)
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
      rw [hu] at h
      exact h)
  have hT : ∀ x, T x = x + i (A x) := fun x => rfl
  obtain ⟨N, S, Pi, M, hlt, -, hS, -, -, -, -, hPi, hPix⟩ :=
    NlsGge.Ramer.linear_decomposition i b hi A T hT P (fun n x => hP n x) hPlim
      (fun n => ContinuousLinearMap.id ℝ H - P n) (fun n x => rfl)
  have hPieq : Pi = S.symm.trans T := by
    ext x; exact hPi x
  refine ⟨1 / 8, N, S, Pi, by norm_num, by norm_num, ⟨hlt, hS⟩, ?_, hPix, ?_, ?_⟩
  · ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply]
    exact (hPi x).trans (hT _)
  · refine ⟨Submodule.map i.toLinearMap (LinearMap.range (P N).toLinearMap), ?_, fun x => ?_⟩
    · haveI := hPfinite N
      exact inferInstance
    · refine ⟨P N (A (S.symm x)), ⟨_, rfl⟩, ?_⟩
      simp [hPix x]
  · ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply]
    have h := hPi (S x)
    rw [ContinuousLinearEquiv.symm_apply_apply] at h
    exact (hT x).symm.trans h.symm

end
end NlsGge.ThirdConsultation.R
