import NlsGge.GK38.AbelianRealJacobianInjective
import NlsGge.GK38.AbelianJacobianDiagonalEquiv
import NlsGge.GK38.Lib.CompactOps

/-! Actual book14.7 inverse from the earned null-direction argument and the
earned diagonal-plus-compact decomposition, on the original isolating family. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem original_family_retained_input_injective (n : ℤ) (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im=0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) :
    ∀ i j : ℤ, i ≠ n → j ≠ n →
      Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n
        (p3RealPart38 n (p2Restrict38 n s)))) i=
      Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n
        (p3RealPart38 n (p2Restrict38 n s)))) j → i=j := by
  have hJ : p3RealInclude38 n (p3RealPart38 n (p2Restrict38 n s))=p2Restrict38 n s :=
    p3RealInclude_realPart38 n _ (fun m => hs m.1)
  have hother (k : ℤ) (hk : k ≠ n) :
      Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n
        (p3RealPart38 n (p2Restrict38 n s)))) k=Lib.sigmaOf s k := by
    rw [hJ]
    unfold Lib.sigmaOf
    rw [p2Extend_at38 n (p2Restrict38 n s) ⟨k,hk⟩,p2Restrict_apply38]
  intro i j hi hj he
  rw [hother i hi,hother j hj] at he
  by_contra hij
  obtain ⟨c,N,hg,_hsp⟩ := hfam
  have hd := (p2OwnSigma_denominator38 C R c N hg i j hij s (hσ i)
    (Lib.sigmaOf s j) (hσ j)).1
  exact hd (sub_eq_zero.mpr he)

theorem original_family_real_jacobian_inverse (n : ℤ) (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im=0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) :
    ∃ e : P3RealSpace38 n ≃L[ℝ] P3RealSpace38 n,
      e.toContinuousLinearMap =
        fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)) := by
  have hinj := real_jacobian_injective n u (p3RealPart38 n (p2Restrict38 n s))
    (original_family_retained_input_injective n u C R hfam s hs hσ)
  obtain ⟨c,N,hg,_hsp⟩ := hfam
  obtain ⟨D,K,hQ,_hHS,hK,_hdiag⟩ :=
    P3JacobianColumns.actual_real_diagonal_decomposition u C R c N hg ⟨c,N,hg,_hsp⟩ s hs hσ n
  have hinj' : Function.Injective (D.toContinuousLinearMap+K) := by
    rw [← hQ]
    exact hinj
  obtain ⟨e,he⟩ := Lib.bijective_of_one_add_compact D K hK hinj'
  refine ⟨e,?_⟩
  apply ContinuousLinearMap.ext
  intro h
  rw [hQ]
  exact congrFun he h

end
end NlsGge.GK38.P4NumeratorVariation
