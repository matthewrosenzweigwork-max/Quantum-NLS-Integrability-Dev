import NlsGge.GK38.AbelianFullRealDiagonalEquiv
import NlsGge.GK38.Lib.CompactOps

/-! Actual full real Qstar inverse from the earned full null-direction proof
and actual diagonal-plus-Hilbert-Schmidt decomposition. -/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38.P6FullJacobian
noncomputable section
open NlsGge.Analysis.RegularizedDeterminant

theorem actual_real_K_isHilbertSchmidt (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k)) :
    IsHilbertSchmidt (P6DiagonalOperator.actualOffDiagonal (p6RealQstar38 u s)) := by
  have hφ := realSlice_mem_gkW u
  obtain ⟨U,hU,_hUW,V,hV,H,hH,hr⟩ :=
    p2OmittedRatio_all_cut_bound38 (realSlice u) hφ (p6RealInclude38 s)
  have hratio := hr (realSlice u) (mem_of_mem_nhds hU)
    (p6RealInclude38 s) (mem_of_mem_nhds hV)
  obtain ⟨Ue,hUe,_hUeW,Ve,hVe,B,_hB,he⟩ :=
    p2RowEnvelope_common_l2_bound38 (realSlice u) hφ (p6RealInclude38 s)
  have hEs := (he (realSlice u) (mem_of_mem_nhds hUe)
    (p6RealInclude38 s) (mem_of_mem_nhds hVe)).1
  have hrow := actual_real_K_row_bound u C R c N hg hfam s hσ H hH hratio
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  exact (P6OperatorBridge.matrix_row_bound_isHS _
    (p2RowEnvelope38 (realSlice u) (p6RealInclude38 s)) (2*c*H)
    (by positivity) (p2RowEnvelope_nonneg38 (realSlice u) (p6RealInclude38 s)) hEs hrow).1

theorem actual_real_diagonal_decomposition (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k)) :
    ∃ (D : P6RealSpace38 ≃L[ℝ] P6RealSpace38)
      (K : P6RealSpace38 →L[ℝ] P6RealSpace38),
      p6RealQstar38 u s=D.toContinuousLinearMap+K ∧ IsHilbertSchmidt K ∧
        IsCompactOperator K ∧ (∀ m : ℤ, K (lp.single 2 m (1 : ℝ)) m=0) := by
  obtain ⟨D,hD⟩ := actual_real_diagonal_equiv u C R hfam s hσ
  have hHS := actual_real_K_isHilbertSchmidt u C R c N hg hfam s hσ
  refine ⟨D,P6DiagonalOperator.actualOffDiagonal (p6RealQstar38 u s),?_,hHS,
    P3OperatorBridge.hilbertSchmidt_isCompact _ hHS,?_⟩
  · rw [hD]
    exact P6DiagonalOperator.actual_decomposition (p6RealQstar38 u s)
  · exact P6DiagonalOperator.actualOffDiagonal_diagonal_zero (p6RealQstar38 u s)

theorem original_family_real_Qstar_inverse (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k)) :
    (p6RealQstar38 u s).IsInvertible := by
  have hinj := p6RealQstar_injective38 u C R hfam s hσ
  obtain ⟨c,N,hg,hsp⟩ := hfam
  obtain ⟨D,K,hQ,_hHS,hK,_hdiag⟩ :=
    actual_real_diagonal_decomposition u C R c N hg ⟨c,N,hg,hsp⟩ s hσ
  have hinj' : Function.Injective (D.toContinuousLinearMap+K) := by
    rw [← hQ]
    exact hinj
  obtain ⟨e,he⟩ := Lib.bijective_of_one_add_compact D K hK hinj'
  change ∃ e : P6RealSpace38 ≃L[ℝ] P6RealSpace38,
    e.toContinuousLinearMap=p6RealQstar38 u s
  refine ⟨e,?_⟩
  apply ContinuousLinearMap.ext
  intro h
  rw [hQ]
  exact congrFun he h

end
end NlsGge.GK38.P6FullJacobian
