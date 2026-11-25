import NlsGge.GK38.AbelianJacobianDiagonalNonzero
import NlsGge.GK38.AbelianJacobianPeriodError
import NlsGge.GK38.AbelianRealJacobianRows
import NlsGge.GK38.AbelianDiagonalLowerBound
import NlsGge.GK38.AbelianJacobianHilbertSchmidt

/-! Pointwise original-family actual real diagonal equivalence and actual D+K.
UNCOMPILED source preparation. Uniform neighborhood/HS bounds and source Omega
identification remain separate. No inverse of the full actual Q is asserted. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section
open NlsGge.Analysis.RegularizedDeterminant

theorem actual_real_diagonal_square_error (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) :
    ∃ a : ℤ → ℝ, (∀ m, 0 ≤ a m) ∧ Summable (fun m : ℤ => a m^2) ∧
      ∀ (n : ℤ) (m : P2Index38 n),
        ‖(fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))
          (lp.single 2 m (1 : ℝ)) m-2‖ ≤ a m.1 := by
  let φ : PotPair := realSlice u
  have hφ : φ ∈ gkW := realSlice_mem_gkW u
  obtain ⟨Ur,hUr,_hUrW,Vr,hVr,Br,H,_hBr,hH,hr⟩ :=
    p3OmittedRatio_all_cut_error38 φ hφ s
  obtain ⟨b,hb0,hbs,_hbB,hb⟩ := hr φ (mem_of_mem_nhds hUr) s (mem_of_mem_nhds hVr)
  obtain ⟨Ue,hUe,_hUeW,Ve,hVe,Be,_hBe,he⟩ := p2RowEnvelope_common_l2_bound38 φ hφ s
  have hEs := (he φ (mem_of_mem_nhds hUe) s (mem_of_mem_nhds hVe)).1
  have hFs := (p3InputRowEnvelope_bounds38 s).1
  let α : ℝ := 2*c*H
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hα : 0 ≤ α := mul_nonneg (mul_nonneg (by norm_num) hc) hH
  let a : ℤ → ℝ := fun m => α*p2RowEnvelope38 φ s m+α*p3InputRowEnvelope38 s m+2*b m
  have ha0 (m : ℤ) : 0 ≤ a m := by
    exact add_nonneg
      (add_nonneg (mul_nonneg hα (p2RowEnvelope_nonneg38 φ s m))
        (mul_nonneg hα (Real.sqrt_nonneg _))) (mul_nonneg (by norm_num) (hb0 m))
  have hdom : Summable (fun m : ℤ => 3*α^2*p2RowEnvelope38 φ s m^2+
      3*α^2*p3InputRowEnvelope38 s m^2+12*b m^2) :=
    ((hEs.mul_left (3*α^2)).add (hFs.mul_left (3*α^2))).add (hbs.mul_left 12)
  have hsq (m : ℤ) : a m^2 ≤ 3*α^2*p2RowEnvelope38 φ s m^2+
      3*α^2*p3InputRowEnvelope38 s m^2+12*b m^2 := by
    dsimp [a]
    nlinarith [sq_nonneg (α*p2RowEnvelope38 φ s m-α*p3InputRowEnvelope38 s m),
      sq_nonneg (α*p2RowEnvelope38 φ s m-2*b m),
      sq_nonneg (α*p3InputRowEnvelope38 s m-2*b m)]
  have has : Summable (fun m : ℤ => a m^2) :=
    hdom.of_nonneg_of_le (fun _ => sq_nonneg _) hsq
  refine ⟨a,ha0,has,?_⟩
  intro n m
  let q : ℝ := (fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))
    (lp.single 2 m (1 : ℝ)) m
  have hmatrix := actual_real_matrix_coordinate u s hs n m m
  have hcast : ((q-2 : ℝ) : ℂ) =
      (((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 φ (p3NumeratorColumn38 n m.1 s)-2 := by
    rw [Complex.ofReal_sub,Complex.ofReal_ofNat]
    exact congrArg (fun w : ℂ => w-2) hmatrix
  have hp := diagonal_period_sub_two_bound φ hφ C R c N hg hfam s n m.1 m.2.symm
    (hσ n) H (b m.1) hH (hb0 m.1)
    (fun z hz => (hb m.1 z hz).2) (fun z hz => (hb m.1 z hz).1)
  calc
    ‖q-2‖ = ‖((q-2 : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
    _ = ‖(((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 φ (p3NumeratorColumn38 n m.1 s)-2‖ :=
      congrArg norm hcast
    _ ≤ a m.1 := hp.trans_eq (by dsimp [a,α]; field_simp [Real.pi_ne_zero])

theorem actual_real_diagonal_equiv (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) (n : ℤ) :
    ∃ D : P3RealSpace38 n ≃L[ℝ] P3RealSpace38 n,
      D.toContinuousLinearMap = P3DiagonalOperator.actualDiagonal n
        (fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s))) := by
  let Q := fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s))
  let d : P2Index38 n → ℝ := fun m => Q (lp.single 2 m (1 : ℝ)) m
  obtain ⟨a,ha0,has,ha⟩ := actual_real_diagonal_square_error u C R c N hg hfam s hs hσ
  have hne (m : P2Index38 n) : d m ≠ 0 :=
    actual_real_diagonal_ne_zero u C R hfam s hs hσ n m
  have hsub : Summable (fun m : P2Index38 n => a m.1^2) :=
    has.comp_injective (i := fun m : P2Index38 n => m.1) Subtype.val_injective
  obtain ⟨δ,hδ,hlower⟩ := P3DiagonalOperator.exists_pos_lower_of_square_error n d
    (fun m => a m.1) hne (fun m => ha0 m.1) hsub (ha n)
  obtain ⟨D,hD,_hDinv⟩ := P3DiagonalOperator.exists_diagonal_equiv_of_bounds n d ‖Q‖ δ
    (norm_nonneg _) hδ (P3DiagonalOperator.actual_diagonal_coefficient_bound n Q) hlower
  refine ⟨D,?_⟩
  apply ContinuousLinearMap.ext
  intro t
  apply Subtype.ext
  funext m
  change D t m = d m*t m
  exact hD t m

theorem actual_real_diagonal_decomposition (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) (n : ℤ) :
    ∃ (D : P3RealSpace38 n ≃L[ℝ] P3RealSpace38 n)
      (K : P3RealSpace38 n →L[ℝ] P3RealSpace38 n),
      (fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s))) =
        D.toContinuousLinearMap+K ∧ IsHilbertSchmidt K ∧ IsCompactOperator K ∧
        (∀ m : P2Index38 n, K (lp.single 2 m (1 : ℝ)) m = 0) := by
  let Q := fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s))
  obtain ⟨D,hD⟩ := actual_real_diagonal_equiv u C R c N hg hfam s hs hσ n
  refine ⟨D,P3DiagonalOperator.actualOffDiagonal n Q,?_,
    P3OperatorBridge.actual_real_K_isHilbertSchmidt u C R c N hg hfam s hs hσ n,
    P3OperatorBridge.actual_real_K_isCompact u C R c N hg hfam s hs hσ n,?_⟩
  · rw [hD]
    exact P3DiagonalOperator.actual_decomposition n Q
  · exact P3DiagonalOperator.actualOffDiagonal_diagonal_zero n Q

end
end NlsGge.GK38.P3JacobianColumns
