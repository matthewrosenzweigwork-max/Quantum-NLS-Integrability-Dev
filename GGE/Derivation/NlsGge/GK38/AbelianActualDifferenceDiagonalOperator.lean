import NlsGge.GK38.AbelianActualDifferenceOperatorBlock
import NlsGge.GK38.AbelianShiftedSquareMass

/-! UNCOMPILED actual nonmissing diagonal OPERATOR norm. Genuine shifted
square-mass membership precedes the square root/term estimates. This estimate
is suited to the fixed actual gap cube, not a uniform tail on an open ball. -/
set_option autoImplicit false
open Set Filter Topology Metric
open scoped Classical
namespace NlsGge.GK38
noncomputable section

theorem p6ComplexDiagonal_norm_le38 {ι : Type*}
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ m : ι, ‖T (lp.single 2 m (1 : ℂ)) m‖ ≤ B) :
    ‖p6ComplexDiagonal38 T‖ ≤ B := by
  let D : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
    lp.mapCLM 2 (fun m : ι => T (lp.single 2 m (1 : ℂ)) m •
      ContinuousLinearMap.id ℂ ℂ) hB (fun m => by
        simpa only [norm_smul,ContinuousLinearMap.norm_id,mul_one] using hb m)
  have he : p6ComplexDiagonal38 T=D := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    funext m
    rfl
  rw [he]
  exact lp.norm_mapCLM_le 2 _ hB _

theorem p6ShiftedSquareMass_term_sqrt38 (d : ℤ → ℝ) (hd0 : ∀ m, 0 ≤ d m)
    (hd : Summable (fun m : ℤ => d m^2)) (n m : ℤ) :
    d m*Lib.c3w m n ≤ Real.sqrt (∑' k : ℤ, d k^2*Lib.c3w k n^2) := by
  have hs := p6ShiftedSquareMass_summable38 d hd n
  have ht : d m^2*Lib.c3w m n^2 ≤ ∑' k : ℤ, d k^2*Lib.c3w k n^2 :=
    hs.le_tsum m (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have he : Real.sqrt (d m^2*Lib.c3w m n^2)=d m*Lib.c3w m n := by
    rw [← mul_pow,Real.sqrt_sq (mul_nonneg (hd0 m) (Lib.c3w_nonneg m n))]
  exact he ▸ Real.sqrt_le_sqrt ht

theorem p6ActualDifference_diagonal_operator_norm38
    (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) (n : ℤ) :
    ‖p6ComplexDiagonal38 (p6NonmissingDifference38 n φ s)‖ ≤
      (2*c*H)*(‖s n‖+Real.sqrt
        (∑' m : ℤ, p2RowEnvelope38 φ 0 m^2*Lib.c3w m n^2)) := by
  let d : ℤ → ℝ := p2RowEnvelope38 φ 0
  have hd : Summable (fun m : ℤ => d m^2) := p6CutCenter_envelope_summable38 φ hφ
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hA : 0 ≤ 2*c*H := by positivity
  apply p6ComplexDiagonal_norm_le38 _ _ (mul_nonneg hA
    (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
  intro m
  have hmatrix := p6NonmissingDifference_matrix38 n φ s m m
  have hb := p6ActualDifference_diagonal_bound38 φ hφ C R c N hg hfam s hσ
    H hH hRatio n m.val m.property
  have hterm := p6ShiftedSquareMass_term_sqrt38 d
    (p2RowEnvelope_nonneg38 φ 0) hd n m.val
  calc
    _ = ‖(p6PaddedJacobian38 n φ s-p6Qstar38 φ s)
        (lp.single (E := fun _ : ℤ => ℂ) 2 m.val (1 : ℂ)) m.val‖ := by
      simpa only [p6ComplexSingle_classical38] using!
        congrArg (fun z : ℂ => ‖z‖) hmatrix
    _ ≤ (2*c*H)*(‖s n‖+d m.val)*Lib.c3w m.val n := hb
    _ = (2*c*H)*(‖s n‖*Lib.c3w m.val n+d m.val*Lib.c3w m.val n) := by ring
    _ ≤ (2*c*H)*(‖s n‖+Real.sqrt (∑' k : ℤ, d k^2*Lib.c3w k n^2)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact add_le_add
        ((mul_le_mul_of_nonneg_left (Lib.c3w_le_one m.val n) (norm_nonneg _)).trans_eq
          (mul_one _)) hterm

end
end NlsGge.GK38
