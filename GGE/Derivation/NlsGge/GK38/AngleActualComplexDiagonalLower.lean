import NlsGge.GK38.AngleActualRealDiagonalLower
import NlsGge.GK38.AbelianPaddedJacobianColumns

/-! Actual real DIAGONAL lower bounds transfer to full complex Qstar and
actual full padded Jacobians at real original-disc inputs. The missing
coordinate has literal diagonal TWO and is included in the lower bound. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem anglePadded_missing_diagonal38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq) :
    p6PaddedJacobian38 n φ s (lp.single 2 n (1 : ℂ)) n=2 := by
  change p2Extend38 n
    ((fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s))
      (p2Restrict38 n (lp.single 2 n (1 : ℂ)))) n+
    (2 : ℂ)*(lp.single (E := fun _ : ℤ => ℂ) 2 n ((lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ)) n)) n=2
  rw [p2Extend_self38,lp.single_apply_self,lp.single_apply_self,zero_add,mul_one]

theorem angleActual_Qstar_complex_diagonal_lower38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k)) :
    ∃ d : ℝ, 0 < d ∧ ∀ m : ℤ,
      d ≤ ‖p6Qstar38 (realSlice u) (p6RealInclude38 s) (lp.single 2 m (1 : ℂ)) m‖ := by
  obtain ⟨d,hd,hbound⟩ := angleActual_full_real_diagonal_lower38 u C R hfam s hσ
  refine ⟨d,hd,?_⟩
  intro m
  have he := congrArg (fun q : Lib.L2Seq => q m)
    (p6RealQstar_include38 u s (lp.single 2 m (1 : ℝ)))
  rw [p6RealInclude_single38,p6RealInclude_apply38] at he
  rw [← he,Complex.norm_real]
  exact hbound m

theorem angleActual_padded_complex_diagonal_lower38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k))
    (n : ℤ) :
    ∃ d : ℝ, 0 < d ∧ ∀ m : ℤ,
      d ≤ ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)
        (lp.single 2 m (1 : ℂ)) m‖ := by
  obtain ⟨d,hd,hbound⟩ := angleActual_omitted_real_diagonal_lower38 u C R hfam
    (p6RealInclude38 s) (fun k => Complex.ofReal_im (s k)) hσ n
  refine ⟨min 2 d,lt_min (by norm_num) hd,?_⟩
  intro m
  by_cases hmn : m=n
  · subst m
    rw [anglePadded_missing_diagonal38]
    simpa only [Complex.norm_ofNat] using min_le_left (2 : ℝ) d
  · let k : P2Index38 n := ⟨m,hmn⟩
    have hr := P3JacobianColumns.actual_real_matrix_coordinate u (p6RealInclude38 s)
      (fun j => Complex.ofReal_im (s j)) n k k
    have hp := p6PaddedJacobian_matrix38 n (realSlice u) (realSlice_mem_gkW u)
      (p6RealInclude38 s) k k
    have he : ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)
        (lp.single 2 m (1 : ℂ)) m‖ =
        ‖(fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n
          (p2Restrict38 n (p6RealInclude38 s)))) (lp.single 2 k (1 : ℝ)) k‖ := by
      rw [hp,← hr,Complex.norm_real]
    rw [he]
    exact (min_le_right (2 : ℝ) d).trans (hbound k)

end
end NlsGge.GK38
