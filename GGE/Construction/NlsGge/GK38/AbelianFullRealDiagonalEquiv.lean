import NlsGge.GK38.AbelianFullRealJacobian
import NlsGge.GK38.AbelianFullDiagonalMean
import NlsGge.GK38.AbelianFullDiagonalOperator
import NlsGge.GK38.AbelianFullHilbertSchmidt
import NlsGge.GK38.AbelianRatioRowError

/-! The actual full real Qstar has an invertible diagonal and a genuine
Hilbert-Schmidt off-diagonal remainder. All premises are actual product bounds. -/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38.P6FullJacobian
noncomputable section
open NlsGge.Analysis.RegularizedDeterminant

theorem actual_real_diagonal_ne_zero (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k)) (m : ℤ) :
    p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m ≠ 0 := by
  have he := p6RealQstar_matrix_coordinate38 u s m m
  change ((p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m : ℝ) : ℂ)=
    abelianPeriod38 m (realSlice u) (fullColumn m (p6RealInclude38 s)) at he
  intro hz
  rw [hz,Complex.ofReal_zero] at he
  exact fullColumn_diagonal_period_ne_zero u C R hfam (p6RealInclude38 s)
    (fun k => Complex.ofReal_im (s k)) hσ m he.symm

theorem actual_real_diagonal_square_error (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : P6RealSpace38) :
    ∃ a : ℤ → ℝ, (∀ m, 0 ≤ a m) ∧ Summable (fun m : ℤ => a m^2) ∧
      ∀ m : ℤ, ‖p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m-2‖ ≤ a m := by
  obtain ⟨U,hU,_hUW,V,hV,B,H,_hB,_hH,hb⟩ :=
    p3OmittedRatio_all_cut_error38 (realSlice u) (realSlice_mem_gkW u) (p6RealInclude38 s)
  obtain ⟨b,hb0,hbs,_hbB,hr⟩ :=
    hb (realSlice u) (mem_of_mem_nhds hU) (p6RealInclude38 s) (mem_of_mem_nhds hV)
  refine ⟨fun m => 2*b m,fun m => mul_nonneg (by norm_num) (hb0 m),?_,?_⟩
  · simpa only [mul_pow] using hbs.mul_left ((2 : ℝ)^2)
  · intro m
    have he := p6RealQstar_matrix_coordinate38 u s m m
    change ((p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m : ℝ) : ℂ)=
      abelianPeriod38 m (realSlice u) (fullColumn m (p6RealInclude38 s)) at he
    calc
      _ = ‖((p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m-2 : ℝ) : ℂ)‖ :=
        (Complex.norm_real _).symm
      _ = ‖abelianPeriod38 m (realSlice u) (fullColumn m (p6RealInclude38 s))-2‖ := by
        rw [Complex.ofReal_sub,Complex.ofReal_ofNat,he]
      _ ≤ 2*b m := fullColumn_diagonal_period_sub_two_bound u C R hfam (p6RealInclude38 s)
        (fun k => Complex.ofReal_im (s k)) m (b m) (fun z hz => (hr m z hz).1)

theorem actual_real_diagonal_equiv (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k)) :
    ∃ D : P6RealSpace38 ≃L[ℝ] P6RealSpace38,
      D.toContinuousLinearMap=P6DiagonalOperator.actualDiagonal (p6RealQstar38 u s) := by
  let Q := p6RealQstar38 u s
  let d : ℤ → ℝ := fun m => Q (lp.single 2 m (1 : ℝ)) m
  obtain ⟨a,ha0,has,ha⟩ := actual_real_diagonal_square_error u C R hfam s
  have hne : ∀ m : ℤ, d m ≠ 0 := actual_real_diagonal_ne_zero u C R hfam s hσ
  obtain ⟨δ,hδ,hlower⟩ := P6DiagonalOperator.exists_pos_lower_of_square_error d a hne ha0 has ha
  obtain ⟨D,hD,_hDinv⟩ := P6DiagonalOperator.exists_diagonal_equiv_of_bounds d ‖Q‖ δ
    (norm_nonneg _) hδ (P6DiagonalOperator.actual_diagonal_coefficient_bound Q) hlower
  refine ⟨D,?_⟩
  apply ContinuousLinearMap.ext
  intro h
  apply Subtype.ext
  funext m
  change D h m=d m*h m
  exact hD h m

theorem actual_real_K_row_bound (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k))
    (H : ℝ) (hH : 0 ≤ H)
    (hratio : ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
      ‖p2OmittedRatio38 m (((realSlice u),p6RealInclude38 s),z)‖ ≤ H) :
    ∀ m r : ℤ,
      ‖P6DiagonalOperator.actualOffDiagonal (p6RealQstar38 u s) (lp.single 2 r (1 : ℝ)) m‖ ≤
        (2*c*H)*p2RowEnvelope38 (realSlice u) (p6RealInclude38 s) m*Lib.c3w m r := by
  intro m r
  by_cases hmr : m=r
  · subst r
    rw [P6DiagonalOperator.actualOffDiagonal_diagonal_zero,norm_zero]
    have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) hH)
        (p2RowEnvelope_nonneg38 (realSlice u) (p6RealInclude38 s) m)) (Lib.c3w_nonneg m m)
  · have hk : P6DiagonalOperator.actualOffDiagonal (p6RealQstar38 u s)
        (lp.single 2 r (1 : ℝ)) m=p6RealQstar38 u s (lp.single 2 r (1 : ℝ)) m := by
      change _-P6DiagonalOperator.actualDiagonal (p6RealQstar38 u s)
        (lp.single 2 r (1 : ℝ)) m = _
      rw [P6DiagonalOperator.actualDiagonal_apply,
        lp.single_apply_ne (E := fun _ : ℤ => ℝ) 2 r (1 : ℝ) hmr,mul_zero,sub_zero]
      rfl
    rw [hk]
    have he := p6RealQstar_matrix_coordinate38 u s m r
    change ((p6RealQstar38 u s (lp.single 2 r (1 : ℝ)) m : ℝ) : ℂ)=
      abelianPeriod38 m (realSlice u) (fullColumn r (p6RealInclude38 s)) at he
    calc
      _ = ‖((p6RealQstar38 u s (lp.single 2 r (1 : ℝ)) m : ℝ) : ℂ)‖ :=
        (Complex.norm_real _).symm
      _ = ‖abelianPeriod38 m (realSlice u) (fullColumn r (p6RealInclude38 s))‖ := congrArg norm he
      _ ≤ _ := fullColumn_offDiagonal_period_bound (realSlice u) (realSlice_mem_gkW u)
        C R c N hg hfam (p6RealInclude38 s) m r (Ne.symm hmr) (hσ r) H hH (hratio m)

end
end NlsGge.GK38.P6FullJacobian
