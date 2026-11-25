import NlsGge.GK38.AbelianMissingCoordinateBlocks
import NlsGge.GK38.AbelianFullGapCompactDomain
import NlsGge.GK38.AbelianShiftedSquareMass

/-! UNCOMPILED missing row/column estimates for the ACTUAL padded difference.
The row coefficient series and shifted column square mass are genuinely
summable before the operator norm estimates are taken. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedJacobian_missing_row38 (n : ℤ) (φ : PotPair) (s x : Lib.L2Seq) :
    p6PaddedJacobian38 n φ s x n=(2 : ℂ)*x n := by
  change p2Extend38 n
    ((fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s))
      (p2Restrict38 n x)) n+
      (2 : ℂ)*(lp.single (E := fun _ : ℤ => ℂ) 2 n (x n)) n=_
  rw [p2Extend_self38,lp.single_apply_self,zero_add]

theorem p6PaddedJacobian_missing_column38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq) :
    p6PaddedJacobian38 n φ s (lp.single 2 n (1 : ℂ))=(2 : ℂ) • lp.single 2 n (1 : ℂ) := by
  have hR : p2Restrict38 n (lp.single 2 n (1 : ℂ))=0 := by
    apply Subtype.ext
    funext m
    rw [p2Restrict_apply38,lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) m.property]
    rfl
  unfold p6PaddedJacobian38
  rw [add_apply]
  change p2Extend38 n
    ((fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s))
      (p2Restrict38 n (lp.single 2 n (1 : ℂ))))+
    (2 : ℂ) • lp.single 2 n ((lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ)) n)=_
  rw [hR,map_zero,map_zero,zero_add,lp.single_apply_self]

theorem p6Qstar_offDiagonal_coefficient_bound38
    (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq) (m r : ℤ) (hrm : r ≠ m)
    (hσr : Lib.sigmaOf s r ∈ closedBall (C r) (R r))
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) :
    ‖p6Qstar38 φ s (lp.single 2 r (1 : ℂ)) m‖ ≤
      (2*c*H)*p2RowEnvelope38 φ s m*Lib.c3w m r := by
  rw [p6Qstar_unit_column38 φ hφ]
  exact P6FullJacobian.fullColumn_offDiagonal_period_bound φ hφ C R c N hg hfam s m r
    hrm hσr H hH hRatio

theorem p6MissingColumnVector_coordinate38 (n : ℤ)
    (T : Lib.L2Seq →L[ℂ] Lib.L2Seq) (m : ℤ) :
    p6MissingColumnVector38 n T m=if m=n then 0 else T (lp.single 2 n (1 : ℂ)) m := by
  classical
  by_cases hmn : m=n
  · subst m
    rw [p6MissingColumnVector38,p2Extend_self38,ite_eq_left rfl]
  · let k : P2Index38 n := ⟨m,hmn⟩
    change p2Extend38 n (p2Restrict38 n (T (lp.single 2 n (1 : ℂ)))) k.val=_
    rw [p2Extend_at38,p2Restrict_apply38,ite_eq_right hmn]

theorem p6Complex_row_c3w_norm_bound38 (n : ℤ)
    (A : P2Space38 n →L[ℂ] Lib.L2Seq) (b : ℝ)
    (hpoint : ∀ r : P2Index38 n,
      ‖A (lp.single (E := fun _ : P2Index38 n => ℂ) 2 r (1 : ℂ))‖ ≤
        b*Lib.c3w n r.val) :
    ‖A‖ ≤ Real.sqrt (b^2*Lib.invSqSum) := by
  have hw := Lib.summable_c3w_sq n
  have hsub : Summable (fun r : P2Index38 n => Lib.c3w n r.val^2) :=
    hw.comp_injective (i := fun r : P2Index38 n => r.val) Subtype.val_injective
  have hmass : (∑' r : P2Index38 n, Lib.c3w n r.val^2) ≤ Lib.invSqSum :=
    (Summable.tsum_subtype_le (fun r : ℤ => Lib.c3w n r^2) {r : ℤ | r ≠ n}
      (fun _ => sq_nonneg _) hw).trans_eq (Lib.tsum_c3w_sq n)
  have hsq (r : P2Index38 n) :
      ‖A (lp.single (E := fun _ : P2Index38 n => ℂ) 2 r (1 : ℂ))‖^2 ≤
        b^2*Lib.c3w n r.val^2 := by
    have hh := mul_self_le_mul_self (norm_nonneg _) (hpoint r)
    nlinarith [hh]
  have hdom := hsub.mul_left (b^2)
  have hsum := hdom.of_nonneg_of_le (fun _ => sq_nonneg _) hsq
  have hb := hsum.tsum_le_tsum hsq hdom
  rw [tsum_mul_left] at hb
  have htotal := hb.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg b))
  have hnorm := p6ComplexLp_opNorm_le_column_mass38 A
    (by simpa only [p6ComplexSingle_classical38] using! hsum)
  have hnorm' : ‖A‖ ≤ Real.sqrt
      (∑' r : P2Index38 n,
        ‖A (lp.single (E := fun _ : P2Index38 n => ℂ) 2 r (1 : ℂ))‖^2) := by
    simpa only [p6ComplexSingle_classical38] using! hnorm
  exact hnorm'.trans (Real.sqrt_le_sqrt htotal)

theorem p6GapCube_missing_row_unit_bound38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ s ∈ p6ComplexFullGapCube38 u, ∀ m : ℤ,
      ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
        ‖p2OmittedRatio38 m ((realSlice u,s),z)‖ ≤ H)
    (n : ℤ) (s : Lib.L2Seq) (hs : s ∈ p6ComplexFullGapCube38 u) (r : P2Index38 n) :
    ‖p6MissingRowBlock38 n
      (p6PaddedJacobian38 n (realSlice u) s-p6Qstar38 (realSlice u) s)
      (lp.single (E := fun _ : P2Index38 n => ℂ) 2 r (1 : ℂ))‖ ≤
        (2*c*H)*p6FixedGapRowEnvelope38 u n*Lib.c3w n r.val := by
  have hgap := p6ComplexFullGapCube_actual_gaps38 u s hs
  have hσ := p6ComplexFullGapCube_original_placement38 u C R hfam s hs
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hconst : 0 ≤ 2*c*H := by positivity
  rw [p6MissingRowBlock_unit38,lp.norm_single (by norm_num : 0 < (2 : ENNReal))]
  change ‖p6PaddedJacobian38 n (realSlice u) s (lp.single 2 r.val (1 : ℂ)) n-
    p6Qstar38 (realSlice u) s (lp.single 2 r.val (1 : ℂ)) n‖ ≤ _
  rw [p6PaddedJacobian_missing_row38,
    lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 r.val (1 : ℂ) (Ne.symm r.property),
    mul_zero,zero_sub,norm_neg]
  exact (p6Qstar_offDiagonal_coefficient_bound38 (realSlice u) (realSlice_mem_gkW u)
    C R c N hg hfam s n r.val r.property (hσ r.val) H hH (hRatio s hs n)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (p6FullGap_row_envelope38 u s hgap n) hconst)
      (Lib.c3w_nonneg n r.val))

theorem p6GapCube_missing_row_norm38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ s ∈ p6ComplexFullGapCube38 u, ∀ m : ℤ,
      ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
        ‖p2OmittedRatio38 m ((realSlice u,s),z)‖ ≤ H)
    (n : ℤ) (s : Lib.L2Seq) (hs : s ∈ p6ComplexFullGapCube38 u) :
    ‖p6MissingRowBlock38 n (p6PaddedJacobian38 n (realSlice u) s-p6Qstar38 (realSlice u) s)‖ ≤
      Real.sqrt ((2*c*H)^2*p6FixedGapRowEnvelope38 u n^2*Lib.invSqSum) := by
  let b : ℝ := (2*c*H)*p6FixedGapRowEnvelope38 u n
  have hb := p6Complex_row_c3w_norm_bound38 n
    (p6MissingRowBlock38 n (p6PaddedJacobian38 n (realSlice u) s-p6Qstar38 (realSlice u) s))
    b (fun r => p6GapCube_missing_row_unit_bound38 u C R c N hg hfam H hH hRatio n s hs r)
  simpa only [b,mul_pow] using hb

theorem p6GapCube_missing_column_norm38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ s ∈ p6ComplexFullGapCube38 u, ∀ m : ℤ,
      ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
        ‖p2OmittedRatio38 m ((realSlice u,s),z)‖ ≤ H)
    (n : ℤ) (s : Lib.L2Seq) (hs : s ∈ p6ComplexFullGapCube38 u) :
    ‖p6MissingColumnVector38 n
      (p6PaddedJacobian38 n (realSlice u) s-p6Qstar38 (realSlice u) s)‖ ≤
      Real.sqrt ((2*c*H)^2*(∑' m : ℤ, p6FixedGapRowEnvelope38 u m^2*Lib.c3w m n^2)) := by
  let T := p6PaddedJacobian38 n (realSlice u) s-p6Qstar38 (realSlice u) s
  let v := p6MissingColumnVector38 n T
  have hgap := p6ComplexFullGapCube_actual_gaps38 u s hs
  have hσ := p6ComplexFullGapCube_original_placement38 u C R hfam s hs
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hconst : 0 ≤ 2*c*H := by positivity
  have hpoint (m : ℤ) : ‖v m‖ ≤ (2*c*H)*p6FixedGapRowEnvelope38 u m*Lib.c3w m n := by
    rw [p6MissingColumnVector_coordinate38]
    by_cases hmn : m=n
    · rw [ite_eq_left hmn,norm_zero]
      exact mul_nonneg (mul_nonneg hconst (p6FixedGapRowEnvelope_nonneg38 u m))
        (Lib.c3w_nonneg m n)
    · rw [ite_eq_right hmn]
      change ‖p6PaddedJacobian38 n (realSlice u) s (lp.single 2 n (1 : ℂ)) m-
        p6Qstar38 (realSlice u) s (lp.single 2 n (1 : ℂ)) m‖ ≤ _
      rw [p6PaddedJacobian_missing_column38,lp.coeFn_smul,Pi.smul_apply,
        lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) hmn,
        smul_zero,zero_sub,norm_neg]
      exact (p6Qstar_offDiagonal_coefficient_bound38 (realSlice u) (realSlice_mem_gkW u)
        C R c N hg hfam s m n (Ne.symm hmn) (hσ n) H hH (hRatio s hs m)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (p6FullGap_row_envelope38 u s hgap m) hconst)
          (Lib.c3w_nonneg m n))
  have hmass := Lib.hasSum_sq_l2 v
  have hdom := (p6ShiftedSquareMass_summable38 (p6FixedGapRowEnvelope38 u)
    (p6FixedGapRowEnvelope_summable38 u) n).mul_left ((2*c*H)^2)
  have hsq (m : ℤ) : ‖v m‖^2 ≤
      (2*c*H)^2*(p6FixedGapRowEnvelope38 u m^2*Lib.c3w m n^2) := by
    have hh := mul_self_le_mul_self (norm_nonneg _) (hpoint m)
    nlinarith [hh]
  have hb := hmass.summable.tsum_le_tsum hsq hdom
  rw [hmass.tsum_eq,tsum_mul_left] at hb
  calc
    _ = Real.sqrt (‖v‖^2) := (Real.sqrt_sq (norm_nonneg v)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hb

end
end NlsGge.GK38
