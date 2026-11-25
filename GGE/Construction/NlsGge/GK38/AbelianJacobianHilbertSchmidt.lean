import NlsGge.GK38.AbelianRealJacobianRows
import NlsGge.GK38.AbelianHilbertSchmidtCompact

/-! Genuine HS membership of the ACTUAL real off-diagonal Jacobian part.
UNCOMPILED source preparation. Finite-column energy is bounded BEFORE column
summability, real tsums and actual HS membership are used. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P3OperatorBridge
noncomputable section
open NlsGge.Analysis.RegularizedDeterminant

theorem matrix_row_bound_isHS (n : ℤ)
    (T : P3RealSpace38 n →L[ℝ] P3RealSpace38 n) (e : ℤ → ℝ) (A : ℝ)
    (_hA : 0 ≤ A) (_he0 : ∀ m, 0 ≤ e m) (hes : Summable (fun m : ℤ => e m^2))
    (hbound : ∀ m r : P2Index38 n,
      ‖T (lp.single 2 r (1 : ℝ)) m‖ ≤ A*e m.1*Lib.c3w m.1 r.1) :
    IsHilbertSchmidt T ∧
    Summable (fun r : P2Index38 n => ‖T (lp.single 2 r (1 : ℝ))‖^2) ∧
    (∑' r : P2Index38 n, ‖T (lp.single 2 r (1 : ℝ))‖^2) ≤
      A^2*Lib.invSqSum*(∑' m : ℤ, e m^2) := by
  classical
  have hcol (r : P2Index38 n) :
      HasSum (fun m : P2Index38 n => ‖T (lp.single 2 r (1 : ℝ)) m‖^2)
        (‖T (lp.single 2 r (1 : ℝ))‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (T (lp.single 2 r (1 : ℝ)))
  have hEsub : Summable (fun m : P2Index38 n => e m.1^2) :=
    hes.comp_injective (i := fun m : P2Index38 n => m.1) Subtype.val_injective
  have hEmass : (∑' m : P2Index38 n, e m.1^2) ≤ ∑' m : ℤ, e m^2 :=
    Summable.tsum_subtype_le (fun m : ℤ => e m^2) {m : ℤ | m ≠ n}
      (fun _ => sq_nonneg _) hes
  have hfinite (S : Finset (P2Index38 n)) :
      ∑ r ∈ S, ‖T (lp.single 2 r (1 : ℝ))‖^2 ≤
        A^2*Lib.invSqSum*(∑' m : ℤ, e m^2) := by
    have hfin : HasSum
        (fun m : P2Index38 n => ∑ r ∈ S, ‖T (lp.single 2 r (1 : ℝ)) m‖^2)
        (∑ r ∈ S, ‖T (lp.single 2 r (1 : ℝ))‖^2) :=
      hasSum_sum (fun r _ => hcol r)
    have hpoint (m : P2Index38 n) :
        ∑ r ∈ S, ‖T (lp.single 2 r (1 : ℝ)) m‖^2 ≤
          (A^2*Lib.invSqSum)*e m.1^2 := by
      have hwfull := Lib.summable_c3w_sq m.1
      have hws : Summable (fun r : P2Index38 n => Lib.c3w m.1 r.1^2) :=
        hwfull.comp_injective (i := fun r : P2Index38 n => r.1) Subtype.val_injective
      have hwmass : (∑' r : P2Index38 n, Lib.c3w m.1 r.1^2) ≤ Lib.invSqSum :=
        (Summable.tsum_subtype_le (fun r : ℤ => Lib.c3w m.1 r^2)
          {r : ℤ | r ≠ n} (fun _ => sq_nonneg _) hwfull).trans_eq (Lib.tsum_c3w_sq m.1)
      have hwfinite : (∑ r ∈ S, Lib.c3w m.1 r.1^2) ≤ Lib.invSqSum :=
        (hws.sum_le_tsum S (fun _ _ => sq_nonneg _)).trans hwmass
      have hsq (r : P2Index38 n) :
          ‖T (lp.single 2 r (1 : ℝ)) m‖^2 ≤ (A^2*e m.1^2)*Lib.c3w m.1 r.1^2 := by
        have hh := mul_self_le_mul_self (norm_nonneg _) (hbound m r)
        nlinarith [hh]
      calc
        _ ≤ ∑ r ∈ S, (A^2*e m.1^2)*Lib.c3w m.1 r.1^2 := Finset.sum_le_sum (fun r _ => hsq r)
        _ = (A^2*e m.1^2)*(∑ r ∈ S, Lib.c3w m.1 r.1^2) := by rw [Finset.mul_sum]
        _ ≤ (A^2*e m.1^2)*Lib.invSqSum :=
          mul_le_mul_of_nonneg_left hwfinite (mul_nonneg (sq_nonneg A) (sq_nonneg _))
        _ = _ := by ring
    have hdom := hEsub.mul_left (A^2*Lib.invSqSum)
    have hb := hfin.summable.tsum_le_tsum hpoint hdom
    rw [hfin.tsum_eq,tsum_mul_left] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hEmass
      (mul_nonneg (sq_nonneg A) Lib.invSqSum_nonneg))
  have hsum : Summable (fun r : P2Index38 n => ‖T (lp.single 2 r (1 : ℝ))‖^2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  have hmass : (∑' r : P2Index38 n, ‖T (lp.single 2 r (1 : ℝ))‖^2) ≤
      A^2*Lib.invSqSum*(∑' m : ℤ, e m^2) :=
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite
  refine ⟨?_,hsum,hmass⟩
  apply isHilbertSchmidt_of_summable (p3RealHilbertBasis38 n)
  simpa only [p3RealHilbertBasis_apply38] using hsum

theorem actual_real_K_isHilbertSchmidt (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) (n : ℤ) :
    IsHilbertSchmidt (P3DiagonalOperator.actualOffDiagonal n
      (fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))) := by
  have hφ := realSlice_mem_gkW u
  obtain ⟨Ur,hUr,_hUrW,Vr,hVr,H,hH,hr⟩ :=
    p2OmittedRatio_all_cut_bound38 (realSlice u) hφ s
  have hratio := hr (realSlice u) (mem_of_mem_nhds hUr) s (mem_of_mem_nhds hVr)
  obtain ⟨Ue,hUe,_hUeW,Ve,hVe,Be,_hBe,he⟩ :=
    p2RowEnvelope_common_l2_bound38 (realSlice u) hφ s
  have hEs := (he (realSlice u) (mem_of_mem_nhds hUe) s (mem_of_mem_nhds hVe)).1
  have hrow := P3JacobianColumns.actual_real_K_row_bound u C R c N hg hfam s hs hσ
    H hH hratio n
  exact (matrix_row_bound_isHS n _ (p2RowEnvelope38 (realSlice u) s)
    (2*Real.pi*c^2*H) (by positivity) (p2RowEnvelope_nonneg38 (realSlice u) s) hEs hrow).1

theorem actual_real_K_isCompact (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) (n : ℤ) :
    IsCompactOperator (P3DiagonalOperator.actualOffDiagonal n
      (fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))) :=
  hilbertSchmidt_isCompact _ (actual_real_K_isHilbertSchmidt u C R c N hg hfam s hs hσ n)

end
end NlsGge.GK38.P3OperatorBridge
