import NlsGge.GK38.AbelianComplexMatrixOperatorBound
import NlsGge.GK38.AbelianCompactDiagonalTails
import Mathlib.Analysis.Normed.Lp.lpHolder

/-! UNCOMPILED ACTUAL complex nonmissing block of padded Qn minus Qstar.
The preceding actual joint coefficient mass is converted to a genuine HS
operator and a TRUE operator norm estimate. Exceptional n row/column and
uniform compact convergence remain separate. -/
set_option autoImplicit false
open Set Filter Topology Metric
open scoped Classical
namespace NlsGge.GK38
noncomputable section

/-- The unit vector data does not depend on the equality decision procedure. -/
theorem p6ComplexSingle_classical38 {ι : Type*} (d : DecidableEq ι) (r : ι) (z : ℂ) :
    @lp.single ι (fun _ : ι => ℂ) (fun _ => inferInstance) d 2 r z=
      @lp.single ι (fun _ : ι => ℂ) (fun _ => inferInstance)
        (fun a b => Classical.propDecidable (a=b)) 2 r z := by
  exact congrArg (fun q : DecidableEq ι =>
    @lp.single ι (fun _ : ι => ℂ) (fun _ => inferInstance) q 2 r z)
    (Subsingleton.elim d (fun a b => Classical.propDecidable (a=b)))

def p6ComplexDiagonal38 {ι : Type*}
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  lp.mapCLM 2 (fun m : ι => T (lp.single 2 m (1 : ℂ)) m •
    ContinuousLinearMap.id ℂ ℂ) (norm_nonneg T) (fun m => by
      simpa only [norm_smul,ContinuousLinearMap.norm_id,mul_one] using
        p6UnitDiagonal_norm_le_operator38 T m)

theorem p6ComplexDiagonal_apply38 {ι : Type*}
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)
    (x : lp (fun _ : ι => ℂ) 2) (m : ι) :
    p6ComplexDiagonal38 T x m=T (lp.single 2 m (1 : ℂ)) m*x m := rfl

def p6NonmissingDifference38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq) :
    P2Space38 n →L[ℂ] P2Space38 n :=
  (p2Restrict38 n).comp ((p6PaddedJacobian38 n φ s-p6Qstar38 φ s).comp (p2Extend38 n))

def p6DifferenceOffDiagonalBlock38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq) :
    P2Space38 n →L[ℂ] P2Space38 n :=
  p6NonmissingDifference38 n φ s-p6ComplexDiagonal38 (p6NonmissingDifference38 n φ s)

theorem p6Extend_unit38 (n : ℤ) (r : P2Index38 n) :
    p2Extend38 n (lp.single 2 r (1 : ℂ))=lp.single 2 r.val (1 : ℂ) := by
  classical
  apply Subtype.ext
  funext k
  by_cases hk : k=n
  · subst k
    rw [p2Extend_self38,lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 r.val
      (1 : ℂ) (Ne.symm r.property)]
  · let m : P2Index38 n := ⟨k,hk⟩
    change p2Extend38 n (lp.single (E := fun _ : P2Index38 n => ℂ) 2 r (1 : ℂ)) m.val=
      (lp.single (E := fun _ : ℤ => ℂ) 2 r.val (1 : ℂ)) m.val
    rw [p2Extend_at38]
    by_cases hmr : m=r
    · change (Pi.single r (1 : ℂ) : P2Index38 n → ℂ) m=
        (Pi.single r.val (1 : ℂ) : ℤ → ℂ) m.val
      simp only [hmr,Pi.single_eq_same]
    · have hv : m.val ≠ r.val := fun he => hmr (Subtype.ext he)
      rw [lp.single_apply_ne (E := fun _ : P2Index38 n => ℂ) 2 r (1 : ℂ) hmr,
        lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 r.val (1 : ℂ) hv]

theorem p6NonmissingDifference_matrix38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq)
    (m r : P2Index38 n) :
    p6NonmissingDifference38 n φ s (lp.single 2 r (1 : ℂ)) m=
      (p6PaddedJacobian38 n φ s-p6Qstar38 φ s) (lp.single 2 r.val (1 : ℂ)) m.val := by
  change (p6PaddedJacobian38 n φ s-p6Qstar38 φ s)
    (p2Extend38 n (lp.single 2 r (1 : ℂ))) m.val=_
  rw [p6Extend_unit38]

theorem p6DifferenceOffDiagonalBlock_matrix38 (n : ℤ) (φ : PotPair)
    (s : Lib.L2Seq) (m r : P2Index38 n) :
    p6DifferenceOffDiagonalBlock38 n φ s (lp.single 2 r (1 : ℂ)) m=
      if r=m then 0 else
        (p6PaddedJacobian38 n φ s-p6Qstar38 φ s) (lp.single 2 r.val (1 : ℂ)) m.val := by
  classical
  change p6NonmissingDifference38 n φ s (lp.single 2 r (1 : ℂ)) m-
    p6ComplexDiagonal38 (p6NonmissingDifference38 n φ s) (lp.single 2 r (1 : ℂ)) m=_
  rw [p6ComplexDiagonal_apply38]
  by_cases hrm : r=m
  · subst r
    rw [lp.single_apply_self,mul_one,ite_eq_left rfl]
    simp only [p6ComplexSingle_classical38,sub_self]
  · rw [lp.single_apply_ne (E := fun _ : P2Index38 n => ℂ) 2 r (1 : ℂ)
      (Ne.symm hrm),mul_zero,sub_zero,ite_eq_right hrm,p6NonmissingDifference_matrix38]

theorem p6ActualDifference_offDiagonal_isHS_norm_bound38
    (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) (n : ℤ) :
    NlsGge.Pilot.IsComplexHilbertSchmidt (p6DifferenceOffDiagonalBlock38 n φ s) ∧
      ‖p6DifferenceOffDiagonalBlock38 n φ s‖ ≤
        Real.sqrt ((2*c^2*H)^2*Lib.invSqSum*
          (∑' m : ℤ, p2RowEnvelope38 φ s m^2*
            (‖s n‖+p2RowEnvelope38 φ 0 m)^2*Lib.c3w m n^2)) := by
  classical
  have hm := p6ActualDifference_offDiagonal_joint_mass38 φ hφ C R c N hg hfam s hσ
    H hH hRatio n
  have heq (p : P2Index38 n × P2Index38 n) :
      ‖p6DifferenceOffDiagonalBlock38 n φ s (lp.single 2 p.2 (1 : ℂ)) p.1‖^2=
      (if p.2=p.1 then 0 else
        ‖(p6PaddedJacobian38 n φ s-p6Qstar38 φ s)
          (lp.single 2 p.2.val (1 : ℂ)) p.1.val‖^2) := by
    rw [p6DifferenceOffDiagonalBlock_matrix38]
    split_ifs <;> simp only [norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hs : Summable (fun p : P2Index38 n × P2Index38 n =>
      ‖p6DifferenceOffDiagonalBlock38 n φ s (lp.single 2 p.2 (1 : ℂ)) p.1‖^2) := by
    simp only [heq]
    convert! hm.1
  have hb := p6ComplexLp_joint_matrix_mass38 (p6DifferenceOffDiagonalBlock38 n φ s)
    (by simpa only [p6ComplexSingle_classical38] using! hs)
  have hbound : ‖p6DifferenceOffDiagonalBlock38 n φ s‖ ≤
      Real.sqrt (∑' p : P2Index38 n × P2Index38 n,
        ‖p6DifferenceOffDiagonalBlock38 n φ s (lp.single 2 p.2 (1 : ℂ)) p.1‖^2) := by
    simpa only [p6ComplexSingle_classical38] using! hb.2.2
  refine ⟨hb.1,hbound.trans (Real.sqrt_le_sqrt ?_)⟩
  simp only [heq]
  convert! hm.2

end
end NlsGge.GK38
