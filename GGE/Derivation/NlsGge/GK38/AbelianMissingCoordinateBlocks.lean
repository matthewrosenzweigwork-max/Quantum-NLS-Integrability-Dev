import NlsGge.GK38.AbelianActualDifferenceOperatorBlock

/-! UNCOMPILED exact full lp2 block decomposition at one signed coordinate.
This is a finite algebraic decomposition of the ACTUAL operator, followed by
norm inequalities. No matrix-energy, invertibility or compactness is assumed. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6Full_coordinate_split38 (n : ℤ) (x : Lib.L2Seq) :
    p2Extend38 n (p2Restrict38 n x)+lp.single 2 n (x n)=x := by
  apply Subtype.ext
  funext k
  by_cases hk : k=n
  · subst k
    rw [lp.coeFn_add,Pi.add_apply,p2Extend_self38,lp.single_apply_self,zero_add]
  · let m : P2Index38 n := ⟨k,hk⟩
    change p2Extend38 n (p2Restrict38 n x) m.val+
      (lp.single (E := fun _ : ℤ => ℂ) 2 n (x n)) m.val=x m.val
    rw [p2Extend_at38,p2Restrict_apply38,
      lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (x n) hk,add_zero]

def p6NonmissingBlock38 (n : ℤ) (T : Lib.L2Seq →L[ℂ] Lib.L2Seq) :
    P2Space38 n →L[ℂ] P2Space38 n :=
  (p2Restrict38 n).comp (T.comp (p2Extend38 n))

def p6MissingRowBlock38 (n : ℤ) (T : Lib.L2Seq →L[ℂ] Lib.L2Seq) :
    P2Space38 n →L[ℂ] Lib.L2Seq :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp (T.comp (p2Extend38 n)))

def p6MissingColumnVector38 (n : ℤ) (T : Lib.L2Seq →L[ℂ] Lib.L2Seq) : Lib.L2Seq :=
  p2Extend38 n (p2Restrict38 n (T (lp.single 2 n (1 : ℂ))))

theorem p6MissingRowBlock_unit38 (n : ℤ) (T : Lib.L2Seq →L[ℂ] Lib.L2Seq)
    (r : P2Index38 n) :
    p6MissingRowBlock38 n T (lp.single 2 r (1 : ℂ))=
      lp.single 2 n (T (lp.single 2 r.val (1 : ℂ)) n) := by
  change lp.single (E := fun _ : ℤ => ℂ) 2 n
    (T (p2Extend38 n (lp.single 2 r (1 : ℂ))) n)=_
  rw [p6Extend_unit38]

theorem p6Full_operator_coordinate_decomposition38 (n : ℤ)
    (T : Lib.L2Seq →L[ℂ] Lib.L2Seq) (x : Lib.L2Seq) :
    T x=p2Extend38 n (p6NonmissingBlock38 n T (p2Restrict38 n x))+
      p6MissingRowBlock38 n T (p2Restrict38 n x)+
      (x n) • p6MissingColumnVector38 n T+
      lp.single 2 n ((x n)*(T (lp.single 2 n (1 : ℂ)) n)) := by
  let z : Lib.L2Seq := T (p2Extend38 n (p2Restrict38 n x))
  let w : Lib.L2Seq := T (lp.single 2 n (1 : ℂ))
  have hunit : lp.single (E := fun _ : ℤ => ℂ) 2 n (x n)=
      (x n) • lp.single 2 n (1 : ℂ) := by
    simpa only [smul_eq_mul,mul_one] using lp.single_smul (E := fun _ : ℤ => ℂ) 2 n (x n) (1 : ℂ)
  have hTx : T x=z+(x n) • w := by
    calc
      _ = T (p2Extend38 n (p2Restrict38 n x)+lp.single 2 n (x n)) :=
        congrArg T (p6Full_coordinate_split38 n x).symm
      _ = _ := by rw [map_add,hunit,map_smul]
  have hsingle : (x n) • lp.single (E := fun _ : ℤ => ℂ) 2 n (w n)=
      lp.single 2 n ((x n)*(w n)) := by
    simpa only [smul_eq_mul] using (lp.single_smul (E := fun _ : ℤ => ℂ) 2 n (x n) (w n)).symm
  calc
    _ = z+(x n) • w := hTx
    _ = (p2Extend38 n (p2Restrict38 n z)+lp.single 2 n (z n))+
        (x n) • (p2Extend38 n (p2Restrict38 n w)+lp.single 2 n (w n)) :=
      congrArg₂ (fun a b : Lib.L2Seq => a+(x n) • b)
        (p6Full_coordinate_split38 n z).symm (p6Full_coordinate_split38 n w).symm
    _ = _ := by
      rw [smul_add,hsingle]
      change (p2Extend38 n (p2Restrict38 n z)+
        lp.single (E := fun _ : ℤ => ℂ) 2 n (z n))+
        ((x n) • p2Extend38 n (p2Restrict38 n w)+
          lp.single (E := fun _ : ℤ => ℂ) 2 n ((x n)*(w n)))=
        p2Extend38 n (p2Restrict38 n z)+
          lp.single (E := fun _ : ℤ => ℂ) 2 n (z n)+
          (x n) • p2Extend38 n (p2Restrict38 n w)+
          lp.single (E := fun _ : ℤ => ℂ) 2 n ((x n)*(w n))
      abel

theorem p6Full_operator_norm_le_of_decomposition38 (n : ℤ)
    (T : Lib.L2Seq →L[ℂ] Lib.L2Seq)
    (A : P2Space38 n →L[ℂ] P2Space38 n)
    (B : P2Space38 n →L[ℂ] Lib.L2Seq) (v : Lib.L2Seq) (a : ℂ)
    (hdecomp : ∀ x : Lib.L2Seq,
      T x=p2Extend38 n (A (p2Restrict38 n x))+B (p2Restrict38 n x)+
        (x n) • v+lp.single (E := fun _ : ℤ => ℂ) 2 n ((x n)*a)) :
    ‖T‖ ≤ ‖A‖+‖B‖+‖v‖+‖a‖ := by
  have hnonneg : 0 ≤ ‖A‖+‖B‖+‖v‖+‖a‖ :=
    add_nonneg (add_nonneg (add_nonneg (norm_nonneg A) (norm_nonneg B))
      (norm_nonneg v)) (norm_nonneg a)
  apply T.opNorm_le_bound hnonneg
  intro x
  have hR : ‖p2Restrict38 n x‖ ≤ ‖x‖ := p2RestrictElement_norm_le38 n x
  have hxn : ‖x n‖ ≤ ‖x‖ :=
    lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x n
  have hA := (A.le_opNorm (p2Restrict38 n x)).trans
    (mul_le_mul_of_nonneg_left hR (norm_nonneg A))
  have hB := (B.le_opNorm (p2Restrict38 n x)).trans
    (mul_le_mul_of_nonneg_left hR (norm_nonneg B))
  calc
    _ = ‖p2Extend38 n (A (p2Restrict38 n x))+B (p2Restrict38 n x)+
        (x n) • v+lp.single (E := fun _ : ℤ => ℂ) 2 n ((x n)*a)‖ :=
      congrArg norm (hdecomp x)
    _ ≤ ‖p2Extend38 n (A (p2Restrict38 n x))‖+‖B (p2Restrict38 n x)‖+
        ‖(x n) • v‖+‖lp.single (E := fun _ : ℤ => ℂ) 2 n ((x n)*a)‖ :=
      norm_add₄_le
    _ = ‖A (p2Restrict38 n x)‖+‖B (p2Restrict38 n x)‖+
        ‖x n‖*‖v‖+‖x n‖*‖a‖ := by
      rw [p2Extend_norm38,norm_smul,
        lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_mul]
    _ ≤ ‖A‖*‖x‖+‖B‖*‖x‖+‖x‖*‖v‖+‖x‖*‖a‖ :=
      add_le_add (add_le_add (add_le_add hA hB)
        (mul_le_mul_of_nonneg_right hxn (norm_nonneg v)))
        (mul_le_mul_of_nonneg_right hxn (norm_nonneg a))
    _ = _ := by
      rw [add_mul,add_mul,add_mul,mul_comm ‖v‖ ‖x‖,mul_comm ‖a‖ ‖x‖]

theorem p6Full_operator_norm_le_blocks38 (n : ℤ) (T : Lib.L2Seq →L[ℂ] Lib.L2Seq) :
    ‖T‖ ≤ ‖p6NonmissingBlock38 n T‖+‖p6MissingRowBlock38 n T‖+
      ‖p6MissingColumnVector38 n T‖+‖T (lp.single 2 n (1 : ℂ)) n‖ := by
  exact p6Full_operator_norm_le_of_decomposition38 n T
    (p6NonmissingBlock38 n T) (p6MissingRowBlock38 n T)
    (p6MissingColumnVector38 n T) (T (lp.single 2 n (1 : ℂ)) n)
    (p6Full_operator_coordinate_decomposition38 n T)

end
end NlsGge.GK38
