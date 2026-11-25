import NlsGge.GK38.AbelianJacobianNumerator

/-! Actual Abelian-period line derivatives and the actual Hilbert Jacobian matrix.
UNCOMPILED source preparation; numerator integrability precedes circle linearity. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section

theorem period_add_single (m n r : ℤ) (hrn : r ≠ n)
    (φ : PotPair) (hφ : φ ∈ gkW) (s : Lib.L2Seq) (t : ℂ) :
    abelianPeriod38 m φ (p2FullNumerator38 n (s + t • lp.single 2 r (1 : ℂ))) =
      abelianPeriod38 m φ (p2FullNumerator38 n s) +
        t * abelianPeriod38 m φ (p3NumeratorColumn38 n r s) := by
  have hb := p2Period_integrable38 m n φ hφ s
  have hc := column_integrable m n r φ hφ s
  have ht : CircleIntegrable
      (fun z => t * (p3NumeratorColumn38 n r s z / canonRoot38 φ z))
      (discC φ m) (discR φ m) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hc.const_smul (a := t)
  have heq : (fun z => p2FullNumerator38 n
      (s + t • lp.single 2 r (1 : ℂ)) z / canonRoot38 φ z) =
      (fun z => p2FullNumerator38 n s z / canonRoot38 φ z +
        t * (p3NumeratorColumn38 n r s z / canonRoot38 φ z)) := by
    funext z
    rw [numerator_add_single n r hrn s z t]
    ring
  unfold abelianPeriod38
  rw [heq, circleIntegral.integral_add hb ht, circleIntegral.integral_const_mul]

theorem extend_single (n : ℤ) (r : P2Index38 n) (t : ℂ) :
    p2Extend38 n (lp.single 2 r t) = t • lp.single 2 r.1 (1 : ℂ) := by
  rw [← P3FreeDerivative.restrict_single n r t]
  apply P2FreeProbe.extend_restrict_of_zero n
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 r.1 (1 : ℂ) (Ne.symm r.2), mul_zero]

/-- The scalar coordinate algebra is earned before transporting the Hilbert graph. -/
theorem fnCoord_add_single (n : ℤ) (m r : P2Index38 n)
    (φ : PotPair) (hφ : φ ∈ gkW) (s : P2Space38 n) (t : ℂ) :
    p2FnCoord38 n (φ, s + t • lp.single 2 r (1 : ℂ)) m =
      p2FnCoord38 n (φ,s) m + t *
        ((((n - m.1 : ℤ) : ℂ)) * abelianPeriod38 m.1 φ
          (p3NumeratorColumn38 n r.1 (p2Extend38 n s))) := by
  unfold p2FnCoord38 p2Numerator38
  rw [map_add, map_smul, extend_single n r 1, one_smul,
    period_add_single m.1 n r.1 r.2 φ hφ (p2Extend38 n s) t]
  ring

/-- Exact actual scalar affine line, for every signed output and input coordinate. -/
theorem coordinate_add_single (n : ℤ) (m r : P2Index38 n)
    (φ : PotPair) (hφ : φ ∈ gkW) (s : P2Space38 n) (t : ℂ) :
    p2Fn38 n (φ, s + t • lp.single 2 r (1 : ℂ)) m =
      p2Fn38 n (φ,s) m + t *
        ((((n - m.1 : ℤ) : ℂ)) * abelianPeriod38 m.1 φ
          (p3NumeratorColumn38 n r.1 (p2Extend38 n s))) := by
  have hleft := p2Fn_apply38 n (φ, s + t • lp.single 2 r (1 : ℂ)) hφ m
  have hbase := p2Fn_apply38 n (φ,s) hφ m
  apply hleft.trans
  exact (fnCoord_add_single n m r φ hφ s t).trans
    (congrArg
      (fun q : ℂ => q + t * ((((n - m.1 : ℤ) : ℂ)) *
        abelianPeriod38 m.1 φ (p3NumeratorColumn38 n r.1 (p2Extend38 n s))))
      hbase.symm)

theorem coordinate_hasDerivAt (n : ℤ) (m r : P2Index38 n)
    (φ : PotPair) (hφ : φ ∈ gkW) (s : P2Space38 n) :
    HasDerivAt
      (fun t : ℂ => p2Fn38 n (φ, s + t • lp.single 2 r (1 : ℂ)) m)
      ((((n - m.1 : ℤ) : ℂ)) *
        abelianPeriod38 m.1 φ (p3NumeratorColumn38 n r.1 (p2Extend38 n s))) 0 := by
  have heq : (fun t : ℂ => p2Fn38 n (φ, s + t • lp.single 2 r (1 : ℂ)) m) =
      (fun t : ℂ => p2Fn38 n (φ,s) m + t *
        ((((n - m.1 : ℤ) : ℂ)) *
          abelianPeriod38 m.1 φ (p3NumeratorColumn38 n r.1 (p2Extend38 n s)))) :=
    funext (coordinate_add_single n m r φ hφ s)
  rw [heq]
  simpa only [one_mul] using!
    (((hasDerivAt_id (0 : ℂ)).mul_const
      ((((n - m.1 : ℤ) : ℂ)) *
        abelianPeriod38 m.1 φ (p3NumeratorColumn38 n r.1 (p2Extend38 n s)))).const_add
      (p2Fn38 n (φ,s) m))

/-- Generic chain-rule transfer; its scalar-line premise is realized above for actual Fn. -/
theorem jacobian_column_from_scalar_line (n : ℤ)
    (f : P2Space38 n → P2Space38 n) (s : P2Space38 n)
    (m r : P2Index38 n) (c : ℂ) (hf : AnalyticAt ℂ f s)
    (hline : HasDerivAt
      (fun t : ℂ => f (s + t • lp.single 2 r (1 : ℂ)) m) c 0) :
    (fderiv ℂ f s) (lp.single 2 r (1 : ℂ)) m = c := by
  let D := fderiv ℂ f s
  let E : P2Space38 n →L[ℂ] ℂ :=
    lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 m
  let S : ℂ →L[ℂ] P2Space38 n :=
    ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 r (1 : ℂ))
  have hfd : HasFDerivAt f D s := hf.differentiableAt.hasFDerivAt
  have ha : HasFDerivAt (fun t : ℂ => s + S t) S 0 :=
    (S.hasFDerivAt (x := 0)).const_add s
  have hf' : HasFDerivAt f D (s + S 0) := by
    simpa only [map_zero, add_zero] using hfd
  have he := (E.hasFDerivAt).comp 0 (hf'.comp 0 ha)
  have hd := he.hasDerivAt
  have hEval (x : P2Space38 n) : E x = x m := rfl
  have hSpan (t : ℂ) : S t = t • lp.single 2 r (1 : ℂ) := rfl
  have hd' : HasDerivAt
      (fun t : ℂ => f (s + t • lp.single 2 r (1 : ℂ)) m)
      (D (lp.single 2 r (1 : ℂ)) m) 0 := by
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      hEval, hSpan, one_smul] using! hd
  exact hd'.unique hline

/-- The matrix coordinate is the earned derivative of the actual Hilbert Fn. -/
theorem matrix_coordinate (n : ℤ) (m r : P2Index38 n)
    (φ : PotPair) (hφ : φ ∈ gkW) (s : P2Space38 n) :
    (fderiv ℂ (fun u : P2Space38 n => p2Fn38 n (φ,u)) s)
        (lp.single 2 r (1 : ℂ)) m =
      (((n - m.1 : ℤ) : ℂ)) *
        abelianPeriod38 m.1 φ (p3NumeratorColumn38 n r.1 (p2Extend38 n s)) := by
  have haf : AnalyticAt ℂ
      (fun u : P2Space38 n => p2Fn38 n (φ,u)) s := AnalyticAt.comp
    (g := p2Fn38 n) (f := fun u : P2Space38 n => (φ,u))
    (p2Fn_analytic38 n (φ,s) ⟨hφ,mem_univ _⟩)
    (analyticAt_const.prod analyticAt_id)
  exact jacobian_column_from_scalar_line n
    (fun u : P2Space38 n => p2Fn38 n (φ,u)) s m r _ haf
    (coordinate_hasDerivAt n m r φ hφ s)

end
end NlsGge.GK38.P3JacobianColumns
