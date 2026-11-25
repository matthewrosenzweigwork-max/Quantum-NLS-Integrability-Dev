import QuantumNLS.Ext025A5Triangular
import QuantumNLS.BetheSmooth

/-! GP-03 finite application, R-864F39DE and R-4C8D7C9E. Real arctangent
analyticity is constructed by analytic inversion of tangent. Thus the actual
finite equations supply a convergent series without an arbitrary Banach-domain
holomorphy-to-series assumption. The actual Gaudin inverse and the global root
existence/uniqueness are imported from their proved constructions. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace QuantumNLS.Ext025A6
open BetheAdmission BetheRoots BetheSmooth

/-- A convergent real multilinear series for arctangent, constructed by
inverting sine/cosine on its actual principal-branch interval. -/
theorem arctan_analyticAt (x : ℝ) : AnalyticAt ℝ Real.arctan x := by
  let a := Real.arctan x
  have hc : Real.cos a ≠ 0 := (Real.cos_arctan_pos x).ne'
  let k := 1 / Real.cos a ^ 2
  have hk : k ≠ 0 := one_div_ne_zero (pow_ne_zero _ hc)
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 k hk)
  have hd : HasFDerivAt Real.tan e.toContinuousLinearMap a := by
    convert (Real.hasDerivAt_tan hc).hasFDerivAt using 1
    ext
    rfl
  have ht : AnalyticAt ℝ Real.tan a := by
    rw [show Real.tan = (fun y : ℝ => Real.sin y / Real.cos y) from
      funext Real.tan_eq_sin_div_cos]
    exact Real.analyticAt_sin.div Real.analyticAt_cos hc
  obtain ⟨p, hp⟩ := ht
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ ℝ ℝ).symm e := by
    apply (continuousMultilinearCurryFin1 ℝ ℝ ℝ).injective
    simpa using hp.hasFDerivAt.unique hd
  have h := (Real.tanPartialHomeomorph.hasFPowerSeriesAt_symm
    (Real.arctan_mem_Ioo x) hp hp1).analyticAt
  simpa only [Real.coe_tanPartialHomeomorph_symm, Real.coe_tanPartialHomeomorph,
    Real.tan_arctan, a] using h

/-- Joint analyticity of the literal logarithmic Bethe equations, including
colliding configurations; only nonzero coupling is required. -/
theorem logMap_analyticAt {N : ℕ} (L : ℝ) {c : ℝ} (hc : c ≠ 0)
    (q : Fin N → ℝ) :
    AnalyticAt ℝ (fun p : ℝ × (Fin N → ℝ) => logMap L p.1 p.2) (c, q) := by
  have hi (i : Fin N) : AnalyticAt ℝ
      (fun p : ℝ × (Fin N → ℝ) => p.2 i) (c, q) :=
    ((ContinuousLinearMap.proj (R := ℝ) i).analyticAt q).comp (x := (c, q)) (f := fun p : ℝ × (Fin N → ℝ) => p.2) analyticAt_snd
  apply AnalyticAt.pi
  intro i
  unfold logMap
  exact (analyticAt_const.mul (hi i)).add
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun j _ =>
      (arctan_analyticAt _).comp (((hi i).sub (hi j)).div analyticAt_fst hc)))

/-- The unique minimizer is jointly analytic in positive coupling and in
arbitrary real forcing. The analytic branch is derived from the actual
Gaudin derivative, and uniqueness identifies it with the constructed roots. -/
theorem root_joint_analyticAt {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) :
    AnalyticAt ℝ (fun p : ℝ × (Fin N → ℝ) => root L p.2 p.1) (c, b) := by
  let q := root L b c
  let f := fun p : ℝ × (Fin N → ℝ) => logMap L p.1 p.2
  let D := fderiv ℝ f (c, q)
  let A := D.comp (ContinuousLinearMap.inl ℝ ℝ (Fin N → ℝ))
  let B := ContinuousLinearEquiv.ofBijective (gaudin L c q)
    (LinearMap.ker_eq_bot.mpr (gaudin_bijective hL hc q).1)
    (LinearMap.range_eq_top.mpr (gaudin_bijective hL hc q).2)
  have hB : B.toContinuousLinearMap = gaudin L c q := rfl
  have hD : A.coprod B.toContinuousLinearMap = D := by
    rw [hB, ← logMap_partial_q L hc q]
    exact D.coprod_comp_inl_inr
  let T : ℝ × (Fin N → ℝ) → ℝ × (Fin N → ℝ) := fun p => (p.1, f p)
  let I := QuantumNLS.Ext025A5.triangularEquiv A B
  have ht : AnalyticAt ℝ T (c, q) :=
    analyticAt_fst.prod (logMap_analyticAt L hc.ne' q)
  have hd : HasFDerivAt T I.toContinuousLinearMap (c, q) := by
    have hf : HasFDerivAt f (A.coprod B.toContinuousLinearMap) (c, q) :=
      hD.symm ▸ (logMap_analyticAt L hc.ne' q).differentiableAt.hasFDerivAt
    exact hasFDerivAt_fst.prodMk hf
  obtain ⟨g, hg, _, _, hr⟩ := QuantumNLS.Ext025A.gp03_analytic_inverse I ht hd
  have hbase : T (c, q) = (c, b) := by
    exact Prod.ext rfl (root_solves hL hc b)
  rw [hbase] at hg hr
  apply (analyticAt_snd.comp hg).congr
  filter_upwards [hr,
    (continuousAt_fst : ContinuousAt Prod.fst (c, b)).tendsto.eventually
      (isOpen_Ioi.mem_nhds hc)] with p hp hpos
  have hfst : (g p).1 = p.1 := by simpa only [T] using congrArg Prod.fst hp
  have hsol : logMap L p.1 (g p).2 = p.2 := by
    simpa only [T, f, hfst] using congrArg Prod.snd hp
  exact eq_root hL hpos hsol

/-- Fixed-forcing coupling analyticity, filling the analytic upgrade missing
from the previously proved smooth root construction. -/
theorem root_analyticAt {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) : AnalyticAt ℝ (root L b) c :=
  (root_joint_analyticAt hL hc b).comp (f := fun d : ℝ => (d, b))
    (analyticAt_id.prod analyticAt_const)

/-- The right-hand side in the source, using zero-based Fin indices.
`2*i+1-N` equals the source's `2*(i+1)-N-1`. -/
def realLabelForce {N : ℕ} (ν : Fin N → ℝ) : Fin N → ℝ :=
  fun i => 2 * Real.pi * ν i + Real.pi * (2 * (i : ℝ) + 1 - N)

/-- This is precisely the local analytic GP-03 application in F02, jointly
in coupling and real labels. Ordering is a separate source condition; the
analyticity conclusion even holds for arbitrary real labels. -/
theorem f02_roots_joint_analyticAt {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (ν : Fin N → ℝ) : AnalyticAt ℝ
      (fun p : ℝ × (Fin N → ℝ) => root L (realLabelForce p.2) p.1) (c, ν) := by
  have hb : AnalyticAt ℝ (fun p : ℝ × (Fin N → ℝ) => realLabelForce p.2) (c, ν) := by
    apply AnalyticAt.pi
    intro i
    exact (analyticAt_const.mul
      (((ContinuousLinearMap.proj (R := ℝ) i).analyticAt ν).comp (x := (c, ν))
        (f := fun p : ℝ × (Fin N → ℝ) => p.2) analyticAt_snd)).add
        analyticAt_const
  exact (root_joint_analyticAt hL hc (realLabelForce ν)).comp
    (f := fun p : ℝ × (Fin N → ℝ) => (p.1, realLabelForce p.2))
    (analyticAt_fst.prod hb)

/-- Literal source equation: no root or residual is supplied as a premise. -/
theorem f02_roots_solve {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (ν : Fin N → ℝ) (i : Fin N) :
    L * root L (realLabelForce ν) c i +
      2 * ∑ j ∈ Finset.univ.erase i,
        Real.arctan ((root L (realLabelForce ν) c i -
          root L (realLabelForce ν) c j) / c) =
      2 * Real.pi * ν i + Real.pi * (2 * (i : ℝ) + 1 - N) := by
  have h := congrFun (root_solves hL hc (realLabelForce ν)) i
  rw [logMap_erase] at h
  exact h
end QuantumNLS.Ext025A6

#print axioms QuantumNLS.Ext025A6.arctan_analyticAt
#print axioms QuantumNLS.Ext025A6.logMap_analyticAt
#print axioms QuantumNLS.Ext025A6.root_joint_analyticAt
#print axioms QuantumNLS.Ext025A6.root_analyticAt
#print axioms QuantumNLS.Ext025A6.realLabelForce
#print axioms QuantumNLS.Ext025A6.f02_roots_joint_analyticAt
#print axioms QuantumNLS.Ext025A6.f02_roots_solve
