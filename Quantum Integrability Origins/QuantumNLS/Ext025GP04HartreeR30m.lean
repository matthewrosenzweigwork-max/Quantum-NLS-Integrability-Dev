import QuantumNLS.Ext025A8SourceHartree

/-! The actual PROP-001 Hartree field is C¹ on a ball larger than the unit ball.
The frozen rank margin controls the differentiated series. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set Metric Filter Topology
open scoped NNReal
namespace QuantumNLS.Ext025GP04HartreeR30m

open TensorCarrier TensorPlacements Ext025A8
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

private def realAdjoint {U V : Type*} [NormedAddCommGroup U] [NormedAddCommGroup V]
    [InnerProductSpace ℂ U] [InnerProductSpace ℂ V] [CompleteSpace U] [CompleteSpace V] :
    (U →L[ℂ] V) →L[ℝ] (V →L[ℂ] U) := by
  let L : (U →L[ℂ] V) →ₗ[ℝ] (V →L[ℂ] U) :=
    { toFun := fun A => A.adjoint
      map_add' := fun A B => map_add ContinuousLinearMap.adjoint A B
      map_smul' := fun c A => by
        change ((c : ℂ) • A).adjoint = (c : ℂ) • A.adjoint
        rw [map_smulₛₗ]
        simp }
  exact L.mkContinuous 1 (fun A => by
    change ‖A.adjoint‖ ≤ 1 * ‖A‖
    simp)

private theorem term_contDiff
    (A : ∀ n : ℕ, HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (n : ℕ) : ContDiff ℝ 1 (hartreeTerm A n) := by
  have haAll : AnalyticOnNhd ℝ (hartreeTerm A n) univ := by
    intro u _
    have hj : AnalyticAt ℂ (insertFirst (H := H) n) u :=
      ((tensorMultilinear (H := H) (n + 1)).curryLeft.flipMultilinear.analyticAt).comp
        (analyticAt_pi_iff.mpr fun _ => analyticAt_id)
    have hp : AnalyticAt ℂ (fun v : H => htpow (𝕜 := ℂ) (n + 1) v) u := by
      change AnalyticAt ℂ (fun v : H => tensorMultilinear (n + 1) (fun _ => v)) u
      exact ((tensorMultilinear (n + 1)).analyticAt).comp (analyticAt_pi_iff.mpr fun _ => analyticAt_id)
    let U := HilbertTensorPower ℂ H (n + 1)
    have ha : AnalyticAt ℝ (fun v : H => (insertFirst n v).adjoint) u :=
      ((realAdjoint (U := H) (V := U)).analyticAt (insertFirst n u)).comp hj.restrictScalars
    let eval : (U →L[ℂ] H) × U → H := fun q => q.1 q.2
    have heval (q : (U →L[ℂ] H) × U) : AnalyticAt ℂ eval q :=
      (ContinuousLinearMap.apply ℂ H (E := U)).flip.analyticAt_bilinear q
    have hA := ((A n).analyticAt _).comp hp
    have hbase : AnalyticAt ℝ (fun v : H => (insertFirst n v).adjoint (A n (htpow (𝕜 := ℂ) (n + 1) v))) u :=
      ((heval _).restrictScalars).comp (ha.prod (hA.restrictScalars))
    have hm (v : H) : AnalyticAt ℝ (fun z : H => ((n + 1 : ℕ) : ℂ) • z) v :=
      ((analyticAt_const : AnalyticAt ℂ (fun _ : H => ((n + 1 : ℕ) : ℂ)) v).smul
        analyticAt_id).restrictScalars
    have he : hartreeTerm A n = fun x : H => ((n + 1 : ℕ) : ℂ) •
        (insertFirst n x).adjoint (A n (htpow (𝕜 := ℂ) (n + 1) x)) := by
      funext x
      unfold hartreeTerm hartreeContraction
      simp only [ContinuousLinearMap.comp_apply, insertFirst_self]
    rw [he]
    exact (hm _).comp hbase
  exact haAll.contDiff

/-- The derivative of the source field is continuous in operator norm
throughout one common ball containing the closed unit ball. -/
theorem source_continuous_derivative
    (A : ∀ n : ℕ, SymSector ℂ H (n + 1) →L[ℂ] SymSector ℂ H (n + 1))
    {a : ℝ} (ha : 0 < a)
    (hs : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n))) :
    ∃ S > (1 : ℝ), ContDiffOn ℝ 1 (sourceHartreeField A) (ball 0 S) ∧
      ContinuousOn (fderiv ℝ (sourceHartreeField A)) (ball 0 S) := by
  let B := fun n => extendSymKernel (A n)
  obtain ⟨S, hS, hv, hd⟩ := exponential_rank_margin ha
    (fun n => norm_nonneg (B n)) (source_rank_summable A hs)
  have hS₀ := zero_lt_one.trans hS
  let U := ball (0 : H) S
  let m : ℕ → ℝ := fun n => (n + 1 : ℕ) * (2 * n + 1 : ℕ) * ‖B n‖ * S ^ (2 * n)
  have hb (n : ℕ) (x : H) (hx : x ∈ U) : ‖fderiv ℝ (hartreeTerm B n) x‖ ≤ m n := by
    let K : ℝ≥0 := ⟨m n, by dsimp [m]; positivity⟩
    have hl : LipschitzOnWith K (hartreeTerm B n) (closedBall 0 S) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      rw [dist_eq_norm, dist_eq_norm]
      change ‖hartreeTerm B n x - hartreeTerm B n y‖ ≤ m n * ‖x-y‖
      exact hartreeTerm_lipschitz B n hS₀.le
        (mem_closedBall_zero_iff.mp hx) (mem_closedBall_zero_iff.mp hy)
    exact norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hl
  have h0 : (0 : H) ∈ U := mem_ball_self hS₀
  have hseries : Summable (fun n => hartreeTerm B n (0 : H)) :=
    hartree_series_summable B hS₀.le hv (by simpa using hS₀.le)
  have hjet (x : H) (hx : x ∈ U) : HasFDerivAt (fun u => ∑' n, hartreeTerm B n u)
      (∑' n, fderiv ℝ (hartreeTerm B n) x) x :=
    hasFDerivAt_tsum_of_isPreconnected hd isOpen_ball (convex_ball _ _).isPreconnected
      (fun n x _ => ((term_contDiff B n).differentiable one_ne_zero x).hasFDerivAt)
      hb h0 hseries hx
  have hdc : ContinuousOn (fun x => ∑' n, fderiv ℝ (hartreeTerm B n) x) U :=
    continuousOn_tsum (fun n => ((term_contDiff B n).continuous_fderiv one_ne_zero).continuousOn)
      hd hb
  have hsmooth : ContDiffOn ℝ 1 (fun u => ∑' n, hartreeTerm B n u) U := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    exact ⟨fun x hx => (hjet x hx).differentiableAt.differentiableWithinAt, by simp,
      contDiffOn_zero.mpr (hdc.congr fun x hx => (hjet x hx).fderiv)⟩
  have hm : ContDiff ℝ 1 (fun v : H => (-Complex.I) • v) :=
    (((-Complex.I) • ContinuousLinearMap.id ℂ H).restrictScalars ℝ).contDiff
  have hfinal : ContDiffOn ℝ 1 (sourceHartreeField A) U :=
    hm.comp_contDiffOn hsmooth
  exact ⟨S, hS, hfinal, hfinal.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl⟩

end QuantumNLS.Ext025GP04HartreeR30m
#print axioms QuantumNLS.Ext025GP04HartreeR30m.source_continuous_derivative
