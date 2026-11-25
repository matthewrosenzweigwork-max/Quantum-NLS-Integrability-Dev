import NlsGge.GK38.ActionRealScalar
import NlsGge.GK38.Lib.InterpolationHilbertOp
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Neighborhoods

/- Local finite-gap density on a genuine chart-ball preimage. The literal
finite-open-actual-gap predicate is used directly; this proof needs no
BirkhoffTop object, Sobolev regularity or physical Fourier truncations. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gk19_actual_finite_gap_dense_on_chart_ball38
    (Phi : PhysicalL2 → Lib.L2Z)
    (hAction : ∀ (u : PhysicalL2) (n : ℤ),
      ‖Phi u n‖ ^ 2 = actualGapActionAllE02_38 u n)
    (e : OpenPartialHomeomorph PhysicalL2 Lib.L2Z)
    (hePhi : ⇑e = Phi)
    (δ : ℝ) (hδ : 0 < δ)
    (hball : Metric.ball (0 : Lib.L2Z) δ ⊆ e.target) :
    IsOpen (e.source ∩ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ) ∧
      (e.source ∩ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ).Nonempty ∧
      (e.source ∩ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ) ⊆
        closure ((e.source ∩ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ) ∩
          {u : PhysicalL2 |
          {n : ℤ | actualGapLowerAllE02_38 u n <
            actualGapUpperAllE02_38 u n}.Finite}) := by
  classical
  let U : Set PhysicalL2 := e.source ∩ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ
  have hopen : IsOpen U := by
    dsimp [U]
    simpa only [← hePhi] using e.isOpen_inter_preimage Metric.isOpen_ball
  have hzeroBall : (0 : Lib.L2Z) ∈ Metric.ball (0 : Lib.L2Z) δ := by
    simp [Metric.mem_ball, hδ]
  have hzeroTarget : (0 : Lib.L2Z) ∈ e.target := hball hzeroBall
  refine ⟨hopen, ?_, ?_⟩
  · refine ⟨e.symm 0, e.map_target hzeroTarget, ?_⟩
    change Phi (e.symm 0) ∈ Metric.ball (0 : Lib.L2Z) δ
    rw [← hePhi, e.right_inv hzeroTarget]
    exact hzeroBall
  · intro u hu
    rcases hu with ⟨huSource, huBall⟩
    have huTarget : Phi u ∈ e.target := hball huBall
    have heu : e u = Phi u := congrFun hePhi u
    have hsymu : e.symm (Phi u) = u := by
      rw [← heu]
      exact e.left_inv huSource
    let z : Lib.L2Z := Phi u
    have hzBall : z ∈ Metric.ball (0 : Lib.L2Z) δ := huBall
    have hzNorm : ‖z‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzBall
    have hsum : HasSum (fun i : ℤ => lp.single (E := fun _ : ℤ => ℂ) (2 : ENNReal) i (z i : ℂ)) z :=
      lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ENNReal)) ENNReal.ofNat_ne_top z
    let q : Finset ℤ → Lib.L2Z := fun s =>
      ∑ i ∈ s, lp.single (E := fun _ : ℤ => ℂ) (2 : ENNReal) i (z i : ℂ)
    have hpartial : Tendsto q atTop (𝓝 z) := by
      change Tendsto
        (fun s : Finset ℤ =>
          ∑ i ∈ s, lp.single (E := fun _ : ℤ => ℂ) (2 : ENNReal) i (z i : ℂ))
        atTop (𝓝 z) at hsum
      simpa only [q] using hsum
    have hcoord (s : Finset ℤ) (n : ℤ) : q s n = if n ∈ s then z n else 0 := by
      simp only [q, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
        Finset.sum_pi_single]
    have hqnorm (s : Finset ℤ) : ‖q s‖ ≤ ‖z‖ := by
      apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
      intro n
      rw [hcoord]
      by_cases hn : n ∈ s <;> simp [hn]
    have hqBall (s : Finset ℤ) : q s ∈ Metric.ball (0 : Lib.L2Z) δ := by
      apply Metric.mem_ball.mpr
      simpa [dist_eq_norm] using (hqnorm s).trans_lt hzNorm
    have hqTarget (s : Finset ℤ) : q s ∈ e.target := hball (hqBall s)
    have hfinite (s : Finset ℤ) :
        {n : ℤ | actualGapLowerAllE02_38 (e.symm (q s)) n <
          actualGapUpperAllE02_38 (e.symm (q s)) n}.Finite := by
      apply s.finite_toSet.subset
      intro n hn
      change n ∈ s
      change actualGapLowerAllE02_38 (e.symm (q s)) n <
        actualGapUpperAllE02_38 (e.symm (q s)) n at hn
      by_contra hns
      have hcoordZero : q s n = 0 := by
        rw [hcoord]
        simp [hns]
      have hPhiZero : Phi (e.symm (q s)) n = 0 := by
        rw [← hePhi, e.right_inv (hqTarget s)]
        exact hcoordZero
      have hActionZero : actualGapActionAllE02_38 (e.symm (q s)) n = 0 := by
        rw [← hAction (e.symm (q s)) n, hPhiZero]
        simp
      have hclosed := (actionZeroIffClosed38 (e.symm (q s)) n).mp hActionZero
      rw [hclosed] at hn
      exact (lt_irrefl _ hn)
    have happrox (s : Finset ℤ) :
        e.symm (q s) ∈ U ∩
          {v : PhysicalL2 |
            {n : ℤ | actualGapLowerAllE02_38 v n <
              actualGapUpperAllE02_38 v n}.Finite} := by
      refine ⟨?_, hfinite s⟩
      refine ⟨e.map_target (hqTarget s), ?_⟩
      change Phi (e.symm (q s)) ∈ Metric.ball (0 : Lib.L2Z) δ
      rw [← hePhi, e.right_inv (hqTarget s)]
      exact hqBall s
    have hlim : Tendsto (fun s : Finset ℤ => e.symm (q s)) atTop (𝓝 u) := by
      simpa only [Function.comp_def, z, hsymu] using
        (e.continuousAt_symm huTarget).tendsto.comp hpartial
    exact mem_closure_of_tendsto hlim (Eventually.of_forall happrox)

end
end NlsGge.GK38
