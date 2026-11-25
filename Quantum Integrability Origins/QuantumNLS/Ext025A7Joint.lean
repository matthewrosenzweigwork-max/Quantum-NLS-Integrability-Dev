import QuantumNLS.Ext025A7Disk

/-! Joint analytic selection on LOCAL-009's quantitative inverse disks.
A selected preimage is constructed; local analytic inverses agree with it
by proved injectivity. No inverse or analytic inverse is a hypothesis. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Ext025A7

def diskInverse (κ L R : ℝ) (z t : ℂ) : ℂ := by
  classical
  exact if h : ∃ w ∈ closedBall (0 : ℂ) R, normalizedSpectral κ L z w = t then
    Classical.choose h else 0

theorem diskInverse_spec (κ L R : ℝ) {z t : ℂ}
    (h : ∃ w ∈ closedBall (0 : ℂ) R, normalizedSpectral κ L z w = t) :
    diskInverse κ L R z t ∈ closedBall (0 : ℂ) R ∧
      normalizedSpectral κ L z (diskInverse κ L R z t) = t := by
  simpa only [diskInverse, dite_eq_left h] using Classical.choose_spec h

theorem diskInverse_eq (κ L R : ℝ) {z t w : ℂ}
    (hD : spectralLinear κ L z ≠ 0)
    (hb : ∀ v ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z v - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    (hw : w ∈ closedBall (0 : ℂ) R) (he : normalizedSpectral κ L z w = t) :
    diskInverse κ L R z t = w := by
  have hs := diskInverse_spec κ L R ⟨w, hw, he⟩
  exact normalizedSpectral_injOn κ L hD hb hs.1 hw (hs.2.trans he.symm)

/-- A joint analytic inverse at any preimage inside the common source disk.
Only the source derivative estimate and its nonzero central slope on an open
spectral neighborhood are supplied. Analyticity of the literal map is proved. -/
theorem diskInverse_joint_analyticAt (κ L R : ℝ) {U : Set ℂ}
    (hU : IsOpen U)
    (hD : ∀ z ∈ U, spectralLinear κ L z ≠ 0)
    (hb : ∀ z ∈ U, ∀ v ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z v - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    {z t w : ℂ} (hz : z ∈ U) (hw : w ∈ ball (0 : ℂ) R)
    (he : normalizedSpectral κ L z w = t) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => diskInverse κ L R p.1 p.2) (z, t) := by
  let f := fun p : ℂ × ℂ => normalizedSpectral κ L p.1 p.2
  let D := fderiv ℂ f (z, w)
  let A := D.comp (ContinuousLinearMap.inl ℂ ℂ ℂ)
  let d := spectralDerivative κ L z w / spectralLinear κ L z
  have hd : d ≠ 0 := div_ne_zero
    (spectralDerivative_nonzero κ L (hD z hz) (hb z hz w (ball_subset_closedBall hw)))
    (hD z hz)
  let B := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d hd)
  have hf : AnalyticAt ℂ f (z, w) := normalizedSpectral_analyticAt κ L (hD z hz)
  have hpart : HasFDerivAt (normalizedSpectral κ L z)
      (D.comp (ContinuousLinearMap.inr ℂ ℂ ℂ)) w := by
    exact hf.differentiableAt.hasFDerivAt.comp w
      ((hasFDerivAt_const z w).prodMk (hasFDerivAt_id w))
  have hscalar : HasFDerivAt (normalizedSpectral κ L z) B.toContinuousLinearMap w := by
    convert (normalizedSpectral_hasDerivAt κ L z w).hasFDerivAt using 1
    ext
    rfl
  have hBD : B.toContinuousLinearMap = D.comp (ContinuousLinearMap.inr ℂ ℂ ℂ) :=
    hscalar.unique hpart
  have hDall : A.coprod B.toContinuousLinearMap = D := by
    rw [hBD]
    exact D.coprod_comp_inl_inr
  let T := fun p : ℂ × ℂ => (p.1, f p)
  let I := QuantumNLS.Ext025A5.triangularEquiv A B
  have hT : AnalyticAt ℂ T (z, w) := analyticAt_fst.prod hf
  have hfd : HasFDerivAt f D (z, w) := hf.differentiableAt.hasFDerivAt
  rw [← hDall] at hfd
  have hTd : HasFDerivAt T I.toContinuousLinearMap (z, w) :=
    hasFDerivAt_fst.prodMk hfd
  obtain ⟨g, hg, hbase, _, hr⟩ := QuantumNLS.Ext025A.gp03_analytic_inverse I hT hTd
  have hTbase : T (z, w) = (z, t) := Prod.ext rfl he
  rw [hTbase] at hg hbase hr
  have han : AnalyticAt ℂ (fun p => (g p).2) (z, t) := analyticAt_snd.comp hg
  have hgw : (g (z, t)).2 ∈ ball (0 : ℂ) R := by simpa [hbase] using hw
  have hnear : ∀ᶠ p in 𝓝 (z, t), (g p).2 ∈ ball (0 : ℂ) R :=
    han.continuousAt (isOpen_ball.mem_nhds hgw)
  apply han.congr
  filter_upwards [hr, hnear,
    (continuousAt_fst : ContinuousAt Prod.fst (z, t)).tendsto.eventually (hU.mem_nhds hz)]
    with p hp hpw hpz
  have hfst : (g p).1 = p.1 := by simpa only [T] using congrArg Prod.fst hp
  have hsol : normalizedSpectral κ L p.1 (g p).2 = p.2 := by
    simpa only [T, f, hfst] using congrArg Prod.snd hp
  exact (diskInverse_eq κ L R (hD p.1 hpz) (hb p.1 hpz)
    (ball_subset_closedBall hpw) hsol).symm

/-- Exact common normalized disk and joint analyticity of its selected inverse. -/
theorem local009_normalized_inverse (κ L : ℝ) {R : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hU : IsOpen U)
    (hD : ∀ z ∈ U, spectralLinear κ L z ≠ 0)
    (hb : ∀ z ∈ U, ∀ v ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z v - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4) :
    ∀ z ∈ U, ∀ t ∈ ball (0 : ℂ) (3 / 4 * R),
      diskInverse κ L R z t ∈ ball (0 : ℂ) R ∧
      normalizedSpectral κ L z (diskInverse κ L R z t) = t ∧
      (∀ v ∈ closedBall (0 : ℂ) R, normalizedSpectral κ L z v = t →
        v = diskInverse κ L R z t) ∧
      AnalyticAt ℂ (fun p : ℂ × ℂ => diskInverse κ L R p.1 p.2) (z, t) := by
  intro z hz t ht
  obtain ⟨w, hw, he, hu⟩ := normalizedSpectral_disk κ L hR (hD z hz) (hb z hz)
    (by simpa [mem_ball, dist_zero_right] using ht)
  have hg := diskInverse_eq κ L R (hD z hz) (hb z hz) (ball_subset_closedBall hw) he
  refine ⟨hg.symm ▸ hw, hg.symm ▸ he, ?_,
    diskInverse_joint_analyticAt κ L R hU hD hb hz hw he⟩
  intro v hv hv'
  exact (hu v hv hv').trans hg.symm
end QuantumNLS.Ext025A7
#print axioms QuantumNLS.Ext025A7.diskInverse
#print axioms QuantumNLS.Ext025A7.diskInverse_spec
#print axioms QuantumNLS.Ext025A7.diskInverse_eq
#print axioms QuantumNLS.Ext025A7.diskInverse_joint_analyticAt
#print axioms QuantumNLS.Ext025A7.local009_normalized_inverse
