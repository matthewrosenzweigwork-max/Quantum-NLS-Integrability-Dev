import NlsGge.Atomic.G1.G1104Host
import NlsGge.Atomic.G1.G1103Spec
import NlsGge.Atomic.G1.G1103Circ
import NlsGge.Atomic.LIB.LIB015
import NlsGge.Atomic.LIB.LIB041
import NlsGge.Atomic.LIB.LIB042
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# G1-104 M7: finite dimensionality of the root space

Support module `G1104FD` for G1-104, clause 1, first conjunct (G1104_STOP.md, item M7).
For every `φ : SourcePairL2`, boundary condition `bc` and `z : ℂ` the root space of the actual
realization `zsRealization φ bc` at `z` is finite dimensional.

Proof (circle Riesz route of G1-103; no `PositivelyOrientedSimple` input):
* `exists_isolating_radius`: the non-resolvent points in a bounded disc are finite
  (landed `G1103Spec.zs_spectrum_finite_in_ball`), hence a small circle `‖μ - z‖ = r` lies in the
  resolvent set.
* `resolventFamily_chain`: for a Jordan chain `w` with `w N = 0`,
  `R(μ) w_j = ∑_{k < N-j} (μ-z)^{-(k+1)} w_{j+k}` (downward induction).
* `circleRieszProjection_fix_rootVector`: since `∮ (μ-z)^{-(k+1)} dμ = 2πi δ_{k0}`, the actual
  Riesz projection `P = zsRieszProjection φ bc (circleLoop z r)` fixes every root vector.
* `P` is compact (landed `zsRieszProjection_isCompact`), the fixed space `ker (P - 1)` of a compact
  operator is finite dimensional (`fixedSpace_finiteDimensional`), and the root space lies in it.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology

namespace NlsGge.Atomic.G1104FD
open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB038 NlsGge.Atomic.LIB040
open NlsGge.Atomic.LIB041 NlsGge.Atomic.LIB042
open NlsGge.GK38.Lib.SlitContours
open NlsGge.GKDefinitionDesign
open NlsGge.Pilot NlsGge.GK38
open NlsGge.Atomic.G1103Circ

/-- The fixed space of a compact operator (here `ker (P - 1)`) is finite dimensional. -/
theorem fixedSpace_finiteDimensional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : E →L[ℂ] E) (hc : IsCompactOperator P) :
    FiniteDimensional ℂ (LinearMap.ker ((P - 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  have hcl : IsClosed ((LinearMap.ker ((P - 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) : Submodule ℂ E) : Set E) :=
    ContinuousLinearMap.isClosed_ker _
  have hp : ∀ x ∈ LinearMap.ker ((P - 1 : E →L[ℂ] E) : E →ₗ[ℂ] E), P.toLinearMap x ∈
      LinearMap.ker ((P - 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    intro x hx
    have hx' : P x = x := by
      have := LinearMap.mem_ker.1 hx
      simpa [sub_eq_zero] using this
    show ((P - 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) (P x) = 0
    rw [hx']
    simpa [sub_eq_zero] using hx'
  have hr := hc.restrict (f := P.toLinearMap) hp hcl
  have he : (P.toLinearMap.restrict hp :
      LinearMap.ker ((P - 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) → LinearMap.ker ((P - 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)) = id := by
    funext x
    have hx : P (x : E) = x := by
      have := LinearMap.mem_ker.1 x.property
      simpa [sub_eq_zero] using this
    exact Subtype.ext hx
  rw [he] at hr
  exact FiniteDimensional.of_isCompactOperator_id hr

lemma ne_center_of_mem_sphere {z μ : ℂ} {r : ℝ} (hr : 0 < r) (hμ : μ ∈ sphere z r) : μ ≠ z := by
  intro h
  have := mem_sphere_iff_norm.1 hμ
  rw [h, sub_self, norm_zero] at this
  exact hr.ne this

lemma continuousOn_pow_inv_sphere (z : ℂ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ContinuousOn (fun μ : ℂ => ((μ - z) ^ (k + 1))⁻¹) (sphere z r) := by
  refine ContinuousOn.inv₀ (by fun_prop) ?_
  intro μ hμ
  exact pow_ne_zero _ (sub_ne_zero.2 (ne_center_of_mem_sphere hr hμ))

/-- Jordan chain: `R(μ) w_j = ∑_{k<d} ((μ - z)^{k+1})⁻¹ • w_{j+k}` when `j + d = N`, `w N = 0`. -/
theorem resolventFamily_chain (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) {μ z : ℂ}
    (hμ : HasBoundedResolvent A μ) (hne : μ ≠ z) (N : ℕ) (w : ℕ → SourcePairL2) (hN : w N = 0)
    (hw : ∀ j : ℕ, j < N → ∃ hj : w j ∈ A.domain, A ⟨w j, hj⟩ - z • w j = w (j + 1)) :
    ∀ d j : ℕ, j + d = N →
      resolventFamily A μ (w j) =
        ∑ k ∈ Finset.range d, ((μ - z) ^ (k + 1))⁻¹ • w (j + k) := by
  have hR : ∀ u : A.domain, resolventFamily A μ (μ • (u : SourcePairL2) - A u) = u := by
    intro u
    rw [resolventFamily_eq A μ hμ]
    exact hμ.choose_spec.2 u
  have hμz : μ - z ≠ 0 := sub_ne_zero.2 hne
  intro d
  induction d with
  | zero =>
    intro j hj
    have : j = N := by omega
    subst this
    simp [hN]
  | succ d ih =>
    intro j hj
    have hjN : j < N := by omega
    obtain ⟨hjd, hact⟩ := hw j hjN
    have key : resolventFamily A μ ((μ - z) • w j - w (j + 1)) = w j := by
      have h1 : μ • (⟨w j, hjd⟩ : A.domain).1 - A ⟨w j, hjd⟩ = (μ - z) • w j - w (j + 1) := by
        rw [← hact]
        simp only
        module
      have := hR ⟨w j, hjd⟩
      rw [h1] at this
      exact this
    rw [map_sub, map_smul] at key
    have hIH := ih (j + 1) (by omega)
    have h2 : resolventFamily A μ (w j) = (μ - z)⁻¹ • (w j + resolventFamily A μ (w (j + 1))) := by
      rw [← sub_eq_iff_eq_add.1 key, inv_smul_smul₀ hμz]
    rw [h2, hIH, Finset.sum_range_succ', smul_add, Finset.smul_sum, add_comm]
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_smul, show j + 1 + k = j + (k + 1) by ring]
      congr 1
      rw [pow_succ _ (k + 1), mul_inv, mul_comm]
    · simp

/-- The circle integral values `∮ ((μ - z)^{k+1})⁻¹ dμ = 2πi δ_{k0}`, on the circle loop. -/
theorem curveIntegral_circle_pow_inv (z : ℂ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    curveIntegral (complexForm (fun μ : ℂ => ((μ - z) ^ (k + 1))⁻¹)) (circleLoop z r) =
      if k = 0 then 2 * (Real.pi : ℂ) * Complex.I else 0 := by
  have hcont := continuousOn_pow_inv_sphere z hr k
  rw [curveIntegral_circleLoop _ z r hr hcont]
  by_cases hk : k = 0
  · subst hk
    simp only [zero_add, pow_one, ite_true]
    exact circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hr)
  · simp only [hk, ite_false]
    have : (fun μ : ℂ => ((μ - z) ^ (k + 1))⁻¹) = fun μ : ℂ => (μ - z) ^ (-((k : ℤ) + 1)) := by
      funext μ
      rw [zpow_neg, show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    rw [this]
    refine circleIntegral.integral_sub_zpow_of_ne ?_ z z r
    omega

/-- The actual circle Riesz projection fixes every root vector of the realization. -/
theorem circleRieszProjection_fix_rootVector (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hres : ∀ μ : ℂ, ‖μ - z‖ = r → HasBoundedResolvent (zsRealization φ bc) μ)
    {v : SourcePairL2} (hv : rootVector (zsRealization φ bc) z v) :
    zsRieszProjection φ bc (circleLoop z r) v = v := by
  obtain ⟨N, w, h0, hN, hw⟩ := hv
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have : v = 0 := by rw [← h0, hN]
    subst this
    simp
  have hγ : NlsGge.Atomic.LIB042.PiecewiseC1 (circleLoop z r) :=
    NlsGge.Atomic.LIB042.PiecewiseC1.ofC1 _ (circle_contDiffOn z r)
  have hmem : ∀ t, circleLoop z r t ∈ sphere z r := fun t => circleLoop_mem_sphere z hr.le t
  have hres' : ∀ t, HasBoundedResolvent (zsRealization φ bc) (circleLoop z r t) :=
    fun t => hres _ (by simpa [mem_sphere_iff_norm] using hmem t)
  obtain ⟨hi, hP⟩ := zsRieszProjection_parameterIntegral φ bc hγ hres'
  rw [hP]
  have hcomm := (ContinuousLinearMap.apply ℂ SourcePairL2 v).intervalIntegral_comp_comm hi
  simp only [ContinuousLinearMap.apply_apply, smul_apply] at hcomm
  rw [smul_apply, ← hcomm]
  -- pointwise expansion of the integrand
  have hform : ∀ k : ℕ, ContinuousOn
      (complexForm (fun μ : ℂ => ((μ - z) ^ (k + 1))⁻¹)) (sphere z r) := by
    intro k
    have hc := continuousOn_pow_inv_sphere z hr k
    unfold complexForm
    exact ((ContinuousLinearMap.mul ℂ ℂ).continuous).comp_continuousOn hc
  have hint : ∀ k : ℕ, IntervalIntegrable
      (curveIntegralFun (complexForm (fun μ : ℂ => ((μ - z) ^ (k + 1))⁻¹)) (circleLoop z r))
      volume 0 1 := fun k =>
    (hform k).curveIntegrable_of_contDiffOn (circle_contDiffOn z r) hmem
  have hpt : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      derivWithin (circleLoop z r).extend (Icc 0 1) t •
        zsResolventFamily φ bc ((circleLoop z r).extend t) v =
      ∑ k ∈ Finset.range N,
        curveIntegralFun (complexForm (fun μ : ℂ => ((μ - z) ^ (k + 1))⁻¹)) (circleLoop z r) t •
          w k := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hext : (circleLoop z r).extend t = circleLoop z r ⟨t, ht⟩ :=
      Path.extend_extends' _ ⟨t, ht⟩
    have hμ : HasBoundedResolvent (zsRealization φ bc) ((circleLoop z r).extend t) := by
      rw [hext]; exact hres' _
    have hne : (circleLoop z r).extend t ≠ z := by
      rw [hext]
      exact ne_center_of_mem_sphere hr (hmem ⟨t, ht⟩)
    have hchain := resolventFamily_chain (zsRealization φ bc) hμ hne N w hN hw N 0 (by omega)
    rw [← h0]
    change derivWithin (circleLoop z r).extend (Icc 0 1) t •
      resolventFamily (zsRealization φ bc) ((circleLoop z r).extend t) (w 0) = _
    rw [hchain, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [curveIntegralFun_def]
    simp only [complexForm, ContinuousLinearMap.mul_apply', zero_add, smul_smul]
    rw [mul_comm]
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_finsetSum (fun k _ => ⟨(hint k).1.smul_const (w k), (hint k).2.smul_const (w k)⟩)]
  have hk : ∀ k ∈ Finset.range N,
      ∫ t in (0 : ℝ)..1,
        curveIntegralFun (complexForm (fun μ : ℂ => ((μ - z) ^ (k + 1))⁻¹)) (circleLoop z r) t •
          w k = (if k = 0 then 2 * (Real.pi : ℂ) * Complex.I else 0) • w k := by
    intro k _
    rw [intervalIntegral.integral_smul_const, ← curveIntegral_def,
      curveIntegral_circle_pow_inv z hr k]
  rw [Finset.sum_congr rfl hk]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.succ_ne_zero, ite_false, zero_smul, Finset.sum_const_zero, zero_add, ite_true, h0]
  rw [smul_smul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero]), one_smul]

/-- Some circle `‖μ - z‖ = r` lies in the resolvent set. -/
theorem exists_isolating_radius (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ μ : ℂ, ‖μ - z‖ = r → HasBoundedResolvent (zsRealization φ bc) μ := by
  obtain ⟨z₀, hz₀⟩ := zs_complex_resolvent_nonempty φ bc
  have hfin := NlsGge.Atomic.G1103Spec.zs_spectrum_finite_in_ball φ bc hz₀ (‖z‖ + 1)
  have hfin' : ({lam : ℂ | ‖lam‖ ≤ ‖z‖ + 1 ∧ ¬ HasBoundedResolvent (zsRealization φ bc) lam} \
      {z}).Finite := hfin.sdiff
  have hopen : IsOpen (({lam : ℂ | ‖lam‖ ≤ ‖z‖ + 1 ∧
      ¬ HasBoundedResolvent (zsRealization φ bc) lam} \ {z})ᶜ) := hfin'.isClosed.isOpen_compl
  have hzmem : z ∈ ({lam : ℂ | ‖lam‖ ≤ ‖z‖ + 1 ∧
      ¬ HasBoundedResolvent (zsRealization φ bc) lam} \ {z})ᶜ := by simp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen z hzmem
  have hpos : 0 < min ε 1 / 2 := by positivity
  refine ⟨min ε 1 / 2, hpos, fun μ hμ => ?_⟩
  by_contra hnot
  have hμz : μ ≠ z := by
    intro h
    rw [h, sub_self, norm_zero] at hμ
    exact hpos.ne hμ
  have hdist : dist μ z < ε := by
    rw [dist_eq_norm, hμ]
    have := min_le_left ε 1
    linarith
  apply hball hdist
  refine ⟨⟨?_, hnot⟩, hμz⟩
  have h1 : ‖μ‖ ≤ ‖μ - z‖ + ‖z‖ := by
    calc ‖μ‖ = ‖(μ - z) + z‖ := by ring_nf
      _ ≤ ‖μ - z‖ + ‖z‖ := norm_add_le _ _
  have := min_le_right ε 1
  rw [hμ] at h1
  linarith

/-- **G1-104 M7.** The root space of the realization `zsRealization φ bc` at `z` is finite
dimensional (all `φ : SourcePairL2`, all boundary conditions, all `z : ℂ`). -/
theorem rootSpace_finiteDimensional (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ) :
    FiniteDimensional ℂ (rootSpace (zsRealization φ bc) z) := by
  obtain ⟨r, hr, hres⟩ := exists_isolating_radius φ bc z
  have hγ : NlsGge.Atomic.LIB042.PiecewiseC1 (circleLoop z r) :=
    NlsGge.Atomic.LIB042.PiecewiseC1.ofC1 _ (circle_contDiffOn z r)
  have hres' : ∀ t, HasBoundedResolvent (zsRealization φ bc) (circleLoop z r t) :=
    fun t => hres _ (by simpa [mem_sphere_iff_norm] using circleLoop_mem_sphere z hr.le t)
  have hcomp : IsCompactOperator (zsRieszProjection φ bc (circleLoop z r)) :=
    zsRieszProjection_isCompact φ bc hγ hres'
  have := fixedSpace_finiteDimensional (zsRieszProjection φ bc (circleLoop z r)) hcomp
  have hle : rootSpace (zsRealization φ bc) z ≤
      LinearMap.ker ((zsRieszProjection φ bc (circleLoop z r) - 1 :
        SourcePairL2 →L[ℂ] SourcePairL2) : SourcePairL2 →ₗ[ℂ] SourcePairL2) := by
    unfold rootSpace
    refine Submodule.span_le.2 ?_
    intro v hv
    have hfix := circleRieszProjection_fix_rootVector φ bc hr hres hv
    show v ∈ LinearMap.ker ((zsRieszProjection φ bc (circleLoop z r) - 1 :
        SourcePairL2 →L[ℂ] SourcePairL2) : SourcePairL2 →ₗ[ℂ] SourcePairL2)
    rw [LinearMap.mem_ker]
    simp [hfix]
  exact Submodule.finiteDimensional_of_le hle

/-- First conjunct of clause 1 of the G1-104 head, for `φ : PotPair`. -/
theorem rootSpace_finiteDimensional_interval (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ) :
    FiniteDimensional ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z) :=
  rootSpace_finiteDimensional _ bc z

end NlsGge.Atomic.G1104FD

end
