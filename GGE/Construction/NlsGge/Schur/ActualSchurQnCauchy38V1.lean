import NlsGge.Schur.ActualSchurCenterHolomorphic38V1
import NlsGge.Schur.ActualSchurOffDiagonalRemainder38V1
import Mathlib.Analysis.Complex.Liouville

/-!
# The Schur coordinate `q_n` and its Cauchy derivative estimate (NEW-F03.06, pair form)

Source: `paper/v2.tex` lines 1127-1129 (F:eq:qn) and 1150-1153 (proof of
F:lem:qgap, first paragraph).  On the independent complex pair space define
`q_n(p) = b_n(σ_n(p); p)` with the actual moving center.  Then

* `q_n` is complex-differentiable on the open radius-`R` balls;
* `|q_n(p) - (u₁)_n| ≤ C R^4/n^2` on the closed balls (F:eq:qCauchy, first);
* along every complex line `ζ ↦ p + ζ w`, `‖w.i‖ ≤ 1`, with `‖p.i‖ ≤ R` and
  the source threshold applied on the radius-`4R` ball, the derivative of
  `q_n - (u₁)_n` at `ζ = 0` is at most `C R^3/n^2` (Cauchy inequality on
  `|ζ| = R`; the line stays in the radius-`2R` ball).

The restriction to the real-type subspace `(u, ū)` (and hence the real-linear
operator norm on real H¹ in F:eq:qCauchy) is NOT done here: it needs the
concrete conjugation on the carrier.  `q_n` is an auxiliary coordinate, not a
Birkhoff coordinate.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- `q_n(p) = b_n(σ_n(p); p)` on the independent complex pair space. -/
def actualSchurQn38 (R : ℝ) (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) : ℂ :=
  actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
    (actualSchurCenter38 R n p, p)

/-- The constant of F:eq:brem. -/
def actualSchurBremConstant38 : ℝ :=
  2 * freeResolventSchurUniformConstant ^ 2 *
    freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant

theorem actualSchurQn38_sub_fourier_bound
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖actualSchurQn38 R n p - p.1 n‖ ≤
      actualSchurBremConstant38 * R ^ 4 / |(n : ℝ)| ^ 2 := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  obtain ⟨hσ, -⟩ := actualSchurCenter38_spec R hR n hthr p hp₁ hp₂
  have h := actualSchurOffDiagonal_sub_fourier_bound38V1 R hR n hn hlarge
    (actualSchurCenter38 R n p) p (closedBall_half_subset_spectralDisk38 n hσ) hp₁ hp₂
  rw [physicalH1ComplexCarrierToL2Actual22_fourier] at h
  unfold actualSchurQn38 actualSchurBremConstant38
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem actualSchurQn38_differentiableAt
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ < R) (hp₂ : ‖p.2‖ < R) :
    DifferentiableAt ℂ (actualSchurQn38 R n) p := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  obtain ⟨hσ, -⟩ := actualSchurCenter38_spec R hR n hthr p hp₁.le hp₂.le
  have hAn := (actualSchurCoefficientsJointAnalyticV2_31 R hR n hn hlarge).2.1
  have hmem : ((actualSchurCenter38 R n p, p) : ℂ × ActualSchurEffectiveH1PairV3_30) ∈
      {x : ℂ × ActualSchurEffectiveH1PairV3_30 |
        x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} :=
    ⟨closedBall_half_subset_spectralDisk38 n hσ, hp₁.le, hp₂.le⟩
  have hb := (hAn _ hmem).hasStrictFDerivAt.hasFDerivAt
  have hσd := (actualSchurCenter38_differentiableAt R hR n hthr p hp₁ hp₂).hasFDerivAt
  have hpair := hσd.prodMk (hasFDerivAt_id p)
  have hc := HasFDerivAt.comp (f := fun q : ActualSchurEffectiveH1PairV3_30 =>
    (actualSchurCenter38 R n q, q)) p hb hpair
  exact hc.differentiableAt

/-- Cauchy estimate along a complex line (F:eq:qCauchy, second inequality, in
independent-pair form).  The threshold is imposed at radius `4R`, as in the
source ("apply the preceding construction on a complex potential ball of
radius `4R`"). -/
theorem actualSchurQn38_line_deriv_bound
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ |(n : ℝ)|)
    (p w : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)
    (hw₁ : ‖w.1‖ ≤ 1) (hw₂ : ‖w.2‖ ≤ 1) :
    ‖deriv (fun ζ : ℂ => actualSchurQn38 (4 * R) n (p + ζ • w) -
        (p + ζ • w).1 n) 0‖ ≤
      actualSchurBremConstant38 * (4 * R) ^ 4 / |(n : ℝ)| ^ 2 / R := by
  have h4R : 1 ≤ 4 * R := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let g : ℂ → ℂ := fun ζ => actualSchurQn38 (4 * R) n (p + ζ • w) - (p + ζ • w).1 n
  have hnorm : ∀ ζ : ℂ, ‖ζ‖ ≤ R →
      ‖(p + ζ • w).1‖ ≤ 2 * R ∧ ‖(p + ζ • w).2‖ ≤ 2 * R := by
    intro ζ hζ
    constructor
    · calc ‖(p + ζ • w).1‖ = ‖p.1 + ζ • w.1‖ := rfl
        _ ≤ ‖p.1‖ + ‖ζ‖ * ‖w.1‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul]
        _ ≤ R + R * 1 := by gcongr
        _ = 2 * R := by ring
    · calc ‖(p + ζ • w).2‖ = ‖p.2 + ζ • w.2‖ := rfl
        _ ≤ ‖p.2‖ + ‖ζ‖ * ‖w.2‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul]
        _ ≤ R + R * 1 := by gcongr
        _ = 2 * R := by ring
  have hcoord : ∀ ζ : ℂ, (p + ζ • w).1 n = p.1 n + ζ * w.1 n := fun ζ => rfl
  have hdiff : ∀ ζ : ℂ, ‖ζ‖ ≤ R → DifferentiableAt ℂ g ζ := by
    intro ζ hζ
    obtain ⟨h1, h2⟩ := hnorm ζ hζ
    have hq := actualSchurQn38_differentiableAt (4 * R) h4R n hthr (p + ζ • w)
      (by linarith) (by linarith)
    have hline : DifferentiableAt ℂ (fun ξ : ℂ => p + ξ • w) ζ :=
      (differentiableAt_id.smul_const w).const_add p
    have hfirst := hq.comp ζ hline
    have hsecond : DifferentiableAt ℂ (fun ξ : ℂ => (p + ξ • w).1 n) ζ := by
      simp only [hcoord]
      exact (differentiableAt_id.mul_const _).const_add _
    exact hfirst.sub hsecond
  have hDC : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hRpos.ne']
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    exact (hdiff ζ hζ).differentiableWithinAt
  have hbound : ∀ ζ ∈ Metric.sphere (0 : ℂ) R,
      ‖g ζ‖ ≤ actualSchurBremConstant38 * (4 * R) ^ 4 / |(n : ℝ)| ^ 2 := by
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    obtain ⟨h1, h2⟩ := hnorm ζ hζ.le
    exact actualSchurQn38_sub_fourier_bound (4 * R) h4R n hthr (p + ζ • w)
      (by linarith) (by linarith)
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hDC hbound

end NlsGge.Schur
