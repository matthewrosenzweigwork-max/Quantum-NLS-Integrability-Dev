import NlsGge.Schur.ActualSchurQnCauchy38V1
import NlsGge.Schur.ActualSchurEntryDerivative38V1

/-!
# NEW-F04 assembly, part 1: chain rule for the moving center and for `q_n`

Source: `paper/v2.tex` lines 1206-1217.  For an independent complex pair `p` in
the open radius-`R` balls and any direction `h`, with `a := D(α_n)(σ_n(p), p)`
and `β := D(b_n)(σ_n(p), p)` the joint complex derivatives of the actual
coefficients,

* `(1 - a(1,0)) · Dσ_n(p)[h] = a(0,h)`   (differentiated F:eq:center),
* `Dq_n(p)[h] = β(1,0) · Dσ_n(p)[h] + β(0,h)`   (chain rule in F:eq:qn),
* `a(1,0)` and `β(1,0)` are the spectral derivatives `⟪e_i, -(G̃G) e_j⟫`.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- Joint derivative of an actual resonant coefficient at `(σ_n(p), p)`. -/
def actualSchurCoefficientJointDeriv38 (R : ℝ) (n : ℤ) (i j : Bool × Sector n)
    (p : ActualSchurEffectiveH1PairV3_30) :
    ℂ × ActualSchurEffectiveH1PairV3_30 →L[ℂ] ℂ :=
  fderiv ℂ (actualSchurCoefficientAfterDext31 n i j) (actualSchurCenter38 R n p, p)

theorem actualSchurCoefficient_hasFDerivAt_center38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (i j : Bool × Sector n)
    (p : ActualSchurEffectiveH1PairV3_30) (hp₁ : ‖p.1‖ < R) (hp₂ : ‖p.2‖ < R) :
    HasFDerivAt (actualSchurCoefficientAfterDext31 n i j)
      (actualSchurCoefficientJointDeriv38 R n i j p) (actualSchurCenter38 R n p, p) := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  obtain ⟨hσ, -⟩ := actualSchurCenter38_spec R hR n hthr p hp₁.le hp₂.le
  have hmem : ((actualSchurCenter38 R n p, p) : ℂ × ActualSchurEffectiveH1PairV3_30) ∈
      {x : ℂ × ActualSchurEffectiveH1PairV3_30 |
        x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} :=
    ⟨closedBall_half_subset_spectralDisk38 n hσ, hp₁.le, hp₂.le⟩
  have hAn : AnalyticOnNhd ℂ (actualSchurCoefficientAfterDext31 n i j)
      {x : ℂ × ActualSchurEffectiveH1PairV3_30 |
        x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} := by
    unfold actualSchurCoefficientAfterDext31
    exact (actualSchurEntryFunctional31 n i j).comp_analyticOnNhd
      (analyticOnNhd_actualSchurEffectiveOperatorAfterDextV3_30 R hR n hn hlarge)
  exact (hAn _ hmem).differentiableAt.hasFDerivAt

/-- The spectral component of the joint derivative is the checked spectral
derivative `⟪e_i, -(G̃G) e_j⟫`. -/
theorem actualSchurCoefficientJointDeriv38_spectral
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (i j : Bool × Sector n)
    (p : ActualSchurEffectiveH1PairV3_30) (hp₁ : ‖p.1‖ < R) (hp₂ : ‖p.2‖ < R)
    (hz : actualSchurCenter38 R n p ∈ spectralDisk n) :
    actualSchurCoefficientJointDeriv38 R n i j p (1, 0) =
      actualSchurEntryFunctional31 n i j
        (-(actualSchurGreenDerivativeProductV3_31 n (actualSchurCenter38 R n p) p hz)) := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  have hJ := actualSchurCoefficient_hasFDerivAt_center38 R hR n hthr i j p hp₁ hp₂
  have h1 : HasFDerivAt
      (fun w : ℂ => ((w, p) : ℂ × ActualSchurEffectiveH1PairV3_30))
      (ContinuousLinearMap.inl ℂ ℂ ActualSchurEffectiveH1PairV3_30)
      (actualSchurCenter38 R n p) :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const p _)
  have h2 := (HasFDerivAt.comp (f := fun w : ℂ => ((w, p) : ℂ × ActualSchurEffectiveH1PairV3_30))
    (actualSchurCenter38 R n p) hJ h1).hasDerivAt
  have h3 := actualSchurEntry_hasDerivAt38V1 R hR n hn hlarge i j p
    (actualSchurCenter38 R n p) hz hp₁.le hp₂.le
  have h := h2.unique h3
  simpa using h

/-- Differentiated center equation: `(1 - a(1,0)) Dσ[h] = a(0,h)`. -/
theorem actualSchurCenter38_fderiv_equation
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30) (hp₁ : ‖p.1‖ < R) (hp₂ : ‖p.2‖ < R)
    (h : ActualSchurEffectiveH1PairV3_30) :
    (1 - actualSchurCoefficientJointDeriv38 R n
        (true, resonantIndex n) (true, resonantIndex n) p (1, 0)) *
      fderiv ℂ (actualSchurCenter38 R n) p h =
      actualSchurCoefficientJointDeriv38 R n
        (true, resonantIndex n) (true, resonantIndex n) p (0, h) := by
  set a := actualSchurCoefficientJointDeriv38 R n
    (true, resonantIndex n) (true, resonantIndex n) p with ha
  have hσd := (actualSchurCenter38_differentiableAt R hR n hthr p hp₁ hp₂).hasFDerivAt
  set s := fderiv ℂ (actualSchurCenter38 R n) p with hs
  have hJ := actualSchurCoefficient_hasFDerivAt_center38 R hR n hthr
    (true, resonantIndex n) (true, resonantIndex n) p hp₁ hp₂
  have hpair := hσd.prodMk (hasFDerivAt_id p)
  have hcomp := HasFDerivAt.comp (f := fun q : ActualSchurEffectiveH1PairV3_30 =>
    (actualSchurCenter38 R n q, q)) p hJ hpair
  have hRHS : HasFDerivAt (fun q : ActualSchurEffectiveH1PairV3_30 =>
      spectralCenter n + actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (true, resonantIndex n) (actualSchurCenter38 R n q, q))
      (a.comp (s.prod (ContinuousLinearMap.id ℂ _))) p :=
    hcomp.const_add _
  have hq1 : ∀ᶠ q in 𝓝 p, ‖q.1‖ < R :=
    (continuous_norm.comp continuous_fst).continuousAt.eventually (gt_mem_nhds hp₁)
  have hq2 : ∀ᶠ q in 𝓝 p, ‖q.2‖ < R :=
    (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds hp₂)
  have hEq : (fun q : ActualSchurEffectiveH1PairV3_30 =>
      spectralCenter n + actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (true, resonantIndex n) (actualSchurCenter38 R n q, q))
      =ᶠ[𝓝 p] actualSchurCenter38 R n := by
    filter_upwards [hq1, hq2] with q h1 h2
    exact (actualSchurCenter38_spec R hR n hthr q h1.le h2.le).2.symm
  have hσ' := hRHS.congr_of_eventuallyEq hEq.symm
  have huniq := hσd.unique hσ'
  have happ := congrArg (fun L : ActualSchurEffectiveH1PairV3_30 →L[ℂ] ℂ => L h) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply] at happ
  have hsplit : ((s h, h) : ℂ × ActualSchurEffectiveH1PairV3_30) =
      s h • ((1 : ℂ), (0 : ActualSchurEffectiveH1PairV3_30)) + (0, h) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at happ
  linear_combination happ

/-- Chain rule for `q_n = b_n(σ_n(p), p)`. -/
theorem actualSchurQn38_fderiv_chain
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30) (hp₁ : ‖p.1‖ < R) (hp₂ : ‖p.2‖ < R)
    (h : ActualSchurEffectiveH1PairV3_30) :
    fderiv ℂ (actualSchurQn38 R n) p h =
      actualSchurCoefficientJointDeriv38 R n
          (true, resonantIndex n) (false, resonantIndex n) p (1, 0) *
        fderiv ℂ (actualSchurCenter38 R n) p h +
      actualSchurCoefficientJointDeriv38 R n
          (true, resonantIndex n) (false, resonantIndex n) p (0, h) := by
  set β := actualSchurCoefficientJointDeriv38 R n
    (true, resonantIndex n) (false, resonantIndex n) p with hβ
  have hσd := (actualSchurCenter38_differentiableAt R hR n hthr p hp₁ hp₂).hasFDerivAt
  set s := fderiv ℂ (actualSchurCenter38 R n) p with hs
  have hJ := actualSchurCoefficient_hasFDerivAt_center38 R hR n hthr
    (true, resonantIndex n) (false, resonantIndex n) p hp₁ hp₂
  have hpair := hσd.prodMk (hasFDerivAt_id p)
  have hcomp := HasFDerivAt.comp (f := fun q : ActualSchurEffectiveH1PairV3_30 =>
    (actualSchurCenter38 R n q, q)) p hJ hpair
  have hq : HasFDerivAt (actualSchurQn38 R n) (β.comp (s.prod (ContinuousLinearMap.id ℂ _))) p :=
    hcomp
  rw [hq.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  have hsplit : ((s h, h) : ℂ × ActualSchurEffectiveH1PairV3_30) =
      s h • ((1 : ℂ), (0 : ActualSchurEffectiveH1PairV3_30)) + (0, h) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul, mul_comm]

end NlsGge.Schur
