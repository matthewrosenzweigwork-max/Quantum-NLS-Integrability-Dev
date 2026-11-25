import NlsGge.Schur.ActualSourceSchurEigenBridge38V1
import NlsGge.Schur.ActualSchurRealTypeEigenvalues38V1
import NlsGge.Schur.ActualSourceParityShift38V1
import NlsGge.Spectral.ActualOppositeParityExclusionE02_38
import NlsGge.Schur.ActualSchurRealTypeCenter38V1

/-!
# F03.07 for the actual source operator (B4): local eigenvalue set near `nπ`

Operator: `actualSourcePerturbedDiracPMapAfterAE n U Ū`, the actual REFLECTED Dirac
operator `𝖫_U = diag(-i∂, i∂) + [[0,U],[Ū,0]]` of F:eq:Dirac (paper line 1003) on the
parity sector of `n` (boundary condition `f(1) = (-1)^n f(0)`), with
`U = physicalH1ComplexCarrierToL2Actual22 w` an H¹ potential and `Ū = star U`.
This is exactly the convention of F:lem:qgap ("`g_n` denotes the gap near `nπ`
for F:eq:Dirac").  The main theorem `actualSourceSectorEigenvalues_realType38` is
about `𝖫_U` only.  The companion `actualSchurRoots_halfTrace_realType38` translates it,
through the existing Floquet link (E02, which rests on `𝖫_u = -L_{-u}` and phase
invariance), into a statement about the half trace of the original `L_U` at `-z`.

For `‖w‖_{H¹} ≤ R` and `|n| ≥ K R^3`: the eigenvalues of this sector operator in
`|z - nπ| ≤ 1` are exactly the two real Schur roots `λ⁺` (zero of `F - |b_n|`) and
`λ⁻` (zero of `F + |b_n|`) in `[nπ - 1/2, nπ + 1/2]`, which are unique there.
Algebraic multiplicity, the opposite-parity sector and global labels are not
covered here.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur
open TransportBridgeV4

theorem actualSourceSectorEigenvalues_realType38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    ∃ lp lm : ℝ,
      (lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0 ∧
        ∀ y : ℝ, y ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) →
          actualSchurShiftedF38 n (w, actualH1Conj38 w) y -
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) y = 0 → y = lp) ∧
      (lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0 ∧
        ∀ y : ℝ, y ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) →
          actualSchurShiftedF38 n (w, actualH1Conj38 w) y +
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) y = 0 → y = lm) ∧
      ∀ z : ℂ, z ∈ spectralDisk n →
        ((∃ Y : recoveredActualSourceFreeWeightedDomain n, Y.val ≠ 0 ∧
            actualSourcePerturbedDiracPMapAfterAE n
              (physicalH1ComplexCarrierToL2Actual22 w)
              (star (physicalH1ComplexCarrierToL2Actual22 w)) Y = z • Y.val) ↔
          (z = (lp : ℂ) ∨ z = (lm : ℂ))) := by
  obtain ⟨lp, lm, hp, hm, hz⟩ :=
    actualSchurCoordinateEigenvalues_realType38 R hR n hthr w hw
  refine ⟨lp, lm, hp, hm, fun z hzD => ?_⟩
  have h := actualSourcePerturbedDirac_eigenvalue_iff_schurCoordinate38V1 n
    (w, actualH1Conj38 w) z
  change (∃ Y : recoveredActualSourceFreeWeightedDomain n, Y.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE n (physicalH1ComplexCarrierToL2Actual22 w)
        (physicalH1ComplexCarrierToL2Actual22 (actualH1Conj38 w)) Y = z • Y.val) ↔ _ at h
  rw [physicalH1_conj38] at h
  rw [h]
  exact hz z hzD

/-- Sign relation between the reflected operator of F:eq:Dirac and the original
ZS operator, proved (not assumed): for the same roots `λ^±`, a point `z` of the
disk `|z - nπ| ≤ 1` is one of `λ⁺, λ⁻` iff the ACTUAL period-one half trace of the
original operator `L_U` satisfies `Δh(U, -z) = (-1)^n`.  Thus the Schur roots of
`𝖫_U` near `nπ` are the negatives of the sector-`n` Floquet points of `L_U` near
`-nπ` (`𝖫_u = -L_{-u}`). -/
theorem actualSchurRoots_halfTrace_realType38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    ∃ lp lm : ℝ,
      (lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0) ∧
      (lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0) ∧
      ∀ z : ℂ, z ∈ spectralDisk n →
        (NlsGge.SpectralFoundations.actualPhysicalUnitHalfTrace32
            (physicalH1ComplexCarrierToL2Actual22 w) (-z) = spectralSign n ↔
          (z = (lp : ℂ) ∨ z = (lm : ℂ))) := by
  obtain ⟨lp, lm, hp, hm, hz⟩ := actualSourceSectorEigenvalues_realType38 R hR n hthr w hw
  refine ⟨lp, lm, ⟨hp.1, hp.2.1⟩, ⟨hm.1, hm.2.1⟩, fun z hzD => ?_⟩
  rw [← NlsGge.SpectralFoundations.actualSourceEigenvalue_iff_halfTrace_E02_38]
  exact hz z hzD

/-- Ordering (round-2 review (b)): any real zeros `λ⁺` of `F - |b_n|` and `λ⁻` of
`F + |b_n|` in the window satisfy `λ⁻ ≤ σ_n ≤ λ⁺` with the real moving center
`σ_n = Re σ_n` (real-type), hence `λ⁻ ≤ λ⁺`. -/
theorem actualSourceSectorRoots_ordered_realType38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) (lp lm : ℝ)
    (hlpI : lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlp : actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0)
    (hlmI : lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlm : actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0) :
    lm ≤ (actualSchurCenter38 R n (w, actualH1Conj38 w)).re ∧
      (actualSchurCenter38 R n (w, actualH1Conj38 w)).re ≤ lp ∧ lm ≤ lp := by
  obtain ⟨hKge, -, -, -⟩ := actualSchurShiftedRootsConstant38_ge
  have hthrC : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right hKge (by positivity)) hthr
  let p : ActualSchurEffectiveH1PairV3_30 := (w, actualH1Conj38 w)
  have hp₁ : ‖p.1‖ ≤ R := hw
  have hp₂ : ‖p.2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]; exact hw
  obtain ⟨hσball, hσfix⟩ := actualSchurCenter38_spec R hR n hthrC p hp₁ hp₂
  have him := actualSchurCenter38_real_realType R hR n hthrC w hw
  set σ := actualSchurCenter38 R n p with hσdef
  have hσreal : ((σ.re : ℝ) : ℂ) = σ := by
    apply Complex.ext <;> simp [him]
  have hσI : σ.re ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hσball
    have h := le_trans (Complex.abs_re_le_norm _) hσball
    rw [Complex.sub_re, abs_le] at h
    have hc : (spectralCenter n).re = Real.pi * n := by
      simp [spectralCenter, Complex.mul_re]; ring
    rw [hc] at h
    obtain ⟨h1, h2⟩ := h
    constructor <;> linarith
  have hfix' : ((σ.re : ℝ) : ℂ) = spectralCenter n + actualSchurAlpha38 n p (σ.re : ℂ) := by
    rw [hσreal]; exact hσfix
  have h := actualSchurGapComparison38V1 R hR n hthrC p hp₁ hp₂ σ.re lm lp hσI hlmI hlpI
    hfix' hlp hlm
  exact ⟨h.1, h.2.1, le_trans h.1 h.2.1⟩

end NlsGge.Schur
