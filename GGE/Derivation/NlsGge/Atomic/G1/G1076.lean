import Mathlib
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PairPotential
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.PoissonMixedRealNormingData
import NlsGge.GK38.PoissonMixedRealKappaAnalytic

/-! G1-076 COMMAND01 pre-approval proof (proof development, AUTHOR; not self-reviewed).  Statement = G1-076_COMMAND01 verbatim.
Assembled from production: `PoissonMixed38.signedNorming_positive38` (0 < (-1)^n u(mu_n) via the trace polynomial u^2 + 1 = Delta u and the
sign of Delta at a Dirichlet root), `PoissonMixed38.normingFactor_real_im38` (u real at a real argument), `PoissonMixed38.analyticOnNhd_realKappa38`
and the label identification `muSeq_eq_gkMu38`. -/

set_option autoImplicit false

namespace NlsGge.Atomic.G1076S1

open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.Pilot NlsGge.SpectralFoundations Set

theorem real_of (φ : PotPair) (h : φ.2 = star φ.1) : φ = realSlice φ.1 := by
  rw [realSlice_apply]; exact Prod.ext rfl h

theorem sign_re_im (u : PhysicalL2) (n : ℤ) :
    ((-1 : ℂ) ^ n * normingFactor (realSlice u) (gkMu u n : ℂ)).im = 0 ∧
    ((-1 : ℂ) ^ n * normingFactor (realSlice u) (gkMu u n : ℂ)).re = signedNorming38 u n := by
  have hU := normingFactor_real_im38 u (gkMu u n)
  have hp : ((-1 : ℂ) ^ n).im = 0 := by
    have : ((-1 : ℂ) ^ n) = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  rw [Complex.mul_im, hp, hU]; ring

theorem G1076_main :
((
  (∀ φ : PotPair, φ.2 = star φ.1 → ∀ n : ℤ,
    let M : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair φ (muSeq φ n)
    let U : ℂ := (M 0 0 + M 0 1 + M 1 0 + M 1 1) / 2
    ((-1 : ℂ) ^ n * U).im = 0 ∧ 0 < ((-1 : ℂ) ^ n * U).re) ∧
  (∀ n : ℤ, AnalyticOnNhd ℝ (fun u : PhysicalL2 =>
    let M : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair (realSlice u) (muSeq (realSlice u) n)
    let U : ℂ := (M 0 0 + M 0 1 + M 1 0 + M 1 1) / 2
    2 * Real.log ((-1 : ℂ) ^ n * U).re) Set.univ)
  : Prop)) := by
  refine ⟨?_, ?_⟩
  · intro φ hφ n
    obtain ⟨u, rfl⟩ : ∃ u : PhysicalL2, φ = realSlice u := ⟨φ.1, real_of φ hφ⟩
    intro M U
    have hmu : muSeq (realSlice u) n = (gkMu u n : ℂ) := muSeq_eq_gkMu38 u n
    obtain ⟨h1, h2⟩ := sign_re_im u n
    have hpos := signedNorming_positive38 u n
    have e : ((-1 : ℂ) ^ n * U) = (-1 : ℂ) ^ n * normingFactor (realSlice u) (gkMu u n : ℂ) := by
      simp only [U, M, hmu, normingFactor]
    rw [e]
    exact ⟨h1, h2 ▸ hpos⟩
  · intro n
    have h := analyticOnNhd_realKappa38 n
    have e : (fun u : PhysicalL2 =>
        let M : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair (realSlice u) (muSeq (realSlice u) n)
        let U : ℂ := (M 0 0 + M 0 1 + M 1 0 + M 1 1) / 2
        2 * Real.log ((-1 : ℂ) ^ n * U).re) = fun u : PhysicalL2 => realKappa38 u n := by
      funext u
      simp only [realKappa38, signedNorming38, muSeq_eq_gkMu38, normingFactor, parity]
    rw [e]
    exact h

end NlsGge.Atomic.G1076S1
