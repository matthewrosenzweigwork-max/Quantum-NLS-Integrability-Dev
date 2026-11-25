-- G1057 PRODUCTION02 (proof development landing kit, 2026-10-27). Proof text from the candidate files named in
-- the header of each section; #check/#print lines and namespace renames only (no proof content change).
import Mathlib
import NlsGge.GK38.NeumannLabels
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.DirichletRealGapIndex
import NlsGge.GK38.DirichletRealDerivative
import NlsGge.GK38.DirichletRealAnalytic
set_option autoImplicit false

section

/-! G1-057 COMMAND01 pre-approval proof (proof development, AUTHOR; not self-reviewed).  Assembled from accepted production pieces:
`lamPlus_real`, `gkMu_mem_gap38`, `muSeq_eq_gkMu38`, `muSeq_simple38`, `muSeq_enumeration38`, `analyticOnNhd_gkMu38`, `gapLower_neg38`/`gapUpper_neg38`,
`neumannChar38_eq_dirichlet_neg`; real-type phi is `realSlice phi.1`. -/

set_option autoImplicit false

namespace NlsGge.Atomic.G1057S3

open NlsGge.GK38 NlsGge.Pilot NlsGge.SpectralFoundations Filter Topology Set

theorem real_of (φ : PotPair) (h : φ.2 = star φ.1) : φ = realSlice φ.1 := by
  rw [realSlice_apply]; exact Prod.ext rfl h

theorem nu_eq (u : PhysicalL2) (n : ℤ) : nuSeq38 (realSlice u) n = (gkMu (-u) n : ℂ) := by
  simpa only [nuSeq38, ← realSlice_neg] using muSeq_eq_gkMu38 (-u) n

theorem dir_simple (u : PhysicalL2) (z : ℂ) (hz : dirichletChar (realSlice u) z = 0) :
    analyticOrderAt (fun w : ℂ => dirichletChar (realSlice u) w) z = 1 := by
  obtain ⟨k, hk⟩ := ((muSeq_enumeration38 (realSlice u)).2.1 z).mp hz
  rw [← hk]
  exact muSeq_simple38 u k

theorem G1057_main :
((
  (∀ φ : PotPair, φ.2 = star φ.1 → ∀ n : ℤ,
    (lamMinus φ n).im = 0 ∧ (lamPlus φ n).im = 0 ∧ (muSeq φ n).im = 0 ∧ (nuSeq38 φ n).im = 0 ∧
    (lamMinus φ n).re ≤ (muSeq φ n).re ∧ (muSeq φ n).re ≤ (lamPlus φ n).re ∧
    (lamMinus φ n).re ≤ (nuSeq38 φ n).re ∧ (nuSeq38 φ n).re ≤ (lamPlus φ n).re) ∧
  (∀ φ : PotPair, φ.2 = star φ.1 → ∀ z : ℂ,
    (dirichletChar φ z = 0 → analyticOrderAt (fun w : ℂ => dirichletChar φ w) z = 1) ∧
    (neumannChar38 φ z = 0 → analyticOrderAt (fun w : ℂ => neumannChar38 φ w) z = 1)) ∧
  (∀ n : ℤ,
    AnalyticOnNhd ℝ (fun u : PhysicalL2 => (muSeq (realSlice u) n).re) Set.univ ∧
    AnalyticOnNhd ℝ (fun u : PhysicalL2 => (nuSeq38 (realSlice u) n).re) Set.univ)
  : Prop)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ hφ n
    obtain ⟨u, rfl⟩ : ∃ u : PhysicalL2, φ = realSlice u := ⟨φ.1, real_of φ hφ⟩
    have hlo : lamMinus (realSlice u) n = (actualGapLowerAllE02_38 u n : ℂ) := (lamPlus_real u n).2
    have hhi : lamPlus (realSlice u) n = (actualGapUpperAllE02_38 u n : ℂ) := (lamPlus_real u n).1
    have hmu : muSeq (realSlice u) n = (gkMu u n : ℂ) := muSeq_eq_gkMu38 u n
    have hnu := nu_eq u n
    have g1 := gkMu_mem_gap38 u n
    have g2 := gkMu_mem_gap38 (-u) n
    rw [gapLower_neg38, gapUpper_neg38] at g2
    rw [hlo, hhi, hmu, hnu]
    simp only [Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨trivial, trivial, trivial, trivial, g1.1, g1.2, g2.1, g2.2⟩
  · intro φ hφ z
    obtain ⟨u, rfl⟩ : ∃ u : PhysicalL2, φ = realSlice u := ⟨φ.1, real_of φ hφ⟩
    refine ⟨dir_simple u z, fun hz => ?_⟩
    have e : (fun w : ℂ => neumannChar38 (realSlice u) w) = fun w : ℂ => dirichletChar (realSlice (-u)) w := by
      funext w; rw [neumannChar38_eq_dirichlet_neg, realSlice_neg]
    have hz' : dirichletChar (realSlice (-u)) z = 0 := by
      rw [realSlice_neg, ← neumannChar38_eq_dirichlet_neg]; exact hz
    rw [e]
    exact dir_simple (-u) z hz'
  · intro n
    refine ⟨?_, ?_⟩
    · exact analyticOnNhd_gkMu38 n
    · have e : (fun u : PhysicalL2 => (nuSeq38 (realSlice u) n).re) = fun u : PhysicalL2 => gkMu (-u) n := by
        funext u; rw [nu_eq u n, Complex.ofReal_re]
      rw [e]
      intro u _
      exact AnalyticAt.comp (g := fun v : PhysicalL2 => gkMu v n) (f := fun v : PhysicalL2 => -v)
        (analyticAt_gkMu38 (-u) n) analyticAt_id.neg

end NlsGge.Atomic.G1057S3

end
