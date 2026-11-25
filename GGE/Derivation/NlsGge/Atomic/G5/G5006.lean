import Mathlib
import NlsGge.Atomic.G5.G5003
import NlsGge.Atomic.G5.G5005
import NlsGge.ThirdConsultation.G5.G5005Support1

/- G5-006 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5006.lean.
   Head `G5006` verbatim from STATEMENTS/G5.md (followup12; round 14 retains the head); `finiteGap` is
   NlsGge.ThirdConsultation.finiteGap (opened by name) as in landed G5004/G5005.  No lexical edits.
   Route: outside the finite set of open gaps gamma2 = 0, so G5-003 expresses the z-gradient through the five gradients
   controlled by G5-005; the Fourier terms cancel exactly (2*a*I*(I/2) = -a) leaving a five-term sum of l2 sequences. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.ThirdConsultation (finiteGap)
open NlsGge.ThirdConsultation.G5005Support1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5006_sq {f : ℤ → ℝ} (h : Memℓp f 2) : Summable (fun n => f n ^ 2) := by
  have := (memℓp_gen_iff (by simp)).mp h
  simpa [Real.norm_eq_abs, sq_abs] using this

theorem g5006_five (v1 v2 v3 v4 v5 : PotPair) :
    pairGradientNorm (v1 + v2 + v3 + v4 + v5) ^ 2 ≤
      16 * pairGradientNorm v1 ^ 2 + 16 * pairGradientNorm v2 ^ 2 + 8 * pairGradientNorm v3 ^ 2 +
        4 * pairGradientNorm v4 ^ 2 + 2 * pairGradientNorm v5 ^ 2 := by
  have h1 := pgn_add_sq (v1 + v2 + v3 + v4) v5
  have h2 := pgn_add_sq (v1 + v2 + v3) v4
  have h3 := pgn_add_sq (v1 + v2) v3
  have h4 := pgn_add_sq v1 v2
  nlinarith

theorem g5006_algebra (n a : ℤ) (ha : a = 1 ∨ a = -1) (gt gm gd gq : PotPair) (q d d' : ℂ) :
    ((2 : ℂ) • (gt - gm) + (2 * (a : ℂ) * Complex.I) • (d • gq + q • (gd + d' • gm))) +
        (2 : ℂ) • fourierMode a n =
      (2 : ℂ) • gt + (-2 : ℂ) • (gm - (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n)) +
        (2 * (a : ℂ) * Complex.I) • (d • gq) +
        (2 * (a : ℂ) * Complex.I) • ((q * d') • gm) +
        (2 * (a : ℂ) * Complex.I) • (q • gd - (Complex.I / 2) • (fourierMode 1 n - fourierMode (-1) n)) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases ha with rfl | rfl
  · simp only [Int.cast_one]
    match_scalars <;> first | ring1 | (linear_combination (1 : ℂ) * hI) | (linear_combination (-1 : ℂ) * hI) | (linear_combination (2 : ℂ) * hI) | (linear_combination (-2 : ℂ) * hI) | (linear_combination (1/2 : ℂ) * hI) | (linear_combination (-1/2 : ℂ) * hI) | (linear_combination (4 : ℂ) * hI) | (linear_combination (-4 : ℂ) * hI)
  · simp only [Int.cast_neg, Int.cast_one]
    match_scalars <;> first | ring1 | (linear_combination (1 : ℂ) * hI) | (linear_combination (-1 : ℂ) * hI) | (linear_combination (2 : ℂ) * hI) | (linear_combination (-2 : ℂ) * hI) | (linear_combination (1/2 : ℂ) * hI) | (linear_combination (-1/2 : ℂ) * hI) | (linear_combination (4 : ℂ) * hI) | (linear_combination (-4 : ℂ) * hI)

theorem G5006 (u : PhysicalL2) (hu : finiteGap u)
    (a : ℤ) (ha : a = 1 ∨ a = -1) :
  Memℓp (fun n : ℤ => pairGradientNorm
    (pairGradient (cartesianZExtended n a) (realSlice u) +
      (2 : ℂ) • fourierMode a n)) 2 := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := G5005 u hu
  have hc2 : ‖(2 * (a : ℂ) * Complex.I)‖ = 2 := by
    rcases ha with rfl | rfl <;> simp
  have hs1 := g5006_sq h1
  have hs2 := g5006_sq h2
  have hs3 := g5006_sq h3
  have hs4 := g5006_sq h4
  have hs5 := g5006_sq h5
  have hbd : Summable (fun n : ℤ => 64 * pairGradientNorm (pairGradient (fun ψ => tauN ψ n) (realSlice u)) ^ 2 +
      64 * pairGradientNorm (pairGradient (fun ψ => muSeq ψ n) (realSlice u) -
        (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n)) ^ 2 +
      32 * pairGradientNorm (antiDiscrim (realSlice u) (muSeq (realSlice u) n) •
        pairGradient (radiusQuotient n) (realSlice u)) ^ 2 +
      16 * pairGradientNorm ((radiusQuotient n (realSlice u) *
        deriv (antiDiscrim (realSlice u)) (muSeq (realSlice u) n)) •
        pairGradient (fun ψ => muSeq ψ n) (realSlice u)) ^ 2 +
      8 * pairGradientNorm (radiusQuotient n (realSlice u) •
        pairGradient (fun ψ => antiDiscrim ψ (muSeq (realSlice u) n)) (realSlice u) -
        (Complex.I / 2) • (fourierMode 1 n - fourierMode (-1) n)) ^ 2) :=
    ((((hs1.mul_left 64).add (hs2.mul_left 64)).add (hs3.mul_left 32)).add (hs4.mul_left 16)).add (hs5.mul_left 8)
  refine memlp_of_sq_summable ?_
  refine Summable.of_norm_bounded_eventually hbd ?_
  have hfin : {n : ℤ | NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n ≠
      NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n}.Finite := hu
  have hev : ∀ᶠ n in cofinite, NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n =
      NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n := by
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with n hn
    by_contra hne
    exact hn hne
  filter_upwards [hev] with n hn
  have hg : gamma2 (realSlice u) n = 0 := by
    rw [(tauGamma_real38 u n).2, hn]; simp
  have hE := G5003 n a ha u hg
  dsimp only at hE
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hE, g5006_algebra n a ha]
  refine le_trans (g5006_five _ _ _ _ _) ?_
  have e2 : ∀ x : PotPair, pairGradientNorm ((2 : ℂ) • x) = 2 * pairGradientNorm x := by
    intro x; rw [pgn_smul]; simp
  have em2 : ∀ x : PotPair, pairGradientNorm ((-2 : ℂ) • x) = 2 * pairGradientNorm x := by
    intro x; rw [pgn_smul]; simp
  have ec : ∀ x : PotPair, pairGradientNorm ((2 * (a : ℂ) * Complex.I) • x) = 2 * pairGradientNorm x := by
    intro x; rw [pgn_smul, hc2]
  rw [em2, e2, ec, ec, ec]
  apply le_of_eq
  ring

end
end NlsGge.GKDefinitionDesign
