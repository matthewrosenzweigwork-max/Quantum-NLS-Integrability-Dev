import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST052
import NlsGge.Atomic.KST.KST059
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST061Host

/- KST-061 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST061.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-061"
   (gpt6pro_followup10; no Pro round 5-12 entry touches KST-061).  Lexical repair only: `actualGapSequence` is the
   landed NlsGge.Atomic.KST059.actualGapSequence (selective open, as in the landed KST052 precedent).
   Route = source Corollary 1.1, first paragraph: the high adapted coefficients are b_n(sigma_n), c_{-n}(sigma_{-n});
   finite Fourier support kills them; KST-052 (collapsed gap) gives gamma_n = 0; the nonzero gap set sits inside Icc.
   Uses only diagonalThreshold <= adaptedThreshold (cutoff spec or the guarded fallback), not the existence theorem
   of KST-035.  Supports: KST035Host, KST061Host. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST059 (actualGapSequence)

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

theorem kst061 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (φ : Potential) (hφ : φ ∈ physicalComponentBall w M)
    (ε : ℝ) (hreal : RealForm ε (periodicPair φ))
    (J : ℕ) (hJ : adaptedThreshold w M < J)
    (hsupport : FiniteFourierSupport J (adaptedCoefficients (adaptedThreshold w M) φ)) :
  (∀ n : ℤ, J < n.natAbs → actualGapSequence (periodicPair φ) n = 0) ∧
  pairFiniteGap (periodicPair φ) := by
  have hw' : UnboundedWeight w :=
    ⟨⟨hw.one_le, hw.even, hw.radial_mono⟩, hunbounded⟩
  have hdiag : diagonalThreshold w M ≤ adaptedThreshold w M := by
    unfold adaptedThreshold
    split_ifs with h
    · exact (Nat.find_spec h).1
    · exact le_rfl
  have hφ2 : φ ∈ physicalComponentBall w (2*M) := by
    intro channel
    refine (hφ channel).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  have key : ∀ n : ℤ, J < n.natAbs → actualGapSequence (periodicPair φ) n = 0 := by
    intro n hn
    have hN : adaptedThreshold w M < n.natAbs := lt_trans hJ hn
    have hb : b φ n (diagonalZero n φ) = 0 := by
      have h0 := hsupport false n hn
      have hnot : ¬ n.natAbs ≤ adaptedThreshold w M := not_le.mpr hN
      simpa [adaptedCoefficients, hnot] using h0
    exact (kst052 w M hM hw' φ hφ2 ε hreal n (le_trans hdiag hN.le) hb).2.2.2.2.2.2
  refine ⟨key, ?_⟩
  unfold pairFiniteGap
  refine (Set.finite_Icc (-(J : ℤ)) (J : ℤ)).subset ?_
  intro n hn
  by_contra hnot
  have : J < n.natAbs := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    omega
  exact hn (key n this)

end NlsGge.ThirdConsultation.KST
end
