import Mathlib
import NlsGge.Atomic.G4.G4048Host
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4025
import NlsGge.Atomic.G4.G4045
import NlsGge.Atomic.G4.G4047

/- G4-048 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4048.lean,
   namespace NlsGge.GKDefinitionDesign as the landed G4 packets.
   Head: design STATEMENTS/G4.md G4-048 (identical in followup2..9; no Pro head), verbatim.
   Route (source GK-16.4): constantEtaCorrection = (K(tau)-1) * eta with eta = elementaryEtaIntegral.
   If lamPlus = lamMinus then eta = 0. Otherwise G4025Aux.noWinding + G4045 bound ||eta|| by pi + log 2 + log(1+2b/g)
   (g = ||lamPlus-lamMinus||, b = ||mu-tau||), hL bounds ||K(tau)-1|| <= L g, and G4047
   `mul_log_one_add_div_le` (a=g, b:=2b) gives g*log(1+2b/g) <= 2b. Constant C = pi + log 2 + 2. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G4048 (V : Set PotPair) (L : ℝ) (hL : NormalizedZetaGapBound V L) :
  ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ V, ∀ n : ℤ,
    ‖constantEtaCorrection n φ‖ ≤ C * L *
      (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) := by
  obtain ⟨hL0, -, hK⟩ := hL
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpi := Real.pi_pos
  refine ⟨Real.pi + Real.log 2 + 2, by linarith, fun φ hφ n => ?_⟩
  have hKn := hK φ hφ n
  set g : ℝ := ‖lamPlus φ n - lamMinus φ n‖ with hg
  set b : ℝ := ‖muSeq φ n - tauN φ n‖ with hb
  have hg0 : 0 ≤ g := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hrhs : 0 ≤ (Real.pi + Real.log 2 + 2) * L * (g + b) := by positivity
  unfold constantEtaCorrection
  rw [norm_mul]
  by_cases hne : lamPlus φ n = lamMinus φ n
  · have : elementaryEtaIntegral n φ = 0 := by
      unfold elementaryEtaIntegral
      rw [if_pos hne]
    rw [this, norm_zero, mul_zero]
    exact hrhs
  · have hγ : lamPlus φ n - lamMinus φ n ≠ 0 := sub_ne_zero.mpr hne
    have hgpos : 0 < g := norm_pos_iff.mpr hγ
    have h45 := G4045 _ _ _ _ (G4025Aux.noWinding (lamPlus φ n - lamMinus φ n) (tauN φ n) (muSeq φ n) hγ)
    have hη : elementaryEtaIntegral n φ =
        elementarySlitIntegral (lamPlus φ n - lamMinus φ n) (tauN φ n) (muSeq φ n) := by
      unfold elementaryEtaIntegral
      rw [if_neg hne]
    rw [hη]
    have hlogterm : g * Real.log (1 + 2 * b / g) ≤ 2 * b := by
      have := NlsGge.Atomic.G4.mul_log_one_add_div_le (a := g) (b := 2 * b) hgpos (by positivity)
      exact this
    have h1 : ‖normalizedZeta n φ (tauN φ n) - 1‖ *
        ‖elementarySlitIntegral (lamPlus φ n - lamMinus φ n) (tauN φ n) (muSeq φ n)‖ ≤
        (L * g) * (Real.pi + Real.log 2 + Real.log (1 + 2 * ‖muSeq φ n - tauN φ n‖ /
          ‖lamPlus φ n - lamMinus φ n‖)) :=
      mul_le_mul hKn h45 (norm_nonneg _) (mul_nonneg hL0 hg0)
    refine h1.trans ?_
    have e1 : (L * g) * (Real.pi + Real.log 2 + Real.log (1 + 2 * b / g)) =
        L * ((Real.pi + Real.log 2) * g + g * Real.log (1 + 2 * b / g)) := by ring
    rw [e1]
    have e2 : (Real.pi + Real.log 2) * g + g * Real.log (1 + 2 * b / g) ≤
        (Real.pi + Real.log 2 + 2) * (g + b) := by nlinarith
    calc L * ((Real.pi + Real.log 2) * g + g * Real.log (1 + 2 * b / g))
        ≤ L * ((Real.pi + Real.log 2 + 2) * (g + b)) := mul_le_mul_of_nonneg_left e2 hL0
      _ = (Real.pi + Real.log 2 + 2) * L * (g + b) := by ring

end
end NlsGge.GKDefinitionDesign
