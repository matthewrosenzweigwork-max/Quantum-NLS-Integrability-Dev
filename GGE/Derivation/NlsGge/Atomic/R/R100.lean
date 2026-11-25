import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.ThirdConsultation.R.R100Host
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-100 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). PACKET R-100, target
   NlsGge/Atomic/R/R100.lean (TASK_INDEX, REUSE/EXTRACT; prerequisites R-098 landed, R-099 in review — not used in Lean,
   R-010 landed). Preamble and the three printed theorems VERBATIM from followup13 STATEMENTS/R.md §R-100 (= r14; r16 no
   change) except owner-APPROVED lexical repair 24 (`B.` → `(B).`). Proofs: printed reuses
   W04WeightedSmoothing38c `differences_mem_CM_38`, `analytic_differences_E0_38`; the third theorem from W06
   `analytic_KW06_38`/`analytic_KinvW06_38` (weightedK/Kinv are the hosted printed names for KW06_38/KinvW06_38) and the
   landed CM norm identity `actualCM_norm_sq` with cmModeWeight = 2·sourceRate, sourceRate c n = fullWeightRate c.val n
   (definitional) — the exact factor 2 of W06_02_38, without its 1/2 < s premise (not needed for the norm identity).
   Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r100_main {lower upper : ℝ}  
    (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 1) :
    (∀ x ∈ seqE38 c s, (B).T x - x ∈ weightedSubmodule (cmModeWeight c)) ∧
      (∀ x ∈ seqE38 c s, (B).Tinv x - x ∈ weightedSubmodule (cmModeWeight c)) :=
  BirkhoffInput38.differences_mem_CM_38 B O c hs

theorem r100_2 {lower upper : ℝ}  
    (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 1) :
    AnalyticOnNhd ℝ (eMap38 c s 0 (fun y => (B).T y - y) ((B).differences_mem_E0_38 O c hs).1)
        Set.univ ∧
      AnalyticOnNhd ℝ (eMap38 c s 0 (fun y => (B).Tinv y - y) ((B).differences_mem_E0_38 O c hs).2)
        Set.univ :=
  BirkhoffInput38.analytic_differences_E0_38 B O c hs

theorem actual_CM_difference_analytic {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs1 : s ≤ 1) :
    AnalyticOnNhd ℝ (weightedK c s hs1) Set.univ ∧
    AnalyticOnNhd ℝ (Kinv c s hs1) Set.univ ∧
    (∀ h : ActualCM c,
      Summable (fun n : ℤ => fullWeightRate c.val n * ‖cmCoord h n‖ ^ 2) ∧
      ‖h‖ ^ 2 = 2 * ∑' n : ℤ, fullWeightRate c.val n * ‖cmCoord h n‖ ^ 2) := by
  refine ⟨(B).analytic_KW06_38 O c hs1, (B).analytic_KinvW06_38 O c hs1, fun h => ⟨?_, ?_⟩⟩
  · have hsum := (weightedHilbert_hasSum (cmModeWeight c) h).summable.div_const 2
    refine hsum.congr fun n => ?_
    show 2 * sourceRate c n * ‖cmCoord h n‖ ^ 2 / 2 = fullWeightRate c.val n * ‖cmCoord h n‖ ^ 2
    unfold sourceRate fullWeightRate
    ring
  · rw [actualCM_norm_sq, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    show 2 * sourceRate c n * ‖cmCoord h n‖ ^ 2 = 2 * (fullWeightRate c.val n * ‖cmCoord h n‖ ^ 2)
    unfold sourceRate fullWeightRate
    ring

end NlsGge.ThirdConsultation.R
