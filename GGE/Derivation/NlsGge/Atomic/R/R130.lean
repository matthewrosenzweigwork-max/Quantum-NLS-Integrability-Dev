import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.F01Determinant38c
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-130 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). PACKET R-130, target
   NlsGge/Atomic/R/R130.lean (TASK_INDEX, REUSE/EXTRACT; listed prerequisites R-129, R-095, R-121). Head and preamble
   VERBATIM from followup13 STATEMENTS/R.md §R-130 (r16 no change), with OWNER-APPROVED lexical repair 24 only:
   `B.GalerkinSol38` → `(B).GalerkinSol38` (two occurrences).  Quantifier order as printed: ∀ R (fixed ball), ∃ N₀,
   ∀ N ≥ N₀, ∀ ζ y w.  Imports declare both notation right-hand sides (PDE.BirkhoffRealization, PDE.OneSmoothing;
   B1 lesson) and the defining modules F01Determinant38c (H2_38) and W09Approx38b (GalerkinSol38, producer).
   Proof: the printed exact landed source reuse `Birkhoff/W09Approx38b.lean:galerkinSol_unique_W09` at the actual
   pair B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38; its type is the head verbatim (N₀ uniform
   over the fixed h² ball, from the landed injOn_TN_ballV38).  This proof does NOT use the unlanded R-129 (nor
   R-095/R-121 directly); they are TASK_INDEX prerequisites only. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r130_main (R : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ζ : ℤ → ℂ, ∀ y w : H2_38, ‖y‖ ≤ R → ‖w‖ ≤ R →
      (B).GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
      (B).GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w) →
      carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w :=
  (B).galerkinSol_unique_W09 O R

end NlsGge.ThirdConsultation.R
