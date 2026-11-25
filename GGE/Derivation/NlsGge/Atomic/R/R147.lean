import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W11Equivalence38f
import NlsGge.Birkhoff.W11Equivalence38c
import NlsGge.Birkhoff.W10Localized38i
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.ThirdConsultation.R.R110Host
import NlsGge.ThirdConsultation.R.R142Host

/- R-147 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). PACKET R-147, target
   NlsGge/Atomic/R/R147.lean (TASK_INDEX, REUSE/EXTRACT). Head and preamble VERBATIM from followup13 STATEMENTS/R.md
   §R-147 (= r14 L7400; r16 no change) except owner-APPROVED lexical repair 24 (`(B).ZW38`). Route as printed: the landed
   actual W11Equivalence38f `W11_38` (∀ divergence δK) specialized to δ = canonicalDelta via its landed characterization
   canonicalDelta_spec (R109Host; the R-109 divergence), with the SAME B, O, c, s and actual fN38 throughout; criterion 1
   is W11Normalizer38 by definition; criterion 2 is translated from the integral form to L1Converges (hosted printed
   eLpNorm body, R142Host) by the landed bridge tendsto_l1_iff_eLpNorm_W11, after integrability of every fN38 and of
   the density (landed weight_W11 certificate at the same δ). actualRamerDensity is fW06_38 at weightedK = KW06_38 and
   canonicalDelta by definition. L1 convergence of the Fourier densities is NOT identified with total variation of
   physical laws: criterion 4 is the printed weak criterion. A criterion EQUIVALENCE only; no criterion is asserted
   true. No unlanded packet module is imported: R-141/R-142/R-143/R-146 are not used in Lean (W11_38 already contains
   their content); the hosts used are R109Host, R110Host (landed) and R142Host (queued q297 — staged-after dependency).
   Preamble addition (logged repair 22 class, root-logged + reviewer-confirmed; precedents R-105, KO-018, T-017, h783
   R-141): `open NlsGge.HierarchyRiccati.Core`, because the printed opens do not resolve `relativePartition38` (unique
   declaration NlsGge.HierarchyRiccati.Core.relativePartition38; worker replica RUN01 871adc7a "Unknown identifier").
   The head's `relativePartition38 c N` is left exactly as printed. Ambiguity check: no other identifier of this file
   names a declaration of that namespace (see SPEC_DRAFT). Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem actual_W11 {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    let hs1 : s ≤ 1 := by linarith
    List.TFAE [
      Tendsto (fun N : ℕ => relativePartition38 c N) atTop (𝓝 ((B).ZW38 c.val)),
      L1Converges (fullWeightedSequenceGaussian c s)
        (fun N : ℕ => fN38 c s N) (actualRamerDensity c s hs hs1),
      UniformIntegrable (fun N : ℕ => fN38 c s N) 1 (fullWeightedSequenceGaussian c s),
      W11Weak38 B c s,
      W11Tight38 c] := by
  intro hs1
  have hδ : RamerDivergence38 c s
      (PDE.actualBirkhoffInput38.KW06_38 PDE.actualOneSmoothingInput38 c
        (le_one_of_lt_three_quarters_W06_38 hs')) (canonicalDelta c s hs hs1) :=
    canonicalDelta_spec c s hs hs1
  have h := ((B).W11_38 O c hs hs').2 _ hδ
  have hW := (B).weight_W11 O c hs hs' _ hδ
  have hb : L1Converges (fullWeightedSequenceGaussian c s)
      (fun N : ℕ => fN38 c s N) (actualRamerDensity c s hs hs1) ↔
      Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
          fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs'))
            (canonicalDelta c s hs hs1) x| ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0) :=
    (tendsto_l1_iff_eLpNorm_W11 (μ := fullWeightedSequenceGaussian c s)
      (fn := fun N x => fN38 c s N x)
      (f := fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs'))
        (canonicalDelta c s hs hs1))
      (fun N => BirkhoffInput38.integrable_fN38 c hs N) hW.integrable).symm
  tfae_have 1 ↔ 2 := (h.out 1 2).trans hb.symm
  tfae_have 2 ↔ 3 := hb.trans (h.out 2 3)
  tfae_have 3 ↔ 4 := h.out 3 4
  tfae_have 4 ↔ 5 := h.out 4 5
  tfae_finish

end NlsGge.ThirdConsultation.R
