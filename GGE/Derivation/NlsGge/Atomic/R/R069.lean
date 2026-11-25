import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.Ramer.RamerFiniteChainRule

/- R069 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/R/R069.lean.
   Packet R-069 (REUSE/EXTRACT). HEAD VERBATIM (block with opens/local notations) from followup13 STATEMENTS/R.md
   "## R-069"; owner-approved LEXICAL REPAIR 24 only: B.field -> (B).field (1 use: (B).detLN).
   Proof = Pro's printed route: landed F01Determinant38d tendstoUniformlyOn_sq_detLN (same TendstoUniformlyOn on the
   same fixed compact K at atTop; uniformity class unchanged), then |1-a| <= |1-a^2| for a = |detLN| >= 0
   (1-a^2 = (1-a)(1+a), 1+a >= 1).  F01_06_identity enters through the producer.  R-066/R-068 not used.
   Own imports declare both notation RHSs (B1 lesson).  RamerFiniteChainRule is import-only.
   Generic replica R069_REPLICA01 lane eba56ae4.  MAIN-ONLY (closure ~150k): needs ROOT MAIN PROBE (R069_RECEIVER01). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r069_main (K : Set H1_38) (hK : IsCompact K) :
    TendstoUniformlyOn (fun (N : ℕ) (x : H1_38) => |(B).detLN x N|)
      (fun _ : H1_38 => (1 : ℝ)) atTop K := by
  have key : ∀ a : ℝ, 0 ≤ a → abs (1 - a) ≤ abs (1 - a ^ 2) := by
    intro a ha
    have hfac : 1 - a ^ 2 = (1 - a) * (1 + a) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 + a by linarith)]
    have h1 : (1 : ℝ) ≤ 1 + a := by linarith
    calc abs (1 - a) = abs (1 - a) * 1 := (mul_one _).symm
      _ ≤ abs (1 - a) * (1 + a) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hsq := NlsGge.Birkhoff.BirkhoffInput38.tendstoUniformlyOn_sq_detLN B O hK
  rw [Metric.tendstoUniformlyOn_iff] at hsq ⊢
  intro ε hε
  filter_upwards [hsq ε hε] with N hN x hx
  have h := hN x hx
  rw [Real.dist_eq] at h ⊢
  exact lt_of_le_of_lt (key _ (abs_nonneg _)) h

end NlsGge.ThirdConsultation.R
