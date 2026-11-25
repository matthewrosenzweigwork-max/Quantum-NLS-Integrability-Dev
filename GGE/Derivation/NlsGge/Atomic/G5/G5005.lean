import Mathlib
import NlsGge.Atomic.G5.G5004
import NlsGge.Atomic.G5.G5005Host
import NlsGge.ThirdConsultation.G5.G5005Support1
import NlsGge.ThirdConsultation.G5.G5005Support2
import NlsGge.ThirdConsultation.G5.G5005Support3
import NlsGge.ThirdConsultation.G5.G5005Support4
import NlsGge.ThirdConsultation.G5.G5005Support5

/- G5-005 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5005.lean.
   Head byte-identical to design STATEMENTS/G5.md:129 (root/gpt6pro_followup8; rounds 9/10 do not touch it);
   `finiteGap` is NlsGge.ThirdConsultation.finiteGap (opened by name, head text unchanged), as in landed G5004.
   Route: five L2 clauses, each from the L2 kernel of the landed GK38/G1 gradient asymptotics, integrated in t;
   see G5005_MAP01.md.  No H1 or Birkhoff hypothesis. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation (finiteGap)

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5005 (u : PhysicalL2) (hu : finiteGap u) :
  let φ := realSlice u
  Memℓp (fun n : ℤ => pairGradientNorm (pairGradient (fun ψ => tauN ψ n) φ)) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    (pairGradient (fun ψ => muSeq ψ n) φ -
      (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n))) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    (antiDiscrim φ (muSeq φ n) • pairGradient (radiusQuotient n) φ)) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    ((radiusQuotient n φ * deriv (antiDiscrim φ) (muSeq φ n)) •
      pairGradient (fun ψ => muSeq ψ n) φ)) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    (radiusQuotient n φ • pairGradient (fun ψ => antiDiscrim ψ (muSeq φ n)) φ -
      (Complex.I / 2) • (fourierMode 1 n - fourierMode (-1) n))) 2 := by
  intro φ
  have hφ : φ ∈ gkW := realSlice_mem_gkW u
  obtain ⟨hq1, -⟩ := G5004 u hu
  have hq : Summable (fun n : ℤ =>
      ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2) := by
    have h := (memℓp_gen_iff (by simp)).mp hq1
    simpa using h
  have h2 := NlsGge.ThirdConsultation.G5005Support2.part2 φ hφ
  exact ⟨NlsGge.ThirdConsultation.G5005Support2.part1 φ hφ, h2,
    NlsGge.ThirdConsultation.G5005Support5.part3 u hu,
    NlsGge.ThirdConsultation.G5005Support5.part4 u hq h2,
    NlsGge.ThirdConsultation.G5005Support4.part5 u hq⟩

end
end NlsGge.GKDefinitionDesign
