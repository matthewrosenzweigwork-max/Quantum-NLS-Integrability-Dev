import Mathlib

/- M-051 HOST01 (proof development, AUTHOR; not reviewed).  Pro round 13 section 10 ("Infinity and Laurent accessor bodies"),
   definition bodies VERBATIM: public `M.AnalyticAtInfinity` and the literal `MPrimitive` infinity predicates
   `infinityFilter`, `ExteriorHolomorphic`, `HasValueAtInfinity`, `HasLaurentCoefficient`.
   Nothing in NlsGge/ defines any of these names (grep, 2026-11-01).
   Lexical changes: import header; `local attribute [instance]` (invalid Lean 4 syntax) -> `attribute [local instance]`. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace NlsGge.ThirdConsultation.M
noncomputable section
attribute [local instance] Classical.propDecidable

def AnalyticAtInfinity (f : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ (fun w : ℂ => if w = 0 then 0 else f w⁻¹) 0

end
end NlsGge.ThirdConsultation.M

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section
attribute [local instance] Classical.propDecidable

def infinityFilter : Filter ℂ :=
  Filter.comap (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ))

def ExteriorHolomorphic (f : ℂ → ℂ) : Prop :=
  ∃ R0 : ℝ, 0 < R0 ∧
    AnalyticOnNhd ℂ f {z : ℂ | R0 < ‖z‖}

def HasValueAtInfinity (f : ℂ → ℂ) (a : ℂ) : Prop :=
  Tendsto f infinityFilter (𝓝 a)

def HasLaurentCoefficient (f : ℂ → ℂ) (k : ℤ) (a : ℂ) : Prop :=
  (∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 < R →
    CircleIntegrable (fun z : ℂ => f z * z ^ (-k - 1)) 0 R) ∧
  Tendsto
    (fun R : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun z : ℂ => f z * z ^ (-k - 1)) 0 R)
    atTop (𝓝 a)

end
end NlsGge.ThirdConsultation.MPrimitive
