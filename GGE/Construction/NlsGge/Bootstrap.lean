import Mathlib

/-!
Minimal project smoke test and provisional scalar conventions.
No manuscript theorem is implemented by this file.
The first cloud task must compile it before reporting any successful Lean build.
-/
set_option autoImplicit false

noncomputable section

namespace NlsGge

def sourceIdentity : String :=
  "0e7c2e61a06ab6886124c3891c73e0b8997ab71473eaf75b05c524098a58e3ec"

theorem source_identity_smoke : sourceIdentity =
    "0e7c2e61a06ab6886124c3891c73e0b8997ab71473eaf75b05c524098a58e3ec" := rfl

def coefficient (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  c j / (Nat.factorial j : ℝ) ^ 4

def weightTerm (c : ℕ → ℝ) (r : ℝ) (j : ℕ) : ℝ :=
  coefficient c j * r ^ (2 * j)

/-- Positivity and bounds, not any result about convergence or the NLS. -/
structure CoefficientBounds (c : ℕ → ℝ) where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  lower_le : ∀ j, lower ≤ c j
  le_upper : ∀ j, c j ≤ upper

end NlsGge
