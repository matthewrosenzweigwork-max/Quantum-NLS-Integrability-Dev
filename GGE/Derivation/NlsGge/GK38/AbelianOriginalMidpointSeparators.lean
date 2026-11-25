import NlsGge.GK38.AbelianRectangularExcision
import Lean.Elab.Tactic.Omega

/-! SOURCE ONLY: the actual original-disc midpoint separators.
These give contiguous finite columns with EXACT outer midpoint-square bounds,
without replacing any original finite-head disc. ROOT owns outer cut geometry.
Exact targets+English preceded proofs. UNCOMPILED, outside next4 scope. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

def p6OriginalSeparator38 (C : ℤ → ℂ) (R : ℤ → ℝ) (n : ℤ) : ℝ :=
  ((C n).re+R n+(C (n+1)).re-R (n+1))/2

theorem p6OriginalSeparator_bounds38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 φ C R) (n : ℤ) :
    (C n).re+R n < p6OriginalSeparator38 C R n ∧
    p6OriginalSeparator38 C R n < (C (n+1)).re-R (n+1) := by
  have hsep := p6Isolating_horizontal_separation38 φ C R hfam n (n+1) (by omega)
  unfold p6OriginalSeparator38
  constructor <;> linarith

theorem p6OriginalSeparator_tail_right38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) (ν : ℕ) (hν : N < ν) :
    p6OriginalSeparator38 C R (ν : ℤ) = ν*Real.pi+Real.pi/2 := by
  have hNν : (N : ℤ) < ν := by exact_mod_cast hν
  have h0 := hgeom.2.2.2.2 (ν : ℤ) (by simpa using hNν)
  have h1 := hgeom.2.2.2.2 ((ν : ℤ)+1) (by
    rw [abs_of_nonneg (by omega)]
    omega)
  unfold p6OriginalSeparator38
  rw [h0.1,h0.2.1,h1.1,h1.2.1]
  simp [countingCenter38]
  ring

theorem p6OriginalSeparator_tail_left38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) (ν : ℕ) (hν : N < ν) :
    p6OriginalSeparator38 C R (-(ν : ℤ)-1) = -(ν*Real.pi+Real.pi/2) := by
  have hNν : (N : ℤ) < ν := by exact_mod_cast hν
  have h0 := hgeom.2.2.2.2 (-(ν : ℤ)-1) (by
    rw [abs_of_nonpos (by omega)]
    omega)
  have h1 := hgeom.2.2.2.2 (-(ν : ℤ)) (by simpa using hNν)
  have hi : (-(ν : ℤ)-1)+1 = -(ν : ℤ) := by omega
  unfold p6OriginalSeparator38
  rw [hi,h0.1,h0.2.1,h1.1,h1.2.1]
  simp [countingCenter38]
  ring

end
end NlsGge.GK38
