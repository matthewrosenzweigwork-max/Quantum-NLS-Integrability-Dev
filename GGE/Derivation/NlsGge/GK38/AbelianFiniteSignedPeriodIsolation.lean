import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Complex.Basic
import Lean.Elab.Tactic.Omega

/-! SOURCE ONLY: finite signed-label sum isolation. No contour/period value
oracle. Actual off-n period vanishing later realizes the meaningful premise.
Exact target/English preceded proof. UNCOMPILED/no native scope. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem p6Finite_signed_period_single38 (A : ℤ → ℂ) (n : ℤ) (ν : ℕ)
    (hn : |n| ≤ (ν : ℤ)) (hzero : ∀ m : ℤ, m ≠ n → A m=0) :
    (∑ k ∈ Finset.range (2*ν+1), A ((k : ℤ)-ν)) = A n := by
  have hnlo := (abs_le.mp hn).1
  have hnhi := (abs_le.mp hn).2
  let k : ℕ := (n+(ν : ℤ)).toNat
  have hk : (k : ℤ) = n+(ν : ℤ) := Int.toNat_of_nonneg (by omega)
  have hkmem : k ∈ Finset.range (2*ν+1) := Finset.mem_range.mpr (by omega)
  have hlabel : (k : ℤ)-(ν : ℤ)=n := by omega
  have hsum : (∑ j ∈ Finset.range (2*ν+1), A ((j : ℤ)-ν)) = A ((k : ℤ)-ν) := by
    apply Finset.sum_eq_single_of_mem k hkmem
    intro j hj hjne
    exact hzero ((j : ℤ)-ν) (by omega)
  simpa only [hlabel] using hsum

end
end NlsGge.GK38
