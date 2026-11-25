import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# `thm:reset-moser` (LOCAL-017), stage 5a: smooth time clamp and smooth radial cutoff

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "The nonautonomous integral equation for `Y_t` has a unique
local solution ... the solution extends through `0 ≤ t ≤ 1`".  To obtain a *complete* autonomous flow on `K × ℝ` (time as an extra
coordinate), the field `(z, t) ↦ (Y_t z, 1)` is replaced outside the region of interest by a field that agrees with it near
`B_r × [0,1]`: the time argument is clamped by a smooth function `sig` with `sig s = s` for `s ∈ [-1/4, 5/4]`, `|sig| ≤ 3/2`
and bounded derivative, and the space argument is cut off by a smooth function of `‖z‖²` (`cut a b`).  Elementary calculus only.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

open Set Metric Filter Topology

namespace QuantumNLS.ResetMoserClamp

/-- Bump equal to `1` on `[-1/4, 5/4]` and supported in `(-1/2, 3/2)`. -/
def clampBump : ContDiffBump (1 / 2 : ℝ) := ⟨3 / 4, 1, by norm_num, by norm_num⟩

/-- The clamped time: `sig s = s` on `[-1/4, 5/4]`, `|sig| ≤ 3/2`, smooth with bounded derivative. -/
def sig (s : ℝ) : ℝ := s * clampBump s

theorem sig_contDiff {n : ℕ∞} : ContDiff ℝ n sig :=
  contDiff_id.mul clampBump.contDiff

theorem sig_contDiff_one : ContDiff ℝ 1 sig := by exact_mod_cast (sig_contDiff (n := 1))

theorem clampBump_one {s : ℝ} (hs : s ∈ Icc (-1 / 4 : ℝ) (5 / 4)) : clampBump s = 1 := by
  apply clampBump.one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq]
  show |s - 1 / 2| ≤ 3 / 4
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2]

theorem sig_eq {s : ℝ} (hs : s ∈ Icc (-1 / 4 : ℝ) (5 / 4)) : sig s = s := by
  simp [sig, clampBump_one hs]

theorem sig_eventuallyEq {s : ℝ} (hs : s ∈ Ioo (-1 / 4 : ℝ) (5 / 4)) : sig =ᶠ[𝓝 s] id := by
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
  exact sig_eq ⟨hx.1.le, hx.2.le⟩

theorem sig_deriv_one {s : ℝ} (hs : s ∈ Ioo (-1 / 4 : ℝ) (5 / 4)) : deriv sig s = 1 := by
  rw [(sig_eventuallyEq hs).deriv_eq]
  simp

theorem abs_sig_le (s : ℝ) : |sig s| ≤ 3 / 2 := by
  by_cases h : |s - 1 / 2| < 1
  · have h1 := abs_lt.mp h
    have h2 : |s| ≤ 3 / 2 := by rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
    have h3 : |clampBump s| ≤ 1 := by
      rw [abs_of_nonneg clampBump.nonneg]; exact clampBump.le_one
    calc |sig s| = |s| * |clampBump s| := abs_mul _ _
      _ ≤ 3 / 2 * 1 := mul_le_mul h2 h3 (abs_nonneg _) (by norm_num)
      _ = 3 / 2 := by norm_num
  · have : clampBump s = 0 := by
      apply clampBump.zero_of_le_dist
      rw [Real.dist_eq]
      show 1 ≤ |s - 1 / 2|
      exact not_lt.mp h
    simp [sig, this]
    norm_num

theorem hasCompactSupport_sig : HasCompactSupport sig := by
  apply HasCompactSupport.intro (isCompact_closedBall (1 / 2 : ℝ) 1)
  intro x hx
  have : clampBump x = 0 := by
    apply clampBump.zero_of_le_dist
    rw [mem_closedBall, not_le] at hx
    exact hx.le
  simp [sig, this]

theorem exists_deriv_sig_bound : ∃ c : ℝ, ∀ s, ‖deriv sig s‖ ≤ c := by
  have h1 : Continuous (deriv sig) := (sig_contDiff (n := 1)).continuous_deriv (by exact_mod_cast le_rfl)
  exact h1.bounded_above_of_compact_support hasCompactSupport_sig.deriv

/-- Smooth radial cutoff: `1` on `[0, a]`, `0` on `[b, ∞)`. -/
def cut (a b : ℝ) (ha : 0 < a) (hab : a < b) : ContDiffBump (0 : ℝ) := ⟨a, b, ha, hab⟩

theorem cut_contDiff (a b : ℝ) (ha : 0 < a) (hab : a < b) {n : ℕ∞} :
    ContDiff ℝ n (cut a b ha hab) := (cut a b ha hab).contDiff

theorem cut_contDiff_one (a b : ℝ) (ha : 0 < a) (hab : a < b) : ContDiff ℝ 1 (cut a b ha hab) := by
  exact_mod_cast (cut_contDiff a b ha hab (n := 1))

theorem cut_one (a b : ℝ) (ha : 0 < a) (hab : a < b) {x : ℝ} (h0 : 0 ≤ x) (hx : x ≤ a) :
    cut a b ha hab x = 1 := by
  apply (cut a b ha hab).one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg h0]
  exact hx

theorem cut_zero (a b : ℝ) (ha : 0 < a) (hab : a < b) {x : ℝ} (hx : b ≤ x) :
    cut a b ha hab x = 0 := by
  apply (cut a b ha hab).zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
  exact hx

theorem cut_nonneg (a b : ℝ) (ha : 0 < a) (hab : a < b) (x : ℝ) : 0 ≤ cut a b ha hab x :=
  (cut a b ha hab).nonneg

theorem cut_le_one (a b : ℝ) (ha : 0 < a) (hab : a < b) (x : ℝ) : cut a b ha hab x ≤ 1 :=
  (cut a b ha hab).le_one

theorem exists_deriv_cut_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ c : ℝ, ∀ x, ‖deriv (cut a b ha hab) x‖ ≤ c := by
  have h1 : Continuous (deriv (cut a b ha hab)) :=
    (cut_contDiff a b ha hab (n := 1)).continuous_deriv (by exact_mod_cast le_rfl)
  exact h1.bounded_above_of_compact_support (cut a b ha hab).hasCompactSupport.deriv

end QuantumNLS.ResetMoserClamp

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoserClamp.sig_contDiff_one
#print axioms QuantumNLS.ResetMoserClamp.cut_contDiff_one
#print axioms QuantumNLS.ResetMoserClamp.sig_eq
#print axioms QuantumNLS.ResetMoserClamp.sig_deriv_one
#print axioms QuantumNLS.ResetMoserClamp.abs_sig_le
#print axioms QuantumNLS.ResetMoserClamp.exists_deriv_sig_bound
#print axioms QuantumNLS.ResetMoserClamp.cut_one
#print axioms QuantumNLS.ResetMoserClamp.cut_zero
#print axioms QuantumNLS.ResetMoserClamp.exists_deriv_cut_bound
