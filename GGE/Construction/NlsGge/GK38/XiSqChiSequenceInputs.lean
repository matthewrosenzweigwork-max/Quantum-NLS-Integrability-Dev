import NlsGge.GK38.XiSqTailInputs
import NlsGge.GK38.XiSqChi
import NlsGge.GK38.Lib.EntireProductsC34g

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- Actual symmetric spectral means lie in the actual labelled cuts. -/
theorem a5Tau_mem_segment38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    tauN φ n ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
  rw [tauN_value38 φ hφ n]
  simpa only [add_comm] using stdRoot_midpoint_mem38 (lamMinus φ n) (lamPlus φ n)

theorem a5Tau_injective38 (φ : PotPair) (hφ : φ ∈ gkW) :
    Function.Injective (tauN φ) := by
  obtain ⟨c, N, hg, hs⟩ := isolating_family38 φ hφ
  intro m n he
  by_contra hmn
  have hm := (hs.1 m).1 (a5Tau_mem_segment38 φ hφ m)
  have hn := (hs.1 n).1 (a5Tau_mem_segment38 φ hφ n)
  rw [he] at hm
  exact Set.disjoint_left.mp (isolating_geometry_disjoint38 _ _ c N hg hmn) hm hn

/-- The accepted common geometry earns precisely the separation used by C.3. -/
theorem a5Tau_Dn_separation38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hs : IsolatingSpectral38 φ C R)
    (n : ℤ) (hn : (N : ℤ) < |n|) (z : ℂ) (hz : z ∈ Lib.Dn n)
    (m : ℤ) (hmn : m ≠ n) :
    c⁻¹ * |(m : ℝ) - n| ≤ ‖tauN φ m - z‖ := by
  have hm := (hs.1 m).1 (a5Tau_mem_segment38 φ hφ m)
  have htail := hg.2.2.2.2 n hn
  have hzn : z ∈ ball (C n) (R n) := by
    rw [htail.1, htail.2.1]
    exact hz
  have hl := (hg.2.2.2.1 m n hmn).1
  have hu := ballDistance38_le_pair (C m) (C n) (R m) (R n) hm hzn
  have hcast : (((m - n : ℤ) : ℝ)) = (m : ℝ) - n := by push_cast; rfl
  rw [hcast] at hl
  exact hl.trans (hu.trans_eq (dist_eq_norm _ _))

/-- Positive convolution of actual gap squares with the accepted inverse-square kernel. -/
def a5GammaConvolution38 (φ : PotPair) (n : ℤ) : ℝ :=
  Lib.c3B 1 (fun m : ℤ => (Real.sqrt ‖gamma2 φ m‖ : ℂ)) (fun _ => 0) n

theorem a5GammaConvolution_eq38 (φ : PotPair) (n : ℤ) :
    a5GammaConvolution38 φ n = ∑' m : ℤ, ‖gamma2 φ m‖ * Lib.c3w n m ^ 2 := by
  unfold a5GammaConvolution38 Lib.c3B
  simp only [one_pow, one_mul, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _)]

theorem a5GammaConvolution_bounds38 (φ : PotPair) (B : ℝ)
    (hs : Summable (fun m : ℤ => ‖gamma2 φ m‖))
    (hb : (∑' m : ℤ, ‖gamma2 φ m‖) ≤ B) :
    (∀ n : ℤ, 0 ≤ a5GammaConvolution38 φ n ∧ a5GammaConvolution38 φ n ≤ B) ∧
      Summable (a5GammaConvolution38 φ) ∧
      (∑' n : ℤ, a5GammaConvolution38 φ n) ≤ B * Lib.invSqSum ∧
      Summable (fun n : ℤ => a5GammaConvolution38 φ n ^ 2) ∧
      (∑' n : ℤ, a5GammaConvolution38 φ n ^ 2) ≤ B^2 * Lib.invSqSum := by
  let σ : ℤ → ℂ := fun m => (Real.sqrt ‖gamma2 φ m‖ : ℂ)
  have hnorm (m : ℤ) : ‖σ m - (0 : ℂ)‖^2 = ‖gamma2 φ m‖ := by
    simp only [σ, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _)]
  have hσ : Summable (fun m : ℤ => ‖σ m - (0 : ℂ)‖^2) := by
    simpa only [hnorm] using hs
  have hσB : (∑' m : ℤ, ‖σ m - (0 : ℂ)‖^2) ≤ B := by
    simpa only [hnorm] using hb
  have hnonneg : ∀ n : ℤ, 0 ≤ a5GammaConvolution38 φ n :=
    Lib.c3B_nonneg 1 σ (fun _ => 0)
  have hpoint : ∀ n : ℤ, a5GammaConvolution38 φ n ≤ B := by
    intro n
    simpa only [a5GammaConvolution38, σ, one_pow, one_mul] using Lib.c3B_le (c := 1) hσ hσB n
  have hfinite (T : Finset ℤ) : ∑ n ∈ T, a5GammaConvolution38 φ n ≤ B * Lib.invSqSum := by
    simpa only [a5GammaConvolution38, σ, one_pow, one_mul] using Lib.sum_c3B_le (c := 1) hσ hσB T
  have hfiniteSq (T : Finset ℤ) :
      ∑ n ∈ T, a5GammaConvolution38 φ n ^ 2 ≤ B^2 * Lib.invSqSum := by
    simpa only [a5GammaConvolution38, σ, one_pow, one_mul] using Lib.sum_c3B_sq_le (c := 1) hσ hσB T
  exact ⟨fun n => ⟨hnonneg n, hpoint n⟩,
    summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite,
    summable_of_sum_le (fun n => sq_nonneg _) hfiniteSq,
    Real.tsum_le_of_sum_le (fun n => sq_nonneg _) hfiniteSq⟩

end
end NlsGge.GK38
