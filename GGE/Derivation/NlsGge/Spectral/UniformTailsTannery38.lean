import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NlsGge.SpectralFoundations

/-! # Q2: Tannery's theorem with uniformly small tails (campaign 38)

The pinned `tendsto_tsum_of_dominated_convergence` needs one fixed summable majorant. Here only the tails
`∑_{|n| > N} |f j n|` are asked to be small uniformly in large `j`. The proof splits at `|n| ≤ M`. -/

/-- the tail `∑_{|n| > M} |h n|` -/
def tailSum38 (h : ℤ → ℝ) (M : ℕ) : ℝ :=
  ∑' n : ℤ, (if (M:ℤ) < |n| then |h n| else 0)

theorem tailSum38_summable (h : ℤ → ℝ) (hh : Summable h) (M : ℕ) :
    Summable (fun n : ℤ => if (M:ℤ) < |n| then |h n| else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hh.abs
  · split_ifs <;> positivity
  · split_ifs
    · exact le_rfl
    · exact abs_nonneg _

theorem tailSum38_antitone (h : ℤ → ℝ) (hh : Summable h) {M M' : ℕ} (hM : M ≤ M') :
    tailSum38 h M' ≤ tailSum38 h M := by
  unfold tailSum38
  refine Summable.tsum_le_tsum (fun n => ?_) (tailSum38_summable h hh M') (tailSum38_summable h hh M)
  have : (M:ℤ) ≤ M' := by exact_mod_cast hM
  by_cases h1 : (M':ℤ) < |n|
  · simp [h1, lt_of_le_of_lt this h1]
  · simp only [h1, ite_false]; split_ifs <;> positivity

theorem tsum_sub_finite_le_tailSum38 (h : ℤ → ℝ) (hh : Summable h) (M : ℕ) :
    |(∑' n, h n) - ∑ n ∈ Finset.Icc (-(M:ℤ)) M, h n| ≤ tailSum38 h M := by
  set F : ℤ → ℝ := fun n => if (M:ℤ) < |n| then h n else 0 with hF
  set G : ℤ → ℝ := fun n => if (M:ℤ) < |n| then 0 else h n with hG
  have hFG : h = fun n => G n + F n := by
    funext n; simp only [hF, hG]; split_ifs <;> simp
  have hFabs : ∀ n, |F n| ≤ |h n| := fun n => by
    simp only [hF]; split_ifs
    · exact le_rfl
    · simp
  have hFs : Summable F := Summable.of_norm_bounded (g := fun n => |h n|) hh.abs
    (fun n => by simpa [Real.norm_eq_abs] using hFabs n)
  have hFn : Summable (fun n => ‖F n‖) := by simpa [Real.norm_eq_abs] using hFs.abs
  have hGs : Summable G := by
    have : G = fun n => h n - F n := by funext n; simp only [hF, hG]; split_ifs <;> simp
    rw [this]; exact hh.sub hFs
  have hGsum : ∑' n, G n = ∑ n ∈ Finset.Icc (-(M:ℤ)) M, h n := by
    rw [tsum_eq_sum (s := Finset.Icc (-(M:ℤ)) M)]
    · refine Finset.sum_congr rfl (fun n hn => ?_)
      have : |n| ≤ (M:ℤ) := by
        rw [Finset.mem_Icc] at hn; exact abs_le.mpr hn
      simp [hG, not_lt.mpr this]
    · intro n hn
      have : (M:ℤ) < |n| := by
        by_contra hc
        exact hn (Finset.mem_Icc.mpr (abs_le.mp (not_lt.mp hc)))
      simp [hG, this]
  have h1 : ∑' n, h n = ∑' n, G n + ∑' n, F n := by
    conv_lhs => rw [hFG]
    exact hGs.tsum_add hFs
  rw [h1, hGsum, add_sub_cancel_left]
  calc |∑' n, F n| = ‖∑' n, F n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖F n‖ := norm_tsum_le_tsum_norm hFn
    _ ≤ tailSum38 h M := by
      unfold tailSum38
      refine Summable.tsum_le_tsum (fun n => ?_) hFn (tailSum38_summable h hh M)
      simp only [hF, Real.norm_eq_abs]; split_ifs <;> simp

/-- Tannery with uniformly small tails (no fixed summable majorant needed). -/
theorem tendsto_tsum_of_uniform_tails38 (f : ℕ → ℤ → ℝ) (g : ℤ → ℝ)
    (hf : ∀ j, Summable (f j)) (hg : Summable g)
    (hpt : ∀ n, Tendsto (fun j => f j n) atTop (𝓝 (g n)))
    (htail : ∀ ε > 0, ∃ N : ℕ, ∃ j₀ : ℕ, ∀ j ≥ j₀,
      ∑' n : ℤ, (if (N:ℤ) < |n| then |f j n| else 0) ≤ ε)
    (htailg : ∀ ε > 0, ∃ N : ℕ, ∑' n : ℤ, (if (N:ℤ) < |n| then |g n| else 0) ≤ ε) :
    Tendsto (fun j => ∑' n, f j n) atTop (𝓝 (∑' n, g n)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨N1, j1, hN1⟩ := htail (ε / 4) hε4
  obtain ⟨N2, hN2⟩ := htailg (ε / 4) hε4
  set M := max N1 N2 with hM
  have hfin : Tendsto (fun j => ∑ n ∈ Finset.Icc (-(M:ℤ)) M, f j n) atTop
      (𝓝 (∑ n ∈ Finset.Icc (-(M:ℤ)) M, g n)) :=
    tendsto_finsetSum _ (fun n _ => hpt n)
  rw [Metric.tendsto_atTop] at hfin
  obtain ⟨j2, hj2⟩ := hfin (ε / 4) hε4
  refine ⟨max j1 j2, fun j hj => ?_⟩
  have hj1 : j ≥ j1 := le_trans (le_max_left _ _) hj
  have hj2' : j ≥ j2 := le_trans (le_max_right _ _) hj
  have e1 := tsum_sub_finite_le_tailSum38 (f j) (hf j) M
  have e2 := tsum_sub_finite_le_tailSum38 g hg M
  have t1 : tailSum38 (f j) M ≤ ε / 4 :=
    (tailSum38_antitone (f j) (hf j) (le_max_left N1 N2)).trans (hN1 j hj1)
  have t2 : tailSum38 g M ≤ ε / 4 :=
    (tailSum38_antitone g hg (le_max_right N1 N2)).trans hN2
  have e3 := hj2 j hj2'
  rw [Real.dist_eq] at e3 ⊢
  set A := ∑' n, f j n
  set B := ∑' n, g n
  set a := ∑ n ∈ Finset.Icc (-(M:ℤ)) M, f j n
  set b := ∑ n ∈ Finset.Icc (-(M:ℤ)) M, g n
  have : |A - B| ≤ |A - a| + |a - b| + |b - B| := by
    calc |A - B| = |(A - a) + (a - b) + (b - B)| := by ring_nf
      _ ≤ |(A - a) + (a - b)| + |b - B| := abs_add_le _ _
      _ ≤ |A - a| + |a - b| + |b - B| := by gcongr; exact abs_add_le _ _
  rw [abs_sub_comm b B] at this
  linarith [abs_sub_comm B b]
