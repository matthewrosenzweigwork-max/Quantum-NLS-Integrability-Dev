import QuantumNLS.F04SelConv
import QuantumNLS.F04SelSeparation

/-! R-F4C3E5BE `CC:F04:selection` (root_response/F04.tex:202) as one named theorem
(`selection`): selection of the forced root and its separation.  Convergence clause:
`F04SelConv.selection_conv` (this record's S1/S4a on top of `SelectionBand.selection_core`);
separation clause: `F04SelSeparation.selection_separation` (review record, read-only). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace QuantumNLS.F04Selection

open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.LocalHeight QuantumNLS.F04SelRank QuantumNLS.F04SelSetup QuantumNLS.F04SelBand
  QuantumNLS.F04SelConv
open PhysicalTensor (L2T)

/-- **R-F4C3E5BE `CC:F04:selection`.**  Let `u` be a unit vector of `L^2(T_L)`, `kappa > 0`,
`mu = M_u`, `I_n = I_n^{(kappa)}(u)`; integers `b < a` (as `b <= k < a`) with `I_b, I_a > 0`; old
occupation arrays `eta_N` (`N = n+1` particles) with `eta_b >= 1`, `eta_N/N -> I` in `l^1`, and
roots `arrRoots L (kappa/N) eta_N` whose empirical measures converge weakly to `mu`
(the printed endpoint hypothesis; all intermediate `s` follow, `path_weak0`).  For every
non-integer `lambda in (k, k+1)`: the point `x(lambda)` with `theta_u(x) = pi lambda` exists, the
selected root of the interpolated array at the printed parameter `s_N(lambda)` and forced rank
`i_N = C_{k,N}` converges to every such point, and the other roots stay a fixed distance from it. -/
theorem selection {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    {b a k : ℤ} (hbk : b ≤ k) (hka : k < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κ / ((n : ℝ) + 1)) (η n)) (Mu hκ u))
    {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) :
    (∃ x, th hκ u x = lam * Real.pi) ∧
    (∀ x, th hκ u x = lam * Real.pi →
      Tendsto (fun n : ℕ => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
        (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)) atTop (𝓝 x)) ∧
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : Fin (n + 1), j ≠ rk (η n) (hηb n) hbk →
      c₀ ≤ |qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) j -
        qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)| := by
  haveI := Mu_prob hκ u hu
  have hL : 0 < L := Fact.out
  have hab : b < a := lt_of_le_of_lt hbk hka
  have hk : k ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hbk, hka⟩
  obtain ⟨hex, hconv⟩ := selection_conv hκ u hu hbk hka hb ha η hηb hη hend h1 h2
  refine ⟨hex, hconv, ?_⟩
  obtain ⟨x, hx⟩ := hex
  have hs01 : ∀ n, 0 < sParam (η n) (hηb n) (a := a) hbk lam ∧
      sParam (η n) (hηb n) (a := a) hbk lam < 1 :=
    fun n => ⟨(sParam_spec (η n) (hηb n) hab hk h1 h2).1, (sParam_spec (η n) (hηb n) hab hk h1 h2).2.1⟩
  have hend0 : EmpiricalWeakConv (fun n : ℕ => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a 0)
      (Mu hκ u) := by
    have : (fun n : ℕ => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a 0) =
        fun n : ℕ => arrRoots L (κ / ((n : ℝ) + 1)) (η n) := by
      funext n
      exact qPath_zero L _ (η n) (hηb n) a
    rw [this]
    exact hend
  have hw := path_weak0 hL hκ hab η hηb hend0
    (fun n => sParam (η n) (hηb n) (a := a) hbk lam) (fun n => (hs01 n).1.le)
    (fun n => (hs01 n).2.le)
  exact QuantumNLS.F04SelSeparation.selection_separation hκ u hu hbk hka hb ha η hηb h1 h2 hx hw (hconv x hx)

end QuantumNLS.F04Selection
#print axioms QuantumNLS.F04Selection.selection
