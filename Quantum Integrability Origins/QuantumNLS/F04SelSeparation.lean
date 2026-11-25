import Mathlib
import QuantumNLS.F04SelSeparationCore
import QuantumNLS.F04SelBand
import QuantumNLS.F04SelSetup

/-!
# CC:F04:separation (R-F4C3E5BE), physical binding

Source: `F04.tex`, Proposition `CC:F04:selection`, conclusion (CC:F04:separation):
`liminf_N min_{j ≠ i_N} |q_{j,N}(s_N(λ)) − q_{i_N,N}(s_N(λ))| > 0`.

Binding of `F04SelSeparationCore.separation_core` to the physical setting of `F04SelBand` / `F04SelSetup` (sonnet_fourier, read-only): unit `u ∈ L²`, `μ = Mu hκ u = M_u`, `b ≤ k < a` with `I_b, I_a > 0`, old occupation arrays
`η_N` with `(η_N)_b ≥ 1`, `λ ∈ (k, k+1)`, the forced rank `rk` (= `i_N`), the parameter `sParam` (= `s_N(λ)`) and the interpolated roots `qPath … (s_N)`.
`selection_separation` takes, as the printed proof does, the selected-root convergence (CC:F04:selected-root, `q_{i_N,N}(s_N(λ)) → x` for a solution `x` of `θ_u(x) = πλ`) and the weak convergence of the interpolated empirical measures to `μ`
(`F04SelConv.path_weak0` / `F04SelSetup.path_weak`) as hypotheses; the conclusion is the existence of `c₀ > 0` with `|q_{j,N} − q_{i_N,N}| ≥ c₀` for all large `N` and all `j ≠ i_N`.
The other labels are separated from `λ` by `F04SelSetup.other_labels` (`CC:F04:other-labels`, `|ν_j − λ| ≥ min(λ−k, k+1−λ) > 0`), `x ∉ supp μ` by `F04SelBand.xlam_data` (`x ∈ (r, l)`, `μ(r,l) = 0`), and the uniform local height
`LocalHeightUniform.local_height_uniform` does the rest.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.F04SelSeparation

open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.LocalHeight QuantumNLS.F04SelSetup QuantumNLS.F04SelBand
open PhysicalTensor (L2T)

theorem selection_separation {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    {b a k : ℤ} (hbk : b ≤ k) (hka : k < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) {x : ℝ}
    (hx : th hκ u x = lam * Real.pi)
    (hw : EmpiricalWeakConv (fun n => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
      (sParam (η n) (hηb n) (a := a) hbk lam)) (Mu hκ u))
    (hconv : Tendsto (fun n : ℕ => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
      (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)) atTop (𝓝 x)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : Fin (n + 1), j ≠ rk (η n) (hηb n) hbk →
      c₀ ≤ |qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a (sParam (η n) (hηb n) (a := a) hbk lam) j -
        qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a (sParam (η n) (hηb n) (a := a) hbk lam)
          (rk (η n) (hηb n) hbk)| := by
  haveI := Mu_prob hκ u hu
  have hL : 0 < L := Fact.out
  have hu0 := ne_zero_of_II_pos hκ hb
  have hab : b < a := lt_of_le_of_lt hbk hka
  have hk : k ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hbk, hka⟩
  obtain ⟨j, ℓ, r, l, hbj, hjk, hkl, hla, hrl, hnull, hrth, hlth, hlow, hup⟩ :=
    band_data hκ u hu hb ha hbk hka
  obtain ⟨-, hall⟩ := xlam_data hκ u hu hjk hkl hrth hlth hrl hu0 h1 h2
  obtain ⟨hxm, hxθ⟩ := hall x hx
  have hsupp : x ∉ (Mu hκ u).support :=
    Measure.notMem_support_iff_exists.mpr ⟨Ioo r l, isOpen_Ioo.mem_nhds hxm, hnull⟩
  have hθ : theta L κ (Mu hκ u) x = Real.pi * lam := by rw [hxθ]; ring
  set s : ℕ → ℝ := fun n => sParam (η n) (hηb n) (a := a) hbk lam with hs
  have hs01 : ∀ n, 0 < s n ∧ s n < 1 ∧
      nuPath (η n) (hηb n) a (s n) (rk (η n) (hηb n) hbk) = lam :=
    fun n => sParam_spec (η n) (hηb n) hab hk h1 h2
  have hB : ∀ n : ℕ, RealBethe L κ n (qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a (s n))
      (nuPath (η n) (hηb n) a (s n)) := fun n =>
    qPath_realBethe hL hκ (η n) (hηb n) a (hs01 n).1.le (hs01 n).2.1.le
  set κ₀ : ℝ := min (lam - k) ((k : ℝ) + 1 - lam) with hκ₀
  have hκ₀pos : 0 < κ₀ := lt_min (by linarith) (by linarith)
  have hlab : ∀ n : ℕ, ∀ j : Fin (n + 1), j ≠ rk (η n) (hηb n) hbk →
      κ₀ ≤ |nuPath (η n) (hηb n) a (s n) j - lam| := by
    intro n j hj
    obtain ⟨o1, o2⟩ := other_labels (η n) (hηb n) hab hk (hs01 n).1.le (hs01 n).2.1.le j
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · have := o1 hlt
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      exact (min_le_left _ _).trans (by linarith)
    · have := o2 hgt
      rw [abs_of_nonneg (by linarith)]
      exact (min_le_right _ _).trans (by linarith)
  exact QuantumNLS.F04SelSeparationCore.separation_core hL hκ hB hw
    (fun n => rk (η n) (hηb n) hbk) hconv hsupp hθ hκ₀pos hlab

end QuantumNLS.F04SelSeparation

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.F04SelSeparation.selection_separation
