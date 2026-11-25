import NlsGge.Spectral.NonlinRiccatiAllK38b
import NlsGge.Spectral.F04Continuity38
import NlsGge.Spectral.F04EnergyIdentity38
import NlsGge.Spectral.F04LiteralBounds38
import NlsGge.Spectral.SobolevToL2Map38
import NlsGge.Birkhoff.BirkhoffAPI38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38

/-! # F04: v2 B:lem:spectral, packaged for all `m ≥ 2`

Source: `paper/v2.tex` lines 627-638 (B:eq:Rm and B:lem:spectral).

Reading (decision D2): `|Φ_n(u)|²` is read as the gap action `I_n(u) = (2/π)∫_{g_n(u)} v`, i.e.
`actualGapActionAllE02_38 u n`.  `a_{m,n} = W_m(2πn)` with `W_m = finiteWeightE02_38 m β`
(`W_m(r) = Σ_{j ≤ m} β_j r^{2j}`), `E_m = energySobolev38 m β`, `V_m = localRemainderSobolev38 m β`.
The `H^k` fields are the Fourier carriers `SobolevHilbert k`, mapped to `L²` by `sobolevToL2_38 k`
(same Fourier coefficients), and `R_m(u)` is the series B:eq:Rm, term by term
`gapRemainderTermE02_38 W_m u n = (2/π)∫_{g_n(u)} [W_m(2λ) - a_{m,n}] v(λ;u) dλ`.

Conjuncts, for every `m ≥ 2` and every `β` with `β_j > 0` for `j ≤ m`:

1. (B:lem:spectral, "converges absolutely and ... nonnegative") for every `y ∈ H^{m-1}`,
   `u = sobolevToL2_38 (m-1) y`: `Σ_n |term_n|` is summable and `R_m(u) ≥ 0`.
2. (B:lem:spectral, "continuous function on `H^{m-1}`") `y ↦ R_m(sobolevToL2_38 (m-1) y)` is continuous.
3. (B:eq:energyidentities, first equality), for every `y ∈ H^m`, `u = sobolevToL2_38 m y`:
   `Σ a_{m,n} I_n` is summable, `Σ_n term_n` is summable, and `E_m(y) = Σ' a_{m,n} I_n + R_m(u)`.
   (`R_m(u)` is the `H^{m-1}` series evaluated at `u`; `H^m ⊂ H^{m-1}` since `sobolevToL2_38 m y` has
   `SobolevSquareSummable m`, hence `(m-1)`.)
4. (B:eq:energyidentities, second equality) for every `y ∈ H^m`: the series `Σ a_{m,n} |û(n)|²` is summable,
   `a_{m,n} = finiteHierarchyRate38 m β n`, `û(n) = y n` (also equal to `physicalFourier (sobolevToL2_38 m y) n`),
   and for the `H^{m-1}` representative `y'` of `y` (which exists), `E_m(y) = Σ' a_{m,n}|û(n)|² + V_m(y')`.
-/

/-- **F04 (B:lem:spectral) for all `m ≥ 2` and positive coefficients.** -/
theorem F04_spectral_lemma38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) :
    -- (i) absolute convergence and nonnegativity of `R_m` on `H^{m-1}`
    (∀ y : SobolevHilbert ((m - 1 : ℕ) : ℝ),
      Summable (fun n : ℤ =>
        |gapRemainderTermE02_38 (finiteWeightE02_38 m β) ((sobolevToL2_38 (m - 1)) y) n|) ∧
      0 ≤ ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β) ((sobolevToL2_38 (m - 1)) y) n) ∧
    -- (ii) continuity of `R_m` on `H^{m-1}`
    (Continuous fun y : SobolevHilbert ((m - 1 : ℕ) : ℝ) => ∑' n : ℤ,
      gapRemainderTermE02_38 (finiteWeightE02_38 m β) ((sobolevToL2_38 (m - 1)) y) n) ∧
    -- (iii) the two energy identities on `H^m`
    (∀ y : SobolevHilbert ((m : ℕ) : ℝ),
      -- first equality, with `|Φ_n|² = I_n` (D2)
      Summable (fun n : ℤ => finiteWeightE02_38 m β (2 * Real.pi * (n : ℝ)) *
        actualGapActionAllE02_38 ((sobolevToL2_38 m) y) n) ∧
      Summable (fun n : ℤ => gapRemainderTermE02_38 (finiteWeightE02_38 m β) ((sobolevToL2_38 m) y) n) ∧
      energySobolev38 m β y =
        ∑' n : ℤ, finiteWeightE02_38 m β (2 * Real.pi * (n : ℝ)) *
          actualGapActionAllE02_38 ((sobolevToL2_38 m) y) n +
        ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β) ((sobolevToL2_38 m) y) n ∧
      -- second equality
      Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) ∧
      (∃ y' : SobolevHilbert ((m - 1 : ℕ) : ℝ),
        ∀ n, (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n =
          (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n) ∧
      (∀ y' : SobolevHilbert ((m - 1 : ℕ) : ℝ),
        (∀ n, (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n =
          (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n) →
        energySobolev38 m β y =
          (∑' n : ℤ, finiteHierarchyRate38 m β n *
            ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) +
          localRemainderSobolev38 m β (toCarrier38 _ y'))) := by
  refine ⟨fun y => ?_, spectralRemainder_continuous_all38 m hm β hβ, fun y => ?_⟩
  · exact spectralRemainder_F04_E02_38 m (by omega) β hβ _ (sobolevToL2_38_sobolev (m - 1) y)
  · have hsob := sobolevToL2_38_sobolev m y
    obtain ⟨hsa, -⟩ := weightedMoment_split38 m hm β hβ _ hsob
    have hcs : ∀ j ∈ Finset.range (m + 1), Summable (fun n : ℤ => β j *
        ((2 * Real.pi * (n : ℝ)) ^ (2 * j) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2)) :=
      fun j hj => (summable_chargeQuad_term38 m j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) y).mul_left _
    have hfun : (fun n : ℤ => finiteHierarchyRate38 m β n *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) = fun n : ℤ =>
          ∑ j ∈ Finset.range (m + 1), β j * ((2 * Real.pi * (n : ℝ)) ^ (2 * j) *
            ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) := by
      funext n
      simp only [finiteHierarchyRate38, finiteHierarchyW38, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hrest : SobolevSquareSummable (((m - 1 : ℕ)) : ℝ) (physicalFourier (sobolevToL2_38 m y)) :=
      sobolevSquareSummable_restrict _ _ (by exact_mod_cast Nat.sub_le m 1) _ hsob
    refine ⟨hsa, ?_, energyIdentity_spectral_all38 m hm β hβ y, ?_, ?_, ?_⟩
    · exact (spectralRemainder_F04_E02_38 m hm β hβ _ hrest).1.of_abs
    · rw [hfun]; exact summable_sum hcs
    · refine ⟨weightedRealComparisonContinuous (sobolevModeWeight (m : ℝ))
        (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) 1 (by norm_num)
        (NlsGge.Birkhoff.sobolevModeWeight_mono_one (by exact_mod_cast Nat.sub_le m 1)) y, fun n => rfl⟩
    · intro y' hyy
      exact energyIdentity_fourier38 m hm β y y' hyy

end NlsGge.SpectralFoundations
end
