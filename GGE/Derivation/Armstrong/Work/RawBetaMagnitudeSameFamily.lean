import NlsGge.GK38.AbelianPsiTheorem141
import NlsGge.GK38.AbelianNormalizedOriginalInputTube
import NlsGge.GK38.AbelianGlobalLocalNormalizedBallAgreement

/-!
# Same supplied normalized family on a common local tube

For the supplied `W` and `F` in the GK15.1 telescope, actual normalized local
branches agree with that very `F` on one ball chosen before all signed labels.
The local full sequence has an auxiliary nth coordinate fixed at the base lower
endpoint; only its restriction, its omitted numerator, and its off-index roots
are identified with `F`. No equality of different nth completions is asserted.

The input tube is arbitrary: every open neighborhood of the actual compact real
gap cube can be used. This is a universally quantified conclusion, not an extra
placement or boundedness hypothesis on the supplied family. Taking `V = univ`
requires no tube data. Periods, numerators and roots are attached to this same
family, as required before the uses of (15.3) and (15.5)-(15.6) in GK15.1
(`references/gk/gk.txt:4997-5053`). Those integral/factorization identities
themselves remain separate obligations.
-/

set_option autoImplicit false
open Set Metric
open NlsGge.Pilot

namespace NlsGge.GK38
noncomputable section

/-- Actual local branches in every original input tube realize the supplied
normalized family, simultaneously for all signed indices. The roots and the
entire omitted numerator agree, and the full local numerator inherits exactly
the supplied period normalization. -/
theorem gk151_same_family_common_input_tube38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      p2Fn38 n (φ, F n φ) = 0)
    (hFinv : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ, y)) (F n φ)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W → ∀ m : ℤ,
      abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t)
    (u : PhysicalL2) :
    ∀ V : Set Lib.L2Seq, IsOpen V →
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V →
      ∃ ρ : ℝ, 0 < ρ ∧ ball (realSlice u) ρ ⊆ W ∧
        ∀ n : ℤ, ∃ t : P3RealSpace38 n,
          t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
          ∃ S : PotPair → Lib.L2Seq,
            S (realSlice u) = p6RealInclude38 (p6GapCubeComplete38 n u t) ∧
            AnalyticOnNhd ℂ S (ball (realSlice u) ρ) ∧
            ∀ φ ∈ ball (realSlice u) ρ,
              S φ ∈ V ∧ F n φ = p2Restrict38 n (S φ) ∧
              Lib.sigmaOf (S φ) n = lamMinus (realSlice u) n ∧
              (∀ m : P2Index38 n,
                Lib.sigmaOf (S φ) m.1 = countingCenter38 m.1 + F n φ m) ∧
              p6PsiNumerator38 n (F n) φ = p2FullNumerator38 n (S φ) ∧
              (∀ z : ℂ, p2FullNumerator38 n (S φ) z = 0 ↔
                ∃ m : P2Index38 n, Lib.sigmaOf (S φ) m.1 = z) ∧
              ∀ m : ℤ, abelianPeriod38 m φ (p2FullNumerator38 n (S φ)) =
                if m = n then 2 * (Real.pi : ℂ) else 0 := by
  intro V hV hKV
  have huW : realSlice u ∈ W := hreal (mem_range_self u)
  obtain ⟨d, hd, _hdW, hbranches⟩ :=
    p6Normalized_common_complex_original_input_tube38 u
      (discC (realSlice u)) (discR (realSlice u))
      (isolating_family38 (realSlice u) (hWgk huW)) V hV hKV
  obtain ⟨a, ha, haW⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds huW)
  let ρ : ℝ := min a d
  have hρ : 0 < ρ := lt_min ha hd
  have hρd : ρ ≤ d := min_le_right _ _
  have hsubd : ball (realSlice u) ρ ⊆ ball (realSlice u) d :=
    ball_subset_ball hρd
  have hρW : ball (realSlice u) ρ ⊆ W :=
    (ball_subset_ball (min_le_left _ _)).trans haW
  refine ⟨ρ, hρ, hρW, ?_⟩
  intro n
  obtain ⟨t, ht, htz, S, hSbase, hSan, hSspec⟩ := hbranches n
  obtain ⟨q, hq, hqz, hFbase⟩ := hFreal n u
  have hSrestrict : p2Restrict38 n (S (realSlice u)) = p3RealInclude38 n t := by
    rw [hSbase, p6GapCubeComplete_restrict38]
  have heq := p6Global_local_normalized_ball_agreement38 n W hWopen hWgk (F n)
    (hFanalytic n).continuousOn (hFn n) (hFinv n) u huW d S hSan.continuousOn
    (fun φ hφ => (hSspec φ hφ).2.1) ρ hρ hρd hρW q t
    ⟨hq, hqz⟩ ⟨ht, htz⟩ hFbase hSrestrict
  refine ⟨t, ht, htz, S, hSbase, hSan.mono hsubd, ?_⟩
  intro φ hφ
  have hcoord (m : P2Index38 n) :
      Lib.sigmaOf (S φ) m.1 = countingCenter38 m.1 + F n φ m := by
    rw [heq φ hφ, p2Restrict_apply38]
    rfl
  have hnum : p6PsiNumerator38 n (F n) φ = p2FullNumerator38 n (S φ) := by
    change p2FullNumerator38 n (p2Extend38 n (F n φ)) = _
    rw [heq φ hφ, p6Numerator_extend_restrict38]
  refine ⟨(hSspec φ (hsubd hφ)).1, heq φ hφ,
    (hSspec φ (hsubd hφ)).2.2, hcoord, hnum, ?_, ?_⟩
  · intro z
    rw [← hnum, p6PsiNumerator_exact_roots38]
    exact exists_congr (fun m => by rw [hcoord m])
  · intro m
    rw [← hnum]
    exact hperiod n φ (hρW hφ) m

end
end NlsGge.GK38
