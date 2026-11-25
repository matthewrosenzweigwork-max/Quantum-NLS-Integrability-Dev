import Armstrong.Work.RawBetaMagnitudeSameFamily
import Armstrong.Work.RawBetaMagnitudeRegularFactor

/-!
# Same-family consumption of the GK15.1 regular-factor estimate

Working proof code. This consumes the accepted common input tube for the same
supplied W/F and the separately checked original-disc regular-factor bound.
It does not seal either frozen beta estimate or promote a graph node.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk151_same_family_regular_factor_original_discs38
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
    ∃ δ : ℝ, ∃ B : ℝ, 0 < δ ∧ 0 < B ∧
      ball (realSlice u) δ ⊆ W ∧
      ∀ n : ℤ, ∃ S : PotPair → Lib.L2Seq,
        AnalyticOnNhd ℂ S (ball (realSlice u) δ) ∧
        ∀ φ ∈ ball (realSlice u) δ,
          F n φ = p2Restrict38 n (S φ) ∧
          Lib.sigmaOf (S φ) n = lamMinus (realSlice u) n ∧
          p6PsiNumerator38 n (F n) φ = p2FullNumerator38 n (S φ) ∧
          ∀ m : ℤ, ∀ hmn : m ≠ n,
            ∀ z ∈ ball (discC (realSlice u) m) (discR (realSlice u) m),
              AnalyticAt ℂ (angleRegularFactor38 n m) ((φ, S φ), z) ∧
              ‖angleRegularFactor38 n m ((φ, S φ), z)‖ ≤
                B * Lib.c3w n m ∧
              ((φ, z) ∈ rootDomain38 →
                p6PsiNumerator38 n (F n) φ z / canonRoot38 φ z =
                  ((countingCenter38 m + F n φ ⟨m, hmn⟩ - z) /
                    stdRoot38 (tauN φ m) (gamma2 φ m) z) *
                      angleRegularFactor38 n m ((φ, S φ), z)) := by
  have huW : realSlice u ∈ W := hreal (mem_range_self u)
  have huGK : realSlice u ∈ gkW := hWgk huW
  have hfam₀ := isolating_family38 (realSlice u) huGK
  let K : Set Lib.L2Seq := p6RealInclude38 '' p5FullRealGapCube38 u
  have hK : IsCompact K :=
    (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous
  obtain ⟨U, V, B, hU, hV, hbase, _hUgk, hKV, hB, hbound⟩ :=
    gk151_regular_factor_compact_original_discs38 (realSlice u) huGK
      (discC (realSlice u)) (discR (realSlice u)) hfam₀ K hK
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hbase)
  obtain ⟨ρ, hρ, hρW, hbranches⟩ :=
    gk151_same_family_common_input_tube38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal u V hV hKV
  let δ : ℝ := min ρ ε
  have hδ : 0 < δ := lt_min hρ hε
  have hsubρ : ball (realSlice u) δ ⊆ ball (realSlice u) ρ :=
    ball_subset_ball (min_le_left _ _)
  have hsubU : ball (realSlice u) δ ⊆ U :=
    (ball_subset_ball (min_le_right _ _)).trans hεU
  refine ⟨δ, max B 1, hδ, (by positivity), hsubρ.trans hρW, ?_⟩
  intro n
  obtain ⟨t, _ht, _htz, S, _hSbase, hSan, hSspec⟩ := hbranches n
  refine ⟨S, hSan.mono hsubρ, ?_⟩
  intro φ hφ
  obtain ⟨hSV, hFnS, hSn, hcoords, hnum, _hroots, _hperiods⟩ :=
    hSspec φ (hsubρ hφ)
  refine ⟨hFnS, hSn, hnum, ?_⟩
  intro m hmn z hz
  obtain ⟨c, N, hgeom, hspec₀⟩ := hfam₀
  have hσ : Lib.sigmaOf (S φ) n ∈
      closedBall (discC (realSlice u) n) (discR (realSlice u) n) := by
    rw [hSn]
    exact ball_subset_closedBall
      ((hspec₀.1 n).1 (left_mem_segment ℝ _ _))
  have hfactor :=
    (hbound φ (hsubU hφ)).2 (S φ) hSV n hσ m hmn.symm z hz
  refine ⟨hfactor.1, hfactor.2.trans
    (mul_le_mul_of_nonneg_right (le_max_left B 1) (Lib.c3w_nonneg n m)), ?_⟩
  intro hroot
  have hden := (p2OwnSigma_denominator38
    (discC (realSlice u)) (discR (realSlice u)) c N hgeom
    n m hmn.symm (S φ) hσ z (ball_subset_closedBall hz)).1
  have hid := angleRegularFactor_factorization38 n m (S φ) φ z hroot hden
  have hmcoord :
      Lib.sigmaOf (S φ) m = countingCenter38 m + F n φ ⟨m, hmn⟩ :=
    hcoords ⟨m, hmn⟩
  calc
    p6PsiNumerator38 n (F n) φ z / canonRoot38 φ z =
        p2FullNumerator38 n (S φ) z / canonRoot38 φ z := by rw [hnum]
    _ = ((Lib.sigmaOf (S φ) m - z) /
          stdRoot38 (tauN φ m) (gamma2 φ m) z) *
          angleRegularFactor38 n m ((φ, S φ), z) := hid
    _ = ((countingCenter38 m + F n φ ⟨m, hmn⟩ - z) /
          stdRoot38 (tauN φ m) (gamma2 φ m) z) *
          angleRegularFactor38 n m ((φ, S φ), z) := by rw [hmcoord]

end
end NlsGge.GK38
