import NlsGge.GK38.PairAsymptotics

/-!
# K1: bilinear star product and antidiscriminant

Grébert–Kappeler, Chapter I, Corollary 3.2 and Lemma 4.2. The two potentials
are independent complex L² classes; the star product here has no conjugation.
-/

set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

abbrev PairVec38 := Fin 2 → ℂ

/-- The column-star product in zero-based component numbering. -/
def starProd38 (g h : PairVec38) : PairVec38 := ![g 1 * h 1, g 0 * h 0]

/-- Complex bilinear alternating pairing. -/
def pairBracket38 (g h : PairVec38) : ℂ := g 0 * h 1 - g 1 * h 0

/-- Off-diagonal sum of the unit-period monodromy. -/
def antiDiscrim (φ : PotPair) (z : ℂ) : ℂ :=
  monodromyPair φ z 0 1 + monodromyPair φ z 1 0

theorem analyticOnNhd_antiDiscrim :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) Set.univ :=
  (analyticOnNhd_monodromyPair 0 1).add (analyticOnNhd_monodromyPair 1 0)

theorem analyticOnNhd_antiDiscrim_z (φ : PotPair) :
    AnalyticOnNhd ℂ (antiDiscrim φ) Set.univ := fun z _ =>
  AnalyticAt.comp (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
    (f := fun z : ℂ => (φ, z))
    (analyticOnNhd_antiDiscrim (φ, z) (Set.mem_univ _))
    ((analyticAt_const (v := φ)).prod analyticAt_id)

theorem analyticOnNhd_antiDiscrim_phi (z : ℂ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => antiDiscrim φ z) Set.univ := fun φ _ =>
  AnalyticAt.comp (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
    (f := fun φ : PotPair => (φ, z))
    (analyticOnNhd_antiDiscrim (φ, z) (Set.mem_univ _))
    (analyticAt_id.prod analyticAt_const)

/-- A square bound including finite windows, before the infinite sum. -/
def k1SquareBound38 (a : ℤ → ℝ) (C : ℝ) : Prop :=
  (∀ T : Finset ℤ, ∑ n ∈ T, a n ≤ C) ∧ Summable a ∧ ∑' n : ℤ, a n ≤ C

theorem k1SquareBound38_of_finite {a : ℤ → ℝ} {C : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hfin : ∀ T : Finset ℤ, ∑ n ∈ T, a n ≤ C) :
    k1SquareBound38 a C := by
  have hs := summable_of_sum_le ha hfin
  exact ⟨hfin, hs, hs.tsum_le_of_sum_le hfin⟩

end
end NlsGge.GK38
