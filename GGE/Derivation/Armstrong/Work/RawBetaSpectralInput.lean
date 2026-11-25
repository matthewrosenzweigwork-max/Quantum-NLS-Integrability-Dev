import Armstrong.Work.RawBetaGeometryV2

/-!
Proof candidate for the concrete spectral inputs to the terminal sheet.
Source: GK I.12 isolating spectrum and I.6 Lemma 6.6.
No compiler has yet checked this candidate. Root owns compilation/integration.
-/

set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem rawBetaPerCharZeroInDiscIff38 (φ : GKPotential38) (m : ℤ) (z : ℂ)
    (hz : z ∈ ball (discC φ.1 m) (discR φ.1 m)) :
    perChar φ.1 z = 0 ↔ z = lamMinus φ.1 m ∨ z = lamPlus φ.1 m := by
  obtain ⟨c, N, hgeom, hspec⟩ := isolating_family38 φ.1 φ.2
  have hpair := (hspec.1 m).2.2.2.2.1
  have hmem := counting_mem_zeroMultiset38 (canonicalCountingCutoff_spec38 φ.1).1
    (discC φ.1 m) (discR φ.1 m) z
  have hmemPair :
      z ∈ Lib.zeroMultiset (perChar φ.1) (ball (discC φ.1 m) (discR φ.1 m)) ↔
        z = lamMinus φ.1 m ∨ z = lamPlus φ.1 m := by
    rw [← hpair]
    simp
  constructor
  · intro hzero
    exact hmemPair.mp (hmem.mpr ⟨hz, hzero⟩)
  · intro htip
    exact (hmem.mp (hmemPair.mpr htip)).2

theorem rawBetaPerCharNonzeroOnSlit38 (φ : GKPotential38) (m : ℤ) (z : ℂ)
    (hz : z ∈ GKOriginalSlit38 φ m) : perChar φ.1 z ≠ 0 := by
  change z ∈ ball (discC φ.1 m) (discR φ.1 m) \
    segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m) at hz
  intro hzero
  rcases (rawBetaPerCharZeroInDiscIff38 φ m z hz.1).mp hzero with hminus | hplus
  · apply hz.2
    rw [hminus]
    exact left_mem_segment ℝ _ _
  · apply hz.2
    rw [hplus]
    exact right_mem_segment ℝ _ _

theorem rawBetaPerCharLowerTipZero38 (φ : GKPotential38) (m : ℤ) :
    perChar φ.1 (lamMinus φ.1 m) = 0 := by
  exact (lamSeq_enumeration38 φ.1).1 (2 * m)

theorem rawBetaDirichletTerminalSquare38 (φ : GKPotential38) (m : ℤ) :
    antiDiscrim φ.1 (muSeq φ.1 m) ^ 2 = perChar φ.1 (muSeq φ.1 m) := by
  exact (dirichlet_perChar_eq_anti_sq38 φ.1 (muSeq φ.1 m)
    (muSeq_root38 φ.1 m)).symm

end
end NlsGge.GK38

#check @NlsGge.GK38.rawBetaPerCharZeroInDiscIff38
#print axioms NlsGge.GK38.rawBetaPerCharZeroInDiscIff38
#check @NlsGge.GK38.rawBetaPerCharNonzeroOnSlit38
#print axioms NlsGge.GK38.rawBetaPerCharNonzeroOnSlit38
#check @NlsGge.GK38.rawBetaPerCharLowerTipZero38
#print axioms NlsGge.GK38.rawBetaPerCharLowerTipZero38
#check @NlsGge.GK38.rawBetaDirichletTerminalSquare38
#print axioms NlsGge.GK38.rawBetaDirichletTerminalSquare38
