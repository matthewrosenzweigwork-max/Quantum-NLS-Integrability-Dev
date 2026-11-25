import QuantumNLS.TerraMultiRound58SmoothParity

/-! Absolute smooth parity by continuity at zero coupling. -/
set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set
namespace QuantumNLS.TerraMultiRound58AbsoluteParity
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound57LevelPowers
open QuantumNLS.TerraMultiRound57CollectedPowers QuantumNLS.TerraMultiRound58SmoothParity

/-- The finite tree coefficient is continuous as a function of coupling. -/
theorem tree_coefficient_continuous {L : ℝ} [Fact (0 < L)] {k : ℕ}
    (x : Ell2) (s n : ℕ) :
    Continuous (fun κ : ℝ => treeCoefficient (L := L) (k := k) κ x s n) := by
  unfold treeCoefficient levelCoeff
  apply continuous_finsetSum
  intro ell hell
  apply continuous_finsetSum
  intro j hj
  split_ifs
  · apply continuous_finsetSum
    intro t ht
    exact (((Complex.continuous_ofReal.neg).pow t.numNodes).mul continuous_const)
  · exact continuous_const

/-- Every retained tree coefficient vanishes at zero coupling. -/
theorem tree_coefficient_zero_coupling {L : ℝ} [Fact (0 < L)] {k : ℕ}
    (x : Ell2) (s n : ℕ) : treeCoefficient (L := L) (k := k) 0 x s n = 0 := by
  unfold treeCoefficient levelCoeff
  apply Finset.sum_eq_zero
  intro ell hell
  have hell' := Finset.mem_Ico.mp hell
  apply Finset.sum_eq_zero
  intro j hj
  split_ifs
  · apply Finset.sum_eq_zero
    intro t ht
    have he := BinaryTree.mem_treesOfNumNodesEq.mp ht
    have hp : 0 < t.numNodes := by omega
    simp [zero_pow (Nat.ne_of_gt hp)]
  · rfl

/-- A continuous real function which vanishes for positive arguments vanishes at zero. -/
lemma continuous_zero_of_pos (g : ℝ → ℝ) (hg : Continuous g)
    (hz : ∀ y : ℝ, 0 < y → g y = 0) : g 0 = 0 := by
  have hc : IsClosed {y : ℝ | g y = 0} := isClosed_eq hg continuous_const
  have hsub : Set.Ioi (0 : ℝ) ⊆ {y : ℝ | g y = 0} := by
    intro y hy
    exact hz y hy
  have hmem : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact show (0 : ℝ) ≤ 0 from le_rfl
  exact closure_minimal hsub hc hmem

/-- On smooth data the real parts at positive even powers and the imaginary
parts at odd powers vanish. -/
theorem smooth_tree_coefficient_parity (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (x : Ell2) (f : ℝ → ℂ)
    (hrep : physRep L (s - 1 : ℕ) x = f) (hf : SmoothPeriodic L f) :
    (∀ m : ℕ, 2 * m + 2 ≤ 2 * s + 1 →
      (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 2)).re = 0) ∧
    (∀ m : ℕ, 2 * m + 1 ≤ 2 * s + 1 →
      (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 1)).im = 0) := by
  constructor
  · intro m hm
    let g : ℝ → ℝ := fun η => (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 2) -
      treeCoefficient (L := L) (k := s - 1) η x s (2 * m + 2)).re
    have hg : Continuous g := Complex.continuous_re.comp
      (continuous_const.sub (tree_coefficient_continuous (L := L) (k := s - 1) x s _))
    have hz : ∀ η : ℝ, 0 < η → g η = 0 := by
      intro η hη
      exact (relative_tree_coefficient_parity L s hs κ η hκ hη x f hrep hf).1 m hm
    have h := continuous_zero_of_pos g hg hz
    simpa [g, tree_coefficient_zero_coupling] using h
  · intro m hm
    let g : ℝ → ℝ := fun η => (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 1) -
      treeCoefficient (L := L) (k := s - 1) η x s (2 * m + 1)).im
    have hg : Continuous g := Complex.continuous_im.comp
      (continuous_const.sub (tree_coefficient_continuous (L := L) (k := s - 1) x s _))
    have hz : ∀ η : ℝ, 0 < η → g η = 0 := by
      intro η hη
      exact (relative_tree_coefficient_parity L s hs κ η hκ hη x f hrep hf).2 m hm
    have h := continuous_zero_of_pos g hg hz
    simpa [g, tree_coefficient_zero_coupling] using h

#print axioms tree_coefficient_continuous
#print axioms tree_coefficient_zero_coupling
#print axioms continuous_zero_of_pos
#print axioms smooth_tree_coefficient_parity
end QuantumNLS.TerraMultiRound58AbsoluteParity
