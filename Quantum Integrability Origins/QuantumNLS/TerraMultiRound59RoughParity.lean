import QuantumNLS.TerraMultiRound59TreeForm
import QuantumNLS.TerraMultiRound59SmoothDensity

/-! Field continuity and density transfer of the coefficient parity. -/
set_option autoImplicit false
noncomputable section
open Set Topology
namespace QuantumNLS.TerraMultiRound59RoughParity
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TerraMultiRound57LevelPowers QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59TreeForm QuantumNLS.TerraMultiRound59SmoothDensity
open QuantumNLS.TerraMultiRound58AbsoluteParity

variable {L : ℝ} [Fact (0 < L)]

theorem tree_coefficient_field_continuous {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) (s n : ℕ)
    (hn : n ≤ 2 * k + 3) :
    Continuous (fun x : Ell2 => treeCoefficient (L := L) (k := k) κ x s n) := by
  unfold treeCoefficient levelCoeff
  apply continuous_finsetSum
  intro ell hell
  have he := Finset.mem_Ico.mp hell
  apply continuous_finsetSum
  intro d hd
  split_ifs with h
  · have hdk : d ≤ 2 * k := by omega
    apply continuous_finsetSum
    intro t ht
    have hc : Continuous (fun x : Ell2 => treeForm (L := L) hk hdk t (fun _ => x)) :=
      (treeForm (L := L) hk hdk t).cont.comp (continuous_pi (fun _ => continuous_id))
    simp only [treeForm_diagonal] at hc
    exact continuous_const.mul hc
  · exact continuous_const

theorem rough_tree_coefficient_parity (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (x : Ell2) :
    (∀ m : ℕ, 2 * m + 2 ≤ 2 * s + 1 →
      (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 2)).re = 0) ∧
    (∀ m : ℕ, 2 * m + 1 ≤ 2 * s + 1 →
      (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 1)).im = 0) := by
  constructor
  · intro m hm
    let S : Set Ell2 := {x | (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 2)).re = 0}
    have hc : IsClosed S := isClosed_eq
      (Complex.continuous_re.comp (tree_coefficient_field_continuous (L := L) (k := s - 1) (by omega) κ s _ (by omega))) continuous_const
    have hd : {x : Ell2 | QuantumNLS.ClassicalCharges.SmoothPeriodic L (physRep L (s - 1 : ℕ) x)} ⊆ S := by
      intro y hy
      exact (smooth_tree_coefficient_parity L s hs κ hκ y _ rfl hy).1 m hm
    exact closure_minimal hd hc (dense_smooth L (s - 1 : ℕ) x)
  · intro m hm
    let S : Set Ell2 := {x | (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 1)).im = 0}
    have hc : IsClosed S := isClosed_eq
      (Complex.continuous_im.comp (tree_coefficient_field_continuous (L := L) (k := s - 1) (by omega) κ s _ (by omega))) continuous_const
    have hd : {x : Ell2 | QuantumNLS.ClassicalCharges.SmoothPeriodic L (physRep L (s - 1 : ℕ) x)} ⊆ S := by
      intro y hy
      exact (smooth_tree_coefficient_parity L s hs κ hκ y _ rfl hy).2 m hm
    exact closure_minimal hd hc (dense_smooth L (s - 1 : ℕ) x)

#print axioms tree_coefficient_field_continuous
#print axioms rough_tree_coefficient_parity
end QuantumNLS.TerraMultiRound59RoughParity
