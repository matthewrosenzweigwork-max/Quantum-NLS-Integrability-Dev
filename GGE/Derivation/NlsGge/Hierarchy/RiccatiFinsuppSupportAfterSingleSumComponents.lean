import NlsGge.Hierarchy.RiccatiFinsuppSingleSumComponents
import Mathlib.Algebra.MvPolynomial.Degrees

set_option autoImplicit false

/-! Fresh support-prerequisite assembly using direct single-sum component
lemmas. The failed three-attempt monomial helper remains frozen separately. -/

namespace NlsGge.HierarchyRiccati.Core

def riccatiJetWeightHomAfterComponents : (Jet →₀ ℕ) →+ ℕ where
  toFun m := m.sum fun v e => e * (v.2 + 1)
  map_zero' := by simp
  map_add' := by
    intro m n
    exact Finsupp.sum_add_index' (by intro v; simp)
      (by intro v a b; simp [Nat.add_mul])

def riccatiJetGaugeHomAfterComponents : (Jet →₀ ℕ) →+ ℤ where
  toFun m := m.sum fun v e => if v.1 then (e : ℤ) else -(e : ℤ)
  map_zero' := by simp
  map_add' := by
    intro m n
    exact Finsupp.sum_add_index' (by intro v; simp)
      (by
        intro v a b
        by_cases hv : v.1 <;> simp [hv, Int.cast_add] <;> ring)

def riccatiJetBidegreeAfterComponents (m : Jet →₀ ℕ) : ℕ × ℤ :=
  (riccatiJetWeightHomAfterComponents m, riccatiJetGaugeHomAfterComponents m)

def HasRiccatiJetBidegreeAfterComponents (P : Poly) (d : ℕ × ℤ) : Prop :=
  ∀ m ∈ P.support, riccatiJetBidegreeAfterComponents m = d

theorem riccatiJetWeightHomAfterComponents_single (v : Jet) :
    riccatiJetWeightHomAfterComponents (Finsupp.single v 1) = v.2 + 1 := by
  calc
    riccatiJetWeightHomAfterComponents (Finsupp.single v 1) =
        (Finsupp.single v 1).sum (fun (w : Jet) (e : ℕ) => e * (w.2 + 1)) := rfl
    _ = v.2 + 1 := finSingle_one_weight_sum v

theorem riccatiJetGaugeHomAfterComponents_single (v : Jet) :
    riccatiJetGaugeHomAfterComponents (Finsupp.single v 1) =
      if v.1 then 1 else -1 := by
  calc
    riccatiJetGaugeHomAfterComponents (Finsupp.single v 1) =
        (Finsupp.single v 1).sum
          (fun (w : Jet) (e : ℕ) => if w.1 then (e : ℤ) else -(e : ℤ)) := rfl
    _ = if v.1 then 1 else -1 := finSingle_one_gauge_sum v

theorem hasRiccatiJetBidegreeAfterComponents_X (v : Jet) :
    HasRiccatiJetBidegreeAfterComponents (MvPolynomial.X v)
      (v.2 + 1, if v.1 then 1 else -1) := by
  classical
  intro m hm
  have hm' : m = Finsupp.single v 1 := by
    rw [MvPolynomial.support_X] at hm
    exact Finset.mem_singleton.mp hm
  subst m
  simp [riccatiJetBidegreeAfterComponents,
    riccatiJetWeightHomAfterComponents_single,
    riccatiJetGaugeHomAfterComponents_single]

end NlsGge.HierarchyRiccati.Core
