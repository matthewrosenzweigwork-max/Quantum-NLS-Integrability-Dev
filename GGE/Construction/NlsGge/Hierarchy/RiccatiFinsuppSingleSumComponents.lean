import NlsGge.Hierarchy.RiccatiAttachedRecursionCore

set_option autoImplicit false

/-! Minimal component facts for evaluating the weighted and signed gauge sums
on a single formal jet. This isolates `Finsupp.sum` normalization from the
AddMonoidHom structure and the later polynomial-support induction. -/

namespace NlsGge.HierarchyRiccati.Core

def riccatiJetGaugeTerm (v : Jet) (e : ℕ) : ℤ :=
  if v.1 then (e : ℤ) else -(e : ℤ)

def riccatiJetWeightTerm (v : Jet) (e : ℕ) : ℕ :=
  e * (v.2 + 1)

theorem finSingle_one_gauge_sum (v : Jet) :
    (Finsupp.single v 1).sum (fun w e => riccatiJetGaugeTerm w e) =
      if v.1 then 1 else -1 := by
  rw [Finsupp.sum_single_index (h := fun w e => riccatiJetGaugeTerm w e)
    (a := v) (b := 1) (by simp [riccatiJetGaugeTerm])]
  simp [riccatiJetGaugeTerm]

theorem finSingle_one_weight_sum (v : Jet) :
    (Finsupp.single v 1).sum (fun w e => riccatiJetWeightTerm w e) = v.2 + 1 := by
  rw [Finsupp.sum_single_index (h := fun w e => riccatiJetWeightTerm w e)
    (a := v) (b := 1) (by simp [riccatiJetWeightTerm])]
  simp [riccatiJetWeightTerm]

end NlsGge.HierarchyRiccati.Core
