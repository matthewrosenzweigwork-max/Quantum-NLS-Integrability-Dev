import Mathlib
import NlsGge.Atomic.M.M009Host
import NlsGge.GK38.IsolatingTopology

/- M016 DENSITY PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016Density.lean. `cutFree_nhdsWithin_neBot`: for φ ∈ gkW, (𝓝[cutFreeFiber φ] z).NeBot at every z of the
   endpoint-closure fiber (endpoints are approached transversally inside their isolating disc; other cuts lie in disjoint
   discs). Discharges the density hypothesis of M.primitive_discriminant_identity_of.
   Lane: M016Dense_RUN01 997fb9a0, exit 0 (verbatim copies of M009Host's two fiber definitions), axioms
   [propext, Classical.choice, Quot.sound]. The split file needs a ROOT MAIN PROBE (M009Host absent from mirror). -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M016ChartAux

open NlsGge.ThirdConsultation.MPrimitive

theorem off_segment (a b z v : ℂ) (hz : z = a ∨ z = b)
    (hv : v = if b = a then 1 else Complex.I * (b - a)) (ε : ℝ) (hε : ε ≠ 0) :
    z + (ε : ℂ) * v ∉ segment ℝ a b := by
  intro hmem
  rw [segment_eq_image'] at hmem
  obtain ⟨θ, -, heq⟩ := hmem
  simp only [Complex.real_smul] at heq
  by_cases hab : b = a
  · rw [if_pos hab] at hv
    subst hv
    have hz' : z = a := by rcases hz with h | h <;> [exact h; exact h.trans hab]
    rw [hab, sub_self, mul_zero, add_zero, hz', mul_one] at heq
    have : (ε : ℂ) = 0 := by linear_combination -heq
    exact hε (by exact_mod_cast this)
  · rw [if_neg hab] at hv
    subst hv
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
    obtain ⟨c, hc⟩ : ∃ c : ℂ, z = a + c * (b - a) ∧ c.im = 0 := by
      rcases hz with h | h
      · exact ⟨0, by rw [h]; ring, rfl⟩
      · exact ⟨1, by rw [h]; ring, rfl⟩
    rw [hc.1] at heq
    have hmul : ((θ : ℂ) - c - (ε : ℂ) * Complex.I) * (b - a) = 0 := by
      linear_combination heq
    have h0 := (mul_eq_zero.mp hmul).resolve_right hba
    have him := congrArg Complex.im h0
    simp [hc.2] at him
    exact hε him

/-- **Density** of the cut-free fiber at every point of the endpoint-closure fiber. -/
theorem cutFree_nhdsWithin_neBot (φ : PotPair) (hW : φ ∈ gkW) (z : ℂ)
    (hz : z ∈ endpointClosureFiber φ) : (𝓝[cutFreeFiber φ] z).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  rcases hz with hc | ⟨n, hn⟩
  · exact subset_closure hc
  obtain ⟨c0, N0, -, hspec⟩ := isolating_family38 φ hW
  have hseg : ∀ j : ℤ, segment ℝ (lamMinus φ j) (lamPlus φ j) ⊆ discU φ j := fun j => (hspec.1 j).1
  have hzU : z ∈ discU φ n := hseg n (by
    rcases hn with h | h
    · rw [h]; exact left_mem_segment ℝ _ _
    · rw [h]; exact right_mem_segment ℝ _ _)
  set v : ℂ := if lamPlus φ n = lamMinus φ n then 1 else Complex.I * (lamPlus φ n - lamMinus φ n) with hv
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (Metric.isOpen_ball : IsOpen (discU φ n)) z hzU
  set ε : ℝ := min δ r / (2 * (‖v‖ + 1)) with hεdef
  have hm : 0 < min δ r := lt_min hδ hr
  have hε : 0 < ε := by positivity
  have hsmall : ‖(ε : ℂ) * v‖ < min δ r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le, hεdef]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have hwU : z + (ε : ℂ) * v ∈ discU φ n := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hsmall (min_le_right _ _))
  refine ⟨z + (ε : ℂ) * v, ?_, ?_⟩
  · simp only [cutFreeFiber, gapSegments38, mem_setOf_eq, mem_iUnion, not_exists]
    intro j hj
    by_cases hjn : j = n
    · subst hjn
      exact off_segment _ _ z v (hn.imp id id) hv ε hε.ne' hj
    · exact Set.disjoint_left.mp ((isolating φ hW).1 hjn) (hseg j hj) hwU
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
    exact lt_of_lt_of_le hsmall (min_le_left _ _)

end NlsGge.ThirdConsultation.M016ChartAux
