import Mathlib
import NlsGge.Atomic.M.M009Host

/- M-009 SUPPORT02 (proof development, AUTHOR; not reviewed).  Stage 2 leaves of Pro round 13 section 11:
   lower_endpoint_mem, upper_endpoint_mem, finite_chain_integral_unique (heads verbatim). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.MPrimitive

theorem lower_endpoint_mem (φ : PotPair) (n : ℤ) :
  lamMinus φ n ∈ endpointClosureFiber φ :=
  Or.inr ⟨n, Or.inl rfl⟩

theorem upper_endpoint_mem (φ : PotPair) (n : ℤ) :
  lamPlus φ n ∈ endpointClosureFiber φ :=
  Or.inr ⟨n, Or.inr rfl⟩

theorem endpoint_filter_neBot :
    NeBot (𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}] ((0 : ℝ), (0 : ℝ))) := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  have hmem : ∀ n : ℕ, ((1 : ℝ) / ((n : ℝ) + 3), (1 : ℝ) / ((n : ℝ) + 3)) ∈
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1} := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    refine ⟨by positivity, by positivity, ?_⟩
    have : (1 : ℝ) / ((n : ℝ) + 3) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    show 1 / ((n : ℝ) + 3) + 1 / ((n : ℝ) + 3) < 1
    linarith
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)
  have h : Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 3), (1 : ℝ) / ((n : ℝ) + 3)))
      atTop (𝓝 ((0 : ℝ), (0 : ℝ))) := h0.prodMk_nhds h0
  exact mem_closure_of_tendsto h (Eventually.of_forall hmem)

theorem endpoint_integral_unique (φ : PotPair) (p : ℝ → ℂ) (a b : ℂ)
    (ha : MContour.HasEndpointIntegral φ p a)
    (hb : MContour.HasEndpointIntegral φ p b) : a = b := by
  have := endpoint_filter_neBot
  exact tendsto_nhds_unique ha.2 hb.2

theorem finite_chain_integral_unique
    (φ : PotPair) (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ)
    (A B : ℂ)
    (hA : MContour.HasFiniteChainIntegral φ m p A)
    (hB : MContour.HasFiniteChainIntegral φ m p B) :
  A = B := by
  obtain ⟨I, hI, rfl⟩ := hA
  obtain ⟨J, hJ, rfl⟩ := hB
  exact Finset.sum_congr rfl fun i _ => endpoint_integral_unique φ (p i) _ _ (hI i) (hJ i)

end NlsGge.ThirdConsultation.MPrimitive
