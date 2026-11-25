import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationC3
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # One product-Borel frequency family on the full action carrier

Use the countable strata indexed by the exact finite support of an action
sequence. Each stratum contributes its explicit square-root-section frequency.
At most one summand is nonzero; off all finite-support strata every summand is
zero. Zero-padding coherence identifies this family with every finite plane.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Birkhoff

/-- The stratum of real action sequences whose exact nonzero support is Λ.
No sign restriction is imposed outside the physical nonnegative action cone. -/
def finiteActionStratum38 (Λ : Finset ℤ) : Set (ℤ → ℝ) :=
  {a | ∀ n, a n ≠ 0 ↔ n ∈ Λ}

/-- Exact finite-support strata are product-Borel, as countable intersections
of coordinate equalities or inequalities. -/
theorem measurableSet_finiteActionStratum38 (Λ : Finset ℤ) :
    MeasurableSet (finiteActionStratum38 Λ) := by
  classical
  unfold finiteActionStratum38
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  by_cases hn : n ∈ Λ
  · simpa only [hn, iff_true, Set.compl_ofPred] using
      (measurableSet_eq_fun (measurable_pi_apply n) (measurable_const : Measurable (fun _ : ℤ → ℝ => (0 : ℝ)))).compl
  · simpa only [hn, iff_false, not_not] using
      (measurableSet_eq_fun (measurable_pi_apply n) (measurable_const : Measurable (fun _ : ℤ → ℝ => (0 : ℝ))))

/-- An action sequence belongs to at most one exact-support stratum. -/
theorem finiteActionStratum_unique38 (Λ Γ : Finset ℤ) (a : ℤ → ℝ)
    (hΛ : a ∈ finiteActionStratum38 Λ) (hΓ : a ∈ finiteActionStratum38 Γ) : Λ = Γ := by
  apply Finset.ext
  intro n
  exact (hΛ n).symm.trans (hΓ n)

/-- The contribution of one finite-support stratum to a coordinate frequency;
an integer outside that finite plane contributes zero. -/
def finiteGapFrequencyTerm38 (n : ℤ) (Λ : Finset ℤ) (a : ℤ → ℝ) : ℝ := by
  classical
  exact if a ∈ finiteActionStratum38 Λ then
    if hn : n ∈ Λ then finitePlaneFrequency38 Λ ⟨n, hn⟩ a else 0
  else 0

/-- Every stratum contribution is measurable without choosing a measurable
support selector. -/
theorem measurable_finiteGapFrequencyTerm38 (n : ℤ) (Λ : Finset ℤ) :
    Measurable (finiteGapFrequencyTerm38 n Λ) := by
  classical
  unfold finiteGapFrequencyTerm38
  apply Measurable.ite (measurableSet_finiteActionStratum38 Λ) _ measurable_const
  by_cases hn : n ∈ Λ
  · simpa only [dite_eq_left hn] using measurable_finitePlaneFrequency38 Λ ⟨n, hn⟩
  · simpa only [dite_eq_right hn] using (measurable_const : Measurable (fun _ : ℤ → ℝ => (0 : ℝ)))

/-- The stratum series is summable for every real action sequence: it has at
most one nonzero term. This precedes every use of its real infinite sum. -/
theorem summable_finiteGapFrequencyTerm38 (n : ℤ) (a : ℤ → ℝ) :
    Summable (fun Λ : Finset ℤ => finiteGapFrequencyTerm38 n Λ a) := by
  classical
  apply summable_of_hasFiniteSupport
  by_cases h : ∃ Λ, a ∈ finiteActionStratum38 Λ
  · obtain ⟨Λ, hΛ⟩ := h
    apply (Set.finite_singleton Λ).subset
    intro Γ hΓ
    have ha : a ∈ finiteActionStratum38 Γ := by
      by_contra hn
      exact hΓ (by simp only [finiteGapFrequencyTerm38, ite_eq_right hn])
    exact (finiteActionStratum_unique38 Γ Λ a ha hΛ)
  · have he : (fun Λ : Finset ℤ => finiteGapFrequencyTerm38 n Λ a) = 0 := by
      funext Λ
      simp only [finiteGapFrequencyTerm38, ite_eq_right (fun hΛ => h ⟨Λ, hΛ⟩), Pi.zero_apply]
    rw [he]
    exact Function.hasFiniteSupport_zero

/-- The global coordinate frequency is the sum of the disjoint exact-support
contributions. It is zero on infinite-support action sequences, and on inactive
or nonpositive-action coordinates. -/
def finiteGapFrequency38 (n : ℤ) (a : ℤ → ℝ) : ℝ :=
  ∑' Λ : Finset ℤ, finiteGapFrequencyTerm38 n Λ a

/-- Every coordinate of the SAME global frequency family is product-Borel. -/
theorem measurable_finiteGapFrequency38 (n : ℤ) : Measurable (finiteGapFrequency38 n) :=
  Measurable.tsum (fun Λ => measurable_finiteGapFrequencyTerm38 n Λ)

/-- On its exact finite-support stratum the global family equals that plane's
explicit frequency at each active integer label. -/
theorem finiteGapFrequency_on_stratum38 (n : ℤ) (Λ : Finset ℤ) (a : ℤ → ℝ)
    (ha : a ∈ finiteActionStratum38 Λ) (hn : n ∈ Λ) :
    finiteGapFrequency38 n a = finitePlaneFrequency38 Λ ⟨n, hn⟩ a := by
  classical
  unfold finiteGapFrequency38
  rw [tsum_eq_single Λ]
  · simp only [finiteGapFrequencyTerm38, ite_eq_left ha, dite_eq_left hn]
  · intro Γ hΓ
    have hnot : a ∉ finiteActionStratum38 Γ :=
      fun h => hΓ (finiteActionStratum_unique38 Γ Λ a h ha)
    simp only [finiteGapFrequencyTerm38, ite_eq_right hnot]

/-- The zero extension of a square-root section is independent of the finite
plane whenever the action sequence vanishes outside that plane. -/
theorem extZero_finitePlaneSection38 (Λ : Finset ℤ) (a : ℤ → ℝ)
    (h : ∀ n, n ∉ Λ → a n = 0) :
    extZero38 Λ (finitePlaneSection38 Λ a) = fun n => (Real.sqrt (a n) : ℂ) := by
  funext n
  by_cases hn : n ∈ Λ
  · rw [extZero38_apply_of_mem _ hn]
    rfl
  · rw [extZero38_apply_of_not_mem _ hn, h n hn, Real.sqrt_zero, Complex.ofReal_zero]

/-- On a common active coordinate, zero padding preserves the explicit
square-root-section frequency. This is a differentiated literal-energy identity. -/
theorem finitePlaneFrequency_eq_of_zero_outside38 (Λ Γ : Finset ℤ) (a : ℤ → ℝ)
    (hΛ : ∀ n, n ∉ Λ → a n = 0) (hΓ : ∀ n, n ∉ Γ → a n = 0)
    (i : Λ) (j : Γ) (hij : i.1 = j.1) :
    finitePlaneFrequency38 Λ i a = finitePlaneFrequency38 Γ j a := by
  have he : extZero38 Λ (finitePlaneSection38 Λ a) =
      extZero38 Γ (finitePlaneSection38 Γ a) := by
    rw [extZero_finitePlaneSection38 Λ a hΛ, extZero_finitePlaneSection38 Γ a hΓ]
  have hY := YLambda_eq_of_extZero38 Λ Γ _ _ he i j hij
  unfold finitePlaneFrequency38
  rw [hij, hY]

set_option maxHeartbeats 400000 in
/-- There is one product-Borel real frequency family for all finite planes.
Its vector identity includes every collapsed and inactive coordinate, with
coherence under zero padding proved above and no measurable choice. -/
theorem exists_measurable_finiteGap_frequencies38 :
    ∃ Ω : ℤ → (ℤ → ℝ) → ℝ, (∀ n, Measurable (Ω n)) ∧
      ∀ (Λ : Finset ℤ) (w : Λ → ℂ) (i : Λ),
        YΛ Λ w i = -Complex.I *
          (Ω i.1 (fun k => ‖extZero38 Λ w k‖ ^ 2) : ℂ) * w i := by
  classical
  refine ⟨finiteGapFrequency38, measurable_finiteGapFrequency38, ?_⟩
  intro Λ w i
  let a : ℤ → ℝ := fun k => ‖extZero38 Λ w k‖ ^ 2
  let S := Λ.filter (fun n => a n ≠ 0)
  have hΛ (n : ℤ) (hn : n ∉ Λ) : a n = 0 := by
    simp only [a, extZero38_apply_of_not_mem _ hn, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hS : a ∈ finiteActionStratum38 S := by
    intro n
    simp only [S, Finset.mem_filter]
    constructor
    · intro hn
      refine ⟨?_, hn⟩
      by_contra hnot
      exact hn (hΛ n hnot)
    · exact And.right
  by_cases hw : w i = 0
  · rw [(YLambda_radial_equivariant38 Λ w w (fun _ => rfl)).2.1 i hw, hw, mul_zero]
  · have ha : a i.1 ≠ 0 := by
      simp only [a, extZero38_apply_of_mem _ i.2]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
    have hi : i.1 ∈ S := (hS i.1).mp ha
    have hzS (n : ℤ) (hn : n ∉ S) : a n = 0 := by
      by_contra h
      exact hn ((hS n).mp h)
    have hf := finiteGapFrequency_on_stratum38 i.1 S a hS hi
    have hc := finitePlaneFrequency_eq_of_zero_outside38 S Λ a hzS hΛ ⟨i.1, hi⟩ i rfl
    change YΛ Λ w i = -Complex.I * (finiteGapFrequency38 i.1 a : ℂ) * w i
    rw [hf, hc]
    exact finitePlaneFrequency_vector38 Λ w i

end LiebLiniger.FixedPeriod.EXT
