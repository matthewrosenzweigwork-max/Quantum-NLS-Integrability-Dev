import NlsGge.Schur.ActualSchurOffDiagonalRemainder38V1
import NlsGge.Schur.OwnModeSequence

/-!
# Own-mode variation `H_n` of the actual paired potential (NEW-F04.01-.03)

Source: `paper/v2.tex` lines 1184-1192.  `H_n` is the actual paired potential
`V(p)` at `p = (e_n, 0)`, where `e_n` is the `n`-th unit vector of the weighted
`H¹` carrier.  Its Hilbert-basis entries are exactly `[b = + ∧ c = - ∧ m + l = 2n]`,
it is a partial isometry (norm `≤ 1`), and `Q H_n P = 0 = P H_n Q`.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

theorem actualH1ModeVector38_coordinates (n : ℤ) :
    weightedCoordinates (sobolevModeWeight (1 : ℝ))
        (fun k : ℤ => if k = n then (1 : ℂ) else 0) =
      Pi.single n ((Real.sqrt (sobolevModeWeight (1 : ℝ) n) : ℂ)) := by
  funext k
  by_cases hk : k = n
  · subst hk; simp [weightedCoordinates]
  · simp [weightedCoordinates, hk]

theorem actualH1ModeVector38_memℓp (n : ℤ) :
    Memℓp (weightedCoordinates (sobolevModeWeight (1 : ℝ))
        (fun k : ℤ => if k = n then (1 : ℂ) else 0)) 2 := by
  rw [actualH1ModeVector38_coordinates]
  exact lp.memℓp (lp.single (E := fun _ : ℤ => ℂ) 2 n
    ((Real.sqrt (sobolevModeWeight (1 : ℝ) n) : ℂ)))

/-- The `n`-th unit vector of the weighted `H¹` carrier. -/
def actualH1ModeVector38 (n : ℤ) : WeightedHilbert (sobolevModeWeight (1 : ℝ)) :=
  ⟨fun k => if k = n then 1 else 0, actualH1ModeVector38_memℓp n⟩

theorem actualH1ModeVector38_apply (n k : ℤ) :
    (actualH1ModeVector38 n) k = if k = n then 1 else 0 := rfl

/-- The own-mode variation `H_n = V((e_n, 0))`. -/
def actualOwnModeVariation38 (n : ℤ) : ParityPair n →L[ℂ] ParityPair n :=
  actualParityPairPotentialParameterAfterScalarWrapperCLM23 n
    (actualH1ModeVector38 n, 0)

theorem actualOwnModeVariation38_entry (n : ℤ) (b c : Bool) (m l : Sector n) :
    inner ℂ (parityPairVector n (b, m))
      (actualOwnModeVariation38 n (parityPairVector n (c, l))) =
      if b = true ∧ c = false ∧ m.val + l.val = 2 * n then 1 else 0 := by
  unfold actualOwnModeVariation38
  rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply,
    actualPotentialTranspose_pair_entry_formula24]
  have hm := m.property
  have hl := l.property
  simp only [physicalH1ComplexCarrierToL2Actual22_fourier, actualH1ModeVector38_apply]
  have hz : ∀ k : ℤ, ((0 : WeightedHilbert (sobolevModeWeight (1 : ℝ))) : ℤ → ℂ) k = 0 :=
    fun _ => rfl
  cases b <;> cases c
  · simp
  · simp [hz]
  · by_cases h : m.val + l.val = 2 * n
    · simp [h]
    · have h2 : ¬ (m.val + l.val) / 2 = n := by omega
      simp [h, h2]
  · simp

theorem parityPairRepr_eq_inner38 (n : ℤ) (f : ParityPair n) (i : Bool × Sector n) :
    parityPairRepr n f i = inner ℂ (parityPairVector n i) f := by
  change (parityPairFourierBasis n).repr f i = _
  rw [HilbertBasis.repr_apply_apply]
  simp only [parityPairFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem actualOwnModeVariation38_hasSum_inner (n : ℤ) (x : ParityPair n)
    (i : Bool × Sector n) :
    HasSum (fun j : Bool × Sector n =>
        parityPairRepr n x j * inner ℂ (parityPairVector n i)
          (actualOwnModeVariation38 n (parityPairVector n j)))
      (inner ℂ (parityPairVector n i) (actualOwnModeVariation38 n x)) := by
  have hb : ∀ j, parityPairFourierBasis n j = parityPairVector n j := by
    intro j
    simp [parityPairFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  have h0 := (parityPairFourierBasis n).hasSum_repr x
  have h1 := (innerSL ℂ (parityPairVector n i)).hasSum
    ((actualOwnModeVariation38 n).hasSum h0)
  simpa [innerSL_apply_apply, hb, inner_smul_right, parityPairRepr] using h1

theorem actualOwnModeVariation38_repr (n : ℤ) (x : ParityPair n) :
    parityPairRepr n (actualOwnModeVariation38 n x) =
      ownModeSquare n (parityPairRepr n x) := by
  ext ⟨b, m⟩
  rw [parityPairRepr_eq_inner38]
  have hs := actualOwnModeVariation38_hasSum_inner n x (b, m)
  cases b
  · have hz : HasSum (fun j : Bool × Sector n =>
        parityPairRepr n x j * inner ℂ (parityPairVector n (false, m))
          (actualOwnModeVariation38 n (parityPairVector n j))) 0 := by
      have : (fun j : Bool × Sector n =>
          parityPairRepr n x j * inner ℂ (parityPairVector n (false, m))
            (actualOwnModeVariation38 n (parityPairVector n j))) = fun _ => 0 := by
        funext ⟨c, l⟩
        rw [actualOwnModeVariation38_entry]
        simp
      rw [this]
      exact hasSum_zero
    rw [hs.unique hz]
    rfl
  · have hsingle : HasSum (fun j : Bool × Sector n =>
        parityPairRepr n x j * inner ℂ (parityPairVector n (true, m))
          (actualOwnModeVariation38 n (parityPairVector n j)))
        (parityPairRepr n x (false, reflectIndex n m) * 1) := by
      have h := hasSum_single (f := fun j : Bool × Sector n =>
        parityPairRepr n x j * inner ℂ (parityPairVector n (true, m))
          (actualOwnModeVariation38 n (parityPairVector n j)))
        (false, reflectIndex n m) (by
          rintro ⟨c, l⟩ hne
          rw [actualOwnModeVariation38_entry]
          have : ¬ (c = false ∧ m.val + l.val = 2 * n) := by
            rintro ⟨rfl, hml⟩
            apply hne
            have : l = reflectIndex n m := by
              apply Subtype.ext
              simp only [reflectIndex_val]
              omega
            rw [this]
          simp [this])
      rw [actualOwnModeVariation38_entry] at h
      simpa using h
    rw [hs.unique hsingle]
    simp [ownModeSquare_upper_apply]

/-- `H_n` is a contraction (indeed a partial isometry). -/
theorem actualOwnModeVariation38_norm_le_one (n : ℤ) :
    ‖actualOwnModeVariation38 n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [← (parityPairRepr n).norm_map (actualOwnModeVariation38 n x),
    actualOwnModeVariation38_repr, ← (parityPairRepr n).norm_map x]
  calc ‖ownModeSquare n (parityPairRepr n x)‖
      ≤ ‖ownModeSquare n‖ * ‖parityPairRepr n x‖ := (ownModeSquare n).le_opNorm _
    _ ≤ 1 * ‖parityPairRepr n x‖ :=
        mul_le_mul_of_nonneg_right (ownModeSquare_norm_le_one n) (norm_nonneg _)

theorem resonantParityPair_repr38 (n : ℤ) (x : ParityPair n) :
    parityPairRepr n (resonantParityPair n x) = resonantSquare n (parityPairRepr n x) := by
  change (parityPairRepr n) ((parityPairRepr n).symm
    (resonantSquare n (parityPairRepr n x))) = _
  exact (parityPairRepr n).apply_symm_apply _

theorem complementaryProjectionTransported_repr38 (n : ℤ) (x : ParityPair n) :
    parityPairRepr n (freeResolventComplementaryProjectionTransported n x) =
      complementarySquare n (parityPairRepr n x) := by
  change (parityPairRepr n) ((parityPairRepr n).symm
    (complementarySquare n (parityPairRepr n x))) = _
  exact (parityPairRepr n).apply_symm_apply _

/-- `Q H_n P = 0` (F:eq:crosszero, first identity). -/
theorem actualOwnModeVariation38_Q_H_P (n : ℤ) :
    (freeResolventComplementaryProjectionTransported n).comp
      ((actualOwnModeVariation38 n).comp (resonantParityPair n)) = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply (parityPairRepr n).injective
  simp only [ContinuousLinearMap.comp_apply, zero_apply, map_zero]
  rw [complementaryProjectionTransported_repr38, actualOwnModeVariation38_repr,
    resonantParityPair_repr38]
  have := congrArg (fun T => T (parityPairRepr n x))
    (complementary_ownModeSquare_resonant_zero n)
  simpa using this

/-- `P H_n Q = 0` (F:eq:crosszero, second identity). -/
theorem actualOwnModeVariation38_P_H_Q (n : ℤ) :
    (resonantParityPair n).comp
      ((actualOwnModeVariation38 n).comp
        (freeResolventComplementaryProjectionTransported n)) = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply (parityPairRepr n).injective
  simp only [ContinuousLinearMap.comp_apply, zero_apply, map_zero]
  rw [resonantParityPair_repr38, actualOwnModeVariation38_repr,
    complementaryProjectionTransported_repr38]
  have := congrArg (fun T => T (parityPairRepr n x))
    (resonant_ownModeSquare_complementary_zero n)
  simpa using this

/-- The `(+,-)` resonant entry of `H_n` is one. -/
theorem actualOwnModeVariation38_resonant_plusMinus (n : ℤ) :
    inner ℂ (parityPairVector n (true, resonantIndex n))
      (actualOwnModeVariation38 n (parityPairVector n (false, resonantIndex n))) = 1 := by
  rw [actualOwnModeVariation38_entry]
  simp [resonantIndex]
  omega

/-- The other three resonant entries of `H_n` vanish. -/
theorem actualOwnModeVariation38_resonant_other (n : ℤ) (b c : Bool)
    (h : ¬ (b = true ∧ c = false)) :
    inner ℂ (parityPairVector n (b, resonantIndex n))
      (actualOwnModeVariation38 n (parityPairVector n (c, resonantIndex n))) = 0 := by
  rw [actualOwnModeVariation38_entry]
  have h' : ¬ (b = true ∧ c = false ∧ (resonantIndex n).val + (resonantIndex n).val = 2 * n) :=
    fun h'' => h ⟨h''.1, h''.2.1⟩
  simp only [h', ite_false]

end NlsGge.Schur
