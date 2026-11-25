/-
QuantumNLS.PlacementProduct — actual union/overlap grouping for LOCAL-011.

The local kernel is the normalized average of the concrete ordered placement
products on the union slots.  Its definition uses only the finite union
configuration and therefore does not depend on the ambient particle number.
-/
import QuantumNLS.PlacementOverlap

set_option linter.style.haveILetI false

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap

noncomputable section

namespace QuantumNLS.PlacementProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The number of union slots in a pair of placements with intersection `s`.
-/
def unionSize (p q s : ℕ) : ℕ := p + (q - s)

/-- A local overlap configuration is a subtype of the finite pair of
placement families; its extra fields are propositions. -/
noncomputable instance overlapConfigurationFintype {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q) :
    Fintype (OverlapConfiguration p q s hsp hsq) := by
  classical
  let f : OverlapConfiguration p q s hsp hsq →
      PlacementSubset p (q - s) × PlacementSubset q (p - s) :=
    fun C => (C.left, C.right)
  have hf : Function.Injective f := by
    intro C D h
    cases C with
    | mk Cl Cr Cinter Ccover =>
      cases D with
      | mk Dl Dr Dinter Dcover =>
        simp only [f, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
  letI : Finite (OverlapConfiguration p q s hsp hsq) := Finite.of_injective f hf
  exact Fintype.ofFinite _

/-- Every feasible overlap type has a concrete representative on its union
slots.  This supplies the nonempty index needed for the local average. -/
theorem overlapConfiguration_nonempty {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q) :
    Nonempty (OverlapConfiguration p q s hsp hsq) := by
  classical
  have hp : p ≤ p + (q - s) := by omega
  have hq : q ≤ p + (q - s) := by omega
  have hrest : q - s ≤ p + (q - s) - p := by omega
  obtain ⟨C, _⟩ : ∃ C : ActualOverlapConfiguration (p + (q - s)) p q s,
      C.left = Finset.univ.map (Fin.castLEEmb hp) :=
    exists_actualOverlapConfiguration hp hsp hsq hrest
  let e := overlapSlotEquiv hsp hsq
  let right : Finset (Fin (q + (p - s))) := C.right.map e.symm.toEmbedding
  have hright : right.card = q := by
    change (C.right.map e.symm.toEmbedding).card = q
    rw [Finset.card_map]
    exact C.right_card
  have hmap : right.map e.toEmbedding = C.right := by
    change (C.right.map e.symm.toEmbedding).map e.toEmbedding = C.right
    rw [Finset.map_map]
    simp [e]
  have hunion : C.left ∪ C.right =
      (Finset.univ : Finset (Fin (p + (q - s)))) := by
    apply (C.left ∪ C.right).card_eq_iff_eq_univ.mp
    calc
      (C.left ∪ C.right).card = p + q - s := C.union_card
      _ = p + (q - s) := by omega
      _ = Fintype.card (Fin (p + (q - s))) := by simp
  refine ⟨⟨⟨C.left, ?_⟩, ⟨right, hright⟩, ?_, ?_⟩⟩
  · exact C.left_card
  · change (C.left ∩ right.map e.toEmbedding).card = s
    rw [hmap]
    exact C.intersection_card
  · change C.left ∪ right.map e.toEmbedding = (Finset.univ : Finset (Fin (p + (q - s))))
    rw [hmap]
    exact hunion

private theorem pair_union_eq_univ {N p q s : ℕ} (S T : Finset (Fin N))
    (hS : S.card = p) (hT : T.card = q)
    (hI : (S ∩ T).card = s) (hN : N = p + q - s) :
    S ∪ T = Finset.univ := by
  apply (S ∪ T).card_eq_iff_eq_univ.mp
  have hcard := Finset.card_inter_add_card_union S T
  rw [hS, hT, hI] at hcard
  have hU : (S ∪ T).card = N := by omega
  simpa using hU

/-- A local overlap configuration is equivalently a left placement and a
right subset in its actual overlap fiber.  The union condition is forced by
the cardinalities, rather than installed as extra combinatorial data. -/
noncomputable def overlapConfigurationFiberEquiv {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q) :
    OverlapConfiguration p q s hsp hsq ≃
      Σ S : PlacementSubset p (q - s),
        {Q : Finset (Fin (p + (q - s))) // Q ∈ overlapFiber S.1 q s} := by
  classical
  let e := overlapSlotEquiv hsp hsq
  refine Equiv.ofBijective ?f ?hf
  · intro C
    refine ⟨C.left, ⟨C.right.1.map e.toEmbedding, ?_⟩⟩
    rw [overlapFiber, Finset.mem_filter]
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · exact Finset.subset_univ _
      · simpa using C.right.2
    · exact C.overlap_card
  · constructor
    · intro C D h
      cases C with
      | mk Cl Cr Ci Cu =>
        cases D with
        | mk Dl Dr Di Du =>
          simp only [Sigma.mk.inj_iff] at h
          rcases h with ⟨hleft, hright⟩
          subst Dl
          have hrightEq := eq_of_heq hright
          have hpair : Cr.1.map e.toEmbedding = Dr.1.map e.toEmbedding :=
            congrArg Subtype.val hrightEq
          have hraw : Cr.1 = Dr.1 := Finset.map_injective e.toEmbedding hpair
          have hsub : Cr = Dr := Subtype.ext hraw
          cases hsub
          rfl
    · intro y
      rcases y with ⟨S, ⟨Q, hQ⟩⟩
      rw [overlapFiber, Finset.mem_filter] at hQ
      rcases hQ with ⟨hQcard, hI⟩
      let e := overlapSlotEquiv hsp hsq
      let R := Q.map e.symm.toEmbedding
      let Rlocal := R.map e.toEmbedding
      have hRcard : R.card = q := by
        change (Q.map e.symm.toEmbedding).card = q
        rw [Finset.card_map]
        exact (Finset.mem_powersetCard.mp hQcard).2
      have hmap : R.map e.toEmbedding = Q := by
        change (Q.map e.symm.toEmbedding).map e.toEmbedding = Q
        rw [Finset.map_map]
        simp [e]
      have hRlocalCard : Rlocal.card = q := by simp [Rlocal, hRcard]
      have hcover : S.1 ∪ Rlocal = Finset.univ := by
        apply pair_union_eq_univ (s := s) S.1 Rlocal S.2 hRlocalCard ?_ (by omega)
        change (S.1 ∩ R.map e.toEmbedding).card = s
        rw [hmap]
        exact hI
      refine ⟨⟨S, ⟨R, hRcard⟩, ?_, hcover⟩, ?_⟩
      · rw [hmap]
        exact hI
      · apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Subtype.ext
          change R.map e.toEmbedding = Q
          exact hmap

/-- There are `choose(p+q-s,p) * choose(p,s)` actual pair configurations on
the union: choose the left subset, then its shared `s` slots. -/
theorem card_overlapConfiguration {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q) :
    Fintype.card (OverlapConfiguration p q s hsp hsq) =
      Nat.choose (p + (q - s)) p * Nat.choose p s := by
  classical
  rw [Fintype.card_congr (overlapConfigurationFiberEquiv hsp hsq),
    Fintype.card_sigma]
  have hfiber (S : PlacementSubset p (q - s)) :
      Fintype.card {Q : Finset (Fin (p + (q - s))) //
        Q ∈ overlapFiber S.1 q s} = Nat.choose p s := by
    rw [Fintype.card_coe, card_overlapFiber S.1 S.2 hsq]
    simp
  simp_rw [hfiber]
  simp

/-- Averaging the actual ordered pair-placement products over all concrete
configurations on their union.  The denominator is the number of such
configurations, so this is a genuine average, not an unnormalized sum.
-/
def averagedOverlapKernel {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    BoundedSymmetricKernel H (unionSize p q s) := by
  letI : Fintype (OverlapConfiguration p q s hsp hsq) := Fintype.ofFinite _
  let r := unionSize p q s
  let hsize : p + (q - s) = r := rfl
  let kernel : SymSector ℂ H r →L[ℂ] SymSector ℂ H r :=
    ((Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ)⁻¹) •
      ∑ C : OverlapConfiguration p q s hsp hsq,
        castSymSectorOperator hsize (overlapFusionKernel C A B)
  exact kernel

/-- The local union kernel is source-normalized by the actual number of
overlap configurations. -/
theorem averagedOverlapKernel_eq_average {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    averagedOverlapKernel hsp hsq A B =
      ((Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ)⁻¹) •
        ∑ C : OverlapConfiguration p q s hsp hsq,
          overlapFusionKernel C A B := by
  rfl

/-- Averaging does not enlarge the local product norm.  The proof uses the
concrete overlap configurations and the frozen contraction estimate for each
ordered placement product. -/
theorem norm_averagedOverlapKernel_le {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    ‖averagedOverlapKernel hsp hsq A B‖ ≤ ‖A‖ * ‖B‖ := by
  letI : Nonempty (OverlapConfiguration p q s hsp hsq) :=
    overlapConfiguration_nonempty hsp hsq
  rw [averagedOverlapKernel_eq_average]
  apply norm_complexAverage_le
  intro C
  simpa using norm_overlapFusionKernel_le C A B

/-- Rewriting the hypergeometric source coefficient by first choosing the
union slots, then its left `p`-subset, then the `s` shared slots gives exactly
the reciprocal-binomial normalization of the two original placements. -/
theorem overlapCoefficient_eq_unionConfigurationNormalization
    {N p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (hr : unionSize p q s ≤ N) :
    overlapCoefficient N p q s =
      ((Nat.choose N (unionSize p q s) : ℝ) *
        (Nat.choose (unionSize p q s) p : ℝ) * (Nat.choose p s : ℝ)) /
        ((Nat.choose N p : ℝ) * (Nat.choose N q : ℝ)) := by
  have hpN : p ≤ N := by
    have hpR : p ≤ unionSize p q s := by dsimp [unionSize]; omega
    exact le_trans hpR hr
  have hqN : q ≤ N := by
    have hqR : q ≤ unionSize p q s := by dsimp [unionSize]; omega
    exact le_trans hqR hr
  have hpr : p ≤ unionSize p q s := by dsimp [unionSize]; omega
  have hchoose : Nat.choose N (unionSize p q s) *
      Nat.choose (unionSize p q s) p =
      Nat.choose N p * Nat.choose (N - p) (q - s) := by
    have h := Nat.choose_mul (n := N) (k := unionSize p q s) (s := p) hpr
    simpa [unionSize, Nat.add_sub_cancel_left] using h
  have hchooseR : (Nat.choose N (unionSize p q s) : ℝ) *
      (Nat.choose (unionSize p q s) p : ℝ) =
      (Nat.choose N p : ℝ) * (Nat.choose (N - p) (q - s) : ℝ) := by
    exact_mod_cast hchoose
  have hdenp : (Nat.choose N p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero hpN)
  have hdenq : (Nat.choose N q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero hqN)
  simp [overlapCoefficient, hsq]
  field_simp [hdenp, hdenq]
  calc
    (Nat.choose p s : ℝ) * (Nat.choose (N - p) (q - s) : ℝ) *
        (Nat.choose N p : ℝ) =
      (Nat.choose p s : ℝ) *
        ((Nat.choose N p : ℝ) * (Nat.choose (N - p) (q - s) : ℝ)) := by ring
    _ = (Nat.choose p s : ℝ) *
        ((Nat.choose N (unionSize p q s) : ℝ) *
          (Nat.choose (unionSize p q s) p : ℝ)) := by rw [← hchooseR]
    _ = _ := by ring

/-- In union-first coordinates, the source probability is the number of
actual local pair configurations times the number of possible unions,
divided by the two original subset counts. -/
theorem overlapCoefficient_eq_unionCountNormalization
    {N p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (hr : unionSize p q s ≤ N) :
    overlapCoefficient N p q s =
      ((Nat.choose N (unionSize p q s) : ℝ) *
        (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℝ)) /
        ((Nat.choose N p : ℝ) * (Nat.choose N q : ℝ)) := by
  rw [card_overlapConfiguration hsp hsq]
  simpa [unionSize, Nat.cast_mul, mul_assoc] using
    overlapCoefficient_eq_unionConfigurationNormalization hsp hsq hr

/-- Multiplying the source overlap probability by the local configuration
average leaves exactly the reciprocal normalization of all original pairs,
with one choice of union subset. -/
theorem overlapCoefficient_mul_localAverageFactor
    {N p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (hr : unionSize p q s ≤ N) :
    overlapCoefficient N p q s *
        (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℝ)⁻¹ =
      (Nat.choose N (unionSize p q s) : ℝ) /
        ((Nat.choose N p : ℝ) * (Nat.choose N q : ℝ)) := by
  have hN : p ≤ N := by
    exact le_trans (by dsimp [unionSize]; omega) hr
  have hqN : q ≤ N := by
    exact le_trans (by dsimp [unionSize]; omega) hr
  have hrp : p ≤ unionSize p q s := by dsimp [unionSize]; omega
  have hcard : (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℝ) ≠ 0 := by
    rw [card_overlapConfiguration hsp hsq]
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos (Nat.choose_pos hrp) (Nat.choose_pos hsp)))
  have hdenp : (Nat.choose N p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero hN)
  have hdenq : (Nat.choose N q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero hqN)
  rw [overlapCoefficient_eq_unionCountNormalization hsp hsq hr]
  field_simp [hcard, hdenp, hdenq]

/-- The source-normalized contribution of one feasible overlap size obeys
the product radius majorant. -/
theorem weightedAveragedOverlapKernel_majorant {N p q s : ℕ} {R : ℝ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (hR : 1 ≤ R) (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    overlapCoefficient N p q s *
        (R ^ unionSize p q s * ‖averagedOverlapKernel hsp hsq A B‖) ≤
      overlapCoefficient N p q s * ((R ^ p * ‖A‖) * (R ^ q * ‖B‖)) := by
  have hcoef := overlapCoefficient_nonneg N p q s
  have hkernel := norm_averagedOverlapKernel_le hsp hsq A B
  have hpow : R ^ unionSize p q s ≤ R ^ (p + q) := by
    apply pow_le_pow_right₀ hR
    dsimp [unionSize]
    omega
  calc
    _ ≤ overlapCoefficient N p q s *
        (R ^ unionSize p q s * (‖A‖ * ‖B‖)) := by
      gcongr
    _ ≤ overlapCoefficient N p q s *
        (R ^ (p + q) * (‖A‖ * ‖B‖)) := by
      gcongr
    _ = _ := by rw [pow_add]; ring

/-- The frozen arbitrary-`N` expansion before regrouping, retained as the
starting identity for the actual union/overlap reindexing. -/
theorem product_eq_actualPairPlacementSum
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    (genericU_N_r N p hp A).comp (genericU_N_r N q hq B) =
      (((Nat.choose N p : ℂ)⁻¹) * ((Nat.choose N q : ℂ)⁻¹)) •
        ∑ S : PlacementSubset p (N - p),
          ∑ T : PlacementSubset q (N - q),
            (arbitraryNSectorSubsetPlacement N p hp S A).comp
              (arbitraryNSectorSubsetPlacement N q hq T B) :=
  arbitraryN_product_eq_actualPairPlacementSum N p q hp hq A B

/-- The source coefficient is the probability of the actual fixed-left
overlap fiber.  This makes the ambient normalization explicit and separate
from the local average above. -/
theorem overlapCoefficient_eq_actualFiberProbability
    {N p q s : ℕ} (P : Finset (Fin N)) (hP : P.card = p) (hsq : s ≤ q) :
    overlapCoefficient N p q s =
      ((overlapFiber P q s).card : ℝ) / (Nat.choose N q : ℝ) :=
  overlapCoefficient_eq_fiberProbability P hP hsq

/-- The actual source overlap probabilities retain the exact binomial
normalization after summing over all intersection sizes. -/
theorem actualFiberProbabilities_sum_one
    {N p q : ℕ} (P : Finset (Fin N)) (hP : P.card = p)
    (hp : p ≤ N) (hq : q ≤ N) :
    (∑ s ∈ Finset.range (q + 1),
      ((overlapFiber P q s).card : ℝ) / (Nat.choose N q : ℝ)) = 1 :=
  sum_overlapFiberProbability_eq_one P hP hp hq

end QuantumNLS.PlacementProduct

#print axioms QuantumNLS.PlacementProduct.averagedOverlapKernel
#print axioms QuantumNLS.PlacementProduct.overlapConfiguration_nonempty
#print axioms QuantumNLS.PlacementProduct.overlapConfigurationFiberEquiv
#print axioms QuantumNLS.PlacementProduct.card_overlapConfiguration
#print axioms QuantumNLS.PlacementProduct.averagedOverlapKernel_eq_average
#print axioms QuantumNLS.PlacementProduct.norm_averagedOverlapKernel_le
#print axioms QuantumNLS.PlacementProduct.overlapCoefficient_eq_unionConfigurationNormalization
#print axioms QuantumNLS.PlacementProduct.overlapCoefficient_eq_unionCountNormalization
#print axioms QuantumNLS.PlacementProduct.overlapCoefficient_mul_localAverageFactor
#print axioms QuantumNLS.PlacementProduct.weightedAveragedOverlapKernel_majorant
#print axioms QuantumNLS.PlacementProduct.product_eq_actualPairPlacementSum
#print axioms QuantumNLS.PlacementProduct.overlapCoefficient_eq_actualFiberProbability
#print axioms QuantumNLS.PlacementProduct.actualFiberProbabilities_sum_one
