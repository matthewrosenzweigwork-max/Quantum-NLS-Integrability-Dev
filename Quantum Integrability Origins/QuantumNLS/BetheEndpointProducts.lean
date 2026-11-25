import QuantumNLS.BetheCyclicGeometry

/-! Actual endpoint survivors and their two finite spectral products. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheEndpointProducts
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheGeneratedLabels
open BetheExteriorSurvivors BetheExteriorReconstruction BetheExteriorMultiplicity
open BethePrimitiveTransport BetheInternalFaces BetheWavefunctions
open BetheCrossDegreeReconstruction BetheMarkedCancellation
attribute [local instance] Classical.propDecidable

theorem exteriorSelected_true_zero {m : ℕ} (L : ℝ) (X : Fin m → ℝ) :
    exteriorSelected L X true 0 = X := by
  funext i
  simp [exteriorSelected, extendedOutput, Fin.succAbove_zero]

theorem exteriorSelected_false_last {m : ℕ} (L : ℝ) (X : Fin m → ℝ) :
    exteriorSelected L X false (Fin.last m) = X := by
  funext i
  simp [exteriorSelected, extendedOutput, Fin.succAbove_last]

theorem mergeChart_original {m q : ℕ} (x : Fin (m+q) → ℝ)
    (S : PlacementSubset m q) :
    mergeChart S (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) = x := by
  funext k
  obtain ⟨a,rfl⟩ := (mergePermutation S).surjective k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) a
  · simpa only [selectedRank, mergePermutation_selected] using
      (mergeChart_selected S (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) i)
  · simpa only [spectatorRank, mergePermutation_spectator] using
      (mergeChart_spectator S (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) j)

theorem endpoint_charts {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (S : PlacementSubset m q) :
    exteriorChart L x hx hb S true 0 = S ∧
      exteriorChart L x hx hb S false (Fin.last m) = S := by
  constructor
  · apply Eq.symm
    apply exteriorChart_unique
    rw [exteriorSelected_true_zero, mergeChart_original]
    exact hx.antitone
  · apply Eq.symm
    apply exteriorChart_unique
    rw [exteriorSelected_false_last, mergeChart_original]
    exact hx.antitone

theorem endpoint_orientations (m : ℕ) :
    orientation (cutBooleans (0 : Fin (m+1))) = (-1 : ℂ)^m ∧
      orientation (cutBooleans (Fin.last m)) = 1 := by
  constructor
  · simp [orientation, cutBooleans]
  · simp [orientation, cutBooleans]

theorem activeRanks_firstPositions {m q : ℕ} (S : PlacementSubset m q) :
    activeRanks S (firstPositions (p := m) (q := q)) = S.1 := by
  have h := congrArg Subtype.val (mergePermutation_image S)
  simpa [activeRanks, placementSubsetOfPerm, Finset.map_eq_image] using h

theorem primitive_finCongr {M N : ℕ} (h : M = N) (c : ℝ)
    (r x : Fin N → ℝ) (z : ℂ) (A : Finset (Fin M)) :
    primitive c (r ∘ finCongr h) (x ∘ finCongr h) z A =
      primitive c r x z (A.map (finCongr h).toEmbedding) := by
  subst N
  simp

/-- Both literal endpoint values, with every degree coefficient and sign. -/
theorem endpoint_values {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ)
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (d : Fin (N+1)) (S : PlacementSubset d.val (N-d.val)) :
    exteriorValue L c n z x hx hb ⟨d,S,true,0⟩ =
      Complex.exp (Complex.I*z*(L : ℂ)) * (- (c : ℂ))^d.val *
        primitive c (BetheSmooth.sourceRoots L n c) x z (S.1.map (ambient d).toEmbedding) ∧
    exteriorValue L c n z x hx hb ⟨d,S,false,Fin.last d.val⟩ =
      (c : ℂ)^d.val *
        primitive c (BetheSmooth.sourceRoots L n c) x z (S.1.map (ambient d).toEmbedding) := by
  have hc := endpoint_charts L (x ∘ ambient d) (fun _ _ h => hx h)
    (fun _ => hb _) S
  have hp : chartPrimitive S c (BetheSmooth.sourceRoots L (n ∘ ambient d) c)
      (fun i => x (ambient d (S.1.orderEmbOfFin S.2 i)))
      (fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))) z
      (firstPositions (p := d.val) (q := N-d.val)) =
      primitive c (BetheSmooth.sourceRoots L n c) x z (S.1.map (ambient d).toEmbedding) := by
    have hm := mergeChart_original (x ∘ ambient d) S
    dsimp only [Function.comp_apply] at hm
    rw [chartPrimitive, hm, activeRanks_firstPositions]
    rw [show ambient d = finCongr (show d.val+(N-d.val) = N by omega) from rfl,
      sourceRoots_finCongr, primitive_finCongr]
  constructor
  · simp only [exteriorValue, exterior_branch_displacement]
    rw [hc.1, exteriorSelected_true_zero, hp, (endpoint_orientations d.val).1]
    have he : extendedOutput L (fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))) true 0 = L := by
      simp [extendedOutput]
    rw [he, neg_pow]
    ring
  · simp only [exteriorValue, exterior_branch_displacement]
    rw [hc.2, exteriorSelected_false_last, hp, (endpoint_orientations d.val).2]
    simp [extendedOutput]

/-- Every literal degree/subset label is one ambient subset, once. -/
def degreeSubsetEquiv (N : ℕ) :
    ((d : Fin (N+1)) × PlacementSubset d.val (N-d.val)) ≃ Finset (Fin N) := by
  let f : ((d : Fin (N+1)) × PlacementSubset d.val (N-d.val)) → Finset (Fin N) :=
    fun p => p.2.1.map (ambient p.1).toEmbedding
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨d,S⟩ ⟨e,T⟩ h
    have hd : d = e := by
      apply Fin.ext
      have hh := congrArg Finset.card h
      simpa [f, S.2, T.2] using hh
    subst e
    have hs : S = T := by
      apply Subtype.ext
      exact Finset.map_injective _ h
    subst T
    rfl
  · intro A
    refine ⟨⟨degree A, outputChart A⟩, ?_⟩
    simp [f, outputChart, Finset.map_map]

theorem sum_degree_subsets {N : ℕ} (F : Finset (Fin N) → ℂ) :
    (∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
      F (S.1.map (ambient d).toEmbedding)) = ∑ A : Finset (Fin N), F A := by
  have h := (degreeSubsetEquiv N).sum_comp F
  change (∑ p : ((d : Fin (N+1)) × PlacementSubset d.val (N-d.val)),
    F (p.2.1.map (ambient p.1).toEmbedding)) = _ at h
  simpa only [Fintype.sum_sigma] using h

/-- Algebraic assembly includes the empty subset and the zero sector. -/
theorem sum_primitive_product {N : ℕ} (c : ℝ) (r x : Fin N → ℝ)
    (z a : ℂ) :
    (∑ A : Finset (Fin N), a^A.card * primitive c r x z A) =
      coordinateAnsatz c r x * ∏ j, (1 + a * (frequency z (r j))⁻¹) := by
  simp only [primitive, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (σ : Equiv.Perm (Fin N)) :
      (∑ A : Finset (Fin N), a^A.card *
        (coefficient c (r ∘ σ) * planeWave (r ∘ σ) x * denominator z (r ∘ σ) A)) =
      coefficient c (r ∘ σ) * planeWave (r ∘ σ) x *
        ∏ j, (1 + a * (frequency z (r j))⁻¹) := by
    have hs : (∑ A : Finset (Fin N), ∏ j ∈ A, a * (frequency z (r (σ j)))⁻¹) =
        ∏ j, (1 + a * (frequency z (r (σ j)))⁻¹) := by
      simpa using (Finset.prod_one_add (Finset.univ : Finset (Fin N))).symm
    have he := Equiv.prod_comp σ (fun j => 1 + a * (frequency z (r j))⁻¹)
    rw [← he, ← hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    simp [denominator, Finset.prod_mul_distrib, mul_assoc, mul_left_comm]
  simp_rw [h]
  rw [← Finset.sum_mul]
  rfl

theorem frequency_inverse (z : ℂ) (q : ℝ) :
    (frequency z q)⁻¹ = Complex.I / (z - q) := by
  rw [frequency, mul_inv_rev, Complex.inv_I, div_eq_mul_inv,
    show (q : ℂ) - z = -(z-q) by ring, inv_neg]
  ring

/-- The true endpoint family is the exponential times the minus product;
the false endpoint family is the plus product. These are literal totalized
finite expressions; their analytic values at poles are handled separately. -/
theorem endpoint_spectral_products {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ)
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    (∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
      exteriorValue L c n z x hx hb ⟨d,S,true,0⟩) =
      Complex.exp (Complex.I*z*(L : ℂ)) * coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x *
        ∏ j, (1 - Complex.I*c/(z - BetheSmooth.sourceRoots L n c j)) ∧
    (∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
      exteriorValue L c n z x hx hb ⟨d,S,false,Fin.last d.val⟩) =
      coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x *
        ∏ j, (1 + Complex.I*c/(z - BetheSmooth.sourceRoots L n c j)) := by
  have hs (a : ℂ) :
      (∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
        a^d.val * primitive c (BetheSmooth.sourceRoots L n c) x z
          (S.1.map (ambient d).toEmbedding)) =
        coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x *
          ∏ j, (1 + a * (frequency z (BetheSmooth.sourceRoots L n c j))⁻¹) := by
    have h := sum_degree_subsets (fun A => a^A.card *
      primitive c (BetheSmooth.sourceRoots L n c) x z A)
    have hc (d : Fin (N+1)) (S : PlacementSubset d.val (N-d.val)) :
        (S.1.map (ambient d).toEmbedding).card = d.val := by simp [S.2]
    simp_rw [hc] at h
    rw [h, sum_primitive_product]
  have hp (a : ℂ) :
      (∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
        a^d.val * primitive c (BetheSmooth.sourceRoots L n c) x z
          (S.1.map (ambient d).toEmbedding)) =
        coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x *
          ∏ j, (1 + Complex.I*a/(z - BetheSmooth.sourceRoots L n c j)) := by
    rw [hs]
    simp only [frequency_inverse, div_eq_mul_inv]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    ring
  constructor
  · simp_rw [(endpoint_values L c n z x hx hb _ _).1]
    calc
      _ = Complex.exp (Complex.I*z*(L : ℂ)) *
          (∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
            (- (c : ℂ))^d.val * primitive c (BetheSmooth.sourceRoots L n c) x z
              (S.1.map (ambient d).toEmbedding)) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = _ := by
        rw [hp]
        simp only [mul_neg, neg_div, ← sub_eq_add_neg, mul_assoc]
  · simp_rw [(endpoint_values L c n z x hx hb _ _).2]
    exact hp c

/-- Degree zero contributes the unmodified wave in each branch, with its
own boundary phase. No term is absorbed into a normalization. -/
theorem degree_zero_values {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ)
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset 0 (N-0)) :
    exteriorValue L c n z x hx hb ⟨0,S,true,0⟩ =
      Complex.exp (Complex.I*z*(L : ℂ)) * coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x ∧
    exteriorValue L c n z x hx hb ⟨0,S,false,Fin.last 0⟩ =
      coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x := by
  have he := endpoint_values L c n z x hx hb 0 S
  have hs : S.1 = ∅ := Finset.card_eq_zero.mp S.2
  simpa only [Fin.val_zero, pow_zero, hs, Finset.map_empty, primitive_empty, mul_one, one_mul] using he

/-- The two actual survivor families equal the printed spectral scalar
times the literal coordinate wave. -/
theorem endpoint_sum_eq_spectral {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ)
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    (∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
      (exteriorValue L c n z x hx hb ⟨d,S,true,0⟩ +
       exteriorValue L c n z x hx hb ⟨d,S,false,Fin.last d.val⟩)) =
      TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z *
        coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x := by
  simp only [Finset.sum_add_distrib]
  rw [(endpoint_spectral_products L c n z x hx hb).1,
    (endpoint_spectral_products L c n z x hx hb).2]
  unfold TransferSeparation.sFun
  rw [show Complex.I*z*(L : ℂ) = Complex.I*L*z by ring]
  ring

/-- Original BGE1 expansion, with every original degree coefficient. -/
theorem original_sum_eq_spectral {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    (∑ d : Fin (N+1), (c : ℂ)^d.val *
      ∑ S : PlacementSubset d.val (N-d.val),
        let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
        let s := fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))
        ∑ T : PlacementSubset d.val (N-d.val),
          (sourceCorners L c (n ∘ ambient d) z X s false T +
           sourceCorners L c (n ∘ ambient d) z X s true T)) =
      TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z *
        coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x :=
  (BetheCyclicGeometry.sum_original_eq_endpoint_survivors hL hc hn z hz x hx hb).trans
    (endpoint_sum_eq_spectral L c n z x hx hb)

/-- A local analytic filling at one root. It divides only by the other
root differences, which stay nonzero near this root. -/
def filledScalar {N : ℕ} (L c : ℝ) (r : Fin N → ℝ) (i : Fin N) (z : ℂ) : ℂ :=
  dslope (BetheOnShell.numerator L c r) (r i) z /
    ∏ k ∈ Finset.univ.erase i, (z - r k)

theorem other_root_product_ne_zero {N : ℕ} (r : Fin N → ℝ)
    (hr : Function.Injective r) (i : Fin N) :
    (∏ k ∈ Finset.univ.erase i, ((r i : ℂ) - r k)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply sub_ne_zero.mpr
  intro h
  exact (Finset.mem_erase.mp hk).1 (hr (Complex.ofReal_injective h)).symm

theorem filledScalar_continuousAt {N : ℕ} (L c : ℝ) (r : Fin N → ℝ)
    (hr : Function.Injective r) (i : Fin N) :
    ContinuousAt (filledScalar L c r i) (r i : ℂ) := by
  apply ContinuousAt.div
  · exact continuousAt_dslope_same.mpr (BetheOnShell.numerator_differentiable L c r _)
  · fun_prop
  · exact other_root_product_ne_zero r hr i

theorem filledScalar_at_root {N : ℕ} (L c : ℝ) (r : Fin N → ℝ) (i : Fin N) :
    filledScalar L c r i (r i) =
      deriv (BetheOnShell.numerator L c r) (r i) /
        ∏ k ∈ Finset.univ.erase i, ((r i : ℂ) - r k) := by
  rw [filledScalar, dslope_same]

/-- Off the roots this filling is exactly the original two-product scalar;
the only zero premise is on the explicit entire numerator. -/
theorem filledScalar_eq_spectral {N : ℕ} (L c : ℝ) (r : Fin N → ℝ) (i : Fin N)
    (hzero : BetheOnShell.numerator L c r (r i) = 0) (z : ℂ)
    (hz : ∀ k, z ≠ (r k : ℂ)) :
    filledScalar L c r i z = TransferSeparation.sFun L c r z := by
  have hD : (∏ k ∈ Finset.univ.erase i, (z - (r k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => sub_ne_zero.mpr (hz k))
  have hfactor : BetheOnShell.numerator L c r z =
      (z - r i) * dslope (BetheOnShell.numerator L c r) (r i) z := by
    simpa only [smul_eq_mul] using (sub_smul_dslope_of_zero hzero z).symm
  have hden : (TransferSeparation.shiftPoly r 0).eval z =
      (z - r i) * ∏ k ∈ Finset.univ.erase i, (z - r k) := by
    simp only [TransferSeparation.eval_shiftPoly, add_zero]
    exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
  have he := BetheOnShell.sFun_mul_denominator L c r z hz
  rw [hden, hfactor] at he
  apply (div_eq_iff hD).mpr
  apply mul_left_cancel₀ (sub_ne_zero.mpr (hz i))
  linear_combination -he

theorem source_numerator_zero {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (i : Fin N) :
    BetheOnShell.numerator L c (BetheSmooth.sourceRoots L n c)
      (BetheSmooth.sourceRoots L n c i) = 0 := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ N => exact BetheOnShell.sourceRoots_numerator_zero hL hc hn i

/-- Genuine punctured limit at each actual positive-c source root, with
the analytic value given explicitly by the numerator derivative. -/
theorem source_spectral_removable_value {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) (i : Fin N) :
    Filter.Tendsto (TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c))
      (nhdsWithin (BetheSmooth.sourceRoots L n c i : ℂ)
        ({(BetheSmooth.sourceRoots L n c i : ℂ)} : Set ℂ)ᶜ)
      (nhds (deriv (BetheOnShell.numerator L c (BetheSmooth.sourceRoots L n c))
        (BetheSmooth.sourceRoots L n c i) /
          ∏ k ∈ Finset.univ.erase i,
            ((BetheSmooth.sourceRoots L n c i : ℂ) - BetheSmooth.sourceRoots L n c k))) := by
  let r := BetheSmooth.sourceRoots L n c
  have hr : Function.Injective r := (BetheSmooth.sourceRoots_strictAnti hL hc hn).injective
  have havoid : ∀ᶠ z : ℂ in nhdsWithin (r i : ℂ) ({(r i : ℂ)} : Set ℂ)ᶜ,
      ∀ k, z ≠ (r k : ℂ) := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : k = i
    · subst k
      exact self_mem_nhdsWithin
    · apply eventually_ne_nhdsWithin
      intro h
      exact hk (hr (Complex.ofReal_injective h)).symm
  have ht := (filledScalar_continuousAt L c r hr i).tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({(r i : ℂ)} : Set ℂ)ᶜ))
  rw [filledScalar_at_root] at ht
  apply ht.congr'
  filter_upwards [havoid] with z hz
  exact filledScalar_eq_spectral L c r i (source_numerator_zero hL hc hn i) z hz

/-- The complete endpoint sum has the same filled limit, multiplied by the
literal wave. Individual totalized branch values at a root are not used
as the analytic extension's value. -/
theorem endpoint_sum_removable_value {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (i : Fin N) :
    Filter.Tendsto
      (fun z => ∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
        (exteriorValue L c n z x hx hb ⟨d,S,true,0⟩ +
         exteriorValue L c n z x hx hb ⟨d,S,false,Fin.last d.val⟩))
      (nhdsWithin (BetheSmooth.sourceRoots L n c i : ℂ)
        ({(BetheSmooth.sourceRoots L n c i : ℂ)} : Set ℂ)ᶜ)
      (nhds ((deriv (BetheOnShell.numerator L c (BetheSmooth.sourceRoots L n c))
        (BetheSmooth.sourceRoots L n c i) /
          ∏ k ∈ Finset.univ.erase i,
            ((BetheSmooth.sourceRoots L n c i : ℂ) - BetheSmooth.sourceRoots L n c k)) *
              coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x)) := by
  simp_rw [endpoint_sum_eq_spectral]
  exact (source_spectral_removable_value hL hc hn i).mul_const _

/-- Literal original antiderivative expansion, including degree zero. -/
def originalExpansion {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ)
    (x : Fin N → ℝ) : ℂ :=
  ∑ d : Fin (N+1), (c : ℂ)^d.val *
    ∑ S : PlacementSubset d.val (N-d.val),
      let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
      let s := fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))
      ∑ T : PlacementSubset d.val (N-d.val),
        (sourceCorners L c (n ∘ ambient d) z X s false T +
         sourceCorners L c (n ∘ ambient d) z X s true T)

theorem source_nonpole_eventually_at_root {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) (i : Fin N) :
    ∀ᶠ z : ℂ in nhdsWithin (BetheSmooth.sourceRoots L n c i : ℂ)
      ({(BetheSmooth.sourceRoots L n c i : ℂ)} : Set ℂ)ᶜ,
      ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ) := by
  rw [Filter.eventually_all]
  intro k
  by_cases hk : k = i
  · subst k
    exact self_mem_nhdsWithin
  · apply eventually_ne_nhdsWithin
    intro h
    exact hk ((BetheSmooth.sourceRoots_strictAnti hL hc hn).injective
      (Complex.ofReal_injective h)).symm

/-- The poles introduced by the original antiderivatives cancel in the
complete BGE1 sum. The displayed value is the genuine punctured limit. -/
theorem original_sum_removable_value {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (i : Fin N) :
    Filter.Tendsto (fun z => originalExpansion L c n z x)
      (nhdsWithin (BetheSmooth.sourceRoots L n c i : ℂ)
        ({(BetheSmooth.sourceRoots L n c i : ℂ)} : Set ℂ)ᶜ)
      (nhds ((deriv (BetheOnShell.numerator L c (BetheSmooth.sourceRoots L n c))
        (BetheSmooth.sourceRoots L n c i) /
          ∏ k ∈ Finset.univ.erase i,
            ((BetheSmooth.sourceRoots L n c i : ℂ) - BetheSmooth.sourceRoots L n c k)) *
              coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x)) := by
  have ht := (source_spectral_removable_value hL hc hn i).mul_const
    (coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x)
  apply ht.congr'
  filter_upwards [source_nonpole_eventually_at_root hL hc hn i] with z hz
  exact (original_sum_eq_spectral hL hc hn z hz x hx hb).symm

/-- Entire scalar continuation in every dimension; in dimension zero
the two empty products give exactly 1+exp(iLz). -/
theorem source_spectral_entire_extension {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ,
      (∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ)) →
        g z = TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z := by
  cases N with
  | zero =>
    refine ⟨fun z => 1 + Complex.exp (Complex.I*L*z), ?_, ?_⟩
    · fun_prop
    · intro z _
      simp [TransferSeparation.sFun]
  | succ N => exact BetheOnShell.sourceRoots_exists_entire_extension hL hc hn

/-- The strict interior original expansion has an actual entire extension,
constructed from the proved source-root numerator cancellation. -/
theorem original_sum_entire_extension {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ z : ℂ,
      (∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ)) →
        F z = originalExpansion L c n z x := by
  obtain ⟨g,hg,he⟩ := source_spectral_entire_extension hL hc hn
  refine ⟨fun z => g z * coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x,
    hg.mul_const _, ?_⟩
  intro z hz
  dsimp only
  rw [he z hz]
  exact (original_sum_eq_spectral hL hc hn z hz x hx hb).symm

end QuantumNLS.BetheEndpointProducts

#print axioms QuantumNLS.BetheEndpointProducts.exteriorSelected_true_zero
#print axioms QuantumNLS.BetheEndpointProducts.exteriorSelected_false_last
#print axioms QuantumNLS.BetheEndpointProducts.mergeChart_original
#print axioms QuantumNLS.BetheEndpointProducts.endpoint_charts
#print axioms QuantumNLS.BetheEndpointProducts.endpoint_orientations
#print axioms QuantumNLS.BetheEndpointProducts.activeRanks_firstPositions
#print axioms QuantumNLS.BetheEndpointProducts.primitive_finCongr
#print axioms QuantumNLS.BetheEndpointProducts.endpoint_values
#print axioms QuantumNLS.BetheEndpointProducts.degreeSubsetEquiv
#print axioms QuantumNLS.BetheEndpointProducts.sum_degree_subsets
#print axioms QuantumNLS.BetheEndpointProducts.sum_primitive_product
#print axioms QuantumNLS.BetheEndpointProducts.frequency_inverse
#print axioms QuantumNLS.BetheEndpointProducts.endpoint_spectral_products
#print axioms QuantumNLS.BetheEndpointProducts.degree_zero_values
#print axioms QuantumNLS.BetheEndpointProducts.endpoint_sum_eq_spectral
#print axioms QuantumNLS.BetheEndpointProducts.original_sum_eq_spectral
#print axioms QuantumNLS.BetheEndpointProducts.filledScalar
#print axioms QuantumNLS.BetheEndpointProducts.other_root_product_ne_zero
#print axioms QuantumNLS.BetheEndpointProducts.filledScalar_continuousAt
#print axioms QuantumNLS.BetheEndpointProducts.filledScalar_at_root
#print axioms QuantumNLS.BetheEndpointProducts.filledScalar_eq_spectral
#print axioms QuantumNLS.BetheEndpointProducts.source_numerator_zero
#print axioms QuantumNLS.BetheEndpointProducts.source_spectral_removable_value
#print axioms QuantumNLS.BetheEndpointProducts.endpoint_sum_removable_value
#print axioms QuantumNLS.BetheEndpointProducts.originalExpansion
#print axioms QuantumNLS.BetheEndpointProducts.source_nonpole_eventually_at_root
#print axioms QuantumNLS.BetheEndpointProducts.original_sum_removable_value
#print axioms QuantumNLS.BetheEndpointProducts.source_spectral_entire_extension
#print axioms QuantumNLS.BetheEndpointProducts.original_sum_entire_extension

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheEndpointProducts.exteriorSelected_true_zero,
    ``QuantumNLS.BetheEndpointProducts.exteriorSelected_false_last,
    ``QuantumNLS.BetheEndpointProducts.mergeChart_original,
    ``QuantumNLS.BetheEndpointProducts.endpoint_charts,
    ``QuantumNLS.BetheEndpointProducts.endpoint_orientations,
    ``QuantumNLS.BetheEndpointProducts.activeRanks_firstPositions,
    ``QuantumNLS.BetheEndpointProducts.primitive_finCongr,
    ``QuantumNLS.BetheEndpointProducts.endpoint_values,
    ``QuantumNLS.BetheEndpointProducts.degreeSubsetEquiv,
    ``QuantumNLS.BetheEndpointProducts.sum_degree_subsets,
    ``QuantumNLS.BetheEndpointProducts.sum_primitive_product,
    ``QuantumNLS.BetheEndpointProducts.frequency_inverse,
    ``QuantumNLS.BetheEndpointProducts.endpoint_spectral_products,
    ``QuantumNLS.BetheEndpointProducts.degree_zero_values,
    ``QuantumNLS.BetheEndpointProducts.endpoint_sum_eq_spectral,
    ``QuantumNLS.BetheEndpointProducts.original_sum_eq_spectral,
    ``QuantumNLS.BetheEndpointProducts.filledScalar,
    ``QuantumNLS.BetheEndpointProducts.other_root_product_ne_zero,
    ``QuantumNLS.BetheEndpointProducts.filledScalar_continuousAt,
    ``QuantumNLS.BetheEndpointProducts.filledScalar_at_root,
    ``QuantumNLS.BetheEndpointProducts.filledScalar_eq_spectral,
    ``QuantumNLS.BetheEndpointProducts.source_numerator_zero,
    ``QuantumNLS.BetheEndpointProducts.source_spectral_removable_value,
    ``QuantumNLS.BetheEndpointProducts.endpoint_sum_removable_value,
    ``QuantumNLS.BetheEndpointProducts.originalExpansion,
    ``QuantumNLS.BetheEndpointProducts.source_nonpole_eventually_at_root,
    ``QuantumNLS.BetheEndpointProducts.original_sum_removable_value,
    ``QuantumNLS.BetheEndpointProducts.source_spectral_entire_extension,
    ``QuantumNLS.BetheEndpointProducts.original_sum_entire_extension,

    ``QuantumNLS.BetheCyclicGeometry.exteriorSelected_true_succ,
    ``QuantumNLS.BetheCyclicGeometry.exteriorSelected_false_castSucc,
    ``QuantumNLS.BetheCyclicGeometry.paired_branch_displacement,
    ``QuantumNLS.BetheCyclicGeometry.cutBooleans_succ_update,
    ``QuantumNLS.BetheCyclicGeometry.paired_orientation,
    ``QuantumNLS.BetheCyclicGeometry.exteriorChart_strict,
    ``QuantumNLS.BetheCyclicGeometry.mergeChart_bounds,
    ``QuantumNLS.BetheCyclicGeometry.antitone_rotate_update_zero,
    ``QuantumNLS.BetheCyclicGeometry.exterior_true_boundary_rank,
    ``QuantumNLS.BetheCyclicGeometry.exterior_chart_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_selected_rank_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_spectator_rank_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_pending_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_merged_rotation,
    ``QuantumNLS.BetheCyclicGeometry.source_primitive_rotate_boundary,
    ``QuantumNLS.BetheCyclicGeometry.exterior_chartPrimitive_cyclic,
    ``QuantumNLS.BetheCyclicGeometry.exterior_chartPrimitive_cyclic_degree,
    ``QuantumNLS.BetheCyclicGeometry.exteriorValue_cyclic,
    ``QuantumNLS.BetheCyclicGeometry.sum_exterior_cuts,
    ``QuantumNLS.BetheCyclicGeometry.global_exterior_cyclic_sum,
    ``QuantumNLS.BetheCyclicGeometry.CyclicArm,
    ``QuantumNLS.BetheCyclicGeometry.cyclicArmIndexEquiv,
    ``QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv,
    ``QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv_apply,
    ``QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv_value,
    ``QuantumNLS.BetheCyclicGeometry.global_exterior_cyclic_sum_degree_zero,
    ``QuantumNLS.BetheCyclicGeometry.sum_original_eq_endpoint_survivors,

    ``QuantumNLS.BetheMarkedCancellation.sourceRoots_finCongr,
    ``QuantumNLS.BetheMarkedCancellation.cornerSummand_finCongr,
    ``QuantumNLS.BetheMarkedCancellation.cornerSummand_boolean_congr,
    ``QuantumNLS.BetheMarkedCancellation.rawLabel_cornerSummand_transport,
    ``QuantumNLS.BetheMarkedCancellation.exchangeLabel_value,
    ``QuantumNLS.BetheMarkedCancellation.promoteLabel_value,
    ``QuantumNLS.BetheMarkedCancellation.actual_value_triple_balance,
    ``QuantumNLS.BetheMarkedCancellation.marked_fiber_cancellation,
    ``QuantumNLS.BetheMarkedCancellation.global_marked_cancellation,
    ``QuantumNLS.BetheMarkedCancellation.sum_labels_eq_exterior,
    ``QuantumNLS.BetheMarkedCancellation.sum_original_eq_exterior,

    ``QuantumNLS.BetheExteriorMultiplicity.exteriorSurvivor_degree_input,
    ``QuantumNLS.BetheExteriorMultiplicity.exterior_rank_iff,
    ``QuantumNLS.BetheExteriorMultiplicity.extendedOutput_sum,
    ``QuantumNLS.BetheExteriorMultiplicity.exterior_branch_displacement,
    ``QuantumNLS.BetheExteriorMultiplicity.exterior_full_branch_phase,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorValue,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorSurvivor_value,
    ``QuantumNLS.BetheExteriorMultiplicity.survivorFiberEquiv,
    ``QuantumNLS.BetheExteriorMultiplicity.noneMarkEquiv,
    ``QuantumNLS.BetheExteriorMultiplicity.sum_noneMark_weighted,
    ``QuantumNLS.BetheExteriorMultiplicity.sum_noneMark_value,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorRegroupedMark,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorRegroupedMark_eq,
    ``QuantumNLS.BetheExteriorMultiplicity.sum_exterior_triples_original_weighted,

    ``QuantumNLS.BetheExteriorReconstruction.rectangle_corner_clipping,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorChart,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorChart_sorted,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorChart_unique,
    ``QuantumNLS.BetheExteriorReconstruction.exterior_box,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorBranch,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorBranch_admitted,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorBranch_corner,
    ``QuantumNLS.BetheExteriorReconstruction.ExteriorData,
    ``QuantumNLS.BetheExteriorReconstruction.Survivor,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw_admitted,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw_input,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw_noSeam,
    ``QuantumNLS.BetheExteriorReconstruction.toSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.survivorCut,
    ``QuantumNLS.BetheExteriorReconstruction.survivorCut_spec,
    ``QuantumNLS.BetheExteriorReconstruction.fromSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.from_toSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.to_fromSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorSurvivorEquiv,

    ``QuantumNLS.BetheExteriorSurvivors.extendedOutput,
    ``QuantumNLS.BetheExteriorSurvivors.cutBooleans,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_corner,
    ``QuantumNLS.BetheExteriorSurvivors.extendedOutput_strict,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_strict,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_origin,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_rectangle,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_ne_spectator,
    ``QuantumNLS.BetheExteriorSurvivors.exterior_append_injective,
    ``QuantumNLS.BetheExteriorSurvivors.exterior_chart_exists,

    ``QuantumNLS.BetheExteriorCut.rectangle_rise_collision,
    ``QuantumNLS.BetheExteriorCut.rectangle_injective_antitone,
    ``QuantumNLS.BetheExteriorCut.antitone_boolean_cut,
    ``QuantumNLS.BetheExteriorCut.noSeam_boolean_cut,

    ``QuantumNLS.BetheExteriorOrigin.noSeam_iff_injective,
    ``QuantumNLS.BetheExteriorOrigin.noSeam_selected_ne_spectator,
    ``QuantumNLS.BetheExteriorOrigin.noSeam_endpoint_origin,
    ``QuantumNLS.BetheExteriorOrigin.noSeam_coordinates,

    ``QuantumNLS.BetheTripleStrata.seamMark,
    ``QuantumNLS.BetheTripleStrata.FirstLower,
    ``QuantumNLS.BetheTripleStrata.SecondLower,
    ``QuantumNLS.BetheTripleStrata.Higher,
    ``QuantumNLS.BetheTripleStrata.SeamStratum,
    ``QuantumNLS.BetheTripleStrata.lowerEquiv,
    ``QuantumNLS.BetheTripleStrata.raise,
    ``QuantumNLS.BetheTripleStrata.higher_pinned,
    ``QuantumNLS.BetheTripleStrata.higher_demotable,
    ``QuantumNLS.BetheTripleStrata.lower,
    ``QuantumNLS.BetheTripleStrata.higherEquiv,
    ``QuantumNLS.BetheTripleStrata.marked_input_eq,
    ``QuantumNLS.BetheTripleStrata.marked_has_moving,
    ``QuantumNLS.BetheTripleStrata.armEquiv,
    ``QuantumNLS.BetheTripleStrata.tripleEquiv,
    ``QuantumNLS.BetheTripleStrata.lowerEquiv_degree,
    ``QuantumNLS.BetheTripleStrata.higherEquiv_degree,
    ``QuantumNLS.BetheTripleStrata.triple_inputs,
    ``QuantumNLS.BetheTripleStrata.triple_noncollapsed,
    ``QuantumNLS.BetheTripleStrata.sum_triples,
    ``QuantumNLS.BetheTripleStrata.sum_triples_degree,
    ``QuantumNLS.BetheTripleStrata.seamMark_branch,
    ``QuantumNLS.BetheTripleStrata.branchFiberEquiv,
    ``QuantumNLS.BetheTripleStrata.sum_branches,
    ``QuantumNLS.BetheTripleStrata.chosenTripleSum,
    ``QuantumNLS.BetheTripleStrata.sum_chosen_triples,
    ``QuantumNLS.BetheTripleStrata.regroupedMark,
    ``QuantumNLS.BetheTripleStrata.regroupedMark_eq,
    ``QuantumNLS.BetheTripleStrata.sum_marks_triples_original,
    ``QuantumNLS.BetheTripleStrata.sum_regrouped_weighted,
    ``QuantumNLS.BetheTripleStrata.sum_value_weighted,
    ``QuantumNLS.BetheTripleStrata.sum_marks_triples_original_weighted,

    ``QuantumNLS.BetheStrictLabelStrata.endpoint_candidates_disjoint,
    ``QuantumNLS.BetheStrictLabelStrata.physicalCell_strict,
    ``QuantumNLS.BetheStrictLabelStrata.Noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.label_physical_strict,
    ``QuantumNLS.BetheStrictLabelStrata.admitted_noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.no_admitted_collapsed,
    ``QuantumNLS.BetheStrictLabelStrata.promoteLabel_noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.mixed_incident_iff,
    ``QuantumNLS.BetheStrictLabelStrata.selected_seam_demote_strict,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_data,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_booleans,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_degree,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_inverse,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_ne,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported,
    ``QuantumNLS.BetheStrictLabelStrata.physicalCorner_exchange_any,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported_any,
    ``QuantumNLS.BetheStrictLabelStrata.MixedStratum,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_involutive,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_ne,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_degree,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_input,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_orientation,
    ``QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv,
    ``QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv_degree,
    ``QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse,
    ``QuantumNLS.BetheSeamProfiles.sum_marks_original,
    ``QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance,
    ``QuantumNLS.BetheSeamProfiles.sum_collapsed_mark,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Endpoint products nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[
    ``QuantumNLS.BetheEndpointProducts.endpoint_spectral_products,
    ``QuantumNLS.BetheEndpointProducts.original_sum_removable_value,
    ``QuantumNLS.BetheEndpointProducts.original_sum_entire_extension,
    ``QuantumNLS.BetheOnShell.sourceRoots_numerator_zero,
    ``QuantumNLS.BetheOnShell.sourceRoots_entire_factorization,
    ``QuantumNLS.BetheSeamProfiles.sum_marks_original,
    ``QuantumNLS.BetheSeamProfiles.sum_collapsed_mark,
    ``QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_promote,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_exchanged,
    ``QuantumNLS.BetheCornerTransport.source_generated_corner_balance,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae,
    ``QuantumNLS.BetheInputAdjacency.chartOrderingEquiv,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheSmooth.sourceRoots,
    ``QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse] do
    unless seen.contains n do
      throwError "Endpoint products aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || (n.toString.startsWith "QuantumNLS.TransferSeparation" &&
        !(#[``QuantumNLS.TransferSeparation.sFun,
          ``QuantumNLS.TransferSeparation.OnShell,
          ``QuantumNLS.TransferSeparation.shiftPoly,
          ``QuantumNLS.TransferSeparation.eval_shiftPoly,
          ``QuantumNLS.TransferSeparation.prod_plus_mul,
          ``QuantumNLS.TransferSeparation.prod_minus_mul].contains n)) ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Endpoint products aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Endpoint products aggregate audit PASS: {seen.size} transitive constants across separate roots. Own endpoint/product/removable-value declarations and inherited BCG1/BMC1 physical action and local balance roots audited. Only the six listed scalar definitions/lemmas from TransferSeparation are allowed. Physical operator assembly and boundary coverage remain open."
