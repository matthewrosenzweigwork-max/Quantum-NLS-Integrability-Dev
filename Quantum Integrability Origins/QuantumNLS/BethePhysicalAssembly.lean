import QuantumNLS.BetheEndpointProducts
import QuantumNLS.BetheEigen

/-! Assembly of the literal physical transfer, retaining its exact (N)_m. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BethePhysicalAssembly
open TensorCarrier TensorPlacements PhysicalTensor BetheHigherPlacement
open BetheGeneralSliceEndpoints BetheGeneratedEndpoints BetheGeneratedLabels
open BetheFaceEnumeration BethePhysicalFaceCharts BethePrimitiveTransport
open BetheRectangleIncidence BetheInternalFaces BetheWavefunctions BetheEndpointProducts
attribute [local instance] Classical.propDecidable

/-- Literal two-chart antiderivative sum at a fixed acted-on block size. -/
def blockExpansion (m q : ℕ) (L c : ℝ) (n : Fin (m+q) → ℤ) (z : ℂ)
    (x : Fin (m+q) → ℝ) : ℂ :=
  (c : ℂ)^m * ∑ S : PlacementSubset m q, ∑ T : PlacementSubset m q,
    (sourceCorners L c n z (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) false T +
     sourceCorners L c n z (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) true T)

/-- The degree summand of the literal BGE1 expansion in a common dimension. -/
def degreeExpansion {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ)
    (x : Fin N → ℝ) (d : Fin (N+1)) : ℂ :=
  blockExpansion d.val (N-d.val) L c (n ∘ ambient d) z (x ∘ ambient d)

theorem complement_zero_rank {q : ℕ} (S : PlacementSubset 0 q) (j : Fin q) :
    S.1ᶜ.orderEmbOfFin (complement_card S) j = (finCongr (Nat.zero_add q)).symm j := by
  have hs : S.1 = ∅ := Finset.card_eq_zero.mp S.2
  have he := Finset.orderEmbOfFin_unique (complement_card S)
    (f := (finCongr (Nat.zero_add q)).symm)
    (fun i => by simp [hs]) (fun _ _ h => h)
  exact (congrFun he j).symm

/-- Empty selected charts preserve the complete spectator tuple. -/
theorem mergeChart_zero {q : ℕ} (S : PlacementSubset 0 q)
    (y : Fin 0 → ℝ) (s : Fin q → ℝ) :
    mergeChart S y s = s ∘ (finCongr (Nat.zero_add q)) := by
  funext k
  obtain ⟨j,rfl⟩ := (finCongr (Nat.zero_add q)).symm.surjective k
  rw [← complement_zero_rank S j]
  have hm := mergeChart_spectator S y s j
  simp only [spectatorRank, mergePermutation_spectator] at hm
  rw [hm]
  simp [complement_zero_rank]

/-- Both degree-zero corner branches retain the original wave. -/
theorem sourceCorners_zero {q : ℕ} (L c : ℝ) (n : Fin (0+q) → ℤ) (z : ℂ)
    (y : Fin 0 → ℝ) (s : Fin q → ℝ) (b : Bool) (S : PlacementSubset 0 q) :
    sourceCorners L c n z y s b S =
      Complex.exp (Complex.I*z*(if b then (L : ℂ) else 0)) *
        coordinateAnsatz c (BetheSmooth.sourceRoots L n c)
          (s ∘ finCongr (Nat.zero_add q)) := by
  cases b <;> simp [sourceCorners, orientation, branchOffset, chartPrimitive,
    firstPositions, activeRanks, primitive_empty, mergeChart_zero]

/-- The empty output and input subsets each occur once. -/
theorem block_zero (q : ℕ) (L c : ℝ) (n : Fin (0+q) → ℤ) (z : ℂ)
    (x : Fin (0+q) → ℝ) :
    blockExpansion 0 q L c n z x =
      (1 + Complex.exp (Complex.I*(L : ℂ)*z)) *
        coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x := by
  have hz (S : PlacementSubset 0 q) : S.1 = ∅ :=
    Finset.card_eq_zero.mp S.2
  have : Subsingleton (PlacementSubset 0 q) :=
    ⟨fun S T => Subtype.ext ((hz S).trans (hz T).symm)⟩
  let S : PlacementSubset 0 q := ⟨∅, by simp⟩
  have hinput : (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) ∘
      finCongr (Nat.zero_add q) = x := by
    funext k
    simp only [Function.comp_apply, complement_zero_rank, Equiv.symm_apply_apply]
  unfold blockExpansion
  rw [pow_zero, one_mul, Fintype.sum_subsingleton _ S, Fintype.sum_subsingleton _ S,
    sourceCorners_zero, sourceCorners_zero, hinput]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, Complex.exp_zero, one_mul]
  ring

/-- Equality of finite dimensions transports the entire original wave. -/
theorem source_wave_finCongr {M N : ℕ} (h : M=N) (L c : ℝ)
    (n : Fin N → ℤ) (x : Fin N → ℝ) :
    coordinateAnsatz c (BetheSmooth.sourceRoots L (n ∘ finCongr h) c)
      (x ∘ finCongr h) = coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x := by
  subst N
  rfl

/-- Degree zero in the ambient dimension, without changing the source wave. -/
theorem degree_zero {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ)
    (x : Fin N → ℝ) :
    degreeExpansion L c n z x 0 =
      (1 + Complex.exp (Complex.I*(L : ℂ)*z)) *
        coordinateAnsatz c (BetheSmooth.sourceRoots L n c) x := by
  unfold degreeExpansion
  dsimp only [Fin.val_zero]
  rw [block_zero]
  congr 1
  exact source_wave_finCongr (show 0+(N-0)=N by omega) L c n x

/-- Every positive physical degree is the corresponding literal expansion
summand; dimension transport changes no roots or normalization. -/
theorem source_degree_ae (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ))
    (d : Fin (N+1)) (hd : 0 < d.val) :
    ∀ᵐ x ∂torusPiMeasure L N, StrictAnti (BetheWeakGradient.representatives L x) →
      physUnitary ((BethePhysicalTransfer.transferTerm L N c z d
        (sourceVector L hc hn)).1) x =
          degreeExpansion L c n z (BetheWeakGradient.representatives L x) d := by
  have hsplit (m q : ℕ) (h : m+q=N) (hm : m=d.val) :
      ∀ᵐ x ∂torusPiMeasure L N, StrictAnti (BetheWeakGradient.representatives L x) →
        physUnitary ((BethePhysicalTransfer.transferTerm L N c z d
          (sourceVector L hc hn)).1) x =
            degreeExpansion L c n z (BetheWeakGradient.representatives L x) d := by
    subst N
    obtain ⟨dv,dh⟩ := d
    dsimp only [Fin.val_mk] at hm
    subst dv
    have hh := source_transferTerm_corners_ae L m q hd hc hn z hz
    have hgen (r : ℕ) (hr : r=q) (hN : m+r=m+q) :
        ∀ᵐ x ∂torusPiMeasure L (m+q),
          StrictAnti (BetheWeakGradient.representatives L x) →
            physUnitary ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,dh⟩
              (sourceVector L hc hn)).1) x =
                blockExpansion m r L c (n ∘ finCongr hN) z
                  (BetheWeakGradient.representatives L x ∘ finCongr hN) := by
      subst r
      simpa only [finCongr_refl, Equiv.coe_refl, Function.comp_id,
        blockExpansion, mergePermutation_selected, mergePermutation_spectator] using hh
    exact hgen (m+q-m) (by omega) (by omega)
  exact hsplit d.val (N-d.val) (by omega) rfl

/-- Finite operator addition and evaluation commute almost everywhere. -/
theorem transfer_position_ae (L : ℝ) [Fact (0 < L)] {N : ℕ}
    (c : ℝ) (z : ℂ) (ψ : SymSector ℂ (L2T L) N) :
    ∀ᵐ x ∂torusPiMeasure L N,
      physUnitary ((BethePhysicalTransfer.transfer L N c z ψ).1) x =
        (1 + Complex.exp (Complex.I*(L : ℂ)*z)) * physUnitary ψ.1 x +
          ∑ d : Fin N, physUnitary ((BethePhysicalTransfer.transferTerm L N c z
            d.succ ψ).1) x := by
  let a := 1 + Complex.exp (Complex.I*(L : ℂ)*z)
  let v : L2TN L N := physUnitary ψ.1
  let F (d : Fin N) : L2TN L N :=
    physUnitary ((BethePhysicalTransfer.transferTerm L N c z d.succ ψ).1)
  have he : physUnitary ((BethePhysicalTransfer.transfer L N c z ψ).1) =
      a • v + ∑ d : Fin N, F d := by
    simp [BethePhysicalTransfer.transfer, Fin.sum_univ_succ,
      BethePhysicalTransfer.transferTerm, a, v, F]
  rw [he]
  filter_upwards [Lp.coeFn_add (a • v) (∑ d : Fin N, F d),
    Lp.coeFn_smul a v, Lp.coeFn_fun_finsetSum Finset.univ F] with x ha hs hf
  rw [ha]
  change (a • v) x + (∑ d : Fin N, F d) x = _
  rw [hs, hf]
  rfl

/-- The actual full physical transfer is the literal original expansion,
including degree zero, on strict ordered representatives almost everywhere. -/
theorem source_transfer_expansion_ordered_ae (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ)) :
    ∀ᵐ x ∂torusPiMeasure L N, StrictAnti (BetheWeakGradient.representatives L x) →
      physUnitary ((BethePhysicalTransfer.transfer L N c z
        (sourceVector L hc hn)).1) x =
          originalExpansion L c n z (BetheWeakGradient.representatives L x) := by
  have hall := Filter.eventually_all.mpr (fun d : Fin N =>
    source_degree_ae L hc hn z hz d.succ (by simp))
  have hi := sourceVector_position L hc hn
  have hin := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
    (torusPiMeasure L N) (sourceInput L hc hn)
  rw [← hi] at hin
  filter_upwards [transfer_position_ae L c z (sourceVector L hc hn), hall, hin]
    with x he hd hv hx
  rw [he, hv]
  change _ = ∑ d : Fin (N+1), degreeExpansion L c n z
    (BetheWeakGradient.representatives L x) d
  rw [Fin.sum_univ_succ, degree_zero]
  have hw : sourceInput L hc hn x = coordinateAnsatz c (BetheSmooth.sourceRoots L n c)
      (BetheWeakGradient.representatives L x) := by
    exact BetheExtension.symmetricExtension_eq L c n hx.antitone
  rw [hw]
  congr 1
  exact Finset.sum_congr rfl (fun d _ => hd d hx)

/-- Strict ordered physical action with the two spectral products. -/
theorem source_transfer_spectral_ordered_ae (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ)) :
    ∀ᵐ x ∂torusPiMeasure L N, StrictAnti (BetheWeakGradient.representatives L x) →
      physUnitary ((BethePhysicalTransfer.transfer L N c z
        (sourceVector L hc hn)).1) x =
          TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z *
            sourceInput L hc hn x := by
  have hint := Filter.eventually_all.mpr (fun j => representatives_interior_ae L N j)
  filter_upwards [source_transfer_expansion_ordered_ae L hc hn z hz, hint]
    with x he hb hx
  rw [he hx]
  change (∑ d : Fin (N+1), degreeExpansion L c n z
    (BetheWeakGradient.representatives L x) d) = _
  have hh := original_sum_eq_spectral (Fact.out : 0 < L) hc hn z hz _ hx hb
  change originalExpansion L c n z (BetheWeakGradient.representatives L x) = _ at hh
  rw [show (∑ d : Fin (N+1), degreeExpansion L c n z
    (BetheWeakGradient.representatives L x) d) = originalExpansion L c n z
      (BetheWeakGradient.representatives L x) from rfl, hh]
  congr 1
  exact (BetheExtension.symmetricExtension_eq L c n hx.antitone).symm

/-- Ordinary product torus measure gives distinct coordinates almost everywhere. -/
theorem torus_ae_injective (L : ℝ) [Fact (0 < L)] (N : ℕ) :
    ∀ᵐ x ∂torusPiMeasure L N, Function.Injective x := by
  let : NullSingletonClass (volume : Measure (AddCircle L)) := ⟨fun x => by
    have h := AddCircle.volume_closedBall (T := L) (x := x) 0
    simpa only [Metric.closedBall_zero, mul_zero,
      min_eq_right (Fact.out : 0 < L).le, ENNReal.ofReal_zero] using h⟩
  exact BetheEigen.pi_ae_injective (I := Fin N) (volume : Measure (AddCircle L))

/-- Sorting and the finite family of measure-preserving permutations extend
an ordered a.e. identity to the whole symmetric physical carrier. -/
theorem symmetric_ordered_ae (L : ℝ) [Fact (0 < L)] {N : ℕ}
    (ψ : SymSector ℂ (L2T L) N) (F : (Fin N → AddCircle L) → ℂ)
    (hF : ∀ x (σ : Equiv.Perm (Fin N)), F (x ∘ σ) = F x) (a : ℂ)
    (he : ∀ᵐ x ∂torusPiMeasure L N,
      StrictAnti (BetheWeakGradient.representatives L x) →
        physUnitary ψ.1 x = a * F x) :
    physUnitary ψ.1 =ᵐ[torusPiMeasure L N] fun x => a * F x := by
  have hs (σ : Equiv.Perm (Fin N)) :
      ∀ᵐ x ∂torusPiMeasure L N,
        physUnitary ψ.1 x = physUnitary ψ.1 (coordPerm σ x) := by
    have hh := coeFn_physPerm σ (physUnitary ψ.1)
    rw [(mem_physSector_iff ψ.1).mp ψ.2 σ] at hh
    exact hh
  have hp (σ : Equiv.Perm (Fin N)) :=
    (measurePreserving_coordPerm (L := L) σ).quasiMeasurePreserving.ae he
  filter_upwards [Filter.eventually_all.mpr hs, Filter.eventually_all.mpr hp,
    torus_ae_injective L N]
    with x hx hperm hinj
  let σ := Tuple.sort (α := ℝᵒᵈ) (BetheWeakGradient.representatives L x)
  have hr : Function.Injective (BetheWeakGradient.representatives L x) := by
    intro i j hij
    apply hinj
    apply (AddCircle.equivIco L 0).injective
    exact Subtype.ext hij
  have ho : StrictAnti (BetheWeakGradient.representatives L (coordPerm σ x)) :=
    (BetheExtension.decreasing_antitone (BetheWeakGradient.representatives L x)).strictAnti_of_injective
      (hr.comp σ.injective)
  rw [hx σ, hperm σ ho]
  exact congrArg (fun w => a*w) (hF x σ)

/-- Full physical action almost everywhere, for every N, off the actual
source roots. There is no ordered-representative premise. -/
theorem source_transfer_spectral_ae (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ)) :
    physUnitary ((BethePhysicalTransfer.transfer L N c z
      (sourceVector L hc hn)).1) =ᵐ[torusPiMeasure L N]
        fun x => TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z *
          sourceInput L hc hn x :=
  symmetric_ordered_ae L _ (sourceInput L hc hn)
    (BetheExtension.torusExtension_permute L c n) _
    (source_transfer_spectral_ordered_ae L hc hn z hz)

/-- The literal physical transfer has the printed spectral value on the
actual unnormalized positive-c Bethe vector, in every particle sector. -/
theorem transfer_source_nonpole (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ)) :
    BethePhysicalTransfer.transfer L N c z (sourceVector L hc hn) =
      TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z •
        sourceVector L hc hn := by
  apply Subtype.ext
  apply (physUnitary (L := L) (N := N)).injective
  change physUnitary ((BethePhysicalTransfer.transfer L N c z
    (sourceVector L hc hn)).1) =
      physUnitary (TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z •
        (sourceVector L hc hn).1)
  rw [map_smul]
  apply Lp.ext
  have hi := sourceVector_position L hc hn
  have hin := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
    (torusPiMeasure L N) (sourceInput L hc hn)
  rw [← hi] at hin
  filter_upwards [source_transfer_spectral_ae L hc hn z hz, hin,
    Lp.coeFn_smul (TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z)
      (physUnitary (sourceVector L hc hn).1)] with x he hv hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, hv]
  exact he

/-- The physical output has this continuous representative on every torus
configuration, including collision walls and the periodic seam. -/
theorem transfer_continuous_representative_nonpole (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ j, z ≠ (BetheSmooth.sourceRoots L n c j : ℂ)) :
    physUnitary ((BethePhysicalTransfer.transfer L N c z (sourceVector L hc hn)).1) =
      ContinuousMap.toLp 2 (torusPiMeasure L N) ℂ
        (TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z •
          sourceInput L hc hn) := by
  rw [transfer_source_nonpole L hc hn z hz]
  change physUnitary (TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z •
    (sourceVector L hc hn).1) = _
  rw [map_smul, sourceVector_position]
  exact (map_smul (ContinuousMap.toLp 2 (torusPiMeasure L N) ℂ) _ _).symm

/-- The actual physical action has the explicit BEP1 root value as its
punctured Hilbert-norm limit, in every sector. -/
theorem transfer_source_removable_limit (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) (i : Fin N) :
    Filter.Tendsto (fun z => BethePhysicalTransfer.transfer L N c z (sourceVector L hc hn))
      (nhdsWithin (BetheSmooth.sourceRoots L n c i : ℂ)
        ({(BetheSmooth.sourceRoots L n c i : ℂ)} : Set ℂ)ᶜ)
      (nhds ((deriv (BetheOnShell.numerator L c (BetheSmooth.sourceRoots L n c))
        (BetheSmooth.sourceRoots L n c i) /
          ∏ k ∈ Finset.univ.erase i,
            ((BetheSmooth.sourceRoots L n c i : ℂ) - BetheSmooth.sourceRoots L n c k)) •
              sourceVector L hc hn)) := by
  have ht := (source_spectral_removable_value (Fact.out : 0 < L) hc hn i).smul_const
    (sourceVector L hc hn)
  apply ht.congr'
  filter_upwards [source_nonpole_eventually_at_root (Fact.out : 0 < L) hc hn i] with z hz
  exact (transfer_source_nonpole L hc hn z hz).symm

end QuantumNLS.BethePhysicalAssembly


#print axioms QuantumNLS.BethePhysicalAssembly.blockExpansion
#print axioms QuantumNLS.BethePhysicalAssembly.degreeExpansion
#print axioms QuantumNLS.BethePhysicalAssembly.complement_zero_rank
#print axioms QuantumNLS.BethePhysicalAssembly.mergeChart_zero
#print axioms QuantumNLS.BethePhysicalAssembly.sourceCorners_zero
#print axioms QuantumNLS.BethePhysicalAssembly.block_zero
#print axioms QuantumNLS.BethePhysicalAssembly.source_wave_finCongr
#print axioms QuantumNLS.BethePhysicalAssembly.degree_zero
#print axioms QuantumNLS.BethePhysicalAssembly.source_degree_ae
#print axioms QuantumNLS.BethePhysicalAssembly.transfer_position_ae
#print axioms QuantumNLS.BethePhysicalAssembly.source_transfer_expansion_ordered_ae
#print axioms QuantumNLS.BethePhysicalAssembly.source_transfer_spectral_ordered_ae
#print axioms QuantumNLS.BethePhysicalAssembly.torus_ae_injective
#print axioms QuantumNLS.BethePhysicalAssembly.symmetric_ordered_ae
#print axioms QuantumNLS.BethePhysicalAssembly.source_transfer_spectral_ae
#print axioms QuantumNLS.BethePhysicalAssembly.transfer_source_nonpole
#print axioms QuantumNLS.BethePhysicalAssembly.transfer_continuous_representative_nonpole
#print axioms QuantumNLS.BethePhysicalAssembly.transfer_source_removable_limit

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BethePhysicalAssembly.blockExpansion,
    ``QuantumNLS.BethePhysicalAssembly.degreeExpansion,
    ``QuantumNLS.BethePhysicalAssembly.complement_zero_rank,
    ``QuantumNLS.BethePhysicalAssembly.mergeChart_zero,
    ``QuantumNLS.BethePhysicalAssembly.sourceCorners_zero,
    ``QuantumNLS.BethePhysicalAssembly.block_zero,
    ``QuantumNLS.BethePhysicalAssembly.source_wave_finCongr,
    ``QuantumNLS.BethePhysicalAssembly.degree_zero,
    ``QuantumNLS.BethePhysicalAssembly.source_degree_ae,
    ``QuantumNLS.BethePhysicalAssembly.transfer_position_ae,
    ``QuantumNLS.BethePhysicalAssembly.source_transfer_expansion_ordered_ae,
    ``QuantumNLS.BethePhysicalAssembly.source_transfer_spectral_ordered_ae,
    ``QuantumNLS.BethePhysicalAssembly.torus_ae_injective,
    ``QuantumNLS.BethePhysicalAssembly.symmetric_ordered_ae,
    ``QuantumNLS.BethePhysicalAssembly.source_transfer_spectral_ae,
    ``QuantumNLS.BethePhysicalAssembly.transfer_source_nonpole,
    ``QuantumNLS.BethePhysicalAssembly.transfer_continuous_representative_nonpole,
    ``QuantumNLS.BethePhysicalAssembly.transfer_source_removable_limit,

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
            throwError "Physical assembly nonstandard dependency: {n}"
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
      throwError "Physical assembly aggregate missing ingredient: {n}"
  unless seen.contains ``QuantumNLS.BetheEigen.pi_ae_injective do
    throwError "Physical assembly missing nonatomic product lemma"
  for n in seen do
    if n == ``sorryAx ||
        (n.toString.startsWith "QuantumNLS.BetheEigen." &&
          !(n.toString.startsWith "QuantumNLS.BetheEigen.pi_ae_injective")) || (n.toString.startsWith "QuantumNLS.TransferSeparation" &&
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
      throwError "Physical assembly aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Physical assembly aggregate audit PASS: {seen.size} transitive constants. Own all-N nonpole physical action, permutation and a.e. transport, continuous representative, physical punctured root limits and inherited BEP1 roots audited. Only the six listed scalar TransferSeparation definitions/lemmas and the nonatomic product lemma from BetheEigen are allowed. Actual physical source-root values remain open."
