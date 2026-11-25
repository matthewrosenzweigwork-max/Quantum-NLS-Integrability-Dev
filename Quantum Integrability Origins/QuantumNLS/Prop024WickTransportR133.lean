import QuantumNLS.Prop021GeneralR132
import QuantumNLS.Prop024WIdent

/-! Intrinsic Wick blocks and contractions on the symmetric sectors, with
intertwining under second quantization of an isometric embedding. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop024WickTransportR133
open TensorCarrier TensorPlacements IntrinsicContact KernelDefinition PhysicalTensor
open BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022BIso Prop022GClassical
open Prop021MarginalTransportR132

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem symProj_map (J : E →ₗᵢ[ℂ] F) (n : ℕ) (x : HilbertTensorPower ℂ E n) :
    tensorMapI J n (symProj ℂ E n x) = symProj ℂ F n (tensorMapI J n x) := by
  rw [symProj_eq_factorial_average, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, map_smul, map_sum, permRep_apply]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => (tensorMapI_perm J σ x).symm

private theorem symProject_map (J : E →ₗᵢ[ℂ] F) (n : ℕ) (x : HilbertTensorPower ℂ E n) :
    symMapI J n ((SymSector ℂ E n).orthogonalProjectionOnto x) =
      (SymSector ℂ F n).orthogonalProjectionOnto (tensorMapI J n x) := by
  apply Subtype.ext
  change tensorMapI J n (((SymSector ℂ E n).orthogonalProjectionOnto x :
    SymSector ℂ E n) : HilbertTensorPower ℂ E n) =
    (((SymSector ℂ F n).orthogonalProjectionOnto (tensorMapI J n x) :
      SymSector ℂ F n) : HilbertTensorPower ℂ F n)
  simpa only [Submodule.coe_orthogonalProjectionOnto_apply, ← symProj_eq_starProjection]
    using symProj_map J n x

/-- Insert the profile into all slots except the k free symmetric slots. -/
def insert (r k : ℕ) (u : E) : SymSector ℂ E k →L[ℂ] SymSector ℂ E (r+k) :=
  (SymSector ℂ E (r+k)).orthogonalProjectionOnto ∘L
    (splitIsometry (𝕜 := ℂ) (E := E) r k).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      htmulR (htpow r u) ∘L (SymSector ℂ E k).subtypeL

private theorem insert_map (J : E →ₗᵢ[ℂ] F) (r k : ℕ) (u : E) (x : SymSector ℂ E k) :
    symMapI J (r+k) (insert r k u x) = insert r k (J u) (symMapI J k x) := by
  unfold insert
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, htmulR_apply, Submodule.subtypeL_apply]
  rw [symProject_map]
  congr 1
  apply (splitIsometry (𝕜 := ℂ) (E := F) r k).injective
  rw [split_tensorMapI, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
    htmap_htmul]
  change htmul (tensorMapI J r (htpow r u)) (tensorMapI J k x.val) = _
  rw [tensorMapI_htpow]
  rfl

private def castOut {m n k : ℕ} (h : m = n) (C : SymSector ℂ E k →L[ℂ] SymSector ℂ E m) :
    SymSector ℂ E k →L[ℂ] SymSector ℂ E n := by
  cases h
  exact C

/-- The same insertion with the output sector written as m. -/
def insertAt (m k : ℕ) (hk : k ≤ m) (u : E) : SymSector ℂ E k →L[ℂ] SymSector ℂ E m :=
  castOut (Nat.sub_add_cancel hk) (insert (m-k) k u)

private theorem cast_insert_map (J : E →ₗᵢ[ℂ] F) (r k n : ℕ) (h : r+k = n)
    (u : E) (x : SymSector ℂ E k) :
    symMapI J n (castOut h (insert r k u) x) =
      castOut h (insert r k (J u)) (symMapI J k x) := by
  subst n
  exact insert_map J r k u x

private theorem insertAt_map (J : E →ₗᵢ[ℂ] F) (m k : ℕ) (hk : k ≤ m) (u : E)
    (x : SymSector ℂ E k) :
    symMapI J m (insertAt m k hk u x) = insertAt m k hk (J u) (symMapI J k x) :=
  cast_insert_map J (m-k) k m (Nat.sub_add_cancel hk) u x

/-- Contract the remaining slots on both sides of Bm against the profile. -/
def contract (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m)
    (Bm : SymSector ℂ E m →L[ℂ] SymSector ℂ E m) (u : E) :
    SymSector ℂ E b →L[ℂ] SymSector ℂ E a :=
  (insertAt m a ha u).adjoint ∘L Bm ∘L insertAt m b hb u

/-- Wick block at fixed input and output particle counts, with spectator
slots left unchanged. -/
def block (a b k : ℕ) (C : SymSector ℂ E b →L[ℂ] SymSector ℂ E a) :
    SymSector ℂ E (b+k) →L[ℂ] SymSector ℂ E (a+k) :=
  (Prop024WBlock.wickCoeff a b k : ℂ) •
    ((SymSector ℂ E (a+k)).orthogonalProjectionOnto ∘L
      (splitIsometry (𝕜 := ℂ) (E := E) a k).symm.toLinearIsometry.toContinuousLinearMap ∘L
      htmap ((SymSector ℂ E a).subtypeL ∘L C ∘L symProjToSector b)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E k)) ∘L
      (splitIsometry (𝕜 := ℂ) (E := E) b k).toLinearIsometry.toContinuousLinearMap ∘L
      (SymSector ℂ E (b+k)).subtypeL)


private theorem symbol_block (a b k : ℕ) (C : SymSector ℂ E b →L[ℂ] SymSector ℂ E a) (g h : E) :
    ⟪powerH (a+k) g, block a b k C (powerH (b+k) h)⟫_ℂ =
      (Prop024WBlock.wickCoeff a b k : ℂ) * (⟪powerH a g, C (powerH b h)⟫_ℂ * ⟪g,h⟫_ℂ ^ k) := by
  have hp : symProjToSector b (htpow b h : HilbertTensorPower ℂ E b) = powerH b h := by
    apply Subtype.ext
    change groupAverage (permRep ℂ E b) (htpow b h : HilbertTensorPower ℂ E b) = htpow b h
    exact groupAverage_apply_of_mem (permRep ℂ E b) (htpow_mem_symSector b h)
  unfold block
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    Submodule.subtypeL_apply, inner_smul_right]
  congr 1
  rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
    ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (powerH (a+k) g).2]
  change ⟪(htpow (a+k) g : HilbertTensorPower ℂ E (a+k)),
    (splitIsometry a k).symm
      (htmap ((SymSector ℂ E a).subtypeL ∘L C ∘L symProjToSector b)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E k))
        (splitIsometry b k (htpow (b+k) h)))⟫_ℂ = _
  rw [← (splitIsometry (𝕜 := ℂ) (E := E) a k).inner_map_map,
    LinearIsometryEquiv.apply_symm_apply, split_htpow, split_htpow, htmap_htmul]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Submodule.subtypeL_apply, hp, inner_htmul, IntrinsicContact.inner_htpow]
  rfl

section Torus

variable {L : ℝ} [Fact (0 < L)]
open Prop024WBlock Prop024WWords Prop024WOrder Prop024WSeries
open Prop024ContractionsR54 Prop022TensorCompressionR115 Prop022BFock1
open Prop021ManyBodyTransportR132 Prop022PositiveDataR126

private theorem powers_total (J : E →ₗᵢ[ℂ] L2T L) (n : ℕ) (x : SymSector ℂ E n)
    (hx : ∀ g : E, ⟪powerH n g, x⟫_ℂ = 0) : x = 0 := by
  apply (symMapI J n).injective
  rw [map_zero]
  apply Prop022ACoherent.powers_total
  intro g
  change ⟪powerH n g, symI J n x⟫_ℂ = 0
  rw [← inner_symAdj_left, symAdj_power]
  exact hx _

private theorem clm_ext_powers (J : E →ₗᵢ[ℂ] L2T L) {n m : ℕ}
    (S T : SymSector ℂ E n →L[ℂ] SymSector ℂ E m)
    (h : ∀ g v : E, ⟪powerH m g, S (powerH n v)⟫_ℂ = ⟪powerH m g, T (powerH n v)⟫_ℂ) :
    S = T := by
  have hST (v : E) : S (powerH n v) = T (powerH n v) := by
    apply sub_eq_zero.mp
    apply powers_total J m
    intro g
    rw [inner_sub_right, h, sub_self]
  have hP : (Submodule.span ℂ (Set.range (powerH (H := E) n))).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal'] at hx
    exact powers_total J n x fun g =>
      inner_eq_zero_symm.mp (hx _ (Submodule.subset_span ⟨g,rfl⟩))
  have hker : Submodule.span ℂ (Set.range (powerH (H := E) n)) ≤
      LinearMap.ker (S - T).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨v,rfl⟩
    change (S - T) (powerH n v) = 0
    rw [ContinuousLinearMap.sub_apply, hST, sub_self]
  have hcl := Submodule.topologicalClosure_minimal _ hker (ContinuousLinearMap.isClosed_ker (S-T))
  rw [hP] at hcl
  apply ContinuousLinearMap.ext
  intro v
  have hv : (S-T) v = 0 := hcl Submodule.mem_top
  simpa only [ContinuousLinearMap.sub_apply, sub_eq_zero] using hv

private theorem contraction_matrix (J : E →ₗᵢ[ℂ] L2T L) (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m)
    (B : SymSector ℂ E m →L[ℂ] SymSector ℂ E m) (u : E) (x : SymSector ℂ E a)
    (y : SymSector ℂ E b) :
    ⟪symI J a x, ck m a b ha hb (extend (symMapI J m) B) (J u) (symI J b y)⟫_ℂ =
      ⟪x, contract m a b ha hb B u y⟫_ℂ := by
  have hcast (r k n : ℕ) (h : r+k = n) :
      castOut h (insert r k (J u)) = castSectorMapCod h (insertion r k (J u)) := by
    subst n
    rfl
  have hIns (k : ℕ) (hk : k ≤ m) (z : SymSector ℂ E k) :
      insertSector m k hk (J u) (symI J k z) = symI J m (insertAt m k hk u z) := by
    change castSectorMapCod _ (insertion (m-k) k (J u)) (symMapI J k z) =
      symMapI J m (insertAt m k hk u z)
    rw [← hcast]
    exact (insertAt_map J m k hk u z).symm
  unfold ck contract
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [hIns, hIns]
  simp only [symI_apply, extend_apply_image, LinearIsometry.inner_map_map]

private theorem block_compression (J : E →ₗᵢ[ℂ] L2T L) (m a b k : ℕ) (ha : a ≤ m) (hb : b ≤ m)
    (B : SymSector ℂ E m →L[ℂ] SymSector ℂ E m) (u : E) (x : SymSector ℂ E (b+k)) :
    symAdj J (a+k) (wickBlock a b k (ck m a b ha hb (extend (symMapI J m) B) (J u))
      (symI J (b+k) x)) = block a b k (contract m a b ha hb B u) x := by
  let D := symAdj J (a+k) ∘L
    wickBlock a b k (ck m a b ha hb (extend (symMapI J m) B) (J u)) ∘L symI J (b+k)
  change D x = _
  suffices h : D = block a b k (contract m a b ha hb B u) by rw [h]
  apply clm_ext_powers J
  intro g v
  simp only [D, ContinuousLinearMap.comp_apply, inner_symAdj_right]
  rw [symbol_block, symI_power, symI_power]
  change ⟪power (a+k) (J g), wickBlock a b k (ck m a b ha hb _ (J u))
    (power (b+k) (J v))⟫_ℂ = _
  rw [symbol_wickBlock, LinearIsometry.inner_map_map]
  have h := contraction_matrix J m a b ha hb B u (powerH a g) (powerH b v)
  rw [symI_power, symI_power] at h
  exact congrArg (fun z => (wickCoeff a b k : ℂ) * (z * ⟪g,v⟫_ℂ ^ k)) h

/-- The normally ordered Wick operator as the sum of its homogeneous blocks. -/
def wick (a b : ℕ) (C : SymSector ℂ E b →L[ℂ] SymSector ℂ E a) (x : FockSpace E) :
    FockSpace E :=
  ∑' k : ℕ, lp.single 2 (a+k) (block a b k C (x (b+k)))

private theorem gamAdj_single (J : E →ₗᵢ[ℂ] L2T L) (n : ℕ) (x : HN L n) :
    gamAdj J (lp.single 2 n x) = lp.single 2 n (symAdj J n x) := by
  apply lp.ext
  funext m
  rw [gamAdj_sector]
  by_cases h : m = n
  · subst m
    simp only [lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ h, lp.single_apply_ne _ _ _ h, map_zero]

private theorem wick_compression (J : E →ₗᵢ[ℂ] L2T L) (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m)
    (B : SymSector ℂ E m →L[ℂ] SymSector ℂ E m) (u : E) (x : FockSpace E)
    (hx : MomentFinite (fockMapI J x)) :
    gamAdj J (wickFock a b (ck m a b ha hb (extend (symMapI J m) B) (J u)) (fockMapI J x)) =
      wick a b (contract m a b ha hb B u) x := by
  unfold wickFock wick
  rw [(gamAdj J).map_tsum (wickFock_summable a b _ hx)]
  apply tsum_congr
  intro k
  change gamAdj J (lp.single 2 (a+k) (wickBlock a b k (ck m a b ha hb _ (J u))
    (symI J (b+k) (x (b+k))))) = _
  rw [gamAdj_single, block_compression]

/-- A degree slice of the printed Wick expansion on the source Hilbert space. -/
def degree (N m j : ℕ) (B : SymSector ℂ E m →L[ℂ] SymSector ℂ E m) (u : E)
    (x : FockSpace E) : FockSpace E :=
  ∑ a ∈ Finset.range (j+1),
    if h : a ≤ m ∧ j-a ≤ m then
      (cellCoeff N m a (j-a) : ℂ) • wick a (j-a) (contract m a (j-a) h.1 h.2 B u) x
    else 0

private theorem degree_compression (J : E →ₗᵢ[ℂ] L2T L) (N m j : ℕ)
    (B : SymSector ℂ E m →L[ℂ] SymSector ℂ E m) (u : E) (x : FockSpace E)
    (hx : MomentFinite (fockMapI J x)) :
    gamAdj J (cellDeg N m j (extend (symMapI J m) B) (J u) (fockMapI J x)) = degree N m j B u x := by
  unfold cellDeg degree
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  unfold cellVec
  split_ifs with h
  · rw [map_smul, wick_compression J m a (j-a) h.1 h.2 B u x hx]
  · exact map_zero _

/-- The printed degree-zero, degree-one and degree-two terms on Fock(H).
The higher Wick orders do not enter this definition. -/
def lowOrders (K : Kernels E) (N : ℕ) (u : E) (x : FockSpace E) : FockSpace E :=
  ((N : ℝ) * symbolH K u : ℂ) • x +
    (∑' m : ℕ, degree N (m+1) 1 (K m) u x) +
    ∑' m : ℕ, degree N (m+1) 2 (K m) u x

theorem lowOrders_eq_compression (J : E →ₗᵢ[ℂ] L2T L) (K : Kernels E) (N : ℕ) (hN : 0 < N)
    (u : E) (hu : ‖u‖ = 1) (x : FockSpace E) (Q M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 < A) (_hQ : 1 ≤ Q) (hK : KBound K M A) (hs : KSelfAdj K)
    (hx : Prop021MomentsR132.NumberMoments Q x) :
    Prop021ContractsR132.lowOrders J K N u Q x hx = lowOrders K N u x := by
  let B := positiveExtension (extendKernels J K)
  let y := fockMapI J x
  have hB := positiveExtension_bound (extendKernels J K) M A (Prop022BClass1.hKJ J K M A hK)
  have hsa := positiveExtension_selfAdjoint _ (extendKernels_selfAdj J K hs)
  have hm := (Prop021MomentsR132.numberMoments_torus Q y).mp
    ((Prop021MomentsR132.numberMoments_transport J Q x).mpr hx)
  have hsm := Prop024WStepOne.mem_physSmooth_of_polyMoments Q y hm.2
  have hfin := momentFinite_of_mem ⟨y,hsm⟩
  have hu' := (J.norm_map u).trans hu
  have h₂ : y ∈ Ext005Moments.momentDomain (L := L) 2 :=
    (Prop024WWeylPhysical.mem_physSmooth_iff_moments y).mp hsm 2
  have hSmooth := Prop024WLinear.smoothOf ⟨y,hsm⟩
  have hL := Prop024WLinear.linVec_eq_linearHamiltonian N B hsa M A hA.le hB (J u) hu'
    ⟨y,hsm⟩ hSmooth
  have hQd := Prop024WQuadratic.quadVec_eq_quadraticAction N hN B hsa M A hA.le hB
    (J u) hu' h₂ hfin
  have hSymbol : Prop022ClassicalTimeR116.classicalSeries B (J u) = symbolH K u := by
    unfold Prop022ClassicalTimeR116.classicalSeries symbolH
    apply tsum_congr
    intro r
    change (⟪powerH (r+1) (J u), extend (symMapI J (r+1)) (K r)
      (powerH (r+1) (J u))⟫_ℂ).re = _
    rw [← symI_power, symI_apply, extend_apply_image, LinearIsometry.inner_map_map]
  have hdeg (j : ℕ) :
      gamAdj J (∑' m : ℕ, cellDeg N (m+1) j (B (m+1)) (J u) y) =
        ∑' m : ℕ, degree N (m+1) j (K m) u x := by
    rw [(gamAdj J).map_tsum
      (summable_norm_cellDeg N j B M A hM hA hB (J u) hu' ⟨y,hsm⟩).of_norm]
    exact tsum_congr fun m => degree_compression J N (m+1) j (K m) u x hfin
  change gamAdj J (Prop021RemainderInputR131.lowOrders B N (J u) y hSmooth h₂) = _
  unfold Prop021RemainderInputR131.lowOrders lowOrders
  rw [← hL, ← hQd, hSymbol, map_add, map_add, map_smul, gamAdj_gam]
  rw [linVec, quadVec, hdeg 1, hdeg 2]

end Torus
end QuantumNLS.Prop024WickTransportR133
