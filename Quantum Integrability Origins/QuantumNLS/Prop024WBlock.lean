import QuantumNLS.Prop024ContractionsR54
import QuantumNLS.Prop022ACoherent

/-! PROP-024 operator-level Wick expansion, module 1 (Prop024WBlock): the unscaled normally ordered Wick operator on the physical sectors.

For a bounded operator `C : HN L b →L HN L a` and `k ≥ 0` the sector block `wickBlock a b k C : HN L (b+k) →L HN L (a+k)` is `√((b+k)!(a+k)!)/k! · P_{a+k} (C ⊗ 1_k) P_{b+k}` (zero extension of `C` on the first `b` tensor slots, spectators `k`), i.e. the printed `𝒲_{a,b}(C)` of `Q7B:eq:wickbound` with norm at most `√((b+k)!(a+k)!)/k! ‖C‖ ≤ (b+k+a)^{(a+b)/2} ‖C‖`.  Proved: linearity in `C`, the norm bounds, the product-vector symbol `⟨g^{a+k}, 𝒲 h^{b+k}⟩ = c_k ⟨g^a, C h^b⟩ ⟨g,h⟩^k`, strong continuity in `C`, and that the balanced block is `(m+k)!/k!` times the frozen DEF-009 placement `U_N_r`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop024WBlock
open TensorCarrier TensorPlacements PhysicalTensor BetheCoefficientTransform KernelDefinition
open Prop022TensorCompressionR115
variable {L : ℝ} [Fact (0 < L)]

abbrev TP (L : ℝ) [Fact (0 < L)] (n : ℕ) : Type := HilbertTensorPower ℂ (L2T L) n

def extC {a b : ℕ} (C : HN L b →L[ℂ] HN L a) : TP L b →L[ℂ] TP L a :=
  (physSector L a).subtypeL ∘L C ∘L symProjToSector b

lemma extC_htpow {a b : ℕ} (C : HN L b →L[ℂ] HN L a) (h : L2T L) :
    extC C (htpow b h : TP L b) = ((C (power b h) : HN L a) : TP L a) := by
  have hproj : symProj ℂ (L2T L) b (htpow b h : TP L b) = htpow b h := by
    change groupAverage (permRep ℂ (L2T L) b) (htpow b h : TP L b) = _
    exact groupAverage_apply_of_mem (permRep ℂ (L2T L) b) (htpow_mem_symSector b h)
  have hsector : symProjToSector (H := L2T L) b (htpow b h) = power b h := by
    apply Subtype.ext
    exact hproj
  simp [extC, hsector]

def rawBlock (a b k : ℕ) (C : HN L b →L[ℂ] HN L a) : TP L (b+k) →L[ℂ] TP L (a+k) :=
  (splitIsometry (𝕜 := ℂ) (E := L2T L) a k).symm.toLinearIsometry.toContinuousLinearMap ∘L
    (htmap (extC C) (ContinuousLinearMap.id ℂ (TP L k))) ∘L
    (splitIsometry (𝕜 := ℂ) (E := L2T L) b k).toLinearIsometry.toContinuousLinearMap

def wickCoeff (a b k : ℕ) : ℝ :=
  Real.sqrt (((b+k).factorial : ℝ) * ((a+k).factorial : ℝ)) / (k.factorial : ℝ)

def wickBlock (a b k : ℕ) (C : HN L b →L[ℂ] HN L a) : HN L (b+k) →L[ℂ] HN L (a+k) :=
  ((wickCoeff a b k : ℝ) : ℂ) •
    ((physSector L (a+k)).orthogonalProjectionOnto ∘L rawBlock a b k C ∘L (physSector L (b+k)).subtypeL)

lemma wickCoeff_nonneg (a b k : ℕ) : 0 ≤ wickCoeff a b k := by
  unfold wickCoeff; positivity

lemma rawBlock_htpow (a b k : ℕ) (C : HN L b →L[ℂ] HN L a) (h : L2T L) :
    rawBlock a b k C (htpow (b+k) h : TP L (b+k)) =
      (splitIsometry (𝕜 := ℂ) (E := L2T L) a k).symm
        (htmul ((C (power b h) : HN L a) : TP L a) (htpow k h : TP L k)) := by
  unfold rawBlock
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]
  rw [KernelDefinition.split_htpow, htmap_htmul, extC_htpow]
  simp

lemma inner_proj_of_mem {n : ℕ} (x : HN L n) (y : TP L n) :
    ⟪x, (physSector L n).orthogonalProjectionOnto y⟫_ℂ = ⟪(x : TP L n), y⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply]
  rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr x.2]

/-- The symbol of a Wick block on product vectors. -/
theorem symbol_wickBlock (a b k : ℕ) (C : HN L b →L[ℂ] HN L a) (g h : L2T L) :
    ⟪power (a+k) g, wickBlock a b k C (power (b+k) h)⟫_ℂ =
      ((wickCoeff a b k : ℝ) : ℂ) * (⟪power a g, C (power b h)⟫_ℂ * ⟪g, h⟫_ℂ ^ k) := by
  unfold wickBlock
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_right]
  congr 1
  rw [inner_proj_of_mem]
  change ⟪(htpow (a+k) g : TP L (a+k)), rawBlock a b k C (htpow (b+k) h)⟫_ℂ = _
  rw [rawBlock_htpow]
  rw [← (splitIsometry (𝕜 := ℂ) (E := L2T L) a k).inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    KernelDefinition.split_htpow, inner_htmul, IntrinsicContact.inner_htpow]
  rfl


/-! ### linearity and norm -/

lemma extC_add {a b : ℕ} (C D : HN L b →L[ℂ] HN L a) : extC (C + D) = extC C + extC D := by
  ext x; simp [extC]

lemma extC_smul {a b : ℕ} (c : ℂ) (C : HN L b →L[ℂ] HN L a) : extC (c • C) = c • extC C := by
  ext x; simp [extC]

lemma norm_extC_le {a b : ℕ} (C : HN L b →L[ℂ] HN L a) : ‖extC C‖ ≤ ‖C‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg C) ?_
  intro x
  have hproj : ‖symProjToSector (H := L2T L) b x‖ ≤ ‖x‖ := by
    change ‖symProj ℂ (L2T L) b x‖ ≤ ‖x‖
    rw [symProj_eq_starProjection]
    exact (SymSector ℂ (L2T L) b).norm_starProjection_apply_le x
  calc ‖extC C x‖ = ‖C (symProjToSector b x)‖ := rfl
    _ ≤ ‖C‖ * ‖symProjToSector b x‖ := C.le_opNorm _
    _ ≤ ‖C‖ * ‖x‖ := mul_le_mul_of_nonneg_left hproj (norm_nonneg C)

lemma rawBlock_add (a b k : ℕ) (C D : HN L b →L[ℂ] HN L a) :
    rawBlock a b k (C + D) = rawBlock a b k C + rawBlock a b k D := by
  unfold rawBlock
  rw [extC_add, htmap_add_left]
  ext x; simp

lemma rawBlock_smul (a b k : ℕ) (c : ℂ) (C : HN L b →L[ℂ] HN L a) :
    rawBlock a b k (c • C) = c • rawBlock a b k C := by
  unfold rawBlock
  rw [extC_smul, htmap_smul_left]
  ext x; simp

lemma wickBlock_apply (a b k : ℕ) (C : HN L b →L[ℂ] HN L a) (z : HN L (b+k)) :
    wickBlock a b k C z = ((wickCoeff a b k : ℝ) : ℂ) •
      (physSector L (a+k)).orthogonalProjectionOnto (rawBlock a b k C (z : TP L (b+k))) := rfl

lemma wickBlock_add (a b k : ℕ) (C D : HN L b →L[ℂ] HN L a) :
    wickBlock a b k (C + D) = wickBlock a b k C + wickBlock a b k D := by
  ext z : 1
  rw [ContinuousLinearMap.add_apply, wickBlock_apply, wickBlock_apply, wickBlock_apply, rawBlock_add,
    ContinuousLinearMap.add_apply, map_add, smul_add]

lemma wickBlock_smul (a b k : ℕ) (c : ℂ) (C : HN L b →L[ℂ] HN L a) :
    wickBlock a b k (c • C) = c • wickBlock a b k C := by
  ext z : 1
  rw [ContinuousLinearMap.smul_apply, wickBlock_apply, wickBlock_apply, rawBlock_smul,
    ContinuousLinearMap.smul_apply, map_smul, smul_comm]

lemma wickBlock_zero (a b k : ℕ) : wickBlock a b k (0 : HN L b →L[ℂ] HN L a) = 0 := by
  have h := wickBlock_add (L := L) a b k 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

lemma wickBlock_sub (a b k : ℕ) (C D : HN L b →L[ℂ] HN L a) :
    wickBlock a b k (C - D) = wickBlock a b k C - wickBlock a b k D := by
  have h := wickBlock_add (L := L) a b k (C - D) D
  rw [sub_add_cancel] at h
  rw [h]; abel

lemma norm_wickBlock_apply_le (a b k : ℕ) (C : HN L b →L[ℂ] HN L a) (z : HN L (b+k)) :
    ‖wickBlock a b k C z‖ ≤ wickCoeff a b k * ‖C‖ * ‖z‖ := by
  rw [wickBlock_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (wickCoeff_nonneg a b k)]
  have h1 : ‖(physSector L (a+k)).orthogonalProjectionOnto (rawBlock a b k C (z : TP L (b+k)))‖ ≤
      ‖rawBlock a b k C (z : TP L (b+k))‖ := Submodule.norm_orthogonalProjectionOnto_apply_le _ _
  have h2 : ‖rawBlock a b k C (z : TP L (b+k))‖ ≤ ‖C‖ * ‖z‖ := by
    unfold rawBlock
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine (mul_le_mul (norm_htmap_le _ _) le_rfl (norm_nonneg _) (by positivity)).trans ?_
    simp only [LinearIsometryEquiv.norm_map]
    have := norm_extC_le C
    have h3 : ‖(ContinuousLinearMap.id ℂ (TP L k))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖extC C‖ * ‖(ContinuousLinearMap.id ℂ (TP L k))‖ * ‖(z : TP L (b+k))‖
        ≤ ‖C‖ * 1 * ‖z‖ :=
          mul_le_mul (mul_le_mul this h3 (norm_nonneg (ContinuousLinearMap.id ℂ (TP L k))) (norm_nonneg C)) (le_of_eq rfl)
            (norm_nonneg _) (by positivity)
      _ = ‖C‖ * ‖z‖ := by ring
  calc wickCoeff a b k * ‖(physSector L (a+k)).orthogonalProjectionOnto (rawBlock a b k C (z : TP L (b+k)))‖
      ≤ wickCoeff a b k * (‖C‖ * ‖z‖) := mul_le_mul_of_nonneg_left (h1.trans h2) (wickCoeff_nonneg a b k)
    _ = _ := by ring


/-! ### strong continuity in the kernel -/

open Filter Topology in
lemma tendsto_of_dense_bounded {ι : Type*} {l : Filter ι} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : ι → E →L[ℂ] F) (T0 : E →L[ℂ] F) (K : ℝ) (hK : ∀ i, ‖T i‖ ≤ K) (S : Set E)
    (hS : Dense S) (hconv : ∀ x ∈ S, Tendsto (fun i => T i x) l (𝓝 (T0 x))) (x : E) :
    Tendsto (fun i => T i x) l (𝓝 (T0 x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M : ℝ := max K 0 + ‖T0‖ + 1 with hM
  have hMpos : 0 < M := by
    have := le_max_right K 0
    have := norm_nonneg T0
    linarith
  obtain ⟨y, hyS, hy⟩ := hS.exists_dist_lt x (show 0 < ε / (3 * M) by positivity)
  have hy' : ‖x - y‖ < ε / (3 * M) := by rwa [dist_eq_norm] at hy
  filter_upwards [(Metric.tendsto_nhds.mp (hconv y hyS)) (ε / 3) (by positivity)] with i hi
  rw [dist_eq_norm] at hi ⊢
  have h1 : ‖T i (x - y)‖ ≤ M * ‖x - y‖ := by
    refine (T i).le_opNorm _ |>.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have := le_max_left K 0
    have := norm_nonneg T0
    linarith [hK i]
  have h2 : ‖T0 (x - y)‖ ≤ M * ‖x - y‖ := by
    refine T0.le_opNorm _ |>.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have := le_max_right K 0
    linarith
  have h3 : T i x - T0 x = T i (x - y) + (T i y - T0 y) - T0 (x - y) := by
    simp only [map_sub]; abel
  have h4 : M * ‖x - y‖ < ε / 3 := by
    calc M * ‖x - y‖ < M * (ε / (3 * M)) := mul_lt_mul_of_pos_left hy' hMpos
      _ = ε / 3 := by field_simp
  rw [h3]
  calc ‖T i (x - y) + (T i y - T0 y) - T0 (x - y)‖
      ≤ ‖T i (x - y)‖ + ‖T i y - T0 y‖ + ‖T0 (x - y)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ < ε := by linarith

/-- `y ↦ ⟨x ⊗ y⟩` in the first slot. -/
def htmulL {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (y : F) : E →L[ℂ] HilbertTensor ℂ E F :=
  LinearMap.mkContinuous
    { toFun := fun x => htmul x y
      map_add' := fun x x' => htmul_add_left x x' y
      map_smul' := fun c x => htmul_smul_left c x y } ‖y‖ (by
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_htmul]
    exact le_of_eq (mul_comm _ _))

lemma htmulL_apply {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (y : F) (x : E) : htmulL y x = htmul x y := rfl

open Filter Topology in
lemma tendsto_htmap_left {ι : Type*} {l : Filter ι} {E G F K' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    (f : ι → E →L[ℂ] G) (f0 : E →L[ℂ] G) (K : ℝ) (hK : ∀ i, ‖f i‖ ≤ K)
    (hconv : ∀ x, Tendsto (fun i => f i x) l (𝓝 (f0 x))) (g : F →L[ℂ] K')
    (z : HilbertTensor ℂ E F) :
    Tendsto (fun i => htmap (f i) g z) l (𝓝 (htmap f0 g z)) := by
  refine tendsto_of_dense_bounded (fun i => htmap (f i) g) (htmap f0 g) (K * ‖g‖) ?_
    (Submodule.span ℂ (Set.range fun p : E × F => (htmul p.1 p.2 : HilbertTensor ℂ E F)) : Set _) ?_ ?_ z
  · intro i
    refine (norm_htmap_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _)
  · have := (span_htmul_dense (𝕜 := ℂ) (E := E) (F := F))
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact this
  · intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨⟨x, y⟩, rfl⟩ := hw
        simp only [htmap_htmul]
        have : Tendsto (fun i => htmulL (g y) (f i x)) l (𝓝 (htmulL (g y) (f0 x))) :=
          ((htmulL (g y)).continuous.tendsto _).comp (hconv x)
        simpa [htmulL_apply] using this
    | zero => simpa using tendsto_const_nhds
    | add w w' _ _ h h' => simpa using h.add h'
    | smul c w _ h => simpa using h.const_smul c

open Filter Topology in
lemma tendsto_wickBlock {ι : Type*} {l : Filter ι} (a b k : ℕ) (C : ι → HN L b →L[ℂ] HN L a)
    (C0 : HN L b →L[ℂ] HN L a) (K : ℝ) (hK : ∀ i, ‖C i‖ ≤ K)
    (hconv : ∀ x, Tendsto (fun i => C i x) l (𝓝 (C0 x))) (z : HN L (b+k)) :
    Tendsto (fun i => wickBlock a b k (C i) z) l (𝓝 (wickBlock a b k C0 z)) := by
  have hext : ∀ x, Tendsto (fun i => extC (C i) x) l (𝓝 (extC C0 x)) := by
    intro x
    have := ((physSector L a).subtypeL.continuous.tendsto _).comp (hconv (symProjToSector b x))
    simpa [extC, Function.comp_def] using this
  have hraw : Tendsto (fun i => rawBlock a b k (C i) (z : TP L (b+k))) l
      (𝓝 (rawBlock a b k C0 (z : TP L (b+k)))) := by
    have h := tendsto_htmap_left (fun i => extC (C i)) (extC C0) K
      (fun i => (norm_extC_le _).trans (hK i)) hext (ContinuousLinearMap.id ℂ (TP L k))
      ((splitIsometry (𝕜 := ℂ) (E := L2T L) b k) (z : TP L (b+k)))
    have h2 := ((splitIsometry (𝕜 := ℂ) (E := L2T L) a k).symm.continuous.tendsto _).comp h
    simpa [rawBlock, Function.comp_def] using h2
  have h3 := (((physSector L (a+k)).orthogonalProjectionOnto.continuous.tendsto _).comp hraw)
  have h4 := h3.const_smul (((wickCoeff a b k : ℝ) : ℂ))
  simpa [wickBlock_apply] using h4


/-! ### the balanced block is the DEF-009 placement -/

lemma rawBlock_balanced (m k : ℕ) (B : HN L m →L[ℂ] HN L m) :
    rawBlock m m k B = firstPlacement (q := k) B := rfl

lemma wickCoeff_balanced (m k : ℕ) :
    wickCoeff m m k = (((m+k).factorial : ℝ) / (k.factorial : ℝ)) := by
  unfold wickCoeff
  rw [← sq (((m+k).factorial : ℕ) : ℝ)] 
  rw [Real.sqrt_sq (by positivity)]

lemma wickBlock_balanced (m k : ℕ) (B : HN L m →L[ℂ] HN L m) (z : HN L (m+k)) :
    wickBlock m m k B z = ((wickCoeff m m k : ℝ) : ℂ) • (U_N_r (r := m) (q := k) B z) := by
  apply Subtype.ext
  rw [wickBlock_apply]
  rw [Submodule.coe_smul, Submodule.coe_smul]
  congr 1
  rw [Submodule.coe_orthogonalProjectionOnto_apply, ← symProj_eq_starProjection]
  have hz : symProj ℂ (L2T L) (m+k) (z : TP L (m+k)) = z := by
    change groupAverage (permRep ℂ (L2T L) (m+k)) (z : TP L (m+k)) = _
    exact groupAverage_apply_of_mem (permRep ℂ (L2T L) (m+k)) z.2
  rw [U_N_r_eq_sandwich]
  change _ = symProj ℂ (L2T L) (m+k) (firstPlacement (q := k) B (symProj ℂ (L2T L) (m+k) (z : TP L (m+k))))
  rw [hz]
  rfl


/-! ### the coefficient -/

lemma wickCoeff_sq (a b k : ℕ) :
    wickCoeff a b k ^ 2 =
      (((b+k).descFactorial b : ℕ) : ℝ) * (((a+k).descFactorial a : ℕ) : ℝ) := by
  have hb : ((b+k).factorial : ℝ) = (k.factorial : ℝ) * (((b+k).descFactorial b : ℕ) : ℝ) := by
    have := Nat.factorial_mul_descFactorial (show b ≤ b + k by omega)
    rw [Nat.add_sub_cancel_left] at this
    exact_mod_cast this.symm
  have ha : ((a+k).factorial : ℝ) = (k.factorial : ℝ) * (((a+k).descFactorial a : ℕ) : ℝ) := by
    have := Nat.factorial_mul_descFactorial (show a ≤ a + k by omega)
    rw [Nat.add_sub_cancel_left] at this
    exact_mod_cast this.symm
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  unfold wickCoeff
  rw [div_pow, Real.sq_sqrt (by positivity), hb, ha]
  field_simp

lemma wickCoeff_sq_le (a b k : ℕ) :
    wickCoeff a b k ^ 2 ≤ (((b+k+a : ℕ) : ℝ)) ^ (a+b) := by
  rw [wickCoeff_sq]
  have h1 : (((b+k).descFactorial b : ℕ) : ℝ) ≤ (((b+k+a : ℕ) : ℝ)) ^ b := by
    calc (((b+k).descFactorial b : ℕ) : ℝ) ≤ (((b+k : ℕ) : ℝ)) ^ b := by
          exact_mod_cast Nat.descFactorial_le_pow (b+k) b
      _ ≤ (((b+k+a : ℕ) : ℝ)) ^ b := by
          apply pow_le_pow_left₀ (by positivity); exact_mod_cast Nat.le_add_right _ _
  have h2 : (((a+k).descFactorial a : ℕ) : ℝ) ≤ (((b+k+a : ℕ) : ℝ)) ^ a := by
    calc (((a+k).descFactorial a : ℕ) : ℝ) ≤ (((a+k : ℕ) : ℝ)) ^ a := by
          exact_mod_cast Nat.descFactorial_le_pow (a+k) a
      _ ≤ (((b+k+a : ℕ) : ℝ)) ^ a := by
          apply pow_le_pow_left₀ (by positivity); exact_mod_cast (by omega : a + k ≤ b + k + a)
  calc _ ≤ (((b+k+a : ℕ) : ℝ)) ^ b * (((b+k+a : ℕ) : ℝ)) ^ a :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by rw [← pow_add, add_comm b a]

end QuantumNLS.Prop024WBlock

#print axioms QuantumNLS.Prop024WBlock.wickBlock_apply
#print axioms QuantumNLS.Prop024WBlock.norm_wickBlock_apply_le
#print axioms QuantumNLS.Prop024WBlock.symbol_wickBlock
#print axioms QuantumNLS.Prop024WBlock.tendsto_wickBlock
#print axioms QuantumNLS.Prop024WBlock.wickBlock_balanced
#print axioms QuantumNLS.Prop024WBlock.wickCoeff_sq_le
#print axioms QuantumNLS.Prop024WBlock.wickBlock_add
#print axioms QuantumNLS.Prop024WBlock.wickBlock_smul

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WBlock." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WBlock." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop024WBlock aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
