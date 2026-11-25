import QuantumNLS.Prop024WMonomial
import QuantumNLS.Prop024ContractionsR54
import QuantumNLS.Prop022ACoherent
import QuantumNLS.Prop022AWeyl
import QuantumNLS.Prop024WBlock
import QuantumNLS.Prop024WSector
import QuantumNLS.Prop024WWords
import Mathlib.Analysis.Normed.Group.Tannery

/-! PROP-024 operator-level Wick expansion, module 4 (Prop024WOrder): the per-order Weyl translation identity.

Main theorem `perOrder`: for every bounded kernel `B_m : HN L m →L HN L m`, every smooth vector `y` and `N ≥ 1`, with `W = physicalWeyl N u = printedWeyl (√N u)` and the printed contraction kernels `contractedKernel m a b = ck m a b`,
`W⁻¹ (N^{1-m} 𝒲_{m,m}(B_m)) W y = ∑_{a,b ≤ m} N^{1-(a+b)/2} C(m,a) C(m,b) 𝒲_{a,b}(C_{m,a,b}(u)) y`.
Proof: (i) rank-one power kernels `|g^m⟩⟨f^m|`: `𝒲_{m,m}` is the word `a*(g)^m a(f)^m` (module 3), its Weyl conjugate is `(a*(g)+⟨v,g⟩)^m (a(f)+⟨f,v⟩)^m` (`weyl_affine_action`), expanded by the binomial theorem, and the contraction of `|g^m⟩⟨f^m|` is `⟨u,g⟩^{m-a}⟨f,u⟩^{m-b} |g^a⟩⟨f^b|` (`ck_rk`); (ii) both sides are linear in `B_m`; (iii) every kernel is the strong limit of a bounded net of finite combinations of such kernels (`exists_strong_approx`, from the frozen `powers_total`), and both sides are strongly continuous (`tendsto_wickFock`, dominated convergence in the Fock norm `fock_tendsto`). -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
open Filter
namespace QuantumNLS.Prop024WOrder
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop022ACoherent Prop022TensorCompressionR115
open Prop024WBlock Prop024WSector Prop024WWords
variable {L : ℝ} [Fact (0 < L)]

/-- Dominated sector-wise convergence in the Fock space. -/
lemma fock_tendsto {ι : Type*} {l : Filter ι} (F : ι → Fock L) (F0 : Fock L)
    (hconv : ∀ n, Tendsto (fun i => (F i : Fock L) n) l (𝓝 (F0 n)))
    (d : ℕ → ℝ) (hd : Summable (fun n => d n ^ 2)) (hb : ∀ i n, ‖(F i : Fock L) n‖ ≤ d n)
    (hb0 : ∀ n, ‖F0 n‖ ≤ d n) : Tendsto F l (𝓝 F0) := by
  have hsq : ∀ i, ‖F i - F0‖ ^ 2 = ∑' n, ‖(F i : Fock L) n - F0 n‖ ^ 2 := by
    intro i
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (F i - F0)
    simpa [Real.rpow_two] using h
  have hT : Tendsto (fun i => ∑' n, ‖(F i : Fock L) n - F0 n‖ ^ 2) l (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := l) (G := ℝ)
      (f := fun i n => ‖(F i : Fock L) n - F0 n‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun n => 4 * d n ^ 2) (hd.mul_left 4)
      (fun n => by
        have h1 := (hconv n).sub_const (F0 n)
        have h2 := (continuous_norm.tendsto _).comp h1
        have h3 := (continuous_pow 2 |>.tendsto _).comp h2
        simpa [Function.comp_def] using h3)
      (Eventually.of_forall (fun i n => by
        have h1 : ‖(F i : Fock L) n - F0 n‖ ≤ 2 * d n :=
          (norm_sub_le _ _).trans (by linarith [hb i n, hb0 n])
        have h2 : 0 ≤ ‖(F i : Fock L) n - F0 n‖ := norm_nonneg _
        rw [Real.norm_of_nonneg (by positivity)]
        calc ‖(F i : Fock L) n - F0 n‖ ^ 2 ≤ (2 * d n) ^ 2 := pow_le_pow_left₀ h2 h1 2
          _ = 4 * d n ^ 2 := by ring))
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun i => Real.sqrt (∑' n, ‖(F i : Fock L) n - F0 n‖ ^ 2)) l (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto _).comp hT
  rw [Real.sqrt_zero] at h2
  refine h2.congr (fun i => ?_)
  rw [← hsq i, Real.sqrt_sq (norm_nonneg _)]


/-! ### Summability and sector components of the Wick operator -/

/-- All polynomial number moments are finite. -/
def MomentFinite (y : Fock L) : Prop := ∀ p : ℕ, Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p * ‖y n‖ ^ 2)

lemma momentFinite_of_mem (y : physSmooth L) : MomentFinite y.1 := by
  intro p
  have h := (mem_physSmooth_iff_moments y.1).mp y.2 p
  rw [Ext005Moments.momentDomain_iff] at h
  exact h

lemma orthFamily_incl (a : ℕ) :
    OrthogonalFamily ℂ (fun k : ℕ => HN L (a+k)) (fun k => inclusion L (a+k)) := by
  intro i j hij v w
  exact inner_incl_incl_ne (a+j) (a+i) (by omega) w v

lemma wick_sq_summable (a b : ℕ) {y : Fock L} (hy : MomentFinite y) :
    Summable (fun k : ℕ => (wickCoeff a b k * ‖y (b+k)‖) ^ 2) := by
  have hs : Summable (fun k : ℕ => ((a+1 : ℝ) ^ (a+b)) * (((b+k : ℕ) : ℝ) + 1) ^ (a+b) * ‖y (b+k)‖ ^ 2) := by
    have h1 := (hy (a+b)).comp_injective (show Function.Injective (fun k : ℕ => b + k) from fun x y h => by simpa using h)
    exact (h1.mul_left ((a+1 : ℝ) ^ (a+b))).congr (fun k => by simp only [Function.comp]; ring)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
  rw [mul_pow]
  have h1 := wickCoeff_sq_le a b k
  have h2 : (((b+k+a : ℕ) : ℝ)) ^ (a+b) ≤ ((a+1 : ℝ) ^ (a+b)) * (((b+k : ℕ) : ℝ) + 1) ^ (a+b) := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b, Nat.cast_nonneg (α := ℝ) k,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (Nat.cast_nonneg (α := ℝ) b),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (Nat.cast_nonneg (α := ℝ) k)]
  exact mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)


lemma wickFock_summable (a b : ℕ) (C : HN L b →L[ℂ] HN L a) {y : Fock L} (hy : MomentFinite y) :
    Summable (fun k : ℕ => inclusion L (a+k) (wickBlock a b k C (y (b+k)))) := by
  rw [(orthFamily_incl a).summable_iff_norm_sq_summable (fun k => wickBlock a b k C (y (b+k)))]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((wick_sq_summable a b hy).mul_left (‖C‖ ^ 2))
  have h := norm_wickBlock_apply_le a b k C (y (b+k))
  calc ‖wickBlock a b k C (y (b+k))‖ ^ 2 ≤ (wickCoeff a b k * ‖C‖ * ‖y (b+k)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ‖C‖ ^ 2 * (wickCoeff a b k * ‖y (b+k)‖) ^ 2 := by ring

lemma projection_incl_ne (n m : ℕ) (hnm : n ≠ m) (w : HN L m) :
    projection L n (inclusion L m w) = 0 := by
  rw [projection_eq_single]
  change lp.single 2 n ((lp.single 2 m w : Fock L) n) = 0
  rw [lp.single_apply_ne _ _ _ hnm]
  simp

lemma projection_incl_self (m : ℕ) (w : HN L m) :
    projection L m (inclusion L m w) = inclusion L m w := by
  rw [projection_eq_single]
  change lp.single 2 m ((lp.single 2 m w : Fock L) m) = _
  rw [lp.single_apply_self]; rfl

lemma inclusion_injective_sector (m : ℕ) {w w' : HN L m} (h : inclusion L m w = inclusion L m w') : w = w' :=
  (inclusion L m).injective h

lemma wickFock_sector (a b : ℕ) (C : HN L b →L[ℂ] HN L a) {y : Fock L} (hy : MomentFinite y) (k0 : ℕ) :
    (wickFock a b C y) (a+k0) = wickBlock a b k0 C (y (b+k0)) := by
  have hV := (wickFock_summable a b C hy).hasSum
  have hP := (projection L (a+k0)).hasSum hV
  have hS : HasSum (fun k => projection L (a+k0) (inclusion L (a+k) (wickBlock a b k C (y (b+k)))))
      (inclusion L (a+k0) (wickBlock a b k0 C (y (b+k0)))) := by
    have := hasSum_single (f := fun k => projection L (a+k0) (inclusion L (a+k) (wickBlock a b k C (y (b+k))))) k0
      (fun k hk => projection_incl_ne _ _ (by omega) _)
    rwa [projection_incl_self] at this
  have := hP.unique hS
  unfold wickFock
  apply inclusion_injective_sector (a+k0)
  rw [inclusion_eq_projection]
  exact this

lemma wickFock_sector_lt (a b : ℕ) (C : HN L b →L[ℂ] HN L a) {y : Fock L} (hy : MomentFinite y)
    (j : ℕ) (hj : j < a) : (wickFock a b C y) j = 0 := by
  have hV := (wickFock_summable a b C hy).hasSum
  have hP := (projection L j).hasSum hV
  have hS : HasSum (fun k => projection L j (inclusion L (a+k) (wickBlock a b k C (y (b+k))))) 0 := by
    have : (fun k => projection L j (inclusion L (a+k) (wickBlock a b k C (y (b+k))))) = fun _ => 0 :=
      funext (fun k => projection_incl_ne _ _ (by omega) _)
    rw [this]; exact hasSum_zero
  have h0 := hP.unique hS
  rw [projection_eq_single] at h0
  have := congrArg (fun v : Fock L => v j) h0
  unfold wickFock
  simpa [lp.single_apply_self] using this


lemma fock_ext_sectors (a : ℕ) (x x' : Fock L) (h0 : ∀ j < a, x j = x' j)
    (hk : ∀ k, x (a+k) = x' (a+k)) : x = x' := by
  apply lp.ext
  funext j
  by_cases hj : j < a
  · exact h0 j hj
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hj)
    exact hk k

lemma wickFock_add (a b : ℕ) (C D : HN L b →L[ℂ] HN L a) {y : Fock L} (hy : MomentFinite y) :
    wickFock a b (C + D) y = wickFock a b C y + wickFock a b D y := by
  apply fock_ext_sectors a
  · intro j hj
    rw [wickFock_sector_lt a b _ hy j hj]
    change _ = (wickFock a b C y) j + (wickFock a b D y) j
    rw [wickFock_sector_lt a b _ hy j hj, wickFock_sector_lt a b _ hy j hj, add_zero]
  · intro k
    change _ = (wickFock a b C y) (a+k) + (wickFock a b D y) (a+k)
    rw [wickFock_sector a b _ hy, wickFock_sector a b _ hy, wickFock_sector a b _ hy, wickBlock_add]
    rfl

lemma wickFock_smul (a b : ℕ) (c : ℂ) (C : HN L b →L[ℂ] HN L a) {y : Fock L} (hy : MomentFinite y) :
    wickFock a b (c • C) y = c • wickFock a b C y := by
  apply fock_ext_sectors a
  · intro j hj
    rw [wickFock_sector_lt a b _ hy j hj]
    change _ = c • (wickFock a b C y) j
    rw [wickFock_sector_lt a b _ hy j hj, smul_zero]
  · intro k
    change _ = c • (wickFock a b C y) (a+k)
    rw [wickFock_sector a b _ hy, wickFock_sector a b _ hy, wickBlock_smul]
    rfl

lemma wickFock_zero (a b : ℕ) {y : Fock L} (hy : MomentFinite y) :
    wickFock a b (0 : HN L b →L[ℂ] HN L a) y = 0 := by
  have h := wickFock_add a b (0 : HN L b →L[ℂ] HN L a) 0 hy
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

lemma tendsto_wickFock {ι : Type*} {l : Filter ι} (a b : ℕ) (C : ι → HN L b →L[ℂ] HN L a)
    (C0 : HN L b →L[ℂ] HN L a) (K : ℝ) (hK : ∀ i, ‖C i‖ ≤ K) (hK0 : ‖C0‖ ≤ K)
    (hconv : ∀ x, Tendsto (fun i => C i x) l (𝓝 (C0 x))) {y : Fock L} (hy : MomentFinite y) :
    Tendsto (fun i => wickFock a b (C i) y) l (𝓝 (wickFock a b C0 y)) := by
  set ny : ℕ → ℝ := fun n => ‖y n‖ with hny
  set d : ℕ → ℝ := fun n => if a ≤ n then wickCoeff a b (n-a) * K * ny (b+(n-a)) else 0 with hd
  have hK' : 0 ≤ K := le_trans (norm_nonneg C0) hK0
  have hda : ∀ k, d (a+k) = wickCoeff a b k * K * ‖y (b+k)‖ := by
    intro k; simp only [hd]; rw [if_pos (Nat.le_add_right a k), Nat.add_sub_cancel_left]
  have hda' : ∀ k, d (k+a) = wickCoeff a b k * K * ‖y (b+k)‖ := by
    intro k; rw [Nat.add_comm, hda]
  have hdlt : ∀ n, n < a → d n = 0 := by
    intro n hn; simp [hd, not_le.mpr hn]
  have hdsum : Summable (fun n => d n ^ 2) := by
    rw [← summable_nat_add_iff a]
    have h1 := (wick_sq_summable a b hy).mul_left (K ^ 2)
    refine h1.congr (fun k => ?_)
    simp only [hda']
    ring
  refine fock_tendsto _ _ ?_ d hdsum ?_ ?_
  · intro n
    by_cases hn : n < a
    · simp only [wickFock_sector_lt a b _ hy n hn]
      exact tendsto_const_nhds
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hn)
      simp only [wickFock_sector a b _ hy k]
      exact tendsto_wickBlock a b k C C0 K hK hconv (y (b+k))
  · intro i n
    by_cases hn : n < a
    · rw [wickFock_sector_lt a b _ hy n hn, hdlt n hn]; simp
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hn)
      rw [wickFock_sector a b _ hy k, hda]
      refine (norm_wickBlock_apply_le a b k _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hK i) (wickCoeff_nonneg a b k)) (norm_nonneg _)
  · intro n
    by_cases hn : n < a
    · rw [wickFock_sector_lt a b _ hy n hn, hdlt n hn]; simp
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hn)
      rw [wickFock_sector a b _ hy k, hda]
      refine (norm_wickBlock_apply_le a b k _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK0 (wickCoeff_nonneg a b k)) (norm_nonneg _)

end QuantumNLS.Prop024WOrder



set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
open Filter
namespace QuantumNLS.Prop024WOrder
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop022ACoherent Prop022TensorCompressionR115
open Prop024WBlock Prop024WSector Prop024WWords Prop024ContractionsR54
variable {L : ℝ} [Fact (0 < L)]

lemma insertSector_coe (r a : ℕ) (ha : a ≤ r + a) (u : L2T L) (x : HN L a) :
    ((insertSector (r+a) a ha u x : HN L (r+a)) : TP L (r+a)) = ((insertion r a u x : HN L (r+a)) : TP L (r+a)) := by
  have key : ∀ (r' : ℕ) (h : r' = r) (h' : r' + a = r + a),
      ((castSectorMapCod h' (insertion r' a u) x : HN L (r+a)) : TP L (r+a)) =
        ((insertion r a u x : HN L (r+a)) : TP L (r+a)) := by
    intro r' h h'
    subst h
    rfl
  exact key (r + a - a) (by omega) _

lemma inner_insertion_power (r a : ℕ) (u g : L2T L) (x : HN L a) :
    ⟪(insertion r a u x : HN L (r+a)), power (r+a) g⟫_ℂ = ⟪u, g⟫_ℂ ^ r * ⟪x, power a g⟫_ℂ := by
  rw [Submodule.coe_inner]
  unfold insertion
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Submodule.coe_orthogonalProjectionOnto_apply]
  change ⟪(physSector L (r+a)).starProjection ((splitIsometry (𝕜 := ℂ) (E := L2T L) r a).symm
      (htmul (htpow r u) (x : TP L a))), (htpow (r+a) g : TP L (r+a))⟫_ℂ = _
  have hp : (physSector L (r+a)).starProjection (htpow (r+a) g : TP L (r+a)) = htpow (r+a) g :=
    Submodule.starProjection_eq_self_iff.mpr (htpow_mem_symSector (r+a) g)
  rw [Submodule.inner_starProjection_left_eq_right, hp]
  rw [← (splitIsometry (𝕜 := ℂ) (E := L2T L) r a).inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    KernelDefinition.split_htpow, inner_htmul, IntrinsicContact.inner_htpow]
  rfl

lemma insertSector_adjoint_power (m a : ℕ) (ha : a ≤ m) (u g : L2T L) :
    (insertSector m a ha u).adjoint (power m g) = ⟪u, g⟫_ℂ ^ (m - a) • power a g := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' ha
  apply ext_inner_sector
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, inner_smul_right, Nat.add_sub_cancel, Submodule.coe_inner,
    insertSector_coe r a ha u x, ← Submodule.coe_inner, inner_insertion_power]

lemma inner_insertSector_power (m b : ℕ) (hb : b ≤ m) (u f : L2T L) (x : HN L b) :
    ⟪insertSector m b hb u x, power m f⟫_ℂ = ⟪u, f⟫_ℂ ^ (m - b) * ⟪x, power b f⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, insertSector_adjoint_power, inner_smul_right]

lemma insertSector_power_inner (m b : ℕ) (hb : b ≤ m) (u f : L2T L) (x : HN L b) :
    ⟪power m f, insertSector m b hb u x⟫_ℂ = ⟪f, u⟫_ℂ ^ (m - b) * ⟪power b f, x⟫_ℂ := by
  have h := congrArg (starRingEnd ℂ) (inner_insertSector_power m b hb u f x)
  rw [inner_conj_symm, map_mul, map_pow, inner_conj_symm, inner_conj_symm] at h
  exact h

/-- The contracted kernel with an arbitrary single kernel `Bm` of order `m`. -/
def ck (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) :
    HN L b →L[ℂ] HN L a :=
  (insertSector m a ha u).adjoint ∘L Bm ∘L insertSector m b hb u

lemma contractedKernel_eq_ck (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) :
    contractedKernel m a b ha hb B u = ck m a b ha hb (B m) u := rfl

/-- The contracted kernel of a rank-one power kernel. -/
lemma ck_rk (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) (g f u : L2T L) :
    ck m a b ha hb (rk m m g f) u =
      (⟪u, g⟫_ℂ ^ (m - a) * ⟪f, u⟫_ℂ ^ (m - b)) • rk a b g f := by
  ext x : 1
  change (insertSector m a ha u).adjoint (rk m m g f (insertSector m b hb u x)) = _
  rw [rk_apply, insertSector_power_inner, map_smul, insertSector_adjoint_power,
    ContinuousLinearMap.smul_apply, rk_apply, smul_smul, smul_smul]
  congr 1
  ring


/-! ### Strong approximation of kernels by rank-one power kernels -/

/-- The span of the rank-one power kernels. -/
def powerKernels (m : ℕ) : Submodule ℂ (HN L m →L[ℂ] HN L m) :=
  Submodule.span ℂ (Set.range (fun p : L2T L × L2T L => rk m m p.1 p.2))

lemma rk_eq_rankOne (m : ℕ) (g f : L2T L) :
    rk m m g f = InnerProductSpace.rankOne ℂ (power m g) (power m f) := by
  ext x : 1
  rw [rk_apply, InnerProductSpace.rankOne_apply]

lemma rankOne_mem_powerKernels (m : ℕ) {x x' : HN L m}
    (hx : x ∈ Submodule.span ℂ (Set.range (power (L := L) m)))
    (hx' : x' ∈ Submodule.span ℂ (Set.range (power (L := L) m))) :
    InnerProductSpace.rankOne ℂ x x' ∈ powerKernels (L := L) m := by
  induction hx using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨g, rfl⟩ := hp
    induction hx' using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨f, rfl⟩ := hq
      rw [← rk_eq_rankOne]
      exact Submodule.subset_span ⟨(g, f), rfl⟩
    | zero => simp
    | add q q' _ _ h h' =>
      have : InnerProductSpace.rankOne ℂ (power m g) (q + q') =
          InnerProductSpace.rankOne ℂ (power m g) q + InnerProductSpace.rankOne ℂ (power m g) q' := by
        ext z : 1; simp [inner_add_left, add_smul]
      rw [this]; exact Submodule.add_mem _ h h'
    | smul c q _ h =>
      have : InnerProductSpace.rankOne ℂ (power m g) (c • q) =
          (starRingEnd ℂ c) • InnerProductSpace.rankOne ℂ (power m g) q := by
        ext z : 1; simp [inner_smul_left, smul_smul]
      rw [this]; exact Submodule.smul_mem _ _ h
  | zero => simp
  | add p p' _ _ h h' =>
    have : InnerProductSpace.rankOne ℂ (p + p') x' =
        InnerProductSpace.rankOne ℂ p x' + InnerProductSpace.rankOne ℂ p' x' := by
      ext z : 1; simp [add_smul]
    rw [this]; exact Submodule.add_mem _ h h'
  | smul c p _ h =>
    have : InnerProductSpace.rankOne ℂ (c • p) x' = c • InnerProductSpace.rankOne ℂ p x' := by
      ext z : 1; simp [smul_smul]
    rw [this]; exact Submodule.smul_mem _ _ h


open Classical in
/-- The finite-dimensional span of finitely many power vectors. -/
def powSpan (m : ℕ) (F : Finset (L2T L)) : Submodule ℂ (HN L m) :=
  Submodule.span ℂ ((power (L := L) m) '' (F : Set (L2T L)))

instance powSpan_fd (m : ℕ) (F : Finset (L2T L)) : FiniteDimensional ℂ (powSpan (L := L) m F) := by
  unfold powSpan
  exact FiniteDimensional.span_of_finite ℂ (F.finite_toSet.image _)

lemma powSpan_mono (m : ℕ) {F F' : Finset (L2T L)} (h : F ⊆ F') : powSpan (L := L) m F ≤ powSpan m F' := by
  unfold powSpan
  exact Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

lemma powSpan_le (m : ℕ) (F : Finset (L2T L)) :
    powSpan (L := L) m F ≤ Submodule.span ℂ (Set.range (power (L := L) m)) := by
  unfold powSpan
  exact Submodule.span_mono (Set.image_subset_range _ _)

/-- The approximating kernel `P_F B P_F`. -/
def approxKernel (m : ℕ) (F : Finset (L2T L)) (B : HN L m →L[ℂ] HN L m) : HN L m →L[ℂ] HN L m :=
  (powSpan m F).starProjection ∘L B ∘L (powSpan m F).starProjection

lemma norm_approxKernel_le (m : ℕ) (F : Finset (L2T L)) (B : HN L m →L[ℂ] HN L m) :
    ‖approxKernel m F B‖ ≤ ‖B‖ := by
  unfold approxKernel
  have h1 : ‖(powSpan (L := L) m F).starProjection‖ ≤ 1 := Submodule.starProjection_norm_le _
  calc _ ≤ ‖(powSpan (L := L) m F).starProjection‖ * (‖B‖ * ‖(powSpan (L := L) m F).starProjection‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖B‖ * 1) := by gcongr
    _ = ‖B‖ := by ring

lemma approxKernel_mem (m : ℕ) (F : Finset (L2T L)) (B : HN L m →L[ℂ] HN L m) :
    approxKernel m F B ∈ powerKernels (L := L) m := by
  set V := powSpan (L := L) m F with hV
  let b := stdOrthonormalBasis ℂ V
  have hP : V.starProjection = ∑ i, InnerProductSpace.rankOne ℂ (b i : HN L m) (b i : HN L m) :=
    b.starProjection_eq_sum_rankOne
  have hb : ∀ i, (b i : HN L m) ∈ Submodule.span ℂ (Set.range (power (L := L) m)) :=
    fun i => powSpan_le m F (b i).2
  have hPx : ∀ x : HN L m, V.starProjection x = ∑ j, ⟪(b j : HN L m), x⟫_ℂ • (b j : HN L m) := by
    intro x
    rw [hP]
    simp only [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply]
  have : approxKernel m F B = ∑ i, InnerProductSpace.rankOne ℂ (V.starProjection (B (b i : HN L m))) (b i : HN L m) := by
    ext x : 1
    unfold approxKernel
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply]
    rw [hPx x, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, map_smul]
  rw [this]
  refine Submodule.sum_mem _ (fun i _ => rankOne_mem_powerKernels m ?_ (hb i))
  exact powSpan_le m F (Submodule.starProjection_apply_mem V _)


lemma span_powers_dense (m : ℕ) :
    (Submodule.span ℂ (Set.range (power (L := L) m))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_orthogonal'] at hx
  apply powers_total m x
  intro g
  exact inner_eq_zero_symm.mp (hx _ (Submodule.subset_span ⟨g, rfl⟩))

lemma tendsto_starProjection_powSpan (m : ℕ) (x : HN L m) :
    Tendsto (fun F : Finset (L2T L) => (powSpan (L := L) m F).starProjection x) atTop (𝓝 x) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hdense : Dense (Submodule.span ℂ (Set.range (power (L := L) m)) : Set (HN L m)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]; exact span_powers_dense m
  obtain ⟨z, hzmem, hz⟩ := hdense.exists_dist_lt x hε
  rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp] at hzmem
  obtain ⟨c, rfl⟩ := hzmem
  refine ⟨c.support, fun F hF => ?_⟩
  have hzF : (c.sum fun i a => a • power (L := L) m i) ∈ powSpan (L := L) m F := by
    unfold Finsupp.sum
    refine Submodule.sum_mem _ (fun g hg => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨g, by exact_mod_cast hF hg, rfl⟩
  have hmin := Submodule.starProjection_minimal (U := powSpan (L := L) m F) x
  have hle : ‖x - (powSpan (L := L) m F).starProjection x‖ ≤ ‖x - (c.sum fun i a => a • power (L := L) m i)‖ := by
    rw [hmin]
    have hbdd : BddBelow (Set.range fun w : powSpan (L := L) m F => ‖x - (w : HN L m)‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hbdd ⟨_, hzF⟩
  rw [dist_eq_norm, norm_sub_rev]
  rw [dist_eq_norm] at hz
  exact hle.trans_lt hz

lemma tendsto_approxKernel (m : ℕ) (B : HN L m →L[ℂ] HN L m) (x : HN L m) :
    Tendsto (fun F : Finset (L2T L) => approxKernel m F B x) atTop (𝓝 (B x)) := by
  have h1 : Tendsto (fun F : Finset (L2T L) => B ((powSpan (L := L) m F).starProjection x)) atTop (𝓝 (B x)) :=
    (B.continuous.tendsto x).comp (tendsto_starProjection_powSpan m x)
  have h2 : Tendsto (fun F : Finset (L2T L) => (powSpan (L := L) m F).starProjection (B x)) atTop (𝓝 (B x)) :=
    tendsto_starProjection_powSpan m (B x)
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1 h2 ⊢
  refine squeeze_zero (fun F => norm_nonneg _) (fun F => ?_) (by simpa using h1.add h2)
  have hP : ‖(powSpan (L := L) m F).starProjection‖ ≤ 1 := Submodule.starProjection_norm_le _
  set P := (powSpan (L := L) m F).starProjection with hPdef
  set w := B (P x) with hw
  have : approxKernel m F B x - B x = P (w - B x) + (P (B x) - B x) := by
    change P (B (P x)) - B x = _
    rw [map_sub]; abel
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  calc ‖P (w - B x)‖ ≤ ‖P‖ * ‖w - B x‖ := P.le_opNorm _
    _ ≤ 1 * ‖w - B x‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ = ‖w - B x‖ := one_mul _

/-- **Strong approximation.** Every bounded kernel of order `m` is the strong limit of a bounded net of
finite combinations of rank-one power kernels. -/
theorem exists_strong_approx (m : ℕ) (B : HN L m →L[ℂ] HN L m) :
    (∀ F : Finset (L2T L), approxKernel m F B ∈ powerKernels (L := L) m) ∧
    (∀ F : Finset (L2T L), ‖approxKernel m F B‖ ≤ ‖B‖) ∧
    ∀ x, Tendsto (fun F : Finset (L2T L) => approxKernel m F B x) atTop (𝓝 (B x)) :=
  ⟨fun F => approxKernel_mem m F B, fun F => norm_approxKernel_le m F B, tendsto_approxKernel m B⟩


/-! ### The cell vectors and the per-order identity -/

/-- The source coefficient `N^{1-(a+b)/2} C(m,a) C(m,b)`. -/
def cellCoeff (N m a b : ℕ) : ℝ :=
  (N : ℝ) / (Real.sqrt (N : ℝ)) ^ (a + b) * (m.choose a : ℝ) * (m.choose b : ℝ)

/-- The `(a,b)` Wick cell of the `m`-th interaction order, `N^{1-(a+b)/2} C(m,a) C(m,b) 𝒲_{a,b}(C_{m,a,b}(u)) y`. -/
def cellVec (N m a b : ℕ) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) (y : Fock L) : Fock L :=
  if hab : a ≤ m ∧ b ≤ m then
    ((cellCoeff N m a b : ℝ) : ℂ) • wickFock a b (ck m a b hab.1 hab.2 Bm u) y
  else 0

/-- The sum of all `(a,b)` cells of the `m`-th order. -/
def cellSum (N m : ℕ) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) (y : Fock L) : Fock L :=
  ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1), cellVec N m a b Bm u y

/-- The `m`-th interaction order applied to a vector: `N^{1-m} 𝒲_{m,m}(B_m) z`. -/
def orderVec (N m : ℕ) (Bm : HN L m →L[ℂ] HN L m) (z : Fock L) : Fock L :=
  (((N : ℝ) / (N : ℝ) ^ m : ℝ) : ℂ) • wickFock m m Bm z

lemma ck_add (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) (B B' : HN L m →L[ℂ] HN L m) (u : L2T L) :
    ck m a b ha hb (B + B') u = ck m a b ha hb B u + ck m a b ha hb B' u := by
  ext x : 1; simp [ck]

lemma ck_smul (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) (c : ℂ) (B : HN L m →L[ℂ] HN L m) (u : L2T L) :
    ck m a b ha hb (c • B) u = c • ck m a b ha hb B u := by
  ext x : 1; simp [ck]

lemma coef_identity (N m a b : ℕ) (hN : 0 < N) (ha : a ≤ m) (hb : b ≤ m) :
    (N : ℝ) / (N : ℝ) ^ m * (Real.sqrt (N : ℝ)) ^ ((m - a) + (m - b)) =
      (N : ℝ) / (Real.sqrt (N : ℝ)) ^ (a + b) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have h2 : (Real.sqrt (N : ℝ)) ^ ((m - a) + (m - b)) * (Real.sqrt (N : ℝ)) ^ (a + b) = (N : ℝ) ^ m := by
    rw [← pow_add]
    have : (m - a) + (m - b) + (a + b) = 2 * m := by omega
    rw [this, pow_mul, Real.sq_sqrt hNr.le]
  field_simp
  rw [← h2]


lemma pend_pow_shift (x : Module.End ℂ (physSmooth L)) (c : ℂ) (m : ℕ) :
    (x + c • (1 : Module.End ℂ (physSmooth L))) ^ m =
      ∑ a ∈ Finset.range (m+1), ((m.choose a : ℂ) * c ^ (m - a)) • x ^ a := by
  have hc : Commute x (c • (1 : Module.End ℂ (physSmooth L))) := (Commute.one_right x).smul_right c
  rw [hc.add_pow]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h1 : (c • (1 : Module.End ℂ (physSmooth L))) ^ (m - a) = (c ^ (m - a)) • (1 : Module.End ℂ (physSmooth L)) := by
    rw [smul_pow, one_pow]
  have h2 : ((m.choose a : ℕ) : Module.End ℂ (physSmooth L)) = ((m.choose a : ℂ)) • (1 : Module.End ℂ (physSmooth L)) := by
    rw [Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul, mul_one]
  rw [h1, h2, mul_smul_comm, mul_one, mul_smul_comm, mul_one, smul_smul, mul_comm]

lemma weylConj_rk (v g f : L2T L) (m : ℕ) :
    weylConj v ((creP g) ^ m * (annP f) ^ m) =
      ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1),
        (((m.choose a : ℂ) * (m.choose b : ℂ)) * (⟪v, g⟫_ℂ ^ (m - a) * ⟪f, v⟫_ℂ ^ (m - b))) •
          ((creP g) ^ a * (annP f) ^ b) := by
  rw [map_mul, map_pow, map_pow, (weyl_affine_action v f).2.2.1, (weyl_affine_action v g).2.2.2,
    pend_pow_shift, pend_pow_shift, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [smul_mul_smul_comm]
  congr 1
  ring


/-- **The per-order translation identity for a rank-one power kernel.** -/
theorem perOrder_rk (N m : ℕ) (hN : 0 < N) (g f u : L2T L) (y : physSmooth L) :
    (Prop022OVacuum.printedWeyl (((Real.sqrt (N : ℝ) : ℝ) : ℂ) • u)).symm
      (orderVec N m (rk m m g f)
        (Prop022OVacuum.printedWeyl (((Real.sqrt (N : ℝ) : ℝ) : ℂ) • u) y.1)) =
      cellSum N m (rk m m g f) u y.1 := by
  set v : L2T L := ((Real.sqrt (N : ℝ) : ℝ) : ℂ) • u with hv
  have hz : Prop022OVacuum.printedWeyl v y.1 = (printedWeylD v y).1 := (printedWeylD_coe v y).symm
  rw [hz]
  unfold orderVec
  rw [wickFock_rk m m g f (printedWeylD v y), printedWeyl_symm, map_smul]
  have h1 : Prop022OVacuum.printedWeyl (-v) ((((creP g) ^ m * (annP f) ^ m) (printedWeylD v y)).1) =
      (weylConj v ((creP g) ^ m * (annP f) ^ m) y).1 := by
    rw [weylConj_apply, printedWeylD_coe]
  rw [h1, weylConj_rk]
  unfold cellSum
  have hsum : ((∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1),
        (((m.choose a : ℂ) * (m.choose b : ℂ)) * (⟪v, g⟫_ℂ ^ (m - a) * ⟪f, v⟫_ℂ ^ (m - b))) •
          ((creP g) ^ a * (annP f) ^ b)) y).1 =
      ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1),
        (((m.choose a : ℂ) * (m.choose b : ℂ)) * (⟪v, g⟫_ℂ ^ (m - a) * ⟪f, v⟫_ℂ ^ (m - b))) •
          (((creP g) ^ a * (annP f) ^ b) y).1 := by
    simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul]
  rw [hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have ha' : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hb' : b ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have hy : MomentFinite y.1 := momentFinite_of_mem y
  unfold cellVec
  rw [dif_pos ⟨ha', hb'⟩, ck_rk, wickFock_smul _ _ _ _ hy, ← wickFock_rk a b g f y]
  rw [smul_smul, smul_smul]
  congr 1
  have hcoef := coef_identity N m a b hN ha' hb'
  have hcoefC := congrArg (fun r : ℝ => (r : ℂ)) hcoef
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow] at hcoefC
  have e1 : ⟪v, g⟫_ℂ = ((Real.sqrt (N : ℝ) : ℝ) : ℂ) * ⟪u, g⟫_ℂ := by
    rw [hv, inner_smul_left, Complex.conj_ofReal]
  have e2 : ⟪f, v⟫_ℂ = ((Real.sqrt (N : ℝ) : ℝ) : ℂ) * ⟪f, u⟫_ℂ := by
    rw [hv, inner_smul_right]
  rw [e1, e2, cellCoeff]
  push_cast
  have hpow : (((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ ((m - a) + (m - b)) =
      (((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ (m - a) * (((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ (m - b) := pow_add _ _ _
  rw [hpow] at hcoefC
  linear_combination ((m.choose a : ℂ) * (m.choose b : ℂ) * ⟪u, g⟫_ℂ ^ (m - a) * ⟪f, u⟫_ℂ ^ (m - b)) * hcoefC


/-! ### The per-order identity for an arbitrary kernel -/

section general

variable (N m : ℕ) (u : L2T L) (y : physSmooth L)

/-- The pulled-back `m`-th order of the interaction. -/
def lhsOrder (Bm : HN L m →L[ℂ] HN L m) : Fock L :=
  (Prop022OVacuum.printedWeyl (((Real.sqrt (N : ℝ) : ℝ) : ℂ) • u)).symm
    (orderVec N m Bm (Prop022OVacuum.printedWeyl (((Real.sqrt (N : ℝ) : ℝ) : ℂ) • u) y.1))

lemma momentFinite_weyl (v : L2T L) : MomentFinite (Prop022OVacuum.printedWeyl v y.1) := by
  have : Prop022OVacuum.printedWeyl v y.1 ∈ physSmooth L := (weyl_mem_physSmooth_iff v y.1).mpr y.2
  exact momentFinite_of_mem ⟨_, this⟩

lemma lhsOrder_add (B B' : HN L m →L[ℂ] HN L m) :
    lhsOrder N m u y (B + B') = lhsOrder N m u y B + lhsOrder N m u y B' := by
  unfold lhsOrder orderVec
  rw [wickFock_add m m B B' (momentFinite_weyl y _), smul_add, map_add]

lemma lhsOrder_smul (c : ℂ) (B : HN L m →L[ℂ] HN L m) :
    lhsOrder N m u y (c • B) = c • lhsOrder N m u y B := by
  unfold lhsOrder orderVec
  rw [wickFock_smul m m c B (momentFinite_weyl y _), smul_comm, map_smul]

lemma cellVec_add (a b : ℕ) (B B' : HN L m →L[ℂ] HN L m) :
    cellVec N m a b (B + B') u y.1 = cellVec N m a b B u y.1 + cellVec N m a b B' u y.1 := by
  unfold cellVec
  split_ifs with h
  · rw [ck_add, wickFock_add _ _ _ _ (momentFinite_of_mem y), smul_add]
  · simp

lemma cellVec_smul (a b : ℕ) (c : ℂ) (B : HN L m →L[ℂ] HN L m) :
    cellVec N m a b (c • B) u y.1 = c • cellVec N m a b B u y.1 := by
  unfold cellVec
  split_ifs with h
  · rw [ck_smul, wickFock_smul _ _ _ _ (momentFinite_of_mem y), smul_comm]
  · simp

lemma cellSum_add (B B' : HN L m →L[ℂ] HN L m) :
    cellSum N m (B + B') u y.1 = cellSum N m B u y.1 + cellSum N m B' u y.1 := by
  unfold cellSum
  simp only [cellVec_add, Finset.sum_add_distrib]

lemma cellSum_smul (c : ℂ) (B : HN L m →L[ℂ] HN L m) :
    cellSum N m (c • B) u y.1 = c • cellSum N m B u y.1 := by
  unfold cellSum
  simp only [cellVec_smul, Finset.smul_sum]

end general


lemma norm_ck_le (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) :
    ‖ck m a b ha hb Bm u‖ ≤ ‖insertSector m a ha u‖ * ‖Bm‖ * ‖insertSector m b hb u‖ := by
  unfold ck
  calc _ ≤ ‖(insertSector m a ha u).adjoint‖ * (‖Bm‖ * ‖insertSector m b hb u‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

open Classical in
/-- **The per-order translation identity.**  For every bounded kernel `B_m` of order `m`, every smooth
vector `y` and every `N ≥ 1`, with `W(√N u) = physicalWeyl N u`,
`W(√N u)⁻¹ ( N^{1-m} 𝒲_{m,m}(B_m) ) W(√N u) y = ∑_{a,b ≤ m} N^{1-(a+b)/2} C(m,a) C(m,b)
𝒲_{a,b}(C_{m,a,b}(u)) y`, with the printed contraction kernels `C_{m,a,b}(u) = contractedKernel m a b`. -/
theorem perOrder (N m : ℕ) (hN : 0 < N) (u : L2T L) (y : physSmooth L) (Bm : HN L m →L[ℂ] HN L m) :
    lhsOrder N m u y Bm = cellSum N m Bm u y.1 := by
  -- the identity holds on the span of the rank-one power kernels
  have hspan : ∀ B ∈ powerKernels (L := L) m, lhsOrder N m u y B = cellSum N m B u y.1 := by
    intro B hB
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨⟨g, f⟩, rfl⟩ := hB
      exact perOrder_rk N m hN g f u y
    | zero =>
      have h1 := lhsOrder_add N m u y (0 : HN L m →L[ℂ] HN L m) 0
      have h2 := cellSum_add N m u y (0 : HN L m →L[ℂ] HN L m) 0
      rw [add_zero] at h1 h2
      rw [add_eq_left.mp h1.symm, add_eq_left.mp h2.symm]
    | add B B' _ _ h h' =>
      rw [lhsOrder_add, cellSum_add, h, h']
    | smul c B _ h =>
      rw [lhsOrder_smul, cellSum_smul, h]
  obtain ⟨hmem, hnorm, hconv⟩ := exists_strong_approx m Bm
  have hy : MomentFinite y.1 := momentFinite_of_mem y
  -- left side converges
  have hL : Tendsto (fun F : Finset (L2T L) => lhsOrder N m u y (approxKernel m F Bm)) atTop
      (𝓝 (lhsOrder N m u y Bm)) := by
    unfold lhsOrder orderVec
    have h1 := tendsto_wickFock m m (fun F : Finset (L2T L) => approxKernel m F Bm) Bm ‖Bm‖ hnorm le_rfl
      hconv (momentFinite_weyl y (((Real.sqrt (N : ℝ) : ℝ) : ℂ) • u))
    have h2 := h1.const_smul (((((N : ℝ) / (N : ℝ) ^ m : ℝ)) : ℂ))
    exact ((LinearIsometryEquiv.continuous _).tendsto _).comp h2
  -- right side converges
  have hR : Tendsto (fun F : Finset (L2T L) => cellSum N m (approxKernel m F Bm) u y.1) atTop
      (𝓝 (cellSum N m Bm u y.1)) := by
    unfold cellSum
    refine tendsto_finset_sum _ (fun a ha => tendsto_finset_sum _ (fun b hb => ?_))
    unfold cellVec
    split_ifs with hab
    · have hK : ∀ F : Finset (L2T L), ‖ck m a b hab.1 hab.2 (approxKernel m F Bm) u‖ ≤
          ‖insertSector m a hab.1 u‖ * ‖Bm‖ * ‖insertSector m b hab.2 u‖ := fun F =>
        (norm_ck_le m a b hab.1 hab.2 _ u).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hnorm F) (norm_nonneg (insertSector m a hab.1 u))) (norm_nonneg (insertSector m b hab.2 u)))
      have hK0 := norm_ck_le m a b hab.1 hab.2 Bm u
      have hconv' : ∀ x, Tendsto (fun F : Finset (L2T L) => ck m a b hab.1 hab.2 (approxKernel m F Bm) u x)
          atTop (𝓝 (ck m a b hab.1 hab.2 Bm u x)) := by
        intro x
        change Tendsto (fun F : Finset (L2T L) =>
            (insertSector m a hab.1 u).adjoint (approxKernel m F Bm (insertSector m b hab.2 u x))) atTop
          (𝓝 ((insertSector m a hab.1 u).adjoint (Bm (insertSector m b hab.2 u x))))
        exact ((insertSector m a hab.1 u).adjoint.continuous.tendsto _).comp (hconv _)
      have h1 := tendsto_wickFock a b (fun F : Finset (L2T L) => ck m a b hab.1 hab.2 (approxKernel m F Bm) u)
        (ck m a b hab.1 hab.2 Bm u) _ hK
        (hK0.trans (by
          refine le_of_eq rfl))
        hconv' hy
      exact h1.const_smul _
    · exact tendsto_const_nhds
  have hEq : ∀ F : Finset (L2T L), lhsOrder N m u y (approxKernel m F Bm) =
      cellSum N m (approxKernel m F Bm) u y.1 := fun F => hspan _ (hmem F)
  have hL' : Tendsto (fun F : Finset (L2T L) => cellSum N m (approxKernel m F Bm) u y.1) atTop
      (𝓝 (lhsOrder N m u y Bm)) := by
    refine hL.congr (fun F => hEq F)
  exact tendsto_nhds_unique hL' hR

end QuantumNLS.Prop024WOrder

#print axioms QuantumNLS.Prop024WOrder.fock_tendsto
#print axioms QuantumNLS.Prop024WOrder.wickFock_sector
#print axioms QuantumNLS.Prop024WOrder.wickFock_summable
#print axioms QuantumNLS.Prop024WOrder.tendsto_wickFock
#print axioms QuantumNLS.Prop024WOrder.exists_strong_approx
#print axioms QuantumNLS.Prop024WOrder.ck_rk
#print axioms QuantumNLS.Prop024WOrder.perOrder_rk
#print axioms QuantumNLS.Prop024WOrder.perOrder

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WOrder." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WOrder." then
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
  Lean.logInfo m!"Prop024WOrder aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
