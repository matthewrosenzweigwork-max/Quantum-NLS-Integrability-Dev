import QuantumNLS.FullCharacterProjection
import QuantumNLS.Ext025HGP15
import QuantumNLS.Ext025GP16R27m
import Mathlib
import QuantumNLS.ActualModelTargetR53a
import QuantumNLS.Ext025A2Phase
import QuantumNLS.Ext025HGP01
import QuantumNLS.Local014StateLimits
import QuantumNLS.BethePhysicalTransfer

/-! The two vector-strong residual estimates for DEF-054. -/
set_option autoImplicit false
set_option linter.unusedTactic false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.DynSeedHaarR47b
open CountRotations FullCharacterProjection BetheCoefficientTransform

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

theorem character_conj (a b : ℤ) (θ : AngleTorus) :
    conj (character a b θ) = character b a θ := by
  rw [character, character, ← Circle.coe_inv_eq_conj, inv_div]

theorem adjoint_component (B : BetheBasis L N) (T : HN L N →L[ℂ] HN L N) (a b : ℤ) :
    (component B T a b).adjoint = component B T.adjoint b a := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, component_apply, component_apply]
  change (innerSL ℂ x) (∫ θ, integrand B T a b y θ ∂productHaar) =
    ⟪∫ θ, integrand B T.adjoint b a x θ ∂productHaar, y⟫_ℂ
  rw [← (innerSL ℂ x).integral_comp_comm (integrand_integrable B T a b y)]
  rw [← inner_conj_symm (∫ θ, integrand B T.adjoint b a x θ ∂productHaar) y,
    ← integral_inner (integrand_integrable B T.adjoint b a x) y, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with θ
  change ⟪x, integrand B T a b y θ⟫_ℂ = conj ⟪y, integrand B T.adjoint b a x θ⟫_ℂ
  rw [inner_conj_symm]
  rw [integrand, integrand, inner_smul_right, inner_smul_left, character_conj]
  let V := quantumRotation B θ
  change character a b θ * ⟪x, V.symm (T (V y))⟫_ℂ =
    character a b θ * ⟪V.symm (T.adjoint (V x)), y⟫_ℂ
  congr 1
  calc
    ⟪x, V.symm (T (V y))⟫_ℂ = ⟪V x, T (V y)⟫_ℂ := by
      rw [← V.inner_map_map, V.apply_symm_apply]
    _ = ⟪T.adjoint (V x), V y⟫_ℂ := (T.adjoint_inner_left _ _).symm
    _ = ⟪V.symm (T.adjoint (V x)), y⟫_ℂ := by
      rw [← V.inner_map_map (V.symm _) y, V.apply_symm_apply]

theorem residual_le (B : BetheBasis L N) (T : HN L N →L[ℂ] HN L N) (a b : ℤ)
    (x : HN L N) (z : ℂ) (e : ℝ)
    (h : ∀ θ, ‖T (quantumRotation B θ x) -
      (character b a θ * z) • quantumRotation B θ x‖ ≤ e) :
    ‖component B T a b x - z • x‖ ≤ e := by
  let g : AngleTorus → HN L N := fun θ => integrand B T a b x θ - z • x
  have hg : Continuous g := (integrand_continuous B T a b x).sub continuous_const
  have hgp := (Ext025GP16R27m.contract_GP16_fixed.{0,0,0,0,0,0,0,0,0,0}.2.1
    (F := HN L N) productHaar g hg)
  have he : ∀ θ, ‖g θ‖ ≤ e := by
    intro θ
    let V := quantumRotation B θ
    have hc : character a b θ * (character b a θ * z) = z := by
      simp only [character, ← Circle.coe_mul, ← mul_assoc]
      simp
    have heq : g θ = character a b θ • V.symm
        (T (V x) - (character b a θ * z) • V x) := by
      simp only [g, integrand, V, map_sub, map_smul, LinearIsometryEquiv.symm_apply_apply,
        smul_sub, smul_smul, hc]
    rw [heq, norm_smul, V.symm.norm_map, show ‖character a b θ‖ = 1 by simp [character], one_mul]
    exact h θ
  have hi : (∫ θ, g θ ∂productHaar) = component B T a b x - z • x := by
    rw [show g = fun θ => integrand B T a b x θ - z • x from rfl,
      integral_sub (integrand_integrable B T a b x) (integrable_const _), integral_const]
    simp [← component_apply, integrand]
  calc
    ‖component B T a b x - z • x‖ = ‖∫ θ, g θ ∂productHaar‖ := by rw [hi]
    _ ≤ ∫ θ, ‖g θ‖ ∂productHaar := hgp.2.1
    _ ≤ e := by
      simpa using integral_mono hgp.1.norm (integrable_const e) he

theorem adjoint_residual_le (B : BetheBasis L N) (T : HN L N →L[ℂ] HN L N) (a b : ℤ)
    (x : HN L N) (z : ℂ) (e : ℝ)
    (h : ∀ θ, ‖T.adjoint (quantumRotation B θ x) -
      conj (character b a θ * z) • quantumRotation B θ x‖ ≤ e) :
    ‖(component B T a b).adjoint x - conj z • x‖ ≤ e := by
  rw [adjoint_component]
  apply residual_le
  intro θ
  simpa only [map_mul, character_conj] using h θ

end QuantumNLS.DynSeedHaarR47b
#print axioms QuantumNLS.DynSeedHaarR47b.character_conj
#print axioms QuantumNLS.DynSeedHaarR47b.adjoint_component
#print axioms QuantumNLS.DynSeedHaarR47b.residual_le
#print axioms QuantumNLS.DynSeedHaarR47b.adjoint_residual_le


/-! Diagonal selection over fixed, positive tolerances. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
namespace QuantumNLS.DynSeedDiagonalR47b

/-- Assemble choices from all sufficiently large sectors for each fixed
tolerance. Every sector has its own bounded-operator carrier in the application. -/
theorem diagonal {A : ℕ → Type*} (P : ∀ n, A n → Prop)
    (err : ∀ n, A n → ℝ≥0∞)
    (fallback : ∀ n, A n) (hfallback : ∀ n, P n (fallback n))
    (happrox : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∃ a, P n a ∧ err n a ≤ ENNReal.ofReal ε) :
    ∃ a : ∀ n, A n, (∀ n, P n (a n)) ∧
      Tendsto (fun n => err n (a n)) atTop (𝓝 0) := by
  classical
  let δ (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ j
  have hδpos (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδ : Tendsto δ atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  let good (n j : ℕ) := ∃ a, P n a ∧ err n a ≤ ENNReal.ofReal (δ j)
  let (n : ℕ) : DecidablePred (good n) := Classical.decPred _
  let j (n : ℕ) := Nat.findGreatest (good n) n
  let a (n : ℕ) : A n := if h : good n (j n) then h.choose else fallback n
  refine ⟨a, ?_, ENNReal.tendsto_nhds_zero.mpr ?_⟩
  · intro n
    by_cases h : good n (j n)
    · simpa only [a, dite_eq_left h] using h.choose_spec.1
    · simpa only [a, dite_eq_right h] using hfallback n
  intro ε hε
  have hδ' : Tendsto (fun j => ENNReal.ofReal (δ j)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hδ
  obtain ⟨i, hi, hiε⟩ := (((ENNReal.tendsto_nhds_zero.mp hδ') ε hε).and
    (eventually_ge_atTop (1 : ℕ))).exists
  filter_upwards [happrox (δ i) (hδpos i), eventually_ge_atTop i] with n hn hni
  have hij : i ≤ j n :=
    le_of_not_gt fun hlt => Nat.findGreatest_is_greatest hlt hni hn
  have hj : good n (j n) :=
    Nat.findGreatest_of_ne_zero rfl (by omega)
  have he : err n (a n) ≤ ENNReal.ofReal (δ (j n)) := by
    simpa only [a, dite_eq_left hj] using hj.choose_spec.2
  have hp : δ (j n) ≤ δ i :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
  exact he.trans ((ENNReal.ofReal_le_ofReal hp).trans hi)

end QuantumNLS.DynSeedDiagonalR47b
#print axioms QuantumNLS.DynSeedDiagonalR47b.diagonal


/-! Exact predecessor interface for the fixed profile and finite family of charge orders.
The implication retains the mixed finite-angle antecedent, every fixed rank, and
every compact time box. The full-angle conclusion uses the original Bethe basis. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
namespace QuantumNLS.DynSeedInputR47b
open PhysicalTensor TensorCarrier CountRotations Def033HierarchyR24m ActualModelTargetR53a
open ActualModelQuantumR52a Def044D1SpectralR51a BetheCoefficientTransform

variable {L κ : ℝ} [Fact (0 < L)]

/-- A finite joint-time box, extended by zero in inactive coordinates. -/
def TimeBox (R : Finset ℕ) (lo hi : ℕ → ℝ) :=
  {t : ℕ → ℝ // ∀ r : ℕ, t r ∈ if r ∈ R then Set.Icc (lo r) (hi r) else {0}}

def classicalOrbit (_hκ : 0 < κ) (F : HigherFlows L κ)
    (u : Smooth L) (R : Finset ℕ) (t : ℕ → ℝ) : L2T L :=
  physical (jointSmooth (hamFlows F R) t u)

def physicalAngle (hκ : 0 < κ) (θ : AngleTorus) (v : L2T L) : L2T L :=
  let C := Def021ChartR41b.chart L κ hκ
  C.Ψ (coordinateRotation θ (C.Φ v))

def quantumOrbit (hκ : 0 < κ) (u : Smooth L)
    (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ) : HN L (n + 1) :=
  chargeUnitary hκ R t n (HighMomentsOps.wvec (n + 1) (physical u))

def marginalError (n k : ℕ) (hk : k ≤ n + 1) (ψ : HN L (n + 1)) (v : L2T L) :
    ℝ≥0∞ :=
  TraceClass.traceNorm (reducedDensityN (n + 1) k hk ψ.val - Prop025OInputs.tensorProj k v)

/-- The uniform finite-angle estimate (dynft-mixed-finite). -/
def MixedFinite (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L) (R : Finset ℕ) : Prop :=
  ∀ (I : Finset ℤ) (k : ℕ) (lo hi : ℕ → ℝ),
    Tendsto (fun n : ℕ => if hk : k ≤ n + 1 then
      ⨆ t : TimeBox R lo hi,
      ⨆ θ : {θ : AngleTorus // ∀ i ∉ I, θ i = 1},
        marginalError n k hk
          (chargeUnitary hκ R t.val n
            (quantumRotation (basis hκ n) θ.val (HighMomentsOps.wvec (n + 1) (physical u))))
          (physicalAngle hκ θ.val (classicalOrbit hκ F u R t.val))
      else 0) atTop (𝓝 0)

/-- The uniform full-product-torus estimate (dynft-full-torus). -/
def FullTorus (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L) (R : Finset ℕ) : Prop :=
  ∀ (k : ℕ) (lo hi : ℕ → ℝ),
    Tendsto (fun n : ℕ => if hk : k ≤ n + 1 then
      ⨆ t : TimeBox R lo hi, ⨆ θ : AngleTorus,
        marginalError n k hk
          (quantumRotation (basis hκ n) θ (quantumOrbit hκ u R t.val n))
          (physicalAngle hκ θ (classicalOrbit hκ F u R t.val))
      else 0) atTop (𝓝 0)

/-- R-B2E70586 in full: under (dynft-mixed-finite), for every fixed rank and
compact joint-time box, the supremum of the trace-norm errors over that box
and the full product torus tends to zero. -/
def DynftFullTorusInput (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L)
    (R : Finset ℕ) : Prop :=
  MixedFinite hκ F u R → FullTorus hκ F u R

end QuantumNLS.DynSeedInputR47b
#print QuantumNLS.DynSeedInputR47b.DynftFullTorusInput
#print axioms QuantumNLS.DynSeedInputR47b.DynftFullTorusInput


/-! Full-product character orthogonality gives the exact directed occupation shift. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.DynSeedGradingR47b
open CountRotations FullCharacterProjection BetheLabels BetheCoefficientTransform Occupation
open Ext025BHaar

local instance (α : Type*) : DecidableEq α := Classical.decEq α

def occupationChar (m : Occ) : AngleTorus →* Circle where
  toFun θ := m.prod fun j k => θ j ^ k
  map_one' := by simp [Finsupp.prod]
  map_mul' θ φ := by
    simp [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]

theorem occupationChar_add (m q : Occ) (θ : AngleTorus) :
    occupationChar (m + q) θ = occupationChar m θ * occupationChar q θ := by
  apply Finsupp.prod_add_index
  · simp
  · simp [pow_add]

theorem occupationChar_single (j : ℤ) (θ : AngleTorus) :
    occupationChar (e j) θ = θ j := by
  change (e j).prod (fun i k => θ i ^ k) = θ j
  simp [Finsupp.prod_single_index]

theorem occupationChar_test (m : Occ) (j : ℤ) (z : Circle) :
    occupationChar m (Pi.mulSingle j z) = z ^ (m j) := by
  change m.prod (fun i k => (Pi.mulSingle j z : AngleTorus) i ^ k) = _
  rw [Finsupp.prod_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.mulSingle_eq_of_ne hi]
  · simp

theorem occupationChar_injective : Function.Injective occupationChar := by
  intro p q hpq
  ext j
  by_contra hn
  let d : ℤ := (p j : ℤ) - (q j : ℤ)
  have hd : (d : ℝ) ≠ 0 := by
    have hdi : d ≠ 0 := by dsimp [d]; omega
    exact_mod_cast hdi
  let z := Circle.exp (Real.pi / (d : ℝ))
  have he := DFunLike.congr_fun hpq (Pi.mulSingle j z)
  rw [occupationChar_test, occupationChar_test] at he
  have hz : z ^ d = 1 := by
    rw [show d = (p j : ℤ) - (q j : ℤ) from rfl, zpow_sub, zpow_natCast,
      zpow_natCast, he, mul_inv_cancel]
  have hz' : z ^ d = Circle.exp Real.pi := by
    rw [show z = Circle.exp (Real.pi / (d : ℝ)) from rfl, ← Circle.exp_intCast_mul]
    congr 1
    field_simp
  exact Circle.exp_pi_ne_one (hz'.symm.trans hz)

theorem countPhase_inv {N : ℕ} (m : MArr N) (θ : AngleTorus) :
    (countPhase θ m)⁻¹ = occupationChar m.val θ := by
  simp [countPhase, occupationChar, Finsupp.prod, Finset.prod_inv_distrib, inv_pow]

theorem phase_integral_of_ne (p q : Occ) (hne : p ≠ q) :
    (∫ θ, (((occupationChar p / occupationChar q) θ : Circle) : ℂ) ∂productHaar) = 0 := by
  have hm : productHaar = productCircleHaar := rfl
  have hi : productHaar.IsMulLeftInvariant := hm ▸ inferInstanceAs productCircleHaar.IsMulLeftInvariant
  let χ := occupationChar p / occupationChar q
  have hc : χ ≠ 1 := by
    intro h
    exact hne (occupationChar_injective (div_eq_one.mp h))
  have hf : ∃ F : Finset ℤ, ∀ x y : AngleTorus, (∀ j ∈ F, x j = y j) → χ x = χ y := by
    refine ⟨p.support ∪ q.support, ?_⟩
    intro x y h
    have hp : occupationChar p x = occupationChar p y :=
      Finset.prod_congr rfl (fun j hj => by
        change x j ^ p j = y j ^ p j
        rw [h j (Finset.mem_union_left _ hj)])
    have hq : occupationChar q x = occupationChar q y :=
      Finset.prod_congr rfl (fun j hj => by
        change x j ^ q j = y j ^ q j
        rw [h j (Finset.mem_union_right _ hj)])
    change occupationChar p x / occupationChar q x = occupationChar p y / occupationChar q y
    rw [hp, hq]
  exact (Ext025HGP15.contract_GP15.2.2.2 productHaar inferInstance hi χ hf).2 hc

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The matrix entry vanishes unless the full array equation holds. -/
theorem coeff_eq_zero (B : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a b : ℤ) (m p : MArr N) (h : p.val + e a ≠ m.val + e b) :
    B.repr (component B T a b (B m)) p = 0 := by
  rw [B.repr_apply_apply, component_apply]
  change (innerSL ℂ (B p)) (∫ θ, integrand B T a b (B m) θ ∂productHaar) = 0
  rw [← (innerSL ℂ (B p)).integral_comp_comm (integrand_integrable B T a b (B m))]
  let f : AngleTorus → ℂ := fun θ =>
    (((occupationChar (p.val + e a) / occupationChar (m.val + e b)) θ : Circle) : ℂ)
  have he : (fun θ => ⟪B p, integrand B T a b (B m) θ⟫_ℂ) =
      fun θ => f θ * B.repr (T (B m)) p := by
    funext θ
    simp only [integrand, inner_smul_right, B.repr_apply_apply]
    let V := quantumRotation B θ
    have hV : ⟪B p, V.symm (T (V (B m)))⟫_ℂ = ⟪V (B p), T (V (B m))⟫_ℂ := by
      rw [← V.inner_map_map, V.apply_symm_apply]
    change character a b θ * ⟪B p, V.symm (T (V (B m)))⟫_ℂ = _
    rw [hV]
    simp only [V, quantumRotation_basis, map_smul, inner_smul_left, inner_smul_right]
    rw [← Circle.coe_inv_eq_conj, countPhase_inv]
    change _ = (((occupationChar (p.val + e a) θ / occupationChar (m.val + e b) θ : Circle) : ℂ)) * _
    rw [occupationChar_add, occupationChar_add, occupationChar_single, occupationChar_single,
      ← countPhase_inv, ← countPhase_inv]
    simp only [character, Circle.coe_div, Circle.coe_mul, Circle.coe_inv]
    field_simp
  change (∫ θ, ⟪B p, integrand B T a b (B m) θ⟫_ℂ ∂productHaar) = 0
  rw [he, integral_mul_const, phase_integral_of_ne _ _ h, zero_mul]

def transfer (a b : ℤ) (m : MArr N) (hm : DonorOK a m.val) : MArr N :=
  (marrArr N).symm (shiftArr a b (marrArr N m) hm)

def Graded (B : BetheBasis L N) (a b : ℤ) (C : HN L N →L[ℂ] HN L N) : Prop :=
  ∃ coeff : MArr N → ℂ, ∀ m : MArr N, C (B m) =
    if hm : DonorOK a m.val then coeff m • B (transfer a b m hm) else 0

theorem transfer_exterior (a b : ℤ) (m : MArr N) (hm : DonorOK a m.val)
    (i : ℤ) (hia : i ≠ a) (hib : i ≠ b) :
    (transfer a b m hm).val i = m.val i := by
  change shift a b m.val i = m.val i
  simp [shift_apply, hia, hib]

theorem zero_graded (B : BetheBasis L N) (a b : ℤ) : Graded B a b 0 := by
  refine ⟨fun _ => 0, fun m => ?_⟩
  split <;> simp

theorem component_graded (B : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a b : ℤ) (hab : a ≠ b) : Graded B a b (component B T a b) := by
  classical
  refine ⟨fun m => if hm : DonorOK a m.val then
    B.repr (component B T a b (B m)) (transfer a b m hm) else 0, ?_⟩
  intro m
  have hand (p : MArr N) (hp : p.val + e a = m.val + e b) :
      DonorOK a m.val := by
    have he := DFunLike.congr_fun hp a
    simp [hab] at he
    unfold DonorOK
    omega
  have hindex (p : MArr N) (hp : p.val + e a = m.val + e b) :
      p = transfer a b m (hand p hp) := by
    apply Subtype.ext
    ext j
    have he := DFunLike.congr_fun hp j
    change p.val j = shift a b m.val j
    rw [shift_apply]
    have he' : p.val j + (if j = a then 1 else 0) = m.val j + (if j = b then 1 else 0) := by
      simpa only [Finsupp.add_apply, Finsupp.single_apply, eq_comm (a := a),
        eq_comm (a := b)] using he
    have hd : 1 ≤ m.val a := hand p hp
    by_cases hja : j = a
    · subst j
      simp only [ite_true, hab, ite_false] at he' ⊢
      omega
    · by_cases hjb : j = b
      · subst j
        simpa [Finsupp.add_apply, Finsupp.single_apply, hab, Ne.symm hab] using he
      · simp only [hja, hjb, ite_false, Nat.sub_zero, Nat.add_zero] at he' ⊢
        exact he'
  by_cases hm : DonorOK a m.val
  · simp only [dite_eq_left hm]
    apply B.repr.injective
    apply lp.ext
    funext p
    rw [map_smul, lp.coeFn_smul, Pi.smul_apply, B.repr_self]
    by_cases h : p = transfer a b m hm
    · subst p
      simp
    · have hp : p.val + e a ≠ m.val + e b := fun eq => h (hindex p eq)
      rw [coeff_eq_zero B T a b m p hp]
      simp [h]
  · rw [dite_eq_right hm]
    apply B.repr.injective
    apply lp.ext
    funext p
    rw [map_zero]
    change B.repr (component B T a b (B m)) p = 0
    exact coeff_eq_zero B T a b m p (fun hp => hm (hand p hp))

end QuantumNLS.DynSeedGradingR47b
#print axioms QuantumNLS.DynSeedGradingR47b.component_graded
#print axioms QuantumNLS.DynSeedGradingR47b.transfer_exterior


/-! The compact common-phase quotient and its polynomial approximation.
The generating quadratics are the rank-one expectations
`⟪v, |w⟩⟨w| v⟫`. Constants, sums, products and conjugation suffice. -/
set_option autoImplicit false
noncomputable section
open Set Topology
namespace QuantumNLS.DynSeedApproxR47b
open Ext025A2
open scoped ComplexConjugate InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

inductive Coherent : (H → ℂ) → Prop
  | constant (c : ℂ) : Coherent (fun _ => c)
  | quadratic (w : H) : Coherent (fun v => ((‖⟪w, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ))
  | add {f g : H → ℂ} : Coherent f → Coherent g → Coherent (fun v => f v + g v)
  | mul {f g : H → ℂ} : Coherent f → Coherent g → Coherent (fun v => f v * g v)
  | conjugate {f : H → ℂ} : Coherent f → Coherent (fun v => conj (f v))

theorem dense_coherent (K : SubMulAction Circle H) (hK : IsCompact (K : Set H))
    (c : C(K, ℂ)) (hc : ∀ (g : Circle) (v : K), c (g • v) = c v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : H → ℂ, Coherent f ∧ ∀ v : K, ‖f v.val - c v‖ < ε := by
  let Q := Quotient (MulAction.orbitRel Circle K)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace Q := (gp01_phase_quotient_topology K hK).1
  let : T2Space Q := (gp01_phase_quotient_topology K hK).2
  let S := gp01_phase_algebra K
  let d := gp01_descend c hc
  have hd : Dense (S.toSubalgebra : Set C(Q, ℂ)) :=
    Ext025HGP01.contract_GP01 S.toSubalgebra (fun f hf => S.star_mem' (show f ∈ S from hf))
      (gp01_phase_algebra_separates K)
  obtain ⟨F, hF, hdist⟩ := Metric.mem_closure_iff.mp (hd d) ε hε
  have hdist' : ‖F - d‖ < ε := by
    simpa only [dist_comm d F, dist_eq_norm] using hdist
  have lift_poly (G : C(Q, ℂ)) (hG : G ∈ S) :
      ∃ f : H → ℂ, Coherent f ∧
        ∀ v : K, f v.val = G (Quotient.mk (MulAction.orbitRel Circle K) v) := by
    refine StarAlgebra.adjoin_induction (R := ℂ) (a := G) ?_ ?_ ?_ ?_ ?_ hG
    · rintro _ ⟨w, rfl⟩
      exact ⟨_, Coherent.quadratic w, fun _ => rfl⟩
    · intro r
      exact ⟨_, Coherent.constant r, fun _ => rfl⟩
    · rintro x y _ _ ⟨f, hf, hfx⟩ ⟨g, hg, hgy⟩
      exact ⟨_, hf.add hg, fun v => by simp [hfx v, hgy v]⟩
    · rintro x y _ _ ⟨f, hf, hfx⟩ ⟨g, hg, hgy⟩
      exact ⟨_, hf.mul hg, fun v => by simp [hfx v, hgy v]⟩
    · rintro x _ ⟨f, hf, hfx⟩
      exact ⟨_, hf.conjugate, fun v => by simp [hfx v]⟩
  obtain ⟨f, hf, hfv⟩ := lift_poly F hF
  refine ⟨f, hf, fun v => ?_⟩
  rw [hfv v, ← gp01_descend_mk c hc v]
  exact (ContinuousMap.norm_coe_le_norm (F - d) _).trans_lt hdist'

end QuantumNLS.DynSeedApproxR47b
#print axioms QuantumNLS.DynSeedApproxR47b.dense_coherent


/-! Strong symbol residuals are stable under the coherent polynomial operations.
This uses uniform operator bounds only for a fixed polynomial. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ComplexConjugate
namespace QuantumNLS.DynSeedPolynomialR47b
open DynSeedApproxR47b

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {n : ℕ}
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

def residual (A : E n →L[ℂ] E n) (s : ℂ) (x : E n) : ℝ :=
  ‖A x - s • x‖ + ‖A.adjoint x - conj s • x‖

def Represents (v : X → H) (x : (n : ℕ) → X → E n) (f : H → ℂ) : Prop :=
  ∃ A : (n : ℕ) → E n →L[ℂ] E n, ∃ B : ℝ, 0 ≤ B ∧ (∀ n, ‖A n‖ ≤ B) ∧
    (∀ p, ‖f (v p)‖ ≤ B) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ p, residual (A n) (f (v p)) (x n p) ≤ ε

theorem residual_add {n : ℕ} (A B : E n →L[ℂ] E n) (z w : ℂ) (x : E n) :
    residual (A + B) (z + w) x ≤ residual A z x + residual B w x := by
  unfold residual
  simp only [map_add, add_apply, add_smul]
  have rearrange (u v y z : E n) : (u + v) - (y + z) = (u - y) + (v - z) := by abel
  rw [rearrange, rearrange]
  linarith [norm_add_le (A x - z • x) (B x - w • x),
    norm_add_le (A.adjoint x - conj z • x) (B.adjoint x - conj w • x)]

omit [∀ n, CompleteSpace (E n)] in
theorem mul_error_le {n : ℕ} (A B : E n →L[ℂ] E n) (z w : ℂ) (x : E n) :
    ‖(A * B) x - (z * w) • x‖ ≤
      ‖A‖ * ‖B x - w • x‖ + ‖w‖ * ‖A x - z • x‖ := by
  have he : (A * B) x - (z * w) • x =
      A (B x - w • x) + w • (A x - z • x) := by
    simp only [mul_apply_eq_comp, map_sub, map_smul, smul_sub, smul_smul, mul_comm w z]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (A.le_opNorm _) (by rw [norm_smul]))

theorem residual_mul {n : ℕ} (A B : E n →L[ℂ] E n) (z w : ℂ) (x : E n)
    {M S : ℝ} (hA : ‖A‖ ≤ M) (hz : ‖z‖ ≤ M) (hB : ‖B‖ ≤ S) (hw : ‖w‖ ≤ S) :
    residual (A * B) (z * w) x ≤ S * residual A z x + M * residual B w x := by
  have h1 := mul_error_le A B z w x
  have h2 := mul_error_le B.adjoint A.adjoint (conj w) (conj z) x
  rw [ContinuousLinearMap.adjoint.norm_map, Complex.norm_conj] at h2
  have hm : (A * B).adjoint = B.adjoint * A.adjoint := by
    exact ContinuousLinearMap.adjoint_comp A B
  unfold residual
  rw [hm, map_mul, mul_comm (conj z)]
  have h3 := mul_le_mul_of_nonneg_right hA (norm_nonneg (B x - w • x))
  have h4 := mul_le_mul_of_nonneg_right hw (norm_nonneg (A x - z • x))
  have h5 := mul_le_mul_of_nonneg_right hB (norm_nonneg (A.adjoint x - conj z • x))
  have h6 := mul_le_mul_of_nonneg_right hz (norm_nonneg (B.adjoint x - conj w • x))
  linarith

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
theorem Represents.constant (v : X → H) (x : (n : ℕ) → X → E n) (c : ℂ) :
    Represents v x (fun _ => c) := by
  refine ⟨fun n => c • ContinuousLinearMap.id ℂ (E n), ‖c‖, norm_nonneg _, ?_, fun _ => le_rfl, ?_⟩
  · intro n
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg c) ContinuousLinearMap.norm_id_le
  · intro ε hε
    apply Eventually.of_forall
    intro n p
    have ha : (c • ContinuousLinearMap.id ℂ (E n)).adjoint =
        conj c • ContinuousLinearMap.id ℂ (E n) := by
      change star (c • ContinuousLinearMap.id ℂ (E n)) = _
      rw [star_smul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
      rfl
    simpa [residual, ha] using hε.le

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
theorem Represents.add {v : X → H} {x : (n : ℕ) → X → E n} {f g : H → ℂ}
    (hf : Represents v x f) (hg : Represents v x g) : Represents v x (fun u => f u + g u) := by
  obtain ⟨A, M, hM, hA, hF, hf⟩ := hf
  obtain ⟨B, S, hS, hB, hG, hg⟩ := hg
  refine ⟨fun n => A n + B n, M + S, add_nonneg hM hS, ?_, ?_, ?_⟩
  · intro n
    exact (norm_add_le _ _).trans (add_le_add (hA n) (hB n))
  · intro p
    exact (norm_add_le _ _).trans (add_le_add (hF p) (hG p))
  · intro ε hε
    filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity)] with n hfn hgn
    intro p
    exact (residual_add _ _ _ _ _).trans (by linarith [hfn p, hgn p])

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
theorem Represents.mul {v : X → H} {x : (n : ℕ) → X → E n} {f g : H → ℂ}
    (hf : Represents v x f) (hg : Represents v x g) : Represents v x (fun u => f u * g u) := by
  obtain ⟨A, M, hM, hA, hF, hf⟩ := hf
  obtain ⟨B, S, hS, hB, hG, hg⟩ := hg
  refine ⟨fun n => A n * B n, M * S, mul_nonneg hM hS, ?_, ?_, ?_⟩
  · intro n
    exact (norm_mul_le _ _).trans (mul_le_mul (hA n) (hB n) (norm_nonneg _) hM)
  · intro p
    rw [norm_mul]
    exact mul_le_mul (hF p) (hG p) (norm_nonneg _) hM
  · intro ε hε
    let δ := ε / (M + S + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    filter_upwards [hf δ hδ, hg δ hδ] with n hfn hgn
    intro p
    refine (residual_mul _ _ _ _ _ (hA n) (hF p) (hB n) (hG p)).trans ?_
    calc
      _ ≤ S * δ + M * δ := add_le_add (mul_le_mul_of_nonneg_left (hfn p) hS)
        (mul_le_mul_of_nonneg_left (hgn p) hM)
      _ = (M + S + 1) * δ - δ := by ring
      _ ≤ ε := by
        have he : (M + S + 1) * δ = ε := by
          dsimp [δ]
          field_simp
        linarith

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
theorem Represents.conj {v : X → H} {x : (n : ℕ) → X → E n} {f : H → ℂ}
    (hf : Represents v x f) : Represents v x (fun u => conj (f u)) := by
  obtain ⟨A, M, hM, hA, hF, hf⟩ := hf
  refine ⟨fun n => (A n).adjoint, M, hM, ?_, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.adjoint.norm_map] using hA
  · simpa only [Complex.norm_conj] using hF
  · intro ε hε
    filter_upwards [hf ε hε] with n hn
    intro p
    simpa [residual, add_comm] using hn p

theorem coherent_residual {v : X → H} {x : (n : ℕ) → X → E n} {f : H → ℂ}
    (hf : Coherent f) (hquad : ∀ w : H, Represents v x (fun u => ((‖inner ℂ w u‖ ^ 2 : ℝ) : ℂ))) :
    Represents v x f := by
  induction hf with
  | constant c => exact Represents.constant v x c
  | quadratic w => exact hquad w
  | add _ _ hf hg => exact hf.add hg
  | mul _ _ hf hg => exact hf.mul hg
  | conjugate _ hf => exact hf.conj

end QuantumNLS.DynSeedPolynomialR47b
#print axioms QuantumNLS.DynSeedPolynomialR47b.coherent_residual


/-! The fixed compact classical torus and its covariant mixed-coordinate symbol. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Set
open scoped ComplexConjugate
namespace QuantumNLS.DynSeedClassicalR47b
open CountRotations DynSeedInputR47b PhysicalTensor
open ResetNormalizationUniqueness (S2)
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

variable {L κ : ℝ} [Fact (0 < L)]

theorem chart_phase (hκ : 0 < κ) (c : Circle) (v : L2T L) :
    let C := Def021ChartR41b.chart L κ hκ
    C.Φ ((c : ℂ) • v) = (c : ℂ) • C.Φ v := by
  let C := Def021ChartR41b.chart L κ hκ
  let lc := Def021ChartR41b.localChart L
  let s : L2T L →L[ℝ] L2T L :=
    ((c : ℂ) • ContinuousLinearMap.id ℂ (L2T L)).restrictScalars ℝ
  have hρ : 0 < lc.d / Real.sqrt κ := div_pos lc.positive (Real.sqrt_pos.2 hκ)
  have hl : ∀ᶠ v in 𝓝 (0 : L2T L), s v ∈ Metric.ball (0 : L2T L) (lc.d / Real.sqrt κ) :=
    Filter.Eventually.mono
      (show ∀ᶠ v : L2T L in 𝓝 0, v ∈ Metric.ball (0 : L2T L) (lc.d / Real.sqrt κ) from
        Metric.ball_mem_nhds 0 hρ)
      (fun v hv => by simpa [s, Metric.mem_ball, dist_zero_right, norm_smul] using hv)
  have hnear : (fun v => C.Φ (s v)) =ᶠ[𝓝 (0 : L2T L)] (fun v => (c : ℂ) • C.Φ v) := by
    filter_upwards [Metric.ball_mem_nhds (0 : L2T L) hρ, hl] with v hv hsv
    rw [C.local_agreement _ hsv, C.local_agreement _ hv]
    obtain ⟨φ, hφ⟩ := Circle.exp_surjective c
    have hce : (c : ℂ) = Complex.exp ((φ : ℂ) * Complex.I) := by rw [← hφ, Circle.coe_exp]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcov, _⟩ := lc.spec.1 κ hκ
    apply lp.ext
    funext j
    change lc.Φ κ ((c : ℂ) • v) j = (c : ℂ) * lc.Φ κ v j
    rw [hce]
    exact (hcov v hv j).2.2.2.2.1 φ
  have ha : AnalyticOnNhd ℝ (fun v => C.Φ (s v)) univ :=
    fun v _ => (C.analytic (s v)).comp (s.analyticAt v)
  have hb : AnalyticOnNhd ℝ (fun v => (c : ℂ) • C.Φ v) univ :=
    fun v _ => (C.analytic v).const_smul (c := (c : ℂ))
  exact congrFun (ha.eq_of_eventuallyEq hb hnear) v

def symbol (hκ : 0 < κ) (a b : ℤ) (v : L2T L) : ℂ :=
  let C := Def021ChartR41b.chart L κ hκ
  C.Φ v a * conj (C.Φ v b)

theorem symbol_continuous (hκ : 0 < κ) (a b : ℤ) :
    Continuous (symbol (L := L) hκ a b) := by
  let C := Def021ChartR41b.chart L κ hκ
  have hc : Continuous C.Φ := continuous_iff_continuousAt.mpr
    (fun v => (C.analytic v).continuousAt)
  exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 a).continuous.comp hc).mul
    (Complex.continuous_conj.comp ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 b).continuous.comp hc))

theorem symbol_phase (hκ : 0 < κ) (a b : ℤ) (c : Circle) (v : L2T L) :
    symbol hκ a b ((c : ℂ) • v) = symbol hκ a b v := by
  unfold symbol
  dsimp only
  rw [chart_phase]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [mul_mul_mul_comm, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul]

theorem symbol_angle (hκ : 0 < κ) (a b : ℤ) (θ : AngleTorus) (v : L2T L) :
    symbol hκ a b (physicalAngle hκ θ v) =
      FullCharacterProjection.character b a θ * symbol hκ a b v := by
  unfold symbol physicalAngle
  dsimp only
  rw [(Def021ChartR41b.chart L κ hκ).right_inverse]
  simp [coordinateRotation, FullCharacterProjection.character, mul_assoc, mul_left_comm,
    ← Circle.coe_inv_eq_conj, div_eq_mul_inv]

/-- The inverse-chart image of the coordinatewise equal-modulus orbit. -/
def torus (hκ : 0 < κ) (u : L2T L) : SubMulAction Circle (L2T L) where
  carrier := {v | ∀ j : ℤ, ‖(Def021ChartR41b.chart L κ hκ).Φ v j‖ =
    ‖(Def021ChartR41b.chart L κ hκ).Φ u j‖}
  smul_mem' c v hv := by
    intro j
    change ‖(Def021ChartR41b.chart L κ hκ).Φ ((c : ℂ) • v) j‖ = _
    rw [chart_phase]
    simpa using hv j

theorem torus_compact (hκ : 0 < κ) (u : L2T L) :
    IsCompact (torus hκ u : Set (L2T L)) := by
  let C := Def021ChartR41b.chart L κ hκ
  let D : Set (S2 ℤ) := {z | ∀ j : ℤ, ‖z j‖ = ‖C.Φ u j‖}
  let a := RootIndexedMasses.masses hκ u
  have hD : D = ActionTorus.actionTorus a := by
    ext z
    change (∀ j, ‖z j‖ = ‖C.Φ u j‖) ↔ (∀ j, ‖z j‖ ^ 2 = a.val j)
    refine forall_congr' fun j => ?_
    rw [show a.val j = ‖C.Φ u j‖ ^ 2 from (C.actions u j).symm]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).symm
  have himg : (torus hκ u : Set (L2T L)) = C.Ψ '' D := by
    ext v
    constructor
    · intro hv
      exact ⟨C.Φ v, hv, C.left_inverse v⟩
    · rintro ⟨z, hz, rfl⟩
      change ∀ j, ‖C.Φ (C.Ψ z) j‖ = _
      rw [C.right_inverse]
      exact hz
  rw [himg, hD]
  exact (ActionTorus.isCompact_actionTorus a).image
    (continuous_iff_continuousAt.mpr fun z => (C.inverse_analytic z).continuousAt)

theorem angle_mem_torus (hκ : 0 < κ) (u v : L2T L) (hv : v ∈ torus hκ u) (θ : AngleTorus) :
    physicalAngle hκ θ v ∈ torus hκ u := by
  intro j
  change ‖(Def021ChartR41b.chart L κ hκ).Φ (physicalAngle hκ θ v) j‖ = _
  unfold physicalAngle
  dsimp only
  rw [(Def021ChartR41b.chart L κ hκ).right_inverse]
  simpa [coordinateRotation, norm_mul] using hv j

theorem torus_norm (hκ : 0 < κ) {u v : L2T L} (hv : v ∈ torus hκ u) : ‖v‖ = ‖u‖ := by
  let C := Def021ChartR41b.chart L κ hκ
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← C.norm v, ← C.norm u, ActionTorus.tsum_sq_eq, ActionTorus.tsum_sq_eq]
  exact tsum_congr fun j => congrArg (fun x : ℝ => x ^ 2) (hv j)

theorem approximants (hκ : 0 < κ) (u : L2T L) (a b : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : L2T L → ℂ, DynSeedApproxR47b.Coherent f ∧
      ∀ v ∈ torus hκ u, ‖f v - symbol hκ a b v‖ < ε := by
  let K := torus hκ u
  let c : C(K, ℂ) := ⟨fun v => symbol hκ a b v.val,
    (symbol_continuous hκ a b).comp continuous_subtype_val⟩
  obtain ⟨f, hf, he⟩ := DynSeedApproxR47b.dense_coherent K (torus_compact hκ u) c
    (fun g v => symbol_phase hκ a b g v.val) hε
  exact ⟨f, hf, fun v hv => he ⟨v, hv⟩⟩

end QuantumNLS.DynSeedClassicalR47b
#print axioms QuantumNLS.DynSeedClassicalR47b.chart_phase
#print axioms QuantumNLS.DynSeedClassicalR47b.approximants


/-! Rank-one quadratic symbols. All diagonal terms in the squared average
are bounded by 4/N. For distinct slots the first and second marginals test
the two centered projections. Both residuals agree since the average is
self-adjoint. The polynomial step extends this result by bounded operations. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter Topology
open scoped InnerProductSpace ENNReal ComplexConjugate
namespace QuantumNLS.DynSeedMomentsR47b
open TensorCarrier PhysicalTensor Local014StateLimits TraceClass TensorPlacements
open DynSeedPolynomialR47b

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "V[" N "]" => HilbertTensorPower ℂ H N
local notation "S[" N "]" => SymSector ℂ H N

theorem slot_covariance (w : H) (N : ℕ) (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    permOp N σ * slot w N i = slot w N (σ i) * permOp N σ := by
  apply ext_pt
  intro f
  simp only [mul_apply_eq_comp, slot_pt, permOp_pt, map_smul,
    Equiv.symm_apply_apply]
  congr 2
  funext j
  by_cases hj : j = σ i
  · subst j
    simp
  · rw [Function.update_of_ne hj, Function.update_of_ne]
    exact fun h => hj (by simpa using congrArg σ h)

theorem slot_pair (w : H) {N : ℕ} (hN : 2 ≤ N) (i j : Fin N) (hij : i ≠ j) (x : S[N]) :
    ⟪x.val, slot w N i (slot w N j x.val)⟫_ℂ =
      ⟪x.val, projT w N 2 hN x.val⟫_ℂ := by
  let z : Fin N := ⟨0, by omega⟩
  let o : Fin N := ⟨1, by omega⟩
  let f : Bool → Fin N := fun b => if b then o else z
  let g : Bool → Fin N := fun b => if b then j else i
  have hf : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp [f, z, o] at h ⊢
  have hg : Function.Injective g := by
    intro a b h
    cases a <;> cases b <;> simp [g, hij, Ne.symm hij] at h ⊢
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hσz : σ z = i := hσ false
  have hσo : σ o = j := hσ true
  have hv : permOp N σ x.val = x.val := x.property σ
  have h0 : projT w N 2 hN = slot w N z * slot w N o := by
    rw [projT_eq_slotProd]
    simp [slotProd, z, o, show 0 < N by omega, show 1 < N by omega]
  have he (k : Fin N) (y : V[N]) :
      permOp N σ (slot w N k y) = slot w N (σ k) (permOp N σ y) :=
    congrArg (fun T : V[N] →L[ℂ] V[N] => T y) (slot_covariance w N σ k)
  rw [h0, mul_apply_eq_comp]
  change _ = ⟪_, _⟫_ℂ
  rw [← (permHilbertIsometry (𝕜 := ℂ) (E := H) σ).inner_map_map x.val
    (slot w N z (slot w N o x.val))]
  change _ = ⟪permOp N σ x.val, permOp N σ (slot w N z (slot w N o x.val))⟫_ℂ
  rw [he, he, hv, hσz, hσo]

theorem slot_first (w : H) {N : ℕ} (i : Fin N) (x : S[N]) :
    ⟪x.val, slot w N i x.val⟫_ℂ =
      ⟪x.val, projT w N 1 (Nat.one_le_of_lt i.isLt) x.val⟫_ℂ := by
  have hi := i.isLt
  let z : Fin N := ⟨0, by omega⟩
  let σ := Equiv.swap z i
  have hv : permOp N σ x.val = x.val := x.property σ
  have h0 : projT w N 1 (by omega) = slot w N z := by
    rw [projT_eq_slotProd]
    simp [slotProd, z, show 0 < N by omega]
  have he := congrArg (fun T : V[N] →L[ℂ] V[N] => T x.val) (slot_covariance w N σ z)
  change permOp N σ (slot w N z x.val) = slot w N (σ z) (permOp N σ x.val) at he
  rw [h0, ← (permHilbertIsometry (𝕜 := ℂ) (E := H) σ).inner_map_map x.val (slot w N z x.val)]
  change _ = ⟪permOp N σ x.val, permOp N σ (slot w N z x.val)⟫_ℂ
  rw [he, hv]
  simp [σ]

def stateError {N : ℕ} (k : ℕ) (hk : k ≤ N) (x : S[N]) (v : H) : ℝ≥0∞ :=
  traceNorm (reducedDensityN N k hk x.val - proj v k)

theorem prefix_error {N : ℕ} (k : ℕ) (hk : k ≤ N) (w v : H)
    (hw : ‖w‖ = 1) (x : S[N]) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : stateError k hk x v ≤ ENNReal.ofReal δ) :
    ‖⟪x.val, projT w N k hk x.val⟫_ℂ - ((‖⟪w, v⟫_ℂ‖ ^ (2*k) : ℝ) : ℂ)‖ ≤ δ := by
  let y : V[k] := htpow k w
  have hy : ‖y‖ = 1 := by simp [y, norm_htpow, hw]
  have htrace : ⟪x.val, projT w N k hk x.val⟫_ℂ =
      ⟪y, reducedDensityN N k hk x.val y⟫_ℂ := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have cast_reduced (j m' : ℕ) (h : j = m') (χ : V[k+m']) :
        reducedDensityPower k j (castHTP (congrArg (k + ·) h.symm) χ) =
        reducedDensityPower k m' χ := by
      subst h
      rfl
    have hr : reducedDensityN (k+m) k hk x.val = reducedDensityPower k m x.val :=
      cast_reduced (k+m-k) m (by omega) x.val
    rw [hr]
    unfold projT reducedDensityPower
    have cast_block (j m' : ℕ) (h : j = m') :
        blockOp (congrArg (k + ·) h) (proj w k) = blockOp (rfl : k + m' = k + m') (proj w k) := by
      subst h
      rfl
    rw [cast_block (k+m-k) m (by omega)]
    let e := splitIsometry (𝕜 := ℂ) (E := H) k m
    change ⟪x.val, e.symm (htmap (InnerProductSpace.rankOne ℂ y y)
      (ContinuousLinearMap.id ℂ (V[m])) (e x.val))⟫_ℂ =
      ⟪y, reducedDensity (e x.val) y⟫_ℂ
    rw [← e.inner_map_map x.val (e.symm _), e.apply_symm_apply,
      ← inner_reducedDensity_left]
    have ha : (reducedDensity (e x.val)).adjoint = reducedDensity (e x.val) :=
      (reducedDensity_isSelfAdjoint (e x.val)).adjoint_eq
    simpa only [ha] using (reducedDensity (e x.val)).adjoint_inner_left y y
  have hprod : ⟪y, proj v k y⟫_ℂ = ((‖⟪w, v⟫_ℂ‖ ^ (2*k) : ℝ) : ℂ) := by
    unfold proj
    rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm
      (htpow k v : V[k]) y, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp [y, IntrinsicContact.inner_htpow, norm_pow, ← pow_mul, Nat.mul_comm]
  have hop := (norm_le_traceNorm (reducedDensityN N k hk x.val - proj v k)).trans he
  have hop' := (ENNReal.ofReal_le_ofReal_iff hδ).mp hop
  rw [htrace, ← hprod, ← inner_sub_right]
  change ‖⟪y, (reducedDensityN N k hk x.val - proj v k) y⟫_ℂ‖ ≤ _
  exact (norm_inner_le_norm _ _).trans (by
    simpa [hy] using ((reducedDensityN N k hk x.val - proj v k).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hop' (norm_nonneg y)))

def avg (w : H) (N : ℕ) : V[N] →L[ℂ] V[N] :=
  ((N : ℂ)⁻¹) • ∑ i : Fin N, slot w N i

theorem slot_norm_le (w : H) (hw : ‖w‖ = 1) (N : ℕ) (i : Fin N) :
    ‖slot w N i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using (slot_isProj hw i).norm_le x

theorem avg_norm_le (w : H) (hw : ‖w‖ = 1) (N : ℕ) : ‖avg w N‖ ≤ 1 := by
  cases N with
  | zero => simp [avg]
  | succ N =>
    rw [avg, norm_smul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (N+1), ‖slot w (N+1) i‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ _i : Fin (N+1), (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => slot_norm_le w hw _ i) (by positivity)
      _ = 1 := by simp [Nat.cast_succ, inv_mul_cancel₀ (by positivity : (N : ℝ) + 1 ≠ 0)]

def sectorAvg (w : H) (N : ℕ) : S[N] →L[ℂ] S[N] :=
  (symProjToSector N).comp ((avg w N).comp (SymSector ℂ H N).subtypeL)

theorem sectorAvg_adjoint (w : H) (hw : ‖w‖ = 1) (N : ℕ) :
    (sectorAvg w N).adjoint = sectorAvg w N := by
  have hav : (avg w N).adjoint = avg w N := by
    change star (avg w N) = _
    simp only [avg, star_smul, star_inv₀, star_natCast, star_sum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => (slot_isProj hw i).1.adjoint_eq)
  simp only [sectorAvg, BethePhysicalTransfer.symProjToSector_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hav,
    ContinuousLinearMap.comp_assoc]

theorem sectorAvg_norm_le (w : H) (hw : ‖w‖ = 1) (N : ℕ) : ‖sectorAvg w N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖symProjToSector N (avg w N x.val)‖ ≤ 1 * ‖x‖
  calc
    _ ≤ ‖avg w N x.val‖ := MixedTraceNorm.norm_symProjToSector_le N _
    _ ≤ ‖avg w N‖ * ‖x‖ := (avg w N).le_opNorm x.val
    _ ≤ _ := mul_le_mul_of_nonneg_right (avg_norm_le w hw N) (norm_nonneg x)

theorem centered_bound {N : ℕ} (hN : 2 ≤ N) (x : S[N]) (hx : ‖x‖ = 1)
    (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (h1 : stateError 1 (by omega : 1 ≤ N) x v ≤ ENNReal.ofReal δ)
    (h2 : stateError 2 hN x v ≤ ENNReal.ofReal δ) :
    ‖sectorAvg w N x - ((‖⟪w, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) • x‖ ^ 2 ≤ 4 / N + 3 * δ := by
  let q : ℝ := ‖⟪w, v⟫_ℂ‖ ^ 2
  have hq0 : 0 ≤ q := sq_nonneg _
  have hq1 : q ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) w v
    rw [hw, hv, one_mul] at h
    exact (sq_le_one_iff₀ (norm_nonneg _)).mpr h
  let y : Fin N → V[N] := fun i => slot w N i x.val - (q : ℂ) • x.val
  have hdiag (i : Fin N) : (⟪y i, y i⟫_ℂ).re ≤ 4 := by
    change RCLike.re ⟪y i, y i⟫_ℂ ≤ 4
    rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
    have h : ‖y i‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by
        simp only [norm_smul, Complex.norm_real, show ‖q‖ = q by exact Real.norm_of_nonneg hq0, show ‖x.val‖ = 1 from hx, mul_one]
        have hb : ‖slot w N i x.val‖ ≤ 1 := by
          simpa only [show ‖x.val‖ = 1 from hx] using (slot_isProj hw i).norm_le x.val
        linarith)
    nlinarith [norm_nonneg (y i)]
  have hoff (i j : Fin N) (hij : i ≠ j) : (⟪y i, y j⟫_ℂ).re ≤ 3 * δ := by
    have hf1 := prefix_error 1 (by omega) w v hw x δ hδ h1
    have hf2 := prefix_error 2 hN w v hw x δ hδ h2
    have hself : ⟪x.val, x.val⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, show ‖x.val‖ = 1 from hx]
      norm_num
    have hi := (slot_isProj hw i).1.adjoint_eq
    have hpair := slot_pair w hN i j hij x
    have hone : ‖⟪x.val, projT w N 1 (by omega) x.val⟫_ℂ - (q : ℂ)‖ ≤ δ := by
      simpa [q] using hf1
    have htwo : ‖⟪x.val, projT w N 2 hN x.val⟫_ℂ - ((q^2 : ℝ) : ℂ)‖ ≤ δ := by
      simpa [q, ← pow_mul] using hf2
    have eq : ⟪y i, y j⟫_ℂ =
        (⟪x.val, projT w N 2 hN x.val⟫_ℂ - ((q^2 : ℝ) : ℂ)) -
        (2 * (q : ℂ)) * (⟪x.val, projT w N 1 (by omega) x.val⟫_ℂ - (q : ℂ)) := by
      have hmove (t : V[N]) : ⟪slot w N i x.val, t⟫_ℂ =
          ⟪x.val, slot w N i t⟫_ℂ := by
        rw [← (slot w N i).adjoint_inner_left t x.val, hi]
      calc
        _ = ⟪slot w N i x.val, slot w N j x.val⟫_ℂ -
            ⟪(q : ℂ) • x.val, slot w N j x.val⟫_ℂ -
            (⟪slot w N i x.val, (q : ℂ) • x.val⟫_ℂ -
              ⟪(q : ℂ) • x.val, (q : ℂ) • x.val⟫_ℂ) := by
          unfold y
          rw [inner_sub_right, inner_sub_left, inner_sub_left]
        _ = _ := by
          rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
            Complex.conj_ofReal, hmove, hpair, hmove, slot_first, slot_first, hself]
          push_cast
          ring
    rw [eq]
    refine (Complex.re_le_norm _).trans ((norm_sub_le _ _).trans ?_)
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, show ‖q‖ = q by exact Real.norm_of_nonneg hq0]
    nlinarith [mul_le_mul_of_nonneg_left hone (by positivity : 0 ≤ 2 * q), mul_le_mul_of_nonneg_right hq1 hδ]
  have hsum : ‖∑ i : Fin N, y i‖ ^ 2 ≤ N * (4 + N * (3 * δ)) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
    simp_rw [inner_sum, map_sum]
    calc
      _ ≤ ∑ _i : Fin N, (4 + N * (3 * δ)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
        refine (add_le_add (hdiag i) (Finset.sum_le_sum fun j hj => hoff i j
          (Ne.symm (Finset.ne_of_mem_erase hj)))).trans ?_
        simp only [Finset.sum_const, nsmul_eq_mul]
        gcongr
        have hcard : (Finset.univ.erase i).card ≤ N := by
          simp
        exact_mod_cast hcard
      _ = _ := by simp [mul_add]
  have hav : avg w N x.val - (q : ℂ) • x.val = ((N : ℂ)⁻¹) • ∑ i : Fin N, y i := by
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp only [avg, y, smul_apply, sum_apply,
      Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have he : ((N : ℂ)⁻¹) • (N • ((q : ℂ) • x.val)) = (q : ℂ) • x.val := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN', one_smul]
    rw [he]
  have hs : ‖sectorAvg w N x - (q : ℂ) • x‖ ≤ ‖avg w N x.val - (q : ℂ) • x.val‖ := by
    have hmap : sectorAvg w N x - (q : ℂ) • x =
        symProjToSector N (avg w N x.val - (q : ℂ) • x.val) := by
      rw [map_sub, map_smul]
      change _ = sectorAvg w N x - (q : ℂ) • symProjToSector N x.val
      rw [symProjToSector_sym]
    rw [hmap]
    exact MixedTraceNorm.norm_symProjToSector_le N _
  have hNreal : (0 : ℝ) < N := by positivity
  calc
    _ ≤ ‖avg w N x.val - (q : ℂ) • x.val‖ ^ 2 := by gcongr
    _ = (N : ℝ)⁻¹ ^ 2 * ‖∑ i : Fin N, y i‖ ^ 2 := by
      rw [hav, norm_smul, norm_inv, Complex.norm_natCast, mul_pow]
    _ ≤ (N : ℝ)⁻¹ ^ 2 * (N * (4 + N * (3 * δ))) := by gcongr
    _ = _ := by field_simp

end QuantumNLS.DynSeedMomentsR47b
#print axioms QuantumNLS.DynSeedMomentsR47b.centered_bound


/-! R-300B8640, dynamic_full_torus.tex:154. The fixed classical trajectory
is the action-preserving hierarchy trajectory through the chosen unit
profile, as stipulated before the printed predecessor. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace QuantumNLS.DynSeedR47b
open DynSeedInputR47b DynSeedClassicalR47b DynSeedPolynomialR47b DynSeedGradingR47b
open DynSeedHaarR47b DynSeedMomentsR47b DynSeedDiagonalR47b
open PhysicalTensor TensorCarrier BetheCoefficientTransform Def044D1SpectralR51a
open CountRotations FullCharacterProjection Def033HierarchyR24m ActualModelTargetR53a

variable {L κ : ℝ} [Fact (0 < L)]

/-- The two residuals summed before the supremum, as in the printed lemma. -/
def boxResidual (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L) (R : Finset ℕ)
    (lo hi : ℕ → ℝ) (a b : ℤ) (n : ℕ) (A : HN L (n+1) →L[ℂ] HN L (n+1)) : ℝ≥0∞ :=
  ⨆ t : TimeBox R lo hi, ENNReal.ofReal
    (DynSeedPolynomialR47b.residual A (symbol hκ a b (classicalOrbit hκ F u R t.val)) (quantumOrbit hκ u R t.val n))

/-- Bounded operators in the physical sectors, exact directed grading and
uniform convergence of the two vector residuals. -/
def SeedStatement (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L) (R : Finset ℕ)
    (lo hi : ℕ → ℝ) (a b : ℤ) : Prop :=
  ∃ A : (n : ℕ) → HN L (n+1) →L[ℂ] HN L (n+1),
    (∀ n, Graded (basis hκ n) a b (A n)) ∧
    Tendsto (fun n => boxResidual hκ F u R lo hi a b n (A n)) atTop (𝓝 0)

/-- Extract the uniform marginal bounds without any growing-rank use. -/
theorem uniform_marginal (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L) (R : Finset ℕ)
    (lo hi : ℕ → ℝ) (hfull : FullTorus hκ F u R) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ hk : k ≤ n+1, ∀ t : TimeBox R lo hi, ∀ θ : AngleTorus,
      stateError k hk
        (quantumRotation (basis hκ n) θ (quantumOrbit hκ u R t.val n))
        (physicalAngle hκ θ (classicalOrbit hκ F u R t.val)) ≤ ENNReal.ofReal δ := by
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hfull k lo hi) (ENNReal.ofReal δ)
    (ENNReal.ofReal_pos.mpr hδ)] with n hn
  intro hk t θ
  rw [dite_eq_left hk] at hn
  let Q (t : TimeBox R lo hi) (θ : AngleTorus) : ℝ≥0∞ :=
    marginalError n k hk (quantumRotation (basis hκ n) θ (quantumOrbit hκ u R t.val n))
      (physicalAngle hκ θ (classicalOrbit hκ F u R t.val))
  change Q t θ ≤ _
  exact ((le_iSup (Q t) θ).trans (le_iSup (fun t => ⨆ θ, Q t θ) t)).trans hn

theorem quadratic_unit {X : Type*} (v : X → L2T L) (x : (n : ℕ) → X → HN L (n+1))
    (hv : ∀ p, ‖v p‖ = 1) (hx : ∀ n p, ‖x n p‖ = 1)
    (harg : ∀ k δ, 0 < δ → ∀ᶠ n in atTop, ∀ hk : k ≤ n+1, ∀ p,
      stateError k hk (x n p) (v p) ≤ ENNReal.ofReal δ)
    (w : L2T L) (hw : ‖w‖ = 1) :
    Represents v x (fun u => ((‖⟪w, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) := by
  refine ⟨fun n => sectorAvg w (n+1), 1, zero_le_one, fun n => sectorAvg_norm_le w hw _, ?_, ?_⟩
  · intro p
    have h := norm_inner_le_norm (𝕜 := ℂ) w (v p)
    rw [hw, hv p, one_mul] at h
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    exact (pow_le_one₀ (norm_nonneg _) h : ‖⟪w, v p⟫_ℂ‖ ^ 2 ≤ 1)
  intro ε hε
  let δ : ℝ := ε ^ 2 / 24
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hNsmall : ∀ᶠ n : ℕ in atTop, 4 / (↑n + 1 : ℝ) < ε ^ 2 / 8 := by
    have h : Tendsto (fun n : ℕ => 4 / (↑n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
    exact h.eventually (gt_mem_nhds (by positivity))
  filter_upwards [harg 1 δ hδ, harg 2 δ hδ, eventually_ge_atTop (1 : ℕ), hNsmall]
    with n h₁ h₂ hn hsmall
  intro p
  have hN : 2 ≤ n+1 := by omega
  have hb := centered_bound hN (x n p) (hx n p) (v p) w (hv p) hw δ hδ.le
    (h₁ (by omega) p) (h₂ hN p)
  have hs : ‖sectorAvg w (n+1) (x n p) - ((‖⟪w, v p⟫_ℂ‖ ^ 2 : ℝ) : ℂ) • x n p‖ ≤ ε / 2 := by
    have hh : 4 / ((n+1 : ℕ) : ℝ) + 3 * δ ≤ (ε/2)^2 := by
      push_cast
      dsimp [δ]
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hb.trans hh)
  unfold DynSeedPolynomialR47b.residual
  rw [sectorAvg_adjoint w hw, Complex.conj_ofReal]
  linarith

theorem quadratic {X : Type*} (v : X → L2T L) (x : (n : ℕ) → X → HN L (n+1))
    (hv : ∀ p, ‖v p‖ = 1) (hx : ∀ n p, ‖x n p‖ = 1)
    (harg : ∀ k δ, 0 < δ → ∀ᶠ n in atTop, ∀ hk : k ≤ n+1, ∀ p,
      stateError k hk (x n p) (v p) ≤ ENNReal.ofReal δ)
    (w : L2T L) :
    Represents v x (fun u => ((‖⟪w, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) := by
  by_cases hw : w = 0
  · simpa [hw] using Represents.constant v x 0
  let y := ((‖w‖ : ℂ)⁻¹) • w
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hy : ‖y‖ = 1 := by
    rw [show y = ((‖w‖ : ℂ)⁻¹) • w from rfl, norm_smul, norm_inv, Complex.norm_real,
      norm_norm, inv_mul_cancel₀ hn.ne']
  have hw' : w = (‖w‖ : ℂ) • y := by
    have h : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
    simp [y, smul_smul, mul_inv_cancel₀ h]
  have hscale : (fun u : L2T L => ((‖⟪w, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) =
    fun u => ((‖w‖ ^ 2 : ℝ) : ℂ) * ((‖⟪y, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext u
    have hi : ⟪w, u⟫_ℂ = (‖w‖ : ℂ) * ⟪y, u⟫_ℂ := by
      nth_rw 1 [hw']
      rw [inner_smul_left, Complex.conj_ofReal]
    rw [hi, norm_mul, Complex.norm_real, norm_norm, mul_pow, Complex.ofReal_mul]
  rw [hscale]
  exact (Represents.constant v x _).mul (quadratic_unit v x hv hx harg y hy)

/-- The intermediate deduction uses the complete printed predecessor as its
one pending input. The finite-angle premise and the action-preserving
hierarchy along the fixed profile are the printed context. -/
theorem seed_intermediate (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b)
    (flow_actions : ∀ t : TimeBox R lo hi,
      classicalOrbit hκ F u R t.val ∈ torus hκ (physical u))
    (mixed : MixedFinite hκ F u R)
    (PredecessorInput : DynftFullTorusInput hκ F u R) :
    SeedStatement hκ F u R lo hi a b := by
  let X := TimeBox R lo hi × AngleTorus
  let v : X → L2T L := fun p => physicalAngle hκ p.2 (classicalOrbit hκ F u R p.1.val)
  let x (n : ℕ) (p : X) : HN L (n+1) :=
    quantumRotation (basis hκ n) p.2 (quantumOrbit hκ u R p.1.val n)
  have hvT (p : X) : v p ∈ torus hκ (physical u) :=
    angle_mem_torus hκ _ _ (flow_actions p.1) p.2
  have hv (p : X) : ‖v p‖ = 1 := (torus_norm hκ (hvT p)).trans hu
  have hx (n : ℕ) (p : X) : ‖x n p‖ = 1 := by
    change ‖quantumRotation (basis hκ n) p.2
      (ActualModelQuantumR52a.chargeUnitary hκ R p.1.val n
        (HighMomentsOps.wvec (n+1) (physical u)))‖ = 1
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    change ‖(htpow (n+1) (physical u) : HilbertTensorPower ℂ (L2T L) (n+1))‖ = 1
    simp [norm_htpow, hu]
  have harg : ∀ k δ, 0 < δ → ∀ᶠ n in atTop, ∀ hk : k ≤ n+1, ∀ p,
      stateError k hk (x n p) (v p) ≤ ENNReal.ofReal δ := by
    intro k δ hδ
    filter_upwards [uniform_marginal hκ F u R lo hi (PredecessorInput mixed) k δ hδ] with n hn
    exact fun hk p => hn hk p.1 p.2
  apply diagonal (fun n A => Graded (basis hκ n) a b A)
    (boxResidual hκ F u R lo hi a b) (fun _ => 0) (fun n => zero_graded (basis hκ n) a b)
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨f, hf, hclose⟩ := approximants hκ (physical u) a b hquarter
  obtain ⟨T, _, _, _, _, hstrong⟩ := coherent_residual hf (quadratic v x hv hx harg)
  filter_upwards [hstrong (ε / 4) hquarter] with n hn
  let C := component (basis hκ n) (T n) a b
  refine ⟨C, component_graded (basis hκ n) (T n) a b hab, ?_⟩
  unfold boxResidual
  apply iSup_le
  intro t
  let z := symbol hκ a b (classicalOrbit hκ F u R t.val)
  let ψ := quantumOrbit hκ u R t.val n
  have he (θ : AngleTorus) : symbol hκ a b (v (t, θ)) = character b a θ * z :=
    symbol_angle hκ a b θ _
  have hfwd (θ : AngleTorus) :
      ‖T n (x n (t, θ)) - (character b a θ * z) • x n (t, θ)‖ ≤ ε / 2 := by
    rw [← he θ]
    have h₁ : ‖T n (x n (t, θ)) - f (v (t, θ)) • x n (t, θ)‖ ≤ ε/4 :=
      le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hn (t, θ))
    have h₂ := (hclose (v (t, θ)) (hvT (t, θ))).le
    have hsplit : T n (x n (t, θ)) - symbol hκ a b (v (t, θ)) • x n (t, θ) =
        (T n (x n (t, θ)) - f (v (t, θ)) • x n (t, θ)) +
          (f (v (t, θ)) - symbol hκ a b (v (t, θ))) • x n (t, θ) := by
      rw [sub_smul]
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (by rw [norm_smul, hx, mul_one]; linarith)
  have hadj (θ : AngleTorus) :
      ‖(T n).adjoint (x n (t, θ)) - conj (character b a θ * z) • x n (t, θ)‖ ≤ ε / 2 := by
    rw [← he θ]
    have h₁ : ‖(T n).adjoint (x n (t, θ)) - conj (f (v (t, θ))) • x n (t, θ)‖ ≤ ε/4 :=
      le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hn (t, θ))
    have h₂ := (hclose (v (t, θ)) (hvT (t, θ))).le
    have hsplit : (T n).adjoint (x n (t, θ)) - conj (symbol hκ a b (v (t, θ))) • x n (t, θ) =
        ((T n).adjoint (x n (t, θ)) - conj (f (v (t, θ))) • x n (t, θ)) +
          conj (f (v (t, θ)) - symbol hκ a b (v (t, θ))) • x n (t, θ) := by
      rw [map_sub, sub_smul]
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (by rw [norm_smul, Complex.norm_conj, hx, mul_one]; linarith)
  have hc := residual_le (basis hκ n) (T n) a b ψ z (ε/2) hfwd
  have hc' := adjoint_residual_le (basis hκ n) (T n) a b ψ z (ε/2) hadj
  apply ENNReal.ofReal_le_ofReal
  exact (add_le_add hc hc').trans (by linarith)

end QuantumNLS.DynSeedR47b
#print axioms QuantumNLS.DynSeedR47b.seed_intermediate

set_option maxHeartbeats 30000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DynSeed" ||
        n.toString.startsWith "_private.QuantumNLS.DynSeed" then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"R47b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
