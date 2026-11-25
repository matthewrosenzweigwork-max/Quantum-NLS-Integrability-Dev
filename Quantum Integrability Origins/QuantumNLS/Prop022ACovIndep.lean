import Mathlib
import QuantumNLS.Prop022ACovPhys
import QuantumNLS.Prop022ACovCoef
import QuantumNLS.Prop022AIndep

/-! PROP-022 route A, stage A5d: EXACT independence of the transporting unitary.

Write `U' = U.trans R` for the unitary `R = chg U U'` of `L²(𝕋_L)`.  Using the covariance of
`Prop022ACovPhys` and `Prop022ACovCoef`:
* `aSym_indep`, `bSym_indep`: the coefficient data `a_t`, `b_t` of the quadratic generator are
  independent of `U`;
* `QH_indep`: the transported generator `Q_H(a,b)` is independent of `U` (for every `a`, `b`);
* `VH_vac_indep`, `VH_indep`: the propagator `V_H(t,s)` is independent of `U` exactly (the unimodular
  phase of `Prop022AIndep.VH_phase` is `1`: it is constant by the Schrödinger equation and equals
  `1` at `t = s`). -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022ACovIndep
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GClassical Prop022GLinear Prop022AFock Prop022AIndep
open Prop022ACovPhys Prop022ACovCoef Prop022OVacuum Prop022FactorialCoefficientsR115
open Prop022ActualProfileR117 Prop022PositiveDataR126 Prop022ACoherent Occupation OccupationUnitary
open Ext006IdentityCyclicR35a Ext006PhysQuasifree Ext006PhysFockCoord Prop022AWeyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

lemma symMap_trans' {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (U : E ≃ₗᵢ[ℂ] F) (V : F ≃ₗᵢ[ℂ] G) (n : ℕ) (x : SymSector ℂ E n) :
    symMap (U.trans V) n x = symMap V n (symMap U n x) :=
  Subtype.ext (tensorMap_trans U V n (x : HilbertTensorPower ℂ E n))

lemma symMap_symm_trans' {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (U : E ≃ₗᵢ[ℂ] F) (V : F ≃ₗᵢ[ℂ] G) (n : ℕ) (y : SymSector ℂ G n) :
    (symMap (U.trans V) n).symm y = (symMap U n).symm ((symMap V n).symm y) := by
  rw [LinearIsometryEquiv.symm_apply_eq, symMap_trans', LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

lemma conjSym_trans (U : H ≃ₗᵢ[ℂ] L2T L) (R : L2T L ≃ₗᵢ[ℂ] L2T L) (m : ℕ)
    (T : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    conjSym (U.trans R) m T = conjSym R m (conjSym U m T) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [conjSym_apply, conjSym_apply, conjSym_apply, symMap_symm_trans', symMap_trans']

lemma BL_trans (U : H ≃ₗᵢ[ℂ] L2T L) (R : L2T L ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (m : ℕ) :
    BL (U.trans R) K m = conjSym R m (BL U K m) := by
  cases m with
  | zero =>
    apply ContinuousLinearMap.ext
    intro y
    simp [BL, positiveExtension, conjSym_apply]
  | succ n =>
    exact conjSym_trans U R (n + 1) (K n)

section Data
variable (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A) (hs : KSelfAdj K)
  (u₀ : H) (hu₀ : ‖u₀‖ = 1)

lemma profile_trans (U : H ≃ₗᵢ[ℂ] L2T L) (R : L2T L ≃ₗᵢ[ℂ] L2T L) (t : ℝ) :
    profile (BL (U.trans R) K) M A hA (BL_bound (U.trans R) K M A hK)
      (BL_selfAdj (U.trans R) K hs) (sphL (U.trans R) u₀ hu₀) t =
    R (profile (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t) := by
  have h := congrFun (profH_indep U (U.trans R) K M A hA hK hs u₀ hu₀) t
  unfold profH at h
  change U.symm _ = U.symm (R.symm _) at h
  have h2 := U.symm.injective h
  rw [LinearIsometryEquiv.eq_symm_apply] at h2
  exact h2.symm

lemma profile_unit (U : H ≃ₗᵢ[ℂ] L2T L) (t : ℝ) :
    ‖profile (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t‖ = 1 := by
  obtain ⟨-, -, hn, -, -⟩ := profile_spec (BL U K) M A hA (BL_bound U K M A hK)
    (BL_selfAdj U K hs) (sphL U u₀ hu₀)
  exact hn t

lemma backConj_trans (U : H ≃ₗᵢ[ℂ] L2T L) (R : L2T L ≃ₗᵢ[ℂ] L2T L) (m : ℕ)
    (X : HN L m →L[ℂ] HN L m) :
    backConj (U.trans R) m (conjSym R m X) = backConj U m X := by
  apply ContinuousLinearMap.ext
  intro y
  simp only [backConj, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, symMap_symm_trans', symMap_trans', conjSym_apply,
    LinearIsometryEquiv.symm_apply_apply]

/-- **The coefficient `a_t` of the quadratic generator is independent of `U`.** -/
theorem aSym_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) (t : ℝ) :
    aSym U' K M A hA hK hs u₀ hu₀ t = aSym U K M A hA hK hs u₀ hu₀ t := by
  have hU' : U' = U.trans (chg U U') := by ext v; simp [chg]
  generalize chg U U' = R at hU'
  subst hU'
  have hBL : BL (U.trans R) K = fun m => conjSym R m (BL U K m) := funext (BL_trans U R K)
  unfold aSym
  rw [profile_trans K M A hA hK hs u₀ hu₀ U R t, hBL]
  rw [← numberCoefficient_cov R (BL U K) M A hA (BL_bound U K M A hK) _
    (profile_unit K M A hA hK hs u₀ hu₀ U t)]
  exact backConj_trans U R 1 _

/-- **The coefficient `b_t` of the quadratic generator is independent of `U`.** -/
theorem bSym_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) (t : ℝ) :
    bSym U' K M A hA hK hs u₀ hu₀ t = bSym U K M A hA hK hs u₀ hu₀ t := by
  have hU' : U' = U.trans (chg U U') := by ext v; simp [chg]
  generalize chg U U' = R at hU'
  subst hU'
  have hBL : BL (U.trans R) K = fun m => conjSym R m (BL U K m) := funext (BL_trans U R K)
  unfold bSym
  rw [profile_trans K M A hA hK hs u₀ hu₀ U R t, hBL]
  rw [← pairCoefficient_cov R (BL U K) _, symMap_symm_trans', LinearIsometryEquiv.symm_apply_apply]

end Data

/-! ### The generator -/

lemma gam_trans (U : H ≃ₗᵢ[ℂ] L2T L) (R : L2T L ≃ₗᵢ[ℂ] L2T L) (y : FockSpace H) :
    gam (U.trans R) y = GR R (gam U y) := fockMap_trans U R y

lemma gam_symm_trans (U : H ≃ₗᵢ[ℂ] L2T L) (R : L2T L ≃ₗᵢ[ℂ] L2T L) (w : Fock L) :
    (gam (U.trans R)).symm w = (gam U).symm ((GR R).symm w) := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  rw [gam_trans, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **The transported quadratic generator does not depend on the transporting unitary.** -/
theorem QH_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1)
    (b : SymSector ℂ H 2) (y : FockSpace H) : QH U' a b y = QH U a b y := by
  have hU' : U' = U.trans (chg U U') := by ext v; simp [chg]
  generalize chg U U' = R at hU'
  subst hU'
  unfold QH
  rw [gam_symm_trans, gam_trans, rootLift_cov, conjSym_trans, symMap_trans',
    ← strongCoordinates_cov, LinearIsometryEquiv.symm_apply_apply]

lemma rootLift_smul (j : ℕ) (c : ℂ) (hc : c ≠ 0) (w : Fock L) :
    Ext005FormCutoffR109.rootLift j (c • w) = c • Ext005FormCutoffR109.rootLift j w := by
  by_cases hw : w ∈ Ext005Moments.momentDomain (L := L) j
  · have hcw : c • w ∈ Ext005Moments.momentDomain (L := L) j := Submodule.smul_mem _ c hw
    rw [Ext005FormCutoffR109.rootLift_eq j _ hw, Ext005FormCutoffR109.rootLift_eq j _ hcw]
    exact LinearPMap.map_smul (Ext005Moments.momentRoot (L := L) j) c ⟨w, hw⟩
  · have hcw : c • w ∉ Ext005Moments.momentDomain (L := L) j := by
      intro h
      apply hw
      have := Submodule.smul_mem _ c⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    simp [Ext005FormCutoffR109.rootLift, hw, hcw]

lemma QH_smul (U : H ≃ₗᵢ[ℂ] L2T L) (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1)
    (b : SymSector ℂ H 2) (c : ℂ) (hc : c ≠ 0) (y : FockSpace H) :
    QH U a b (c • y) = c • QH U a b y := by
  unfold QH
  rw [map_smul, rootLift_smul _ c hc, map_smul, map_smul]

/-! ### The phase of the propagator -/

lemma vac_eq_single : (vac (L := L)) = lp.single 2 0 (ketVec (L := L) 0) := by
  have hv : Phi (vac (L := L)) = secEmb 0 (ketVec (L := L) 0) := by
    have h1 : (Phi (L := L)) (vac (L := L)) = (ketD (0 : Occ)).1 := by
      unfold vac
      rw [physCore_ket, LinearIsometryEquiv.apply_symm_apply]
      rfl
    rw [h1, ket_eq_emb (L := L) 0]
    rfl
  apply (Phi (L := L)).injective
  exact hv

lemma vacH_mem (U : H ≃ₗᵢ[ℂ] L2T L) (j : ℕ) : vacH U ∈ momentDomainH j := by
  rw [← gam_mem_momentDomain U j, vacH, LinearIsometryEquiv.apply_symm_apply,
    Ext005Moments.momentDomain_iff]
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  have hn0 : n ≠ 0 := by simpa using hn
  have h0 : (vac (L := L)) n = 0 := by
    rw [vac_eq_single]
    exact lp.single_apply_ne 2 0 _ hn0
  rw [h0]
  simp


section Phase
variable (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A)
  (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

/-- **The vacuum evolution does not depend on the transporting unitary.** -/
theorem VH_vac_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) (t : ℝ) :
    VH U' K M A hA.le hK hs u₀ hu₀ (by linarith) t 0 (vacH U) =
      VH U K M A hA.le hK hs u₀ hu₀ (by linarith) t 0 (vacH U) := by
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨w, e, -⟩ := exists_hilbertBasis ℂ H
  have T1 := PROP022_fock_transport U K M A hM hA hK hs u₀ hu₀ 0 1 le_rfl e
  have T2 := PROP022_fock_transport U' K M A hM hA hK hs u₀ hu₀ 0 1 le_rfl e
  obtain ⟨h01, -, -, hder1, -, hvac1⟩ := T1
  obtain ⟨h02, -, -, hder2, -, -⟩ := T2
  set x := vacH U with hx
  set f : ℝ → FockSpace H := fun t => VH U K M A hA.le hK hs u₀ hu₀ hM0 t 0 x with hf
  set g : ℝ → FockSpace H := fun t => VH U' K M A hA.le hK hs u₀ hu₀ hM0 t 0 x with hg
  set Q : ℝ → FockSpace H → FockSpace H := fun t =>
    QH U (aSym U K M A hA.le hK hs u₀ hu₀ t) (bSym U K M A hA.le hK hs u₀ hu₀ t) with hQ
  have hxd : ∀ j : ℕ, x ∈ momentDomainH j := fun j => vacH_mem U j
  have hfd : ∀ t, HasDerivAt f ((-Complex.I) • Q t (f t)) t := fun t => hder1 0 t x hxd
  have hgd : ∀ t, HasDerivAt g ((-Complex.I) • Q t (g t)) t := by
    intro t
    have h := hder2 0 t x hxd
    rw [QH_indep U U', aSym_indep K M A hA.le hK hs u₀ hu₀ U U',
      bSym_indep K M A hA.le hK hs u₀ hu₀ U U'] at h
    exact h
  have hfn : ∀ t, ‖f t‖ = 1 := fun t => (hvac1 t).2.1
  have hf0 : f 0 = x := h01 0 x
  have hg0 : g 0 = x := h02 0 x
  have hphase : ∀ t, ∃ c : ℂ, ‖c‖ = 1 ∧ g t = c • f t := by
    intro t
    obtain ⟨c, hc, h⟩ := VH_phase K M A hA.le hK hs u₀ hu₀ hM0 U U' t 0
    exact ⟨c, hc, h x⟩
  set z : ℝ → ℂ := fun t => ⟪f t, g t⟫_ℂ with hz
  have hzc : ∀ t, ‖z t‖ = 1 ∧ g t = z t • f t := by
    intro t
    obtain ⟨c, hc, h⟩ := hphase t
    have hzt : z t = c := by
      change ⟪f t, g t⟫_ℂ = c
      rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K, hfn t]
      simp
    exact ⟨by rw [hzt]; exact hc, by rw [hzt]; exact h⟩
  have hzd : ∀ t, HasDerivAt z (⟪f t, (-Complex.I) • Q t (g t)⟫_ℂ +
      ⟪(-Complex.I) • Q t (f t), g t⟫_ℂ) t := fun t =>
    HasDerivAt.inner ℂ (hfd t) (hgd t)
  have hz0 : ∀ t, HasDerivAt z 0 t := by
    intro t
    set D := ⟪f t, (-Complex.I) • Q t (g t)⟫_ℂ + ⟪(-Complex.I) • Q t (f t), g t⟫_ℂ with hD
    have h1 : HasDerivAt (fun r => z r • f r) (z t • ((-Complex.I) • Q t (f t)) + D • f t) t :=
      (hzd t).smul (hfd t)
    have h2 : HasDerivAt (fun r => z r • f r) ((-Complex.I) • Q t (g t)) t := by
      have : (fun r => z r • f r) = g := funext fun r => (hzc r).2.symm
      rw [this]; exact hgd t
    have h3 := h1.unique h2
    have hz1 : z t ≠ 0 := by
      intro h; have := (hzc t).1; rw [h] at this; simp at this
    have hQs : Q t (z t • f t) = z t • Q t (f t) := QH_smul U _ _ (z t) hz1 _
    rw [(hzc t).2, hQs, smul_comm (-Complex.I) (z t) (Q t (f t))] at h3
    have h4 : D • f t = 0 := by
      have h5 := congrArg (fun v => v - z t • (-Complex.I • Q t (f t))) h3
      simpa using h5
    have hft : f t ≠ 0 := by
      intro h; have := hfn t; rw [h] at this; simp at this
    have hD0 : D = 0 := by
      rcases smul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h hft
    rw [← hD0]
    exact hzd t
  have hconst : ∀ t, z t = z 0 := fun t =>
    is_const_of_deriv_eq_zero (fun r => (hz0 r).differentiableAt) (fun r => (hz0 r).deriv) t 0
  have hz00 : z 0 = 1 := by
    change ⟪f 0, g 0⟫_ℂ = 1
    rw [hf0, hg0, inner_self_eq_norm_sq_to_K]
    have := hfn 0
    rw [hf0] at this
    rw [this]; simp
  have := (hzc t).2
  rw [hconst t, hz00, one_smul] at this
  exact this

/-- **EXACT independence of the propagator `V_H(t,s)` of the transporting unitary.** -/
theorem VH_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) (t s : ℝ) :
    VH U' K M A hA.le hK hs u₀ hu₀ (by linarith) t s =
      VH U K M A hA.le hK hs u₀ hu₀ (by linarith) t s := by
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨w, e, -⟩ := exists_hilbertBasis ℂ H
  have hv : ∀ t, VH U' K M A hA.le hK hs u₀ hu₀ hM0 t 0 = VH U K M A hA.le hK hs u₀ hu₀ hM0 t 0 := by
    intro t
    obtain ⟨z, hz, hph⟩ := VH_phase K M A hA.le hK hs u₀ hu₀ hM0 U U' t 0
    have h := VH_vac_indep K M A hM hA hK hs u₀ hu₀ U U' t
    have h2 := hph (vacH U)
    rw [h] at h2
    have hn : ‖vacH U‖ = 1 := by
      have T1 := PROP022_fock_transport U K M A hM hA hK hs u₀ hu₀ 0 1 le_rfl e
      obtain ⟨h01, -, -, -, -, hvac1⟩ := T1
      have := (hvac1 0).2.1
      rwa [h01 0 (vacH U)] at this
    have hVn : ‖VH U K M A hA.le hK hs u₀ hu₀ hM0 t 0 (vacH U)‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map, hn]
    have hz1 : z = 1 := by
      have h3 : (z - 1) • VH U K M A hA.le hK hs u₀ hu₀ hM0 t 0 (vacH U) = 0 := by
        rw [sub_smul, one_smul, ← h2, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · exact sub_eq_zero.mp h
      · rw [h] at hVn; simp at hVn
    subst hz1
    ext x
    rw [hph x, one_smul]
  have hcoc := PROP022_fock_transport U K M A hM hA hK hs u₀ hu₀ 0 1 le_rfl e
  have hcoc' := PROP022_fock_transport U' K M A hM hA hK hs u₀ hu₀ 0 1 le_rfl e
  obtain ⟨-, hc1, -, -, -, -⟩ := hcoc
  obtain ⟨-, hc2, -, -, -, -⟩ := hcoc'
  ext w
  obtain ⟨x₀, rfl⟩ := (VH U K M A hA.le hK hs u₀ hu₀ hM0 s 0).surjective w
  have e1 := hc1 0 s t x₀
  have e2 := hc2 0 s t x₀
  have e3 : VH U' K M A hA.le hK hs u₀ hu₀ hM0 s 0 x₀ = VH U K M A hA.le hK hs u₀ hu₀ hM0 s 0 x₀ := by
    rw [hv s]
  rw [e3] at e2
  rw [e1, e2, hv t]

end Phase

end QuantumNLS.Prop022ACovIndep

#print axioms QuantumNLS.Prop022ACovIndep.aSym_indep
#print axioms QuantumNLS.Prop022ACovIndep.bSym_indep
#print axioms QuantumNLS.Prop022ACovIndep.QH_indep
#print axioms QuantumNLS.Prop022ACovIndep.VH_vac_indep
#print axioms QuantumNLS.Prop022ACovIndep.VH_indep
