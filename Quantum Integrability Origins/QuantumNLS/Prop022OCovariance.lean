import QuantumNLS.Prop022OClassical
import QuantumNLS.Prop022OFormIdentity

/-! PROP-022 takeover, stage O6b. Covariance of the ACTUAL R122 quadratic
propagator. For smooth x, y the function
  k(r) = <V(r,s) y, phi(S'(r,s) h) V(r,s) x>
has zero derivative: the strong Schrodinger equation (R125/R126), the
classical generator equation (O6a), the first-moment continuity of the
evolution (R122) and the commutator form identity (O5) combine exactly.
Hence V(t,s) is field covariant on the smooth domain, and by O1 it is a
source-Weyl implementer of S'(t,s) = J⁻¹ S(t,s) J. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate
open Filter Topology Set
namespace QuantumNLS.Prop022OCovariance
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005FormCutoffR109 Occupation Prop022OQuadraticKet Prop022OWeakIdentity
open Prop022OFormIdentity Prop022OClassical Prop022OWeylField
open Ext006BogoliubovAlg Ext006SmoothOperatorsR34a Ext006StrongFieldR41a
open Ext006IdentityCyclicR35a Ext006PhysFockCoord Ext006ModeDomainR33a
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022FockPropagatorR122
open Prop022DomainR122 Prop022SmoothDomainR126
variable {L : ℝ} [Fact (0 < L)]

local notation "OF" => Ext006VacuumRecurrence.Fock

/-! ### Occupation weights and the physical first moment -/

lemma coefficient_symm (v : OF) :
    Ext006PhysicalVacuum.coefficient ((Phi (L := L)).symm v) = v := by
  funext m
  rw [← Phi_apply, LinearIsometryEquiv.apply_symm_apply]

lemma occ_moment (v : D) :
    T v.1 + ‖v.1‖^2 = ‖rootLift 1 ((Phi (L := L)).symm v.1)‖^2 := by
  set y := (Phi (L := L)).symm v.1
  have hy : y ∈ momentDomain (L := L) 1 := smooth_mem v 1
  have hroot : ‖rootLift 1 y‖^2 = energy 1 y := by
    rw [rootLift_eq 1 y hy]
    exact (energy_eq_root 1 ⟨y, hy⟩).symm
  rw [hroot]
  have hf : Summable (fun m : Occ => ((total m : ℝ) + 1)^1 * ‖v.1 m‖^2) := v.2 1
  have hcoef : ∀ m, Ext006PhysicalVacuum.coefficient y m = v.1 m := fun m => by
    rw [coefficient_symm]
  have hsig : (∑' m : Occ, ((total m : ℝ) + 1)^1 * ‖v.1 m‖^2) =
      ∑' n : ℕ, ∑' m : Arr n, ((total m.val : ℝ) + 1)^1 * ‖v.1 m.val‖^2 := by
    rw [← (Equiv.sigmaFiberEquiv (fun m : Occ => total m)).tsum_eq]
    exact ((Equiv.sigmaFiberEquiv (fun m : Occ => total m)).summable_iff.mpr hf).tsum_sigma'
      (fun n => by
        have := (sector_weighted_parseval 1 n y).1
        simp only [hcoef] at this
        exact this)
  have hsec : ∀ n, (∑' m : Arr n, ((total m.val : ℝ) + 1)^1 * ‖v.1 m.val‖^2) =
      momentWeight 1 n * ‖y n‖^2 := fun n => by
    simpa only [hcoef] using (sector_weighted_parseval 1 n y).2
  have hT : Summable (fun m : Occ => (total m : ℝ) * ‖v.1 m‖^2) :=
    Summable.of_nonneg_of_le (f := fun m : Occ => ((total m : ℝ) + 1)^1 * ‖v.1 m‖^2)
      (fun _ => by positivity) (fun m => by nlinarith [sq_nonneg ‖v.1 m‖]) hf
  have hN : ‖v.1‖^2 = ∑' m : Occ, ‖v.1 m‖^2 := by
    have := (lp.hasSum_norm (p := 2) (by norm_num) v.1).tsum_eq
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    exact this.symm
  have hS : Summable (fun m : Occ => ‖v.1 m‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := 2) (by norm_num) v.1).summable
  rw [T, hN, ← hT.tsum_add hS, energy]
  rw [show (fun m : Occ => (total m : ℝ) * ‖v.1 m‖^2 + ‖v.1 m‖^2) =
      fun m => ((total m : ℝ) + 1)^1 * ‖v.1 m‖^2 by funext m; ring, hsig]
  exact tsum_congr hsec

/-- The first-moment norm of a smooth vector. -/
def ρ (v : D) : ℝ := Real.sqrt (T v.1 + ‖v.1‖^2)

lemma ρ_eq (v : D) : ρ v = ‖rootLift 1 ((Phi (L := L)).symm v.1)‖ := by
  rw [ρ, occ_moment (L := L) v, Real.sqrt_sq (norm_nonneg _)]

lemma field_ρ (h : H) (v : D) : ‖(field h v).1‖ ≤ 2 * ‖h‖ * ρ v := field_bound h v

/-! ### The occupation evolution -/

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
local notation "V" => evolution B M A hM hA hB hs u₀
local notation "aₜ" t => numberCoefficient B (profile B M A hA hB hs u₀ t)
local notation "bₜ" t => pairCoefficient B (profile B M A hA hB hs u₀ t)

/-- The actual propagator in occupation coordinates. -/
def Vo (s t : ℝ) (w : OF) : OF := Phi (L := L) (V s t ((Phi (L := L)).symm w))

lemma Vo_smooth (s t : ℝ) (x : D) : Smooth (Vo B M A hM hA hB hs u₀ s t x.1) := by
  have h := (evolution_smooth_iff B M A hM hA hB hs u₀ s t ((Phi (L := L)).symm x.1)).mpr
    (by rw [coefficient_symm]; exact x.2)
  exact h

def VoD (s t : ℝ) (x : D) : D := ⟨Vo B M A hM hA hB hs u₀ s t x.1, Vo_smooth B M A hM hA hB hs u₀ s t x⟩

lemma hasDerivAt_Phi {f : ℝ → Fock L} {f' : Fock L} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun r => Phi (f r)) (Phi f') t := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hf
  apply hasDerivAt_iff_tendsto_slope.mpr
  refine (((Phi (L := L)).continuous.tendsto f').comp hs).congr (fun r => ?_)
  simp only [Function.comp_apply, slope_def_module]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
    map_sub]

lemma Vo_hasDerivAt (s t : ℝ) (x : D) :
    HasDerivAt (fun r => Vo B M A hM hA hB hs u₀ s r x.1)
      ((-Complex.I) • Qo (aₜ t) (bₜ t) (Vo B M A hM hA hB hs u₀ s t x.1)) t := by
  have hx : Smooth (Ext006PhysicalVacuum.coefficient ((Phi (L := L)).symm x.1)) := by
    rw [coefficient_symm]; exact x.2
  have h := hasDerivAt_Phi (evolution_smooth_hasDerivAt B M A hM hA hB hs u₀ s t _ hx)
  refine h.congr_deriv ?_
  change Phi ((-Complex.I) • Prop022StrongOperatorR125.strongCoordinates (aₜ t) (bₜ t)
    (rootLift 2 (V s t ((Phi (L := L)).symm x.1)))) = _
  rw [map_smul, Qo, Vo, LinearIsometryEquiv.symm_apply_apply]
  rfl

lemma Vo_continuous (s : ℝ) (x : D) : Continuous (fun r => Vo B M A hM hA hB hs u₀ s r x.1) :=
  continuous_iff_continuousAt.mpr (fun t => (Vo_hasDerivAt B M A hM hA hB hs u₀ s t x).continuousAt)

lemma ρ_tendsto (s t : ℝ) (x : D) :
    Tendsto (fun r => ρ (VoD B M A hM hA hB hs u₀ s r x - VoD B M A hM hA hB hs u₀ s t x))
      (𝓝 t) (𝓝 0) := by
  set y := (Phi (L := L)).symm x.1
  have hy3 : y ∈ momentDomain (L := L) 3 := smooth_mem x 3
  have hc := (evolution_root_continuous B M A hM hA hB hs u₀ 1 s ⟨y, hy3⟩).tendsto t
  have hmem : ∀ r, V s r y ∈ momentDomain (L := L) 1 := fun r =>
    domain_mono (by omega) ((evolution_energy B M A hM hA hB hs u₀ 3 (by omega) s r ⟨y, hy3⟩).1)
  have he : ∀ r, ρ (VoD B M A hM hA hB hs u₀ s r x - VoD B M A hM hA hB hs u₀ s t x) =
      ‖rootLift 1 (V s r y) - rootLift 1 (V s t y)‖ := by
    intro r
    rw [ρ_eq (L := L)]
    change ‖rootLift 1 ((Phi (L := L)).symm (Vo (L := L) B M A hM hA hB hs u₀ s r x.1 -
      Vo (L := L) B M A hM hA hB hs u₀ s t x.1))‖ = _
    rw [Vo, Vo, map_sub, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.symm_apply_apply,
      rootLift_eq 1 _ (Submodule.sub_mem _ (hmem r) (hmem t)), rootLift_eq 1 _ (hmem r),
      rootLift_eq 1 _ (hmem t)]
    congr 1
    exact (momentRoot (L := L) 1).map_sub ⟨_, hmem r⟩ ⟨_, hmem t⟩
  simp only [he]
  have := (hc.sub_const (rootLift 1 (V s t y))).norm
  simpa using this

lemma ρ_VoD_tendsto (s t : ℝ) (x : D) :
    Tendsto (fun r => ρ (VoD B M A hM hA hB hs u₀ s r x)) (𝓝 t)
      (𝓝 (ρ (VoD B M A hM hA hB hs u₀ s t x))) := by
  set y := (Phi (L := L)).symm x.1
  have hy3 : y ∈ momentDomain (L := L) 3 := smooth_mem x 3
  have hc := (evolution_root_continuous B M A hM hA hB hs u₀ 1 s ⟨y, hy3⟩).tendsto t
  have he : ∀ r, ρ (VoD B M A hM hA hB hs u₀ s r x) = ‖rootLift 1 (V s r y)‖ := by
    intro r
    rw [ρ_eq (L := L)]
    change ‖rootLift 1 ((Phi (L := L)).symm (Vo (L := L) B M A hM hA hB hs u₀ s r x.1))‖ = _
    rw [Vo, LinearIsometryEquiv.symm_apply_apply]
  simp only [he]
  exact hc.norm

/-! ### The derivative argument -/

lemma field_tendsto {ι : Type*} {l : Filter ι} {h : ι → H} {h0 : H}
    (hh : Tendsto h l (𝓝 h0)) (v : D) :
    Tendsto (fun i => (field (h i) v).1) l (𝓝 (field h0 v).1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ i, ‖(field (h i) v).1 - (field h0 v).1‖ ≤ 2 * ‖h i - h0‖ * ρ v := fun i => by
    rw [← field_sub_smear]; exact field_ρ _ v
  refine squeeze_zero (fun _ => norm_nonneg _) hb ?_
  have := ((tendsto_iff_norm_sub_tendsto_zero.mp hh).const_mul 2).mul_const (ρ v)
  simpa using this

lemma real_smul_OF (c : ℝ) (v : OF) : c • v = (c : ℂ) • v := RCLike.real_smul_eq_coe_smul (K := ℂ) c v
lemma real_smul_H (c : ℝ) (v : H) : c • v = (c : ℂ) • v := RCLike.real_smul_eq_coe_smul (K := ℂ) c v

theorem k_hasDerivAt (s : ℝ) (h : H) (x y : D) (t : ℝ) :
    HasDerivAt (fun r => ⟪Vo B M A hM hA hB hs u₀ s r y.1,
      (field (gco B M A hA hB hs u₀ s h r) (VoD B M A hM hA hB hs u₀ s r x)).1⟫_ℂ) 0 t := by
  set Y := fun r => Vo B M A hM hA hB hs u₀ s r y.1 with hYdef
  set X := fun r => Vo B M A hM hA hB hs u₀ s r x.1 with hXdef
  set XD := fun r => VoD B M A hM hA hB hs u₀ s r x with hXDdef
  set g := gco B M A hA hB hs u₀ s h with hgdef
  set yt := VoD B M A hM hA hB hs u₀ s t y
  have hY := Vo_hasDerivAt B M A hM hA hB hs u₀ s t y
  have hX := Vo_hasDerivAt B M A hM hA hB hs u₀ s t x
  have hg := gco_hasDerivAt B M A hA hB hs u₀ s h t
  have hYs := hasDerivAt_iff_tendsto_slope.mp hY
  have hXs := hasDerivAt_iff_tendsto_slope.mp hX
  have hgs := hasDerivAt_iff_tendsto_slope.mp hg
  -- the moving field vector is continuous
  have hΦ : Tendsto (fun r => (field (g r) (XD r)).1) (𝓝 t) (𝓝 (field (g t) (XD t)).1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ r, ‖(field (g r) (XD r)).1 - (field (g t) (XD t)).1‖ ≤
        2 * ‖g r - g t‖ * ρ (XD r) + 2 * ‖g t‖ * ρ (XD r - XD t) := by
      intro r
      have he : (field (g r) (XD r)).1 - (field (g t) (XD t)).1 =
          (field (g r - g t) (XD r)).1 + (field (g t) (XD r - XD t)).1 := by
        rw [field_sub_smear, map_sub, Submodule.coe_sub]
        abel
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (field_ρ _ _) (field_ρ _ _))
    refine squeeze_zero (fun _ => norm_nonneg _) hb ?_
    have h1 := ((tendsto_iff_norm_sub_tendsto_zero.mp (hg.continuousAt.tendsto)).const_mul 2).mul
      (ρ_VoD_tendsto B M A hM hA hB hs u₀ s t x)
    have h2 := (ρ_tendsto B M A hM hA hB hs u₀ s t x).const_mul (2 * ‖g t‖)
    simpa using h1.add h2
  rw [hasDerivAt_iff_tendsto_slope]
  have hdec : ∀ r, slope (fun r => ⟪Y r, (field (g r) (XD r)).1⟫_ℂ) t r =
      ⟪slope Y t r, (field (g r) (XD r)).1⟫_ℂ + ⟪(field (slope g t r) yt).1, X r⟫_ℂ +
        ⟪(field (g t) yt).1, slope X t r⟫_ℂ := by
    intro r
    simp only [slope_def_module, real_smul_OF, real_smul_H, Complex.real_smul,
      Ext006WeylScalingR44a.field_real_smul, LinearMap.smul_apply, Submodule.coe_smul,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, field_sub_smear, inner_sub_left,
      inner_sub_right]
    have e1 := Ext006FieldClosureR42a.field_symmetric (g r) yt (XD r)
    have e2 := Ext006FieldClosureR42a.field_symmetric (g t) yt (XD t)
    change _ = _ at e1 e2
    have hYt : Y t = yt.1 := rfl
    have hXr : X r = (XD r).1 := rfl
    have hXt : X t = (XD t).1 := rfl
    rw [hYt, hXr, hXt, e1, e2]
    ring
  refine Tendsto.congr (fun r => (hdec r).symm) ?_
  have hlim : Tendsto (fun r => ⟪slope Y t r, (field (g r) (XD r)).1⟫_ℂ +
      ⟪(field (slope g t r) yt).1, X r⟫_ℂ + ⟪(field (g t) yt).1, slope X t r⟫_ℂ) (𝓝[≠] t)
      (𝓝 (⟪(-Complex.I) • Qo (aₜ t) (bₜ t) (Y t), (field (g t) (XD t)).1⟫_ℂ +
        ⟪(field (LamH (aₜ t) (bₜ t) (g t)) yt).1, X t⟫_ℂ +
        ⟪(field (g t) yt).1, (-Complex.I) • Qo (aₜ t) (bₜ t) (X t)⟫_ℂ)) := by
    refine ((hYs.inner (hΦ.mono_left nhdsWithin_le_nhds)).add
      ((field_tendsto hgs yt).inner
        ((Vo_continuous B M A hM hA hB hs u₀ s x).tendsto t |>.mono_left nhdsWithin_le_nhds))).add
      (tendsto_const_nhds.inner hXs)
  convert hlim using 2
  have hform := form_identity (aₜ t) (numberCoefficient_adjoint B hs _) (bₜ t) (g t) yt (XD t)
  have hsym := Ext006FieldClosureR42a.field_symmetric (LamH (aₜ t) (bₜ t) (g t)) yt (XD t)
  change _ = _ at hsym
  rw [inner_smul_left, inner_smul_right]
  change 0 = (starRingEnd ℂ) (-Complex.I) * ⟪Qo (aₜ t) (bₜ t) yt.1, (field (g t) (XD t)).1⟫_ℂ +
    ⟪(field (LamH (aₜ t) (bₜ t) (g t)) yt).1, (XD t).1⟫_ℂ +
    -Complex.I * ⟪(field (g t) yt).1, Qo (aₜ t) (bₜ t) (XD t).1⟫_ℂ
  rw [← hsym, map_neg, Complex.conj_I, neg_neg]
  linear_combination (-Complex.I) * hform - Complex.I_mul_I * ⟪yt.1,
    (field (LamH (aₜ t) (bₜ t) (g t)) (XD t)).1⟫_ℂ

theorem k_const (s : ℝ) (h : H) (x y : D) (t : ℝ) :
    ⟪Vo B M A hM hA hB hs u₀ s t y.1,
      (field (gco B M A hA hB hs u₀ s h t) (VoD B M A hM hA hB hs u₀ s t x)).1⟫_ℂ =
      ⟪y.1, (field h x).1⟫_ℂ := by
  have he := is_const_of_deriv_eq_zero
    (fun r => (k_hasDerivAt B M A hM hA hB hs u₀ s h x y r).differentiableAt)
    (fun r => (k_hasDerivAt B M A hM hA hB hs u₀ s h x y r).deriv) t s
  rw [he]
  have hV : ∀ z : D, VoD B M A hM hA hB hs u₀ s s z = z := by
    intro z
    apply Subtype.ext
    change Phi (V s s ((Phi (L := L)).symm z.1)) = z.1
    rw [evolution_self, LinearIsometryEquiv.apply_symm_apply]
  have hy : Vo B M A hM hA hB hs u₀ s s y.1 = y.1 := congrArg Subtype.val (hV y)
  simp only [hy, hV x, gco_self]

/-! ### Field covariance and the Weyl implementation -/

lemma Vtil_eq (s t : ℝ) (w : OF) :
    Ext006PhysQuasifree.Vtil (propagator B M A hM hA hB hs u₀ s t) w =
      Vo B M A hM hA hB hs u₀ s t w := rfl

lemma Vo_inner (s t : ℝ) (u v : OF) :
    ⟪Vo B M A hM hA hB hs u₀ s t u, Vo B M A hM hA hB hs u₀ s t v⟫_ℂ = ⟪u, v⟫_ℂ := by
  rw [Vo, Vo, (Phi (L := L)).inner_map_map, LinearIsometry.inner_map_map,
    (Phi (L := L)).symm.inner_map_map]

/-- **Field covariance** of the actual quadratic propagator at J⁻¹ S J. -/
theorem fieldCovariant (s t : ℝ) :
    FieldCovariant (Ext006PhysQuasifree.Vtil (propagator B M A hM hA hB hs u₀ s t))
      (coordinateMap (Sp B M A hA hB hs u₀ t s)) := by
  refine ⟨fun x => ?_, fun h v w hw => ?_⟩
  · rw [Vtil_eq]
    have h := evolution_smooth_iff B M A hM hA hB hs u₀ s t ((Phi (L := L)).symm x)
    rw [coefficient_symm] at h
    exact h.symm
  · rw [Vtil_eq] at hw ⊢
    apply Ext006ClosedFieldGraphsR36a.ket_total
    intro m
    let y : D := VoD B M A hM hA hB hs u₀ t s (ketD m)
    have hy : Vo B M A hM hA hB hs u₀ s t y.1 = (ketD m).1 := by
      change Phi (V s t ((Phi (L := L)).symm (Phi (V t s ((Phi (L := L)).symm (ketD m).1))))) = _
      rw [LinearIsometryEquiv.symm_apply_apply, evolution_comp, evolution_self,
        LinearIsometryEquiv.apply_symm_apply]
    have hw' : VoD B M A hM hA hB hs u₀ s t v = w := Subtype.ext hw.symm
    have hk := k_const B M A hM hA hB hs u₀ s h v y t
    rw [hy, hw', gco_eq] at hk
    rw [hk, ← hy, Vo_inner]

/-- **Covariance of the actual propagator.** The R122 quadratic propagator
V(t,s) = propagator s t is a source-Weyl implementer of J⁻¹ S(t,s) J. -/
theorem propagator_implements (s t : ℝ) :
    Ext006SourceWeylR44a.SourceWeylImplementer (Sp B M A hA hB hs u₀ t s)
      (propagator B M A hM hA hB hs u₀ s t) :=
  sourceWeyl_of_field _ _ (fieldCovariant B M A hM hA hB hs u₀ s t)

end QuantumNLS.Prop022OCovariance

#print axioms QuantumNLS.Prop022OCovariance.propagator_implements
