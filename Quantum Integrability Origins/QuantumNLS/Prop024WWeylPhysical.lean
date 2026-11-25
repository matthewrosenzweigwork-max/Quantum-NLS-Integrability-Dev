import QuantumNLS.Prop024WAffine
import QuantumNLS.Prop024WeylConventionR55
import QuantumNLS.Prop022SmoothDomainR126

/-! PROP-024 affine Weyl action, module 5: the printed Weyl operator on the PHYSICAL Fock space
`Fock L` over `L2T L`, with exact domains.

Frozen inputs (all compared byte-for-byte with their snapshots before use):
* `Prop022OVacuum.printedWeyl v = sourceWeyl ((-I)•v)`, the printed `W(v) = exp(a*(v) - a(v))`;
* `Ext006SourceWeylR44a.sourceWeyl_eq`, `Ext006GlobalCovarianceR43a.physicalExponential_apply`:
  `sourceWeyl f = Φ⁻¹ ∘ unitary (repr f) 1 ∘ Φ`;
* `Prop024WeylConventionR55.physicalWeyl_eq_printedWeyl` (the physical displacement
  `physicalWeyl N u = printedWeyl (√N u)`), quoted below for the scaled vector;
* `Prop022SmoothDomainR126.smooth_iff_moments`: smooth domain `= ⋂ⱼ momentDomain j`.

Headline `weyl_affine_action`: on the common smooth domain `physSmooth L = ⋂ⱼ momentDomain j`,
with `a(f) = annP f`, `a*(f) = creP f` the transports of the frozen `A (repr f)`, `C (repr f)`,

  `W(v)⁻¹ a(f) W(v) = a(f) + ⟨f,v⟩`,    `W(v)⁻¹ a*(f) W(v) = a*(f) + ⟨v,f⟩`

(inner product linear in the second slot), as identities in `End (physSmooth L)`, where `W(v)`
restricts to an automorphism of `physSmooth L` and maps every `momentDomain j` into itself with
the explicit bound of module 3. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal ComplexConjugate
namespace QuantumNLS.Prop024WWeylPhysical
open PhysicalTensor Ext025B3PhysicalSectors Ext006PhysFockCoord
open Ext006KernelHilbertSchmidt (physicalBasis)
open Prop024WCoordinates Prop024WEnergy Prop024WAffine
open Occupation Ext006SmoothOperatorsR34a Ext006BoundedExponentialR43a
open Ext006StrongFieldR41a Ext006QuasifreeWeak Ext006ModeDomainR33a

variable {L : ℝ} [Fact (0 < L)]

/-! ### The physical smooth domain -/

/-- The common smooth domain of the physical Fock space: all polynomial particle-number moments
are finite.  It is the pull-back of the frozen EXT-006 domain `D` under the unitary `Φ`. -/
def physSmooth (L : ℝ) [Fact (0 < L)] : Submodule ℂ (Fock L) :=
  Submodule.comap (Phi (L := L)).toLinearEquiv.toLinearMap Ext006SmoothOperatorsR34a.domain

lemma mem_physSmooth (x : Fock L) :
    x ∈ physSmooth L ↔ Smooth (Phi (L := L) x) := Iff.rfl

/-- The exact identification with the frozen physical moment domains. -/
theorem mem_physSmooth_iff_moments (x : Fock L) :
    x ∈ physSmooth L ↔ ∀ j : ℕ, x ∈ Ext005Moments.momentDomain (L := L) j :=
  Prop022SmoothDomainR126.smooth_iff_moments (L := L) x

/-- The vacuum is smooth. -/
lemma vac_mem_physSmooth : (vac : Fock L) ∈ physSmooth L :=
  Prop022SmoothDomainR126.vacuum_smooth (L := L)

/-- Linear equivalence of the physical smooth domain with the frozen occupation domain `D`. -/
def physToD : physSmooth L ≃ₗ[ℂ] D where
  toFun x := ⟨Phi (L := L) x.1, x.2⟩
  map_add' x y := Subtype.ext (map_add (Phi (L := L)) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (Phi (L := L)) c x.1)
  invFun y := ⟨(Phi (L := L)).symm y.1, by
    change Smooth (Phi (L := L) ((Phi (L := L)).symm y.1))
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

lemma physToD_coe (x : physSmooth L) : (physToD x).1 = Phi (L := L) x.1 := rfl

lemma physToD_symm_coe (y : D) : ((physToD (L := L)).symm y).1 = (Phi (L := L)).symm y.1 := rfl

/-- Transport of endomorphisms of `D` to the physical smooth domain. -/
def transport : Module.End ℂ D ≃ₐ[ℂ] Module.End ℂ (physSmooth L) :=
  ((physToD (L := L)).conjAlgEquiv ℂ).symm

lemma transport_coe (T : Module.End ℂ D) (x : physSmooth L) :
    (transport T x).1 = (Phi (L := L)).symm (T (physToD x)).1 := rfl

lemma Phi_transport (T : Module.End ℂ D) (x : physSmooth L) :
    Phi (L := L) (transport T x).1 = (T (physToD x)).1 := by
  rw [transport_coe, LinearIsometryEquiv.apply_symm_apply]

/-! ### Physical creation and annihilation operators -/

/-- The physical annihilator `a(f)` on the smooth domain: the transport of the frozen
`Ext006SmoothOperatorsR34a.A` at the physical coordinates `repr f`. -/
def annP (f : L2T L) : Module.End ℂ (physSmooth L) :=
  transport (A ((physicalBasis L).repr f))

/-- The physical creator `a*(f)` on the smooth domain. -/
def creP (f : L2T L) : Module.End ℂ (physSmooth L) :=
  transport (C ((physicalBasis L).repr f))

lemma Phi_annP (f : L2T L) (x : physSmooth L) (m : Occ) :
    Phi (L := L) (annP f x).1 m = inner ℂ ((physicalBasis L).repr f) (xvec (Phi (L := L) x.1) m) := by
  rw [annP, Phi_transport]
  rfl

lemma Phi_creP (f : L2T L) (x : physSmooth L) (m : Occ) :
    Phi (L := L) (creP f x).1 m =
      ∑ a ∈ m.support, ((physicalBasis L).repr f) a * creCoeff a (Phi (L := L) x.1) m := by
  rw [creP, Phi_transport]
  rfl

/-- The mode annihilator is the frozen physical mode operator: its `m`-th coordinate is
`√(m_a+1) · coefficient x (m + e_a)`, i.e. `⟨ket m, a_a x⟩ = ⟨a_a^* ket m, x⟩`. -/
theorem annP_mode (a : ℤ) (x : physSmooth L) (m : Occ) :
    Phi (L := L) (annP (physicalBasis L a) x).1 m =
      (Real.sqrt ((m a : ℝ) + 1) : ℂ) * Ext006PhysicalVacuum.coefficient x.1 (m + e a) := by
  rw [Phi_annP, HilbertBasis.repr_self]
  rw [show inner ℂ (lp.single 2 a (1 : ℂ)) (xvec (Phi (L := L) x.1) m) =
      annC (lp.single 2 a (1 : ℂ)) m (Phi (L := L) x.1) from rfl, annC_single]
  rfl

theorem annP_mode_inner (a : ℤ) (x : physSmooth L) (m : Occ) :
    inner ℂ (physCore (Occupation.Cre a (Occupation.ket m))) x.1 =
      Phi (L := L) (annP (physicalBasis L a) x).1 m := by
  rw [inner_physCore_Cre, annP_mode]

/-! ### The printed Weyl operator and its restriction -/

/-- The occupation-coordinate smearing vector of the printed Weyl operator. -/
def weylVec (v : L2T L) : Ext006BogoliubovAlg.H := (physicalBasis L).repr ((-Complex.I) • v)

/-- The printed Weyl operator in occupation coordinates. -/
lemma printedWeyl_eq_unitary (v : L2T L) (x : Fock L) :
    Prop022OVacuum.printedWeyl v x =
      (Phi (L := L)).symm (unitary (weylVec v) 1 (Phi (L := L) x)) := by
  rw [Prop022OVacuum.printedWeyl, Ext006SourceWeylR44a.sourceWeyl_eq,
    Ext006GlobalCovarianceR43a.physicalExponential_apply]
  rfl

lemma weylVec_neg (v : L2T L) :
    weylVec (-v) = (((-1 : ℝ) : ℂ)) • weylVec v := by
  unfold weylVec
  rw [smul_neg, map_neg]
  simp

lemma norm_weylVec (v : L2T L) : ‖weylVec v‖ = ‖v‖ := by
  unfold weylVec
  rw [LinearIsometryEquiv.norm_map, norm_smul]
  simp

/-- `W(-v) W(v) = 1` on the whole physical Fock space. -/
theorem printedWeyl_neg_apply (v : L2T L) (x : Fock L) :
    Prop022OVacuum.printedWeyl (-v) (Prop022OVacuum.printedWeyl v x) = x := by
  rw [printedWeyl_eq_unitary (-v), printedWeyl_eq_unitary v, LinearIsometryEquiv.apply_symm_apply,
    weylVec_neg, Ext006WeylScalingR44a.unitary_real_smul,
    Ext006SeriesIdentificationR43a.unitary_add, neg_add_cancel,
    Ext006SeriesIdentificationR43a.unitary_zero, LinearIsometryEquiv.symm_apply_apply]

/-- The adjoint (inverse) of the printed Weyl operator is `W(-v)`. -/
theorem printedWeyl_symm (v : L2T L) :
    (Prop022OVacuum.printedWeyl v).symm = Prop022OVacuum.printedWeyl (-v) := by
  refine LinearIsometryEquiv.ext fun y => ?_
  apply (Prop022OVacuum.printedWeyl v).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have := printedWeyl_neg_apply (-v) y
  rw [neg_neg] at this
  exact this.symm

/-- `W(v)` restricted to the physical smooth domain. -/
def printedWeylD (v : L2T L) : Module.End ℂ (physSmooth L) :=
  transport (Ud (weylVec v) 1)

lemma printedWeylD_coe (v : L2T L) (x : physSmooth L) :
    (printedWeylD v x).1 = Prop022OVacuum.printedWeyl v x.1 := by
  rw [printedWeyl_eq_unitary]
  rfl

lemma Phi_printedWeylD (v : L2T L) (x : physSmooth L) :
    Phi (L := L) (printedWeylD v x).1 = unitary (weylVec v) 1 (Phi (L := L) x.1) := by
  rw [printedWeylD, Phi_transport]
  rfl

/-- `W(-v) = W(v)⁻¹` on the smooth domain. -/
lemma printedWeylD_neg_mul (v : L2T L) : printedWeylD (-v) * printedWeylD v = 1 := by
  have h1 : Ud (weylVec (-v)) 1 = Ud (weylVec v) (-1) := by
    rw [weylVec_neg]
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact Ext006WeylScalingR44a.unitary_real_smul (-1) _ x.1
  unfold printedWeylD
  rw [← map_mul, h1, Ud_neg_mul, map_one]

lemma printedWeylD_mul_neg (v : L2T L) : printedWeylD v * printedWeylD (-v) = 1 := by
  simpa using printedWeylD_neg_mul (-v)

/-- `W(v)` as a linear automorphism of the smooth domain. -/
def printedWeylE (v : L2T L) : physSmooth L ≃ₗ[ℂ] physSmooth L :=
  LinearEquiv.ofLinearMap (printedWeylD v) (printedWeylD (-v)) (printedWeylD_mul_neg v)
    (printedWeylD_neg_mul v)

lemma printedWeylE_apply (v : L2T L) (x : physSmooth L) :
    printedWeylE v x = printedWeylD v x := rfl

lemma printedWeylE_symm_apply (v : L2T L) (x : physSmooth L) :
    (printedWeylE v).symm x = printedWeylD (-v) x := rfl

/-- The conjugation `T ↦ W(v)⁻¹ T W(v)` as an algebra automorphism of `End (physSmooth L)`. -/
def weylConj (v : L2T L) : Module.End ℂ (physSmooth L) ≃ₐ[ℂ] Module.End ℂ (physSmooth L) :=
  ((printedWeylE v).symm).conjAlgEquiv ℂ

lemma weylConj_apply (v : L2T L) (T : Module.End ℂ (physSmooth L)) (x : physSmooth L) :
    weylConj v T x = printedWeylD (-v) (T (printedWeylD v x)) := rfl

/-! ### The inner-product constants -/

lemma coeff_ann (v f : L2T L) :
    Complex.I * (((1 : ℝ)) : ℂ) * inner ℂ ((physicalBasis L).repr f) (weylVec v) = inner ℂ f v := by
  unfold weylVec
  rw [LinearIsometryEquiv.inner_map_map, inner_smul_right]
  simp only [Complex.ofReal_one, mul_one]
  rw [← mul_assoc, show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_mul]

lemma coeff_cre (v f : L2T L) :
    Complex.I * (((1 : ℝ)) : ℂ) * (-(inner ℂ (weylVec v) ((physicalBasis L).repr f))) =
      inner ℂ v f := by
  unfold weylVec
  rw [LinearIsometryEquiv.inner_map_map, inner_smul_left]
  simp only [Complex.ofReal_one, mul_one, map_neg, Complex.conj_I]
  rw [neg_mul, neg_neg, ← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

/-! ### Headline: the affine Weyl action with exact domains -/

/-- **`weyl_affine_action`.**  On the physical smooth domain `⋂ⱼ momentDomain j`, with the
source inner product linear in the second slot:
`a(f) W(v) = W(v) (a(f) + ⟨f,v⟩)` and `a*(f) W(v) = W(v) (a*(f) + ⟨v,f⟩)` in `End (physSmooth L)`;
equivalently `W(v)⁻¹ a(f) W(v) = a(f) + ⟨f,v⟩` and `W(v)⁻¹ a*(f) W(v) = a*(f) + ⟨v,f⟩`. -/
theorem weyl_affine_action (v f : L2T L) :
    (annP f * printedWeylD v =
        printedWeylD v * (annP f + (inner ℂ f v) • (1 : Module.End ℂ (physSmooth L)))) ∧
    (creP f * printedWeylD v =
        printedWeylD v * (creP f + (inner ℂ v f) • (1 : Module.End ℂ (physSmooth L)))) ∧
    (weylConj v (annP f) = annP f + (inner ℂ f v) • (1 : Module.End ℂ (physSmooth L))) ∧
    (weylConj v (creP f) = creP f + (inner ℂ v f) • (1 : Module.End ℂ (physSmooth L))) := by
  have hA := A_Ud ((physicalBasis L).repr f) (weylVec v) 1
  have hC := C_Ud ((physicalBasis L).repr f) (weylVec v) 1
  rw [coeff_ann] at hA
  rw [coeff_cre] at hC
  have hA' := congrArg (transport (L := L)) hA
  have hC' := congrArg (transport (L := L)) hC
  simp only [map_mul, map_add, map_smul, map_one] at hA' hC'
  have e1 : annP f * printedWeylD v =
      printedWeylD v * (annP f + (inner ℂ f v) • (1 : Module.End ℂ (physSmooth L))) := hA'
  have e2 : creP f * printedWeylD v =
      printedWeylD v * (creP f + (inner ℂ v f) • (1 : Module.End ℂ (physSmooth L))) := hC'
  refine ⟨e1, e2, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [weylConj_apply]
    have := congrArg (fun T : Module.End ℂ (physSmooth L) => printedWeylD (-v) (T x)) e1
    simp only [Module.End.mul_apply] at this
    rw [this, ← Module.End.mul_apply (printedWeylD (-v)), printedWeylD_neg_mul]
    simp
  · refine LinearMap.ext fun x => ?_
    rw [weylConj_apply]
    have := congrArg (fun T : Module.End ℂ (physSmooth L) => printedWeylD (-v) (T x)) e2
    simp only [Module.End.mul_apply] at this
    rw [this, ← Module.End.mul_apply (printedWeylD (-v)), printedWeylD_neg_mul]
    simp

/-- Pointwise form of the annihilation identity on every smooth vector:
`W(v)* a(f) W(v) x = a(f) x + ⟨f,v⟩ x`, with `W(v)* = W(v)⁻¹ = W(-v)`. -/
theorem weyl_conj_ann_apply (v f : L2T L) (x : physSmooth L) :
    (Prop022OVacuum.printedWeyl v).symm ((annP f (printedWeylD v x)).1) =
      (annP f x).1 + (inner ℂ f v) • x.1 := by
  have h := LinearMap.congr_fun (weyl_affine_action v f).2.2.1 x
  rw [weylConj_apply] at h
  have h2 := congrArg Subtype.val h
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.coe_add, Submodule.coe_smul] at h2
  rw [← h2, printedWeylD_coe, printedWeyl_symm]

/-- Pointwise form of the creation identity on every smooth vector. -/
theorem weyl_conj_cre_apply (v f : L2T L) (x : physSmooth L) :
    (Prop022OVacuum.printedWeyl v).symm ((creP f (printedWeylD v x)).1) =
      (creP f x).1 + (inner ℂ v f) • x.1 := by
  have h := LinearMap.congr_fun (weyl_affine_action v f).2.2.2 x
  rw [weylConj_apply] at h
  have h2 := congrArg Subtype.val h
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.coe_add, Submodule.coe_smul] at h2
  rw [← h2, printedWeylD_coe, printedWeyl_symm]

/-! ### Exact domains: the displacement preserves each number-moment domain -/

lemma summable_iff_En_ne_top (p : ℕ) (y : Occupation.Occ → ℂ) :
    Summable (fun m => wt p m * ‖y m‖^2) ↔ En p y ≠ ⊤ := by
  constructor
  · intro hs
    have := ENNReal.ofReal_tsum_of_nonneg
      (f := fun m => wt p m * ‖y m‖^2) (fun m => mul_nonneg (wt_nonneg p m) (sq_nonneg _)) hs
    unfold En
    rw [← this]
    exact ENNReal.ofReal_ne_top
  · intro h
    have hs := ENNReal.summable_toReal h
    refine hs.congr fun m => ?_
    exact ENNReal.toReal_ofReal (mul_nonneg (wt_nonneg p m) (sq_nonneg _))

lemma mem_momentDomain_iff_En (j : ℕ) (x : Fock L) :
    x ∈ Ext005Moments.momentDomain (L := L) j ↔ En j (Phi (L := L) x) ≠ ⊤ := by
  rw [← Prop022SmoothDomainR126.coefficient_moment_iff]
  exact summable_iff_En_ne_top j (Phi (L := L) x)

/-- The quantitative energy bound for the printed Weyl operator, in physical form. -/
theorem weyl_energy_bound (v : L2T L) (j : ℕ) (x : Fock L) :
    En j (Phi (L := L) (Prop022OVacuum.printedWeyl v x)) ≤
      Cn (ENNReal.ofReal (1^2 * ‖weylVec v‖^2)) j * En j (Phi (L := L) x) := by
  rw [printedWeyl_eq_unitary, LinearIsometryEquiv.apply_symm_apply]
  have := energy_bound (weylVec v) 1 j (Phi (L := L) x)
  simpa using this

/-- **Exact domain statement.** `W(v)` maps each moment domain `momentDomain j` into itself. -/
theorem weyl_mem_momentDomain (v : L2T L) (j : ℕ) (x : Fock L)
    (hx : x ∈ Ext005Moments.momentDomain (L := L) j) :
    Prop022OVacuum.printedWeyl v x ∈ Ext005Moments.momentDomain (L := L) j := by
  rw [mem_momentDomain_iff_En] at hx ⊢
  refine ne_top_of_le_ne_top ?_ (weyl_energy_bound v j x)
  exact ENNReal.mul_ne_top (Cn_ne_top ENNReal.ofReal_ne_top j) hx

/-- ... and `W(v)` is a bijection of each moment domain (inverse `W(-v)`). -/
theorem weyl_mem_momentDomain_iff (v : L2T L) (j : ℕ) (x : Fock L) :
    Prop022OVacuum.printedWeyl v x ∈ Ext005Moments.momentDomain (L := L) j ↔
      x ∈ Ext005Moments.momentDomain (L := L) j := by
  refine ⟨fun h => ?_, weyl_mem_momentDomain v j x⟩
  have := weyl_mem_momentDomain (-v) j _ h
  rwa [printedWeyl_neg_apply] at this

/-- `W(v)` maps the smooth domain onto itself. -/
theorem weyl_mem_physSmooth_iff (v : L2T L) (x : Fock L) :
    Prop022OVacuum.printedWeyl v x ∈ physSmooth L ↔ x ∈ physSmooth L := by
  rw [mem_physSmooth_iff_moments, mem_physSmooth_iff_moments]
  exact forall_congr' fun j => weyl_mem_momentDomain_iff v j x

/-- The displaced vacuum (a coherent state) lies in every number-moment domain. -/
theorem weyl_vac_mem_physSmooth (v : L2T L) :
    Prop022OVacuum.printedWeyl v (vac : Fock L) ∈ physSmooth L :=
  (weyl_mem_physSmooth_iff v _).mpr vac_mem_physSmooth

/-- The physical displacement `physicalWeyl N u = W(√N u)` of the frozen R54/R55 convention
theorem is covered by the same domain statement. -/
theorem physicalWeyl_mem_physSmooth_iff (N : ℕ) (u : L2T L) (x : Fock L) :
    Prop024ContractionsR54.physicalWeyl N u x ∈ physSmooth L ↔ x ∈ physSmooth L := by
  rw [Prop024WeylConventionR55.physicalWeyl_eq_printedWeyl]
  exact weyl_mem_physSmooth_iff _ x

end QuantumNLS.Prop024WWeylPhysical

#print axioms QuantumNLS.Prop024WWeylPhysical.weyl_affine_action
#print axioms QuantumNLS.Prop024WWeylPhysical.weyl_conj_ann_apply
#print axioms QuantumNLS.Prop024WWeylPhysical.weyl_conj_cre_apply
#print axioms QuantumNLS.Prop024WWeylPhysical.weyl_energy_bound
#print axioms QuantumNLS.Prop024WWeylPhysical.weyl_mem_momentDomain
#print axioms QuantumNLS.Prop024WWeylPhysical.weyl_mem_momentDomain_iff
#print axioms QuantumNLS.Prop024WWeylPhysical.weyl_mem_physSmooth_iff
#print axioms QuantumNLS.Prop024WWeylPhysical.weyl_vac_mem_physSmooth
#print axioms QuantumNLS.Prop024WWeylPhysical.physicalWeyl_mem_physSmooth_iff
#print axioms QuantumNLS.Prop024WWeylPhysical.printedWeyl_symm
#print axioms QuantumNLS.Prop024WWeylPhysical.annP_mode
#print axioms QuantumNLS.Prop024WWeylPhysical.annP_mode_inner

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WWeylPhysical." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WWeylPhysical." then
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
  Lean.logInfo m!"Prop024WWeylPhysical aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
