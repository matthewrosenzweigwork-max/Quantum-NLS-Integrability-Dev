import NlsGge.Sobolev38.MixedLpProduct38
import NlsGge.Sobolev38.SobolevCarrier38
import NlsGge.Hierarchy.RiccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second
import NlsGge.Hierarchy.RiccatiSmoothClassicalDerivativePhysicalL2AgreementRecovery30Fifth
import NlsGge.Hierarchy.RiccatiActualMonomialFiniteSlotsRecovery31Fourth
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar
import NlsGge.Hierarchy.RiccatiQ4IteratedDerivStarPrerequisiteThird
import Mathlib.Tactic

/-! Batch 38, E06.05: one real continuous multilinear form on `H^s` for every
occurrence of a normalized hierarchy monomial, realizing the source monomial's
period integral on smooth fields.

Source: paper/v2.tex line 624 (`B:lem:local` proof): "For `j ≤ m`, at most two
factors can have derivative order `m-1`. Put these factors in `L²`. Every
factor of derivative order at most `m-2` belongs to `H¹` and therefore to
`L^∞`. If fewer than two factors have the highest order, the same estimate
uses the unit volume of the torus. This gives a continuous multilinear
functional of `H^{m-1}` arguments for each monomial."

Here `s` is the Sobolev order `m-1`. Lower occurrences use the accepted
continuous-representative CLM composed with `toLp ∞`; top occurrences use the
accepted `L²` derivative CLM. The true Boolean jet component is conjugated. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Sobolev38
open MeasureTheory
open scoped ENNReal ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-! ### Real-linear optional conjugation (salvaged from the owner candidate) -/

/-- Optional complex conjugation as a real continuous linear map. -/
def conjugateIf38 (eps : Bool) : ℂ →L[ℝ] ℂ := by
  let L : ℂ →ₗ[ℝ] ℂ := {
    toFun := fun z => if eps then star z else z
    map_add' := by intro z w; cases eps <;> simp
    map_smul' := by intro r z; cases eps <;> simp
  }
  exact L.mkContinuous 1 (by intro z; cases eps <;> simp [L])

theorem conjugateIf38_apply (eps : Bool) (z : ℂ) :
    conjugateIf38 eps z = if eps then star z else z := rfl

def conjugateIfLp38 (eps : Bool) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℂ p spatialMeasure →L[ℝ] Lp ℂ p spatialMeasure :=
  (conjugateIf38 eps).compLpL p spatialMeasure

theorem conjugateIfLp38_ae (eps : Bool) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp ℂ p spatialMeasure) :
    (conjugateIfLp38 eps p f : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      (fun x => conjugateIf38 eps (f x)) :=
  (conjugateIf38 eps).coeFn_compLpL f

/-! ### Slot maps -/

/-- Select the top (`L²`) or lower (`L^∞`) realization by the slot flag. -/
def slotMapOfBool38 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Bool) (top : E →L[ℝ] Lp ℂ 2 spatialMeasure)
    (low : E →L[ℝ] Lp ℂ ∞ spatialMeasure) :
    E →L[ℝ] Lp ℂ (slotExponent38 b) spatialMeasure :=
  match b with
  | true => top
  | false => low

/-- Lower jet realization in `L^∞`: the accepted continuous representative of
the `k`-th derivative (zero only in the excluded case `k+1 > s`, which is never
used for a lower slot), conjugated iff the Boolean component is true. -/
def lowerJetLinfty38 (s : ℕ) (v : Jet) :
    SobolevCarrier38 (s : ℝ) →L[ℝ] Lp ℂ ∞ spatialMeasure :=
  if h : v.2 + 1 ≤ s then
    (conjugateIfLp38 v.1 ∞).comp
      ((ContinuousMap.toLp ∞ spatialMeasure ℝ (E := ℂ)).comp
        (liftCLM38
          (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth s v.2 h)))
  else 0

/-- Top jet realization in `L²`: the accepted order-`s` derivative class,
conjugated iff the Boolean component is true. -/
def topJetL2_38 (s : ℕ) (v : Jet) :
    SobolevCarrier38 (s : ℝ) →L[ℝ] Lp ℂ 2 spatialMeasure :=
  (conjugateIfLp38 v.1 2).comp
    (liftCLM38 (riccatiSobolevIteratedDerivativeL2CLMRecovery30First s s le_rfl))

/-- The slot index of a monomial: `Fin` enumeration of its occurrence finset. -/
abbrev monomialSlotCount38 (q : Jet →₀ ℕ) : ℕ :=
  (riccatiActualMonomialSlotFinsetRecovery31Fourth q).card

def monomialSlotEquiv38 (q : Jet →₀ ℕ) :
    Fin (monomialSlotCount38 q) ≃ {σ // σ ∈ riccatiActualMonomialSlotFinsetRecovery31Fourth q} :=
  (riccatiActualMonomialSlotFinsetRecovery31Fourth q).equivFin.symm

/-- The jet carried by slot `i`. -/
def monomialSlotJet38 (q : Jet →₀ ℕ) (i : Fin (monomialSlotCount38 q)) : Jet :=
  (monomialSlotEquiv38 q i).1.1

/-- The top flag of slot `i` at Sobolev order `s`. -/
def monomialSlotTop38 (s : ℕ) (q : Jet →₀ ℕ) (i : Fin (monomialSlotCount38 q)) : Bool :=
  decide ((monomialSlotJet38 q i).2 = s)

def monomialSlotMap38 (s : ℕ) (q : Jet →₀ ℕ) (i : Fin (monomialSlotCount38 q)) :
    SobolevCarrier38 (s : ℝ) →L[ℝ]
      Lp ℂ (slotExponent38 (monomialSlotTop38 s q i)) spatialMeasure :=
  slotMapOfBool38 (monomialSlotTop38 s q i)
    (topJetL2_38 s (monomialSlotJet38 q i)) (lowerJetLinfty38 s (monomialSlotJet38 q i))

theorem monomialSlot_highCount38 (s : ℕ) (q : Jet →₀ ℕ) :
    highCount38 (monomialSlotTop38 s q) =
      ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
        (fun σ => σ.1.2 = s)).card := by
  classical
  rw [highCount_eq_sum38, Finset.card_filter,
    ← Finset.sum_coe_sort (riccatiActualMonomialSlotFinsetRecovery31Fourth q),
    ← Equiv.sum_comp (monomialSlotEquiv38 q)]
  simp only [monomialSlotTop38, monomialSlotJet38]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (↑(monomialSlotEquiv38 q i) :
      Σ v : Jet, Fin (q v)).1.2 = s <;> simp [h]

/-- Real part after multiplication by a complex coefficient. -/
def realCoefficient38 (c : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ) c)

theorem realCoefficient38_apply (c z : ℂ) : realCoefficient38 c z = (c * z).re := rfl

/-- At most two top occurrences, in the form required by the generic product. -/
theorem monomialSlot_highCount_le_two38 (s : ℕ) (q : Jet →₀ ℕ)
    (htop : ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = s)).card ≤ 2) :
    highCount38 (monomialSlotTop38 s q) ≤ 2 := by
  rw [monomialSlot_highCount38]
  exact htop

/-- E06.05 monomial realization: one real continuous multilinear form with one
`H^s` input per occurrence of the monomial `q` (repeated factors kept), equal
to `Re (c ∫ ∏ slots)` with lower slots in `L^∞` and the at most two top slots
(order `s`) in `L²`. -/
def riccatiMonomialSobolevCMM38 (s : ℕ) (q : Jet →₀ ℕ) (c : ℤ)
    (htop : ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = s)).card ≤ 2) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin (monomialSlotCount38 q) => SobolevCarrier38 (s : ℝ)) ℝ :=
  postcomposeCML38 (realCoefficient38 (c : ℂ))
    (postcomposeCML38
      (integrateProductLp38 (highCount38 (monomialSlotTop38 s q))
        (monomialSlot_highCount_le_two38 s q htop))
      (mixedProduct38 (E := SobolevCarrier38 (s : ℝ)) (monomialSlotTop38 s q)
        (monomialSlot_highCount_le_two38 s q htop) (monomialSlotMap38 s q)))

/-- The slot count is the field degree of the monomial. -/
theorem monomialSlotCount38_eq_degree (q : Jet →₀ ℕ) :
    monomialSlotCount38 q = q.degree :=
  riccatiActualMonomialSlotFinset_cardRecovery31Fourth q

/-- General value formula: the form is `Re (c ∫ ∏_i slot_i)` over the actual
probability measure, with the product of representatives integrable. -/
theorem riccatiMonomialSobolevCMM38_apply (s : ℕ) (q : Jet →₀ ℕ) (c : ℤ)
    (htop : ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = s)).card ≤ 2)
    (y : Fin (monomialSlotCount38 q) → SobolevCarrier38 (s : ℝ)) :
    riccatiMonomialSobolevCMM38 s q c htop y =
      ((c : ℂ) * ∫ t, ∏ i, (monomialSlotMap38 s q i (y i) : PhysicalCircle → ℂ) t
        ∂spatialMeasure).re := by
  change ((c : ℂ) * integrateProductLp38 _ _ (mixedProduct38 (E := SobolevCarrier38 (s : ℝ))
    (monomialSlotTop38 s q) (monomialSlot_highCount_le_two38 s q htop)
    (monomialSlotMap38 s q) y)).re = _
  rw [integrateProductLp_eq_integral38]
  rw [integral_congr_ae (mixedProduct_ae38 _ (monomialSlotTop38 s q)
    (monomialSlot_highCount_le_two38 s q htop) (monomialSlotMap38 s q) y)]

/-- Polynomial bound of the diagonal: `|P(x)| ≤ ‖P‖ ‖x‖^{deg q}`. -/
theorem riccatiMonomialSobolevCMM38_diag_bound (s : ℕ) (q : Jet →₀ ℕ) (c : ℤ)
    (htop : ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = s)).card ≤ 2) (x : SobolevCarrier38 (s : ℝ)) :
    |riccatiMonomialSobolevCMM38 s q c htop (fun _ => x)| ≤
      ‖riccatiMonomialSobolevCMM38 s q c htop‖ * ‖x‖ ^ q.degree := by
  have h := (riccatiMonomialSobolevCMM38 s q c htop).le_opNorm (fun _ => x)
  rw [Real.norm_eq_abs, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rwa [← monomialSlotCount38_eq_degree]

/-! ### Smooth-field identity (E06.05 realization on smooth witnesses) -/

theorem slotMapOfBool38_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Bool) (top : E →L[ℝ] Lp ℂ 2 spatialMeasure)
    (low : E →L[ℝ] Lp ℂ ∞ spatialMeasure) (y : E) (F : PhysicalCircle → ℂ)
    (htop : b = true → (top y : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] F)
    (hlow : b = false → (low y : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] F) :
    (slotMapOfBool38 b top low y : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] F := by
  cases b
  · exact hlow rfl
  · exact htop rfl

/-- The periodic lift agrees with the real-line function on `[0,1]`. -/
theorem liftIoc_unit_eq38 (f : ℝ → ℂ) (hper : Function.Periodic f 1) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    AddCircle.liftIoc 1 0 f (r : PhysicalCircle) = f r := by
  rcases eq_or_lt_of_le hr.1 with h0 | hpos
  · subst h0
    have hcoe : ((0 : ℝ) : PhysicalCircle) = ((1 : ℝ) : PhysicalCircle) := by
      rw [AddCircle.coe_period]
      simp
    rw [hcoe, AddCircle.liftIoc_coe_apply (by norm_num : (1 : ℝ) ∈ Set.Ioc 0 (0 + 1))]
    simpa using hper 0
  · exact AddCircle.liftIoc_coe_apply ⟨hpos, by simpa using hr.2⟩

/-- Lower jets of the Sobolev element of a smooth field are the classical
derivatives (pointwise, as continuous functions on the circle). -/
theorem lowerJetCLM_smooth38 (s k : ℕ) (h : k + 1 ≤ s) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) (x : SobolevHilbert (s : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight (s : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth s k h x :
        PhysicalCircle → ℂ) =
      AddCircle.liftIoc 1 0 (iteratedDeriv k u) := by
  obtain ⟨x', hx', hj⟩ := riccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second s u hu hper
  have hxx : x = x' := by
    apply Subtype.ext
    funext n
    exact (hsource n).trans (hx' n).symm
  subst hxx
  have hk : riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth s k h x =
      riccatiSmoothPeriodicLiftContinuousMapRecovery30First (iteratedDeriv k u)
        (by
          rw [iteratedDeriv_eq_iterate]
          exact (ContDiff.iterate_deriv k hu).continuous)
        (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper k) := by
    simpa [riccatiSobolevJetContinuousRepresentativeRecovery30Eighth] using hj (false, k) h
  rw [hk]
  rfl

theorem riccatiJetFunction_eq_conjugateIf38 (u : ℝ → ℂ) (v : Jet) (r : ℝ) :
    riccatiJetFunction u v r = conjugateIf38 v.1 (iteratedDeriv v.2 u r) := by
  rcases v with ⟨b, k⟩
  cases b
  · simp [riccatiJetFunction, conjugateIf38_apply]
  · have h := congrFun (iteratedDeriv_star_prerequisite u k) r
    simpa [riccatiJetFunction, conjugateIf38_apply] using h

theorem monomialSlotJet38_mem (q : Jet →₀ ℕ) (i : Fin (monomialSlotCount38 q)) :
    monomialSlotJet38 q i ∈ q.support := by
  have h := (monomialSlotEquiv38 q i).2
  unfold riccatiActualMonomialSlotFinsetRecovery31Fourth at h
  exact (Finset.mem_sigma.1 h).1

/-- Each slot of the Sobolev element of a smooth field is a.e. the classical
(conjugated) derivative. -/
theorem monomialSlotMap38_smooth_ae (s : ℕ) (q : Jet →₀ ℕ)
    (hord : ∀ v ∈ q.support, v.2 ≤ s) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (x : SobolevHilbert (s : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight (s : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n)
    (i : Fin (monomialSlotCount38 q)) :
    (monomialSlotMap38 s q i (toCarrier38 (s : ℝ) x) : PhysicalCircle → ℂ)
      =ᵐ[spatialMeasure] fun t => conjugateIf38 (monomialSlotJet38 q i).1
        (AddCircle.liftIoc 1 0 (iteratedDeriv (monomialSlotJet38 q i).2 u) t) := by
  set v := monomialSlotJet38 q i with hvdef
  have hvs : v.2 ≤ s := hord v (monomialSlotJet38_mem q i)
  unfold monomialSlotMap38
  apply slotMapOfBool38_ae
  · intro hb
    have hv2 : v.2 = s := by
      simpa [monomialSlotTop38, ← hvdef] using hb
    have hD := riccatiSobolevIteratedDerivativeL2_agrees_classicalRecovery30First
      s s le_rfl x u hu hper hsource
    change (conjugateIfLp38 v.1 2
        (riccatiSobolevIteratedDerivativeL2CLMRecovery30First s s le_rfl x) :
          PhysicalCircle → ℂ) =ᵐ[spatialMeasure] _
    rw [hD, hv2]
    filter_upwards [conjugateIfLp38_ae v.1 2 _, ContinuousMap.coeFn_toLp
      (p := 2) (𝕜 := ℂ) spatialMeasure
      (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (iteratedDeriv s u)
        (by
          rw [iteratedDeriv_eq_iterate]
          exact (ContDiff.iterate_deriv s hu).continuous)
        (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper s))]
      with t ht hl
    rw [ht, hl]
    rfl
  · intro hb
    have hv2 : v.2 ≠ s := by
      simpa [monomialSlotTop38, ← hvdef] using hb
    have hlow : v.2 + 1 ≤ s := by omega
    have hL := lowerJetCLM_smooth38 s v.2 hlow u hu hper x hsource
    change (lowerJetLinfty38 s v (toCarrier38 (s : ℝ) x) : PhysicalCircle → ℂ)
      =ᵐ[spatialMeasure] _
    simp only [lowerJetLinfty38, hlow, dite_true]
    change (conjugateIfLp38 v.1 ∞
        (ContinuousMap.toLp ∞ spatialMeasure ℝ (E := ℂ)
          (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth s v.2 hlow x)) :
          PhysicalCircle → ℂ) =ᵐ[spatialMeasure] _
    filter_upwards [conjugateIfLp38_ae v.1 ∞ _, ContinuousMap.coeFn_toLp
      (p := ∞) (𝕜 := ℝ) spatialMeasure
      (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth s v.2 hlow x)]
      with t ht hl
    rw [ht, hl, hL]

/-- E06.05 smooth identity: on the Sobolev element of a smooth period-one
field, the diagonal of the monomial form is the real part of the source
monomial's period integral (integer coefficient included). -/
theorem riccatiMonomialSobolevCMM38_diag_smooth (s : ℕ) (q : Jet →₀ ℕ) (c : ℤ)
    (htop : ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = s)).card ≤ 2)
    (hord : ∀ v ∈ q.support, v.2 ≤ s) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (x : SobolevHilbert (s : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight (s : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    riccatiMonomialSobolevCMM38 s q c htop (fun _ => toCarrier38 (s : ℝ) x) =
      (∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t (MvPolynomial.monomial q c)).re := by
  classical
  set G : Fin (monomialSlotCount38 q) → PhysicalCircle → ℂ := fun i t =>
    conjugateIf38 (monomialSlotJet38 q i).1
      (AddCircle.liftIoc 1 0 (iteratedDeriv (monomialSlotJet38 q i).2 u) t) with hG
  have hall : ∀ᵐ t ∂spatialMeasure, ∀ i,
      (monomialSlotMap38 s q i (toCarrier38 (s : ℝ) x) : PhysicalCircle → ℂ) t = G i t :=
    ae_all_iff.2 (fun i => monomialSlotMap38_smooth_ae s q hord u hu hper x hsource i)
  have hint : (∫ t, ∏ i, (monomialSlotMap38 s q i (toCarrier38 (s : ℝ) x) :
      PhysicalCircle → ℂ) t ∂spatialMeasure) = ∫ t, ∏ i, G i t ∂spatialMeasure := by
    apply integral_congr_ae
    filter_upwards [hall] with t ht
    exact Finset.prod_congr rfl (fun i _ => ht i)
  have hprod : ∀ r ∈ Set.uIcc (0 : ℝ) 1,
      (∏ i, G i (r : PhysicalCircle)) =
        q.prod (fun v n => riccatiJetFunction u v r ^ n) := by
    intro r hr
    rw [Set.uIcc_of_le zero_le_one] at hr
    have hpt : ∀ i, G i (r : PhysicalCircle) = riccatiJetFunction u (monomialSlotJet38 q i) r := by
      intro i
      rw [hG, riccatiJetFunction_eq_conjugateIf38]
      simp only
      rw [liftIoc_unit_eq38 _
        (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper _) hr]
    simp_rw [hpt]
    rw [← riccatiActualMonomialSlotFinset_prodRecovery31Fourth,
      ← Finset.prod_coe_sort (riccatiActualMonomialSlotFinsetRecovery31Fourth q),
      ← Equiv.prod_comp (monomialSlotEquiv38 q)]
    rfl
  rw [riccatiMonomialSobolevCMM38_apply, hint,
    ← unitIntervalIntegral_lift_eq_spatialHaar (fun t => ∏ i, G i t),
    intervalIntegral.integral_congr hprod]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  simp [riccatiJetEvaluation, polynomialEvaluation]

end NlsGge.HierarchyRiccati.Core

end
