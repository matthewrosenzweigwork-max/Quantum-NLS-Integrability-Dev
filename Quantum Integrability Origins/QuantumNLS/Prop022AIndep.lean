import Mathlib
import QuantumNLS.Prop022AFock
import QuantumNLS.Prop022AWeyl

/-! PROP-022 route A, stage A3: independence of the transporting unitary.

For `U, U' : H ≃ₗᵢ[ℂ] L²(𝕋_L)` put `R = U'U⁻¹` (a unitary of `L²(𝕋_L)`), so `Γ(U') = Γ(R) Γ(U)`.
Using the Weyl covariance of `Prop022AWeyl` (`Γ(R) W(w) Γ(R)⁻¹ = W(R w)`):
* `WH_indep`:  `W_H(v)` does not depend on `U`;
* `vacH_indep`: the vacuum does not depend on `U`;
* `VH_phase`: the propagators `V_{H,U}(t,s)`, `V_{H,U'}(t,s)` implement the same `S_H(t,s)` and
  hence differ by a unimodular phase (uniqueness of Weyl implementers up to phase);
* `QFH_of_implementer`, `QFH_indep`: the transported pure-quasifree predicate holds for every `U'`
  at `ξ_t = V_{H,U}(t,0) Ω`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace

namespace QuantumNLS.Prop022AIndep
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GClassical Prop022GLinear Prop022AFock Prop022AWeyl Prop022ACoherent
open Prop022OVacuum Prop022TensorCompressionR115 OccupationUnitary Occupation Ext006IdentityCyclicR35a
open Ext006PhysQuasifree Ext006PhysFockCoord
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- The change of transporting unitary `R = U' U⁻¹`. -/
def chg (U U' : H ≃ₗᵢ[ℂ] L2T L) : L2T L ≃ₗᵢ[ℂ] L2T L := U.symm.trans U'

lemma chg_apply (U U' : H ≃ₗᵢ[ℂ] L2T L) (v : H) : chg U U' (U v) = U' v := by
  simp [chg]

lemma gam_chg (U U' : H ≃ₗᵢ[ℂ] L2T L) (x : FockSpace H) :
    gam U' x = (fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L) (gam U x) := by
  have : U' = U.trans (chg U U') := by
    ext v
    simp [chg]
  conv_lhs => rw [this]
  exact fockMap_trans U (chg U U') x

lemma gam_symm_chg (U U' : H ≃ₗᵢ[ℂ] L2T L) (y : Fock L) :
    (gam U').symm y = (gam U).symm
      ((fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L).symm y) := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  rw [gam_chg U U', LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **The transported printed Weyl operator does not depend on `U`.** -/
theorem WH_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) (v : H) : WH U' v = WH U v := by
  apply LinearIsometryEquiv.ext
  intro x
  change (gam U').symm (printedWeyl (U' v) (gam U' x)) =
    (gam U).symm (printedWeyl (U v) (gam U x))
  rw [gam_symm_chg U U', gam_chg U U', ← chg_apply U U' v,
    ← printedWeyl_covariant (chg U U') (U v)]
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma fockMap_vac (R : L2T L ≃ₗᵢ[ℂ] L2T L) :
    (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) (vac (L := L)) = vac := by
  have hv : Phi (vac (L := L)) = secEmb 0 (ketVec (L := L) 0) := by
    have h1 : (Phi (L := L)) (vac (L := L)) = (ketD (0 : Occ)).1 := by
      unfold vac
      rw [physCore_ket, LinearIsometryEquiv.apply_symm_apply]
      rfl
    rw [h1, ket_eq_emb (L := L) 0]
    rfl
  have hk : symMap R 0 (ketVec (L := L) 0) = ketVec 0 := by
    have : ketVec (L := L) 0 = power 0 (0 : L2T L) := by
      change (physicalOccupation L 0).symm (lp.single 2 (⟨0, rfl⟩ : Arr 0) (1 : ℂ)) = _
      rw [LinearIsometryEquiv.symm_apply_eq]
      apply lp.ext
      funext m
      rw [physOcc_power_apply]
      have hm : m = ⟨0, rfl⟩ := Subtype.ext ((Finsupp.degree_eq_zero_iff m.1).mp m.2)
      subst hm
      simp [normalization, multiplicityFactorial]
    rw [this, symMap_power]
    simp
  apply (Phi (L := L)).injective
  have h2 := TT_emb R 0 (ketVec 0)
  rw [hk, ← hv] at h2
  change Phi ((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) ((Phi (L := L)).symm (Phi vac))) = _ at h2
  rw [LinearIsometryEquiv.symm_apply_apply] at h2
  exact h2

/-- **The transported vacuum does not depend on `U`.** -/
theorem vacH_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) : vacH U' = vacH U := by
  unfold vacH
  rw [gam_symm_chg U U']
  have h : (fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L).symm (vac (L := L)) = vac :=
    (LinearIsometryEquiv.symm_apply_eq _).mpr (fockMap_vac _).symm
  rw [h]


/-! ### Phase independence of the propagator and the quasifree predicate -/

/-- Conjugation of a real-linear map of `L²(𝕋_L)` by a unitary `R`. -/
def conjRr (R : L2T L ≃ₗᵢ[ℂ] L2T L) (S : L2T L ≃L[ℝ] L2T L) : L2T L ≃L[ℝ] L2T L :=
  ((Rr R).symm.trans S).trans (Rr R)

lemma conjRr_apply (R : L2T L ≃ₗᵢ[ℂ] L2T L) (S : L2T L ≃L[ℝ] L2T L) (f : L2T L) :
    conjRr R S f = R (S (R.symm f)) := rfl

/-- Conjugation of a unitary of Fock space by `Γ(R)`. -/
def conjY (R : L2T L ≃ₗᵢ[ℂ] L2T L) (V : Fock L ≃ₗᵢ[ℂ] Fock L) : Fock L ≃ₗᵢ[ℂ] Fock L :=
  (((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L).symm.trans V).trans (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L))

lemma weyl_covariant_symm (R : L2T L ≃ₗᵢ[ℂ] L2T L) (f : L2T L) (y : Fock L) :
    (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L).symm (Ext006SourceWeylR44a.sourceWeyl f y) =
      Ext006SourceWeylR44a.sourceWeyl (R.symm f)
        ((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L).symm y) := by
  have h := sourceWeyl_covariant R (R.symm f) ((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L).symm y)
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply] at h
  rw [LinearIsometryEquiv.symm_apply_eq]
  exact h.symm

lemma conjY_implements (R : L2T L ≃ₗᵢ[ℂ] L2T L) (V : Fock L ≃ₗᵢ[ℂ] Fock L)
    (S : L2T L ≃L[ℝ] L2T L) (hV : Ext006SourceWeylR44a.SourceWeylImplementer S V) :
    Ext006SourceWeylR44a.SourceWeylImplementer (conjRr R S) (conjY R V) := by
  intro f x
  have hsy : (conjY R V).symm x =
      (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) (V.symm ((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L).symm x)) := rfl
  have happ : ∀ z, conjY R V z =
      (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) (V ((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L).symm z)) :=
    fun _ => rfl
  rw [hsy, happ, weyl_covariant_symm, LinearIsometryEquiv.symm_apply_apply, hV,
    sourceWeyl_covariant, LinearIsometryEquiv.apply_symm_apply, conjRr_apply]

section Phase
variable (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A) (hs : KSelfAdj K)
  (u₀ : H) (hu₀ : ‖u₀‖ = 1) (hM0 : 0 ≤ M)

/-- The source-orientation symplectic map `S' = J⁻¹ S J` of the transported data. -/
def SpU (U : H ≃ₗᵢ[ℂ] L2T L) (t s : ℝ) : L2T L ≃L[ℝ] L2T L :=
  Prop022OClassical.Sp (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t s

lemma propL_implements (U : H ≃ₗᵢ[ℂ] L2T L) (s t : ℝ) :
    Ext006SourceWeylR44a.SourceWeylImplementer (SpU K M A hA hK hs u₀ hu₀ U t s)
      (propL U K M A hA hK hs u₀ hu₀ hM0 s t) :=
  Prop022OCovariance.propagator_implements (BL U K) M A hM0 hA (BL_bound U K M A hK)
    (BL_selfAdj U K hs) (sphL U u₀ hu₀) s t

lemma flow_eq_SH (U : H ≃ₗᵢ[ℂ] L2T L) (t s : ℝ) (w : L2T L) :
    Prop022VariationalR123.flow (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs)
      (sphL U u₀ hu₀) t s w = U (SH U K M A hA hK hs u₀ hu₀ t s (U.symm w)) := by
  have h := SH_apply U K M A hA hK hs u₀ hu₀ t s (U.symm w)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [h, LinearIsometryEquiv.apply_symm_apply]

lemma flow_conj (U U' : H ≃ₗᵢ[ℂ] L2T L) (t s : ℝ) (w : L2T L) :
    Prop022VariationalR123.flow (BL U' K) M A hA (BL_bound U' K M A hK) (BL_selfAdj U' K hs)
      (sphL U' u₀ hu₀) t s w =
    chg U U' (Prop022VariationalR123.flow (BL U K) M A hA (BL_bound U K M A hK)
      (BL_selfAdj U K hs) (sphL U u₀ hu₀) t s ((chg U U').symm w)) := by
  rw [flow_eq_SH K M A hA hK hs u₀ hu₀ U' t s, flow_eq_SH K M A hA hK hs u₀ hu₀ U t s,
    ← SH_indep U U' K M A hA hK hs u₀ hu₀ t s]
  have h1 : (chg U U').symm w = U (U'.symm w) := by simp [chg]
  rw [h1, LinearIsometryEquiv.symm_apply_apply, chg_apply]

lemma Sp_conj (U U' : H ≃ₗᵢ[ℂ] L2T L) (t s : ℝ) (f : L2T L) :
    SpU K M A hA hK hs u₀ hu₀ U' t s f =
      conjRr (chg U U') (SpU K M A hA hK hs u₀ hu₀ U t s) f := by
  unfold SpU
  change Prop022OClassical.Sp (BL U' K) M A hA (BL_bound U' K M A hK) (BL_selfAdj U' K hs)
      (sphL U' u₀ hu₀) t s f =
    chg U U' (Prop022OClassical.Sp (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs)
      (sphL U u₀ hu₀) t s ((chg U U').symm f))
  rw [Prop022OClassical.Sp_apply, Prop022OClassical.Sp_apply,
    flow_conj K M A hA hK hs u₀ hu₀ U U']
  simp only [LinearIsometryEquiv.map_smul]

lemma propL_phase (U U' : H ≃ₗᵢ[ℂ] L2T L) (s t : ℝ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ y : Fock L,
      propL U' K M A hA hK hs u₀ hu₀ hM0 s t y =
        z • conjY (chg U U') (propL U K M A hA hK hs u₀ hu₀ hM0 s t) y := by
  have h1 := propL_implements K M A hA hK hs u₀ hu₀ hM0 U' s t
  have h2 := conjY_implements (chg U U') _ _ (propL_implements K M A hA hK hs u₀ hu₀ hM0 U s t)
  have hS : conjRr (chg U U') (SpU K M A hA hK hs u₀ hu₀ U t s) =
      SpU K M A hA hK hs u₀ hu₀ U' t s := by
    refine ContinuousLinearEquiv.ext (funext fun f => ?_)
    exact (Sp_conj K M A hA hK hs u₀ hu₀ U U' t s f).symm
  rw [hS] at h2
  exact Ext006SourceWeylR44a.sourceWeyl_unique_phase _ _ _ h2 h1

/-- **The propagators for two transporting unitaries differ by a phase.** -/
theorem VH_phase (U U' : H ≃ₗᵢ[ℂ] L2T L) (t s : ℝ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ x : FockSpace H,
      VH U' K M A hA hK hs u₀ hu₀ hM0 t s x = z • VH U K M A hA hK hs u₀ hu₀ hM0 t s x := by
  obtain ⟨z, hz, h⟩ := propL_phase K M A hA hK hs u₀ hu₀ hM0 U U' s t
  refine ⟨z, hz, fun x => ?_⟩
  change (gam U').symm (propL U' K M A hA hK hs u₀ hu₀ hM0 s t (gam U' x)) =
    z • (gam U).symm (propL U K M A hA hK hs u₀ hu₀ hM0 s t (gam U x))
  rw [h, gam_symm_chg U U', gam_chg U U', map_smul]
  have : conjY (chg U U') (propL U K M A hA hK hs u₀ hu₀ hM0 s t)
      ((fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L) (gam U x)) =
      (fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L) (propL U K M A hA hK hs u₀ hu₀ hM0 s t (gam U x)) := by
    change (fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L)
      ((propL U K M A hA hK hs u₀ hu₀ hM0 s t)
        ((fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L).symm
          ((fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L) (gam U x)))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [this, LinearIsometryEquiv.symm_apply_apply, map_smul]

/-- **The transported pure-quasifree predicate holds for every transporting unitary** at the
vacuum evolution. -/
theorem QFH_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) (t : ℝ) :
    QFH U' (VH U K M A hA hK hs u₀ hu₀ hM0 t 0 (vacH U)) := by
  have hY := conjY_implements (chg U U') _ _ (propL_implements K M A hA hK hs u₀ hu₀ hM0 U 0 t)
  have hS : conjRr (chg U U') (SpU K M A hA hK hs u₀ hu₀ U t 0) = SpU K M A hA hK hs u₀ hu₀ U' t 0 := by
    refine ContinuousLinearEquiv.ext (funext fun f => ?_)
    exact (Sp_conj K M A hA hK hs u₀ hu₀ U U' t 0 f).symm
  rw [hS] at hY
  have hsymp := Prop022OVacuum.Sp_symplectic (BL U' K) M A hA (BL_bound U' K M A hK)
    (BL_selfAdj U' K hs) (sphL U' u₀ hu₀) t 0
  have hβ : TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
      (Ext006KernelHilbertSchmidt.beta (Ext006KernelHilbertSchmidt.physicalBasis L)
        (SpU K M A hA hK hs u₀ hu₀ U' t 0)) ≠ ⊤ := by
    change TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
      (Ext006KernelHilbertSchmidt.beta (Ext006KernelHilbertSchmidt.physicalBasis L)
        (Prop022OClassical.Sp (BL U' K) M A hA (BL_bound U' K M A hK) (BL_selfAdj U' K hs)
          (sphL U' u₀ hu₀) t 0)) ≠ ⊤
    rw [Prop022OVacuum.hsSq_beta_Sp]
    exact Prop022WeylVacuumR124.actual_beta_finite (BL U' K) M A hM0 hA (BL_bound U' K M A hK)
      (BL_selfAdj U' K hs) (sphL U' u₀ hu₀) 0 t
  obtain ⟨hq, -, -, -⟩ := Prop022OVacuum.implementer_vacuum _ hsymp hβ _ hY
  unfold QFH
  have hv : (gam U') (VH U K M A hA hK hs u₀ hu₀ hM0 t 0 (vacH U)) =
      conjY (chg U U') (propL U K M A hA hK hs u₀ hu₀ hM0 0 t) vac := by
    change (gam U') ((gam U).symm (propL U K M A hA hK hs u₀ hu₀ hM0 0 t (gam U (vacH U)))) = _
    unfold vacH
    rw [LinearIsometryEquiv.apply_symm_apply, gam_chg U U', LinearIsometryEquiv.apply_symm_apply]
    change _ = (fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L)
      ((propL U K M A hA hK hs u₀ hu₀ hM0 0 t)
        ((fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L).symm vac))
    have h : (fockMap (chg U U') : Fock L ≃ₗᵢ[ℂ] Fock L).symm (vac (L := L)) = vac :=
      (LinearIsometryEquiv.symm_apply_eq _).mpr (fockMap_vac _).symm
    rw [h]
  rw [hv]
  exact hq

end Phase

end QuantumNLS.Prop022AIndep

#print axioms QuantumNLS.Prop022AIndep.WH_indep
#print axioms QuantumNLS.Prop022AIndep.vacH_indep
#print axioms QuantumNLS.Prop022AIndep.VH_phase
#print axioms QuantumNLS.Prop022AIndep.QFH_indep
