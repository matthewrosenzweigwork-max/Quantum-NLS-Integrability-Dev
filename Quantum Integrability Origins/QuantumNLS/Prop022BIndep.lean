import Mathlib
import QuantumNLS.Prop022BFock3

/-! PROP-022 route A, finite-dimensional case, stage B5b: independence of the isometric embedding.

If `R` is a unitary of `L2T L` with `R (J v) = J' v` then `Γ(J') = Γ(R) Γ(J)`, `kernelsI J' K = conj_R (kernelsI J K)`,
and the frozen unitary covariance (`VH_indep`, `printedWeyl_covariant`, `strongCoordinates_cov`,
`pairCoefficient_cov`, `numberCoefficient_cov`, `QFH_indep`) gives, for the compressed objects:
`W_{J'} = W_J`, `vac_{J'} = vac_J`, `V_{J'} = V_J`, `a_{J'} = a_J`, `b_{J'} = b_J`, `Q_{J'}(a,b) = Q_J(a,b)`, and the
quasifree predicate for `J'` holds at `V_J(t,0) Ω`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace Topology NNReal ENNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022BIndep
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GAntiHS Prop022GClassical Prop022GLinear
open Prop022BIso Prop022BClass1 Prop022BClass2 Prop022BFock1 Prop022BFock2 Prop022BFock3
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022FockPropagatorR122
open Prop022PositiveDataR126 Prop022AFock Prop022ACovIndep Prop022AWeyl Prop022OVacuum
open Ext006PhysFockCoord Ext006PhysQuasifree
open Prop022PrintedCoefficientsR124 Prop022ACoherent Prop022ACovPhys Prop022AIndep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

section Trans
variable (J J' : H →ₗᵢ[ℂ] L2T L) (R : L2T L ≃ₗᵢ[ℂ] L2T L) (hR : ∀ v, R (J v) = J' v)
include hR

lemma fockMapI_trans (x : FockSpace H) : fockMapI J' x = fockMap R (fockMapI J x) := by
  have h : J' = R.toLinearIsometry.comp J := LinearIsometry.ext (fun v => (hR v).symm)
  rw [h, fockMapI_comp, fockMapI_equiv]

lemma symI_trans (m : ℕ) (x : SymSector ℂ H m) : symI J' m x = symMap R m (symI J m x) := by
  have h := congrArg (fun w : Fock L => w m) (fockMapI_trans J J' R hR (lp.single 2 m x : FockSpace H))
  change (fockMapI J' (lp.single 2 m x : FockSpace H)) m =
    symMap R m ((fockMapI J (lp.single 2 m x : FockSpace H)) m) at h
  rw [fockMapI_single, fockMapI_single, lp.single_apply_self] at h
  rw [lp.single_apply_self] at h
  exact h

lemma symAdj_trans (m : ℕ) (y : SymSector ℂ (L2T L) m) :
    symAdj J' m y = symAdj J m ((symMap R m).symm y) := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_symAdj_left, inner_symAdj_left, symI_trans J J' R hR, LinearIsometryEquiv.inner_map_eq_flip,
    LinearIsometryEquiv.symm_symm]

lemma gamAdj_trans (u : Fock L) : gamAdj J' (fockMap R u) = gamAdj J u := by
  apply ext_inner_right ℂ
  intro v
  rw [gamAdj, gamAdj, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  change ⟪fockMap R u, fockMapI J' v⟫_ℂ = ⟪u, fockMapI J v⟫_ℂ
  rw [fockMapI_trans J J' R hR, LinearIsometryEquiv.inner_map_map]

lemma conjSym_symI (m : ℕ) (X : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    conjSym R m (symI J m ∘L X ∘L symAdj J m) = symI J' m ∘L X ∘L symAdj J' m := by
  apply ContinuousLinearMap.ext
  intro y
  rw [conjSym_apply]
  simp only [ContinuousLinearMap.comp_apply, symI_trans J J' R hR, symAdj_trans J J' R hR]

lemma kernelsI_trans (K : Kernels H) (n : ℕ) :
    kernelsI J' K n = conjSym R (n + 1) (kernelsI J K n) := by
  have h := conjSym_symI J J' R hR (n + 1) (K n)
  exact h.symm

lemma BL_trans_J (K : Kernels H) :
    BL (UI L) (kernelsI J' K) = BL ((UI L).trans R) (kernelsI J K) := by
  funext m
  rw [BL_trans]
  cases m with
  | zero =>
    apply ContinuousLinearMap.ext
    intro y
    simp [BL, positiveExtension, conjSym_apply]
  | succ n =>
    have h1 : BL (UI L) (kernelsI J' K) (n + 1) = kernelsI J' K n :=
      conjSym_kernelsI J' K (UI L) (fun _ => rfl) n
    have h2 : BL (UI L) (kernelsI J K) (n + 1) = kernelsI J K n :=
      conjSym_kernelsI J K (UI L) (fun _ => rfl) n
    rw [h1, h2, kernelsI_trans J J' R hR K n]

lemma profile_congr {B B' : ∀ m, HN L m →L[ℂ] HN L m} (hBB : B = B') (M A : ℝ) (hA : 0 ≤ A)
    (hb : FactorialBound B M A) (hb' : FactorialBound B' M A)
    (hs : ∀ m, (B m).adjoint = B m) (hs' : ∀ m, (B' m).adjoint = B' m)
    (u u' : Prop001.Sphere (L2T L)) (huu : u = u') (t : ℝ) :
    profile B M A hA hb hs u t = profile B' M A hA hb' hs' u' t := by
  subst hBB
  subst huu
  rfl

section Data
variable (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

lemma sph_trans : sphL ((UI L).trans R) (J u₀) (hJu J u₀ hu₀) = sphL (UI L) (J' u₀) (hJu J' u₀ hu₀) :=
  Subtype.ext (hR u₀)

/-- The physical propagator is transported by `Γ(R)`. -/
theorem Pr_transport (s t : ℝ) (z : Fock L) :
    Pr J' K M A hM hA hK hs u₀ hu₀ s t (fockMap R z) =
      fockMap R (Pr J K M A hM hA hK hs u₀ hu₀ s t z) := by
  have hVi := congrArg (fun V : FockSpace (L2T L) ≃ₗᵢ[ℂ] FockSpace (L2T L) => V)
    (Prop022ACovIndep.VH_indep (kernelsI J K) M A hM hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
      (hJu J u₀ hu₀) (UI L) ((UI L).trans R) t s)
  have hP : propL ((UI L).trans R) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
      (hJu J u₀ hu₀) (zero_le_one.trans hM) s t =
      Pr J' K M A hM hA hK hs u₀ hu₀ s t :=
    propagator_congr (BL_trans_J J J' R hR K).symm M A _ hA.le _ _ _ _ _ _
      (sph_trans J J' R hR u₀ hu₀) s t
  have hx := congrArg (fun V : FockSpace (L2T L) ≃ₗᵢ[ℂ] FockSpace (L2T L) =>
    V ((gam (UI L)).symm z)) hVi

  have hx' : (gam ((UI L).trans R)).symm
      (propL ((UI L).trans R) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
        (hJu J u₀ hu₀) (zero_le_one.trans hM) s t (gam ((UI L).trans R) ((gam (UI L)).symm z))) =
      (gam (UI L)).symm (Pr J K M A hM hA hK hs u₀ hu₀ s t
        (gam (UI L) ((gam (UI L)).symm z))) := hx
  rw [hP, gam_symm_trans, gam_trans, LinearIsometryEquiv.apply_symm_apply (gam (UI L))] at hx'
  have h2 := (gam (UI L)).symm.injective hx'
  have h3 := congrArg (GR R) h2
  rw [LinearIsometryEquiv.apply_symm_apply] at h3
  exact h3

theorem VJ_indep (t s : ℝ) :
    VJ J' K M A hM hA hK hs u₀ hu₀ t s = VJ J K M A hM hA hK hs u₀ hu₀ t s := by
  refine LinearIsometryEquiv.ext (fun x => ?_)
  apply (fockMapI J').injective
  have e1 : ∀ x, fockMapI J' (VJ J' K M A hM hA hK hs u₀ hu₀ t s x) =
      Pr J' K M A hM hA hK hs u₀ hu₀ s t (fockMapI J' x) := fun x => gam_compress J' _ _ x
  have e2 : ∀ x, fockMapI J (VJ J K M A hM hA hK hs u₀ hu₀ t s x) =
      Pr J K M A hM hA hK hs u₀ hu₀ s t (fockMapI J x) := fun x => gam_compress J _ _ x
  rw [e1, fockMapI_trans J J' R hR x, Pr_transport J J' R hR K M A hM hA hK hs u₀ hu₀,
    fockMapI_trans J J' R hR (VJ J K M A hM hA hK hs u₀ hu₀ t s x), e2]

theorem QFJ_indep (t : ℝ) :
    QFJ J' (VJ J K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J)) := by
  have h := QFH_indep (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
    (hJu J u₀ hu₀) (zero_le_one.trans hM) (UI L) ((UI L).trans R) t
  unfold QFH at h
  rw [gam_trans] at h
  have hv : gam (UI L) (VH (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
      (hJu J u₀ hu₀) (zero_le_one.trans hM) t 0 (vacH (UI L))) =
      Pr J K M A hM hA hK hs u₀ hu₀ 0 t (vac : Fock L) := by
    change gam (UI L) ((gam (UI L)).symm (propL (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK)
      (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) (zero_le_one.trans hM) 0 t
        (gam (UI L) (vacH (UI L))))) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    unfold vacH
    rw [LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [hv] at h
  unfold QFJ
  rw [fockMapI_trans J J' R hR]
  have e2 : fockMapI J (VJ J K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J)) =
      Pr J K M A hM hA hK hs u₀ hu₀ 0 t (fockMapI J (vacJ J)) := gam_compress J _ _ _
  rw [e2, gam_vacJ]
  exact h

end Data

theorem WJ_indep (v : H) : WJ J' v = WJ J v := by
  refine LinearIsometryEquiv.ext (fun x => ?_)
  apply (fockMapI J').injective
  have e1 : ∀ w x, fockMapI J' (WJ J' w x) = printedWeyl (J' w) (fockMapI J' x) :=
    fun w x => gam_compress J' _ _ x
  have e2 : ∀ w x, fockMapI J (WJ J w x) = printedWeyl (J w) (fockMapI J x) :=
    fun w x => gam_compress J _ _ x
  rw [e1, fockMapI_trans J J' R hR x, fockMapI_trans J J' R hR (WJ J v x), e2, ← hR v]
  exact (printedWeyl_covariant R (J v) _).symm

theorem vacJ_indep : vacJ J' = vacJ (L := L) J := by
  apply (fockMapI J').injective
  rw [gam_vacJ, fockMapI_trans J J' R hR, gam_vacJ]
  exact (fockMap_vac R).symm

theorem QJ_indep (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2)
    (y : FockSpace H) : QJ J' a b y = QJ J a b y := by
  unfold QJ
  rw [← conjSym_symI J J' R hR 1 a, symI_trans J J' R hR 2 b, fockMapI_trans J J' R hR y,
    rootLift_cov R 2 _, ← strongCoordinates_cov, gamAdj_trans J J' R hR]

section Coef
variable (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)
include hM

local notation "BpJ" J₀:max => BL (UI L) (kernelsI J₀ K)
local notation "upJ" J₀:max t:max => profile (BL (UI L) (kernelsI J₀ K)) M A hA.le
  (BL_bound (UI L) (kernelsI J₀ K) M A (hKJ J₀ K M A hK))
  (BL_selfAdj (UI L) (kernelsI J₀ K) (hsJ J₀ K hs)) (sphL (UI L) (J₀ u₀) (hJu J₀ u₀ hu₀)) t

lemma prof_trans (t : ℝ) : (upJ J' t) = R (upJ J t) := by
  have h1 : (upJ J' t) = profile (BL ((UI L).trans R) (kernelsI J K)) M A hA.le
      (BL_bound ((UI L).trans R) (kernelsI J K) M A (hKJ J K M A hK))
      (BL_selfAdj ((UI L).trans R) (kernelsI J K) (hsJ J K hs))
      (sphL ((UI L).trans R) (J u₀) (hJu J u₀ hu₀)) t :=
    profile_congr J J' R hR (BL_trans_J J J' R hR K) M A hA.le _ _ _ _ _ _
      (sph_trans J J' R hR u₀ hu₀).symm t
  rw [h1]
  exact profile_trans (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
    (hJu J u₀ hu₀) (UI L) R t

lemma BLtrans_fun : (BpJ J') = fun m => conjSym R m ((BpJ J) m) :=
  (BL_trans_J J J' R hR K).trans (funext (BL_trans (UI L) R (kernelsI J K)))

lemma unit_upJ (t : ℝ) : ‖upJ J t‖ = 1 :=
  profile_unit (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) (UI L) t

lemma ap_trans (t : ℝ) :
    numberCoefficient (BpJ J') (upJ J' t) = conjSym R 1 (numberCoefficient (BpJ J) (upJ J t)) := by
  rw [prof_trans J J' R hR K M A hM hA hK hs u₀ hu₀ t, BLtrans_fun J J' R hR K M hM]
  exact (Prop022ACovCoef.numberCoefficient_cov R (BpJ J) M A hA.le
    (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK)) (upJ J t)
    (unit_upJ J J' R hR K M A hM hA hK hs u₀ hu₀ t)).symm

lemma bp_trans (t : ℝ) :
    pairCoefficient (BpJ J') (upJ J' t) = symMap R 2 (pairCoefficient (BpJ J) (upJ J t)) := by
  rw [prof_trans J J' R hR K M A hM hA hK hs u₀ hu₀ t, BLtrans_fun J J' R hR K M hM]
  exact (Prop022ACovCoef.pairCoefficient_cov R (BpJ J) (upJ J t)).symm

theorem aSymJ_indep (t : ℝ) :
    aSymJ J' K M A hA hK hs u₀ hu₀ t = aSymJ J K M A hA hK hs u₀ hu₀ t := by
  unfold aSymJ
  rw [ap_trans J J' R hR K M A hM hA hK hs u₀ hu₀ t]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply, symI_trans J J' R hR, symAdj_trans J J' R hR,
    conjSym_apply, LinearIsometryEquiv.symm_apply_apply]

theorem bSymJ_indep (t : ℝ) :
    bSymJ J' K M A hA hK hs u₀ hu₀ t = bSymJ J K M A hA hK hs u₀ hu₀ t := by
  unfold bSymJ
  rw [bp_trans J J' R hR K M A hM hA hK hs u₀ hu₀ t, symAdj_trans J J' R hR,
    LinearIsometryEquiv.symm_apply_apply]

end Coef

end Trans

end QuantumNLS.Prop022BIndep

#print axioms QuantumNLS.Prop022BIndep.VJ_indep
#print axioms QuantumNLS.Prop022BIndep.QFJ_indep
#print axioms QuantumNLS.Prop022BIndep.WJ_indep
#print axioms QuantumNLS.Prop022BIndep.vacJ_indep
#print axioms QuantumNLS.Prop022BIndep.QJ_indep
#print axioms QuantumNLS.Prop022BIndep.aSymJ_indep
#print axioms QuantumNLS.Prop022BIndep.bSymJ_indep
