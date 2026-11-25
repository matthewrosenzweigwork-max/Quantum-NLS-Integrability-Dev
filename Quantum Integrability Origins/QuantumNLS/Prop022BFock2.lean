import Mathlib
import QuantumNLS.Prop022BClass2
import QuantumNLS.Prop022BFock1
import QuantumNLS.Prop022AIndep
import QuantumNLS.Prop022ACovIndep
import QuantumNLS.Prop022OMain

/-! PROP-022 route A, finite-dimensional case, stage B4: the Fock side through an isometric
embedding `J : H →ₗᵢ L2T L` (printed conclusions 4-6 of Q7B:lem:pair).

With `K' = kernelsI J K` the frozen physical propagator `Pr s t = propL (refl) K' ... s t` of `Fock(L2T L)`
and the printed Weyl operators `printedWeyl (J v)` commute with `Γ(R)` for every unitary `R` of `L2T L`
fixing `range J` (frozen `VH_indep` / `printedWeyl_covariant`), hence by `Prop022BFock1.compress` restrict to
unitaries `VJ`, `WJ` of `Fock(H)`.  The generator `QJ(a,b) = Γ(J)* strongCoordinates(Γ₁ a Γ₁*, Γ₂ b) rootLift Γ(J)`,
with coefficient data `aSymJ = Γ₁(J)* a' Γ₁(J)`, `bSymJ = Γ₂(J)* b'` (`a', b'` the physical coefficients, whose
support in `Sym(range J)` is proved here, `aSym_support`, `bSym_support`).  `PROP022_fock_J` states the six
Fock-side conclusions. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace Topology NNReal ENNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022BFock2
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GAntiHS Prop022GClassical Prop022GLinear
open Prop022BIso Prop022BClass1 Prop022BClass2 Prop022BFock1
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022FockPropagatorR122
open Prop022PositiveDataR126 Prop022AFock Prop022ACovIndep Prop022AWeyl Prop022OVacuum
open Ext006PhysFockCoord Ext006PhysQuasifree
open Prop022PrintedCoefficientsR124 Prop022ACoherent Prop022ACovPhys Prop022AIndep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-! ### Invariance of the compressed kernels under rotations fixing `range J` -/

section Fixed
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H)

lemma symMap_symI (R : L2T L ≃ₗᵢ[ℂ] L2T L) (hR : Fixes J R) (m : ℕ) (x : SymSector ℂ H m) :
    symMap R m (symI J m x) = symI J m x := by
  have h := congrArg (fun w : Fock L => w m)
    (fock_fixed_of_range J R hR (lp.single 2 m x : FockSpace H))
  change symMap R m ((fockMapI J (lp.single 2 m x : FockSpace H)) m) =
    (fockMapI J (lp.single 2 m x : FockSpace H)) m at h
  rw [fockMapI_single, lp.single_apply_self] at h
  exact h

lemma symAdj_symMap (R : L2T L ≃ₗᵢ[ℂ] L2T L) (hR : Fixes J R) (m : ℕ)
    (y : SymSector ℂ (L2T L) m) : symAdj J m ((symMap R m).symm y) = symAdj J m y := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_symAdj_left, inner_symAdj_left, LinearIsometryEquiv.inner_map_eq_flip,
    LinearIsometryEquiv.symm_symm, symMap_symI J R hR]

lemma conjSym_kernelsI (R : L2T L ≃ₗᵢ[ℂ] L2T L) (hR : Fixes J R) (n : ℕ) :
    conjSym R (n + 1) (kernelsI J K n) = kernelsI J K n := by
  apply ContinuousLinearMap.ext
  intro y
  rw [conjSym_apply, kernelsI_apply, kernelsI_apply, symMap_symI J R hR, symAdj_symMap J R hR]

lemma BL_fix (R : L2T L ≃ₗᵢ[ℂ] L2T L) (hR : Fixes J R) (m : ℕ) :
    conjSym R m (BL (UI L) (kernelsI J K) m) = BL (UI L) (kernelsI J K) m := by
  cases m with
  | zero =>
    apply ContinuousLinearMap.ext
    intro y
    simp [BL, positiveExtension, conjSym_apply]
  | succ n =>
    have h1 : BL (UI L) (kernelsI J K) (n + 1) = kernelsI J K n :=
      conjSym_kernelsI J K (UI L) (fun _ => rfl) n
    rw [h1]
    exact conjSym_kernelsI J K R hR n

lemma propagator_congr {B B' : ∀ m, HN L m →L[ℂ] HN L m} (hBB : B = B') (M A : ℝ) (hM : 0 ≤ M)
    (hA : 0 ≤ A) (hb : FactorialBound B M A) (hb' : FactorialBound B' M A)
    (hs : ∀ m, (B m).adjoint = B m) (hs' : ∀ m, (B' m).adjoint = B' m)
    (u u' : Prop001.Sphere (L2T L)) (huu : u = u') (s t : ℝ) :
    propagator B M A hM hA hb hs u s t = propagator B' M A hM hA hb' hs' u' s t := by
  subst hBB
  subst huu
  rfl

end Fixed

section Main
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

/-- The physical propagator of the compressed kernels. -/
def Pr (s t : ℝ) : Fock L ≃ₗᵢ[ℂ] Fock L :=
  propL (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀)
    (zero_le_one.trans hM) s t

/-- The propagator `Pr` commutes with `Γ(R)` for every unitary `R` fixing `range J`
(frozen `VH_indep` applied to `UI` and `UI.trans R`). -/
theorem Pr_commutes (s t : ℝ) : Commutes J (Pr J K M A hM hA hK hs u₀ hu₀ s t) := by
  intro R hR z
  have hVi := congrArg (fun V : FockSpace (L2T L) ≃ₗᵢ[ℂ] FockSpace (L2T L) => V)
    (Prop022ACovIndep.VH_indep (kernelsI J K) M A hM hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
      (hJu J u₀ hu₀) (UI L) ((UI L).trans R) t s)
  have hBL : BL ((UI L).trans R) (kernelsI J K) = BL (UI L) (kernelsI J K) := by
    funext m
    rw [BL_trans]
    exact BL_fix J K R hR m
  have hsph : sphL ((UI L).trans R) (J u₀) (hJu J u₀ hu₀) = sphL (UI L) (J u₀) (hJu J u₀ hu₀) :=
    Subtype.ext (hR u₀)
  have hP : propL ((UI L).trans R) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
      (hJu J u₀ hu₀) (zero_le_one.trans hM) s t =
      Pr J K M A hM hA hK hs u₀ hu₀ s t :=
    propagator_congr hBL M A _ hA.le _ _ _ _ _ _ hsph s t
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
  exact h3.symm

/-- The compressed propagator `V_J(t,s) = Γ(J)* Pr(s,t) Γ(J)` on `Fock(H)`. -/
def VJ (t s : ℝ) : FockSpace H ≃ₗᵢ[ℂ] FockSpace H :=
  compress J (Pr J K M A hM hA hK hs u₀ hu₀ s t) (Pr_commutes J K M A hM hA hK hs u₀ hu₀ s t)

end Main

section Weyl
variable (J : H →ₗᵢ[ℂ] L2T L)

theorem Weyl_commutes (v : H) : Commutes J (printedWeyl (J v)) := by
  intro R hR z
  rw [printedWeyl_covariant, hR v]

/-- The printed Weyl operator `W_J(v) = Γ(J)* W(J v) Γ(J)` on `Fock(H)`. -/
def WJ (v : H) : FockSpace H ≃ₗᵢ[ℂ] FockSpace H := compress J (printedWeyl (J v)) (Weyl_commutes J v)

/-- The vacuum of `Fock(H)`. -/
def vacJ : FockSpace H := gamAdj J (vac (L := L))

/-- Pure-quasifree predicate on `Fock(H)`, through `J`. -/
def QFJ (ξ : FockSpace H) : Prop := PhysicalQuasifreeSource (fockMapI J ξ)

/-- The quadratic generator `dΓ(a) + ½(a*(b)+a(b))` on `Fock(H)` for coefficient data
`a ∈ B(Sym¹H)`, `b ∈ Sym²H`, acting on second-moment coordinates. -/
def QJ (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2) (y : FockSpace H) :
    FockSpace H :=
  gamAdj J (Prop022StrongOperatorR125.strongCoordinates (symI J 1 ∘L a ∘L symAdj J 1) (symI J 2 b)
    (Ext005FormCutoffR109.rootLift 2 (fockMapI J y)))

lemma gam_vacJ : fockMapI J (vacJ J) = (vac : Fock L) := by
  apply fock_mem_range
  intro R hR
  exact fockMap_vac R

end Weyl

end QuantumNLS.Prop022BFock2
