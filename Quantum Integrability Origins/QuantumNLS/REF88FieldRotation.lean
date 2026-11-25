import Mathlib
import QuantumNLS.REF88Finite
import QuantumNLS.REF88EnergyBound
import QuantumNLS.REF88EnergyGrad
import QuantumNLS.REF88GradStructure

/-!
# REF88FieldRotation: the finite-action field identity `FieldRotation` is PROVED (R-EF8C2837)

Source: `source-text/chapters/global/physical_cubic.tex`, proof, paragraphs "Bounded contour energies near
arbitrary mass" and "Physical rotations on finite action supports" (printed lines 38 to 175).  This module
discharges the obligation `QuantumNLS.REF88Finite.FieldRotation hΦ κ` (the printed
`eq:global-finite-action-field` in the chart) from the accepted chart hypotheses and the named input
`Reg015Input` (only for: every finite-action field is in every `H^s`, accepted REG-015 consequence).

Printed step -> Lean:
* weighted contour energy `E_F` real analytic near `u_*`: `REF88EnergyContour.analyticAt_cellEnergy`,
  `REF88EnergyBound.analyticAt_contourEnergy`;
* `H_κ ≥ E_F` with equality at `u_*`, scalar uniqueness: `REF88EnergyBound`;
* minimum principle on `H¹`, density, `X_{E_F}(u_*) = i u_*'' - 2iκ|u_*|²u_*`:
  `REF88EnergyGrad.fderiv_eq_omega_physField`;
* `e_F = E_F ∘ Φ⁻¹` invariant under all rotations (its value depends only on the indexed masses, R-063C168E;
  `eOf_rot`), radial structure of its differential (zero coordinates by the half-turn, active coordinates by the
  rotation, complement by density): `REF88GradStructure`;
* transfer of the Hamiltonian field through the strongly symplectic `Φ⁻¹` (`field_identity`);
* the frequencies `λ_n = lamFun` depend only on the action array (`lamFun_act`): two finitely supported points
  with the same actions differ by a rotation, the contour energy is the same function for both (same
  quantum measure, same separators), and `e_F ∘ R_θ = e_F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate InnerProductSpace
open Filter Topology

namespace QuantumNLS.REF88FieldRotation

open QuantumNLS.Fourier QuantumNLS.RephasingFlow QuantumNLS.ChartFrequencies QuantumNLS.StrongSymplectic
open QuantumNLS.REF88Chart QuantumNLS.REF88Reg015 QuantumNLS.REF88Finite
open QuantumNLS.REF88EnergyContour QuantumNLS.REF88EnergyBound QuantumNLS.REF88EnergyGrad
open QuantumNLS.REF88GradStructure
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ProductEnergyPreparation (OneH1)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The exact (finite) support of a finitely supported point, `∅` otherwise. -/
def suppF (z : K) : Finset ℤ := by
  classical exact if h : (Function.support (fun n => (z : ℤ → ℂ) n)).Finite then h.toFinset else ∅

lemma mem_suppF {z : K} (hz : ∃ F : Finset ℤ, ∀ n, n ∉ F → z n = 0) {n : ℤ} :
    n ∈ suppF z ↔ z n ≠ 0 := by
  obtain ⟨F, hF⟩ := hz
  have hfin : (Function.support (fun n => (z : ℤ → ℂ) n)).Finite := by
    apply F.finite_toSet.subset
    intro m hm
    by_contra hmF
    exact hm (hF m hmF)
  unfold suppF
  rw [dif_pos hfin, Set.Finite.mem_toFinset]
  rfl

lemma suppF_congr {z z' : K} (h : ∀ n, ‖z n‖ = ‖z' n‖) : suppF z = suppF z' := by
  have hs : Function.support (fun n => (z : ℤ → ℂ) n) = Function.support (fun n => (z' : ℤ → ℂ) n) := by
    ext n
    have h0 : ((z : ℤ → ℂ) n = 0) ↔ ((z' : ℤ → ℂ) n = 0) := by
      rw [← norm_eq_zero (a := (z : ℤ → ℂ) n), ← norm_eq_zero (a := (z' : ℤ → ℂ) n), h n]
    exact not_congr h0
  unfold suppF
  rw [hs]

lemma omega_sub_left' (a b h : L2T L) :
    SymplecticBracket.omega (a - b) h = SymplecticBracket.omega a h - SymplecticBracket.omega b h := by
  unfold SymplecticBracket.omega
  rw [inner_sub_left, Complex.sub_im]; ring

lemma eq_zero_of_omega {d : L2T L} (hd : ∀ k, SymplecticBracket.omega d k = 0) : d = 0 := by
  have := SymplecticBracket.omega_mul_I d
  rw [hd] at this
  have h2 : ‖d‖ ^ 2 = 0 := by linarith
  exact norm_eq_zero.mp (by simpa using h2)

section Chart

variable (hκ : 0 < κ) {Φ : L2T L → K} (hΦ : IsStronglySymplectic Φ)

lemma masses_chart (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    (y : K) (n : ℤ) : (RootIndexedMasses.masses hκ (chartInv hΦ y)).1 n = ‖y n‖ ^ 2 := by
  rw [← hmod (chartInv hΦ y) n, chartInv_right hΦ]

lemma differentiable_chartInv : Differentiable ℝ (chartInv hΦ) :=
  (Classical.choose_spec hΦ.exists_inverse).2.2

/-- The contour energy of the cells of the base point `z`, in the chart. -/
def eOf (z : K) : K → ℝ := fun y =>
  contourEnergy hκ (sep hκ (chartInv hΦ z)) (suppF z) (chartInv hΦ y)

/-- The active frequency `λ_n(z) = ∂_{a_n} h_F` read off `d e_F(z)[z_n e_n] = 2 |z_n|² λ_n`. -/
def lamAt (z : K) (n : ℤ) : ℝ :=
  fderiv ℝ (eOf hκ hΦ z) z (sg n (z n)) / (2 * ‖z n‖ ^ 2)

lemma hasDerivAt_along {e : K → ℝ} {y : K} (hd : DifferentiableAt ℝ e y) (v : K) :
    HasDerivAt (fun s : ℝ => e (y + s • v)) (fderiv ℝ e y v) 0 := by
  have hd' : HasFDerivAt e (fderiv ℝ e y) (y + (0 : ℝ) • v) := by
    simpa using hd.hasFDerivAt
  exact hd'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line y v)

lemma rotE_line (θ : ℤ → ℝ) (z : K) (n : ℤ) (w : ℂ) (s : ℝ) :
    rotE θ (z + s • sg n w) = rotE θ z + s • sg n (Complex.exp ((θ n : ℂ) * Complex.I) * w) := by
  apply lp.ext; funext m
  simp only [rotE_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, sg_apply,
    Complex.real_smul]
  by_cases hm : m = n
  · subst hm; simp; ring
  · simp [hm]

variable (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
include hmod

lemma eOf_rot (z : K) (θ : ℤ → ℝ) (y : K) : eOf hκ hΦ z (rotE θ y) = eOf hκ hΦ z y := by
  unfold eOf
  apply contourEnergy_eq_of_masses
  intro n
  rw [masses_chart hκ hΦ hmod, masses_chart hκ hΦ hmod, rotE_apply, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

lemma eOf_congr {z z' : K} (h : ∀ n, ‖z n‖ = ‖z' n‖) : eOf hκ hΦ z = eOf hκ hΦ z' := by
  have hsep : sep hκ (chartInv hΦ z) = sep hκ (chartInv hΦ z') := by
    apply sep_eq_of_masses
    intro n
    rw [masses_chart hκ hΦ hmod, masses_chart hκ hΦ hmod, h n]
  funext y
  unfold eOf
  rw [hsep, suppF_congr h]

lemma differentiableAt_eOf {z y : K} (h : ∀ n, ‖y n‖ = ‖z n‖) :
    DifferentiableAt ℝ (eOf hκ hΦ z) y := by
  have hsep : sep hκ (chartInv hΦ y) = sep hκ (chartInv hΦ z) := by
    apply sep_eq_of_masses
    intro n
    rw [masses_chart hκ hΦ hmod, masses_chart hκ hΦ hmod, h n]
  have h1 := (analyticAt_contourEnergy_of_sep hκ (suppF z) hsep).differentiableAt
  exact h1.comp y (differentiable_chartInv hΦ y)


/-- The frequency is the same at two points differing by a rotation. -/
lemma lamAt_rot (z0 z : K) (θ : ℤ → ℝ) (hz : z = rotE θ z0) (n : ℤ) :
    lamAt hκ hΦ z n = lamAt hκ hΦ z0 n := by
  have hn : ∀ m, ‖z0 m‖ = ‖z m‖ := by
    intro m; rw [hz, rotE_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have he : eOf hκ hΦ z = eOf hκ hΦ z0 := eOf_congr hκ hΦ hmod (fun m => (hn m).symm)
  have hd0 : DifferentiableAt ℝ (eOf hκ hΦ z0) z0 := differentiableAt_eOf hκ hΦ hmod (fun m => rfl)
  have hd1 : DifferentiableAt ℝ (eOf hκ hΦ z0) z :=
    differentiableAt_eOf hκ hΦ hmod (fun m => (hn m).symm)
  have h0 := hasDerivAt_along hd0 (sg n (z0 n))
  have h1 := hasDerivAt_along hd1 (sg n (z n))
  have hfun : (fun s : ℝ => eOf hκ hΦ z0 (z + s • sg n (z n))) =
      fun s : ℝ => eOf hκ hΦ z0 (z0 + s • sg n (z0 n)) := by
    funext s
    have : z + s • sg n (z n) = rotE θ (z0 + s • sg n (z0 n)) := by
      rw [rotE_line, ← hz, hz, rotE_apply]
    rw [this, eOf_rot hκ hΦ hmod]
  rw [hfun] at h1
  have hu := h1.unique h0
  unfold lamAt
  rw [he, hu, ← hn n]

open Classical in
/-- The frequency function of the action array (any representative; independent of the phases). -/
def lamFun : (ℤ → ℝ) → ℤ → ℝ := fun a n =>
  if h : ∃ z : K, (∃ F : Finset ℤ, ∀ m, m ∉ F → z m = 0) ∧ act z = a then
    lamAt hκ hΦ (Classical.choose h) n else 0

lemma lamFun_act (z : K) (hz : ∃ F : Finset ℤ, ∀ m, m ∉ F → z m = 0) (n : ℤ) :
    lamFun hκ hΦ (act z) n = lamAt hκ hΦ z n := by
  have h : ∃ z' : K, (∃ F : Finset ℤ, ∀ m, m ∉ F → z' m = 0) ∧ act z' = act z := ⟨z, hz, rfl⟩
  unfold lamFun
  rw [dif_pos h]
  obtain ⟨-, hact⟩ := Classical.choose_spec h
  set z0 := Classical.choose h with hz0
  have hm : ∀ m, ‖z0 m‖ = ‖z m‖ := by
    intro m
    have := congrFun hact m
    simp only [act] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  obtain ⟨θ, hθ⟩ := exists_rotE_of_norm_eq hm
  exact (lamAt_rot hκ hΦ hmod z0 z θ hθ n).symm

/-- **The finite-action field identity at one point.** -/
theorem field_identity (hR : Reg015Input L κ hκ) (z : K) (F : Finset ℤ)
    (hz : ∀ n, n ∉ F → z n = 0) :
    fderiv ℝ (chartInv hΦ) z (∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
      (-Complex.I * ((lamAt hκ hΦ z n : ℝ) : ℂ) * z n)) = physField κ (chartInv hΦ z) := by
  set u := chartInv hΦ z with hu
  have hex : ∃ F : Finset ℤ, ∀ n, n ∉ F → z n = 0 := ⟨F, hz⟩
  have hF0 : ∀ n, n ∉ suppF z → (RootIndexedMasses.masses hκ u).1 n = 0 := by
    intro n hn
    rw [hu, masses_chart hκ hΦ hmod]
    have : z n = 0 := by
      by_contra h; exact hn ((mem_suppF hex).2 h)
    simp [this]
  have hu2 : MemHsLp L 2 u := finite_action_mem_Hs hκ hR u ⟨suppF z, hF0⟩ 2 (by norm_num)
  have hOne : OneH1 u := (RootEnergyVariation.m21 (g2 hu2)).summable
  obtain ⟨hI, hmom⟩ := moment_of_oneH1 hκ u hOne
  set E : L2T L → ℝ := contourEnergy hκ (sep hκ u) (suppF z) with hE
  have hEd : DifferentiableAt ℝ E u := (analyticAt_contourEnergy hκ (suppF z) u).differentiableAt
  have hle : ∀ v : L2T L, OneH1 v →
      E v ≤ ChargeEnergy.energyH1 κ (v : AddCircle L → ℂ) :=
    fun v hv => contourEnergy_le_energy hκ (sep_strictMono hκ u) (suppF z) v hv
  have heq : E u = ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) := by
    rw [hE, contourEnergy_eq_at_base hκ u (suppF z) hF0 hI, hmom]
  have hP := fderiv_eq_omega_physField (κ := κ) hu2 E hEd hle heq
  have hΨd := differentiable_chartInv hΦ
  have hΦd := hΦ.differentiable
  have hchain1 : ∀ (w' : K) (x : K), fderiv ℝ Φ (chartInv hΦ w') (fderiv ℝ (chartInv hΦ) w' x) = x := by
    intro w' x
    have hcomp : Φ ∘ chartInv hΦ = id := funext (chartInv_right hΦ)
    have h1 : fderiv ℝ (Φ ∘ chartInv hΦ) w' = ContinuousLinearMap.id ℝ K := by
      rw [hcomp, fderiv_id]
    rw [fderiv_comp w' (hΦd (chartInv hΦ w')) (hΨd w')] at h1
    have h2 := congrArg (fun T => T x) h1
    simpa using h2
  have hchain2 : ∀ (u' : L2T L) (h : L2T L),
      fderiv ℝ (chartInv hΦ) (Φ u') (fderiv ℝ Φ u' h) = h := by
    intro u' h
    have hcomp : chartInv hΦ ∘ Φ = id := funext (chartInv_left hΦ)
    have h1 : fderiv ℝ (chartInv hΦ ∘ Φ) u' = ContinuousLinearMap.id ℝ (L2T L) := by
      rw [hcomp, fderiv_id]
    rw [fderiv_comp u' (hΨd (Φ u')) (hΦd u')] at h1
    have h2 := congrArg (fun T => T h) h1
    simpa using h2
  have hDe : DifferentiableAt ℝ (eOf hκ hΦ z) z := differentiableAt_eOf hκ hΦ hmod (fun n => rfl)
  have hD := D_eq_sum hDe (eOf_rot hκ hΦ hmod z) F hz
  set w : K := ∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
      (-Complex.I * ((lamAt hκ hΦ z n : ℝ) : ℂ) * z n) with hw
  have hω : ∀ k : K, SymplecticBracket.omega w k = fderiv ℝ (eOf hκ hΦ z) z k := by
    intro k
    rw [hw, omega_sum_single, hD k]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [lamAt, ← mul_div_assoc, mul_div_mul_left _ _ two_ne_zero]
  have hcomp : fderiv ℝ (eOf hκ hΦ z) z = (fderiv ℝ E u).comp (fderiv ℝ (chartInv hΦ) z) :=
    (hEd.hasFDerivAt.comp z (hΨd z).hasFDerivAt).fderiv
  have hmain : ∀ h : L2T L, SymplecticBracket.omega (fderiv ℝ (chartInv hΦ) z w) h =
      SymplecticBracket.omega (physField κ u) h := by
    intro h
    set k : K := fderiv ℝ Φ u h with hk
    have hΦu : Φ u = z := chartInv_right hΦ z
    have hkh : fderiv ℝ (chartInv hΦ) z k = h := by
      have := hchain2 u h
      rwa [hΦu] at this
    have hsymp := hΦ.symplectic u (fderiv ℝ (chartInv hΦ) z w) (fderiv ℝ (chartInv hΦ) z k)
    have e1 : fderiv ℝ Φ u (fderiv ℝ (chartInv hΦ) z w) = w := hchain1 z w
    have e2 : fderiv ℝ Φ u (fderiv ℝ (chartInv hΦ) z k) = k := hchain1 z k
    have hrw : SymplecticBracket.omega (fderiv ℝ Φ u (fderiv ℝ (chartInv hΦ) z w))
        (fderiv ℝ Φ u (fderiv ℝ (chartInv hΦ) z k)) = SymplecticBracket.omega w k := by
      rw [e1, e2]
    have hsymp' : SymplecticBracket.omega (fderiv ℝ (chartInv hΦ) z w) (fderiv ℝ (chartInv hΦ) z k) =
        SymplecticBracket.omega w k := hsymp.symm.trans hrw
    calc SymplecticBracket.omega (fderiv ℝ (chartInv hΦ) z w) h
        = SymplecticBracket.omega (fderiv ℝ (chartInv hΦ) z w) (fderiv ℝ (chartInv hΦ) z k) := by
          rw [hkh]
      _ = SymplecticBracket.omega w k := hsymp'
      _ = fderiv ℝ (eOf hκ hΦ z) z k := hω k
      _ = fderiv ℝ E u (fderiv ℝ (chartInv hΦ) z k) := by rw [hcomp]; rfl
      _ = fderiv ℝ E u h := by rw [hkh]
      _ = _ := hP h
  have hzero : fderiv ℝ (chartInv hΦ) z w - physField κ u = 0 :=
    eq_zero_of_omega fun h => by rw [omega_sub_left', hmain h, sub_self]
  exact sub_eq_zero.mp hzero

/-- **`FieldRotation` is proved**: the printed finite-action field identity in the chart, with frequencies
depending only on the action array. -/
theorem fieldRotation (hR : Reg015Input L κ hκ) : FieldRotation hΦ κ := by
  refine ⟨lamFun hκ hΦ, fun F z hz => ?_⟩
  have hex : ∃ F : Finset ℤ, ∀ n, n ∉ F → z n = 0 := ⟨F, hz⟩
  have := field_identity hκ hΦ hmod hR z F hz
  simp only [lamFun_act hκ hΦ hmod z hex]
  exact this

#print axioms fieldRotation

end Chart

end QuantumNLS.REF88FieldRotation
