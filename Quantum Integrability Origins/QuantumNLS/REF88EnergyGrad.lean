import Mathlib
import QuantumNLS.REF88Finite
import QuantumNLS.RootEnergyVectorField

/-!
# REF88EnergyGrad: minimum principle on `H¹` and density, identifying the differential of `E_F`
(R-EF8C2837, "Bounded contour energies near arbitrary mass")

Source: `source-text/chapters/global/physical_cubic.tex`, proof, paragraph "Bounded contour energies near
arbitrary mass" (printed lines 38 to 77):

  "Thus the differentiable real function `H_κ - E_F` on `H¹` has a minimum at `u_*`, and its differential
   there vanishes on every `H¹` direction.  Since `u_* ∈ H²`, the physical differential has the full `L²`
   representative `-u_*'' + 2κ|u_*|²u_*` with the real pairing `2 Re⟨·,·⟩`.  The differential of `E_F` is already
   bounded on `L²`.  Density therefore identifies their representatives and gives
   `X_{E_F}(u_*) = i u_*'' - 2iκ|u_*|²u_*`."

`fderiv_eq_omega_physField` is exactly this: for ANY real function `E` on `L²` that is differentiable at the
`H²` point `u_*`, with `E ≤ H_κ` on `H¹` and equality at `u_*`, the `L²` differential is
`dE(u_*)[h] = Ω(i u_*'' - 2iκ|u_*|²u_*, h)`, `Ω(k,h) = 2 Im⟨k,h⟩` (`SymplecticBracket.omega`).  It is applied to
the contour energy `E_F` of `REF88EnergyBound`.  Accepted modules used read-only:
`RootEnergyVectorField.root_energy_vector_field` (`H²`/`H¹` differential of the energy), `RootEnergyVariation`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate InnerProductSpace
open Filter Topology

namespace QuantumNLS.REF88EnergyGrad

open QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
open QuantumNLS.RootEnergyVariation QuantumNLS.RootEnergyVectorField
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.REF88Finite
open QuantumNLS.ProductEnergyPreparation (OneH1)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The finitely supported sequence `n ↦ if n ∈ s then f n else 0` as an element of `h^1` (F04). -/
def truncH1 (f : lp (fun _ : ℤ => ℂ) 2) (s : Finset ℤ) : h04 L 1 :=
  WSeq.mk (f04W L 1) (fun n => if n ∈ s then (f : ℤ → ℂ) n else 0) (by
    apply summable_of_ne_finset_zero (s := s)
    intro n hn
    simp [hn])

lemma fourierL2_physical_m10 (b : h04 L 1) (n : ℤ) :
    fourierL2 L (physical (m10 b)) n = b.val n := by
  rw [physical_coeff]; rfl

lemma sum_single_apply (f : lp (fun _ : ℤ => ℂ) 2) (s : Finset ℤ) (n : ℤ) :
    ((∑ i ∈ s, lp.single (E := fun _ : ℤ => ℂ) 2 i ((f : ℤ → ℂ) i) : lp (fun _ : ℤ => ℂ) 2) : ℤ → ℂ) n =
      if n ∈ s then (f : ℤ → ℂ) n else 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single, Pi.single_apply]
  by_cases hn : n ∈ s
  · rw [Finset.sum_eq_single n]
    · simp [hn]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h; exact absurd hn h
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]
    apply Finset.sum_eq_zero
    intro b hb
    have : n ≠ b := fun e => hn (e ▸ hb)
    simp [this]

/-- The `H¹` fields are dense in `L²`. -/
theorem denseRange_physical_m10 :
    DenseRange (fun b : h04 L 1 => physical (m10 b)) := by
  intro w
  set f := fourierL2 L w with hf
  have hs := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := 2) (by simp) f
  have hlim : Tendsto (fun s : Finset ℤ => (fourierL2 L).symm
      (∑ i ∈ s, lp.single (E := fun _ : ℤ => ℂ) 2 i ((f : ℤ → ℂ) i))) atTop (𝓝 w) := by
    have h2 := ((fourierL2 L).symm.continuous.tendsto f).comp hs
    have h3 : (fourierL2 L).symm f = w := by
      rw [hf]; exact LinearIsometryEquiv.symm_apply_apply _ _
    rw [h3] at h2
    exact h2
  have hmem : ∀ s : Finset ℤ, (fourierL2 L).symm
      (∑ i ∈ s, lp.single (E := fun _ : ℤ => ℂ) 2 i ((f : ℤ → ℂ) i)) ∈
        Set.range (fun b : h04 L 1 => physical (m10 b)) := by
    intro s
    refine ⟨truncH1 f s, ?_⟩
    apply (fourierL2 L).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    apply lp.ext; funext n
    rw [fourierL2_physical_m10, sum_single_apply]
    rfl
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hmem)

/-! ### `physField` is the F04 Hamiltonian vector `X = -i ∇H` -/

lemma Fh_m21' (a : h04 L 2) (n : ℤ) :
    (Fh (le_refl (1 : ℝ)) (m21 a)).val n = (Fh (by norm_num : (1 : ℝ) ≤ 2) a).val n := by
  show coeff L (nlRep L (m21 a).val) n = coeff L (nlRep L a.val) n
  rfl

lemma physField_eq_X {u : L2T L} (hu : MemHsLp L 2 u) :
    physField κ u = X κ (g2 hu) := by
  apply (fourierL2 L).injective
  apply lp.ext; funext n
  rw [fourier_physField hu, toL2ᵢ_apply_zero, Gder_val]
  simp only [X, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [physical_coeff]
  simp only [grad, lap, ContinuousLinearMap.comp_apply, WSeq.val_add,
    WSeq.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, m10_val]
  rw [Fh_m21']
  have h1 : ((h04_mono L (by norm_num : (0 : ℝ) ≤ 2 - 2)) (lapOp 2 (g2 hu))).val n =
      ((freq L n ^ 2 : ℝ) : ℂ) * (g2 hu).val n := by
    rw [show ((h04_mono L (by norm_num : (0 : ℝ) ≤ 2 - 2)) (lapOp 2 (g2 hu))).val n =
        (lapOp 2 (g2 hu)).val n from rfl, lapOp_val]
  rw [h1]
  push_cast
  ring

/-- **Minimum principle on `H¹` and density.**  Let `E : L² → ℝ` be differentiable at the `H²` point `u`,
bounded by the energy `H_κ` on `H¹`, with equality at `u`.  Then for every `L²` direction `h`,
`dE(u)[h] = Ω(i u'' - 2iκ|u|²u, h)`. -/
theorem fderiv_eq_omega_physField {u : L2T L} (hu : MemHsLp L 2 u) (E : L2T L → ℝ)
    (hE : DifferentiableAt ℝ E u)
    (hle : ∀ v : L2T L, OneH1 v → E v ≤ ChargeEnergy.energyH1 κ (v : AddCircle L → ℂ))
    (heq : E u = ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ)) (h : L2T L) :
    fderiv ℝ E u h = SymplecticBracket.omega (physField κ u) h := by
  set a : h04 L 2 := g2 hu with ha
  have hphys : physical (m10 (m21 a)) = u := by
    apply (fourierL2 L).injective
    apply lp.ext; funext n
    rw [fourierL2_physical_m10]
    rfl
  let T : h04 L 1 →L[ℝ] L2T L :=
    (((physical (L := L)).toContinuousLinearEquiv.toContinuousLinearMap).comp m10).restrictScalars ℝ
  have hT : ∀ b, T b = physical (m10 b) := fun _ => rfl
  have hTa : T (m21 a) = u := by rw [hT, hphys]
  have hmin : IsLocalMin (fun b : h04 L 1 => energy κ b - E (T b)) (m21 a) := by
    refine Eventually.of_forall fun b => ?_
    have h1 : energy κ (m21 a) - E (T (m21 a)) = 0 := by
      rw [hTa, heq, ← physical_energy κ (m21 a), hphys]
      ring
    have h2 : 0 ≤ energy κ b - E (T b) := by
      have := hle (physical (m10 b)) (physical_oneH1 b)
      rw [physical_energy κ b] at this
      rw [hT]; linarith
    show energy κ (m21 a) - E (T (m21 a)) ≤ energy κ b - E (T b)
    linarith
  have hE' : HasFDerivAt E (fderiv ℝ E u) (T (m21 a)) := by
    rw [hTa]; exact hE.hasFDerivAt
  have hf : HasFDerivAt (fun b : h04 L 1 => energy κ b - E (T b))
      (differential κ a - (fderiv ℝ E u).comp T) (m21 a) :=
    (energy_fderiv κ a).sub (hE'.comp (m21 a) T.hasFDerivAt)
  have h0 := hmin.hasFDerivAt_eq_zero hf
  have hdiff : ∀ b : h04 L 1, fderiv ℝ E u (physical (m10 b)) = differential κ a b := by
    intro b
    have := congrArg (fun A : h04 L 1 →L[ℝ] ℝ => A b) h0
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] at this
    rw [← hT]; linarith
  have h7 := (root_energy_vector_field κ a).2.2.2.2.2.2.1
  have hX := physField_eq_X (κ := κ) hu
  have hcont1 : Continuous fun k : L2T L => fderiv ℝ E u k := (fderiv ℝ E u).continuous
  have hcont2 : Continuous fun k : L2T L => SymplecticBracket.omega (physField κ u) k := by
    unfold SymplecticBracket.omega
    fun_prop
  have hdense := denseRange_physical_m10 (L := L)
  have := hdense.equalizer hcont1 hcont2 (by
    funext b
    simp only [Function.comp_apply]
    rw [hdiff b, hX]
    exact ((h7 b).2).symm)
  exact congrFun this h

#print axioms fderiv_eq_omega_physField

end QuantumNLS.REF88EnergyGrad
