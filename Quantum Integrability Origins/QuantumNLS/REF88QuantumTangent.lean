import Mathlib
import QuantumNLS.REF88FieldRotation

/-!
# REF88QuantumTangent: the tangent argument that identifies `∂h_F` with the chart frequencies (R-EF8C2837, item (iii))

Source: `source-text/chapters/global/physical_cubic.tex`, proof paragraphs "Bounded contour energies near arbitrary
mass" (printed lines 38-77, `H_κ ≥ E_F` with equality at `u_*`) and "Quantum derivatives at arbitrary finite mass"
(printed lines 296-315, "Varying actions at fixed mass and then varying all actions proportionally gives ...").

The finitely supported chart point `z` (all coordinates on `F` nonzero) is rescaled coordinatewise by
`curveY F c z s` (the `n`-th action becomes `(1 + s c_n) |z_n|²`).  Since `H_κ(Φ⁻¹ y) ≥ E_F^{(z)}(Φ⁻¹ y) = e_F(y)`
on the (finite-action, hence `H¹`) curve with equality at `s = 0` (accepted `RootEnergyMoment` second-moment
identity and `REF88EnergyBound`), the difference has a local minimum at `0`; hence if
`s ↦ H_κ(Φ⁻¹ y(s))` is differentiable at `0` its derivative equals `d e_F(z)[y'(0)] = ∑ c_n |z_n|² λ_n(z)`,
with `λ_n = REF88FieldRotation.lamAt` the frequencies of stage C (`d e_F(z)[z_n e_n] = 2 |z_n|² λ_n`):
`tangent`.  Only `Reg015Input` (finite action in every `H^s`) is used, as in stage C.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate InnerProductSpace
open Filter Topology

namespace QuantumNLS.REF88QuantumTangent

open QuantumNLS.Fourier QuantumNLS.RephasingFlow QuantumNLS.ChartFrequencies QuantumNLS.StrongSymplectic
open QuantumNLS.REF88Chart QuantumNLS.REF88Reg015 QuantumNLS.REF88Finite
open QuantumNLS.REF88EnergyContour QuantumNLS.REF88EnergyBound QuantumNLS.REF88EnergyGrad
open QuantumNLS.REF88GradStructure QuantumNLS.REF88FieldRotation
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ProductEnergyPreparation (OneH1)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- Coordinatewise real rescaling of a finitely supported point: the `n`-th action becomes
`(1 + s c_n) |z_n|²` (for `1 + s c_n ≥ 0`). -/
def curveY (F : Finset ℤ) (c : ℤ → ℝ) (z : K) (s : ℝ) : K :=
  ∑ n ∈ F, sg n (((Real.sqrt (1 + s * c n) : ℝ) : ℂ) * z n)

lemma curveY_apply (F : Finset ℤ) (c : ℤ → ℝ) (z : K) (s : ℝ) (m : ℤ) :
    (curveY F c z s : ℤ → ℂ) m = if m ∈ F then ((Real.sqrt (1 + s * c m) : ℝ) : ℂ) * z m else 0 := by
  unfold curveY
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [sg_apply]
  by_cases hm : m ∈ F
  · rw [Finset.sum_eq_single m]
    · simp [hm]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hm h
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro b hb
    have : m ≠ b := fun e => hm (e ▸ hb)
    simp [this]

lemma curveY_zero (F : Finset ℤ) (c : ℤ → ℝ) (z : K) (hz : ∀ n, n ∉ F → z n = 0) :
    curveY F c z 0 = z := by
  apply lp.ext; funext m
  rw [curveY_apply]
  by_cases hm : m ∈ F
  · simp [hm]
  · simp [hm, hz m hm]

lemma curveY_supp (F : Finset ℤ) (c : ℤ → ℝ) (z : K) (s : ℝ) {m : ℤ} (hm : m ∉ F) :
    (curveY F c z s : ℤ → ℂ) m = 0 := by
  rw [curveY_apply, if_neg hm]

lemma norm_sq_curveY (F : Finset ℤ) (c : ℤ → ℝ) (z : K) (s : ℝ) (m : ℤ)
    (hs : ∀ n ∈ F, 0 ≤ 1 + s * c n) :
    ‖(curveY F c z s : ℤ → ℂ) m‖ ^ 2 = if m ∈ F then (1 + s * c m) * ‖z m‖ ^ 2 else 0 := by
  rw [curveY_apply]
  by_cases hm : m ∈ F
  · simp only [hm, if_true, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [Real.sq_sqrt (hs m hm)]
  · simp [hm]

lemma hasDerivAt_curveY (F : Finset ℤ) (c : ℤ → ℝ) (z : K) :
    HasDerivAt (curveY F c z) (∑ n ∈ F, sg n ((((c n / 2 : ℝ)) : ℂ) * z n)) 0 := by
  unfold curveY
  apply HasDerivAt.fun_sum
  intro n hn
  have h1 : HasDerivAt (fun s : ℝ => 1 + s * c n) (c n) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (c n)).const_add 1
  have h2 : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s * c n)) (c n / (2 * Real.sqrt (1 + 0 * c n))) 0 :=
    h1.sqrt (by norm_num)
  have h3 : HasDerivAt (fun s : ℝ => ((Real.sqrt (1 + s * c n) : ℝ) : ℂ))
      (((c n / (2 * Real.sqrt (1 + 0 * c n)) : ℝ) : ℂ)) 0 := h2.ofReal_comp
  have h4 := h3.mul_const (z n)
  have hι := ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).restrictScalars ℝ).hasFDerivAt
    (x := ((Real.sqrt (1 + (0:ℝ) * c n) : ℝ) : ℂ) * z n)
  have h5 := hι.comp_hasDerivAt (0 : ℝ) h4
  have e : (c n / (2 * Real.sqrt (1 + 0 * c n))) = c n / 2 := by simp
  simpa [Function.comp_def, sg, e] using h5


section Chart

variable (hκ : 0 < κ) {Φ : L2T L → K} (hΦ : IsStronglySymplectic Φ)
  (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
  (hR : Reg015Input L κ hκ)
include hmod hR

/-- Every point of the chart with finite support is an `H¹` field (finite action lies in every `H^s`). -/
lemma oneH1_chartInv (y : K) (F : Finset ℤ) (hy : ∀ n, n ∉ F → y n = 0) :
    OneH1 (chartInv hΦ y) := by
  have hF0 : ∀ n, n ∉ F → (RootIndexedMasses.masses hκ (chartInv hΦ y)).1 n = 0 := by
    intro n hn
    rw [masses_chart hκ hΦ hmod, hy n hn]; simp
  have hu2 : MemHsLp L 2 (chartInv hΦ y) :=
    finite_action_mem_Hs hκ hR _ ⟨F, hF0⟩ 2 (by norm_num)
  exact (RootEnergyVariation.m21 (g2 hu2)).summable

/-- **The tangent argument** (printed: `h_F ≥ e_F` with equality at the base point, so the two have the
same derivative along every curve through it).  If `s ↦ H_κ(Φ⁻¹ y(s))` is differentiable at `0`, where
`y(s)` rescales the actions of the finitely supported point `z` by `1 + s c_n`, then its derivative is
`∑ c_n |z_n|² λ_n(z)`. -/
theorem tangent (F : Finset ℤ) (z : K) (hz : ∀ n, n ∉ F → z n = 0) (hne : ∀ n ∈ F, z n ≠ 0)
    (c : ℤ → ℝ) {h' : ℝ}
    (hd : HasDerivAt (fun s : ℝ =>
      ChargeEnergy.energyH1 κ ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ)) h' 0) :
    h' = ∑ n ∈ F, c n * ‖z n‖ ^ 2 * lamAt hκ hΦ z n := by
  have hex : ∃ F : Finset ℤ, ∀ n, n ∉ F → z n = 0 := ⟨F, hz⟩
  have hsupp : suppF z = F := by
    ext n; rw [mem_suppF hex]; constructor
    · intro h; by_contra hn; exact h (hz n hn)
    · intro h; exact hne n h
  -- the base point
  set u := chartInv hΦ z with hu
  have hF0 : ∀ n, n ∉ suppF z → (RootIndexedMasses.masses hκ u).1 n = 0 := by
    intro n hn
    rw [hu, masses_chart hκ hΦ hmod]
    have : z n = 0 := by
      by_contra h; exact hn ((mem_suppF hex).2 h)
    simp [this]
  have hOne : OneH1 u := oneH1_chartInv hκ hΦ hmod hR z F hz
  obtain ⟨hI, hmom⟩ := moment_of_oneH1 hκ u hOne
  have hsepmono := sep_strictMono hκ u
  -- value at the base point
  have hbase : eOf hκ hΦ z z = ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) := by
    unfold eOf
    rw [← hu, contourEnergy_eq_at_base hκ u (suppF z) hF0 hI, hmom]
  -- inequality along the curve
  have hge : ∀ s : ℝ, eOf hκ hΦ z (curveY F c z s) ≤
      ChargeEnergy.energyH1 κ ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ) := by
    intro s
    unfold eOf
    exact contourEnergy_le_energy hκ hsepmono (suppF z) _
      (oneH1_chartInv hκ hΦ hmod hR _ F (fun n hn => curveY_supp F c z s hn))
  -- derivative of e along the curve
  have hDe : DifferentiableAt ℝ (eOf hκ hΦ z) z := differentiableAt_eOf hκ hΦ hmod (fun n => rfl)
  have hy := hasDerivAt_curveY F c z
  have hz0 : curveY F c z 0 = z := curveY_zero F c z hz
  have he : HasDerivAt (fun s => eOf hκ hΦ z (curveY F c z s))
      (fderiv ℝ (eOf hκ hΦ z) z (∑ n ∈ F, sg n ((((c n / 2 : ℝ)) : ℂ) * z n))) 0 := by
    have hd' : HasFDerivAt (eOf hκ hΦ z) (fderiv ℝ (eOf hκ hΦ z) z) (curveY F c z 0) := by
      rw [hz0]; exact hDe.hasFDerivAt
    exact hd'.comp_hasDerivAt (0 : ℝ) hy
  -- evaluate the differential
  have hval : fderiv ℝ (eOf hκ hΦ z) z (∑ n ∈ F, sg n ((((c n / 2 : ℝ)) : ℂ) * z n)) =
      ∑ n ∈ F, c n * ‖z n‖ ^ 2 * lamAt hκ hΦ z n := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [D_single_formula hDe (eOf_rot hκ hΦ hmod z) n]
    have hn0 : (‖z n‖ ^ 2 : ℝ) ≠ 0 := by have := hne n hn; positivity
    have hre : (conj ((z : ℤ → ℂ) n) * (((c n / 2 : ℝ) : ℂ) * (z : ℤ → ℂ) n)).re =
        c n / 2 * ‖z n‖ ^ 2 := by
      have : conj ((z : ℤ → ℂ) n) * (((c n / 2 : ℝ) : ℂ) * (z : ℤ → ℂ) n) =
          (((c n / 2 * ‖z n‖ ^ 2 : ℝ)) : ℂ) := by
        rw [← mul_assoc, mul_comm (conj ((z : ℤ → ℂ) n)), mul_assoc, Complex.conj_mul']
        push_cast; ring
      rw [this, Complex.ofReal_re]
    rw [hre, lamAt]
    field_simp
  -- local minimum of the difference
  have hg : HasDerivAt (fun s => ChargeEnergy.energyH1 κ
        ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ) - eOf hκ hΦ z (curveY F c z s))
      (h' - ∑ n ∈ F, c n * ‖z n‖ ^ 2 * lamAt hκ hΦ z n) 0 := by
    have := hd.sub he
    rwa [hval] at this
  have hmin : IsLocalMin (fun s => ChargeEnergy.energyH1 κ
        ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ) - eOf hκ hΦ z (curveY F c z s)) 0 := by
    refine Filter.Eventually.of_forall fun s => ?_
    have h0 : ChargeEnergy.energyH1 κ
        ((chartInv hΦ (curveY F c z 0) : L2T L) : AddCircle L → ℂ) - eOf hκ hΦ z (curveY F c z 0) = 0 := by
      rw [hz0, hbase, ← hu]; ring
    show (ChargeEnergy.energyH1 κ
        ((chartInv hΦ (curveY F c z 0) : L2T L) : AddCircle L → ℂ) - eOf hκ hΦ z (curveY F c z 0)) ≤
      (ChargeEnergy.energyH1 κ
        ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ) - eOf hκ hΦ z (curveY F c z s))
    rw [h0]
    linarith [hge s]
  have := hmin.hasDerivAt_eq_zero hg
  linarith

end Chart

end QuantumNLS.REF88QuantumTangent

#print axioms QuantumNLS.REF88QuantumTangent.hasDerivAt_curveY
#print axioms QuantumNLS.REF88QuantumTangent.oneH1_chartInv
#print axioms QuantumNLS.REF88QuantumTangent.tangent
