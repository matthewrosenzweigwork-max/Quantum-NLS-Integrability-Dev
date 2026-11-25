import Mathlib
import QuantumNLS.REF88FieldRotation
import QuantumNLS.ActualGapR26
import QuantumNLS.RootMassScaling

/-!
# REF88QuantumDef: the quantum objects `ℰ`, `𝒯`, `W`, `ω_{nj}` of R-EF8C2837 as Lean objects (item (iii))

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), theorem statement lines 28-86
and proof paragraph "Quantum derivatives at arbitrary finite mass" (printed lines 215-315).

Printed objects -> Lean (all REUSED from accepted modules, none re-defined):
* the normalized quantum-derived spectral measure with indexed probabilities `x` at effective coupling `K`:
  `F04SelBand.Mu hK v = PhysicalQuantumMeasure.measure hK v` for a unit profile `v` (`‖v‖ = 1`) with
  `F04SelBand.II hK v n = x n` (accepted R-063C168E scalar uniqueness: the measure depends only on `x`);
* its increasing quantile `Q = QuantileTransport.qm`, and `ℰ = ∫_0^1 Q²` : `qEnergy`;
* the response `W` of the quadratic bulk-response form equation `eq:global-quantum-response` (accepted
  DEF-052 `BulkResponseForm.BulkResponseData.IsResponse`, existence/uniqueness
  `BulkResponseRiesz.existsUnique_response`), and `𝒯 = 2ℰ - 2L ∫_0^1 Q W` : `qT`;
* the actual gap data `ω_{ab} = 4π ∫_b^a f_ext(x(λ)) dλ` of the accepted R-C455C541 / R-C88B5D59 /
  R-1E0C40B3: `ActualGapDataR26.Data` (response, pullback `f`, phase inverse `x(λ)`) and `Data.omega a b`;
  `omega_swap` is the printed orientation antisymmetry.
`Efun L K x` is the function `(K, x) ↦ ℰ` on the whole parameter set (value `0` where no profile exists);
`Efun_eq` is the statement that it is `qEnergy (Mu hK v)` for every unit profile `v` with indexed masses `x`.

Printed `h_F(a) = m ℰ(κ m, a/m)` (the physical energy; "The physical energy is h_F(a) = mℰ(κm, a/m)") is
`energy_eq_mass_mul_qEnergy`: for an `H¹` field `u ≠ 0` of mass `m = ‖u‖²`, `H_κ(u) = m ℰ(μ_{κm, u/√m})`,
from the accepted amplitude scaling `RootMassScaling.measure_smul` and the accepted second-moment identity
`RootEnergyMoment.root_energy_moment` (via `REF88EnergyBound.moment_of_oneH1`) and `QuantileTransport.map_qm`.
`II_unitDir` is the printed full-field scaling of the indexed probabilities (`I_n^{(κ)}(u) = m I_n^{(κm)}(u/√m)`).

No held contract is imported (no LNS/EXT-005 held part, DEF-035, DEF-044, HeldGP14Tonelli, RegularCut, DEF-024).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory

namespace QuantumNLS.REF88QuantumDef

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.QuantileTransport (qm)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.BulkResponseForm (BulkResponseData L2Unit)
open QuantumNLS.ActualGapDataR26 (Data)

variable {L : ℝ} [Fact (0 < L)]

/-- `ℰ(μ) = ∫_0^1 Q²` where `Q = qm μ` is the increasing quantile of `μ`. -/
def qEnergy (μ : Measure ℝ) : ℝ := ∫ t, (qm μ t) ^ 2 ∂uI

/-- `𝒯 = 2ℰ - 2L ∫_0^1 Q W` for the bulk response data `D` and a response `W`. -/
def qT (D : BulkResponseData) (W : L2Unit) : ℝ :=
  2 * qEnergy D.μ - 2 * D.L * ∫ t, qm D.μ t * (W : ℝ → ℝ) t ∂uI

theorem qEnergy_eq_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    qEnergy μ = ∫ t, t ^ 2 ∂μ := by
  unfold qEnergy
  have h := QuantileTransport.map_qm μ
  have hm := QuantileTransport.measurable_qm μ
  conv_rhs => rw [← h]
  rw [integral_map hm.aemeasurable (by fun_prop)]
  rfl

/-- amplitude scaling of the measure at the unit profile -/
theorem measure_unitDir {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    (hK : 0 < κ * ‖u‖ ^ 2) :
    Mu hκ u = ENNReal.ofReal (‖u‖ ^ 2) • Mu hK (FullMass.unitDir u) := by
  have hc : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hu)
  have h := RootMassScaling.measure_smul hκ ((‖u‖ : ℝ) : ℂ) hc (FullMass.unitDir u)
  rw [FullMass.smul_unitDir hu] at h
  have hn : ‖((‖u‖ : ℝ) : ℂ)‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have key : ∀ (K1 K2 : ℝ) (e : K1 = K2) (h1 : 0 < K1) (h2 : 0 < K2) (v : L2T L),
      Mu h1 v = Mu h2 v := by
    intro K1 K2 e h1 h2 v; subst e; rfl
  show PhysicalQuantumMeasure.measure hκ u = _
  rw [h]
  have e1 : ENNReal.ofReal (‖((‖u‖ : ℝ) : ℂ)‖ ^ 2) = ENNReal.ofReal (‖u‖ ^ 2) := by rw [hn]
  have e2 := key (κ * ‖((‖u‖ : ℝ) : ℂ)‖ ^ 2) (κ * ‖u‖ ^ 2) (by rw [hn])
    (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) hK (FullMass.unitDir u)
  rw [e1]
  exact congrArg _ e2


theorem Mu_congr_coupling {K1 K2 : ℝ} (e : K1 = K2) (h1 : 0 < K1) (h2 : 0 < K2) (v : L2T L) :
    Mu h1 v = Mu h2 v := by subst e; rfl

/-- `ω_{ab} = -ω_{ba}` (reversing the integration interval). -/
theorem omega_swap {κ : ℝ} {hκ : 0 < κ} {u : L2T L} (D : Data hκ u) (a b : ℤ) :
    D.omega a b = - D.omega b a := by
  unfold Data.omega
  rw [intervalIntegral.integral_symm (a := (b : ℝ)) (b := (a : ℝ))]
  ring

theorem II_unitDir {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    (hK : 0 < κ * ‖u‖ ^ 2) (n : ℤ) :
    II hκ u n = ‖u‖ ^ 2 * II hK (FullMass.unitDir u) n := by
  have hc : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hu)
  have h := RootMassScaling.masses_smul hκ ((‖u‖ : ℝ) : ℂ) hc (FullMass.unitDir u) n
  rw [FullMass.smul_unitDir hu] at h
  have hn : ‖((‖u‖ : ℝ) : ℂ)‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hm : ∀ (K1 K2 : ℝ) (e : K1 = K2) (h1 : 0 < K1) (h2 : 0 < K2) (v : L2T L),
      (RootIndexedMasses.masses h1 v).1 n = (RootIndexedMasses.masses h2 v).1 n := by
    intro K1 K2 e h1 h2 v; subst e; rfl
  show (RootIndexedMasses.masses hκ u).1 n = _
  rw [h]
  have e2 := hm (κ * ‖((‖u‖ : ℝ) : ℂ)‖ ^ 2) (κ * ‖u‖ ^ 2) (by rw [hn])
    (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) hK (FullMass.unitDir u)
  rw [e2, hn]

/-- **`H_κ(u) = m ℰ(κ m, u/√m)`** (printed `h_F(a) = m ℰ(κ m, a/m)`): the physical energy of an `H¹` field of
mass `m = ‖u‖²` is `m` times the second moment of the quantile of the normalized quantum measure at coupling
`K = κ m`. -/
theorem energy_eq_mass_mul_qEnergy {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    (hH : ProductEnergyPreparation.OneH1 u) (hK : 0 < κ * ‖u‖ ^ 2) :
    ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) =
      ‖u‖ ^ 2 * qEnergy (Mu hK (FullMass.unitDir u)) := by
  obtain ⟨-, hmom⟩ := REF88EnergyBound.moment_of_oneH1 hκ u hH
  rw [← hmom]
  have : IsProbabilityMeasure (Mu hK (FullMass.unitDir u)) :=
    F04SelBand.Mu_prob hK _ (FullMass.norm_unitDir hu)
  rw [qEnergy_eq_moment]
  show ∫ t, t ^ 2 ∂(Mu hκ u) = _
  rw [measure_unitDir hκ hu hK, integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]


theorem II_congr_coupling {K1 K2 : ℝ} (e : K1 = K2) (h1 : 0 < K1) (h2 : 0 < K2) (v : L2T L) (n : ℤ) :
    II h1 v n = II h2 v n := by subst e; rfl

variable (L) in
/-- The quantum energy `ℰ(K, x)`: `∫_0^1 Q²` for the quantile `Q` of the normalized quantum measure at
effective coupling `K` with indexed probabilities `x` (any unit profile `v` with `I_n^{(K)}(v) = x_n`; the
measure does not depend on the choice by scalar uniqueness, `Efun_eq`).  `0` if there is no such profile. -/
def Efun (K : ℝ) (x : ℤ → ℝ) : ℝ := by
  classical
  exact if h : ∃ v : L2T L, ‖v‖ = 1 ∧ ∃ hK : 0 < K, ∀ n, II hK v n = x n then
    qEnergy (Mu h.choose_spec.2.choose h.choose) else 0

theorem Efun_eq {K : ℝ} (hK : 0 < K) {x : ℤ → ℝ} {v : L2T L} (hv : ‖v‖ = 1)
    (hx : ∀ n, II hK v n = x n) : Efun L K x = qEnergy (Mu hK v) := by
  classical
  have h : ∃ v : L2T L, ‖v‖ = 1 ∧ ∃ hK : 0 < K, ∀ n, II hK v n = x n := ⟨v, hv, hK, hx⟩
  unfold Efun
  rw [dif_pos h]
  obtain ⟨-, hK', hx'⟩ := h.choose_spec
  have hm : Mu hK' h.choose = Mu hK v :=
    (RootScalarUniquenessR28.root_scalar_uniqueness (L := L) hK).1 _ _
      (fun n => (hx' n).trans (hx n).symm)
  exact congrArg qEnergy hm

theorem Efun_eq_unitDir {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (hK : 0 < κ * ‖u‖ ^ 2) {K : ℝ}
    (hKK : K = κ * ‖u‖ ^ 2) {x : ℤ → ℝ}
    (hx : ∀ n, II hκ u n = ‖u‖ ^ 2 * x n) :
    ∃ hK' : 0 < K, Efun L K x = qEnergy (Mu hK' (FullMass.unitDir u)) := by
  have hK' : 0 < K := hKK ▸ hK
  refine ⟨hK', Efun_eq hK' (FullMass.norm_unitDir hu) (fun n => ?_)⟩
  have h1 := II_unitDir hκ hu hK n
  have h2 := II_congr_coupling hKK.symm hK hK' (FullMass.unitDir u) n
  have hm : (0 : ℝ) < ‖u‖ ^ 2 := by have := norm_pos_iff.2 hu; positivity
  rw [← h2]
  have := hx n
  rw [h1] at this
  exact mul_left_cancel₀ hm.ne' this

end QuantumNLS.REF88QuantumDef

#print axioms QuantumNLS.REF88QuantumDef.qEnergy_eq_moment
#print axioms QuantumNLS.REF88QuantumDef.measure_unitDir
#print axioms QuantumNLS.REF88QuantumDef.omega_swap
#print axioms QuantumNLS.REF88QuantumDef.II_unitDir
#print axioms QuantumNLS.REF88QuantumDef.energy_eq_mass_mul_qEnergy
#print axioms QuantumNLS.REF88QuantumDef.Efun_eq
#print axioms QuantumNLS.REF88QuantumDef.Efun_eq_unitDir
