import Mathlib
import QuantumNLS.PlaneWaveChamber
import QuantumNLS.OneParticleBorn
import QuantumNLS.NormalizedTransfer

/-!
# The product symbol of a plane wave in closed form

Source: `ROOT_spectral_measure.tex`, `prop:root-free`, plane-wave clause: for `u = L^{-1/2}e^{ipx}`, `p = 2πm/L`,
`s(z;u) = e^{i(z−p)L/2}(e^{iLR/2} + e^{−iLR/2})`, `R = √((z−p)² − 4κ/L)`.  Here the statement is proved in the equivalent root form
`s(z;u) = e^{ρ₁L} + e^{ρ₂L}` for any `ρ₁ + ρ₂ = i(z−p)`, `ρ₁ρ₂ = −κ/L`, `ρ₁ ≠ ρ₂`.

* `torus_double`: iterated torus integrals of `conj Φ(x) K(rep x, rep y) Φ(y)` equal the cube integrals;
* `kps_plane`: `⟨u^{⊗r}, K_{r,z}u^{⊗r}⟩ = L^{-r}( Jc_r(L; z−p) + e^{izL} Jc_r(L; −(z−p)) )` for `u = modeLp L m` (alternating chamber integrals; the plus/minus
  kernels of `BethePhysicalTransfer.physicalKernel`, derived from the frozen literal integral kernels);
* `symbol_plane`: `productSymbol L κ u z = e^{ρ₁L} + e^{ρ₂L}` (`PlaneWaveChamber.Jc_eq_Rr`, `VolterraSeries.hasSum_Phi`, `sym_closed`).
No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.PlaneWaveSymbol

open QuantumNLS.PhysicalTensor (L2T L2TN prodLp prodFun memLp_prodFun torusPiMeasure)
open QuantumNLS.Fourier (mode modeLp coeFn_modeLp mode_coe continuous_mode)
open QuantumNLS.BetheWeakGradient (representatives cubeMeasure representatives_coe_ae torus_integral_cube
  measurable_representatives)
open QuantumNLS.BetheTransferKernelAdjoint (rawPlus rawMinus PlusOrder MinusOrder displacement)
open QuantumNLS.PlaneWaveChamber (Jc integrable_bdd measurable_param Jc_eq_Rr)
open QuantumNLS.NormalizedTransfer (orderedKernel productSymbol symbolTerm)
open QuantumNLS.KernelDefinition (kernelProductSymbol)
open QuantumNLS.HighMomentsOps (wvec)
open QuantumNLS.VolterraSeries (Rr hasSum_Phi sym_closed Phi)

variable {L : ℝ} [Fact (0 < L)]

/-- The momentum `p = 2πm/L`. -/
def pm (L : ℝ) (m : ℤ) : ℝ := 2 * Real.pi * m / L

/-- `Φ(x) = ∏_j e_m(x_j)` on the torus. -/
def phiT (L : ℝ) [Fact (0 < L)] (m : ℤ) (r : ℕ) (x : Fin r → AddCircle L) : ℂ := ∏ j, mode L m (x j)

theorem measurable_phiT (m : ℤ) (r : ℕ) : Measurable (phiT L m r) := by
  unfold phiT
  have : Continuous (fun x : Fin r → AddCircle L => ∏ j, mode L m (x j)) :=
    continuous_finsetProd _ (fun j _ => (continuous_mode (L := L) m).comp (continuous_apply j))
  exact this.measurable

theorem phiT_coe (m : ℤ) (r : ℕ) (x : Fin r → ℝ) :
    phiT L m r (fun j => (x j : AddCircle L)) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ^ r * Complex.exp (Complex.I * (pm L m : ℂ) * ((∑ j, x j : ℝ) : ℂ)) := by
  unfold phiT
  simp_rw [mode_coe]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Complex.exp_sum]
  have hexp : ∑ j : Fin r, (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (x j : ℂ) / (L : ℂ)) =
      Complex.I * (pm L m : ℂ) * ((∑ j, x j : ℝ) : ℂ) := by
    unfold pm
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hexp]

theorem prodLp_ae (m : ℤ) (r : ℕ) :
    (prodLp (fun _ : Fin r => modeLp L m) : (Fin r → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L r] phiT L m r := by
  have h1 := (memLp_prodFun (fun _ : Fin r => modeLp L m)).coeFn_toLp
  have h2 : ∀ᵐ y ∂(torusPiMeasure L r), ∀ j : Fin r, (modeLp L m : AddCircle L → ℂ) (y j) = mode L m (y j) :=
    ae_all_iff.2 (fun j => (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure (AddCircle L))) j).ae
      (QuantumNLS.Fourier.coeFn_modeLp L m))
  filter_upwards [h1, h2] with y hy1 hy2
  have : (prodLp (fun _ : Fin r => modeLp L m) : (Fin r → AddCircle L) → ℂ) y =
      prodFun (fun _ : Fin r => modeLp L m) y := hy1
  rw [this]
  unfold prodFun phiT
  exact Finset.prod_congr rfl (fun j _ => hy2 j)

/-! ### Torus double integrals as cube integrals -/

theorem torus_double (r : ℕ) (Φ : (Fin r → AddCircle L) → ℂ) (hΦ : Measurable Φ)
    (K : (Fin r → ℝ) → (Fin r → ℝ) → ℂ) (hK : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => K p.1 p.2)) :
    ∫ x, ∫ y, conj (Φ x) * K (representatives L x) (representatives L y) * Φ y ∂torusPiMeasure L r ∂torusPiMeasure L r =
      ∫ x, ∫ y, conj (Φ (fun j => (x j : AddCircle L))) * K x y * Φ (fun j => (y j : AddCircle L))
        ∂cubeMeasure r L ∂cubeMeasure r L := by
  have hrep := measurable_representatives (L := L) r
  have hin : ∀ x : Fin r → AddCircle L, ∫ y, conj (Φ x) * K (representatives L x) (representatives L y) * Φ y ∂torusPiMeasure L r =
      ∫ y, conj (Φ x) * K (representatives L x) y * Φ (fun j => (y j : AddCircle L)) ∂cubeMeasure r L := by
    intro x
    have hm : Measurable (fun y : Fin r → AddCircle L =>
        conj (Φ x) * K (representatives L x) (representatives L y) * Φ y) :=
      (measurable_const.mul (hK.comp (measurable_const.prodMk hrep))).mul hΦ
    rw [show torusPiMeasure L r = (volume : Measure (Fin r → AddCircle L)) from rfl,
      torus_integral_cube L _ hm.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [representatives_coe_ae r L] with y hy
    simp only [hy]
  simp_rw [hin]
  set H : (Fin r → AddCircle L) → ℂ := fun x =>
    ∫ y, conj (Φ x) * K (representatives L x) y * Φ (fun j => (y j : AddCircle L)) ∂cubeMeasure r L with hH
  have hHm : Measurable H := by
    have : Measurable (fun p : (Fin r → AddCircle L) × (Fin r → ℝ) =>
        conj (Φ p.1) * K (representatives L p.1) p.2 * Φ (fun j => (p.2 j : AddCircle L))) := by
      have e1 : Measurable (fun p : (Fin r → AddCircle L) × (Fin r → ℝ) => conj (Φ p.1)) :=
        (Complex.continuous_conj.measurable).comp (hΦ.comp measurable_fst)
      have e2 : Measurable (fun p : (Fin r → AddCircle L) × (Fin r → ℝ) => K (representatives L p.1) p.2) :=
        hK.comp ((hrep.comp measurable_fst).prodMk measurable_snd)
      have e3 : Measurable (fun p : (Fin r → AddCircle L) × (Fin r → ℝ) => Φ (fun j => (p.2 j : AddCircle L))) :=
        hΦ.comp (by
          refine measurable_pi_iff.2 (fun j => ?_)
          exact (AddCircle.measurePreserving_mk L 0).measurable.comp ((measurable_pi_apply j).comp measurable_snd))
      exact (e1.mul e2).mul e3
    exact measurable_param (ν := cubeMeasure r L) this
  show ∫ x, H x ∂torusPiMeasure L r = _
  rw [show torusPiMeasure L r = (volume : Measure (Fin r → AddCircle L)) from rfl,
    torus_integral_cube L H hHm.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [representatives_coe_ae r L] with x hx
  simp only [hH, hx]

/-! ### Phases -/

theorem sum_sub_eq {r : ℕ} (x y : Fin r → ℝ) : (∑ j, y j) - (∑ j, x j) = -displacement x y := by
  unfold displacement
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem phase_plus (m : ℤ) {r : ℕ} (z : ℂ) (x y : Fin r → ℝ) :
    Complex.exp (Complex.I * (pm L m : ℂ) * (((∑ j, y j) - (∑ j, x j) : ℝ) : ℂ)) * rawPlus L z x y =
      rawPlus L (z - (pm L m : ℂ)) x y := by
  classical
  unfold rawPlus
  split_ifs with h
  · rw [← Complex.exp_add, sum_sub_eq]
    congr 1
    push_cast
    ring
  · simp

theorem phase_minus (m : ℤ) {r : ℕ} (z : ℂ) (x y : Fin r → ℝ) :
    Complex.exp (Complex.I * (pm L m : ℂ) * (((∑ j, y j) - (∑ j, x j) : ℝ) : ℂ)) * rawMinus L z x y =
      Complex.exp (Complex.I * z * L) * rawPlus L (-(z - (pm L m : ℂ))) y x := by
  classical
  unfold rawMinus rawPlus MinusOrder
  split_ifs with h
  · rw [← Complex.exp_add, ← Complex.exp_add]
    have : (∑ j, y j) - (∑ j, x j) = displacement y x := by
      unfold displacement
      rw [← Finset.sum_sub_distrib]
    rw [this]
    unfold displacement
    congr 1
    push_cast
    ring
  · simp

theorem conj_phiT (m : ℤ) (r : ℕ) (x : Fin r → ℝ) :
    conj (phiT L m r (fun j => (x j : AddCircle L))) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ^ r * Complex.exp (-(Complex.I * (pm L m : ℂ) * ((∑ j, x j : ℝ) : ℂ))) := by
  rw [phiT_coe, map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_ofReal]

theorem integrand_plus (m : ℤ) (r : ℕ) (z : ℂ) (x y : Fin r → ℝ) :
    conj (phiT L m r (fun j => (x j : AddCircle L))) * rawPlus L z x y * phiT L m r (fun j => (y j : AddCircle L)) =
      ((((L⁻¹) ^ r : ℝ)) : ℂ) * rawPlus L (z - (pm L m : ℂ)) x y := by
  rw [conj_phiT, phiT_coe, ← phase_plus (L := L) m z x y]
  have hL : 0 < L := Fact.out
  have hr : (Real.sqrt L)⁻¹ * (Real.sqrt L)⁻¹ = L⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hL.le]
  have h2 : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ^ r * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ^ r = (((L⁻¹) ^ r : ℝ) : ℂ) := by
    rw [← mul_pow, ← Complex.ofReal_mul, hr, Complex.ofReal_pow]
  have h3 : Complex.exp (-(Complex.I * (pm L m : ℂ) * ((∑ j, x j : ℝ) : ℂ))) *
      Complex.exp (Complex.I * (pm L m : ℂ) * ((∑ j, y j : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (pm L m : ℂ) * (((∑ j, y j) - (∑ j, x j) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← h2, ← h3]
  ring

theorem integrand_minus (m : ℤ) (r : ℕ) (z : ℂ) (x y : Fin r → ℝ) :
    conj (phiT L m r (fun j => (x j : AddCircle L))) * rawMinus L z x y * phiT L m r (fun j => (y j : AddCircle L)) =
      ((((L⁻¹) ^ r : ℝ)) : ℂ) * (Complex.exp (Complex.I * z * L) * rawPlus L (-(z - (pm L m : ℂ))) y x) := by
  rw [conj_phiT, phiT_coe, ← phase_minus (L := L) m z x y]
  have hL : 0 < L := Fact.out
  have hr : (Real.sqrt L)⁻¹ * (Real.sqrt L)⁻¹ = L⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hL.le]
  have h2 : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ^ r * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ^ r = (((L⁻¹) ^ r : ℝ) : ℂ) := by
    rw [← mul_pow, ← Complex.ofReal_mul, hr, Complex.ofReal_pow]
  have h3 : Complex.exp (-(Complex.I * (pm L m : ℂ) * ((∑ j, x j : ℝ) : ℂ))) *
      Complex.exp (Complex.I * (pm L m : ℂ) * ((∑ j, y j : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (pm L m : ℂ) * (((∑ j, y j) - (∑ j, x j) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← h2, ← h3]
  ring

/-! ### The coefficients `⟨u^{⊗r}, K_{r,z}u^{⊗r}⟩` -/

theorem kps_eq_inner (r : ℕ) (z : ℂ) (u : L2T L) :
    kernelProductSymbol (orderedKernel L r z) u =
      ⟪(prodLp (fun _ : Fin r => u) : L2TN L r),
        QuantumNLS.BetheTransferOperators.rawOperator L r z (prodLp (fun _ : Fin r => u))⟫_ℂ := by
  have h := QuantumNLS.BethePhysicalTransfer.inner_physicalKernel L r z (wvec r u) (wvec r u)
  have hpos : QuantumNLS.BethePhysicalTransfer.positionInclusion L r (wvec r u) = prodLp (fun _ : Fin r => u) :=
    QuantumNLS.PhysicalTensor.physUnitary_ptprod (fun _ : Fin r => u)
  have e : kernelProductSymbol (orderedKernel L r z) u =
      ⟪wvec r u, QuantumNLS.BethePhysicalTransfer.physicalKernel L r z (wvec r u)⟫_ℂ := rfl
  rw [e, h, hpos]

theorem replace_psi (m : ℤ) (r : ℕ) (K : (Fin r → ℝ) → (Fin r → ℝ) → ℂ) :
    ∫ x, ∫ y, conj ((prodLp (fun _ : Fin r => modeLp L m) : (Fin r → AddCircle L) → ℂ) x) *
        K (representatives L x) (representatives L y) * (prodLp (fun _ : Fin r => modeLp L m) : (Fin r → AddCircle L) → ℂ) y
        ∂torusPiMeasure L r ∂torusPiMeasure L r =
      ∫ x, ∫ y, conj (phiT L m r x) * K (representatives L x) (representatives L y) * phiT L m r y
        ∂torusPiMeasure L r ∂torusPiMeasure L r := by
  have hae := prodLp_ae (L := L) m r
  have hin : ∀ x, ∫ y, conj ((prodLp (fun _ : Fin r => modeLp L m) : (Fin r → AddCircle L) → ℂ) x) *
        K (representatives L x) (representatives L y) * (prodLp (fun _ : Fin r => modeLp L m) : (Fin r → AddCircle L) → ℂ) y
        ∂torusPiMeasure L r =
      ∫ y, conj ((prodLp (fun _ : Fin r => modeLp L m) : (Fin r → AddCircle L) → ℂ) x) *
        K (representatives L x) (representatives L y) * phiT L m r y ∂torusPiMeasure L r := by
    intro x
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hy]
  simp_rw [hin]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

theorem kps_plane (m : ℤ) (r : ℕ) (z : ℂ) :
    kernelProductSymbol (orderedKernel L r z) (modeLp L m) =
      ((((L⁻¹) ^ r : ℝ)) : ℂ) * (Jc L r L (z - (pm L m : ℂ)) +
        Complex.exp (Complex.I * z * L) * Jc L r L (-(z - (pm L m : ℂ)))) := by
  have hL : 0 < L := Fact.out
  rw [kps_eq_inner, QuantumNLS.BetheTransferOperators.inner_rawOperator]
  rw [replace_psi m r (fun x y => rawPlus L z x y), replace_psi m r (fun x y => rawMinus L z x y)]
  rw [torus_double r (phiT L m r) (measurable_phiT m r) (fun x y => rawPlus L z x y)
      (QuantumNLS.BetheTransferOperators.measurable_rawPlus r L z),
    torus_double r (phiT L m r) (measurable_phiT m r) (fun x y => rawMinus L z x y)
      (QuantumNLS.BetheTransferOperators.measurable_rawMinus r L z)]
  simp_rw [integrand_plus, integrand_minus]
  haveI : IsFiniteMeasure (cubeMeasure r L) := inferInstance
  have hplus : ∫ x, ∫ y, ((((L⁻¹) ^ r : ℝ)) : ℂ) * rawPlus L (z - (pm L m : ℂ)) x y ∂cubeMeasure r L ∂cubeMeasure r L =
      ((((L⁻¹) ^ r : ℝ)) : ℂ) * Jc L r L (z - (pm L m : ℂ)) := by
    simp_rw [integral_const_mul]
    rfl
  have hminus : ∫ x, ∫ y, ((((L⁻¹) ^ r : ℝ)) : ℂ) * (Complex.exp (Complex.I * z * L) *
      rawPlus L (-(z - (pm L m : ℂ))) y x) ∂cubeMeasure r L ∂cubeMeasure r L =
      ((((L⁻¹) ^ r : ℝ)) : ℂ) * (Complex.exp (Complex.I * z * L) * Jc L r L (-(z - (pm L m : ℂ)))) := by
    simp_rw [integral_const_mul]
    congr 2
    have hint : Integrable (Function.uncurry fun x y : Fin r → ℝ => rawPlus L (-(z - (pm L m : ℂ))) y x)
        ((cubeMeasure r L).prod (cubeMeasure r L)) := by
      refine integrable_bdd ?_ (B := Real.exp (L * |(-(z - (pm L m : ℂ))).im|)) (fun p => ?_)
      · exact (QuantumNLS.BetheTransferOperators.measurable_rawPlus r L _).comp measurable_swap
      · exact QuantumNLS.BetheTransferOperators.norm_rawPlus_le L hL.le _ _ _
    rw [integral_integral_swap hint]
    rfl
  rw [hplus, hminus]
  ring

/-! ### The closed form -/

theorem exp_p_L (m : ℤ) : Complex.exp (-(Complex.I * ((pm L m * L : ℝ) : ℂ))) = 1 := by
  have hL : 0 < L := Fact.out
  have : (pm L m * L : ℝ) = 2 * Real.pi * m := by unfold pm; field_simp
  rw [this]
  have h := Complex.exp_int_mul_two_pi_mul_I (-m)
  convert h using 2
  push_cast; ring

theorem symbol_plane {κ : ℝ} (hκ : κ ≠ 0) (m : ℤ) {z : ℂ} (hz : 0 < z.im) {ρ1 ρ2 : ℂ}
    (hsum : ρ1 + ρ2 = Complex.I * (z - (pm L m : ℂ)))
    (hprod : ρ1 * ρ2 = -(((κ / L : ℝ)) : ℂ)) (h12 : ρ1 ≠ ρ2) :
    productSymbol L κ (modeLp L m) z = Complex.exp (ρ1 * L) + Complex.exp (ρ2 * L) := by
  have hL : 0 < L := Fact.out
  set w : ℂ := z - (pm L m : ℂ) with hw
  have hwim : 0 < w.im := by simp [hw]; exact hz
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
  have hnw0 : -w ≠ 0 := neg_ne_zero.2 hw0
  have hc : ρ1 + ρ2 ≠ 0 := by rw [hsum]; exact mul_ne_zero Complex.I_ne_zero hw0
  have hlam : ((κ / L : ℝ) : ℂ) ≠ 0 := by
    have : κ / L ≠ 0 := div_ne_zero hκ hL.ne'
    exact_mod_cast this
  have h1 : ρ1 ≠ 0 := fun h => by rw [h, zero_mul] at hprod; exact hlam (neg_eq_zero.1 hprod.symm)
  have h2 : ρ2 ≠ 0 := fun h => by rw [h, mul_zero] at hprod; exact hlam (neg_eq_zero.1 hprod.symm)
  -- the coefficients
  have hcoef : ∀ r : ℕ, (κ : ℂ) ^ r * kernelProductSymbol (orderedKernel L r z) (modeLp L m) =
      (-(ρ1 * ρ2)) ^ r * (Rr (ρ1 + ρ2) r L + Complex.exp (Complex.I * z * L) * Rr (-(ρ1 + ρ2)) r L) := by
    intro r
    rw [kps_plane, Jc_eq_Rr hL.le hw0 r L hL.le le_rfl, Jc_eq_Rr hL.le hnw0 r L hL.le le_rfl]
    have e1 : Complex.I * w = ρ1 + ρ2 := hsum.symm
    have e2 : Complex.I * (-w) = -(ρ1 + ρ2) := by rw [← e1]; ring
    rw [e1, e2, hprod, neg_neg]
    have hk : ((κ / L : ℝ) : ℂ) ^ r = (κ : ℂ) ^ r * (((L⁻¹) ^ r : ℝ) : ℂ) := by
      push_cast; rw [div_eq_mul_inv, mul_pow, inv_pow]
    rw [hk]
    ring
  -- the two series
  have hs1 := hasSum_Phi h12 h1 h2 hc hL.le
  have hs2 := hasSum_Phi (ρ1 := -ρ1) (ρ2 := -ρ2) (by intro h; exact h12 (neg_injective h)) (neg_ne_zero.2 h1)
    (neg_ne_zero.2 h2) (by rw [← neg_add]; exact neg_ne_zero.2 hc) hL.le
  have hneg : (-ρ1) + (-ρ2) = -(ρ1 + ρ2) := by ring
  have hneg2 : -((-ρ1) * (-ρ2)) = -(ρ1 * ρ2) := by ring
  rw [hneg, hneg2] at hs2
  have hS := hs1.add (hs2.mul_left (Complex.exp (Complex.I * z * L)))
  -- shift index
  have hE : Complex.exp (Complex.I * z * L) = Complex.exp ((ρ1 + ρ2) * L) := by
    rw [hsum]
    have := exp_p_L (L := L) m
    rw [show Complex.I * (z - (pm L m : ℂ)) * (L : ℂ) = Complex.I * z * L + (-(Complex.I * ((pm L m * L : ℝ) : ℂ))) by
      push_cast; ring, Complex.exp_add, this, mul_one]
  have hsym := sym_closed h12 L
  rw [← hE] at hsym
  have hS' : HasSum (fun r : ℕ => (-(ρ1 * ρ2)) ^ r * (Rr (ρ1 + ρ2) r L + Complex.exp (Complex.I * z * L) * Rr (-(ρ1 + ρ2)) r L))
      (Complex.exp (ρ1 * L) + Complex.exp (ρ2 * L)) := by
    have := hS
    rw [hsym] at this
    convert this using 2 with r
    ring
  have hshift := (hasSum_nat_add_iff' 1).2 hS'
  have hsum2 : ∑' j : ℕ, symbolTerm L κ (modeLp L m) z (j + 1) =
      Complex.exp (ρ1 * L) + Complex.exp (ρ2 * L) - (1 + Complex.exp (Complex.I * z * L)) := by
    have : (fun j : ℕ => symbolTerm L κ (modeLp L m) z (j + 1)) =
        fun j : ℕ => (-(ρ1 * ρ2)) ^ (j + 1) * (Rr (ρ1 + ρ2) (j + 1) L +
          Complex.exp (Complex.I * z * L) * Rr (-(ρ1 + ρ2)) (j + 1) L) := by
      funext j
      unfold symbolTerm
      rw [Complex.ofReal_pow]
      exact hcoef (j + 1)
    rw [this]
    refine (hshift.tsum_eq).trans ?_
    simp [Finset.sum_range_one, Rr]
  unfold productSymbol
  rw [hsum2]
  ring

end QuantumNLS.PlaneWaveSymbol

#print axioms QuantumNLS.PlaneWaveSymbol.torus_double
#print axioms QuantumNLS.PlaneWaveSymbol.kps_plane
#print axioms QuantumNLS.PlaneWaveSymbol.symbol_plane
