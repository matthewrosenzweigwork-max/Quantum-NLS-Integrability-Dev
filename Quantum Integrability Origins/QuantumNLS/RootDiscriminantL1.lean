import Mathlib
import QuantumNLS.L2SpatialTransfer
import QuantumNLS.RootDiscriminant

/-!
# R-7E0532E7: realness and `det M = 1` for the Carathéodory solutions (`L¹` coefficients, hence every `L²` class)

For a profile `v` that is interval integrable on `[0,L]` (every `L²` class pulled back to the period, `L2SpatialTransfer`)
let `M = L1SpatialTransfer.transfer (balCoef κ v z)` be the Volterra-series (Carathéodory) fundamental matrix.

* `transfer_symm`: for REAL `t`, `M(x,t) = P conj(M(x,t)) P` on `[0,L]` (both solve the same integral equation; uniqueness
  `L1SpatialTransfer.fundamental_spec`), hence **`Δ_v(t) = tr M(L,t)` is real** (`discriminant_im_eq_zero_L1`).
* `det_transfer`: **`det M(x,z) = 1`** for all `z ∈ ℂ`, `x ∈ [0,L]`: the entries are absolutely continuous
  (`ac_transfer`, Lipschitz entry maps), the determinant is an absolutely continuous function with a.e. derivative
  `tr(A)·det = 0` (`ae_hasDerivAt_transfer`), so it is constant (`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`).
* `norm_sq_sub_eq_one_L1`: `|M₀₀|² - |M₀₁|² = 1` for real `t`.
* Corollaries for `L2SpatialTransfer.spatialTransfer/discriminant` of an arbitrary `L²(𝕋_L)` class.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer QuantumNLS.RootDiscriminant

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.RootDiscriminantL1

variable {L : ℝ} {v : ℝ → ℂ}

theorem intervalIntegrable_balCoef (hv : IntervalIntegrable v volume 0 L) (κ : ℝ) (z : ℂ) :
    IntervalIntegrable (balCoef κ v z) volume 0 L :=
  QuantumNLS.L2SpatialTransfer.intervalIntegrable_coef hv _ _ z

/-- The Carathéodory fundamental matrix. -/
def TT (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) : ℝ → Mat2 := transfer (balCoef κ v z)

/-- **Realness structure** `M = P conj(M) P` on `[0,L]` for real `t`. -/
theorem transfer_symm (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L) (κ t : ℝ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) L) :
    cswapCLM (TT κ v (t : ℂ) x) = TT κ v (t : ℂ) x := by
  have hA := intervalIntegrable_balCoef hv κ (t : ℂ)
  have hc : ContinuousOn (TT κ v (t : ℂ)) (Icc 0 L) := continuousOn_transfer hL hA
  have hcs : ContinuousOn (fun y => cswapCLM (TT κ v (t : ℂ) y)) (Icc 0 L) := cswapCLM.continuous.comp_continuousOn hc
  have hint : ∀ y ∈ Icc (0 : ℝ) L, cswapCLM (TT κ v (t : ℂ) y) =
      1 + ∫ s in (0 : ℝ)..y, balCoef κ v (t : ℂ) s * cswapCLM (TT κ v (t : ℂ) s) := by
    intro y hy
    have h1 : TT κ v (t : ℂ) y = 1 + ∫ s in (0 : ℝ)..y, balCoef κ v (t : ℂ) s * TT κ v (t : ℂ) s :=
      transfer_integral_eq hL hA hy
    have hAy : IntervalIntegrable (fun s => balCoef κ v (t : ℂ) s * TT κ v (t : ℂ) s) volume 0 y := by
      have hsub : uIcc (0 : ℝ) y ⊆ uIcc 0 L := by
        rw [uIcc_of_le hy.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hy.2
      exact (hA.mono_set hsub).mul_continuousOn (by
        have := hc.mono (by rw [uIcc_of_le hy.1]; exact Icc_subset_Icc_right hy.2 : uIcc (0 : ℝ) y ⊆ Icc 0 L)
        exact this)
    have h2 := cswapCLM.intervalIntegral_comp_comm (μ := volume) (a := 0) (b := y) hAy
    rw [h1, map_add, cswap_one]
    refine congrArg (fun w => 1 + w) ?_
    exact h2.symm.trans (intervalIntegral.integral_congr (fun s _ => cswap_mul_coef κ v t s _))
  have hEq := (fundamental_spec hL hA).2.2.2 _ hcs hint
  exact hEq hx

theorem transfer_symm_apply (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L) (κ t : ℝ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) L) (i j : Fin 2) :
    TT κ v (t : ℂ) x i j = conj (TT κ v (t : ℂ) x i.rev j.rev) := by
  have := transfer_symm hL hv κ t hx
  calc TT κ v (t : ℂ) x i j = (cswapCLM (TT κ v (t : ℂ) x)) i j := by rw [this]
    _ = _ := cswapCLM_apply _ _ _

/-- The real discriminant of the Carathéodory solution. -/
def discL1 (L κ : ℝ) (v : ℝ → ℂ) (z : ℂ) : ℂ := (TT κ v z L).trace

theorem discriminant_im_eq_zero_L1 (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L) (κ t : ℝ) :
    (discL1 L κ v (t : ℂ)).im = 0 := by
  have h11 := transfer_symm_apply hL hv κ t (x := L) ⟨hL, le_rfl⟩ 1 1
  have hr1 : (1 : Fin 2).rev = 0 := rfl
  simp only [hr1] at h11
  unfold discL1
  rw [Matrix.trace_fin_two, h11]
  simp

/-! ### Determinant one -/

theorem det_transfer (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L) (κ : ℝ) (z : ℂ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) L) : (TT κ v z x).det = 1 := by
  have hA := intervalIntegrable_balCoef hv κ z
  have hAC := ac_transfer hL hA
  have hder := ae_hasDerivAt_transfer hL hA
  set M := TT κ v z with hM
  have hent : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun y => M y i j) 0 L := by
    intro i j
    exact ((entryCLM i j).lipschitz).comp_absolutelyContinuousOnInterval hAC
  have hg : AbsolutelyContinuousOnInterval (fun y => (M y).det) 0 L := by
    have hfun : (fun y => (M y).det) = fun y => M y 0 0 * M y 1 1 - M y 0 1 * M y 1 0 := by
      funext y; rw [Matrix.det_fin_two]
    rw [hfun]
    exact ((hent 0 0).smul (hent 1 1)).sub ((hent 0 1).smul (hent 1 0))
  have hae : ∀ᵐ y, y ∈ uIcc (0 : ℝ) L → HasDerivAt (fun s => (M s).det) 0 y := by
    have := (ae_restrict_iff' measurableSet_Icc).1 hder
    filter_upwards [this] with y hy hyu
    rw [uIcc_of_le hL] at hyu
    have hd := hy hyu
    have e : ∀ i j, HasDerivAt (fun s => M s i j) ((balCoef κ v z y * M y) i j) y :=
      fun i j => hasDerivAt_entry hd i j
    have h1 := ((e 0 0).mul (e 1 1)).sub ((e 0 1).mul (e 1 0))
    have hfun : (fun s => (M s).det) = fun s => M s 0 0 * M s 1 1 - M s 0 1 * M s 1 0 := by
      funext s; rw [Matrix.det_fin_two]
    rw [hfun]
    refine h1.congr_deriv ?_
    simp only [balCoef, coef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  obtain ⟨C, hC⟩ := hg.const_of_ae_hasDerivAt_zero hae
  have h0 : (M 0).det = 1 := by
    have := transfer_integral_eq hL hA (x := 0) ⟨le_rfl, hL⟩
    simp [hM, TT, this]
  have hxu : x ∈ uIcc (0 : ℝ) L := by rw [uIcc_of_le hL]; exact hx
  have h00 : (0 : ℝ) ∈ uIcc (0 : ℝ) L := by rw [uIcc_of_le hL]; exact ⟨le_rfl, hL⟩
  rw [hC x hxu, ← hC 0 h00, h0]

theorem norm_sq_sub_eq_one_L1 (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L) (κ t : ℝ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) L) :
    ‖TT κ v (t : ℂ) x 0 0‖ ^ 2 - ‖TT κ v (t : ℂ) x 0 1‖ ^ 2 = 1 := by
  have hd := det_transfer hL hv κ (t : ℂ) hx
  rw [Matrix.det_fin_two] at hd
  have h11 := transfer_symm_apply hL hv κ t hx 1 1
  have h10 := transfer_symm_apply hL hv κ t hx 1 0
  have hr1 : (1 : Fin 2).rev = 0 := rfl
  have hr0 : (0 : Fin 2).rev = 1 := rfl
  simp only [hr1, hr0] at h11 h10
  rw [h11, h10] at hd
  have : ((‖TT κ v (t : ℂ) x 0 0‖ ^ 2 - ‖TT κ v (t : ℂ) x 0 1‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hd, Complex.mul_conj, Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq]
  exact_mod_cast this

/-! ### The `L²(𝕋_L)` class -/

section L2

variable [Fact (0 < L)]

open QuantumNLS.L2SpatialTransfer in
theorem L2_det (κ : ℝ) (u : QuantumNLS.PhysicalTensor.L2T L) (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    (QuantumNLS.L2SpatialTransfer.spatialTransfer κ u z x).det = 1 :=
  det_transfer (Fact.out : 0 < L).le (QuantumNLS.L2SpatialTransfer.intervalIntegrable_profile u) κ z hx

open QuantumNLS.L2SpatialTransfer in
theorem L2_discriminant_im_eq_zero (κ t : ℝ) (u : QuantumNLS.PhysicalTensor.L2T L) :
    (QuantumNLS.L2SpatialTransfer.discriminant κ u (t : ℂ)).im = 0 :=
  discriminant_im_eq_zero_L1 (Fact.out : 0 < L).le (QuantumNLS.L2SpatialTransfer.intervalIntegrable_profile u) κ t

end L2

#print axioms det_transfer
#print axioms discriminant_im_eq_zero_L1
#print axioms norm_sq_sub_eq_one_L1

end QuantumNLS.RootDiscriminantL1
