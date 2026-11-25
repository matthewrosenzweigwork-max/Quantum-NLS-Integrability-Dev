import Mathlib
import QuantumNLS.RootInteractionL1
import QuantumNLS.RootChamberIntegral

/-!
# R-7E0532E7 `eq:root-trace-symbol`, spatial side: the discriminant as a sum of iterated interval integrals

For `κ ≥ 0`, `z ∈ ℂ` and a profile `v` that is interval integrable on `[0,L]` (every `L²(𝕋_L)` class via `profile`), let
`M = TT κ v z = L1SpatialTransfer.transfer (balCoef κ v z)` (so `Δ = tr M(L)` is `L2SpatialTransfer.discriminant`).  With
`N = transfer (Bc κ v z)` the interaction-picture transfer (`RootInteractionL1.Nc_eq_transfer : Dc z x · M x = N x`):

* **`dyson_even`**: the Dyson iterates of `Bc` are `D_{2r}(x) = diag(κ^r W⁺_r(x), κ^r W⁻_r(x))` and `D_{2r+1}` off-diagonal, where
  `W⁺_r = Wr (v̄) v z r`, `W⁻_r = Wr v v̄ (−z) r` are the alternating-chamber iterated integrals of `RootChamberIntegral`.
* **`trace_eq`**: `tr M(L) = e^{-izL/2} Σ_r κ^r W⁺_r(L) + e^{izL/2} Σ_r κ^r W⁻_r(L)`, both series summable, for EVERY `z ∈ ℂ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer QuantumNLS.LinearFundamental
open QuantumNLS.RootInteractionL1 QuantumNLS.RootChamberIntegral
open QuantumNLS.RootDiscriminantBound (P1 P2)

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

local instance instPseudoMetrizableMat2RTSS : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance instENormedAddMonoidMat2RTSS : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.RootTraceSymbolSpatial

variable {L κ : ℝ} {v : ℝ → ℂ} {z : ℂ}

theorem E1c_sq (z : ℂ) (x : ℝ) : E1c z x * E1c z x = Complex.exp (Complex.I * z * x) := by
  unfold E1c a1c; rw [← Complex.exp_add]; congr 1; ring

theorem E2c_sq (z : ℂ) (x : ℝ) : E2c z x * E2c z x = Complex.exp (-(Complex.I * z * x)) := by
  unfold E2c a1c; rw [← Complex.exp_add]; congr 1; ring

theorem Bc_00 (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) (s : ℝ) : Bc κ v z s 0 0 = 0 := by simp [Bc]
theorem Bc_11 (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) (s : ℝ) : Bc κ v z s 1 1 = 0 := by simp [Bc]
theorem Bc_01 (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) (s : ℝ) :
    Bc κ v z s 0 1 = (Real.sqrt κ : ℂ) * conj (v s) * Complex.exp (Complex.I * z * s) := by
  simp [Bc, E1c_sq]
theorem Bc_10 (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) (s : ℝ) :
    Bc κ v z s 1 0 = (Real.sqrt κ : ℂ) * v s * Complex.exp (-(Complex.I * z * s)) := by
  simp [Bc, E2c_sq]

theorem mul_entry (B D : Mat2) (hB00 : B 0 0 = 0) (hB11 : B 1 1 = 0) :
    (B * D) 0 0 = B 0 1 * D 1 0 ∧ (B * D) 0 1 = B 0 1 * D 1 1 ∧
    (B * D) 1 0 = B 1 0 * D 0 0 ∧ (B * D) 1 1 = B 1 0 * D 0 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hB00, hB11]

theorem dyson_succ_entry (hB : IntervalIntegrable (Bc κ v z) volume 0 L) (hL : 0 ≤ L) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) L) (n : ℕ) (i j : Fin 2) :
    dyson (Bc κ v z) (n + 1) x i j = ∫ s in (0 : ℝ)..x, (Bc κ v z s * dyson (Bc κ v z) n s) i j := by
  have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
    rw [uIcc_of_le hx.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2
  have hi : IntervalIntegrable (fun s => Bc κ v z s * dyson (Bc κ v z) n s) volume 0 x :=
    (integrable_dyson_product hB n).mono_set hsub
  show (∫ s in (0 : ℝ)..x, Bc κ v z s * dyson (Bc κ v z) n s) i j = _
  exact (((QuantumNLS.RootDiscriminant.entryCLM i j).restrictScalars ℝ).intervalIntegral_comp_comm hi).symm

section Steps

variable (hB : IntervalIntegrable (Bc κ v z) volume 0 L) (hL : 0 ≤ L)
include hB hL

theorem dyson_succ_00 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) (n : ℕ) (F : ℝ → ℂ)
    (h : ∀ t ∈ Icc (0 : ℝ) L, dyson (Bc κ v z) n t 1 0 = F t) :
    dyson (Bc κ v z) (n + 1) x 0 0 = ∫ s in (0 : ℝ)..x, Bc κ v z s 0 1 * F s := by
  rw [dyson_succ_entry hB hL hx n 0 0]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have hx0 : 0 ≤ x := hx.1
  have ht' : t ∈ Icc (0 : ℝ) L := by
    rw [uIcc_of_le hx0] at ht; exact ⟨ht.1, ht.2.trans hx.2⟩
  rw [(mul_entry _ _ (Bc_00 κ v z t) (Bc_11 κ v z t)).1, h t ht']

theorem dyson_succ_01 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) (n : ℕ) (F : ℝ → ℂ)
    (h : ∀ t ∈ Icc (0 : ℝ) L, dyson (Bc κ v z) n t 1 1 = F t) :
    dyson (Bc κ v z) (n + 1) x 0 1 = ∫ s in (0 : ℝ)..x, Bc κ v z s 0 1 * F s := by
  rw [dyson_succ_entry hB hL hx n 0 1]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have ht' : t ∈ Icc (0 : ℝ) L := by
    rw [uIcc_of_le hx.1] at ht; exact ⟨ht.1, ht.2.trans hx.2⟩
  rw [(mul_entry _ _ (Bc_00 κ v z t) (Bc_11 κ v z t)).2.1, h t ht']

theorem dyson_succ_10 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) (n : ℕ) (F : ℝ → ℂ)
    (h : ∀ t ∈ Icc (0 : ℝ) L, dyson (Bc κ v z) n t 0 0 = F t) :
    dyson (Bc κ v z) (n + 1) x 1 0 = ∫ s in (0 : ℝ)..x, Bc κ v z s 1 0 * F s := by
  rw [dyson_succ_entry hB hL hx n 1 0]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have ht' : t ∈ Icc (0 : ℝ) L := by
    rw [uIcc_of_le hx.1] at ht; exact ⟨ht.1, ht.2.trans hx.2⟩
  rw [(mul_entry _ _ (Bc_00 κ v z t) (Bc_11 κ v z t)).2.2.1, h t ht']

theorem dyson_succ_11 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) (n : ℕ) (F : ℝ → ℂ)
    (h : ∀ t ∈ Icc (0 : ℝ) L, dyson (Bc κ v z) n t 0 1 = F t) :
    dyson (Bc κ v z) (n + 1) x 1 1 = ∫ s in (0 : ℝ)..x, Bc κ v z s 1 0 * F s := by
  rw [dyson_succ_entry hB hL hx n 1 1]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have ht' : t ∈ Icc (0 : ℝ) L := by
    rw [uIcc_of_le hx.1] at ht; exact ⟨ht.1, ht.2.trans hx.2⟩
  rw [(mul_entry _ _ (Bc_00 κ v z t) (Bc_11 κ v z t)).2.2.2, h t ht']

end Steps

/-- Even Dyson iterates are diagonal with the chamber integrals; odd iterates are off diagonal. -/
theorem dyson_even (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L) (z : ℂ) :
    ∀ r : ℕ, ∀ x ∈ Icc (0 : ℝ) L,
      dyson (Bc κ v z) (2 * r) x 0 0 = (κ : ℂ) ^ r * Wr (fun s => conj (v s)) v z r x ∧
      dyson (Bc κ v z) (2 * r) x 1 1 = (κ : ℂ) ^ r * Wr v (fun s => conj (v s)) (-z) r x ∧
      dyson (Bc κ v z) (2 * r) x 0 1 = 0 ∧ dyson (Bc κ v z) (2 * r) x 1 0 = 0 := by
  have hB := intervalIntegrable_Bc hv κ z
  have hs : ((Real.sqrt κ : ℝ) : ℂ) * ((Real.sqrt κ : ℝ) : ℂ) = (κ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hκ]
  have hk : ∀ r : ℕ, (κ : ℂ) ^ (r + 1) = ((Real.sqrt κ : ℂ) * (Real.sqrt κ : ℂ)) * (κ : ℂ) ^ r := by
    intro r; rw [hs, pow_succ]; ring
  intro r
  induction r with
  | zero =>
    intro x hx
    have h0 : dyson (Bc κ v z) 0 x = 1 := rfl
    simp [h0, Wr]
  | succ r ih =>
    intro x hx
    have e2 : 2 * (r + 1) = 2 * r + 1 + 1 := by ring
    have hsub : ∀ y ∈ Icc (0 : ℝ) L, ∀ t ∈ uIcc (0 : ℝ) y, t ∈ Icc (0 : ℝ) L := by
      intro y hy t ht
      rw [uIcc_of_le hy.1] at ht
      exact ⟨ht.1, ht.2.trans hy.2⟩
    -- odd iterate formulas
    have hodd10 : ∀ y ∈ Icc (0 : ℝ) L, dyson (Bc κ v z) (2 * r + 1) y 1 0 =
        (Real.sqrt κ : ℂ) * (κ : ℂ) ^ r * ∫ t in (0 : ℝ)..y, v t * Complex.exp (-(Complex.I * z * t)) *
          Wr (fun s => conj (v s)) v z r t := by
      intro y hy
      rw [dyson_succ_10 hB hL hy (2 * r) (fun t => (κ : ℂ) ^ r * Wr (fun s => conj (v s)) v z r t)
        (fun t ht => (ih t ht).1), ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      simp only [Bc_10]
      ring
    have hodd01 : ∀ y ∈ Icc (0 : ℝ) L, dyson (Bc κ v z) (2 * r + 1) y 0 1 =
        (Real.sqrt κ : ℂ) * (κ : ℂ) ^ r * ∫ t in (0 : ℝ)..y, conj (v t) *
          Complex.exp (-(Complex.I * (-z) * t)) * Wr v (fun s => conj (v s)) (-z) r t := by
      intro y hy
      rw [dyson_succ_01 hB hL hy (2 * r) (fun t => (κ : ℂ) ^ r * Wr v (fun s => conj (v s)) (-z) r t)
        (fun t ht => (ih t ht).2.1), ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      simp only [Bc_01]
      have e : Complex.exp (-(Complex.I * (-z) * t)) = Complex.exp (Complex.I * z * t) := by
        congr 1; ring
      rw [e]
      ring
    have hodd00 : ∀ y ∈ Icc (0 : ℝ) L, dyson (Bc κ v z) (2 * r + 1) y 0 0 = 0 := by
      intro y hy
      rw [dyson_succ_00 hB hL hy (2 * r) (fun _ => 0) (fun t ht => (ih t ht).2.2.2)]
      simp
    have hodd11 : ∀ y ∈ Icc (0 : ℝ) L, dyson (Bc κ v z) (2 * r + 1) y 1 1 = 0 := by
      intro y hy
      rw [dyson_succ_11 hB hL hy (2 * r) (fun _ => 0) (fun t ht => (ih t ht).2.2.1)]
      simp
    rw [e2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [dyson_succ_00 hB hL hx (2 * r + 1) _ hodd10]
      rw [show (κ : ℂ) ^ (r + 1) * Wr (fun s => conj (v s)) v z (r + 1) x =
          ∫ s in (0 : ℝ)..x, (κ : ℂ) ^ (r + 1) * (conj (v s) * Complex.exp (Complex.I * z * s) *
            ∫ y in (0 : ℝ)..s, v y * Complex.exp (-(Complex.I * z * y)) * Wr (fun s => conj (v s)) v z r y) by
        rw [intervalIntegral.integral_const_mul]; rfl]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      simp only [Bc_01, hk r]
      ring
    · rw [dyson_succ_11 hB hL hx (2 * r + 1) _ hodd01]
      rw [show (κ : ℂ) ^ (r + 1) * Wr v (fun s => conj (v s)) (-z) (r + 1) x =
          ∫ s in (0 : ℝ)..x, (κ : ℂ) ^ (r + 1) * (v s * Complex.exp (Complex.I * (-z) * s) *
            ∫ y in (0 : ℝ)..s, conj (v y) * Complex.exp (-(Complex.I * (-z) * y)) *
              Wr v (fun s => conj (v s)) (-z) r y) by
        rw [intervalIntegral.integral_const_mul]; rfl]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      simp only [Bc_10, hk r]
      have e : Complex.exp (-(Complex.I * z * t)) = Complex.exp (Complex.I * (-z) * t) := by
        congr 1; ring
      rw [e]
      ring
    · rw [dyson_succ_01 hB hL hx (2 * r + 1) (fun _ => 0) hodd11]
      simp
    · rw [dyson_succ_10 hB hL hx (2 * r + 1) (fun _ => 0) hodd00]
      simp

/-- Odd Dyson iterates have vanishing diagonal. -/
theorem dyson_odd_diag (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L) (z : ℂ)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    dyson (Bc κ v z) (2 * r + 1) x 0 0 = 0 ∧ dyson (Bc κ v z) (2 * r + 1) x 1 1 = 0 := by
  have hB := intervalIntegrable_Bc hv κ z
  constructor
  · rw [dyson_succ_00 hB hL hx (2 * r) (fun _ => 0) (fun t ht => (dyson_even hκ hL hv z r t ht).2.2.2)]
    simp
  · rw [dyson_succ_11 hB hL hx (2 * r) (fun _ => 0) (fun t ht => (dyson_even hκ hL hv z r t ht).2.2.1)]
    simp

/-! ### The trace -/

theorem summable_dyson (hL : 0 ≤ L) (hB : IntervalIntegrable (Bc κ v z) volume 0 L) :
    Summable (fun n : ℕ => dyson (Bc κ v z) n L) := by
  obtain ⟨hs, hb⟩ := uniform_dyson_bound hL hB
  exact Summable.of_norm_bounded hs (fun n => hb n L ⟨hL, le_rfl⟩)

theorem tsum_even_of_odd_zero {a : ℕ → ℂ} (hs : Summable a) (ho : ∀ k, a (2 * k + 1) = 0) :
    ∑' n, a n = ∑' k, a (2 * k) := by
  have he : Summable (fun k => a (2 * k)) := hs.comp_injective (fun x y h => by simpa using h)
  have hoS : Summable (fun k => a (2 * k + 1)) :=
    hs.comp_injective (i := fun k => 2 * k + 1) (fun x y h => by simpa using h)
  have := tsum_even_add_odd he hoS
  simp only [ho, tsum_zero, add_zero] at this
  exact this.symm

theorem Dc_mul_00 (z : ℂ) (x : ℝ) (M : Mat2) : (Dc z x * M) 0 0 = E1c z x * M 0 0 := by
  simp [Dc, P1, P2, Matrix.mul_apply, Fin.sum_univ_two]

theorem Dc_mul_11 (z : ℂ) (x : ℝ) (M : Mat2) : (Dc z x * M) 1 1 = E2c z x * M 1 1 := by
  simp [Dc, P1, P2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `(0,0)` and `(1,1)` entries of the interaction-picture transfer at `L`. -/
theorem transfer_entries (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hv : IntervalIntegrable v volume 0 L) (z : ℂ) :
    Summable (fun r : ℕ => (κ : ℂ) ^ r * Wr (fun s => conj (v s)) v z r L) ∧
    Summable (fun r : ℕ => (κ : ℂ) ^ r * Wr v (fun s => conj (v s)) (-z) r L) ∧
    transfer (Bc κ v z) L 0 0 = ∑' r : ℕ, (κ : ℂ) ^ r * Wr (fun s => conj (v s)) v z r L ∧
    transfer (Bc κ v z) L 1 1 = ∑' r : ℕ, (κ : ℂ) ^ r * Wr v (fun s => conj (v s)) (-z) r L := by
  have hB := intervalIntegrable_Bc hv κ z
  have hsum := summable_dyson hL hB
  have hLm : L ∈ Icc (0 : ℝ) L := ⟨hL, le_rfl⟩
  have hs00 : Summable (fun n => dyson (Bc κ v z) n L 0 0) :=
    ((QuantumNLS.RootDiscriminant.entryCLM 0 0).restrictScalars ℝ).summable hsum
  have hs11 : Summable (fun n => dyson (Bc κ v z) n L 1 1) :=
    ((QuantumNLS.RootDiscriminant.entryCLM 1 1).restrictScalars ℝ).summable hsum
  have ht00 : transfer (Bc κ v z) L 0 0 = ∑' n, dyson (Bc κ v z) n L 0 0 :=
    (((QuantumNLS.RootDiscriminant.entryCLM 0 0).restrictScalars ℝ).map_tsum hsum)
  have ht11 : transfer (Bc κ v z) L 1 1 = ∑' n, dyson (Bc κ v z) n L 1 1 :=
    (((QuantumNLS.RootDiscriminant.entryCLM 1 1).restrictScalars ℝ).map_tsum hsum)
  have e00 : ∀ r, dyson (Bc κ v z) (2 * r) L 0 0 = (κ : ℂ) ^ r * Wr (fun s => conj (v s)) v z r L :=
    fun r => (dyson_even hκ hL hv z r L hLm).1
  have e11 : ∀ r, dyson (Bc κ v z) (2 * r) L 1 1 = (κ : ℂ) ^ r * Wr v (fun s => conj (v s)) (-z) r L :=
    fun r => (dyson_even hκ hL hv z r L hLm).2.1
  have h00 : Summable (fun k => dyson (Bc κ v z) (2 * k) L 0 0) :=
    hs00.comp_injective (i := fun k => 2 * k) (fun x y h => by simpa using h)
  have h11 : Summable (fun k => dyson (Bc κ v z) (2 * k) L 1 1) :=
    hs11.comp_injective (i := fun k => 2 * k) (fun x y h => by simpa using h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [e00] using h00
  · simpa only [e11] using h11
  · rw [ht00, tsum_even_of_odd_zero hs00 (fun k => (dyson_odd_diag hκ hL hv z k hLm).1)]
    exact tsum_congr e00
  · rw [ht11, tsum_even_of_odd_zero hs11 (fun k => (dyson_odd_diag hκ hL hv z k hLm).2)]
    exact tsum_congr e11

/-- **Trace formula** for every `z ∈ ℂ`. -/
theorem trace_eq (hκ : 0 ≤ κ) (hL : 0 < L) (hv : IntervalIntegrable v volume 0 L) (z : ℂ) :
    Matrix.trace (QuantumNLS.RootDiscriminantL1.TT κ v z L) =
      E2c z L * (∑' r : ℕ, (κ : ℂ) ^ r * Wr (fun s => conj (v s)) v z r L) +
        E1c z L * (∑' r : ℕ, (κ : ℂ) ^ r * Wr v (fun s => conj (v s)) (-z) r L) := by
  obtain ⟨-, -, h00, h11⟩ := transfer_entries hκ hL.le hv z
  have hN := Nc_eq_transfer hL hv κ z ⟨hL.le, le_rfl⟩
  have a00 := congrArg (fun m : Mat2 => m 0 0) hN
  have a11 := congrArg (fun m : Mat2 => m 1 1) hN
  simp only [Dc_mul_00, Dc_mul_11] at a00 a11
  rw [h00] at a00
  rw [h11] at a11
  rw [Matrix.trace_fin_two]
  have hE : E2c z L * E1c z L = 1 := by rw [mul_comm]; exact E1c_mul_E2c z L
  have m00 : QuantumNLS.RootDiscriminantL1.TT κ v z L 0 0 = E2c z L * ∑' r : ℕ, (κ : ℂ) ^ r * Wr (fun s => conj (v s)) v z r L := by
    rw [← a00, ← mul_assoc, hE, one_mul]
  have m11 : QuantumNLS.RootDiscriminantL1.TT κ v z L 1 1 = E1c z L * ∑' r : ℕ, (κ : ℂ) ^ r * Wr v (fun s => conj (v s)) (-z) r L := by
    rw [← a11, ← mul_assoc, mul_comm (E1c z L), hE, one_mul]
  rw [m00, m11]

end QuantumNLS.RootTraceSymbolSpatial

#print axioms QuantumNLS.RootTraceSymbolSpatial.dyson_even
#print axioms QuantumNLS.RootTraceSymbolSpatial.dyson_odd_diag
#print axioms QuantumNLS.RootTraceSymbolSpatial.transfer_entries
#print axioms QuantumNLS.RootTraceSymbolSpatial.trace_eq
