import Mathlib
import QuantumNLS.RootDiscriminantContinuity

/-!
# R-7E0532E7: `Δ_u(z) = tr M(L,z)` is ENTIRE in `z` (continuous-representative class)

Variational equation + Gronwall (no series): with `A_{z+h} = A_z + h·A₁`, `A₁ = diag(-i/2, i/2) = ∂_z A`, `det M = 1` (so
`M⁻¹ = adj M`), put `Ṁ = M · ∫₀ˣ adj(M) A₁ M`; then `Ṁ' = A Ṁ + A₁ M`, `E_h = M_{z+h} - M_z - hṀ` satisfies
`E_h' = A_z E_h + h A₁ (M_{z+h} - M_z)`, and Gronwall + the Lipschitz estimate `‖M_{z+h}-M_z‖ ≤ C|h|` give
`‖E_h(L)‖ ≤ C'|h|²`.  Hence `z ↦ M(L,z)` is complex differentiable everywhere (`differentiable_transfer`) and
`discriminant L κ u` is entire (`differentiable_discriminant`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open ComplexConjugate MeasureTheory Filter Topology Set
open scoped Matrix NNReal
open QuantumNLS.SpatialTransfer QuantumNLS.LinearFundamental QuantumNLS.RootDiscriminant
  QuantumNLS.RootDiscriminantBound QuantumNLS.RootDiscriminantContinuity

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootDiscriminantEntire

/-- `A₁ = ∂_z A_z = diag(-i/2, i/2)`. -/
def Aone : Mat2 := !![-Complex.I / 2, 0; 0, Complex.I / 2]

theorem balCoef_add (κ : ℝ) (u : ℝ → ℂ) (z h : ℂ) (x : ℝ) :
    balCoef κ u (z + h) x = balCoef κ u z x + h • Aone := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [balCoef, coef, Aone] <;> ring

theorem norm_Aone_le : ‖Aone‖ ≤ 1 / 2 := by
  refine norm_le_of_row_sums _ (by norm_num) (fun i => ?_)
  fin_cases i <;> simp [Aone]

theorem alg_identity (A B M' M Md : Mat2) (h : ℂ) :
    (A + h • B) * M' - A * M - h • (A * Md + B * M) =
      A * (M' - M - h • Md) + h • (B * (M' - M)) := by
  simp only [add_mul, smul_mul_assoc, mul_sub, mul_add, mul_smul_comm, smul_sub, smul_add]
  module

theorem gronwallBound_zero_le {K ε x : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    gronwallBound 0 K ε x ≤ ε * x * Real.exp (K * x) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  simp only [zero_mul, zero_add]
  have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
    have := Real.add_one_le_exp (-(K * x))
    have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (K * x)]
  calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ε * x * Real.exp (K * x) := by field_simp

variable (κ : ℝ)

/-- Uniform Lipschitz estimate in `z` on `[0,L]`, `‖z‖ ≤ R`. -/
theorem lipschitz_x {u : ℝ → ℂ} (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) (R : ℝ) :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 ≤ C ∧ (∀ z : ℂ, ‖z‖ ≤ R → ∀ x ∈ Icc (0 : ℝ) L, ‖balCoef κ u z x‖ ≤ K) ∧
      ∀ z z' : ℂ, ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ x ∈ Icc (0 : ℝ) L,
        ‖spatialTransfer κ u z x - spatialTransfer κ u z' x‖ ≤ C * ‖z - z'‖ := by
  obtain ⟨Ku, hKu⟩ : ∃ Ku, ∀ x ∈ Icc (0 : ℝ) L, ‖u x‖ ≤ Ku :=
    (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn hu.continuousOn
  set K : ℝ := max 1 (R / 2 + Real.sqrt κ * Ku) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := by linarith
  have hAK : ∀ z : ℂ, ‖z‖ ≤ R → ∀ x ∈ Icc (0 : ℝ) L, ‖balCoef κ u z x‖ ≤ K := by
    intro z hz x hx
    refine (norm_balCoef_le κ u z x).trans ?_
    refine le_trans ?_ (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left (hKu x hx) (Real.sqrt_nonneg κ)
    linarith
  have hMb : ∀ z : ℂ, ‖z‖ ≤ R → ∀ x ∈ Icc (0 : ℝ) L, ‖spatialTransfer κ u z x‖ ≤ Real.exp (K * L) := by
    intro z hz x hx
    have hM := spatialTransfer_spec' κ hu z
    have := gronwall_mat2 (δ := 1) (K := K) (ε := 0) (L := L) (f := spatialTransfer κ u z)
      (f' := fun y => balCoef κ u z y * spatialTransfer κ u z y) hM.2
      (by rw [hM.1]; exact norm_one_mat2_le)
      (fun y hy => by
        calc ‖balCoef κ u z y * spatialTransfer κ u z y‖
            ≤ ‖balCoef κ u z y‖ * ‖spatialTransfer κ u z y‖ := norm_mul_le _ _
          _ ≤ K * ‖spatialTransfer κ u z y‖ :=
            mul_le_mul_of_nonneg_right (hAK z hz y ⟨hy.1, hy.2.le⟩) (norm_nonneg _)
          _ = K * ‖spatialTransfer κ u z y‖ + 0 := by ring) x hx
    rw [gronwallBound_ε0, sub_zero, one_mul] at this
    exact this.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx.2 (by linarith)))
  refine ⟨K, L * Real.exp (2 * K * L) / 2, hK1, by positivity, hAK, fun z z' hz hz' x hx => ?_⟩
  have hMz := spatialTransfer_spec' κ hu z
  have hMz' := spatialTransfer_spec' κ hu z'
  have hD : ∀ y, HasDerivAt (fun s => spatialTransfer κ u z s - spatialTransfer κ u z' s)
      (balCoef κ u z y * spatialTransfer κ u z y - balCoef κ u z' y * spatialTransfer κ u z' y) y :=
    fun y => (hMz.2 y).sub (hMz'.2 y)
  have hg := gronwall_mat2 (δ := 0) (K := K) (ε := ‖z - z'‖ / 2 * Real.exp (K * L)) (L := L)
    (f := fun y => spatialTransfer κ u z y - spatialTransfer κ u z' y) hD
    (by simp [hMz.1, hMz'.1]) (fun y hy => by
      have hyI : y ∈ Icc (0 : ℝ) L := ⟨hy.1, hy.2.le⟩
      have e : balCoef κ u z y * spatialTransfer κ u z y - balCoef κ u z' y * spatialTransfer κ u z' y =
          balCoef κ u z y * (spatialTransfer κ u z y - spatialTransfer κ u z' y) +
            (balCoef κ u z y - balCoef κ u z' y) * spatialTransfer κ u z' y := by
        rw [mul_sub, sub_mul]; abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hAK z hz y hyI) (norm_nonneg _))
      · refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul (norm_balCoef_sub κ u z z' y) (hMb z' hz' y hyI) (norm_nonneg _) (by positivity)) x hx
  have hx0 : 0 ≤ x := hx.1
  have hxL : x ≤ L := hx.2
  simp only [sub_zero] at hg
  refine hg.trans ((gronwallBound_zero_le hKpos (by positivity) hx0).trans ?_)
  have h1 : Real.exp (K * x) ≤ Real.exp (K * L) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxL hKpos.le)
  have h2 : Real.exp (K * L) * Real.exp (K * L) = Real.exp (2 * K * L) := by rw [← Real.exp_add]; ring_nf
  calc ‖z - z'‖ / 2 * Real.exp (K * L) * x * Real.exp (K * x)
      ≤ ‖z - z'‖ / 2 * Real.exp (K * L) * L * Real.exp (K * L) := by
        gcongr
    _ = L * Real.exp (2 * K * L) / 2 * ‖z - z'‖ := by rw [← h2]; ring


section Diff

variable {κ} {u : ℝ → ℂ}

/-- `J(x) = ∫₀ˣ adj(M) A₁ M` and `Ṁ = M J` (the `z`-derivative of the fundamental solution). -/
def Jint (κ : ℝ) (u : ℝ → ℂ) (z0 : ℂ) (x : ℝ) : Mat2 :=
  ∫ s in (0 : ℝ)..x, Matrix.adjugate (spatialTransfer κ u z0 s) * Aone * spatialTransfer κ u z0 s

def Mdot (κ : ℝ) (u : ℝ → ℂ) (z0 : ℂ) (x : ℝ) : Mat2 := spatialTransfer κ u z0 x * Jint κ u z0 x

theorem mul_adj_spatialTransfer (hu : Continuous u) (z0 : ℂ) (x : ℝ) :
    spatialTransfer κ u z0 x * Matrix.adjugate (spatialTransfer κ u z0 x) = 1 := by
  rw [Matrix.mul_adjugate, det_spatialTransfer κ hu z0 x, one_smul]

theorem continuous_transfer_x (hu : Continuous u) (z0 : ℂ) : Continuous (spatialTransfer κ u z0) := by
  have hM := spatialTransfer_spec' κ hu z0
  exact continuous_iff_continuousAt.2 fun y => (hM.2 y).continuousAt

theorem hasDerivAt_Mdot (hu : Continuous u) (z0 : ℂ) (x : ℝ) :
    HasDerivAt (Mdot κ u z0) (balCoef κ u z0 x * Mdot κ u z0 x + Aone * spatialTransfer κ u z0 x) x := by
  have hM := spatialTransfer_spec' κ hu z0
  have hMc := continuous_transfer_x (κ := κ) hu z0
  have hc : Continuous fun s => Matrix.adjugate (spatialTransfer κ u z0 s) * Aone * spatialTransfer κ u z0 s :=
    ((hMc.matrix_adjugate).mul continuous_const).mul hMc
  have hJ : HasDerivAt (Jint κ u z0)
      (Matrix.adjugate (spatialTransfer κ u z0 x) * Aone * spatialTransfer κ u z0 x) x :=
    (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have h := (hM.2 x).mul hJ
  refine h.congr_deriv ?_
  have h1 := mul_adj_spatialTransfer (κ := κ) hu z0 x
  show balCoef κ u z0 x * spatialTransfer κ u z0 x * Jint κ u z0 x +
      spatialTransfer κ u z0 x * (Matrix.adjugate (spatialTransfer κ u z0 x) * Aone * spatialTransfer κ u z0 x) =
    balCoef κ u z0 x * (spatialTransfer κ u z0 x * Jint κ u z0 x) + Aone * spatialTransfer κ u z0 x
  rw [Matrix.mul_assoc (balCoef κ u z0 x), ← Matrix.mul_assoc (spatialTransfer κ u z0 x),
    ← Matrix.mul_assoc (spatialTransfer κ u z0 x), h1, Matrix.one_mul]

theorem Mdot_zero (hu : Continuous u) (z0 : ℂ) : Mdot κ u z0 0 = 0 := by
  simp [Mdot, Jint]

/-- **`z ↦ M(L,z)` is complex differentiable** with derivative `Ṁ(L)`. -/
theorem hasDerivAt_transfer (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) (z0 : ℂ) :
    HasDerivAt (fun z : ℂ => spatialTransfer κ u z L) (Mdot κ u z0 L) z0 := by
  obtain ⟨K, C, hK1, hC, hAK, hLip⟩ := lipschitz_x κ hu hL (‖z0‖ + 1)
  have hKpos : 0 < K := by linarith
  set C2 : ℝ := C / 2 * L * Real.exp (K * L) with hC2
  have hC20 : 0 ≤ C2 := by positivity
  -- key quadratic bound
  have key : ∀ h : ℂ, ‖h‖ ≤ 1 →
      ‖spatialTransfer κ u (z0 + h) L - spatialTransfer κ u z0 L - h • Mdot κ u z0 L‖ ≤ C2 * ‖h‖ ^ 2 := by
    intro h hh
    have hzR : ‖z0 + h‖ ≤ ‖z0‖ + 1 := (norm_add_le _ _).trans (by linarith)
    have hz0R : ‖z0‖ ≤ ‖z0‖ + 1 := by linarith
    have hM := spatialTransfer_spec' κ hu z0
    have hM' := spatialTransfer_spec' κ hu (z0 + h)
    have hE : ∀ y, HasDerivAt (fun s => spatialTransfer κ u (z0 + h) s - spatialTransfer κ u z0 s -
        h • Mdot κ u z0 s)
        (balCoef κ u (z0 + h) y * spatialTransfer κ u (z0 + h) y - balCoef κ u z0 y * spatialTransfer κ u z0 y -
          h • (balCoef κ u z0 y * Mdot κ u z0 y + Aone * spatialTransfer κ u z0 y)) y :=
      fun y => ((hM'.2 y).sub (hM.2 y)).sub ((hasDerivAt_Mdot hu z0 y).const_smul h)
    have hg := gronwall_mat2 (δ := 0) (K := K) (ε := ‖h‖ * (‖h‖ / 2 * C)) (L := L)
      (f := fun s => spatialTransfer κ u (z0 + h) s - spatialTransfer κ u z0 s - h • Mdot κ u z0 s) hE
      (by simp [hM.1, hM'.1, Mdot_zero hu z0]) (fun y hy => by
        have hyI : y ∈ Icc (0 : ℝ) L := ⟨hy.1, hy.2.le⟩
        have e := alg_identity (balCoef κ u z0 y) Aone (spatialTransfer κ u (z0 + h) y)
          (spatialTransfer κ u z0 y) (Mdot κ u z0 y) h
        rw [← balCoef_add] at e
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hAK z0 (by linarith) y hyI) (norm_nonneg _))
        · calc ‖h • (Aone * (spatialTransfer κ u (z0 + h) y - spatialTransfer κ u z0 y))‖
              ≤ ‖h‖ * ‖Aone * (spatialTransfer κ u (z0 + h) y - spatialTransfer κ u z0 y)‖ := norm_smul_le _ _
            _ ≤ ‖h‖ * (‖Aone‖ * ‖spatialTransfer κ u (z0 + h) y - spatialTransfer κ u z0 y‖) :=
                mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
            _ ≤ ‖h‖ * (1 / 2 * (C * ‖h‖)) := by
                refine mul_le_mul_of_nonneg_left (mul_le_mul norm_Aone_le ?_ (norm_nonneg _) (by norm_num)) (norm_nonneg _)
                have := hLip (z0 + h) z0 hzR hz0R y hyI
                simpa using this
            _ = ‖h‖ * (‖h‖ / 2 * C) := by ring) L ⟨hL, le_rfl⟩
    simp only [sub_zero] at hg
    refine hg.trans ((gronwallBound_zero_le hKpos (by positivity) hL).trans ?_)
    rw [hC2]
    have : ‖h‖ * (‖h‖ / 2 * C) * L * Real.exp (K * L) = C / 2 * L * Real.exp (K * L) * ‖h‖ ^ 2 := by ring
    rw [this]
  refine hasDerivAt_iff_isLittleO_nhds_zero.2 ?_
  refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (lt_min one_pos (div_pos hε (by linarith : 0 < C2 + 1)))] with h hh
  have hh' : ‖h‖ < min 1 (ε / (C2 + 1)) := by simpa [dist_eq_norm] using hh
  have h1 : ‖h‖ ≤ 1 := (lt_of_lt_of_le hh' (min_le_left _ _)).le
  have h2 : ‖h‖ < ε / (C2 + 1) := lt_of_lt_of_le hh' (min_le_right _ _)
  calc ‖spatialTransfer κ u (z0 + h) L - spatialTransfer κ u z0 L - h • Mdot κ u z0 L‖ ≤ C2 * ‖h‖ ^ 2 := key h h1
    _ = (C2 * ‖h‖) * ‖h‖ := by ring
    _ ≤ ε * ‖h‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have h3 : C2 * ‖h‖ ≤ C2 * (ε / (C2 + 1)) := mul_le_mul_of_nonneg_left h2.le hC20
        have h4 : C2 * (ε / (C2 + 1)) ≤ ε := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]; nlinarith
        linarith

theorem differentiable_transfer (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) :
    Differentiable ℂ (fun z : ℂ => spatialTransfer κ u z L) :=
  fun z0 => (hasDerivAt_transfer hu hL z0).differentiableAt

/-- **`Δ_u(z) = tr M(L,z)` is entire.** -/
theorem differentiable_discriminant (L : ℝ) (hu : Continuous u) (hL : 0 ≤ L) :
    Differentiable ℂ (discriminant L κ u) := by
  have h := differentiable_transfer (κ := κ) hu hL
  have hd : Differentiable ℂ (fun m : Mat2 => m.trace) := by
    have : (fun m : Mat2 => m.trace) = fun m => entryCLM 0 0 m + entryCLM 1 1 m := by
      funext m; rw [Matrix.trace_fin_two]; rfl
    rw [this]
    exact ((entryCLM 0 0).differentiable.add (entryCLM 1 1).differentiable)
  exact hd.comp h

#print axioms differentiable_discriminant

end Diff

end QuantumNLS.RootDiscriminantEntire
