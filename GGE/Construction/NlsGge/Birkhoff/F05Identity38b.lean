import NlsGge.Birkhoff.F05Identity38

/-! # F05, file b: Ramer's setting `S_m` carries `T`, `K`, `K'` (v2 l.680-681)

`E = h^{m-1}` via `F05EquivCarrier`, `H = (S_m).H = h^m` as a set with the equivalent (not
isometric) norm `2 Σ a_{m,n}|h_n|²`.  The comparison `h^m → S_m.H` is a bounded coordinate-identity
(`cmOf05`), because `a_{m,n} ≤ C ⟨n⟩^{2m}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.Ramer.General Filter Topology
open scoped ENNReal

section Setting

variable (m : ℕ) (β : ℕ → ℝ) (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

/-- The Ramer setting `S_m` of F05 (`F05Setting`) under `β_j > 0`. -/
abbrev S05 : RamerSetting :=
  F05Setting m β hm (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)

/-- `h^{m-1} ≃ S_m.E` (isometric, coordinate preserving). -/
def Eq05 : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) ≃ₗᵢ[ℝ] (S05 m β hm hβ).E :=
  F05EquivCarrier m β hm (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)

theorem coord_Eq05 (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) (n : ℤ) :
    (S05 m β hm hβ).coord n (Eq05 m β hm hβ y) = carrierCoe38 _ y n :=
  coord_F05Equiv m β hm (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) y n

theorem S05_q (n : ℤ) : (S05 m β hm hβ).q n = finiteHierarchyRate38 m β n := rfl

theorem S05_γ : (S05 m β hm hβ).γ = gammaM38 m β := rfl

/-- `a_{m,n} ≤ C ⟨n⟩^{2m}`. -/
theorem rate_le_bracket38 (hβ0 : ∀ i ≤ m, 0 ≤ β i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, finiteHierarchyRate38 m β n ≤ C * (1 + (n : ℝ) ^ 2) ^ m := by
  refine ⟨∑ j ∈ Finset.range (m + 1), β j * (2 * Real.pi) ^ (2 * j),
    Finset.sum_nonneg fun j hj => mul_nonneg (hβ0 j (by have := Finset.mem_range.1 hj; omega))
      (by positivity), fun n => ?_⟩
  unfold finiteHierarchyRate38 finiteHierarchyW38
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j ≤ m := by have := Finset.mem_range.1 hj; omega
  have h1 : (2 * Real.pi * (n : ℝ)) ^ (2 * j) = (2 * Real.pi) ^ (2 * j) * ((n : ℝ) ^ 2) ^ j := by
    rw [mul_pow, pow_mul (n : ℝ)]
  have h2 : ((n : ℝ) ^ 2) ^ j ≤ (1 + (n : ℝ) ^ 2) ^ m := by
    calc ((n : ℝ) ^ 2) ^ j ≤ (1 + (n : ℝ) ^ 2) ^ j :=
          pow_le_pow_left₀ (sq_nonneg _) (by linarith) j
      _ ≤ (1 + (n : ℝ) ^ 2) ^ m := pow_le_pow_right₀ (by nlinarith [sq_nonneg (n : ℝ)]) hj'
  have hb := hβ0 j hj'
  calc β j * (2 * Real.pi * (n : ℝ)) ^ (2 * j)
      = β j * (2 * Real.pi) ^ (2 * j) * ((n : ℝ) ^ 2) ^ j := by rw [h1]; ring
    _ ≤ β j * (2 * Real.pi) ^ (2 * j) * (1 + (n : ℝ) ^ 2) ^ m :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The constant `C` with `a_{m,n} ≤ C ⟨n⟩^{2m}`. -/
def Cr05 : ℝ := (rate_le_bracket38 m β (fun i hi => (hβ i hi).le)).choose

theorem Cr05_nonneg : 0 ≤ Cr05 m β hβ :=
  (rate_le_bracket38 m β (fun i hi => (hβ i hi).le)).choose_spec.1

theorem rate_le_Cr05 (n : ℤ) :
    finiteHierarchyRate38 m β n ≤ Cr05 m β hβ * (1 + (n : ℝ) ^ 2) ^ m :=
  (rate_le_bracket38 m β (fun i hi => (hβ i hi).le)).choose_spec.2 n

/-- The coordinate-identity `h^k → S_m.H` for `k ≥ m`. -/
def cmOf05 (k : ℕ) (hk : m ≤ k) : SobolevCarrier38 (k : ℝ) →L[ℝ] (S05 m β hm hβ).H :=
  (weightedRealComparisonContinuous (sobolevModeWeight (k : ℝ))
    (S05 m β hm hβ).cmWeight
    (2 * Cr05 m β hβ) (by have := Cr05_nonneg m β hβ; positivity) (by
      intro n
      have h := rate_le_Cr05 m β hβ n
      rw [sobolevWeight_eq38]
      have : (1 + (n : ℝ) ^ 2) ^ m ≤ (1 + (n : ℝ) ^ 2) ^ k :=
        pow_le_pow_right₀ (by nlinarith [sq_nonneg (n : ℝ)]) hk
      have hc := Cr05_nonneg m β hβ
      show 2 * finiteHierarchyRate38 m β n ≤ _
      nlinarith))

theorem hcoord_cmOf05 (k : ℕ) (hk : m ≤ k) (y : SobolevCarrier38 (k : ℝ)) (n : ℤ) :
    (S05 m β hm hβ).hcoord (cmOf05 m β hm hβ k hk y) n = carrierCoe38 _ y n := rfl

end Setting


section TK

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

theorem one_le_pred05 (hm : 2 ≤ m) : 1 ≤ m - 1 := by omega

theorem le_pred_add_one05 (m : ℕ) (hm : 2 ≤ m) : m ≤ m - 1 + 1 := by omega

/-- `T : S_m.E ≃ₜ S_m.E`, transported from `T : h^{m-1} ≃ₜ h^{m-1}`. -/
def T05 : (S05 m β hm hβ).E ≃ₜ (S05 m β hm hβ).E :=
  ((Eq05 m β hm hβ).toHomeomorph.symm.trans (B.homeoC (m - 1))).trans
    (Eq05 m β hm hβ).toHomeomorph

theorem T05_apply (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) :
    T05 B hm hβ (Eq05 m β hm hβ y) = Eq05 m β hm hβ (B.TC (m - 1) y) := by
  simp [T05]

theorem T05_symm_apply (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) :
    (T05 B hm hβ).symm (Eq05 m β hm hβ y) = Eq05 m β hm hβ (B.TinvC (m - 1) y) := by
  simp [T05]

/-- `K = T - Id : E → H` (`h^{m-1} → h^m` by one-smoothing, then into `S_m.H`). -/
def K05 (x : (S05 m β hm hβ).E) : (S05 m β hm hβ).H :=
  cmOf05 m β hm hβ (m - 1 + 1) (le_pred_add_one05 m hm)
    (carrierMap38 ((m - 1 : ℕ) : ℝ) ((m - 1 + 1 : ℕ) : ℝ) (fun y => B.T y - y)
      (O.smooth_T (m - 1) (one_le_pred05 hm)) ((Eq05 m β hm hβ).symm x))

/-- `T⁻¹ - Id : E → H`. -/
def K05' (x : (S05 m β hm hβ).E) : (S05 m β hm hβ).H :=
  cmOf05 m β hm hβ (m - 1 + 1) (le_pred_add_one05 m hm)
    (carrierMap38 ((m - 1 : ℕ) : ℝ) ((m - 1 + 1 : ℕ) : ℝ) (fun y => B.Tinv y - y)
      (O.smooth_Tinv (m - 1) (one_le_pred05 hm)) ((Eq05 m β hm hβ).symm x))

theorem hcoord_K05 (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) (n : ℤ) :
    (S05 m β hm hβ).hcoord (K05 B O hm hβ (Eq05 m β hm hβ y)) n =
      B.T (carrierCoe38 _ y) n - carrierCoe38 _ y n := by
  simp only [K05, LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem hcoord_K05' (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) (n : ℤ) :
    (S05 m β hm hβ).hcoord (K05' B O hm hβ (Eq05 m β hm hβ y)) n =
      B.Tinv (carrierCoe38 _ y) n - carrierCoe38 _ y n := by
  simp only [K05', LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem hT05 (x : (S05 m β hm hβ).E) :
    T05 B hm hβ x = x + (S05 m β hm hβ).incl (K05 B O hm hβ x) := by
  obtain ⟨y, rfl⟩ := (Eq05 m β hm hβ).surjective x
  apply (S05 m β hm hβ).E_ext
  intro n
  rw [T05_apply, (S05 m β hm hβ).coord_add, (S05 m β hm hβ).coord_incl, hcoord_K05,
    coord_Eq05, coord_Eq05]
  show B.T (carrierCoe38 _ y) n = _
  ring

theorem hTs05 (x : (S05 m β hm hβ).E) :
    (T05 B hm hβ).symm x = x + (S05 m β hm hβ).incl (K05' B O hm hβ x) := by
  obtain ⟨y, rfl⟩ := (Eq05 m β hm hβ).surjective x
  apply (S05 m β hm hβ).E_ext
  intro n
  rw [T05_symm_apply, (S05 m β hm hβ).coord_add, (S05 m β hm hβ).coord_incl, hcoord_K05',
    coord_Eq05, coord_Eq05]
  show B.Tinv (carrierCoe38 _ y) n = _
  ring

theorem analytic_K05 : AnalyticOnNhd ℝ (K05 B O hm hβ) Set.univ := by
  have h1 : AnalyticOnNhd ℝ (fun x : (S05 m β hm hβ).E => (Eq05 m β hm hβ).symm x) Set.univ :=
    ((Eq05 m β hm hβ).symm.toLinearIsometry.toContinuousLinearMap).analyticOnNhd _
  have h2 := (O.analytic_smooth_T (m - 1) (one_le_pred05 hm)).comp h1 (fun _ _ => Set.mem_univ _)
  exact ((cmOf05 m β hm hβ (m - 1 + 1) (le_pred_add_one05 m hm)).analyticOnNhd _).comp h2
    (fun _ _ => Set.mem_univ _)

theorem analytic_K05' : AnalyticOnNhd ℝ (K05' B O hm hβ) Set.univ := by
  have h1 : AnalyticOnNhd ℝ (fun x : (S05 m β hm hβ).E => (Eq05 m β hm hβ).symm x) Set.univ :=
    ((Eq05 m β hm hβ).symm.toLinearIsometry.toContinuousLinearMap).analyticOnNhd _
  have h2 := (O.analytic_smooth_Tinv (m - 1) (one_le_pred05 hm)).comp h1
    (fun _ _ => Set.mem_univ _)
  exact ((cmOf05 m β hm hβ (m - 1 + 1) (le_pred_add_one05 m hm)).analyticOnNhd _).comp h2
    (fun _ _ => Set.mem_univ _)

end TK

end NlsGge.Birkhoff
