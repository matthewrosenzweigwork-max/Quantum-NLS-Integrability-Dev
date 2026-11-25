import NlsGge.Spectral.TraceFormulaLowerOrder38
import NlsGge.Spectral.QuasimomentumL2Continuity38
import NlsGge.Spectral.QuadraticRiccatiRemainder38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38

/-! # R3a (TF-H^k): density extension of the uniform nonlinear Riccati remainder

The R3c hypothesis `NonlinRiccatiSmoothBound38 k` (uniform nonlinear remainder bound on Fourier planes
in an `H^k` ball) is extended to all `H^k` fields linked to a Sobolev element `y`, by Fourier
truncation: R2 (`k_u(iη)`), L²-continuity of `quadRiccati38` along truncations, and continuity of the
charges `chargeSobolev38`, `chargeQuad38` on `H^k`.  The result is conditional on R3c. -/

/-- **R3c hypothesis** (the statement of `nonlinRiccati38_smooth_bound` for this `k`, as a `Prop`).
Uniform nonlinear Riccati remainder for Fourier planes in an `H^k` ball: the constants depend only on
`k` and `B`, not on `N` or the plane. -/
def NonlinRiccatiSmoothBound38 (k : ℕ) : Prop :=
  ∀ B : ℝ, ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 ≤ B ^ 2 →
    ∀ η : ℝ, η₀ ≤ η →
    |η ^ (2*k+1) * ((actualQuasimomentumE02_38 (planeL2 N z) (Complex.I*η)).im - η
        - quadRiccati38 (planeL2 N z) η
        - ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
            (localCharge38 (planeReal N z) j -
              ∑ i : Fin (2*N+1), (2*Real.pi*(modeIndex N i : ℤ))^(2*j) * ‖z i‖^2))| ≤ C / η

/-! ## L²-continuity of `quadRiccati38` along Fourier truncations -/

theorem quadMultiplier_nonneg38 (η : ℝ) (hη : 0 < η) (n : ℤ) :
    0 ≤ 2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2) := by positivity

theorem quadMultiplier_le38 (η : ℝ) (hη : 0 < η) (n : ℤ) :
    2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2) ≤ 1 / (2 * η) := by
  have hd : 0 < 4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hd (by positivity)]
  nlinarith [sq_nonneg ((n:ℝ) * Real.pi), sq_nonneg η]

theorem summable_quadTerm38 (u : PhysicalL2) (η : ℝ) (hη : 0 < η) :
    Summable (fun n : ℤ => ‖physicalFourier u n‖ ^ 2 *
      (2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (quadMultiplier_nonneg38 η hη n))
    (fun n => ?_) ((summable_physicalFourier_sq u).mul_right (1 / (2 * η)))
  exact mul_le_mul_of_nonneg_left (quadMultiplier_le38 η hη n) (by positivity)

/-- For fixed `η > 0`, `quadRiccati38` is continuous along the Fourier truncations of any `L²` field. -/
theorem quadRiccati38_trunc_tendsto (u : PhysicalL2) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ => quadRiccati38 (truncL2E02_38 u N) η) atTop (𝓝 (quadRiccati38 u η)) := by
  unfold quadRiccati38
  refine tendsto_tsum_of_dominated_convergence (summable_quadTerm38 u η hη) (fun n => ?_) ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    have hlo : -(N:ℤ) ≤ n := by omega
    have hhi : n ≤ (N:ℤ) := by omega
    rw [physicalFourier_truncL2_in_E02_38 u N n hlo hhi]
  · refine Eventually.of_forall fun N n => ?_
    have hq := quadMultiplier_nonneg38 η hη n
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hq)]
    by_cases h : -(N:ℤ) ≤ n ∧ n ≤ N
    · rw [physicalFourier_truncL2_in_E02_38 u N n h.1 h.2]
    · have h' : n < -(N:ℤ) ∨ (N:ℤ) < n := by omega
      rw [physicalFourier_truncL2_out_E02_38 u N n h']
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact mul_nonneg (by positivity) hq

/-! ## Truncation bookkeeping for `y ∈ H^k` -/

theorem rpow_two_one38 (n : ℤ) : Real.rpow (japaneseBracket n) (2 * 1) = 1 + (n : ℝ) ^ 2 := by
  have := japaneseBracket_rpow_two_nat38 1 n
  simpa using this

section Trunc

variable (k : ℕ) (u : PhysicalL2) (y : SobolevHilbert ((k + 1 - 1 : ℕ) : ℝ))
  (hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y) n =
    physicalFourier u n)

include hy in
theorem hk_hasSum38 :
    HasSum (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ k * ‖physicalFourier u n‖ ^ 2) (‖y‖ ^ 2) := by
  have h := weightedHilbert_hasSum (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ))
    (show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y)
  have hr : ((k + 1 - 1 : ℕ) : ℝ) = (k : ℝ) := by simp
  have e : (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ k * ‖physicalFourier u n‖ ^ 2) =
      fun n => sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ) n *
        ‖(show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y) n‖ ^ 2 := by
    funext n
    rw [hy n, hr, sobolevModeWeight_nat38]
  rw [e]; exact h

include hy in
theorem hk_summable38 (hk : 1 ≤ k) (v : PhysicalL2)
    (hle : ∀ n, ‖physicalFourier v n‖ ≤ ‖physicalFourier u n‖) :
    SobolevSquareSummable 1 (physicalFourier v) := by
  unfold SobolevSquareSummable
  have hS := (hk_hasSum38 k u y hy).summable
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Real.rpow_nonneg (japaneseBracket_pos n).le _)
    (sq_nonneg _)) (fun n => ?_) hS
  rw [rpow_two_one38]
  have h1 : (1:ℝ) ≤ 1 + (n:ℝ) ^ 2 := by nlinarith [sq_nonneg (n:ℝ)]
  exact mul_le_mul (le_self_pow₀ h1 (by omega)) (pow_le_pow_left₀ (norm_nonneg _) (hle n) 2)
    (by positivity) (by positivity)

include hy in
theorem h1_le38 (hk : 1 ≤ k) (v : PhysicalL2)
    (hle : ∀ n, ‖physicalFourier v n‖ ≤ ‖physicalFourier u n‖)
    (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    ‖physicalSobolevL2 1 v hv‖ ≤ ‖y‖ := by
  have hS := (hk_hasSum38 k u y hy)
  have hsq : ‖physicalSobolevL2 1 v hv‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [physicalSobolevL2_norm_sq, ← hS.tsum_eq]
    refine Summable.tsum_le_tsum (fun n => ?_) hv hS.summable
    rw [rpow_two_one38]
    have h1 : (1:ℝ) ≤ 1 + (n:ℝ) ^ 2 := by nlinarith [sq_nonneg (n:ℝ)]
    exact mul_le_mul (le_self_pow₀ h1 (by omega)) (pow_le_pow_left₀ (norm_nonneg _) (hle n) 2)
      (by positivity) (by positivity)
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg y, norm_nonneg (physicalSobolevL2 1 v hv)]

include hy in
theorem plane_bound38 (N : ℕ) :
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k *
        ‖truncPlaneE02_38 u N i‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have hS := hk_hasSum38 k u y hy
  rw [← hS.tsum_eq]
  exact plane_sum_le_tsum_E02_38 N (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ k * ‖physicalFourier u n‖ ^ 2)
    (fun n => by positivity) hS.summable

include hy in
theorem chargeQuad_trunc38 (j : ℕ) (N : ℕ) :
    chargeQuad38 _ j (truncSobolev38 _ N y) =
      ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℤ)) ^ (2 * j) *
        ‖truncPlaneE02_38 u N i‖ ^ 2 := by
  classical
  unfold chargeQuad38
  rw [tsum_eq_sum (s := Finset.univ.image (modeIndex N))]
  · rw [Finset.sum_image (fun a _ b _ h => modeIndex_injective N h)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hmem : modeIndex N i ∈ Finset.Icc (-(N : ℤ)) N := by
      rw [Finset.mem_Icc]; exact modeIndex_bounds N i
    rw [truncSobolev38_apply]
    simp only [hmem, ↓reduceIte]
    rw [hy]
    rfl
  · intro n hn
    have hout : n ∉ Finset.Icc (-(N : ℤ)) N := by
      intro hmem
      rw [Finset.mem_Icc] at hmem
      obtain ⟨i, hi⟩ := modeIndex_covers N n hmem.1 hmem.2
      exact hn (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
    rw [truncSobolev38_apply]
    simp only [hout, ↓reduceIte]
    simp

end Trunc

/-! ## R3a -/

set_option linter.unusedVariables false in
/-- **R3a** (conditional on R3c).  Density extension of the uniform nonlinear Riccati remainder from
Fourier planes to every `u ∈ H^k` linked to `y ∈ SobolevHilbert k` with `‖y‖ ≤ B`. -/
theorem nonlinRiccati38_sobolev_bound (k : ℕ) (hk : 1 ≤ k) (hR3c : NonlinRiccatiSmoothBound38 k)
    (B : ℝ) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 ≤ C ∧ ∀ (u : PhysicalL2) (y : SobolevHilbert ((k + 1 - 1 : ℕ) : ℝ))
      (hy : ∀ n, (show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y) n =
        physicalFourier u n), ‖y‖ ≤ B → ∀ η : ℝ, η₀ ≤ η →
      |η ^ (2*k+1) * ((actualQuasimomentumE02_38 u (Complex.I*η)).im - η - quadRiccati38 u η
          - ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
              (chargeSobolev38 (k + 1) j y - chargeQuad38 _ j y))| ≤ C / η := by
  obtain ⟨η₀, C, hη₀, hC, hbound⟩ := hR3c B
  refine ⟨η₀, C, hη₀, hC, fun u y hy hyB η hη => ?_⟩
  have hηpos : 0 < η := lt_of_lt_of_le hη₀ hη
  have hB0 : 0 ≤ B := le_trans (norm_nonneg y) hyB
  -- the H¹ control
  have hle_u : ∀ n, ‖physicalFourier u n‖ ≤ ‖physicalFourier u n‖ := fun n => le_rfl
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := hk_summable38 k u y hy hk u hle_u
  have hle_t : ∀ N n, ‖physicalFourier (truncL2E02_38 u N) n‖ ≤ ‖physicalFourier u n‖ := by
    intro N n
    by_cases h : -(N:ℤ) ≤ n ∧ n ≤ N
    · rw [physicalFourier_truncL2_in_E02_38 u N n h.1 h.2]
    · have h' : n < -(N:ℤ) ∨ (N:ℤ) < n := by omega
      rw [physicalFourier_truncL2_out_E02_38 u N n h']; simp
  have hB1 : 1 ≤ max B 1 := le_max_right _ _
  have huB : ‖physicalSobolevL2 1 u hu1‖ ≤ max B 1 :=
    (h1_le38 k u y hy hk u hle_u hu1).trans (hyB.trans (le_max_left _ _))
  have hNB : ∀ N, ‖physicalSobolevL2 1 (truncL2E02_38 u N) (truncL2_sobolev_E02_38 u N)‖ ≤ max B 1 :=
    fun N => (h1_le38 k u y hy hk _ (hle_t N) _).trans (hyB.trans (le_max_left _ _))
  -- convergence of the quasimomentum
  have hz : 0 < (Complex.I * (η:ℂ)).im := by simpa using hηpos
  have hq := actualQuasimomentum_tendsto_of_L2_E02_38 u hu1 (max B 1) hB1 huB (truncL2E02_38 u)
    (truncL2_sobolev_E02_38 u) hNB (tendsto_truncL2_E02_38 u) _ hz
  have hqim := (Complex.continuous_im.tendsto _).comp hq
  -- convergence of the quadratic term
  have hquad := quadRiccati38_trunc_tendsto u η hηpos
  -- convergence of the charges
  have hT := tendsto_truncSobolev38 ((k + 1 - 1 : ℕ) : ℝ) y
  have hch : ∀ j ∈ Finset.range (k + 1),
      Tendsto (fun N : ℕ => (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
        (chargeSobolev38 (k + 1) j (truncSobolev38 _ N y) - chargeQuad38 _ j (truncSobolev38 _ N y)))
        atTop (𝓝 ((-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
          (chargeSobolev38 (k + 1) j y - chargeQuad38 _ j y))) := by
    intro j hj
    have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
    have h1 := ((continuous_chargeSobolev38 (k + 1) j (by omega)).tendsto y).comp hT
    have h2 := ((continuous_chargeQuad38 k j hjk).tendsto y).comp hT
    exact (h1.sub h2).const_mul _
  have hsum := tendsto_finsetSum (Finset.range (k + 1)) hch
  have hlim : Tendsto (fun N : ℕ => η ^ (2*k+1) *
      ((actualQuasimomentumE02_38 (truncL2E02_38 u N) (Complex.I*η)).im - η
        - quadRiccati38 (truncL2E02_38 u N) η
        - ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
            (chargeSobolev38 (k + 1) j (truncSobolev38 _ N y) - chargeQuad38 _ j (truncSobolev38 _ N y))))
      atTop (𝓝 (η ^ (2*k+1) *
      ((actualQuasimomentumE02_38 u (Complex.I*η)).im - η - quadRiccati38 u η
          - ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
              (chargeSobolev38 (k + 1) j y - chargeQuad38 _ j y)))) :=
    (((hqim.sub_const η).sub hquad).sub hsum).const_mul _
  refine le_of_tendsto (hlim.abs) (Eventually.of_forall fun N => ?_)
  have h := hbound N (truncPlaneE02_38 u N) ((plane_bound38 k u y hy N).trans
    (pow_le_pow_left₀ (norm_nonneg y) hyB 2)) η hη
  have hcharge : ∀ j ∈ Finset.range (k + 1),
      chargeSobolev38 (k + 1) j (truncSobolev38 _ N y) - chargeQuad38 _ j (truncSobolev38 _ N y) =
      localCharge38 (planeReal N (truncPlaneE02_38 u N)) j -
        ∑ i : Fin (2*N+1), (2*Real.pi*(modeIndex N i : ℤ))^(2*j) * ‖truncPlaneE02_38 u N i‖^2 := by
    intro j hj
    have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
    rw [chargeSobolev38_trunc (k + 1) j (by omega) (by omega) N y, chargeQuad_trunc38 k u y hy j N,
      ← truncPlane_eq_sobolev38 (k + 1) u y hy N]
  rw [Finset.sum_congr rfl (fun j hj => by rw [hcharge j hj])]
  exact h

/-! ## The consequence used by R4 -/

/-- **R3a + R3b** (conditional on R3c).  For `u ∈ H^k` linked to `y`, `k ≥ 1`, the full remainder of the
quasimomentum expansion, multiplied by `η^{2k+1}`, tends to `0`:
`η^{2k+1} (Im k_u(iη) − η − Σ_{j ≤ k} (−1)^j Q_{2j}(u) / (2·4^j η^{2j+1})) → 0`. -/
theorem nonlinRiccati38_full_remainder_tendsto (k : ℕ) (hk : 1 ≤ k)
    (hR3c : NonlinRiccatiSmoothBound38 k) (u : PhysicalL2)
    (y : SobolevHilbert ((k + 1 - 1 : ℕ) : ℝ))
    (hy : ∀ n, (show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n) :
    Tendsto (fun η : ℝ => η ^ (2*k+1) *
      ((actualQuasimomentumE02_38 u (Complex.I*η)).im - η
        - ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
            chargeSobolev38 (k + 1) j y)) atTop (𝓝 0) := by
  obtain ⟨η₀, C, hη₀, hC, hbound⟩ := nonlinRiccati38_sobolev_bound k hk hR3c ‖y‖
  -- R3a part
  have hE : Tendsto (fun η : ℝ => η ^ (2*k+1) * ((actualQuasimomentumE02_38 u (Complex.I*η)).im - η
      - quadRiccati38 u η
      - ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
          (chargeSobolev38 (k + 1) j y - chargeQuad38 _ j y))) atTop (𝓝 0) := by
    have hC' : Tendsto (fun η : ℝ => C / η) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hC'
    filter_upwards [eventually_ge_atTop η₀] with η hη
    rw [Real.norm_eq_abs]
    exact hbound u y hy le_rfl η hη
  -- R3b part
  have hu : SobolevSquareSummable (k : ℝ) (physicalFourier u) := by
    unfold SobolevSquareSummable
    refine (hk_hasSum38 k u y hy).summable.congr (fun n => ?_)
    rw [japaneseBracket_rpow_two_nat38]
  have hP : Tendsto (fun η : ℝ => η ^ (2*k+1) * (quadRiccati38 u η -
      ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
        ∑' n : ℤ, (2*Real.pi*n)^(2*j) * ‖physicalFourier u n‖ ^ 2)) atTop (𝓝 0) := by
    have htail := (quadRiccati38_remainder_tendsto k u hu).const_mul (1/2 : ℝ)
    rw [mul_zero] at htail
    refine squeeze_zero_norm' ?_ htail
    filter_upwards [eventually_gt_atTop 0] with η hη
    rw [Real.norm_eq_abs]
    have := quadRiccati38_remainder k u hu η hη
    exact this
  have hsum := hE.add hP
  rw [add_zero] at hsum
  refine hsum.congr (fun η => ?_)
  have hquad : ∀ j : ℕ, chargeQuad38 _ j y =
      ∑' n : ℤ, (2*Real.pi*n)^(2*j) * ‖physicalFourier u n‖ ^ 2 := fun j => by
    unfold chargeQuad38
    exact tsum_congr (fun n => by rw [hy n])
  simp only [hquad]
  rw [← mul_add]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end NlsGge.SpectralFoundations
end
