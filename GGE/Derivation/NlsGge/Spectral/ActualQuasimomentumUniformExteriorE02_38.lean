import NlsGge.Spectral.ActualQuasimomentumDecayE02_38
import NlsGge.Spectral.ActualCouplingSobolevUniformBox38
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # Uniform exterior bound `‖k(z) - z‖ ≤ 1/4` on bounded H¹ balls -/

/-- Uniform (in `u` with `‖u‖_{H¹} ≤ B`) normalized half-trace bound. -/
theorem exists_uniform_normalized_bound_E02_38 (B : ℝ) (hB : 0 ≤ B) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ (u : PhysicalL2)
      (hu : SobolevSquareSummable 1 (physicalFourier u)), ‖physicalSobolevL2 1 u hu‖ ≤ B →
      ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z : ℂ, 0 ≤ z.im → K ≤ ‖z‖ →
      ‖Complex.exp (Complex.I*z) * actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z -
        (1 + Complex.exp (2*Complex.I*z))/2‖ ≤ C / ‖z‖ := by
  obtain ⟨Ci, C1, hCi, hC1, hrep⟩ := NlsGge.Schur.actualH1ACRepresentativeUniformBox38V1
  set A := Ci * B
  set a := C1 * B
  have hA0 : 0 ≤ A := by positivity
  have ha0 : 0 ≤ a := by positivity
  refine ⟨4*(A + A^2 + a) + 1, (4/3)*(A + A^2 + a) + 1, by positivity, by positivity, ?_⟩
  intro u hu huB τ hτ z hz hzK
  have hu' := sobolevSquareSummable_smul38 (τ:ℂ) u hu
  obtain ⟨f, f', hfac, hf'i, hder, hae, hfb, hf'b⟩ := hrep ((τ:ℂ) • u) hu'
  have hnorm : ‖physicalSobolevL2 1 ((τ:ℂ) • u) hu'‖ ≤ B := by
    rw [physicalSobolevL2_smul_norm38 (τ:ℂ) u hu hu']
    have : ‖(τ:ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ.1]; exact hτ.2
    nlinarith [norm_nonneg (physicalSobolevL2 1 u hu)]
  have hfb' : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖f t‖ ≤ A := fun t ht =>
    (hfb t ht).trans (mul_le_mul_of_nonneg_left hnorm hCi.le)
  have hf'b' : ∫ t in (0:ℝ)..1, ‖f' t‖ ≤ a := hf'b.trans (mul_le_mul_of_nonneg_left hnorm hC1.le)
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hzK
  have hden : 0 < 2 * ‖z‖ := by positivity
  have hβ : A / (2 * ‖z‖) ≤ 1/4 := by
    rw [div_le_iff₀ hden]; nlinarith [sq_nonneg A]
  have hη : (A^2 + a) / (2 * ‖z‖) ≤ 1/8 := by
    rw [div_le_iff₀ hden]; nlinarith [sq_nonneg A]
  have h := uniformBox_normalized_bound_of_rep38 ((τ:ℂ) • u) f f' A a hfac hf'i hder hae hfb'
    hf'b' z hz hz0 hβ hη
  refine h.trans ?_
  rw [show 8 / 3 * (A / (2 * ‖z‖) + (A ^ 2 + a) / (2 * ‖z‖)) =
    (4/3)*(A + A^2 + a) / ‖z‖ by field_simp; ring]
  apply div_le_div_of_nonneg_right (by linarith) hz0.le

/-- Exterior bound for a single `u`, with explicit radius and constant in terms of `K, C₀`. -/
theorem exterior_bound_of_normalized_E02_38 (u : PhysicalL2) (K C₀ : ℝ) (hK : 0 < K)
    (hC₀ : 0 < C₀)
    (hnb : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z : ℂ, 0 ≤ z.im → K ≤ ‖z‖ →
      ‖Complex.exp (Complex.I*z) * actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z -
        (1 + Complex.exp (2*Complex.I*z))/2‖ ≤ C₀ / ‖z‖) :
    ∀ z : ℂ, 0 < z.im → max K (20000 * C₀) + 1 < ‖z‖ →
      ‖actualQuasimomentumE02_38 u z - z‖ ≤
        (3/2) * (3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * C₀) + 8 * C₀) / Real.sqrt ‖z‖ := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set k := actualQuasimomentumE02_38 u
  have he3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set R₁ : ℝ := max K (20000 * C₀) + 1
  have hR₁ : 1 ≤ R₁ := by
    have : 0 ≤ max K (20000 * C₀) := le_trans hK.le (le_max_left _ _)
    linarith
  set D : ℝ := 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * C₀) + 8 * C₀
  have hD : 0 ≤ D := by positivity
  have hφ : ∀ z : ℂ, 0 < z.im → R₁ < ‖z‖ →
      ‖Complex.exp (Complex.I * (k z - z)) - 1‖ ≤ D / Real.sqrt ‖z‖ ∧
      ‖Complex.exp (Complex.I * (k z - z)) - 1‖ ≤ 1/6 := by
    intro z hzi hzR
    have hz1 : 1 ≤ ‖z‖ := le_trans hR₁ hzR.le
    have hzpos : 0 < ‖z‖ := by linarith
    set ε := C₀ / ‖z‖
    have hε0 : 0 ≤ ε := by positivity
    have hε : ε ≤ 1/20000 := by
      rw [div_le_iff₀ hzpos]
      have : 20000 * C₀ ≤ R₁ := le_trans (le_max_right _ _) (by linarith)
      linarith
    have hKz : K ≤ ‖z‖ := le_trans (le_trans (le_max_left _ _) (by linarith)) hzR.le
    have h := norm_exp_sub_one_le_of_normalized_E02_38 u z hzi ε hε0 hε
      (fun τ hτ => hnb τ hτ z hzi.le hKz)
    have hsz : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr hzpos
    constructor
    · refine h.trans (max_le ?_ ?_)
      · have : Real.sqrt (2 * Real.exp 1 * ε) = Real.sqrt (2 * Real.exp 1 * C₀) / Real.sqrt ‖z‖ := by
          rw [show 2 * Real.exp 1 * ε = (2 * Real.exp 1 * C₀) / ‖z‖ by simp only [ε]; ring,
            Real.sqrt_div' _ hzpos.le]
        rw [this, mul_div_assoc']
        apply div_le_div_of_nonneg_right _ hsz.le
        linarith [show 0 ≤ 8 * C₀ by positivity]
      · have hsle : Real.sqrt ‖z‖ ≤ ‖z‖ := by
          calc Real.sqrt ‖z‖ ≤ Real.sqrt (‖z‖^2) := Real.sqrt_le_sqrt (by nlinarith)
            _ = ‖z‖ := Real.sqrt_sq hzpos.le
        have h8 : 8 * ε ≤ 8 * C₀ / Real.sqrt ‖z‖ := by
          simp only [ε]
          rw [mul_div_assoc']
          exact div_le_div_of_nonneg_left (by positivity) hsz hsle
        have h3 : 0 ≤ 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * C₀) := by positivity
        refine h8.trans (div_le_div_of_nonneg_right ?_ hsz.le)
        simp only [D]; linarith
    · refine h.trans (max_le ?_ ?_)
      · have h1 : 2 * Real.exp 1 * ε ≤ 6/20000 := by nlinarith
        have h2 : Real.sqrt (2 * Real.exp 1 * ε) ≤ Real.sqrt (6/20000) := Real.sqrt_le_sqrt h1
        have h3 : Real.sqrt (6/20000) < 1/57 := by
          rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have h5 : 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * ε) ≤ 3 * 3 * (1/57) :=
          mul_le_mul (by linarith) (h2.trans h3.le) (Real.sqrt_nonneg _) (by norm_num)
        linarith
      · linarith
  set S : Set ℂ := {z : ℂ | 0 < z.im ∧ R₁ < ‖z‖}
  have hS : IsPreconnected S := isPreconnected_upperExterior_E02_38 R₁ (by linarith)
  obtain ⟨Rh, hRh, hhigh⟩ := hk.2.2.2 1 one_pos
  set Y₁ : ℝ := max Rh (R₁ + 1)
  let z₁ : ℂ := ((0:ℝ):ℂ) + Complex.I * ((Y₁:ℝ):ℂ)
  have hY₁ : R₁ + 1 ≤ Y₁ := le_max_right _ _
  have hz₁ : z₁ ∈ S := by
    constructor
    · simp [z₁]; linarith
    · have : ‖z₁‖ = Y₁ := by
        simp only [z₁, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_pos (by linarith)
      rw [this]; linarith
  have hz₁s : ‖k z₁ - z₁‖ < 1 := hhigh Y₁ (le_max_left _ _) 0
  have hcontS : ContinuousOn (fun z => k z - z) S :=
    (hk.1.continuousOn.mono (fun z hz => hz.1)).sub continuousOn_id
  have hunif := norm_le_of_exp_mul_I_near_one_E02_38 S hS _ hcontS (1/2) le_rfl
    (fun z hz => (hφ z hz.1 hz.2).2.trans (by norm_num)) z₁ hz₁ hz₁s
  intro z hzi hzR
  have hp := norm_le_of_exp_mul_I_pointwise_E02_38 (k z - z)
    (by have := hunif z ⟨hzi, hzR⟩; linarith) ((hφ z hzi hzR).2.trans (by norm_num))
  rw [mul_div_assoc]
  exact hp.trans (mul_le_mul_of_nonneg_left (hφ z hzi hzR).1 (by norm_num))

/-- Core uniform statement with a non-strict radius `X₀` (used for the boundary limit). -/
theorem actualQuasimomentum_uniformExterior_core_E02_38 :
    ∀ B : ℝ, 1 ≤ B → ∃ X : ℝ, 0 < X ∧ ∀ (u : PhysicalL2)
      (hu : SobolevSquareSummable 1 (physicalFourier u)),
      ‖physicalSobolevL2 1 u hu‖ ≤ B → ∀ z : ℂ, 0 < z.im → X ≤ ‖z‖ →
        ‖actualQuasimomentumE02_38 u z - z‖ ≤ 1/4 := by
  intro B hB
  obtain ⟨K, C₀, hK, hC₀, hnb⟩ := exists_uniform_normalized_bound_E02_38 B (by linarith)
  set D : ℝ := 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * C₀) + 8 * C₀
  have hD : 0 ≤ D := by positivity
  set R₁ : ℝ := max K (20000 * C₀) + 1
  have hR₁ : 1 ≤ R₁ := by
    have : 0 ≤ max K (20000 * C₀) := le_trans hK.le (le_max_left _ _)
    linarith
  refine ⟨R₁ + 1 + (6 * D)^2, by positivity, ?_⟩
  intro u hu huB z hzi hzX
  have hzR : max K (20000 * C₀) + 1 < ‖z‖ := by nlinarith [sq_nonneg (6 * D)]
  have h := exterior_bound_of_normalized_E02_38 u K C₀ hK hC₀
    (fun τ hτ z hz hKz => hnb u hu huB τ hτ z hz hKz) z hzi hzR
  have hzpos : 0 < ‖z‖ := by nlinarith [sq_nonneg (6 * D)]
  have hsz : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr hzpos
  have hs6 : 6 * D ≤ Real.sqrt ‖z‖ := by
    calc 6 * D = Real.sqrt ((6 * D)^2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ‖z‖ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (6 * D)])
  refine h.trans ?_
  rw [div_le_iff₀ hsz]
  nlinarith

/-- Uniform exterior bound `‖k(z) - z‖ ≤ 1/4` for `‖z‖ ≥ X` on the closed `H¹` ball of radius `B`. -/
theorem actualQuasimomentum_uniformExterior_E02_38 :
    ∀ B : ℝ, 1 ≤ B → ∃ X : ℝ, 0 < X ∧ ∀ (u : PhysicalL2)
      (hu : SobolevSquareSummable 1 (physicalFourier u)),
      ‖physicalSobolevL2 1 u hu‖ ≤ B → ∀ z : ℂ, 0 < z.im → X ≤ ‖z‖ →
        ‖actualQuasimomentumE02_38 u z - z‖ ≤ 1/4 := by
  intro B hB
  obtain ⟨X, hX, h⟩ := actualQuasimomentum_uniformExterior_core_E02_38 B hB
  exact ⟨X + 1, by linarith, fun u hu huB z hz hzX => h u hu huB z hz (by linarith)⟩

/-- Boundary corollary (same radius): `‖k(x + i0) - x‖ ≤ 1/4` for `|x| ≥ X`. -/
theorem actualQuasimomentumBoundary_uniformExterior_E02_38 :
    ∀ B : ℝ, 1 ≤ B → ∃ X : ℝ, 0 < X ∧ ∀ (u : PhysicalL2)
      (hu : SobolevSquareSummable 1 (physicalFourier u)),
      ‖physicalSobolevL2 1 u hu‖ ≤ B →
        ∀ x : ℝ, X ≤ |x| → ‖actualQuasimomentumBoundaryE02_38 u x - x‖ ≤ 1/4 := by
  intro B hB
  obtain ⟨X, hX, h⟩ := actualQuasimomentum_uniformExterior_core_E02_38 B hB
  refine ⟨X + 1, by linarith, fun u hu huB x hx => ?_⟩
  
  have hNe : (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 (by simp))
  have hlim := ((tendsto_actualQuasimomentumBoundaryE02_38 u x).sub
    (tendsto_id.mono_left nhdsWithin_le_nhds)).norm
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (x:ℂ) one_pos)] with w hw hwb
  apply h u hu huB w hw
  have h1 : ‖(x:ℂ)‖ ≤ ‖w‖ + ‖(x:ℂ) - w‖ := by
    have := norm_add_le w ((x:ℂ) - w); simpa using this
  have h2 : ‖(x:ℂ) - w‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hwb; rwa [norm_sub_rev]
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  linarith

#check @actualQuasimomentum_uniformExterior_E02_38
#check @actualQuasimomentumBoundary_uniformExterior_E02_38
#print axioms actualQuasimomentum_uniformExterior_E02_38
#print axioms actualQuasimomentumBoundary_uniformExterior_E02_38

end NlsGge.SpectralFoundations
end
