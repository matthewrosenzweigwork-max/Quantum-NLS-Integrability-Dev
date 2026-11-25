import QuantumNLS.ActionTorus

/-! The classical cutoff on one fixed phase orbit. Uniformity is over all
angles and all points on the orbit, including zero coordinates. This does
not assume uniform continuity of the inverse chart on an infinite ball. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Set
open QuantumNLS.ActionTorus QuantumNLS.ResetNormalizationUniqueness
namespace QuantumNLS.TerraMultiRound87Classical

/-- On a fixed modulus orbit, agreement on finitely many coordinates makes
all rotated points uniformly close in ℓ². -/
theorem finite_coordinates_control (z : S2 ℤ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset ℤ, ∀ (x : S2 ℤ), (∀ n, ‖x n‖ = ‖z n‖) →
      ∀ θ φ : ℤ → Circle, (∀ n ∈ F, θ n = φ n) →
        ‖rotate θ x - rotate φ x‖ < δ := by
  classical
  have hδ2 : 0 < δ ^ 2 := by positivity
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero
    (fun n : ℤ => 4 * ‖z n‖ ^ 2)).eventually (gt_mem_nhds hδ2)).exists
  refine ⟨F, ?_⟩
  intro x hx θ φ hθ
  let d := rotate θ x - rotate φ x
  have hpoint (n : ℤ) : ‖d n‖ ^ 2 ≤ 4 * ‖z n‖ ^ 2 := by
    change ‖(θ n : ℂ) * x n - (φ n : ℂ) * x n‖ ^ 2 ≤ 4 * ‖z n‖ ^ 2
    rw [← sub_mul, norm_mul, mul_pow, hx]
    have hb : ‖(θ n : ℂ) - (φ n : ℂ)‖ ≤ 2 := by
      calc
        _ ≤ ‖(θ n : ℂ)‖ + ‖(φ n : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by simp; norm_num
    exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg ((θ n : ℂ) - (φ n : ℂ))]) (sq_nonneg _)
  have hzero : ∑ n ∈ F, ‖d n‖ ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [d, hθ n hn]
  have ht : ∑' n : {x : ℤ // x ∉ F}, ‖d n‖ ^ 2 ≤
      ∑' n : {x : ℤ // x ∉ F}, 4 * ‖z n‖ ^ 2 := by
    exact Summable.tsum_le_tsum (fun n => hpoint n)
      ((summable_sq d).comp_injective Subtype.val_injective)
      (((summable_sq z).mul_left 4).comp_injective Subtype.val_injective)
  have hsq : ‖d‖ ^ 2 < δ ^ 2 := by
    rw [tsum_sq_eq, ← (summable_sq d).sum_add_tsum_subtype_compl F, hzero]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le hsq

/-- Equal moduli determine an orbit point, including the zero coordinates. -/
theorem orbit_of_equal_moduli (x z : S2 ℤ) (h : ∀ n, ‖x n‖ = ‖z n‖) :
    ∃ α : ℤ → Circle, rotate α z = x := by
  classical
  have hex : ∀ n : ℤ, ∃ a : Circle, (a : ℂ) * z n = x n := by
    intro n
    by_cases hn : z n = 0
    · have hx : x n = 0 := norm_eq_zero.mp (by rw [h n, hn, norm_zero])
      exact ⟨1, by simp [hn, hx]⟩
    · have ha : ‖x n / z n‖ = 1 := by
        rw [norm_div, h n, div_self (norm_ne_zero_iff.mpr hn)]
      exact ⟨⟨x n / z n, mem_sphere_zero_iff_norm.mpr ha⟩,
        div_mul_cancel₀ _ hn⟩
  choose α hα using hex
  refine ⟨α, ?_⟩
  apply lp.ext
  funext n
  exact hα n

/-- A continuous inverse chart carries the uniform coordinate cutoff to a
uniform physical cutoff on the compact orbit of the fixed profile. -/
theorem physical_finite_coordinates_control {Y : Type*} [PseudoMetricSpace Y]
    (g : S2 ℤ → Y) (hg : Continuous g) (z : S2 ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset ℤ, ∀ (α θ φ : ℤ → Circle), (∀ n ∈ F, θ n = φ n) →
      dist (g (rotate θ (rotate α z))) (g (rotate φ (rotate α z))) < ε := by
  let orbit : Set (S2 ℤ) := Set.range (fun α : ℤ → Circle => rotate α z)
  have horbit : IsCompact orbit := isCompact_range (continuous_rotate_left z)
  have hUC := horbit.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  obtain ⟨F, hF⟩ := finite_coordinates_control z δ hδ
  refine ⟨F, ?_⟩
  intro α θ φ hθ
  apply hδ'
  · exact ⟨θ * α, (rotate_mul θ α z)⟩
  · exact ⟨φ * α, (rotate_mul φ α z)⟩
  · rw [dist_eq_norm]
    apply hF (rotate α z)
    · intro n
      simp
    · exact hθ

/-- The finite set may be enclosed in a symmetric interval, yielding the
uniform radial cutoff used in the source. -/
theorem physical_radial_cutoff {Y : Type*} [PseudoMetricSpace Y]
    (g : S2 ℤ → Y) (hg : Continuous g) (z : S2 ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (α θ φ : ℤ → Circle),
      (∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = φ n) →
      dist (g (rotate θ (rotate α z))) (g (rotate φ (rotate α z))) < ε := by
  obtain ⟨F, hF⟩ := physical_finite_coordinates_control g hg z ε hε
  refine ⟨F.sup Int.natAbs, ?_⟩
  intro α θ φ hθ
  apply hF α θ φ
  intro n hn
  apply hθ n
  have h := Finset.le_sup (f := Int.natAbs) hn
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

/-- Action conservation supplies equal moduli; this version therefore uses
exactly that fact and does not choose phases at vanishing coordinates. -/
theorem physical_radial_cutoff_of_equal_moduli {Y : Type*} [PseudoMetricSpace Y]
    (g : S2 ℤ → Y) (hg : Continuous g) (z : S2 ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (x : S2 ℤ), (∀ n, ‖x n‖ = ‖z n‖) →
      ∀ θ φ : ℤ → Circle,
      (∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = φ n) →
      dist (g (rotate θ x)) (g (rotate φ x)) < ε := by
  obtain ⟨R, hR⟩ := physical_radial_cutoff g hg z ε hε
  refine ⟨R, ?_⟩
  intro x hx θ φ hθ
  obtain ⟨α, rfl⟩ := orbit_of_equal_moduli x z hx
  exact hR α θ φ hθ

#print axioms physical_radial_cutoff_of_equal_moduli
#print axioms orbit_of_equal_moduli
#print axioms physical_radial_cutoff
#print axioms finite_coordinates_control
#print axioms physical_finite_coordinates_control
end QuantumNLS.TerraMultiRound87Classical
