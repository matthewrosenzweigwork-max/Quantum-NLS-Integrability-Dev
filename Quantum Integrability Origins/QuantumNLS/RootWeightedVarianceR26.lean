import QuantumNLS.RootWeightedFirstR26
import QuantumNLS.RootMassPlane

/-! Physical lower bounds and their equality case. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.RootWeightedVarianceR26
open PhysicalTensor (L2T)
open QuantumNLS.Fourier ProductEnergyPreparation ChargeEnergy RootWeightedPhysicalR26
variable {L : ℝ} [hLf : Fact (0 < L)]

theorem quartic_lower (u : L2T L) (hH : OneH1 u) :
    ‖u‖^4/L ≤ quartic (u : AddCircle L → ℂ) := by
  have hmInt : Integrable (fun x => ‖u x‖^2) (volume : Measure (AddCircle L)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hqInt := quartic_integrable (oneH1_h04 hH)
  have hm : (∫ x,‖u x‖^2 ∂(volume : Measure (AddCircle L))) = ‖u‖^2 :=
    (lp_norm_sq _ u).symm
  let a := ‖u‖^2/L
  have he : (∫ x,(‖u x‖^2-a)^2 ∂(volume : Measure (AddCircle L))) =
      quartic (u : AddCircle L → ℂ)-2*a*‖u‖^2+a^2*L := by
    calc
      _ = ∫ x,(‖u x‖^4-2*a*‖u x‖^2+a^2) ∂(volume : Measure (AddCircle L)) :=
        integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = _ := by
        have hmul : Integrable (fun x => 2*a*‖u x‖^2) (volume : Measure (AddCircle L)) := hmInt.const_mul (2*a)
        have hsub : Integrable (fun x => ‖u x‖^4-2*a*‖u x‖^2) (volume : Measure (AddCircle L)) := hqInt.sub hmul
        rw [integral_add hsub (integrable_const (a^2)),
          integral_sub hqInt hmul,integral_const_mul,hm,integral_const]
        simp only [smul_eq_mul,measureReal_def,torus_mass,ENNReal.toReal_ofReal hLf.out.le]
        unfold quartic
        ring
  have h0 : 0 ≤ quartic (u : AddCircle L → ℂ)-2*a*‖u‖^2+a^2*L :=
    he ▸ integral_nonneg (fun _ => sq_nonneg _)
  dsimp [a] at h0
  have hL := hLf.out
  field_simp [hL.ne'] at h0 ⊢
  nlinarith [h0]

def variance (u : L2T L) (a : ℝ) : ℝ :=
  ∑' n : ℤ,(freq L n-a)^2*‖fourierL2 L u n‖^2

theorem variance_summable (u : L2T L) (hH : OneH1 u) (a : ℝ) :
    Summable (fun n : ℤ => (freq L n-a)^2*‖fourierL2 L u n‖^2) := by
  have h0 := Energy.summable_sq (fourierL2 L u)
  have hk := (hasSum_kin_a hH).summable
  have hP := (momentum_summable u hH).of_abs
  exact ((hk.sub (hP.mul_left (2*a))).add (h0.mul_left (a^2))).congr (fun n => by ring)

theorem variance_eq (u : L2T L) (hH : OneH1 u) (a : ℝ) :
    variance u a = kinetic (u : AddCircle L → ℂ)-2*a*fourierMomentum u+a^2*‖u‖^2 := by
  have h0 := Energy.summable_sq (fourierL2 L u)
  have hk := (hasSum_kin_a hH).summable
  have hP := (momentum_summable u hH).of_abs
  have hn : (∑' n : ℤ,‖fourierL2 L u n‖^2) = ‖u‖^2 := by
    rw [← norm_fourierL2]
    exact (Energy.norm_sq_eq_tsum _).symm
  unfold variance
  calc
    _ = ∑' n : ℤ,(freq L n^2*‖fourierL2 L u n‖^2-
        (2*a)*(freq L n*‖fourierL2 L u n‖^2)+a^2*‖fourierL2 L u n‖^2) :=
      tsum_congr fun n => by ring
    _ = _ := by
      rw [(hk.sub (hP.mul_left (2*a))).tsum_add (h0.mul_left (a^2)),
        hk.tsum_sub (hP.mul_left (2*a)),tsum_mul_left,tsum_mul_left,
        (hasSum_kin_a hH).tsum_eq,hn]
      rfl

theorem variance_nonneg (u : L2T L) (a : ℝ) : 0 ≤ variance u a :=
  tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem zero_variance_plane (u : L2T L) (hH : OneH1 u) (k : ℤ)
    (hv : variance u (freq L k) = 0) : ∃ c : ℂ,u = c • modeLp L k := by
  classical
  have hz : ∀ n : ℤ,n ≠ k → fourierL2 L u n = 0 := by
    intro n hn
    have he : (freq L n-freq L k)^2*‖fourierL2 L u n‖^2 ≤ variance u (freq L k) := by
      simpa only [Finset.sum_singleton,variance] using Summable.sum_le_tsum ({n} : Finset ℤ)
        (fun i _ => mul_nonneg (sq_nonneg (freq L i-freq L k)) (sq_nonneg ‖fourierL2 L u i‖))
        (variance_summable u hH (freq L k))
    rw [hv] at he
    have hf : freq L n-freq L k ≠ 0 := by
      intro hf
      unfold freq at hf
      field_simp [hLf.out.ne'] at hf
      have hc : (n : ℝ) = (k : ℝ) := by nlinarith [Real.pi_pos]
      exact hn (Int.cast_injective hc)
    have hsq : ‖fourierL2 L u n‖^2 = 0 :=
      (mul_eq_zero.mp (le_antisymm he (mul_nonneg (sq_nonneg _) (sq_nonneg _)))).resolve_left
        (pow_ne_zero 2 hf)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  refine ⟨fourierL2 L u k,?_⟩
  apply (fourierL2 L).injective
  rw [map_smul,fourierL2_modeLp]
  apply lp.ext
  funext n
  by_cases hn : n = k
  · subst n
    simp
  · simp [lp.single_apply,hn,hz n hn]

end QuantumNLS.RootWeightedVarianceR26
