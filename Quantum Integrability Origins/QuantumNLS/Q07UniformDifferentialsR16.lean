import QuantumNLS.Q07UniformGeometryR16
import QuantumNLS.Q07LogBoundsR16
import QuantumNLS.Q07StripUniformR16
import QuantumNLS.ContourPrefactor

/-! Uniform actual logarithm Hessians and their rectangular contour bounds.
The contour expression below is explicitly the integrated logarithm Hessian;
identifying it as the Hessian of the window Hamiltonian is a separate step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace QuantumNLS.Q07UniformDifferentialsR16
open PhysicalTensor (L2T)
open Q07LogDifferentialsR16 Q07UniformGeometryR16
open Q07StripInteractionR16 (interaction control)
open ResolventNeighborhood (GammaN)
variable {L κ : ℝ} [Fact (0 < L)]

/-- Strip value bounds for the physical product symbol on full physical balls. -/
theorem symbol_bound (hκ : 0 ≤ κ) {R h : ℝ} (u : L2T L)
    (hu : ‖u‖ ≤ R) {z : ℂ} (hz : |z.im| ≤ h) :
    ‖NormalizedTransfer.productSymbol L κ u z‖ ≤
      (1+Real.exp (h*L)) *
        (Real.exp (Real.sqrt κ*Real.exp (h*L)*‖Q07PhysicalProfilesR15.toProfile (L := L)‖*R)+2) := by
  let C := 1+Real.exp (h*L)
  let T := Real.exp (Real.sqrt κ*Real.exp (h*L)*‖Q07PhysicalProfilesR15.toProfile (L := L)‖*R)
  let N := interaction κ (Q07PhysicalProfilesR15.toProfile u) z
  have hN : ‖N‖ ≤ T := by
    refine (Q07StripInteractionR16.norm_interaction_le (Fact.out : 0 < L).le _ hz).trans ?_
    apply Real.exp_le_exp.mpr
    have hp := Q07PhysicalProfilesR15.toProfile.le_opNorm u
    change Real.sqrt κ*Real.exp (h*L)*‖Q07PhysicalProfilesR15.toProfile u‖ ≤
      Real.sqrt κ*Real.exp (h*L)*‖Q07PhysicalProfilesR15.toProfile (L := L)‖*R
    have hh : ‖Q07PhysicalProfilesR15.toProfile u‖ ≤ ‖Q07PhysicalProfilesR15.toProfile (L := L)‖*R :=
      hp.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
    calc
      _ ≤ (Real.sqrt κ*Real.exp (h*L))*(‖Q07PhysicalProfilesR15.toProfile (L := L)‖*R) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  have hn : ‖N-1‖ ≤ T+1 := (norm_sub_le _ _).trans (by
    have hh := RootDiscriminantBound.norm_one_mat2_le
    linarith)
  have he : ‖Complex.exp (Complex.I*z*L)‖ ≤ Real.exp (h*L) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hi : -z.im ≤ h := (neg_le_abs _).trans hz
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_sub, mul_zero, sub_zero]
    nlinarith [Fact.out (p := 0 < L)]
  have hs := Q07StripUniformR16.symbol_error_le hκ u hz
  have hh := norm_add_le
    (NormalizedTransfer.productSymbol L κ u z-1-Complex.exp (Complex.I*z*L))
    (1+Complex.exp (Complex.I*z*L))
  rw [show NormalizedTransfer.productSymbol L κ u z-1-Complex.exp (Complex.I*z*L)+
    (1+Complex.exp (Complex.I*z*L)) = NormalizedTransfer.productSymbol L κ u z by ring] at hh
  have hf := norm_add_le (1 : ℂ) (Complex.exp (Complex.I*z*L))
  norm_num only [norm_one] at hf
  change ‖NormalizedTransfer.productSymbol L κ u z‖ ≤ C*(T+2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmul := mul_le_mul_of_nonneg_left hn hC
  change ‖NormalizedTransfer.productSymbol L κ u z-1-Complex.exp (Complex.I*z*L)‖ ≤ C*‖N-1‖ at hs
  nlinarith

/-- The actual normalized logarithm has a uniform full bilinear Hessian
bound over every high rectangle and on one fixed physical neighborhood. -/
theorem uniform_log_hessians (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (B : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ l : ℕ, l0 ≤ l → ∀ u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B,
        ∀ v : L2T L, ‖v-u‖ < δ → ∀ z ∈ GammaN (PROP017UniformN.cutSeq L l) h,
          RootCauchyJointR9.Regular κ (v,z) ∧ ∀ w q : L2T L,
            ‖second (logarithm hκ z) v w q‖ ≤ C*‖w‖*‖q‖ := by
  obtain ⟨δ,hδ,l0,R,d,hR,hd,hgeo⟩ := uniform_contour_data (L := L) hκ hs B hh
  obtain ⟨C1,C2,h1,h2,hbnd⟩ := Q07LogBoundsR16.logarithm_hessian_bound (L := L) hκ hR hh.le
  let M := (1+Real.exp (h*L)) *
    (Real.exp (Real.sqrt κ*Real.exp (h*L)*‖Q07PhysicalProfilesR15.toProfile (L := L)‖*R)+2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let C := d⁻¹*C2+M*d⁻¹^3*C1^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨δ,hδ,l0,C,hC,?_⟩
  intro l hl u hu v hv z hz
  obtain ⟨hvR,hreg⟩ := hgeo l hl u hu v hv
  obtain ⟨hp,hD⟩ := hreg z hz
  have hzi := NonvanishingD.GammaN_im_abs hh.le hz
  refine ⟨hp,?_⟩
  intro w q
  exact hbnd z (by linarith [neg_le_abs z.im]) v (mem_ball_zero_iff.mpr hvR) hp d M hd hM hD
    (symbol_bound hκ.le v hvR.le hzi) w q

end QuantumNLS.Q07UniformDifferentialsR16
