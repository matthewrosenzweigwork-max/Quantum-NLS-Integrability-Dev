import NlsGge.GK38.AbelianJointMatrixMass
import NlsGge.Analysis.ComplexHilbertSchmidtNorm

/-! UNCOMPILED complex lp2 matrix-energy bridge. Finite Cauchy--Schwarz and
actual lp partial-sum convergence earn the operator norm bound. Joint matrix
summability is an explicit meaningful input, realized by the preceding leaf.
No complex HS-to-operator API is assumed. -/
set_option autoImplicit false
open Set Filter Topology
open scoped Classical
namespace NlsGge.GK38
noncomputable section

/-- The exact unit vectors used by the actual complex matrix coefficients. -/
def p6ComplexLpBasis38 (ι : Type*) : HilbertBasis ι ℂ (lp (fun _ : ι => ℂ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

theorem p6ComplexLpBasis_apply38 (ι : Type*) (r : ι) :
    p6ComplexLpBasis38 ι r=lp.single 2 r (1 : ℂ) := by
  classical
  simpa only [p6ComplexLpBasis38,LinearIsometryEquiv.coe_refl] using!
    (p6ComplexLpBasis38 ι).repr_self r

theorem p6ComplexLp_opNorm_le_column_mass38 {ι κ : Type*}
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : κ => ℂ) 2)
    (hs : Summable (fun r : ι => ‖T (lp.single 2 r (1 : ℂ))‖^2)) :
    ‖T‖ ≤ Real.sqrt (∑' r : ι, ‖T (lp.single 2 r (1 : ℂ))‖^2) := by
  classical
  let B : ℝ := ∑' r : ι, ‖T (lp.single 2 r (1 : ℂ))‖^2
  apply T.opNorm_le_bound (Real.sqrt_nonneg B)
  intro x
  have hx : HasSum (fun r : ι => ‖x r‖^2) (‖x‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) x
  have hfinite (S : Finset ι) : ‖∑ r ∈ S, T (lp.single 2 r (x r))‖ ≤
      Real.sqrt B*‖x‖ := by
    have hunit (r : ι) : T (lp.single 2 r (x r))=
        x r • T (lp.single 2 r (1 : ℂ)) := by
      have he : lp.single (E := fun _ : ι => ℂ) 2 r (x r)=
          x r • lp.single (E := fun _ : ι => ℂ) 2 r (1 : ℂ) := by
        simpa only [smul_eq_mul,mul_one] using lp.single_smul (E := fun _ : ι => ℂ) 2 r (x r) (1 : ℂ)
      rw [he,map_smul]
    have hxs : (∑ r ∈ S, ‖x r‖^2) ≤ ‖x‖^2 :=
      sum_le_hasSum S (fun _ _ => sq_nonneg _) hx
    have hTs : (∑ r ∈ S, ‖T (lp.single 2 r (1 : ℂ))‖^2) ≤ B :=
      hs.sum_le_tsum S (fun _ _ => sq_nonneg _)
    calc
      _ ≤ ∑ r ∈ S, ‖T (lp.single 2 r (x r))‖ := norm_sum_le _ _
      _ = ∑ r ∈ S, ‖x r‖*‖T (lp.single 2 r (1 : ℂ))‖ := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hunit,norm_smul]
      _ ≤ Real.sqrt (∑ r ∈ S, ‖x r‖^2)*
          Real.sqrt (∑ r ∈ S, ‖T (lp.single 2 r (1 : ℂ))‖^2) :=
        Real.sum_mul_le_sqrt_mul_sqrt S _ _
      _ ≤ Real.sqrt (‖x‖^2)*Real.sqrt B :=
        mul_le_mul (Real.sqrt_le_sqrt hxs) (Real.sqrt_le_sqrt hTs)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_sq (norm_nonneg x),mul_comm]
  have hsum := (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x).mapL T
  have hlim : Tendsto (fun S : Finset ι => ‖∑ r ∈ S, T (lp.single 2 r (x r))‖)
      atTop (𝓝 ‖T x‖) := (continuous_norm.tendsto (T x)).comp hsum
  exact le_of_tendsto hlim (Eventually.of_forall hfinite)

theorem p6ComplexLp_joint_matrix_mass38 {ι κ : Type*}
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : κ => ℂ) 2)
    (hs : Summable (fun p : κ × ι => ‖T (lp.single 2 p.2 (1 : ℂ)) p.1‖^2)) :
    NlsGge.Pilot.IsComplexHilbertSchmidt T ∧
      (∑' r : ι, ‖T (lp.single 2 r (1 : ℂ))‖^2)=
        (∑' p : κ × ι, ‖T (lp.single 2 p.2 (1 : ℂ)) p.1‖^2) ∧
      ‖T‖ ≤ Real.sqrt (∑' p : κ × ι, ‖T (lp.single 2 p.2 (1 : ℂ)) p.1‖^2) := by
  have hrows := (summable_prod_of_nonneg
    (fun p : ι × κ => sq_nonneg (‖T (lp.single 2 p.1 (1 : ℂ)) p.2‖))).mp hs.prod_symm
  have hcol (r : ι) : (∑' m : κ, ‖T (lp.single 2 r (1 : ℂ)) m‖^2)=
      ‖T (lp.single 2 r (1 : ℂ))‖^2 := by
    have hh : HasSum (fun m : κ => ‖T (lp.single 2 r (1 : ℂ)) m‖^2)
        (‖T (lp.single 2 r (1 : ℂ))‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal)
          (T (lp.single 2 r (1 : ℂ)))
    exact hh.tsum_eq
  have hcs : Summable (fun r : ι => ‖T (lp.single 2 r (1 : ℂ))‖^2) := by
    simpa only [hcol] using hrows.2
  have hmass : (∑' r : ι, ‖T (lp.single 2 r (1 : ℂ))‖^2)=
      (∑' p : κ × ι, ‖T (lp.single 2 p.2 (1 : ℂ)) p.1‖^2) := by
    calc
      _ = ∑' r : ι, ∑' m : κ, ‖T (lp.single 2 r (1 : ℂ)) m‖^2 :=
        tsum_congr (fun r => (hcol r).symm)
      _ = ∑' m : κ, ∑' r : ι, ‖T (lp.single 2 r (1 : ℂ)) m‖^2 := hs.tsum_comm
      _ = _ := hs.tsum_prod.symm
  refine ⟨?_,hmass,?_⟩
  · apply NlsGge.Pilot.isComplexHilbertSchmidt_of_summable_basis (p6ComplexLpBasis38 ι)
    simpa only [p6ComplexLpBasis_apply38] using hcs
  · rw [← hmass]
    exact p6ComplexLp_opNorm_le_column_mass38 T hcs

end
end NlsGge.GK38
