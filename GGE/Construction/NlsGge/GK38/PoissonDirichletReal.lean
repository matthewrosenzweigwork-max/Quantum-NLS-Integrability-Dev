import NlsGge.GK38.PoissonDirichletCommute

/-! Every actual real labelled Dirichlet root realizes the complex theorem.
The Hamiltonian direction is proved to be an actual real-slice pair. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.PoissonDirichlet38
noncomputable section

theorem physicalL2_eq_of_coverRep_Icc38 (f g : PhysicalL2)
    (h : coverRep38 f =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] coverRep38 g) : f = g := by
  have _hi := intervalIntegrable_coverRep38_sq_one (f-g)
  have hz : ‖f-g‖^2 = 0 := by
    rw [← integral_sq_coverRep38_one]
    calc
      (∫ s in (0 : ℝ)..1, ‖coverRep38 (f-g) s‖^2) = ∫ _s in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc]
        filter_upwards [h,ae_restrict_of_ae (coverRep38_sub_ae f g)] with s hs hd
        rw [hd,hs,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      _ = 0 := intervalIntegral.integral_zero
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (f-g)]

theorem dirEigenKernel38_realSymmetric (u : PhysicalL2) (n : ℤ) :
    realSymmetric (dirEigenKernel38 (realSlice u) (gkMu u n : ℂ)) := by
  change realSymmetric ((Q (dirState u n))⁻¹ • square (dirState u n))
  rw [real_denominator _ (dirState_real_symmetry u n)]
  intro t
  simp [square,starProd38,dirState_real_symmetry u n t, ← Complex.ofReal_inv]

theorem dirEigenHamField38_realSlice (u : PhysicalL2) (n : ℤ) :
    realSlice (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)).1 =
      dirEigenHamField38 (realSlice u) (gkMu u n : ℂ) := by
  apply Prod.ext
  · rfl
  change star (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)).1 =
    (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)).2
  apply physicalL2_eq_of_coverRep_Icc38
  filter_upwards [dirEigenHamField38_rep (realSlice u) (gkMu u n : ℂ),
    ae_restrict_of_ae (coverRep38_star_ae
      (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)).1),
    ae_restrict_mem measurableSet_Icc] with s hr hs hm
  change coverRep38 (star (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)).1) s =
    potRepSnd38 (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)) s
  rw [hs]
  change star (potRepFst38 (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)) s) = _
  rw [hr.1,hr.2,pairKernelExt38_of_mem _ hm]
  rw [dirEigenKernel38_realSymmetric u n ⟨s,hm⟩]
  simp

theorem actual_dirichlet_labels_mutual_commute38 (u : PhysicalL2) (m n : ℤ) :
    Q (dirState u m) ≠ 0 ∧ Q (dirState u n) ≠ 0 ∧
    IntervalIntegrable (dirEigenWedge38 (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ)) volume 0 1 ∧
    dirEigenPoisson38 (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ) = 0 ∧
    dirImplicitGradient (realSlice u) (gkMu u m : ℂ)
      (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)) = 0 := by
  have h := dirichletMutualCommuteTarget (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ)
    (gkMu_root38 u m) (gkMu_root38 u n)
    (dirichlet_root_deriv_ne_zero38 u (gkMu u m) (gkMu_root38 u m))
    (dirichlet_root_deriv_ne_zero38 u (gkMu u n) (gkMu_root38 u n))
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.trans h.2.2.2.1⟩

theorem actual_fderiv_dirichlet_label_hamField_eq_zero38 (u : PhysicalL2) (m n : ℤ) :
    (fderiv ℝ (fun v : PhysicalL2 => gkMu v m) u)
      (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)).1 = 0 := by
  have h := actual_dirichlet_label_complex_gradient u m
    (dirEigenHamField38 (realSlice u) (gkMu u n : ℂ)).1
  rw [dirEigenHamField38_realSlice,
    (actual_dirichlet_labels_mutual_commute38 u m n).2.2.2.2] at h
  exact_mod_cast h

end
end NlsGge.GK38.PoissonDirichlet38
