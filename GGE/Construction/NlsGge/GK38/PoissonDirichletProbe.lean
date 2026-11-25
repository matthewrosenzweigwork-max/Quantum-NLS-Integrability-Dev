import NlsGge.GK38.PoissonDirichletReal
import NlsGge.GK38.GradEigenRealGradientProbe
import NlsGge.GK38.GradEigenDirichletProbe

/-! Concrete free, nonfree negative-label, nonreal and phase regressions. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.PoissonDirichlet38
noncomputable section

theorem constant_dirState_kernel_field38 (φ : PotPair) (z : ℂ)
    (hc : ∀ t : Time, state φ z ![1,1] t = ![1,1]) :
    Q (state φ z ![1,1]) = 2 ∧
    (∀ t : Time, dirEigenKernel38 φ z t = ![1/2,1/2]) ∧
    dirEigenHamField38 φ z = realSlice (constL2 (-Complex.I/2)) := by
  have _hi := kernel_integrability (state φ z ![1,1])
  have he (s : ℝ) : pairKernelExt38 (state φ z ![1,1]) s = ![1,1] :=
    hc (projIcc 0 1 zero_le_one s)
  have hQ : Q (state φ z ![1,1]) = 2 := by norm_num [Q,he]
  have hk (t : Time) : dirEigenKernel38 φ z t = ![1/2,1/2] := by
    ext i
    fin_cases i <;> norm_num [dirEigenKernel38,hQ,square,hc,starProd38]
  have hkext (s : ℝ) : pairKernelExt38 (dirEigenKernel38 φ z) s = ![1/2,1/2] :=
    hk (projIcc 0 1 zero_le_one s)
  refine ⟨hQ,hk,?_⟩
  rw [realSlice_constL2]
  apply Prod.ext
  · apply physicalL2_eq_of_coverRep_Icc38
    filter_upwards [dirEigenHamField38_rep φ z,
      ae_restrict_of_ae (coverRep38_const_ae (-Complex.I/2))] with s hr hs
    change potRepFst38 (dirEigenHamField38 φ z) s = _
    rw [hr.1,hs,hkext]
    simp only [Matrix.cons_val_one,Matrix.cons_val_fin_one]
    ring
  · apply physicalL2_eq_of_coverRep_Icc38
    filter_upwards [dirEigenHamField38_rep φ z,
      ae_restrict_of_ae (coverRep38_const_ae (star (-Complex.I/2)))] with s hr hs
    change potRepSnd38 (dirEigenHamField38 φ z) s = _
    rw [hr.2,hs,hkext]
    simp
    ring

theorem probe_free_dirichlet_commutation38 (m n : ℤ) :
    gkMu 0 m = (m : ℝ)*Real.pi ∧ gkMu 0 n = (n : ℝ)*Real.pi ∧
    Q (dirState 0 m) = 2 ∧ Q (dirState 0 n) = 2 ∧
    dirEigenPoisson38 0 (gkMu 0 m : ℂ) (gkMu 0 n : ℂ) = 0 ∧
    (fderiv ℝ (fun v : PhysicalL2 => gkMu v m) 0)
      (dirEigenHamField38 0 (gkMu 0 n : ℂ)).1 = 0 := by
  have hQ (k : ℤ) : Q (dirState 0 k) = 2 := by
    rw [real_denominator _ (dirState_real_symmetry 0 k),
      (probe_free_dirichlet_gradient k).2.2.1]
    norm_num
  have hc := (actual_dirichlet_labels_mutual_commute38 0 m n).2.2.2.1
  have hd := actual_fderiv_dirichlet_label_hamField_eq_zero38 0 m n
  rw [realSlice_zero] at hc hd
  exact ⟨gkMu_free38 m,gkMu_free38 n,hQ m,hQ n,hc,hd⟩

theorem probe_free_central_hamField38 :
    Q (state 0 0 ![1,1]) = 2 ∧
    (∀ t : Time, dirEigenKernel38 0 0 t = ![1/2,1/2]) ∧
    dirEigenHamField38 0 0 = realSlice (constL2 (-Complex.I/2)) := by
  apply constant_dirState_kernel_field38
  intro t
  have h := probe_free_dirichlet 0 t
  change state (realSlice 0) (gkMu 0 0 : ℂ) ![1,1] t = _ at h
  rw [realSlice_zero,gkMu_free38] at h
  norm_num only [Int.cast_zero,zero_mul,Complex.ofReal_zero,mul_zero,neg_zero,Complex.exp_zero] at h
  exact h

theorem probe_nonfree_negative_dirichlet_commutation38 :
    gkMu (constL2 1) (-1) = -Real.sqrt (Real.pi^2+1) ∧
    gkMu (constL2 1) 0 = 1 ∧
    Q (dirState (constL2 1) (-1)) ≠ 0 ∧
    dirEigenPoisson38 (realSlice (constL2 1))
      (gkMu (constL2 1) (-1) : ℂ) 1 = 0 ∧
    (fderiv ℝ (fun v : PhysicalL2 => gkMu v (-1)) (constL2 1))
      (constL2 (-Complex.I/2)) = 0 := by
  have hc := actual_dirichlet_labels_mutual_commute38 (constL2 1) (-1) 0
  have hd := actual_fderiv_dirichlet_label_hamField_eq_zero38 (constL2 1) (-1) 0
  have hf := constant_dirState_kernel_field38 (realSlice (constL2 1))
    (gkMu (constL2 1) 0 : ℂ) (probe_constant_dirichlet_state)
  rw [hf.2.2] at hd
  change (fderiv ℝ (fun v : PhysicalL2 => gkMu v (-1)) (constL2 1))
    (constL2 (-Complex.I/2)) = 0 at hd
  have hb := hc.2.2.2.1
  rw [dirichlet_real_constant_labels_probe38.1] at hb
  norm_num only [Complex.ofReal_one] at hb
  exact ⟨dirichlet_real_constant_labels_probe38.2.2,
    dirichlet_real_constant_labels_probe38.1,hc.1,hb,hd⟩

theorem normalized_square_phase_invariant38 (c : ℂ) (v : PairKernelCont38)
    (hc : c ≠ 0) (hQ : Q v ≠ 0) :
    (Q (c • v))⁻¹ • square (c • v) = (Q v)⁻¹ • square v := by
  have hs : (c^2 * Q v)⁻¹ * c^2 = (Q v)⁻¹ := by field_simp
  rw [Q_smul,square_smul,smul_smul,hs]

theorem probe_nonreal_dirichlet_commutation_phase38 :
    let φ : PotPair := (constL2 (2*Complex.I),0)
    let v := state φ Complex.I ![1,1]
    φ ≠ 0 ∧ (∀ u : PhysicalL2, φ ≠ realSlice u) ∧ Q v ≠ 0 ∧
    Q (Complex.I • v) = -Q v ∧ Q (Complex.I • v) ≠ 0 ∧
    (Q (Complex.I • v))⁻¹ • square (Complex.I • v) = dirEigenKernel38 φ Complex.I ∧
    dirEigenPoisson38 φ Complex.I Complex.I = 0 ∧
    dirImplicitGradient φ Complex.I (dirEigenHamField38 φ Complex.I) = 0 := by
  dsimp only
  have hroot := probe_dirichlet_nonreal_simple
  have h := dirichletMutualCommuteTarget _ _ _ hroot.1 hroot.1 hroot.2.2 hroot.2.2
  have hp := probe_dirichlet_nonreal_phase
  exact ⟨probe_dirichlet_nonreal_pair.1,probe_dirichlet_nonreal_pair.2,h.1,
    hp.1,hp.2.1,normalized_square_phase_invariant38 _ _ Complex.I_ne_zero h.1,
    h.2.2.2.1,h.2.2.2.2.trans h.2.2.2.1⟩

end
end NlsGge.GK38.PoissonDirichlet38
