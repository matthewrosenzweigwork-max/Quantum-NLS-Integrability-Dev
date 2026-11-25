import NlsGge.GK38.GradEigenPeriodicSpectral
import NlsGge.GK38.GradEigenDirichlet
set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem state_seed_smul (φ : PotPair) (z s : ℂ) (a : PairVec38) :
    state φ z (s • a) = s • state φ z a := by
  ext t i
  simp [state,smul_add,smul_smul,mul_assoc]
  ring

theorem periodic_perChar_deriv (φ : PotPair) (z : ℂ) :
    deriv (perChar φ) z = (2*discrim φ z)*deriv (discrim φ) z := by
  have h := ((analyticOnNhd_discrim_z φ) z (mem_univ _)).differentiableAt.hasDerivAt
  have hp := (h.pow 2).sub_const 4
  exact (show HasDerivAt (perChar φ)
    ((2*discrim φ z)*deriv (discrim φ) z) z by
      simpa only [perChar,perCharOf,Nat.reduceSub,pow_one] using! hp).deriv

theorem periodic_simple_discrim_nonzero (φ : PotPair) (z : ℂ)
    (hsimple : deriv (perChar φ) z ≠ 0) : deriv (discrim φ) z ≠ 0 := by
  intro hz
  apply hsimple
  rw [periodic_perChar_deriv,hz,mul_zero]

theorem periodic_chart_coverage (φ : PotPair) (z c : ℂ) (a : PairVec38)
    (hc : c^2=1) (ha : a ≠ 0)
    (he : Matrix.mulVec (monodromyPair φ z) a = c • a)
    (hsimple : deriv (perChar φ) z ≠ 0) :
    monodromyPair φ z 0 1 ≠ 0 ∨ monodromyPair φ z 1 0 ≠ 0 := by
  have htrace := periodic_eigen_trace _ c a hc (monodromy_det_scalar φ z) ha he
  by_cases h01 : monodromyPair φ z 0 1=0
  · right
    intro h10
    have hscalar := periodic_diagonal_scalar _ c hc (monodromy_det_scalar φ z) htrace h01 h10
    exact periodic_simple_discrim_nonzero φ z hsimple
      (periodic_scalar_spectral_deriv_zero φ z c hscalar)
  · exact Or.inl h01

theorem periodic_kernel01 (φ : PotPair) (z c : ℂ)
    (hs : c+c=monodromyPair φ z 0 0+monodromyPair φ z 1 1)
    (hc : c*c=1) (hb : monodromyPair φ z 0 1 ≠ 0) :
    gradDiscrimCont38 φ z = (-Complex.I*monodromyPair φ z 0 1) •
      square (state φ z (floquetSeed01 φ z c)) := by
  apply ContinuousMap.ext
  intro t
  have h := congrArg (fun v : PairVec38 => (-Complex.I) • v)
    (floquet_gradient01 φ z c c hs hc hb t)
  have hI : (-Complex.I)*Complex.I=1 := by simp
  simp only [smul_smul,hI,one_smul] at h
  change gradDiscrim38 φ z t = (-Complex.I*monodromyPair φ z 0 1) •
    starProd38 (state φ z (floquetSeed01 φ z c) t) (state φ z (floquetSeed01 φ z c) t)
  exact h

theorem periodic_kernel10 (φ : PotPair) (z c : ℂ)
    (hs : c+c=monodromyPair φ z 0 0+monodromyPair φ z 1 1)
    (hc : c*c=1) (hb : monodromyPair φ z 1 0 ≠ 0) :
    gradDiscrimCont38 φ z = (Complex.I*monodromyPair φ z 1 0) •
      square (state φ z (floquetSeed10 φ z c)) := by
  apply ContinuousMap.ext
  intro t
  have h := congrArg (fun v : PairVec38 => (-Complex.I) • v)
    (floquet_gradient10 φ z c c hs hc hb t)
  have hI : (-Complex.I)*Complex.I=1 := by simp
  simp only [smul_smul,hI,one_smul,neg_mul_neg] at h
  change gradDiscrim38 φ z t = (Complex.I*monodromyPair φ z 1 0) •
    starProd38 (state φ z (floquetSeed10 φ z c) t) (state φ z (floquetSeed10 φ z c) t)
  exact h

theorem periodic_gradient_from_kernel (φ : PotPair) (z k : ℂ) (w : PairKernelCont38)
    (hd : deriv (discrim φ) z ≠ 0)
    (hk : gradDiscrimCont38 φ z = k • square w)
    (hs : deriv (discrim φ) z = -k*Q w) :
    Q w ≠ 0 ∧ perImplicitGradient φ z = bilinearGradient w := by
  have hQ : Q w ≠ 0 := by
    intro hz
    apply hd
    rw [hs,hz,mul_zero]
  have hinv : -(deriv (discrim φ) z)⁻¹*k=(Q w)⁻¹ := by
    field_simp
    linear_combination -hs
  refine ⟨hQ,?_⟩
  unfold perImplicitGradient bilinearGradient
  change -(deriv (discrim φ) z)⁻¹ • integralPairCLM38 (gradDiscrimCont38 φ z) t1 = _
  rw [hk,integralPairCLM38_kernelSmul,smul_smul,hinv]

theorem periodic_canonical_gradient01 (φ : PotPair) (z c : ℂ)
    (hs : c+c=monodromyPair φ z 0 0+monodromyPair φ z 1 1)
    (hc : c*c=1) (hb : monodromyPair φ z 0 1 ≠ 0)
    (hd : deriv (discrim φ) z ≠ 0) :
    Q (state φ z (floquetSeed01 φ z c)) ≠ 0 ∧
      perImplicitGradient φ z=bilinearGradient (state φ z (floquetSeed01 φ z c)) := by
  apply periodic_gradient_from_kernel φ z (-Complex.I*monodromyPair φ z 0 1) _ hd
    (periodic_kernel01 φ z c hs hc hb)
  rw [periodic_spectral_Q01 φ z c hs hc hb]
  ring

theorem periodic_canonical_gradient10 (φ : PotPair) (z c : ℂ)
    (hs : c+c=monodromyPair φ z 0 0+monodromyPair φ z 1 1)
    (hc : c*c=1) (hb : monodromyPair φ z 1 0 ≠ 0)
    (hd : deriv (discrim φ) z ≠ 0) :
    Q (state φ z (floquetSeed10 φ z c)) ≠ 0 ∧
      perImplicitGradient φ z=bilinearGradient (state φ z (floquetSeed10 φ z c)) := by
  apply periodic_gradient_from_kernel φ z (Complex.I*monodromyPair φ z 1 0) _ hd
    (periodic_kernel10 φ z c hs hc hb)
  simpa only [neg_mul] using periodic_spectral_Q10 φ z c hs hc hb

theorem periodic_arbitrary_eigenvector_gradient (φ : PotPair) (z c : ℂ) (a : PairVec38)
    (hc : c^2=1) (hsimple : deriv (perChar φ) z ≠ 0)
    (ha : a ≠ 0) (he : Matrix.mulVec (monodromyPair φ z) a=c • a) :
    Q (state φ z a) ≠ 0 ∧ deriv (discrim φ) z ≠ 0 ∧
      perImplicitGradient φ z=bilinearGradient (state φ z a) := by
  have hd := periodic_simple_discrim_nonzero φ z hsimple
  have htrace := periodic_eigen_trace _ c a hc (monodromy_det_scalar φ z) ha he
  have hs : c+c=monodromyPair φ z 0 0+monodromyPair φ z 1 1 := by
    linear_combination -htrace
  have hc' : c*c=1 := by simpa only [pow_two] using hc
  rcases periodic_chart_coverage φ z c a hc ha he hsimple with h01 | h10
  · obtain ⟨ha0,haeq⟩ := periodic_eigen_chart01 _ c a ha he h01
    have hstate : state φ z a=a 0 • state φ z (floquetSeed01 φ z c) := by
      change a = a 0 • floquetSeed01 φ z c at haeq
      exact (congrArg (state φ z) haeq).trans (state_seed_smul φ z (a 0) _)
    obtain ⟨hQ,hgrad⟩ := periodic_canonical_gradient01 φ z c hs hc' h01 hd
    refine ⟨?_,hd,?_⟩
    · rw [hstate,Q_smul]
      exact mul_ne_zero (pow_ne_zero 2 ha0) hQ
    · rw [hstate,bilinear_gradient_smul _ _ ha0 hQ]
      exact hgrad
  · obtain ⟨ha1,haeq⟩ := periodic_eigen_chart10 _ c a ha he h10
    have hstate : state φ z a=a 1 • state φ z (floquetSeed10 φ z c) := by
      change a = a 1 • floquetSeed10 φ z c at haeq
      exact (congrArg (state φ z) haeq).trans (state_seed_smul φ z (a 1) _)
    obtain ⟨hQ,hgrad⟩ := periodic_canonical_gradient10 φ z c hs hc' h10 hd
    refine ⟨?_,hd,?_⟩
    · rw [hstate,Q_smul]
      exact mul_ne_zero (pow_ne_zero 2 ha1) hQ
    · rw [hstate,bilinear_gradient_smul _ _ ha1 hQ]
      exact hgrad

end
end NlsGge.GK38.GradEigen38
