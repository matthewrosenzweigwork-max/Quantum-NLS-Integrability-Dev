import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.ThirdConsultation.G5.G5017Support1
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G1.G1052
import NlsGge.GK38.GradFundamentalGradient
import NlsGge.GK38.PairRealBridge
import NlsGge.GK38.RealTypeMultiplicityRealDeriv
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.AbelianPeriods
import NlsGge.Spectral.ActualGapActionAllNE02_38

/- G5-032 SUPPORT 1 `G5032Sup1` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5032Sup1.lean, namespace NlsGge.GKDefinitionDesign.G5032Sup1.
   (R) Reality of the double bracket on the real axis (closes blocker 1 of proof development/G5032_STOP.md), from landed definitions only:
       cartesianX/Y are real on the real slice (hypothesis hXY here; discharged by the landed G4040 in the final G5032) => their complex derivatives at real points are real on real
       directions => angleDerivative is a real covector at real points => anglePoisson is real on the real slice => its derivative is a
       real covector => its Hamiltonian field at a real point lies in the real slice (bilinear gradient of a real covector:
       second component = star of the first) => {Delta(x), {theta_m, theta_n}} = dDelta(x)[real direction] is real for real x
       (Delta real on real slice x real axis: landed discrim_real_restriction38).
   (A) The double bracket is entire in lam: it is dG(phi,lam)(Y,0) for G(phi,lam) = discrim phi lam jointly analytic.
   (C) core32: the G5-032 conclusion from vanishing periods (G2-046 in every gap, choice, real labelling of the gaps
       (lamPlus_real, level sets of the quasimomentum => injectivity), l2 from G1-052). -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.GKDefinitionDesign
namespace G5032Sup1
noncomputable section

/-- A complex function real on the real slice has a complex derivative that is real on real directions. -/
theorem fderiv_realSlice_im (h : PotPair → ℂ) (hr : ∀ w : PhysicalL2, (h (realSlice w)).im = 0)
    (u a : PhysicalL2) : (fderiv ℂ h (realSlice u) (realSlice a)).im = 0 := by
  by_cases hd : DifferentiableAt ℂ h (realSlice u)
  · have h1 : HasFDerivAt (fun w : PhysicalL2 => (h (realSlice w)).im)
        (Complex.imCLM.comp ((fderiv ℂ h (realSlice u)).restrictScalars ℝ ∘L realSlice)) u :=
      Complex.imCLM.hasFDerivAt.comp u
        ((hd.hasFDerivAt.restrictScalars ℝ).comp u realSlice.hasFDerivAt)
    have h2 : HasFDerivAt (fun w : PhysicalL2 => (h (realSlice w)).im)
        (0 : PhysicalL2 →L[ℝ] ℝ) u := by
      have e : (fun w : PhysicalL2 => (h (realSlice w)).im) = fun _ => (0 : ℝ) := funext hr
      rw [e]
      exact hasFDerivAt_const 0 u
    have h3 := congrArg (fun L : PhysicalL2 →L[ℝ] ℝ => L a) (h1.unique h2)
    simpa using h3
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simp

/-- The bilinear gradient of a functional that is real on the real slice: second component is the star of the first. -/
theorem star_pairGradientCLM_snd (L : PotPair →L[ℂ] ℂ)
    (hL : ∀ a : PhysicalL2, (L (realSlice a)).im = 0) :
    star (pairGradientCLM L).2 = (pairGradientCLM L).1 := by
  have key : ∀ w : PhysicalL2, inner ℂ (star (pairGradientCLM L).2) (star w) =
      inner ℂ (pairGradientCLM L).1 (star w) := by
    intro w
    have e1 : L (realSlice w) = inner ℂ (star (pairGradientCLM L).1) w +
        inner ℂ (star (pairGradientCLM L).2) (star w) := by
      rw [clm_eq_bilinPair L]
      rfl
    have e2 : L (realSlice (Complex.I • w)) =
        Complex.I * inner ℂ (star (pairGradientCLM L).1) w -
          Complex.I * inner ℂ (star (pairGradientCLM L).2) (star w) := by
      rw [clm_eq_bilinPair L]
      simp only [realSlice_apply, star_smul_lp, Complex.conj_I, inner_smul_right]
      ring
    have h1 := hL w
    have h2 := hL (Complex.I • w)
    rw [e1] at h1
    rw [e2] at h2
    set A := inner ℂ (star (pairGradientCLM L).1) w with hA
    set B := inner ℂ (star (pairGradientCLM L).2) (star w) with hB
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add] at h1 h2
    have hBA : B = (starRingEnd ℂ) A := by
      apply Complex.ext
      · simp only [Complex.conj_re]
        linarith
      · simp only [Complex.conj_im]
        linarith
    rw [hBA, hA, inner_conj_symm, ← star_star w, bilinPair_comm (star w) (star (pairGradientCLM L).1),
      star_star, star_star]
  apply ext_inner_right ℂ
  intro v
  have := key (star v)
  rwa [star_star] at this

/-- The Hamiltonian vector field of a real covector lies in the real slice. -/
theorem hamField_eq_realSlice (M : PotPair →L[ℂ] ℂ)
    (hM : ∀ a : PhysicalL2, (M (realSlice a)).im = 0) :
    ((-Complex.I • (pairGradientCLM M).2, Complex.I • (pairGradientCLM M).1) : PotPair) =
      realSlice (-Complex.I • (pairGradientCLM M).2) := by
  rw [realSlice_apply, star_smul_lp, star_pairGradientCLM_snd M hM, map_neg, Complex.conj_I, neg_neg]

/-- The Poisson pairing of two real covectors is real. -/
theorem pairPoissonCLM_im (L M : PotPair →L[ℂ] ℂ)
    (hL : ∀ a : PhysicalL2, (L (realSlice a)).im = 0)
    (hM : ∀ a : PhysicalL2, (M (realSlice a)).im = 0) :
    (pairPoissonCLM L M).im = 0 := by
  unfold pairPoissonCLM
  rw [hamField_eq_realSlice M hM]
  exact hL _

/-- The angle differential at a real point is a real covector, given that cartesianX/Y are real on the real slice
    (the hypothesis `hXY` is discharged by the landed G4040 in the final G5032). -/
theorem angleDerivative_realSlice_im
    (hXY : ∀ (j : ℤ) (v : PhysicalL2),
      (cartesianX j (realSlice v)).im = 0 ∧ (cartesianY j (realSlice v)).im = 0)
    (n : ℤ) (w a : PhysicalL2) :
    (angleDerivative n (realSlice w) (realSlice a)).im = 0 := by
  have hX := (hXY n w).1
  have hY := (hXY n w).2
  have hdX := fderiv_realSlice_im (cartesianX n) (fun v => (hXY n v).1) w a
  have hdY := fderiv_realSlice_im (cartesianY n) (fun v => (hXY n v).2) w a
  rw [← Complex.conj_eq_iff_im] at hX hY hdX hdY ⊢
  simp only [angleDerivative, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul, map_mul, map_inv₀, map_sub, map_add, map_pow, hX, hY, hdX, hdY]

/-- The angle-angle bracket is real on the real slice. -/
theorem anglePoisson_realSlice_im
    (hXY : ∀ (j : ℤ) (v : PhysicalL2),
      (cartesianX j (realSlice v)).im = 0 ∧ (cartesianY j (realSlice v)).im = 0)
    (m n : ℤ) (w : PhysicalL2) :
    (anglePoisson m n (realSlice w)).im = 0 :=
  pairPoissonCLM_im _ _ (angleDerivative_realSlice_im hXY m w) (angleDerivative_realSlice_im hXY n w)

/-- The Hamiltonian field of the angle-angle bracket at a real point lies in the real slice. -/
theorem pairHamiltonianField_anglePoisson_realSlice
    (hXY : ∀ (j : ℤ) (v : PhysicalL2),
      (cartesianX j (realSlice v)).im = 0 ∧ (cartesianY j (realSlice v)).im = 0)
    (m n : ℤ) (u : PhysicalL2) :
    pairHamiltonianField (anglePoisson m n) (realSlice u) =
      realSlice (-Complex.I • (pairGradientCLM (fderiv ℂ (anglePoisson m n) (realSlice u))).2) :=
  hamField_eq_realSlice _
    (fderiv_realSlice_im (anglePoisson m n) (anglePoisson_realSlice_im hXY m n) u)

/-- (R) The double bracket is real on the real axis. -/
theorem doubleBracket_real
    (hXY : ∀ (j : ℤ) (v : PhysicalL2),
      (cartesianX j (realSlice v)).im = 0 ∧ (cartesianY j (realSlice v)).im = 0)
    (m n : ℤ) (u : PhysicalL2) (x : ℝ) :
    (doubleAngleDiscriminantBracket m n (realSlice u) (x : ℂ)).im = 0 := by
  show (fderiv ℂ (fun ψ : PotPair => discrim ψ (x : ℂ)) (realSlice u)
    (pairHamiltonianField (anglePoisson m n) (realSlice u))).im = 0
  rw [pairHamiltonianField_anglePoisson_realSlice hXY m n u]
  exact fderiv_realSlice_im _ (fun w => discrim_real_restriction38 w x) u _

/-- The `phi`-gradient of the discriminant is the partial derivative of the joint map. -/
theorem gradDiscrimCLM_eq_fderiv (φ : PotPair) (z : ℂ) :
    gradDiscrimCLM φ z = (fderiv ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) (φ, z)).comp
      (ContinuousLinearMap.inl ℂ PotPair ℂ) := by
  have hG : DifferentiableAt ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) (φ, z) :=
    (analyticOnNhd_discrim (φ, z) (mem_univ _)).differentiableAt
  have h1 : HasFDerivAt (fun ψ : PotPair => discrim ψ z)
      ((fderiv ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) (φ, z)).comp
        (ContinuousLinearMap.inl ℂ PotPair ℂ)) φ := by
    have hi := hasFDerivAt_prodMk_left (𝕜 := ℂ) φ z
    exact hG.hasFDerivAt.comp φ hi
  exact (hasFDerivAt_gradDiscrimCLM φ z).unique h1

/-- (A) The double bracket is entire in `lam`. -/
theorem doubleBracket_analytic (m n : ℤ) (φ : PotPair) :
    AnalyticOnNhd ℂ (doubleAngleDiscriminantBracket m n φ) univ := by
  intro z _
  have hB : doubleAngleDiscriminantBracket m n φ = fun lam =>
      (ContinuousLinearMap.apply ℂ ℂ ((pairHamiltonianField (anglePoisson m n) φ, (0 : ℂ)) : PotPair × ℂ))
        (fderiv ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) (φ, lam)) := by
    funext lam
    show fderiv ℂ (fun ψ : PotPair => discrim ψ lam) φ (pairHamiltonianField (anglePoisson m n) φ) = _
    rw [(hasFDerivAt_gradDiscrimCLM φ lam).fderiv, gradDiscrimCLM_eq_fderiv]
    rfl
  rw [hB]
  have hD : AnalyticAt ℂ (fderiv ℂ (fun p : PotPair × ℂ => discrim p.1 p.2)) (φ, z) :=
    analyticOnNhd_discrim.fderiv (φ, z) (mem_univ _)
  have hc : AnalyticAt ℂ (fun lam : ℂ => ((φ, lam) : PotPair × ℂ)) z :=
    analyticAt_const.prod analyticAt_id
  exact ((ContinuousLinearMap.apply ℂ ℂ _).analyticAt _).comp (hD.comp hc)

/-- (C) The G5-032 conclusion from the vanishing of all periods of the double bracket. -/
theorem core32
    (hXY : ∀ (j : ℤ) (v : PhysicalL2),
      (cartesianX j (realSlice v)).im = 0 ∧ (cartesianY j (realSlice v)).im = 0)
    (u : PhysicalL2) (m n : ℤ)
    (hper : ∀ k : ℤ,
      abelianPeriod38 k (realSlice u) (doubleAngleDiscriminantBracket m n (realSlice u)) = 0) :
    ∃ ν : ℤ → ℝ, Function.Injective ν ∧
      (∀ k : ℤ, ν k ∈ Set.Icc (actualGapLowerAllE02_38 u k)
        (actualGapUpperAllE02_38 u k) ∧
        doubleAngleDiscriminantBracket m n (realSlice u) (ν k : ℂ) = 0) ∧
      Memℓp (fun k : ℤ => ν k - (k : ℝ) * Real.pi) 2 := by
  have hzero : ∀ k : ℤ, ∃ x : ℝ,
      x ∈ Set.Icc (actualGapLowerAllE02_38 u k) (actualGapUpperAllE02_38 u k) ∧
        doubleAngleDiscriminantBracket m n (realSlice u) (x : ℂ) = 0 := by
    intro k
    obtain ⟨-, x, hx, hfx⟩ := G2_046 u k (discC (realSlice u)) (discR (realSlice u))
      (isolating_family38 (realSlice u) (realSlice_mem_gkW u))
      (doubleAngleDiscriminantBracket m n (realSlice u))
      ((doubleBracket_analytic m n (realSlice u)).mono (subset_univ _))
      (fun x _ => doubleBracket_real hXY m n u x) (hper k)
    refine ⟨x, ?_, hfx⟩
    obtain ⟨hp, hm'⟩ := lamPlus_real u k
    have hLU : actualGapLowerAllE02_38 u k ≤ actualGapUpperAllE02_38 u k := by
      obtain ⟨⟨y, hy⟩, hI⟩ := actualGapLevelSet_eq_Icc_E02_38 u k
      rw [hI] at hy
      exact hy.1.trans hy.2
    have hx' : (x : ℂ) ∈ segment ℝ (lamMinus (realSlice u) k) (lamPlus (realSlice u) k) := hx
    rw [hp, hm'] at hx'
    have hseg : x ∈ segment ℝ (actualGapLowerAllE02_38 u k) (actualGapUpperAllE02_38 u k) := by
      obtain ⟨a, b, ha, hb, hab, hxe⟩ := hx'
      refine ⟨a, b, ha, hb, hab, ?_⟩
      have := congrArg Complex.re hxe
      simpa using this
    rwa [segment_eq_Icc hLU] at hseg
  choose ν hν using hzero
  have hlev : ∀ k : ℤ, actualQuasimomentumRealPartE02_38 u (ν k) = (k : ℝ) * Real.pi := by
    intro k
    have h := (hν k).1
    rw [← (actualGapLevelSet_eq_Icc_E02_38 u k).2] at h
    exact h
  refine ⟨ν, ?_, hν, ?_⟩
  · intro j k hjk
    have h := hlev j
    rw [hjk, hlev k] at h
    have h' : (k : ℝ) = (j : ℝ) := mul_right_cancel₀ Real.pi_ne_zero h
    exact_mod_cast h'.symm
  · obtain ⟨V, hV, C, hC⟩ := NlsGge.Atomic.G1052S3.G1052_main.1 (realSlice u)
    obtain ⟨hsum, -⟩ := hC (realSlice u) (mem_of_mem_nhds hV)
    apply memℓp_gen
    rw [ENNReal.toReal_ofNat]
    refine hsum.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    obtain ⟨hp, hm'⟩ := lamPlus_real u k
    have e : ∀ y : ℝ, ‖(y : ℂ) - (k : ℂ) * (Real.pi : ℂ)‖ = |y - (k : ℝ) * Real.pi| := by
      intro y
      rw [show (y : ℂ) - (k : ℂ) * (Real.pi : ℂ) = ((y - (k : ℝ) * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hp, hm', e, e, Real.rpow_two, Real.norm_eq_abs, sq_abs, sq_abs, sq_abs]
    obtain ⟨h1, h2⟩ := (hν k).1
    rcases le_total (ν k) ((k : ℝ) * Real.pi) with h | h
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (add_nonneg (sub_nonneg.2 h)
        (sub_nonneg.2 (h1.trans h))), sq_nonneg (actualGapUpperAllE02_38 u k - (k : ℝ) * Real.pi)]
    · nlinarith [mul_nonneg (sub_nonneg.2 h2) (add_nonneg (sub_nonneg.2 h)
        (sub_nonneg.2 (h.trans h2))), sq_nonneg (actualGapLowerAllE02_38 u k - (k : ℝ) * Real.pi)]

end
end G5032Sup1
end NlsGge.GKDefinitionDesign
