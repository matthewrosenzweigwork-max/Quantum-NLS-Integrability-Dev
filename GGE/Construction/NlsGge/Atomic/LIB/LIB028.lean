import NlsGge.Atomic.IntervalZSBoundary
import NlsGge.Atomic.LIB.LIB027
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# LIB-028: the four symmetric Dirac boundary domains

The literal source endpoint relations cancel the Green boundary form. Smooth
pairs supported in the open interval lift to the distributional H1 carrier and
satisfy every boundary condition. Their actual L2 classes form a dense subspace:
real interior test functions annihilating an orthogonal vector force both its
components to vanish by the local fundamental lemma. No endpoint or absolute
continuity condition is assumed on the L2 vectors in this density argument.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff
namespace NlsGge.Atomic.LIB028
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026

lemma zs_boundaryForm_eq_zero (bc : ZSBoundaryCondition) (f g : H1Pair)
    (hf : HasZSBoundaryCondition bc f) (hg : HasZSBoundaryCondition bc g) :
    zsBoundaryForm f g = 0 := by
  cases bc with
  | dirichlet =>
    rcases hf with ⟨hf0, hf1⟩
    rcases hg with ⟨hg0, hg1⟩
    simp [zsBoundaryForm, hf0, hf1, hg0, hg1]
  | neumann =>
    rcases hf with ⟨hf0, hf1⟩
    rcases hg with ⟨hg0, hg1⟩
    simp [zsBoundaryForm, hf0, hf1, hg0, hg1]
  | periodic =>
    change (∀ b : Bool, traceRight (f b) = traceLeft (f b)) at hf
    change (∀ b : Bool, traceRight (g b) = traceLeft (g b)) at hg
    simp [zsBoundaryForm, hf, hg]
  | antiperiodic =>
    change (∀ b : Bool, traceRight (f b) = -traceLeft (f b)) at hf
    change (∀ b : Bool, traceRight (g b) = -traceLeft (g b)) at hg
    simp [zsBoundaryForm, hf, hg]

/-- The actual L2 Dirac action is symmetric on each literal boundary domain. -/
theorem zs_boundary_domain_symmetric {φ : SourcePairL2} (hφ : IsRealType φ)
    (bc : ZSBoundaryCondition) (f g : H1Pair)
    (hf : HasZSBoundaryCondition bc f) (hg : HasZSBoundaryCondition bc g) :
    inner ℂ (zsApply φ f) (h1PairValue g) = inner ℂ (h1PairValue f) (zsApply φ g) := by
  apply sub_eq_zero.mp
  rw [NlsGge.Atomic.LIB027.zs_green_identity hφ, zs_boundaryForm_eq_zero bc f g hf hg]

lemma smooth_memLp (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    MemLp u 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  hu.continuous.memLp_of_hasCompactSupport hc

lemma smooth_deriv_memLp (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) :
    MemLp (deriv u) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (hu.continuous_deriv (by simp)).memLp_of_hasCompactSupport hc.deriv

lemma smooth_hasWeakDerivative (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) :
    HasWeakDerivative u (deriv u) := by
  intro ψ hψs hψc hψU
  have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (lt_irrefl (0 : ℝ)) (hψU h).1)
  have hψ1 : ψ 1 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (lt_irrefl (1 : ℝ)) (hψU h).2)
  have heq := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu.continuous.continuousOn
    (Complex.continuous_ofReal.comp hψs.continuous).continuousOn
    (fun x _ => ((hu.differentiable (by simp)) x).hasDerivAt)
    (fun x _ => ((hψs.differentiable (by simp)) x).hasDerivAt.ofReal_comp)
    ((hu.continuous_deriv (by simp)).intervalIntegrable 0 1)
    ((Complex.continuous_ofReal.comp (hψs.continuous_deriv (by simp))).intervalIntegrable 0 1)
  simpa only [Function.comp_apply, hψ0, hψ1, Complex.ofReal_zero, mul_zero, sub_self, zero_sub] using heq

def smoothH1 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) : H1 where
  value := (smooth_memLp u hu hc).toLp u
  derivative := (smooth_deriv_memLp u hu hc).toLp (deriv u)
  weak := by
    intro ψ hψs hψc hψU
    have h := smooth_hasWeakDerivative u hu ψ hψs hψc hψU
    have hval := (smooth_memLp u hu hc).coeFn_toLp
    have hder := (smooth_deriv_memLp u hu hc).coeFn_toLp
    have hv : (∫ x in (0 : ℝ)..1,
        ((smooth_memLp u hu hc).toLp u) x * ((deriv ψ x : ℝ) : ℂ)) =
        ∫ x in (0 : ℝ)..1, u x * ((deriv ψ x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr_ae_restrict
      simp only [uIoc_of_le zero_le_one]
      filter_upwards [hval] with x hx
      rw [hx]
    have hd : (∫ x in (0 : ℝ)..1,
        ((smooth_deriv_memLp u hu hc).toLp (deriv u)) x * (ψ x : ℂ)) =
        ∫ x in (0 : ℝ)..1, deriv u x * (ψ x : ℂ) := by
      apply intervalIntegral.integral_congr_ae_restrict
      simp only [uIoc_of_le zero_le_one]
      filter_upwards [hder] with x hx
      rw [hx]
    rw [hv, hd]
    exact h

lemma smoothH1_representative (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (x : Icc (0 : ℝ) 1) :
    representative (smoothH1 u hu hc) x = u x := by
  let F : C(Icc (0 : ℝ) 1, ℂ) := ⟨fun x => u x, hu.continuous.comp continuous_subtype_val⟩
  have heq : F = representative (smoothH1 u hu hc) := by
    apply representative_eq_of_ae
    filter_upwards [(smooth_memLp u hu hc).coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with y hy hmem
    rw [IccExtend_of_mem zero_le_one F ⟨hmem.1.le, hmem.2⟩]
    exact hy.symm
  exact congrArg (fun f : C(Icc (0 : ℝ) 1, ℂ) => f x) heq.symm

lemma smoothH1_traceLeft (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ Ioo (0 : ℝ) 1) :
    traceLeft (smoothH1 u hu hc) = 0 := by
  rw [traceLeft, smoothH1_representative]
  exact image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (lt_irrefl (0 : ℝ)) (hs h).1)

lemma smoothH1_traceRight (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ Ioo (0 : ℝ) 1) :
    traceRight (smoothH1 u hu hc) = 0 := by
  rw [traceRight, smoothH1_representative]
  exact image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (lt_irrefl (1 : ℝ)) (hs h).2)

/-- An actual interval L2 class with an interior smooth compactly supported representative. -/
def IsInteriorSmooth (f : SourceIntervalL2) : Prop :=
  ∃ u : ℝ → ℂ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
    tsupport u ⊆ Ioo (0 : ℝ) 1 ∧ (fun x => f x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] u

/-- The test-pair subspace sits in the actual source L2 Hilbert space. -/
def interiorSmoothPairSubmodule : Submodule ℂ SourcePairL2 where
  carrier := {f | ∀ b : Bool, IsInteriorSmooth (f b)}
  zero_mem' := by
    intro b
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
    · simp
    · exact Lp.coeFn_zero ℂ 2 _
  add_mem' := by
    intro f g hf hg b
    obtain ⟨u, hus, huc, huU, hu⟩ := hf b
    obtain ⟨v, hvs, hvc, hvU, hv⟩ := hg b
    refine ⟨u + v, hus.add hvs, huc.add hvc, ?_, ?_⟩
    · exact (tsupport_add u v).trans (union_subset huU hvU)
    · exact (Lp.coeFn_add (f b) (g b)).trans (hu.add hv)
  smul_mem' := by
    intro c f hf b
    obtain ⟨u, hus, huc, huU, hu⟩ := hf b
    refine ⟨c • u, hus.const_smul c, huc.smul_left, ?_, ?_⟩
    · exact (tsupport_smul_subset_right (fun _ : ℝ => c) u).trans huU
    · exact (Lp.coeFn_smul c (f b)).trans (hu.const_smul c)


lemma interiorSmoothPairSubmodule_orthogonal_eq_bot :
    interiorSmoothPairSubmoduleᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  have hcomponent (b : Bool) : g b = 0 := by
    have htests : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ioo (0 : ℝ) 1 → ∫ x, ψ x • g b x = 0 := by
      intro ψ hψs hψc hψU
      let p : ℝ → ℂ := fun x => (ψ x : ℂ)
      have hps : ContDiff ℝ ∞ p := Complex.ofRealCLM.contDiff.comp hψs
      have hpc : HasCompactSupport p := hψc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
      have hpU : tsupport p ⊆ Ioo (0 : ℝ) 1 :=
        (tsupport_comp_subset (g := fun x : ℝ => (x : ℂ)) (by simp) ψ).trans hψU
      have hpm : MemLp p 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
        hps.continuous.memLp_of_hasCompactSupport hpc
      let pLp : SourceIntervalL2 := hpm.toLp p
      let q : SourcePairL2 := PiLp.single 2 b pLp
      have hq : q ∈ interiorSmoothPairSubmodule := by
        intro c
        by_cases hcb : c = b
        · subst c
          refine ⟨p, hps, hpc, hpU, ?_⟩
          simpa only [q, PiLp.single_eq_same] using hpm.coeFn_toLp
        · refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, ?_⟩
          simpa only [q, PiLp.single_eq_of_ne 2 hcb] using
            (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1)))
      have hz := interiorSmoothPairSubmodule.inner_right_of_mem_orthogonal hq hg
      have hinner : inner ℂ pLp (g b) = 0 := by
        rw [PiLp.inner_apply, Fintype.sum_bool] at hz
        cases b <;> simpa [q] using hz
      have hid : inner ℂ pLp (g b) = ∫ x, ψ x • g b x := by
        rw [NlsGge.Atomic.LIB027.sourceInterval_inner_eq_integral]
        calc
          _ = ∫ x in (0 : ℝ)..1, g b x * (ψ x : ℂ) := by
            apply intervalIntegral.integral_congr_ae_restrict
            simp only [uIoc_of_le zero_le_one]
            filter_upwards [hpm.coeFn_toLp] with x hx
            change star (pLp x) * g b x = _
            rw [show pLp x = (ψ x : ℂ) from hx]
            simp [mul_comm]
          _ = ∫ x, g b x * (ψ x : ℂ) := interval_integral_mul_test_eq_integral _ hψU
          _ = ∫ x, ψ x • g b x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Complex.real_smul]
            ring
      rw [← hid]
      exact hinner
    have hi : IntegrableOn (fun x => g b x) (Ioo (0 : ℝ) 1) volume :=
      (intervalIntegrable_L2 (g b)).def'.mono_set (by
        rw [uIoc_of_le zero_le_one]
        exact Ioo_subset_Ioc_self)
    have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hi.locallyIntegrableOn htests
    have hzI : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), g b x = 0 :=
      (ae_restrict_iff' measurableSet_Ioo).mpr hz
    rw [restrict_Ioo_eq_restrict_Ioc] at hzI
    apply Lp.ext
    filter_upwards [hzI, Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))]
      with x hx hzero
    exact hx.trans hzero.symm
  have hgz : g = 0 := by
    apply PiLp.ext
    intro b
    exact hcomponent b
  change g = 0
  exact hgz

theorem interiorSmoothPairSubmodule_dense :
    Dense (interiorSmoothPairSubmodule : Set SourcePairL2) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr
    ((Submodule.topologicalClosure_eq_top_iff).mpr
      interiorSmoothPairSubmodule_orthogonal_eq_bot)


/-- Every actual smooth compact-interior pair belongs to each source boundary domain. -/
theorem interiorSmoothPairSubmodule_subset_boundaryDomain (bc : ZSBoundaryCondition) :
    (interiorSmoothPairSubmodule : Set SourcePairL2) ⊆ zsBoundaryDomain bc := by
  intro g hg
  change ∀ b : Bool, IsInteriorSmooth (g b) at hg
  choose u hus huc huU hueq using hg
  let f : H1Pair := fun b => smoothH1 (u b) (hus b) (huc b)
  have hL (b : Bool) : traceLeft (f b) = 0 :=
    smoothH1_traceLeft (u b) (hus b) (huc b) (huU b)
  have hR (b : Bool) : traceRight (f b) = 0 :=
    smoothH1_traceRight (u b) (hus b) (huc b) (huU b)
  have hbc : HasZSBoundaryCondition bc f := by
    cases bc <;> simp [HasZSBoundaryCondition, hL, hR]
  refine ⟨f, hbc, ?_⟩
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [(smooth_memLp (u b) (hus b) (huc b)).coeFn_toLp, hueq b] with x hx hy
  change ((smooth_memLp (u b) (hus b) (huc b)).toLp (u b)) x = g b x
  exact hx.trans hy.symm

/-- Any actual L2 pair represented by smooth compact-interior tests lies in every domain. -/
theorem zs_compact_test_mem_boundaryDomain (bc : ZSBoundaryCondition)
    (g : SourcePairL2) (u : Bool → ℝ → ℂ)
    (hus : ∀ b, ContDiff ℝ ∞ (u b)) (huc : ∀ b, HasCompactSupport (u b))
    (huU : ∀ b, tsupport (u b) ⊆ Ioo (0 : ℝ) 1)
    (hueq : ∀ b, (fun x => g b x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] u b) :
    g ∈ zsBoundaryDomain bc :=
  interiorSmoothPairSubmodule_subset_boundaryDomain bc
    (fun b => ⟨u b, hus b, huc b, huU b, hueq b⟩)

/-- Each of the four literal source boundary domains is dense in the actual interval L2 pair. -/
theorem zs_boundary_domain_dense (bc : ZSBoundaryCondition) : Dense (zsBoundaryDomain bc) :=
  interiorSmoothPairSubmodule_dense.mono (interiorSmoothPairSubmodule_subset_boundaryDomain bc)

end NlsGge.Atomic.LIB028
