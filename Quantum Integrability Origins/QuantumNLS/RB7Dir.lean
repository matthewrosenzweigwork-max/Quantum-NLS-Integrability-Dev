import Mathlib
import QuantumNLS.RB7Reg
import QuantumNLS.RB7HJoint
import QuantumNLS.HierarchyFlow

/-!
# R-7B122087 `thm:hierarchy`: derivative of `Re I_{r+1}` along smooth directions through the chart (RB7Dir)

Printed: "Full Hilbert symplecticity, tested against smooth variations, identifies its derivative with `-i∇I_{r+1}(u(t))`.  The test gradients and vectors are smooth and the sums converge."

* `smoothL2_add_smul`, `smoothL2_const_mul`, `inner_smoothL2` (`⟨[g],[h]⟩ = ∫_0^L conj g h` = `HierarchyFlow.pair L g h`): the function-level pairing of DEF-015 is the `L²(𝕋_L)` inner product.
* `eq_of_re_inner`: two `L²` classes whose real inner products against every smooth periodic test function agree are equal (Fourier modes `e_n` and `i e_n`).
* `dir_deriv` (A8, smooth directions): for smooth periodic `f` there is `v ∈ L²` with `DΦ(f) v = -i G` (`G` the coordinate gradient of `F_r` at `Φ f`, in `h^{2S_r}`), such that for every smooth
  periodic `h`, `d/dε Re I_{r+1}(f + εh)|₀ = 2 Re⟨i v, h⟩`.  This is `RB7Plumb.dI_RF535` with REG-015 (`REG015Concl`) supplying the chart curve `ε ↦ Φ(f + εh)` in `h^{2S_r}`.
* `grad_eq_of_isSmoothGradient`: a DEF-015 smooth gradient `g` of `HierarchyFlow.hamiltonian L κ r` at `f` (`HierarchyFlow.IsSmoothGradient`) satisfies `smoothL2 g = i v`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology NNReal ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.Reg015Setting QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.WeakDerivatives QuantumNLS.LossSobolev

variable {L κ : ℝ} [Fact (0 < L)]

theorem smooth_add_smul {f h : ℝ → ℂ} (hf : SmoothPeriodic L f) (hh : SmoothPeriodic L h) (ε : ℂ) :
    SmoothPeriodic L (fun x => f x + ε * h x) :=
  ⟨hf.smooth.add (contDiff_const.mul hh.smooth), fun x => by
    simp only [hf.periodic x, hh.periodic x]⟩

theorem smooth_const_mul {h : ℝ → ℂ} (hh : SmoothPeriodic L h) (c : ℂ) : SmoothPeriodic L (fun x => c * h x) :=
  ⟨contDiff_const.mul hh.smooth, fun x => by simp only [hh.periodic x]⟩

theorem smoothL2_add_smul {f h : ℝ → ℂ} (hf : SmoothPeriodic L f) (hh : SmoothPeriodic L h) (ε : ℂ)
    (hs : SmoothPeriodic L (fun x => f x + ε * h x)) :
    smoothL2 hs = smoothL2 hf + ε • smoothL2 hh := by
  unfold smoothL2
  rw [← map_smul, ← map_add]
  congr 1
  ext p
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
  simp [liftC_coe]

theorem smoothL2_const_mul {h : ℝ → ℂ} (hh : SmoothPeriodic L h) (c : ℂ) (hs : SmoothPeriodic L (fun x => c * h x)) :
    smoothL2 hs = c • smoothL2 hh := by
  unfold smoothL2
  rw [← map_smul]
  congr 1
  ext p
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
  simp [liftC_coe]

/-- `⟨[g], [h]⟩_{L²} = ∫_0^L conj g · h` (`HierarchyFlow.pair`). -/
theorem inner_smoothL2 {g h : ℝ → ℂ} (hg : SmoothPeriodic L g) (hh : SmoothPeriodic L h) :
    inner ℂ (smoothL2 hg) (smoothL2 hh) = HierarchyFlow.pair L g h := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∀ᵐ a ∂(volume : Measure (AddCircle L)),
      inner ℂ ((smoothL2 hg : L2T L) a) ((smoothL2 hh : L2T L) a) =
        conj ((liftC hg.smooth.continuous hg.periodic : C(AddCircle L, ℂ)) a) *
          (liftC hh.smooth.continuous hh.periodic : C(AddCircle L, ℂ)) a := by
    filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) (volume : Measure (AddCircle L))
        (liftC hg.smooth.continuous hg.periodic),
      ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) (volume : Measure (AddCircle L))
        (liftC hh.smooth.continuous hh.periodic)] with a ha hb
    have e1 : (smoothL2 hg : L2T L) a = (liftC hg.smooth.continuous hg.periodic : C(AddCircle L, ℂ)) a := ha
    have e2 : (smoothL2 hh : L2T L) a = (liftC hh.smooth.continuous hh.periodic : C(AddCircle L, ℂ)) a := hb
    rw [e1, e2]
    exact RCLike.inner_apply' _ _
  rw [integral_congr_ae h1]
  have h2 := AddCircle.intervalIntegral_preimage L 0 (fun a : AddCircle L =>
    conj ((liftC hg.smooth.continuous hg.periodic : C(AddCircle L, ℂ)) a) *
      (liftC hh.smooth.continuous hh.periodic : C(AddCircle L, ℂ)) a)
  rw [zero_add] at h2
  rw [← h2]
  unfold HierarchyFlow.pair
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [liftC_coe]

/-- The smooth periodic function `e_n`. -/
theorem smoothPeriodic_cfun (n : ℤ) : SmoothPeriodic L (RB7H.cfun L n) :=
  ⟨RB7H.contDiff_cfun n, fun x => RB7H.cfun_add_period n x⟩

theorem smoothL2_cfun (n : ℤ) : smoothL2 (smoothPeriodic_cfun (L := L) n) = modeLp L n := by
  unfold smoothL2 modeLp
  refine Lp.ext ?_
  refine (ContinuousMap.coeFn_toLp _ _).trans ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_modeLp L n).symm
  refine Filter.Eventually.of_forall fun p => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
  rw [liftC_coe, mode_coe]
  have hexp : (2 * Real.pi * Complex.I * n * x / L : ℂ) = (Complex.I * (QuantumNLS.Fourier.freq L n : ℂ)) * (x : ℂ) := by
    simp only [QuantumNLS.Fourier.freq]; push_cast; ring
  rw [hexp]
  rfl

/-- **Density of smooth test functions**: `L²` classes with the same real inner products against all smooth periodic functions coincide. -/
theorem eq_of_re_inner {a b : L2T L}
    (H : ∀ (h : ℝ → ℂ) (hh : SmoothPeriodic L h), (inner ℂ a (smoothL2 hh)).re = (inner ℂ b (smoothL2 hh)).re) :
    a = b := by
  have hd : ∀ (h : ℝ → ℂ) (hh : SmoothPeriodic L h), (inner ℂ (a - b) (smoothL2 hh)).re = 0 := by
    intro h hh
    rw [inner_sub_left, Complex.sub_re, H h hh, sub_self]
  have hn : ∀ n : ℤ, inner ℂ (a - b) (modeLp L n) = 0 := by
    intro n
    have h1 := hd _ (smoothPeriodic_cfun (L := L) n)
    rw [smoothL2_cfun] at h1
    have h2 := hd _ (smooth_const_mul (smoothPeriodic_cfun (L := L) n) Complex.I)
    rw [smoothL2_const_mul (smoothPeriodic_cfun (L := L) n) Complex.I, smoothL2_cfun, inner_smul_right] at h2
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h2
    apply Complex.ext
    · simpa using h1
    · simpa using h2
  have hc : ∀ n : ℤ, fourierL2 L (a - b) n = 0 := by
    intro n
    have h1 : inner ℂ (modeLp L n) (a - b) = (fourierL2 L (a - b)) n := by
      have := (fourierL2 L).inner_map_map (modeLp L n) (a - b)
      rw [← this, fourierL2_modeLp, lp.inner_single_left]
      simp
    rw [← h1, ← inner_conj_symm, hn n]
    simp
  have : a - b = 0 := by
    apply (fourierL2 L).injective
    ext n
    simpa using hc n
  exact sub_eq_zero.1 this

/-! ## `dI` along smooth directions through the REG-015 chart -/

variable {hκ : 0 < κ}

theorem memHs_two_S (r : ℕ) : (0 : ℝ) ≤ 2 * ((SOf r : ℝ≥0) : ℝ) := by positivity

/-- The coordinates `Φ(f) ∈ h^{2 S_r}` of a smooth periodic profile. -/
def zeta0 (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {f : ℝ → ℂ}
    (hf : SmoothPeriodic L f) : h02 L (2 * ((SOf r : ℝ≥0) : ℝ)) :=
  h02.ofMem (hinf_smooth hR C hf _ (memHs_two_S r))

/-- The `ℓ²` coordinate gradient of `F_r` at `Φ(f)`. -/
def Gcoord (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {f : ℝ → ℂ}
    (hf : SmoothPeriodic L f) : lp (fun _ : ℤ => ℂ) 2 :=
  Gl (cmp_def002 (L := L) (NNReal.coe_nonneg (SOf r))) (Fd_contDiff hR C r) (Fd_inv hR C r) (zeta0 hR C r hf)

theorem emb_val' {S T : ℝ≥0} (hT : T ≤ S) (w : (fieldScale L).Y S) :
    ((fieldScale L).emb S T hT w).val = w.val := rfl

/-- **A8 along smooth directions.** -/
theorem dir_deriv (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {f : ℝ → ℂ}
    (hf : SmoothPeriodic L f) :
    ∃ v : L2T L, fderiv ℝ C.Φ (smoothL2 hf) v = -Complex.I • Gcoord hR C r hf ∧
      ∀ (h : ℝ → ℂ) (hh : SmoothPeriodic L h),
        HasDerivAt (fun ε : ℝ => HierarchyFlow.hamiltonian L κ r (fun x => f x + (ε : ℂ) * h x))
          (2 * (inner ℂ (Complex.I • v) (smoothL2 hh)).re) 0 := by
  have hS0 : (0 : ℝ) ≤ ((SOf r : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  set u : L2T L := smoothL2 hf with hu
  classical
  let I' : L2T L → ℝ := fun x =>
    if hm : MemHsLp L ((qOf r : ℝ≥0) : ℝ) x then IOf hR C r ⟨x, hm⟩ else 0
  obtain ⟨v, hv, hder⟩ := dI_RF535 hκ C hS0 (Fd_contDiff hR C r) (Fd_inv hR C r) I' u (zeta0 hR C r hf)
    (fun n => rfl)
  refine ⟨v, hv, fun h hh => ?_⟩
  have key : ∀ (ε : ℝ) (x : L2T L), (ε : ℂ) • x = ε • x := fun ε x =>
    (RCLike.real_smul_eq_coe_smul (K := ℂ) ε x).symm
  obtain ⟨F2, hF2⟩ := regHomeo hR C (2 * ((SOf r : ℝ≥0) : ℝ)) (memHs_two_S r)
  let vu : H02 L (2 * ((SOf r : ℝ≥0) : ℝ)) := WField.mk u (memHs_of_smooth hf _)
  let vh : H02 L (2 * ((SOf r : ℝ≥0) : ℝ)) := WField.mk (smoothL2 hh) (memHs_of_smooth hh _)
  let ζ : ℝ → h02 L (2 * ((SOf r : ℝ≥0) : ℝ)) := fun ε => (F2 (vu + (ε : ℂ) • vh)).val
  have hζc : Continuous ζ := curve_continuous (memHs_two_S r) _ (chartHomeo C) F2 vu vh
  have hcoord : ∀ (ε : ℝ) (n : ℤ), (ζ ε).val n = C.Φ (u + ε • smoothL2 hh) n := by
    intro ε n
    show (F2 (vu + (ε : ℂ) • vh)).val.val n = _
    rw [hF2]
    show C.Φ (u + (ε : ℂ) • smoothL2 hh) n = _
    rw [key ε]
  have hI : ∀ ε : ℝ, I' (u + ε • smoothL2 hh) =
      Fd hR C r (iWU (cmp_def002 (L := L) hS0) (ζ ε)) := by
    intro ε
    have hs := smooth_add_smul hf hh (ε : ℂ)
    have hsl := smoothL2_add_smul hf hh (ε : ℂ) hs
    rw [key ε] at hsl
    have hm : MemHsLp L ((qOf r : ℝ≥0) : ℝ) (u + ε • smoothL2 hh) := by
      rw [← hsl]; exact memHs_of_smooth hs _
    have hw : (gOf hR C (SOf r) (iWU (cmp_def002 (L := L) hS0) (ζ ε))).val = u + ε • smoothL2 hh := by
      rw [gOf_val]
      have : toBase (L := L) ((SOf r : ℝ≥0) : ℝ) (SOf r).2 (iWU (cmp_def002 (L := L) hS0) (ζ ε)) =
          C.Φ (u + ε • smoothL2 hh) := by
        refine lp.ext (funext fun n => ?_)
        exact (toBase_apply (L := L) _ _ _ n).trans (hcoord ε n)
      rw [this, C.ΨΦ]
    simp only [I', dif_pos hm, Fd]
    congr 1
    apply WField.ext
    exact hw.symm
  have h1 := hder (smoothL2 hh) ζ hζc hcoord hI
  convert h1 using 1
  funext ε
  have hs := smooth_add_smul hf hh (ε : ℂ)
  have hsl := smoothL2_add_smul hf hh (ε : ℂ) hs
  rw [key ε] at hsl
  have hm : MemHsLp L ((qOf r : ℝ≥0) : ℝ) (u + ε • smoothL2 hh) := by
    rw [← hsl]; exact memHs_of_smooth hs _
  simp only [I', dif_pos hm]
  have := IOf_char hR C r _ hs (by rw [hsl]; exact hm)
  simp only [HierarchyFlow.hamiltonian]
  rw [← this]
  congr 1
  apply WField.ext
  show smoothL2 hs = u + ε • smoothL2 hh
  rw [hsl]

/-- A DEF-015 smooth gradient `g` of `HierarchyFlow.hamiltonian L κ r` at `f` is `i v`. -/
theorem grad_eq_of_isSmoothGradient (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {f : ℝ → ℂ} (hf : SmoothPeriodic L f) {v : L2T L}
    (hv : ∀ (h : ℝ → ℂ) (hh : SmoothPeriodic L h),
        HasDerivAt (fun ε : ℝ => HierarchyFlow.hamiltonian L κ r (fun x => f x + (ε : ℂ) * h x))
          (2 * (inner ℂ (Complex.I • v) (smoothL2 hh)).re) 0)
    {g : ℝ → ℂ} (hg : HierarchyFlow.IsSmoothGradient L (HierarchyFlow.hamiltonian L κ r) f g) :
    smoothL2 hg.1 = Complex.I • v := by
  refine eq_of_re_inner (fun h hh => ?_)
  have h1 := hg.2 h hh
  have h2 := hv h hh
  have h3 := h1.unique h2
  rw [inner_smoothL2 hg.1 hh]
  linarith

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.inner_smoothL2
#print axioms QuantumNLS.RB7.eq_of_re_inner
#print axioms QuantumNLS.RB7.dir_deriv
#print axioms QuantumNLS.RB7.grad_eq_of_isSmoothGradient
