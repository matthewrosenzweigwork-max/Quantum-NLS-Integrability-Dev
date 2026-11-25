import Mathlib
import QuantumNLS.RB7Reg
import QuantumNLS.RB7Dir
import QuantumNLS.RB7Slice
import QuantumNLS.RB7Zf
import QuantumNLS.RB7HFlow

/-!
# R-7B122087 `thm:hierarchy`: existence of the function-level Hamiltonian flow of `Re I_{r+1}` (RB7Exist)

Printed: "`u(t) = (Z^new)^{-1} z(t)` is smooth in space and time.  Full Hilbert symplecticity, tested against smooth variations, identifies its derivative with `-i∇I_{r+1}(u(t))`."

* `z0 hR C u`: the `h^0` coordinates `Φ(f)` of a smooth periodic `f` (`RB7Reg.hinf_smooth`); `PsiC C`: the analytic inverse chart `h^0 → H^0`; `curveOf hR C r u τ = Ψ(Zf_r(τ)(z0 u))`.
* `hZsm_chart`, `hreg_chart`, `hchart_chart`: the hypotheses `hZsm`, `hreg`, `hchart` of haiku_inventory's `RB7H.isHamFlow_of_chart` for this chart data (A7b).
* `hgrad_chart` (own task 2): the `hgrad` hypothesis of `RB7H.isHamFlow_of_chart`: `IsSmoothGradient` (identification of the function-level `HierarchyFlow.pair` with the `L²` inner product,
  `g = i v`, `RB7Dir`) together with the pointwise time derivative `∂_s Φ_s u (x) = -i g(x)` (the `L²`-derivative of the joint smooth curve, `RB7Slice`, equals the chain-rule velocity
  `e⁻¹ ż` of `Ψ ∘ z`).
* `isHamFlow_chart`: `HierarchyFlow.IsHamFlow L (hamiltonian L κ r) (physFlow (curveOf hR C r))`, every `r`.
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
open QuantumNLS.Reg015Setting QuantumNLS.LossSobolev QuantumNLS.Loss QuantumNLS.ClassicalCharges
open QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.HierarchyFlow
open QuantumNLS.D01LocalPrimitive (K)

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

/-- Rapidly decreasing coordinates (all real `b`) of a smooth profile. -/
theorem hinf_all (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {f : ℝ → ℂ}
    (hf : SmoothPeriodic L f) : Hinf L (fun n => C.Φ (smoothL2 hf) n) := by
  intro b
  rcases le_or_gt 0 b with h | h
  · exact hinf_smooth hR C hf b h
  · exact RB7H.memHs_of_le h.le _ (hinf_smooth hR C hf 0 le_rfl)

open Classical in
/-- The `h^0` coordinates `Φ(f)` of a smooth periodic profile (`0` for a non-smooth one). -/
def z0 (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (u : ℝ → ℂ) : (seqScale L).Y 0 :=
  if hu : SmoothPeriodic L u then h02.ofMem (hinf_smooth hR C hu (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0)) else 0

theorem z0_val (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    (z0 hR C u).val = fun n => C.Φ (smoothL2 hu) n := by
  exact (congrArg (fun x : h02 L (((0 : ℝ≥0) : ℝ)) => x.val) (dif_pos hu : z0 hR C u = _)).trans rfl

/-- The analytic inverse chart `h^0 → H^0`. -/
def PsiC (C : ChartFacts (L := L) hκ) : (seqScale L).Y 0 → (fieldScale L).Y 0 :=
  fun z => toH0 (C.Ψ (toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) z))

theorem PsiC_val (C : ChartFacts (L := L) hκ) (z : (seqScale L).Y 0) :
    (PsiC C z).val = C.Ψ (toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) z) := rfl

theorem PsiC_analytic (C : ChartFacts (L := L) hκ) : AnalyticOnNhd ℝ (PsiC C) Set.univ := by
  intro z _
  have h1 : AnalyticAt ℝ (fun y : (seqScale L).Y 0 => toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) y) z :=
    ((toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0)).restrictScalars ℝ).analyticAt z
  exact ((toH0 (L := L)).analyticAt _).comp ((C.ana_Ψ _).comp h1)

theorem toBase_z0 (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) (z0 hR C u) = C.Φ (smoothL2 hu) :=
  lp.ext (funext fun n => (toBase_apply (L := L) _ (NNReal.coe_nonneg 0) (z0 hR C u) n).trans
    (congrFun (z0_val hR C hu) n))

/-- The physical curve map. -/
def curveOf (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) :
    (ℝ → ℂ) → ℝ → L2T L :=
  fun u τ => (PsiC C (Zf hR C r τ (z0 hR C u))).val

theorem hreg_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) :
    ∀ S : ℝ≥0, ∃ g : (seqScale L).Y S → (fieldScale L).Y S, Continuous g ∧
      ∀ x, (fieldScale L).emb S 0 (nn_zero_le S) (g x) = PsiC C ((seqScale L).emb S 0 (nn_zero_le S) x) := by
  intro S
  refine ⟨gOf hR C S, gOf_cont hR C S, fun x => ?_⟩
  apply WField.ext
  show (gOf hR C S x).val = C.Ψ (toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) (h02_mono L (NNReal.coe_nonneg S) x))
  refine (gOf_val hR C S x).trans ?_
  exact congrArg C.Ψ (lp.ext (funext fun n =>
    (toBase_apply (L := L) _ S.2 x n).trans
      (toBase_apply (L := L) _ (NNReal.coe_nonneg 0) (h02_mono L (NNReal.coe_nonneg S) x) n).symm))

theorem hchart_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) :
    ∀ (u : ℝ → ℂ) (hu : SmoothPeriodic L u), (PsiC C (z0 hR C u)).val = (smoothL2 hu : L2T L) := by
  intro u hu
  rw [PsiC_val, toBase_z0 hR C hu, C.ΨΦ]

/-- The sequence flow is smooth into every level `S`, with the correct values in `h^0`. -/
theorem hZsm_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) :
    ∀ (u : ℝ → ℂ), SmoothPeriodic L u → ∀ S : ℝ≥0, ∃ zS : ℝ → (seqScale L).Y S,
      ContDiff ℝ ∞ zS ∧ ∀ τ, (seqScale L).emb S 0 (nn_zero_le S) (zS τ) = Zf hR C r τ (z0 hR C u) := by
  intro u hu S
  set a : ℝ := max ((S : ℝ≥0) : ℝ) ((SOf r : ℝ≥0) : ℝ) with ha
  have haS : ((SOf r : ℝ≥0) : ℝ) ≤ a := le_max_right _ _
  have hSa : ((S : ℝ≥0) : ℝ) ≤ a := le_max_left _ _
  have ha0 : 0 ≤ a := le_trans (NNReal.coe_nonneg _) hSa
  let za : h02 L a := h02.ofMem (hinf_all hR C hu a)
  refine ⟨fun τ => h02_mono L hSa (zflow hR C r a haS τ za), ?_, fun τ => ?_⟩
  · have h1 := zflow_contDiff hR C r a haS za (hinf_all hR C hu)
    exact ((h02_mono L hSa).restrictScalars ℝ).contDiff.comp h1
  · apply WSeq.ext
    show (zflow hR C r a haS τ za).val = (Zf hR C r τ (z0 hR C u)).val
    rw [Zf_val hR C r τ (z0 hR C u) haS za (by rw [z0_val hR C hu]; rfl)]

/-- The `ℓ²`-curve `τ ↦ Φ(curveOf τ)` is the flow coordinate curve. -/
theorem toBase_curve (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) (τ : ℝ) :
    toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) (Zf hR C r τ (z0 hR C u)) =
      toBase (L := L) ((SOf r : ℝ≥0) : ℝ) (SOf r).2
        (zflow hR C r _ le_rfl τ (h02.ofMem (hinf_all hR C hu ((SOf r : ℝ≥0) : ℝ)))) := by
  refine lp.ext (funext fun n => ?_)
  have := Zf_val hR C r τ (z0 hR C u) (le_refl ((SOf r : ℝ≥0) : ℝ))
    (h02.ofMem (hinf_all hR C hu ((SOf r : ℝ≥0) : ℝ))) (by rw [z0_val hR C hu]; rfl)
  exact ((toBase_apply (L := L) _ (NNReal.coe_nonneg 0) _ n).trans (congrFun this n)).trans
    (toBase_apply (L := L) _ (SOf r).2 _ n).symm

theorem Phi_curve (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) (u : ℝ → ℂ) (τ : ℝ) :
    C.Φ (curveOf hR C r u τ) =
      toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) (Zf hR C r τ (z0 hR C u)) := by
  show C.Φ (C.Ψ _) = _
  rw [C.ΦΨ]

theorem hlift_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) :
    ∀ q : ℝ, 0 < q → ∃ V : ℝ → H02 L q, ContDiff ℝ ∞ V ∧ ∀ τ, (V τ).val = curveOf hR C r u τ :=
  fun q hq => RB7H.curve_lift (PsiC C) (PsiC_analytic C) (fun τ => Zf hR C r τ (z0 hR C u))
    (hZsm_chart hR C r u hu) (hreg_chart hR C) q hq

/-- Each time slice of the function-level flow is smooth periodic with `L²` class `Ψ(Zf_r(s) Φ u)`. -/
theorem physFlow_slice (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) (s : ℝ) :
    ∃ hf : SmoothPeriodic L (RB7H.physFlow (curveOf hR C r) s u),
      smoothL2 hf = curveOf hR C r u s :=
  (RB7H.joint_smooth (curveOf hR C r u) (hlift_chart hR C r hu)).2.2 s

/-- **`hgrad`** (task 2): `IsSmoothGradient` and the time derivative for the chart flow. -/
theorem hgrad_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) :
    ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s : ℝ, ∃ g : ℝ → ℂ,
      IsSmoothGradient L (hamiltonian L κ r) (RB7H.physFlow (curveOf hR C r) s u) g ∧
        ∀ x : ℝ, HasDerivAt (fun s' => RB7H.physFlow (curveOf hR C r) s' u x) (-Complex.I * g x) s := by
  intro u hu s
  obtain ⟨hG, -, hsl⟩ := RB7H.joint_smooth (curveOf hR C r u) (hlift_chart hR C r hu)
  set G := RB7H.Gfun (curveOf hR C r u) with hGdef
  have hper : ∀ τ x, G (τ, x + L) = G (τ, x) := fun τ x => RB7H.Gfun_periodic _ τ x
  have hc : ∀ τ, smoothL2 (slice_smooth hG hper τ) = curveOf hR C r u τ := fun τ => (hsl τ).choose_spec
  have h1 : HasDerivAt (fun τ => curveOf hR C r u τ) (smoothL2 (dslice_smooth hG hper s)) s := by
    have := hasDerivAt_slice hG hper s
    simp only [hc] at this
    exact this
  -- the coordinate curve
  set zS : h02 L ((SOf r : ℝ≥0) : ℝ) := h02.ofMem (hinf_all hR C hu ((SOf r : ℝ≥0) : ℝ)) with hzS
  obtain ⟨d, hd, hdval⟩ := zflow_hasDerivAt hR C r zS (hinf_all hR C hu) s
  have hζ : HasDerivAt (fun τ => toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0)
      (Zf hR C r τ (z0 hR C u))) d s := by
    have e : (fun τ => toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) (Zf hR C r τ (z0 hR C u))) =
        fun t : ℝ => toBase (L := L) ((SOf r : ℝ≥0) : ℝ) (SOf r).2 (zflow hR C r _ le_rfl t zS) :=
      funext fun τ => toBase_curve hR C r hu τ
    rw [e]; exact hd
  -- chain rule through the inverse chart
  set us := curveOf hR C r u s with hus
  obtain ⟨e, he, he'⟩ := C.iso us
  have hΦus : C.Φ us = toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) (Zf hR C r s (z0 hR C u)) :=
    Phi_curve hR C r u s
  rw [hΦus] at he'
  have h2 : HasDerivAt (fun τ => C.Ψ (toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0)
      (Zf hR C r τ (z0 hR C u)))) ((e.symm : K →L[ℝ] L2T L) d) s := he'.comp_hasDerivAt s hζ
  have hvel : smoothL2 (dslice_smooth hG hper s) = e.symm d := h1.unique h2
  -- the gradient
  have hfs := slice_smooth hG hper s
  have hsmooth_s : smoothL2 hfs = us := hc s
  obtain ⟨vd, hvd, hder⟩ := dir_deriv hR C r hfs
  have hD : fderiv ℝ C.Φ (smoothL2 hfs) = (e : L2T L →L[ℝ] K) := by rw [hsmooth_s]; exact he.fderiv
  rw [hD] at hvd
  have hdG : d = -Complex.I • Gcoord hR C r hfs := by
    refine lp.ext (funext fun j => ?_)
    rw [hdval j]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    show _ = Gs (Fd hR C r) (cmp_def002 (L := L) (NNReal.coe_nonneg (SOf r))) (zeta0 hR C r hfs) j
    unfold Gs
    congr 2
    apply WSeq.ext
    funext n
    have h5 : C.Φ us = toBase (L := L) ((SOf r : ℝ≥0) : ℝ) (SOf r).2 (zflow hR C r _ le_rfl s zS) :=
      hΦus.trans (toBase_curve hR C r hu s)
    have h6 := congrFun (congrArg (fun z : lp (fun _ : ℤ => ℂ) 2 => (z : ℤ → ℂ)) h5) n
    show (zflow hR C r _ le_rfl s zS).val n = C.Φ (smoothL2 hfs) n
    rw [hsmooth_s]
    exact (h6.trans (toBase_apply (L := L) _ _ _ n)).symm
  have hvd2 : vd = smoothL2 (dslice_smooth hG hper s) := by
    rw [hvel]
    have h7 : (e : L2T L →L[ℝ] K) vd = d := by rw [hvd, hdG]
    have h8 : e vd = d := h7
    rw [← h8]; exact (e.symm_apply_apply vd).symm
  refine ⟨fun x => Complex.I * dslice G s x, ⟨smooth_const_mul (dslice_smooth hG hper s) Complex.I, fun h hh => ?_⟩, fun x => ?_⟩
  · have := hder h hh
    have e1 : Complex.I • vd = smoothL2 (smooth_const_mul (dslice_smooth hG hper s) Complex.I) := by
      rw [smoothL2_const_mul (dslice_smooth hG hper s) Complex.I, hvd2]
    rw [e1, inner_smoothL2] at this
    exact this
  · have := hasDerivAt_partial (hG.of_le (by simp)) s x
    have e3 : -Complex.I * (Complex.I * dslice G s x) = dslice G s x := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    rw [e3]
    exact this

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.hreg_chart
#print axioms QuantumNLS.RB7.hchart_chart
#print axioms QuantumNLS.RB7.hZsm_chart
#print axioms QuantumNLS.RB7.physFlow_slice
#print axioms QuantumNLS.RB7.hgrad_chart
