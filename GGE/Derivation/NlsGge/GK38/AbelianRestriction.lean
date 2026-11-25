import NlsGge.GK38.AbelianSpace
import NlsGge.GK38.Lib.HilbertValuedAnalytic

/-! Genuine omitted-index restriction and the Hilbert analytic criterion.
UNCOMPILED prospective proof source. No bound for actual F is assumed proved. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- Genuine full-space summability is inherited by the actual omitted subtype. -/
def p2RestrictElement38 (n : ℤ) (s : Lib.L2Seq) : P2Space38 n := by
  refine ⟨fun m => s m.1, ?_⟩
  have hs : Summable (fun m : ℤ => ‖s m‖^2) := by
    simpa using (memℓp_gen_iff (by norm_num : 0<(2:ENNReal).toReal)).mp s.2
  apply (memℓp_gen_iff (by norm_num : 0<(2:ENNReal).toReal)).mpr
  have he : Summable (fun m : P2Index38 n => ‖s m.1‖^2) :=
    hs.comp_injective (i := fun m : P2Index38 n => m.1) Subtype.val_injective
  simpa using he

@[simp] theorem p2RestrictElement_apply38 (n : ℤ) (s : Lib.L2Seq) (m : P2Index38 n) :
    p2RestrictElement38 n s m=s m.1 := rfl

theorem p2RestrictElement_norm_le38 (n : ℤ) (s : Lib.L2Seq) :
    ‖p2RestrictElement38 n s‖ ≤ ‖s‖ := by
  have hs : Summable (fun m : ℤ => ‖s m‖^2) := by
    simpa using (memℓp_gen_iff (by norm_num : 0<(2:ENNReal).toReal)).mp s.2
  have hsum := Summable.tsum_subtype_le (fun m : ℤ => ‖s m‖^2)
    {m : ℤ | m ≠ n} (fun m => sq_nonneg ‖s m‖) hs
  have hR := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ENNReal).toReal)
    (p2RestrictElement38 n s)
  have hS := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ENNReal).toReal) s
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,p2RestrictElement_apply38] at hR hS
  have hle : ‖p2RestrictElement38 n s‖^2 ≤ ‖s‖^2 := by
    calc
      _ = _ := hR
      _ ≤ _ := hsum
      _ = _ := hS.symm
  nlinarith [norm_nonneg (p2RestrictElement38 n s),norm_nonneg s]

def p2RestrictLinear38 (n : ℤ) : Lib.L2Seq →ₗ[ℂ] P2Space38 n where
  toFun := p2RestrictElement38 n
  map_add' s t := by
    apply Subtype.ext
    funext m
    rfl
  map_smul' c s := by
    apply Subtype.ext
    funext m
    rfl

def p2Restrict38 (n : ℤ) : Lib.L2Seq →L[ℂ] P2Space38 n :=
  (p2RestrictLinear38 n).mkContinuous 1 (by
    intro s
    change ‖p2RestrictElement38 n s‖ ≤ 1*‖s‖
    simpa only [one_mul] using p2RestrictElement_norm_le38 n s)

@[simp] theorem p2Restrict_apply38 (n : ℤ) (s : Lib.L2Seq) (m : P2Index38 n) :
    p2Restrict38 n s m=s m.1 := rfl

@[simp] theorem p2Restrict_extend38 (n : ℤ) (s : P2Space38 n) :
    p2Restrict38 n (p2Extend38 n s)=s := by
  apply Subtype.ext
  funext m
  exact p2Extend_at38 n s m

/-- The accepted integer-index criterion is transported to the genuine omitted space.
This is a generic criterion ONLY. Actual P2 summability/local bounds remain to be earned. -/
theorem p2AnalyticOnNhd_of_coords_of_locBdd38
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (n : ℤ) (f : E → P2Space38 n) {U : Set E} (hU : IsOpen U)
    (hc : ∀ m : P2Index38 n, AnalyticOnNhd ℂ (fun x => f x m) U)
    (hb : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ ball x r, ‖f y‖ ≤ C) :
    AnalyticOnNhd ℂ f U := by
  have hcoords : ∀ m : ℤ,
      AnalyticOnNhd ℂ (fun x => p2Extend38 n (f x) m) U := by
    intro m
    by_cases hm : m=n
    · subst m
      simpa only [p2Extend_self38] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : E => (0:ℂ)) U)
    · have heq : (fun x : E => p2Extend38 n (f x) m)=(fun x : E => f x ⟨m,hm⟩) :=
        funext (fun x => p2Extend_at38 n (f x) ⟨m,hm⟩)
      rw [heq]
      exact hc ⟨m,hm⟩
  have hbound : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ,
      ∀ y ∈ ball x r, ‖p2Extend38 n (f y)‖ ≤ C := by
    simpa only [p2Extend_norm38] using hb
  have he := Lib.analyticOnNhd_of_coords_of_locBdd
    (fun x => p2Extend38 n (f x)) hU hcoords hbound
  intro x hx
  have hcomp := AnalyticAt.comp (g := p2Restrict38 n)
    (f := fun y : E => p2Extend38 n (f y))
    ((p2Restrict38 n).analyticAt (p2Extend38 n (f x))) (he x hx)
  simpa only [Function.comp_def,p2Restrict_extend38] using hcomp

#print axioms p2RestrictElement_norm_le38
#print axioms p2Restrict38
#print axioms p2AnalyticOnNhd_of_coords_of_locBdd38
end
end NlsGge.GK38
