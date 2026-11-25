import NlsGge.GK38.Lib.EntireProductsParam
import NlsGge.GK38.Lib.InterpolationHilbertOp

/-! Genuine omitted-index Hilbert space. UNCOMPILED prospective source checkpoint. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

abbrev P2Index38 (n : ℤ) : Type := {m : ℤ // m ≠ n}
abbrev P2Space38 (n : ℤ) : Type := lp (fun _ : P2Index38 n => ℂ) 2

def p2RealSeq38 (n : ℤ) (s : P2Space38 n) : Prop :=
  ∀ m : P2Index38 n, (s m).im = 0

def p2RawExtend38 (n : ℤ) (s : P2Space38 n) (m : ℤ) : ℂ :=
  if h : m = n then 0 else s ⟨m,h⟩

@[simp] theorem p2RawExtend_at38 (n : ℤ) (s : P2Space38 n) (m : P2Index38 n) :
    p2RawExtend38 n s m.1 = s m := by
  simp [p2RawExtend38,m.2]

@[simp] theorem p2RawExtend_self38 (n : ℤ) (s : P2Space38 n) : p2RawExtend38 n s n=0 := by
  simp [p2RawExtend38]

/-- Summability is proved before the extension is bundled into lp. -/
theorem p2RawExtend_summable38 (n : ℤ) (s : P2Space38 n) :
    Summable (fun m : ℤ => ‖p2RawExtend38 n s m‖^2) := by
  have hs : Summable (fun m : P2Index38 n => ‖s m‖^2) := by
    simpa using (memℓp_gen_iff (by norm_num : 0<(2:ENNReal).toReal)).mp s.2
  have hs' : Summable (fun m : P2Index38 n => ‖p2RawExtend38 n s m.1‖^2) := by
    simpa only [p2RawExtend_at38] using hs
  have hi := (summable_subtype_iff_indicator (f := fun m : ℤ => ‖p2RawExtend38 n s m‖^2)
    (s := {m : ℤ | m ≠ n})).mp hs'
  have he : Set.indicator {m : ℤ | m ≠ n} (fun m => ‖p2RawExtend38 n s m‖^2) =
      (fun m : ℤ => ‖p2RawExtend38 n s m‖^2) := by
    funext m
    by_cases hm : m=n
    · subst m
      rw [Set.indicator_of_notMem (by simp : n ∉ {m : ℤ | m ≠ n})]
      simp only [p2RawExtend_self38,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    · exact Set.indicator_of_mem hm _
  rwa [he] at hi

def p2ExtendElement38 (n : ℤ) (s : P2Space38 n) : Lib.L2Seq :=
  ⟨p2RawExtend38 n s,(memℓp_gen_iff (by norm_num : 0<(2:ENNReal).toReal)).mpr
    (by simpa using p2RawExtend_summable38 n s)⟩

@[simp] theorem p2ExtendElement_apply38 (n : ℤ) (s : P2Space38 n) (m : ℤ) :
    p2ExtendElement38 n s m=p2RawExtend38 n s m := rfl

theorem p2ExtendElement_norm38 (n : ℤ) (s : P2Space38 n) : ‖p2ExtendElement38 n s‖=‖s‖ := by
  have hsupport : Function.support (fun m : ℤ => ‖p2RawExtend38 n s m‖^2) ⊆ {m : ℤ | m ≠ n} := by
    intro m hm he
    subst m
    exact hm (by simp only [p2RawExtend_self38,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)])
  have hsum := tsum_subtype_eq_of_support_subset hsupport
  have hE := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ENNReal).toReal) (p2ExtendElement38 n s)
  have hS := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ENNReal).toReal) s
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,p2ExtendElement_apply38] at hE hS
  simp only [p2RawExtend_at38] at hsum
  have heq : ‖p2ExtendElement38 n s‖^2=‖s‖^2 :=
    hE.trans (hsum.symm.trans hS.symm)
  nlinarith [norm_nonneg (p2ExtendElement38 n s),norm_nonneg s]

/-- The map is an actual linear isometry for the genuine omitted index topology. -/
def p2ExtendIsometry38 (n : ℤ) : P2Space38 n →ₗᵢ[ℂ] Lib.L2Seq where
  toFun := p2ExtendElement38 n
  map_add' s t := by
    apply Subtype.ext
    funext m
    change p2RawExtend38 n (s+t) m=p2RawExtend38 n s m+p2RawExtend38 n t m
    by_cases hm : m=n
    · subst m
      simp [p2RawExtend38]
    · simp [p2RawExtend38,hm]
  map_smul' c s := by
    apply Subtype.ext
    funext m
    by_cases hm : m=n
    · subst m
      simp [p2ExtendElement38,p2RawExtend38,lp.coeFn_smul]
    · simp [p2ExtendElement38,p2RawExtend38,hm,lp.coeFn_smul]
  norm_map' := p2ExtendElement_norm38 n

def p2Extend38 (n : ℤ) : P2Space38 n →L[ℂ] Lib.L2Seq :=
  (p2ExtendIsometry38 n).toContinuousLinearMap

@[simp] theorem p2Extend_at38 (n : ℤ) (s : P2Space38 n) (m : P2Index38 n) :
    p2Extend38 n s m.1=s m := p2RawExtend_at38 n s m

@[simp] theorem p2Extend_self38 (n : ℤ) (s : P2Space38 n) : p2Extend38 n s n=0 :=
  p2RawExtend_self38 n s

theorem p2Extend_norm38 (n : ℤ) (s : P2Space38 n) : ‖p2Extend38 n s‖=‖s‖ :=
  p2ExtendElement_norm38 n s

#print axioms p2RawExtend_summable38
#print axioms p2ExtendElement_norm38
#print axioms p2Extend38
end
end NlsGge.GK38
