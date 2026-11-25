import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.L1SpatialTransfer

/-! LOCAL-020 stage S2/S3 (part 1): unit diagonal multipliers on `H2 L = L²(0,L;ℂ²)`.

For continuous `α, β : ℝ → ℂ` of modulus one, `dmat α β x = diag(α x, β x)` and `mulU` the multiplication
`f ↦ (x ↦ diag(α x, β x) f x)` as a linear isometric equivalence of `H2 L`.  `isH1Rep_mul`: if `f` has the `H¹`
representative `(g, h)` and `α, β` are `C¹`, then `mulU f` has the `H¹` representative
`(diag g, diag h + diag' g)` (product rule for absolutely continuous functions). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Topology QuantumNLS.LocalSpectral
open scoped ENNReal

namespace QuantumNLS.Local020Mul1

variable {L : ℝ}

/-- Coordinate projection `v ↦ v_i e_i`. -/
def Pc (i : Fin 2) : E2 →L[ℂ] E2 :=
  (EuclideanSpace.proj i : E2 →L[ℂ] ℂ).smulRight (EuclideanSpace.single i (1 : ℂ))

theorem Pc_apply (i : Fin 2) (v : E2) : Pc i v = v i • EuclideanSpace.single i (1 : ℂ) := rfl

/-- `diag(α x, β x)` acting on `ℂ²`. -/
def dmat (α β : ℝ → ℂ) (x : ℝ) (v : E2) : E2 := α x • Pc 0 v + β x • Pc 1 v

theorem dmat_eq (α β : ℝ → ℂ) (x : ℝ) (v : E2) : dmat α β x v = vec2 (α x * v 0) (β x * v 1) := by
  ext i
  fin_cases i <;> simp [dmat, Pc_apply, vec2, EuclideanSpace.single_apply]

theorem dmat_add (α β : ℝ → ℂ) (x : ℝ) (v w : E2) :
    dmat α β x (v + w) = dmat α β x v + dmat α β x w := by
  simp only [dmat, map_add, smul_add]; abel

theorem dmat_smul (α β : ℝ → ℂ) (x : ℝ) (c : ℂ) (v : E2) :
    dmat α β x (c • v) = c • dmat α β x v := by
  simp only [dmat, map_smul]
  rw [smul_add, smul_comm (α x) c, smul_comm (β x) c]

theorem norm_dmat {α β : ℝ → ℂ} {x : ℝ} (ha : ‖α x‖ = 1) (hb : ‖β x‖ = 1) (v : E2) :
    ‖dmat α β x v‖ = ‖v‖ := by
  rw [dmat_eq]
  have h1 : ‖vec2 (α x * v 0) (β x * v 1)‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, vec2, ha, hb]
  have := sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.1 h1
  exact this

theorem dmat_dmat {α β α₂ β₂ : ℝ → ℂ} {x : ℝ} (h1 : α₂ x * α x = 1) (h2 : β₂ x * β x = 1) (v : E2) :
    dmat α₂ β₂ x (dmat α β x v) = v := by
  rw [dmat_eq, dmat_eq]
  ext i
  fin_cases i
  · simp [vec2]; rw [← mul_assoc, h1, one_mul]
  · simp [vec2]; rw [← mul_assoc, h2, one_mul]

theorem continuous_dmat {α β : ℝ → ℂ} (ha : Continuous α) (hb : Continuous β) :
    Continuous (fun p : ℝ × E2 => dmat α β p.1 p.2) := by
  unfold dmat
  have h0 : Continuous fun p : ℝ × E2 => Pc 0 p.2 := (Pc 0).continuous.comp continuous_snd
  have h1 : Continuous fun p : ℝ × E2 => Pc 1 p.2 := (Pc 1).continuous.comp continuous_snd
  exact ((ha.comp continuous_fst).smul h0).add ((hb.comp continuous_fst).smul h1)

/-- Unit diagonal multipliers. -/
structure UnitDiag (α β : ℝ → ℂ) : Prop where
  ca : Continuous α
  cb : Continuous β
  na : ∀ x, ‖α x‖ = 1
  nb : ∀ x, ‖β x‖ = 1

theorem UnitDiag.inv {α β : ℝ → ℂ} (h : UnitDiag α β) :
    UnitDiag (fun x => starRingEnd ℂ (α x)) (fun x => starRingEnd ℂ (β x)) :=
  ⟨Complex.continuous_conj.comp h.ca, Complex.continuous_conj.comp h.cb,
    fun x => by simp [h.na x], fun x => by simp [h.nb x]⟩

theorem UnitDiag.conj_mul {α : ℝ → ℂ} {x : ℝ} (h : ‖α x‖ = 1) : starRingEnd ℂ (α x) * α x = 1 := by
  rw [Complex.conj_mul', h]; simp

variable {α β : ℝ → ℂ}

theorem memLp_mulFun (h : UnitDiag α β) (f : H2 L) :
    MemLp (fun x => dmat α β x ((f : ℝ → E2) x)) 2 (μI L) := by
  have h2 : AEStronglyMeasurable (fun x : ℝ => (x, (f : ℝ → E2) x)) (μI L) :=
    aestronglyMeasurable_id.prodMk (Lp.aestronglyMeasurable f)
  have hm : AEStronglyMeasurable (fun x => dmat α β x ((f : ℝ → E2) x)) (μI L) := by
    have := (continuous_dmat h.ca h.cb).comp_aestronglyMeasurable h2
    exact this
  have hg : MemLp (f : ℝ → E2) 2 (μI L) := Lp.memLp f
  have hle : ∀ᵐ x ∂(μI L), ‖dmat α β x ((f : ℝ → E2) x)‖ ≤ ‖(f : ℝ → E2) x‖ :=
    Eventually.of_forall (fun x => (norm_dmat (h.na x) (h.nb x) _).le)
  first
    | exact MemLp.mono hg hm hle
    | exact MemLp.of_le hg hm hle
    | exact MemLp.mono' hg hm hle

/-- The multiplication isometry. -/
def mulLI (h : UnitDiag α β) : H2 L →ₗᵢ[ℂ] H2 L where
  toFun f := (memLp_mulFun h f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_mulFun h (f + g)).coeFn_toLp, (memLp_mulFun h f).coeFn_toLp,
      (memLp_mulFun h g).coeFn_toLp, Lp.coeFn_add (memLp_mulFun h f).toLp (memLp_mulFun h g).toLp,
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1, h4, h2, h3, h5, dmat_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_mulFun h (c • f)).coeFn_toLp, (memLp_mulFun h f).coeFn_toLp,
      Lp.coeFn_smul c (memLp_mulFun h f).toLp, Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [Pi.smul_apply, RingHom.id_apply] at h3 h4 ⊢
    rw [h1, h3, h2, h4, dmat_smul]
  norm_map' f := by
    have hae : ∀ᵐ x ∂(μI L), ‖((memLp_mulFun h f).toLp _ : H2 L) x‖ = ‖(f : ℝ → E2) x‖ := by
      filter_upwards [(memLp_mulFun h f).coeFn_toLp] with x hx
      rw [hx, norm_dmat (h.na x) (h.nb x)]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (hae.mono fun _ hx => hx.le))
      (Lp.norm_le_norm_of_ae_le (hae.mono fun _ hx => hx.ge))

theorem mulLI_ae (h : UnitDiag α β) (f : H2 L) :
    (mulLI h f : ℝ → E2) =ᵐ[μI L] fun x => dmat α β x ((f : ℝ → E2) x) :=
  (memLp_mulFun h f).coeFn_toLp

theorem mulLI_inv (h : UnitDiag α β) (f : H2 L) :
    mulLI h.inv (mulLI h f) = f := by
  apply Lp.ext
  filter_upwards [mulLI_ae h.inv (mulLI h f), mulLI_ae h f] with x h1 h2
  rw [h1, h2, dmat_dmat (UnitDiag.conj_mul (h.na x)) (UnitDiag.conj_mul (h.nb x))]

/-- The multiplier as a linear isometric equivalence. -/
def mulU (h : UnitDiag α β) : H2 L ≃ₗᵢ[ℂ] H2 L :=
  LinearIsometryEquiv.ofSurjective (mulLI h) (fun g => by
    refine ⟨mulLI h.inv g, ?_⟩
    have := mulLI_inv h.inv g
    simpa [UnitDiag.inv, Complex.conj_conj] using congrArg id this)

theorem mulU_ae (h : UnitDiag α β) (f : H2 L) :
    (mulU h f : ℝ → E2) =ᵐ[μI L] fun x => dmat α β x ((f : ℝ → E2) x) :=
  mulLI_ae h f

theorem norm_Pc_le (i : Fin 2) (v : E2) : ‖Pc i v‖ ≤ ‖v‖ := by
  rw [Pc_apply, norm_smul, PiLp.norm_single, norm_one, mul_one]
  exact PiLp.norm_apply_le v i

/-- FTC for absolutely continuous Banach-valued functions (as `RootH1RatioAC.ac_integral_eq`). -/
theorem ac_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hL : 0 ≤ L) {f d : ℝ → E} (hf : AbsolutelyContinuousOnInterval f 0 L)
    (hd : IntervalIntegrable d volume 0 L)
    (hder : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt f (d t) t)
    {x : ℝ} (hx : x ∈ Icc 0 L) : f x = f 0 + ∫ t in (0:ℝ)..x, d t := by
  let F : ℝ → E := fun t => f t - ∫ s in (0:ℝ)..t, d s
  have hac : AbsolutelyContinuousOnInterval F 0 L :=
    hf.sub (QuantumNLS.L1SpatialTransfer.ac_integral hd)
  have hz : ∀ᵐ t, t ∈ uIcc (0:ℝ) L → HasDerivAt F 0 t := by
    have hder' := (ae_restrict_iff' measurableSet_Icc).mp hder
    filter_upwards [hder', hd.ae_hasDerivAt_integral] with t ht hi htL
    have htI : t ∈ Icc (0:ℝ) L := by simpa [uIcc_of_le hL] using htL
    simpa only [F, sub_self] using! (ht htI).sub (hi htL 0 (by simp))
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero hz
  have he0 := hC 0 (by simp)
  have hex := hC x (by simpa [uIcc_of_le hL] using hx)
  simp only [F, intervalIntegral.integral_same, sub_zero] at he0
  dsimp [F] at hex
  rw [← he0] at hex
  exact sub_eq_iff_eq_add.mp hex

section H1

variable {f : H2 L} {g h : ℝ → E2}

theorem rep_intervalIntegrable (hL : 0 ≤ L) (hrep : IsH1Rep L f g h) :
    IntervalIntegrable h volume 0 L :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).2
    (hrep.2.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))

theorem rep_ac (hL : 0 ≤ L) (hrep : IsH1Rep L f g h) : AbsolutelyContinuousOnInterval g 0 L := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => g 0) 0 L :=
    (LipschitzWith.const (g 0)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (hc.add (QuantumNLS.L1SpatialTransfer.ac_integral (rep_intervalIntegrable hL hrep))).congr
    (fun t ht => (hrep.2.2 t (by simpa [uIcc_of_le hL] using ht)).symm)

theorem rep_ae_deriv (hL : 0 ≤ L) (hrep : IsH1Rep L f g h) :
    ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt g (h t) t := by
  have hi := rep_intervalIntegrable hL hrep
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  have hn0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff]
  have hnL : ∀ᵐ t : ℝ, t ≠ L := by simp [ae_iff]
  filter_upwards [hi.ae_hasDerivAt_integral, hn0, hnL] with t hd ht0 htL ht
  have hti : t ∈ Ioo (0:ℝ) L := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htL⟩
  have hd' := (hd (by simpa [uIcc_of_le hL] using ht) 0 (by simp)).const_add (g 0)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
  exact hrep.2.2 s ⟨hs.1.le, hs.2.le⟩

theorem rep_bound (hL : 0 ≤ L) (hrep : IsH1Rep L f g h) : ∃ M : ℝ, ∀ x ∈ Icc 0 L, ‖g x‖ ≤ M := by
  have hint : IntegrableOn h (Ioc 0 L) volume := hrep.2.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨‖g 0‖ + ∫ s in Ioc 0 L, ‖h s‖, fun x hx => ?_⟩
  rw [hrep.2.2 x hx]
  refine (norm_add_le _ _).trans ?_
  gcongr
  rw [intervalIntegral.integral_of_le hx.1]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_set hint.norm ?_ ?_
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact (Ioc_subset_Ioc_right hx.2).eventuallyLE

theorem aesm_rep (hrep : IsH1Rep L f g h) : AEStronglyMeasurable g (μI L) :=
  (Lp.aestronglyMeasurable f).congr hrep.1

end H1

section H1Mul

variable {f : H2 L} {g h : ℝ → E2} {α' β' : ℝ → ℂ}

theorem memLp_dmat_rep (hu : UnitDiag α β) (hh : MemLp h 2 (μI L)) :
    MemLp (fun x => dmat α β x (h x)) 2 (μI L) := by
  have h2 : AEStronglyMeasurable (fun x : ℝ => (x, h x)) (μI L) :=
    aestronglyMeasurable_id.prodMk hh.aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun x => dmat α β x (h x)) (μI L) := by
    have := (continuous_dmat hu.ca hu.cb).comp_aestronglyMeasurable h2
    exact this
  have hle : ∀ᵐ x ∂(μI L), ‖dmat α β x (h x)‖ ≤ ‖h x‖ :=
    Eventually.of_forall (fun x => (norm_dmat (hu.na x) (hu.nb x) _).le)
  exact MemLp.mono hh hm hle

theorem memLp_dmat_deriv (hL : 0 < L) (hrep : IsH1Rep L f g h) (hα' : Continuous α')
    (hβ' : Continuous β') : MemLp (fun x => dmat α' β' x (g x)) 2 (μI L) := by
  obtain ⟨M, hM⟩ := rep_bound hL.le hrep
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn (hα'.continuousOn (s := Icc 0 L))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hβ'.continuousOn (s := Icc 0 L))
  have h2 : AEStronglyMeasurable (fun x : ℝ => (x, g x)) (μI L) :=
    aestronglyMeasurable_id.prodMk (aesm_rep hrep)
  have hm : AEStronglyMeasurable (fun x => dmat α' β' x (g x)) (μI L) := by
    have := (continuous_dmat hα' hβ').comp_aestronglyMeasurable h2
    exact this
  refine MemLp.of_bound hm (A * M + B * M) ?_
  have hmem : ∀ᵐ x ∂(μI L), x ∈ Ioc 0 L := by unfold μI; exact ae_restrict_mem measurableSet_Ioc
  filter_upwards [hmem] with x hx
  have hx' : x ∈ Icc 0 L := ⟨hx.1.le, hx.2⟩
  unfold dmat
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have h0 := norm_Pc_le 0 (g x)
  have h1 := norm_Pc_le 1 (g x)
  have hg := hM x hx'
  have hA' := hA x hx'
  have hB' := hB x hx'
  have : 0 ≤ ‖g x‖ := norm_nonneg _
  exact add_le_add (mul_le_mul hA' (h0.trans hg) (norm_nonneg _) ((norm_nonneg _).trans hA'))
    (mul_le_mul hB' (h1.trans hg) (norm_nonneg _) ((norm_nonneg _).trans hB'))

theorem contDiff_of_hasDerivAt {a a' : ℝ → ℂ} (ha : ∀ x, HasDerivAt a (a' x) x) (ha' : Continuous a') :
    ContDiff ℝ 1 a := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (ha x).differentiableAt, ?_⟩
  have : deriv a = a' := funext fun x => (ha x).deriv
  rw [this]; exact ha'

theorem hasDerivAt_dmat {t : ℝ} (hα : HasDerivAt α (α' t) t) (hβ : HasDerivAt β (β' t) t)
    (hg : HasDerivAt g (h t) t) :
    HasDerivAt (fun x => dmat α β x (g x)) (dmat α β t (h t) + dmat α' β' t (g t)) t := by
  have h0 := hα.smul (((Pc 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hg)
  have h1 := hβ.smul (((Pc 1).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hg)
  refine (h0.add h1).congr_deriv ?_
  simp only [dmat, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  abel

/-- **The multiplier preserves `H¹` representatives** (product rule). -/
theorem isH1Rep_mul (hL : 0 < L) (hrep : IsH1Rep L f g h) (hu : UnitDiag α β)
    (hα : ∀ x, HasDerivAt α (α' x) x) (hβ : ∀ x, HasDerivAt β (β' x) x)
    (hα' : Continuous α') (hβ' : Continuous β') :
    IsH1Rep L (mulU hu f) (fun x => dmat α β x (g x))
      (fun x => dmat α β x (h x) + dmat α' β' x (g x)) := by
  have hmem : MemLp (fun x => dmat α β x (h x) + dmat α' β' x (g x)) 2 (μI L) :=
    (memLp_dmat_rep hu hrep.2.1).add (memLp_dmat_deriv hL hrep hα' hβ')
  refine ⟨?_, hmem, ?_⟩
  · filter_upwards [mulU_ae hu f, hrep.1] with x h1 h2
    rw [h1, h2]
  · have hd : IntervalIntegrable (fun x => dmat α β x (h x) + dmat α' β' x (g x)) volume 0 L :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).2
        (hmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    have gac := rep_ac hL.le hrep
    have gi : ∀ i, AbsolutelyContinuousOnInterval (fun x => Pc i (g x)) 0 L := fun i =>
      (Pc i).lipschitz.comp_absolutelyContinuousOnInterval gac
    have αac : AbsolutelyContinuousOnInterval α 0 L :=
      (contDiff_of_hasDerivAt hα hα').contDiffOn.absolutelyContinuousOnInterval
    have βac : AbsolutelyContinuousOnInterval β 0 L :=
      (contDiff_of_hasDerivAt hβ hβ').contDiffOn.absolutelyContinuousOnInterval
    have Fac : AbsolutelyContinuousOnInterval (fun x => dmat α β x (g x)) 0 L :=
      (αac.fun_smul (gi 0)).add (βac.fun_smul (gi 1))
    have hder : ∀ᵐ t ∂volume.restrict (Icc 0 L),
        HasDerivAt (fun x => dmat α β x (g x)) (dmat α β t (h t) + dmat α' β' t (g t)) t := by
      filter_upwards [rep_ae_deriv hL.le hrep] with t ht
      exact hasDerivAt_dmat (hα t) (hβ t) ht
    intro x hx
    exact ac_integral_eq hL.le Fac hd hder hx

end H1Mul

end QuantumNLS.Local020Mul1

#print axioms QuantumNLS.Local020Mul1.isH1Rep_mul
#print axioms QuantumNLS.Local020Mul1.mulU_ae
#print axioms QuantumNLS.Local020Mul1.ac_integral_eq
