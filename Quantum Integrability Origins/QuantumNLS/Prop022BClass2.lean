import Mathlib
import QuantumNLS.Prop022BClass1

/-! PROP-022 route A, finite-dimensional case, stage B3b: the printed classical conclusions 1-3 of
Q7B:lem:pair for an arbitrary complex Hilbert space `H` (finite-dimensional included) embedded
isometrically in `L2T L`, with independence of the embedding.

Every object is defined in `Prop022BClass1` by compression through `J`; here `aJ, bJ, alphaJ, betaJ` are
the complex-linear and antilinear parts of `hessJ (profJ t)` and of `SJ`, exactly as in the frozen
`Prop022GLinear`.  `PROP022_J_classical` reproduces the conclusions of
`Prop022GMain.PROP022_general_classical` with `U` replaced by `J`, and the independence of the
isometry `J`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022BClass2
open TensorCarrier PhysicalTensor Prop022GTensor Prop022AIsoTensor Prop022GAntiHS
open Prop022GClassical Prop022GLinear Prop022BIso Prop022BClass1
open Prop022FactorialMajorantR115

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

section Parts
variable (J : H →ₗᵢ[ℂ] L2T L)

lemma Jr_J (x : H) : Jr J (Ext006Blocks.J x) = Ext006Blocks.J (Jr J x) := by
  simp [Ext006Blocks.J_apply]

lemma Jar_J (y : L2T L) : Jar J (Ext006Blocks.J y) = Ext006Blocks.J (Jar J y) := by
  simp [Ext006Blocks.J_apply]

lemma complexPart_compress (T : L2T L →L[ℝ] L2T L) :
    Ext006Blocks.complexPart ((Jar J).comp (T.comp (Jr J))) =
      (Jar J).comp ((Ext006Blocks.complexPart T).comp (Jr J)) := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  simp only [Ext006Blocks.complexPart_apply, ContinuousLinearMap.comp_apply, map_sub, map_smul,
    Jr_J, Jar_J]

lemma antilinearPart_compress (T : L2T L →L[ℝ] L2T L) :
    Ext006Blocks.antilinearPart ((Jar J).comp (T.comp (Jr J))) =
      (Jar J).comp ((Ext006Blocks.antilinearPart T).comp (Jr J)) := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  simp only [Ext006Blocks.antilinearPart_apply, ContinuousLinearMap.comp_apply, map_add, map_smul,
    Jr_J, Jar_J]

lemma complexPart_embed (X : H →L[ℝ] H) :
    Ext006Blocks.complexPart ((Jr J).comp (X.comp (Jar J))) =
      (Jr J).comp ((Ext006Blocks.complexPart X).comp (Jar J)) := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  simp only [Ext006Blocks.complexPart_apply, ContinuousLinearMap.comp_apply, map_sub, map_smul,
    Jr_J, Jar_J]

lemma antilinearPart_embed (X : H →L[ℝ] H) :
    Ext006Blocks.antilinearPart ((Jr J).comp (X.comp (Jar J))) =
      (Jr J).comp ((Ext006Blocks.antilinearPart X).comp (Jar J)) := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  simp only [Ext006Blocks.antilinearPart_apply, ContinuousLinearMap.comp_apply, map_add, map_smul,
    Jr_J, Jar_J]

lemma antilinear_embed (X : H →L[ℝ] H) (hX : Antilinear X) :
    Antilinear ((Jr J).comp (X.comp (Jar J))) := by
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  rw [Jar_J, hX, map_neg, Jr_J]

lemma norm_compress_le (T : L2T L →L[ℝ] L2T L) : ‖(Jar J).comp (T.comp (Jr J))‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) (fun x => ?_)
  simp only [ContinuousLinearMap.comp_apply, Jr_apply, Jar_apply]
  calc ‖Jadj J (T (J x))‖ ≤ ‖T (J x)‖ := norm_Jadj_le J _
    _ ≤ ‖T‖ * ‖J x‖ := T.le_opNorm _
    _ = ‖T‖ * ‖x‖ := by rw [LinearIsometry.norm_map]

/-- **Compression of the HS sum**: the HS sum of an antilinear `X` on `H` equals that of its embedding
in `L2T L`, in any Hilbert bases. -/
theorem antiHS_embed {ι κ : Type*} (e : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ (L2T L))
    (X : H →L[ℝ] H) (hX : Antilinear X) :
    antiHS e X = antiHS c ((Jr J).comp (X.comp (Jar J))) := by
  classical
  set T : L2T L →L[ℝ] L2T L := (Jr J).comp (X.comp (Jar J)) with hTdef
  have hT : Antilinear T := antilinear_embed J X hX
  have hTJ : ∀ z : H, T (J z) = J (X z) := by
    intro z
    simp [hTdef, Jadj_J]
  have hinj : Function.Injective (fun i => J (e i)) :=
    J.injective.comp e.orthonormal.linearIndependent.injective
  have ho : Orthonormal ℂ (fun i => J (e i)) :=
    (LinearIsometry.orthonormal_comp_iff J).mpr e.orthonormal
  have hos : Orthonormal ℂ ((↑) : Set.range (fun i => J (e i)) → L2T L) :=
    (orthonormal_subtype_range hinj).mpr ho
  obtain ⟨w, b, hsw, hb⟩ := hos.exists_hilbertBasis_extension
  have h1 : antiHS e X = ∑' i, ENNReal.ofReal (‖T (J (e i))‖ ^ 2) := by
    unfold antiHS
    refine tsum_congr (fun i => ?_)
    rw [hTJ, LinearIsometry.norm_map]
  have h2 : ∑' i, ENNReal.ofReal (‖T (J (e i))‖ ^ 2) = antiHS b T := by
    unfold antiHS
    let g : ι → w := fun i => ⟨J (e i), hsw ⟨i, rfl⟩⟩
    have hg : Function.Injective g := fun i j h => hinj (congrArg Subtype.val h)
    have hsupp : Function.support (fun x : w => ENNReal.ofReal (‖T (b x)‖ ^ 2)) ⊆ Set.range g := by
      intro x hx
      by_contra hnot
      apply hx
      have hxs : (x : L2T L) ∉ Set.range (fun i => J (e i)) :=
        fun ⟨i, hi⟩ => hnot ⟨i, Subtype.ext hi⟩
      have hperp : ∀ i, ⟪J (e i), (x : L2T L)⟫_ℂ = 0 := by
        intro i
        have hne : (⟨J (e i), hsw ⟨i, rfl⟩⟩ : w) ≠ x :=
          fun h => hxs ⟨i, congrArg Subtype.val h⟩
        have := b.orthonormal.2 hne
        simpa [hb] using this
      have hJx : Jadj J (x : L2T L) = 0 := by
        apply e.repr.injective
        rw [map_zero]
        apply lp.ext
        funext i
        rw [HilbertBasis.repr_apply_apply, inner_Jadj_right, hperp]
        rfl
      have hTx : T (x : L2T L) = 0 := by
        simp [hTdef, hJx]
      simp [hb, hTx]
    have := hg.tsum_eq (f := fun x : w => ENNReal.ofReal (‖T (b x)‖ ^ 2)) hsupp
    rw [← this]
    refine tsum_congr (fun i => ?_)
    simp only [g, hb]
  rw [h1, h2]
  exact antiHS_basis_indep hT b c

end Parts

section Objects
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
  (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

local notation "G'" => gradH (UI L) (kernelsI J K)
local notation "Φ'" => flowH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs)
local notation "u'" => profH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
  (hJu J u₀ hu₀)
local notation "S'" => SH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
  (hJu J u₀ hu₀)
local notation "hess'" => hessH (UI L) (kernelsI J K)

/-- `a_t`: complex-linear part of the Hessian along the trajectory. -/
def aJ (t : ℝ) : H →L[ℝ] H :=
  Ext006Blocks.complexPart (hessJ J K (profJ J K M A hA hK hs u₀ hu₀ t))

/-- `b_t`: antilinear part of the Hessian along the trajectory. -/
def bJ (t : ℝ) : H →L[ℝ] H :=
  Ext006Blocks.antilinearPart (hessJ J K (profJ J K M A hA hK hs u₀ hu₀ t))

def alphaJ (t s : ℝ) : H →L[ℝ] H := Ext006Blocks.complexPart (SJ J K M A hA hK hs u₀ hu₀ t s)

def betaJ (t s : ℝ) : H →L[ℝ] H := Ext006Blocks.antilinearPart (SJ J K M A hA hK hs u₀ hu₀ t s)

lemma hess'_prof (t : ℝ) :
    hess' (u' t) = (Jr J).comp ((hessJ J K (profJ J K M A hA hK hs u₀ hu₀ t)).comp (Jar J)) := by
  rw [hess_embed J K M A hA hK hs]
  rfl

lemma hessJ_prof (t : ℝ) :
    hessJ J K (profJ J K M A hA hK hs u₀ hu₀ t) = (Jar J).comp ((hess' (u' t)).comp (Jr J)) := by
  rw [hessJ_eq J K M A hA hK hs, J_profJ J K M A hA hK hs u₀ hu₀]

lemma aJ_eq (t : ℝ) :
    aJ J K M A hA hK hs u₀ hu₀ t = (Jar J).comp ((aH (UI L) (kernelsI J K) M A hA
      (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) t).comp (Jr J)) := by
  unfold aJ aH
  rw [hessJ_prof J K M A hA hK hs u₀ hu₀, complexPart_compress]

lemma bJ_eq (t : ℝ) :
    bJ J K M A hA hK hs u₀ hu₀ t = (Jar J).comp ((bH (UI L) (kernelsI J K) M A hA
      (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) t).comp (Jr J)) := by
  unfold bJ bH
  rw [hessJ_prof J K M A hA hK hs u₀ hu₀, antilinearPart_compress]

lemma aH'_eq (t : ℝ) :
    aH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) t =
      (Jr J).comp ((aJ J K M A hA hK hs u₀ hu₀ t).comp (Jar J)) := by
  unfold aJ aH
  rw [hess'_prof J K M A hA hK hs u₀ hu₀, complexPart_embed]

lemma bH'_eq (t : ℝ) :
    bH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) t =
      (Jr J).comp ((bJ J K M A hA hK hs u₀ hu₀ t).comp (Jar J)) := by
  unfold bJ bH
  rw [hess'_prof J K M A hA hK hs u₀ hu₀, antilinearPart_embed]

lemma betaH'_eq (t s : ℝ) :
    betaH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) t s =
      (Jr J).comp ((betaJ J K M A hA hK hs u₀ hu₀ t s).comp (Jar J)) := by
  have hS : S' t s = (Jr J).comp ((SJ J K M A hA hK hs u₀ hu₀ t s).comp (Jar J)) +
      (ContinuousLinearMap.id ℝ (L2T L) - (Jr J).comp (Jar J)) := by
    refine ContinuousLinearMap.ext (fun w => ?_)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, Jr_apply, Jar_apply]
    exact S_decomp J K M A hA hK hs u₀ hu₀ t s w
  have hcl : CLinear (ContinuousLinearMap.id ℝ (L2T L) - (Jr J).comp (Jar J)) := by
    intro x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, Jar_J, Jr_J, map_sub]
  unfold betaH
  rw [hS]
  have hadd : ∀ (P Q : L2T L →L[ℝ] L2T L),
      Ext006Blocks.antilinearPart (P + Q) =
        Ext006Blocks.antilinearPart P + Ext006Blocks.antilinearPart Q := by
    intro P Q
    refine ContinuousLinearMap.ext (fun x => ?_)
    simp only [Ext006Blocks.antilinearPart_apply, ContinuousLinearMap.add_apply, map_add,
      smul_add]
    abel
  rw [hadd, antilinearPart_of_clinear hcl, add_zero, antilinearPart_embed]
  rfl

theorem SJ_self (s : ℝ) (x : H) : SJ J K M A hA hK hs u₀ hu₀ s s x = x := by
  rw [SJ_apply, SH_self, Jadj_J]

theorem profJ_spec : profJ J K M A hA hK hs u₀ hu₀ 0 = u₀ ∧ ∀ t,
    ‖profJ J K M A hA hK hs u₀ hu₀ t‖ = 1 ∧
      HasDerivAt (profJ J K M A hA hK hs u₀ hu₀)
        ((-Complex.I) • gradJ J K (profJ J K M A hA hK hs u₀ hu₀ t)) t := by
  obtain ⟨h0, hd⟩ := profH_spec (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs)
    (J u₀) (hJu J u₀ hu₀)
  refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
  · show Jadj J (u' 0) = u₀
    rw [h0, Jadj_J]
  · rw [← LinearIsometry.norm_map J, J_profJ J K M A hA hK hs u₀ hu₀, (hd t).1]
  · have h := hasDerivAt_Jadj J (hd t).2
    rw [map_smul] at h
    refine h.congr_deriv ?_
    congr 1
    show _ = Jadj J (G' (J (profJ J K M A hA hK hs u₀ hu₀ t)))
    rw [J_profJ J K M A hA hK hs u₀ hu₀]

theorem profJ_unique (γ : ℝ → H) (h0 : γ 0 = u₀)
    (hγ : ∀ t, ‖γ t‖ = 1 ∧ HasDerivAt γ ((-Complex.I) • gradJ J K (γ t)) t) :
    γ = profJ J K M A hA hK hs u₀ hu₀ := by
  have hu := profH_unique (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
    (hJu J u₀ hu₀) (fun t => J (γ t)) (by simp only [h0])
    (fun t => ⟨by rw [LinearIsometry.norm_map]; exact (hγ t).1, by
      have h := hasDerivAt_J J (hγ t).2
      rw [map_smul, ← grad_embed_J J K M A hA hK hs] at h
      exact h⟩)
  funext t
  have ht := congrFun hu t
  change J (γ t) = u' t at ht
  show γ t = Jadj J (u' t)
  rw [← ht, Jadj_J]

theorem flowJ_spec (x : H) : flowJ J K M A hA hK hs 0 x = x ∧ ∀ t,
    HasDerivAt (fun r => flowJ J K M A hA hK hs r x)
      ((-Complex.I) • gradJ J K (flowJ J K M A hA hK hs t x)) t ∧
    ‖flowJ J K M A hA hK hs t x‖ = ‖x‖ := by
  obtain ⟨h0, hd⟩ := flowH_spec (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J x)
  refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
  · show Jadj J (Φ' 0 (J x)) = x
    rw [h0, Jadj_J]
  · have h := hasDerivAt_Jadj J (hd t).1
    rw [map_smul] at h
    refine h.congr_deriv ?_
    congr 1
    show _ = Jadj J (G' (J (flowJ J K M A hA hK hs t x)))
    rw [J_flowJ J K M A hA hK hs]
  · rw [← LinearIsometry.norm_map J, J_flowJ J K M A hA hK hs, (hd t).2, LinearIsometry.norm_map]

theorem flowJ_profJ (s t : ℝ) :
    flowJ J K M A hA hK hs (t - s) (profJ J K M A hA hK hs u₀ hu₀ s) =
      profJ J K M A hA hK hs u₀ hu₀ t := by
  show Jadj J (Φ' (t - s) (J (profJ J K M A hA hK hs u₀ hu₀ s))) = Jadj J (u' t)
  rw [J_profJ J K M A hA hK hs u₀ hu₀, flowH_profH]

theorem norm_S'_le (T P : ℝ) (hP : 1 ≤ P) (t s : ℝ) (hS : ‖SJ J K M A hA hK hs u₀ hu₀ t s‖ ≤ P) :
    ‖S' t s‖ ≤ P := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun w => ?_)
  rw [S_decomp J K M A hA hK hs u₀ hu₀]
  set y := SJ J K M A hA hK hs u₀ hu₀ t s (Jadj J w) with hy
  set z := w - J (Jadj J w) with hz
  have hzJ : Jadj J z = 0 := by rw [hz, map_sub, Jadj_J, sub_self]
  have horth : ⟪J y, z⟫_ℂ = 0 := by rw [← inner_Jadj_right, hzJ, inner_zero_right]
  have h1 : ‖J y + z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (J y) z horth
    rw [LinearIsometry.norm_map] at this
    rw [sq, sq, sq]
    exact this
  have horth2 : ⟪J (Jadj J w), z⟫_ℂ = 0 := by rw [← inner_Jadj_right, hzJ, inner_zero_right]
  have h2 : ‖w‖ ^ 2 = ‖Jadj J w‖ ^ 2 + ‖z‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (J (Jadj J w)) z horth2
    rw [LinearIsometry.norm_map, hz, add_sub_cancel] at this
    rw [sq, sq, hz, sq]
    exact this
  have hy1 : ‖y‖ ≤ P * ‖Jadj J w‖ := by
    calc ‖y‖ = ‖SJ J K M A hA hK hs u₀ hu₀ t s (Jadj J w)‖ := rfl
      _ ≤ ‖SJ J K M A hA hK hs u₀ hu₀ t s‖ * ‖Jadj J w‖ := (SJ J K M A hA hK hs u₀ hu₀ t s).le_opNorm _
      _ ≤ P * ‖Jadj J w‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
  have hy2 : ‖y‖ ^ 2 ≤ P ^ 2 * ‖Jadj J w‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hy1 2
  have hP2 : 1 ≤ P ^ 2 := by nlinarith
  have h3 : ‖J y + z‖ ^ 2 ≤ (P * ‖w‖) ^ 2 := by
    rw [h1, mul_pow, h2]
    nlinarith [sq_nonneg ‖z‖, sq_nonneg ‖Jadj J w‖]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h3

end Objects

end QuantumNLS.Prop022BClass2
