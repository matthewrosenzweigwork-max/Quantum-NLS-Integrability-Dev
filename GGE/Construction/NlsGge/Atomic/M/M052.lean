import Mathlib
import NlsGge.Atomic.M.M010
import NlsGge.Atomic.M.M051
import NlsGge.Atomic.G2.G2037
import NlsGge.Spectral.ActualQuasimomentumFullInfinityE02_38

set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.M

/-- Literal agreement on the endpoint-filled source domain outside one disk. -/
def ExteriorPrimitiveRepresentative (φ : PotPair) (R : ℝ)
    (F : ℂ → ℂ) : Prop :=
  0 < R ∧
  ∀ z : ℂ, R < ‖z‖ →
    ∃ hz : φ ∈ gkW ∧ z ∈ MPrimitive.endpointClosureFiber φ,
      F z = primitive ⟨(φ, z), hz⟩

namespace M052Aux

theorem analytic_chart_value_eq_of_tendsto
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (z : ℕ → ℂ) (hz : Tendsto z atTop (𝓝 (0 : ℂ)))
    (c : ℂ)
    (hgz : Tendsto (fun n => g (z n) - c) atTop (𝓝 (0 : ℂ))) :
    g 0 = c := by
  have hcont : Tendsto (fun n => g (z n) - c) atTop (𝓝 (g 0 - c)) :=
    (hg.continuousAt.tendsto.comp hz).sub_const c
  have heq := tendsto_nhds_unique hcont hgz
  exact sub_eq_zero.mp heq

end M052Aux

namespace M052Replica

def imaginaryAxisSeq (n : ℕ) : ℂ := ((n + 1 : ℕ) : ℂ) * Complex.I

theorem imaginaryAxisSeq_im_pos (n : ℕ) : 0 < (imaginaryAxisSeq n).im := by
  norm_num [imaginaryAxisSeq, Complex.mul_im]
  positivity

theorem imaginaryAxisSeq_norm (n : ℕ) :
    ‖imaginaryAxisSeq n‖ = (n : ℝ) + 1 := by
  rw [imaginaryAxisSeq, norm_mul, Complex.norm_natCast, Complex.norm_I]
  simp only [Nat.cast_add, Nat.cast_one, mul_one]

theorem inv_imaginaryAxisSeq_tendsto_zero :
    Tendsto (fun n : ℕ => (imaginaryAxisSeq n)⁻¹) atTop (𝓝 (0 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hEventually : ∀ᶠ n : ℕ in atTop, Nat.ceil (ε⁻¹) + 1 ≤ n :=
    Filter.eventually_atTop.2 ⟨Nat.ceil (ε⁻¹) + 1, fun n hn => hn⟩
  filter_upwards [hEventually] with n hn
  rw [dist_eq_norm, sub_zero, norm_inv, imaginaryAxisSeq_norm]
  have hnreal : (Nat.ceil (ε⁻¹) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hceil : ε⁻¹ ≤ (Nat.ceil (ε⁻¹) : ℝ) := Nat.le_ceil _
  have hden : ε⁻¹ < (n : ℝ) + 1 := by linarith
  have hinv := (inv_lt_inv₀ (by positivity : 0 < (n : ℝ) + 1)
    (inv_pos.mpr hε)).2 hden
  simpa only [inv_inv] using hinv

theorem hasDerivAt_congr_of_localEq
    {f g : ℂ → ℂ} {f' x : ℂ}
    (hf : HasDerivAt f f' x) (hgf : g =ᶠ[𝓝 x] f) :
    HasDerivAt g f' x :=
  hf.congr_of_eventuallyEq hgf

theorem analyticAt_congr_of_localEq
    {f g : ℂ → ℂ} {x : ℂ}
    (hg : AnalyticAt ℂ g x) (hfg : f =ᶠ[𝓝 x] g) :
    AnalyticAt ℂ f x :=
  hg.congr hfg.symm

end M052Replica

namespace M052Replica2

theorem additive_const_eq_zero {a d : ℂ} (h : a = a + d) : d = 0 := by
  have h' := congrArg (fun x : ℂ => x - a) h
  calc
    d = (a + d) - a := by ring
    _ = a - a := h'.symm
    _ = 0 := sub_self _

theorem verticalPath_mem_upper (x ε : ℝ) (hε : 0 < ε) :
    (x : ℂ) + Complex.I * (ε : ℂ) ∈ {z : ℂ | 0 < z.im} := by
  change 0 < ((x : ℂ) + Complex.I * (ε : ℂ)).im
  have hIm : (Complex.I * (ε : ℂ)).im = ε := by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re]
    ring
  rw [Complex.add_im, Complex.ofReal_im, hIm]
  simpa only [zero_add] using hε

theorem alias_rewrite {α β : Type} (f : α → β) {a b : α} (hab : a = b) :
    f a = f b := by
  rw [hab]

theorem subtypeFunction_congr
    {α : Type} {p : α → Prop} {β : Type}
    (f : {a : α // p a} → β) {x y : α}
    (hxy : x = y) (hx : p x) (hy : p y) :
    f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
  subst y
  have hproof : hx = hy := Subsingleton.elim _ _
  subst hy
  rfl

noncomputable def reciprocalChart (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  if w = 0 then 0 else F w⁻¹ + Complex.I * w⁻¹

theorem reciprocalChart_apply_inv (F : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    reciprocalChart F (z⁻¹) = F z + Complex.I * z := by
  have hzinv : z⁻¹ ≠ 0 := inv_ne_zero hz
  calc
    reciprocalChart F (z⁻¹) = F (z⁻¹)⁻¹ + Complex.I * (z⁻¹)⁻¹ := by
      simp only [reciprocalChart, if_neg hzinv]
    _ = F z + Complex.I * z := by rw [inv_inv]

end M052Replica2

namespace M052Replica3

theorem subtypeValue_eq
    {α : Type} {p : α → Prop} {x y : α} (hxy : x = y)
    (hx : p x) (hy : p y) :
    (⟨x, hx⟩ : {a : α // p a}) = ⟨y, hy⟩ := by
  apply Subtype.ext
  exact hxy

end M052Replica3

theorem finitegap_primitive_meromorphic_infinity
    (u : PhysicalL2) (hfg : finiteGap u) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      ExteriorPrimitiveRepresentative (realSlice u) R F ∧
      MPrimitive.ExteriorHolomorphic F ∧
      AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z) ∧
      MPrimitive.HasValueAtInfinity (fun z : ℂ => F z + Complex.I * z) 0 := by
  classical
  have hG2037 :
      ∃ S : Finset ℤ,
        (∀ n : ℤ, n ∈ S ↔
          actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n) ∧
        AnalyticOnNhd ℂ (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ ∧
        (∀ z : ℂ, (realSlice u,z) ∈ rootDomain38 →
          deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z =
            finiteGapDifferential u S z) ∧
        (∀ (C : ℤ → ℂ) (R : ℤ → ℝ), IsolatingFamily38 (realSlice u) C R →
          ∀ n : ℤ, CircleIntegrable (finiteGapDifferential u S) (C n) (R n) ∧
            circleIntegral (finiteGapDifferential u S) (C n) (R n) = 0) ∧
        ∃ R : ℝ, 0 < R ∧ finiteGapCuts u S ⊆ Metric.closedBall (0 : ℂ) R ∧
          ∃ f g : ℂ → ℂ,
            AnalyticOnNhd ℂ f (finiteGapCuts u S)ᶜ ∧
            (∀ z : ℂ, z ∉ finiteGapCuts u S →
              HasDerivAt f (finiteGapDifferential u S z) z) ∧
            AnalyticAt ℂ g 0 ∧
            (∀ z : ℂ, R < ‖z‖ → f z = -Complex.I*z + g z⁻¹) :=
    NlsGge.GKDefinitionDesign.G2_037 u hfg
  obtain ⟨S, hG2037Rest⟩ := hG2037
  obtain ⟨hS, hG2037Rest⟩ := hG2037Rest
  obtain ⟨_, hG2037Rest⟩ := hG2037Rest
  obtain ⟨hrootEq, hG2037Rest⟩ := hG2037Rest
  obtain ⟨_, hG2037Rest⟩ := hG2037Rest
  obtain ⟨R0, hG2037Rest⟩ := hG2037Rest
  obtain ⟨hR0, hG2037Rest⟩ := hG2037Rest
  obtain ⟨hcuts, hG2037Rest⟩ := hG2037Rest
  obtain ⟨f, hG2037Rest⟩ := hG2037Rest
  obtain ⟨g, hG2037Rest⟩ := hG2037Rest
  obtain ⟨hf, hG2037Rest⟩ := hG2037Rest
  obtain ⟨hfd, hG2037Rest⟩ := hG2037Rest
  obtain ⟨hg, hexp⟩ := hG2037Rest
  let φ : PotPair := realSlice u
  let k : ℂ → ℂ := actualQuasimomentumE02_38 u
  let R : ℝ := R0 + 1
  let F : ℂ → ℂ := fun z => f z - g 0
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hnotcuts : ∀ z : ℂ, R < ‖z‖ → z ∉ finiteGapCuts u S := by
    intro z hz hzc
    have hb := hcuts hzc
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    dsimp [R] at hz
    linarith
  have hcutsReal : ∀ z : ℂ, z ∈ finiteGapCuts u S → z.im = 0 := by
    intro z hz
    change z ∈ ⋃ n ∈ (S : Set ℤ), gapSegment φ n at hz
    obtain ⟨n, hnS, hseg⟩ := Set.mem_iUnion₂.1 hz
    have hseg' : z ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
      simpa [gapSegment, φ] using hseg
    exact MPrimitive.segment_im_zero u n hseg'
  have hfiniteSubsetGap : finiteGapCuts u S ⊆ gapSegments38 φ := by
    intro z hz
    change z ∈ ⋃ n ∈ (S : Set ℤ), gapSegment φ n at hz
    obtain ⟨n, hnS, hseg⟩ := Set.mem_iUnion₂.1 hz
    have hseg' : z ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
      simpa [gapSegment, φ] using hseg
    change z ∈ ⋃ n : ℤ, segment ℝ (lamMinus φ n) (lamPlus φ n)
    exact Set.mem_iUnion.2 ⟨n, hseg'⟩
  let upper : Set ℂ := {z | 0 < z.im}
  have hupperOpen : IsOpen upper := by
    exact isOpen_lt continuous_const Complex.continuous_im
  have hupperPre : IsPreconnected upper :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have hupperFder : ∀ z ∈ upper,
      HasDerivAt f (finiteGapDifferential u S z) z := by
    intro z hz
    apply hfd
    intro hzc
    have := hcutsReal z hzc
    change 0 < z.im at hz
    linarith
  have hupperQder : ∀ z ∈ upper,
      HasDerivAt (fun w => -Complex.I * k w) (finiteGapDifferential u S z) z := by
    intro z hz
    have hroot : (realSlice u, z) ∈ rootDomain38 := by
      exact ⟨realSlice_mem_gkW u,
        MPrimitive.nonreal_mem_cutFreeFiber u (ne_of_gt hz)⟩
    have hEq := hrootEq z hroot
    exact (NlsGge.GK38.ActionBranch.primitive_hasDeriv_upper u z hz).congr_deriv hEq
  obtain ⟨c, hc⟩ :=
    NlsGge.ThirdConsultation.MPrimitive.exists_const_eq_add
      hupperOpen hupperPre ⟨Complex.I, by
        change 0 < Complex.I.im
        norm_num⟩
      (P := f) (g := fun z => -Complex.I * k z)
      (w := fun z => finiteGapDifferential u S z)
      hupperFder hupperQder
  let zseq : ℕ → ℂ := M052Replica.imaginaryAxisSeq
  have hzseqIm : ∀ n : ℕ, 0 < (zseq n).im := M052Replica.imaginaryAxisSeq_im_pos
  have hzseqNorm : ∀ n : ℕ, ‖zseq n‖ = (n : ℝ) + 1 := M052Replica.imaginaryAxisSeq_norm
  have hKlim : Tendsto (fun n : ℕ => k (zseq n) - zseq n) atTop (𝓝 (0 : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨Rk, hRk, hbound⟩ :=
      actualQuasimomentumE02_38_sub_tendsto_zero u ε hε
    filter_upwards
      [Filter.eventually_ge_atTop (Nat.ceil Rk)] with n hn
    rw [dist_eq_norm, sub_zero]
    change ‖actualQuasimomentumE02_38 u (zseq n) - zseq n‖ < ε
    apply hbound (zseq n) (hzseqIm n)
    rw [hzseqNorm]
    have hnreal : (Nat.ceil Rk : ℝ) ≤ n := by exact_mod_cast hn
    have hceil : Rk ≤ (Nat.ceil Rk : ℝ) := Nat.le_ceil Rk
    linarith
  have hRelation : (fun n : ℕ => g ((zseq n)⁻¹) - c) =ᶠ[atTop]
      (fun n => -Complex.I * (k (zseq n) - zseq n)) := by
    filter_upwards
      [Filter.eventually_ge_atTop (Nat.ceil R0)] with n hn
    have hlarge : R0 < ‖zseq n‖ := by
      rw [hzseqNorm]
      have hnreal : (Nat.ceil R0 : ℝ) ≤ n := by exact_mod_cast hn
      have hceil : R0 ≤ (Nat.ceil R0 : ℝ) := Nat.le_ceil R0
      linarith
    have hexpn := hexp (zseq n) hlarge
    have hcN := hc (zseq n) (hzseqIm n)
    calc
      g ((zseq n)⁻¹) - c = (-Complex.I * zseq n + g ((zseq n)⁻¹)) +
          Complex.I * zseq n - c := by ring
      _ = f (zseq n) + Complex.I * zseq n - c := by rw [hexpn]
      _ = -Complex.I * (k (zseq n) - zseq n) := by rw [hcN]; ring
  have hKlim' : Tendsto (fun n : ℕ => -Complex.I * (k (zseq n) - zseq n))
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [mul_zero] using hKlim.const_mul (-Complex.I)
  have hgminus : Tendsto (fun n : ℕ => g ((zseq n)⁻¹) - c)
      atTop (𝓝 (0 : ℂ)) := hKlim'.congr' hRelation.symm
  have hInvSeq : Tendsto (fun n : ℕ => (zseq n)⁻¹) atTop (𝓝 (0 : ℂ)) := by
    exact M052Replica.inv_imaginaryAxisSeq_tendsto_zero
  have hg0c := M052Aux.analytic_chart_value_eq_of_tendsto g hg
    (fun n => (zseq n)⁻¹) hInvSeq c hgminus
  have hupperValue : ∀ z : ℂ, z ∈ upper → F z = -Complex.I * k z := by
    intro z hz
    dsimp [F]
    rw [hc z hz, hg0c]
    ring
  let P : ℂ → ℂ := fun z =>
    if hz : z ∈ MPrimitive.cutFreeFiber φ then
      primitive ⟨(φ, z), ⟨realSlice_mem_gkW u, Or.inl hz⟩⟩
    else 0
  have hPder : ∀ z ∈ MPrimitive.cutFreeFiber φ,
      HasDerivAt P (MContour.omega φ z) z := by
    intro z hz
    obtain ⟨U, hU, hzU, hUD, L, hL, hLD⟩ :=
      MPrimitive.symmetric_primitive_hasDerivAt φ (realSlice_mem_gkW u) z hz
    have hloc : P =ᶠ[𝓝 z] L := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      have hwF := hUD hw
      have hPval : P w = MPrimitive.symmetricPrimitive
          ⟨(φ, w), ⟨realSlice_mem_gkW u, Or.inl hwF⟩⟩ := by
        simp only [P, dif_pos hwF, M.primitive]
      exact hPval.trans (hL w hw).symm
    exact M052Replica.hasDerivAt_congr_of_localEq (hLD z hzU) hloc
  have hFder : ∀ z ∈ MPrimitive.cutFreeFiber φ,
      HasDerivAt F (finiteGapDifferential u S z) z := by
    intro z hz
    have hzNot : z ∉ finiteGapCuts u S := fun h => hz (hfiniteSubsetGap h)
    change HasDerivAt (fun w => f w - g 0) (finiteGapDifferential u S z) z
    exact (hfd z hzNot).sub_const (g 0)
  have hPderFD : ∀ z ∈ MPrimitive.cutFreeFiber φ,
      HasDerivAt P (finiteGapDifferential u S z) z := by
    intro z hz
    have hroot : (realSlice u, z) ∈ rootDomain38 := ⟨realSlice_mem_gkW u, hz⟩
    have hEq := hrootEq z hroot
    have h := hPder z hz
    change HasDerivAt P (deriv (discrim φ) z / canonRoot38 φ z) z at h
    exact h.congr_deriv hEq
  obtain ⟨d, hPF⟩ :=
    NlsGge.ThirdConsultation.MPrimitive.exists_const_eq_add
      (MPrimitive.cutFreeFiber_isOpen φ (realSlice_mem_gkW u))
      (MPrimitive.polygonal_isPreconnected
        (MPrimitive.cutFreeFiber_polygonal φ (realSlice_mem_gkW u)))
      ⟨Complex.I, MPrimitive.nonreal_mem_cutFreeFiber u (by simp)⟩
      (P := P) (g := F) (w := fun z => finiteGapDifferential u S z)
      hPderFD hFder
  have hI : Complex.I ∈ MPrimitive.cutFreeFiber φ :=
    MPrimitive.nonreal_mem_cutFreeFiber u (by simp)
  have hPI : P Complex.I = -Complex.I * k Complex.I := by
    have h := (MPrimitive.primitive_formulas u).1 Complex.I (by norm_num)
    simpa only [P, dif_pos hI, M.primitive, φ, k] using h
  have hFI : F Complex.I = -Complex.I * k Complex.I :=
    hupperValue Complex.I (by
      change 0 < Complex.I.im
      norm_num)
  have hdzero : d = 0 := by
    have h := hPF Complex.I hI
    rw [hPI, hFI] at h
    exact M052Replica2.additive_const_eq_zero h
  have hPF_eq : ∀ z ∈ MPrimitive.cutFreeFiber φ, F z = P z := by
    intro z hz
    have h := hPF z hz
    rw [hdzero, add_zero] at h
    exact h.symm
  have hmemExterior : ∀ z : ℂ, R < ‖z‖ →
      z ∈ MPrimitive.endpointClosureFiber φ := by
    intro z hz
    by_cases hzfree : z ∈ MPrimitive.cutFreeFiber φ
    · exact Or.inl hzfree
    · obtain ⟨n, hseg⟩ := MPrimitive.exists_cut_of_not_mem_fiber hzfree
      by_cases hnS : n ∈ S
      · have hzCut : z ∈ finiteGapCuts u S := by
          change z ∈ ⋃ j ∈ (S : Set ℤ), gapSegment φ j
          exact Set.mem_iUnion₂.2 ⟨n, hnS, hseg⟩
        have hb := hcuts hzCut
        rw [Metric.mem_closedBall, dist_zero_right] at hb
        dsimp [R] at hz
        linarith
      · have hend := NlsGge.GK38.lamPlus_real u n
        have hcollapse : lamMinus φ n = lamPlus φ n := by
          by_contra hne
          apply hnS
          apply (hS n).2
          intro hEq
          apply hne
          rw [hend.2, hend.1, hEq]
        have hseg' : z ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
          simpa [gapSegment, φ] using hseg
        rw [hcollapse, segment_same] at hseg'
        have hzpoint : z = lamPlus φ n := by simpa using hseg'
        exact Or.inr ⟨n, Or.inr hzpoint⟩
  have hrep : ExteriorPrimitiveRepresentative φ R F := by
    refine ⟨hRpos, ?_⟩
    intro z hz
    have hm := hmemExterior z hz
    refine ⟨⟨realSlice_mem_gkW u, hm⟩, ?_⟩
    by_cases hzfree : z ∈ MPrimitive.cutFreeFiber φ
    · have h := hPF_eq z hzfree
      simpa only [P, dif_pos hzfree, M.primitive] using h
    · have him : z.im = 0 := by
        by_contra hne
        exact hzfree (MPrimitive.nonreal_mem_cutFreeFiber u hne)
      have hx : z = (z.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [him]
      have hxmem : (z.re : ℂ) ∈ MPrimitive.endpointClosureFiber φ := by
        exact hx ▸ hm
      have hxnot : (z.re : ℂ) ∉ finiteGapCuts u S := by
        exact hx ▸ hnotcuts z hz
      have hFa : AnalyticAt ℂ F (z.re : ℂ) := by
        change AnalyticAt ℂ (fun w => f w - g 0) (z.re : ℂ)
        exact (hf (z.re : ℂ) hxnot).sub analyticAt_const
      have hPathUpper : Tendsto (fun ε : ℝ => (z.re : ℂ) + Complex.I * (ε : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝[{w : ℂ | 0 < w.im}] (z.re : ℂ)) :=
        vertical_tendsto_upper_E02_38 z.re
      have hFlim : Tendsto
          (fun ε : ℝ => F ((z.re : ℂ) + Complex.I * (ε : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 (F (z.re : ℂ))) :=
        hFa.continuousAt.tendsto.comp (hPathUpper.mono_right nhdsWithin_le_nhds)
      have hKlim : Tendsto
          (fun ε : ℝ => -Complex.I *
            actualQuasimomentumE02_38 u ((z.re : ℂ) + Complex.I * (ε : ℂ)))
          (𝓝[>] (0 : ℝ))
          (𝓝 (-Complex.I * actualQuasimomentumBoundaryE02_38 u z.re)) :=
        (tendsto_actualQuasimomentumBoundaryE02_38 u z.re).comp hPathUpper |>.const_mul (-Complex.I)
      have hEqPath :
          (fun ε : ℝ => F ((z.re : ℂ) + Complex.I * (ε : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun ε : ℝ => -Complex.I *
            actualQuasimomentumE02_38 u ((z.re : ℂ) + Complex.I * (ε : ℂ))) := by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hPointUpper : (z.re : ℂ) + Complex.I * (ε : ℂ) ∈ upper :=
          M052Replica2.verticalPath_mem_upper z.re ε hε
        exact hupperValue _ hPointUpper
      have hFboundary := tendsto_nhds_unique hFlim (hKlim.congr' hEqPath.symm)
      have hMboundary := (MPrimitive.primitive_formulas u).2.2 z.re hxmem
      have hTarget : F (z.re : ℂ) =
          primitive ⟨(realSlice u, (z.re : ℂ)), ⟨realSlice_mem_gkW u, hxmem⟩⟩ := by
        have hMboundary' := hMboundary
        dsimp only [realSlice] at hMboundary'
        dsimp only [primitive, M.primitive, realSlice]
        rw [hMboundary']
        exact hFboundary
      have hPair :
          ((realSlice u, z) : PotPair × ℂ) = (realSlice u, (z.re : ℂ)) :=
        congrArg (fun w : ℂ => (realSlice u, w)) hx
      have hPrimitivePoint :
          (⟨(realSlice u, z), ⟨realSlice_mem_gkW u, hm⟩⟩ : PrimitivePoint) =
            ⟨(realSlice u, (z.re : ℂ)), ⟨realSlice_mem_gkW u, hxmem⟩⟩ :=
        M052Replica3.subtypeValue_eq hPair
          ⟨realSlice_mem_gkW u, hm⟩ ⟨realSlice_mem_gkW u, hxmem⟩
      have hPrimitiveTransport :
          primitive ⟨(realSlice u, z), ⟨realSlice_mem_gkW u, hm⟩⟩ =
          primitive ⟨(realSlice u, (z.re : ℂ)), ⟨realSlice_mem_gkW u, hxmem⟩⟩ :=
        congrArg (fun p : PrimitivePoint => primitive p) hPrimitivePoint
      calc
        F z = F (z.re : ℂ) := congrArg F hx
        _ = primitive ⟨(realSlice u, (z.re : ℂ)), ⟨realSlice_mem_gkW u, hxmem⟩⟩ := hTarget
        _ = primitive ⟨(realSlice u, z), ⟨realSlice_mem_gkW u, hm⟩⟩ :=
          hPrimitiveTransport.symm
  have hExteriorHolomorphic : MPrimitive.ExteriorHolomorphic F := by
    refine ⟨R, hRpos, ?_⟩
    intro z hz
    change AnalyticAt ℂ (fun w => f w - g 0) z
    exact (hf z (hnotcuts z hz)).sub analyticAt_const
  let chart : ℂ → ℂ := M052Replica2.reciprocalChart F
  have hchartEq : chart =ᶠ[𝓝 (0 : ℂ)] (fun w => g w - g 0) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.2 hR0)] with w hw
    by_cases hw0 : w = 0
    · simp [chart, M052Replica2.reciprocalChart, hw0]
    · have hwball : ‖w‖ < R0⁻¹ := by
        simpa [Metric.mem_ball, dist_zero_right] using hw
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hprod : R0 * ‖w‖ < 1 := by
        calc
          R0 * ‖w‖ < R0 * R0⁻¹ := mul_lt_mul_of_pos_left hwball hR0
          _ = 1 := by field_simp
      have hlarge : R0 < ‖w⁻¹‖ := by
        rw [norm_inv, ← one_div]
        exact (lt_div_iff₀ hwpos).2 hprod
      have hexpn := hexp (w⁻¹) hlarge
      have hchartw : chart w = F w⁻¹ + Complex.I * w⁻¹ := by
        simp only [chart, M052Replica2.reciprocalChart, if_neg hw0]
      rw [hchartw]
      change (f w⁻¹ - g 0) + Complex.I * w⁻¹ = g w - g 0
      rw [hexpn, inv_inv]
      ring
  have hchartAnalytic : AnalyticAt ℂ chart 0 := by
    have hgsub : AnalyticAt ℂ (fun w => g w - g 0) 0 := hg.sub analyticAt_const
    exact M052Replica.analyticAt_congr_of_localEq hgsub hchartEq
  have hAnalyticAtInfinity : AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z) := by
    change AnalyticAt ℂ
      (fun w : ℂ => if w = 0 then 0 else F w⁻¹ + Complex.I * w⁻¹) 0
    exact hchartAnalytic
  have hchartCont : Tendsto (fun w : ℂ => g w - g 0)
      (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have h : Tendsto (fun w : ℂ => g w - g 0) (𝓝 (0 : ℂ))
        (𝓝 (g 0 - g 0)) :=
      (hg.sub (analyticAt_const (v := g 0))).continuousAt.tendsto
    have hzero : Tendsto (fun w : ℂ => g w - g 0) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa only [sub_self] using h
    exact hzero.mono_left nhdsWithin_le_nhds
  have hchartCont' : Tendsto chart (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    hchartCont.congr' (hchartEq.filter_mono nhdsWithin_le_nhds).symm
  have hinv : Tendsto (fun z : ℂ => z⁻¹) MPrimitive.infinityFilter
      (𝓝[≠] (0 : ℂ)) := by
    unfold MPrimitive.infinityFilter
    exact Filter.tendsto_comap
  have hcomp : Tendsto (fun z : ℂ => chart (z⁻¹)) MPrimitive.infinityFilter
      (𝓝 (0 : ℂ)) := hchartCont'.comp hinv
  have hInfNe : ∀ᶠ z : ℂ in MPrimitive.infinityFilter, z ≠ 0 := by
    have hInvNe : ∀ᶠ z : ℂ in MPrimitive.infinityFilter, z⁻¹ ≠ 0 :=
      hinv.eventually (self_mem_nhdsWithin : {w : ℂ | w ≠ 0} ∈ 𝓝[≠] (0 : ℂ))
    filter_upwards [hInvNe] with z hz
    by_contra hz0
    subst z
    simpa using hz
  have hInfEq : (fun z : ℂ => chart (z⁻¹)) =ᶠ[MPrimitive.infinityFilter]
      (fun z => F z + Complex.I * z) := by
    filter_upwards [hInfNe] with z hz
    simpa only [chart] using M052Replica2.reciprocalChart_apply_inv F hz
  have hValueAtInfinity : MPrimitive.HasValueAtInfinity
      (fun z : ℂ => F z + Complex.I * z) 0 := by
    unfold MPrimitive.HasValueAtInfinity
    exact hcomp.congr' hInfEq
  exact ⟨R, F, hrep, hExteriorHolomorphic, hAnalyticAtInfinity, hValueAtInfinity⟩

end NlsGge.ThirdConsultation.M
