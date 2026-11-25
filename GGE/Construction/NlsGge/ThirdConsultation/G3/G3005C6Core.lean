import Mathlib
import Armstrong.Frozen.RawBeta.GKArcCurve38
import Armstrong.Frozen.RawBeta.GKArcSheet38
import Armstrong.Frozen.RawBeta.GKPathMiddleIntegral38
import Armstrong.Frozen.RawBeta.GKRootedArcChain38
import Armstrong.Frozen.RawBeta.GKRootedArcIntegrand38
import Armstrong.Frozen.RawBeta.GKRootedC1Arc38
import Armstrong.Frozen.RawBeta.GKOriginalSlit38
import Armstrong.Work.RawBetaSpectralInput
import Armstrong.Work.RawBetaEndpointZero
import Armstrong.Work.CartesianEtaPathSpec

                                                                                                                                                                            
                                                                                                                            
                                                                                                                    
                                                                                                                                 
                                                                                                                              
                                                                                                   
                                                                                             
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory intervalIntegral
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G3005C6
noncomputable section

theorem hasDerivAt_comp_left {f : ℂ → ℂ} {g h : ℝ → ℂ} {f' h' : ℂ} {t : ℝ}
    (hg : ContinuousAt g t) (hf : HasDerivAt f f' (g t))
    (hh : HasDerivAt h h' t) (hf' : f' ≠ 0)
    (hcomp : f ∘ g =ᶠ[nhds t] h) :
    HasDerivAt g (h' / f') t := by
  have hinv : Function.LeftInverse
      ((ContinuousLinearMap.toSpanSingleton ℂ f'⁻¹).restrictScalars ℝ)
      ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ) := by
    intro z
    simp [hf']
  have hd := HasFDerivAt.of_comp_of_leftInverse hg
    (hf.hasFDerivAt.restrictScalars ℝ) hh.hasFDerivAt hcomp hinv
  simpa [div_eq_mul_inv] using hd.hasDerivAt

theorem root_hasDerivAt {s : ℝ → ℂ} {t : ℝ} {q : ℂ}
    (hsc : ContinuousAt s t) (hsn : s t ≠ 0)
    (hsq : HasDerivAt (fun u => s u ^ 2) q t) :
    HasDerivAt s (q / (2 * s t)) t := by
  have hpow : HasDerivAt (fun z : ℂ => z ^ 2) (2 * s t) (s t) := by
    simpa using hasDerivAt_pow 2 (s t)
  exact hasDerivAt_comp_left hsc hpow hsq
    (mul_ne_zero (by norm_num) hsn) Filter.EventuallyEq.rfl

theorem sheet_primitive_hasDerivAt
    {P Ψ R : ℂ → ℂ} {γ s : ℝ → ℂ} {t : ℝ} {P' R' γ' : ℂ}
    (hγ : HasDerivAt γ γ' t) (hP : HasDerivAt P P' (γ t))
    (hR : HasDerivAt R R' (γ t))
    (hsc : ContinuousAt s t) (hsn : s t ≠ 0)
    (he : (fun u => s u ^ 2) =ᶠ[nhds t] P ∘ γ)
    (hODE : P (γ t) * R' + (P' / 2) * R (γ t) = Ψ (γ t)) :
    HasDerivAt (fun u => s u * R (γ u)) ((Ψ (γ t) / s t) * γ') t := by
  have hs : HasDerivAt s ((P' * γ') / (2 * s t)) t :=
    root_hasDerivAt hsc hsn ((hP.comp t hγ).congr_of_eventuallyEq he)
  have hsq : s t ^ 2 = P (γ t) := he.self_of_nhds
  apply (hs.mul (hR.comp t hγ)).congr_deriv
  calc
    ((P' * γ') / (2 * s t)) * R (γ t) + s t * (R' * γ')
        = ((s t ^ 2 * R' + (P' / 2) * R (γ t)) / s t) * γ' := by
            field_simp [hsn]
            ring
    _ = ((Ψ (γ t) / s t) * γ') := by rw [hsq, hODE]

/-- The sheet of a rooted arc is nonzero on the open parameter interval. -/
theorem arc_sheet_ne_zero (φ : GKPotential38) (m : ℤ) (a : GKRootedC1Arc38 φ m)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : GKArcSheet38 a t ≠ 0 := by
  intro hz
  have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  apply rawBetaPerCharNonzeroOnSlit38 φ m (GKArcCurve38 a t) (a.2.2.2.2.2.2 t ht)
  have hsq : GKArcSheet38 a t ^ 2 = perChar φ.1 (GKArcCurve38 a t) := a.2.2.2.2.1 t htc
  simpa only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hsq.symm

/-- Primitive of the rooted arc integrand built from an analytic coefficient. -/
def arcPrim (φ : GKPotential38) (m : ℤ) (R : ℂ → ℂ) (a : GKRootedC1Arc38 φ m) (t : ℝ) : ℂ :=
  GKArcSheet38 a t * R (GKArcCurve38 a t)

theorem arcPrim_continuousOn (φ : GKPotential38) (m : ℤ) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (a : GKRootedC1Arc38 φ m) :
    ContinuousOn (arcPrim φ m R a) (Icc (0 : ℝ) 1) :=
  a.2.2.2.1.mul (hR.continuousOn.comp a.2.1 (fun t ht => a.2.2.2.2.2.1 t ht))

theorem arcPrim_hasDerivAt (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (a : GKRootedC1Arc38 φ m) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (arcPrim φ m R a) (GKRootedArcIntegrand38 n m F φ a t) t := by
  have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have htn : Icc (0 : ℝ) 1 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hγd : DifferentiableAt ℝ (GKArcCurve38 a) t :=
    (a.2.2.1.differentiableOn (by norm_num) t htc).differentiableAt htn
  have hsc : ContinuousAt (GKArcSheet38 a) t := a.2.2.2.1.continuousAt htn
  have hsn := arc_sheet_ne_zero φ m a t ht
  have he : (fun u => GKArcSheet38 a u ^ 2) =ᶠ[nhds t]
      perChar φ.1 ∘ GKArcCurve38 a := by
    filter_upwards [htn] with u hu
    exact a.2.2.2.2.1 u hu
  exact sheet_primitive_hasDerivAt hγd.hasDerivAt
    ((analyticOnNhd_perChar_z φ.1) _ (mem_univ _)).differentiableAt.hasDerivAt
    (hR _ (a.2.2.2.2.2.1 t htc)).differentiableAt.hasDerivAt
    hsc hsn he (hODE _ (a.2.2.2.2.2.2 t ht))

theorem arc_integral_of_prim (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (a : GKRootedC1Arc38 φ m) (u v : ℝ)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hi : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume u v) :
    (∫ t in u..v, GKRootedArcIntegrand38 n m F φ a t) =
      arcPrim φ m R a v - arcPrim φ m R a u :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    ((arcPrim_continuousOn φ m R hR a).mono
      (fun t ht => ⟨hu.trans ht.1, ht.2.trans hv⟩))
    (fun t ht => arcPrim_hasDerivAt n m F φ R hR hODE a t
      ⟨hu.trans_lt ht.1, ht.2.trans_le hv⟩) hi

theorem arcPrim_join (φ : GKPotential38) (m : ℤ) (R : ℂ → ℂ)
    (a b : GKRootedC1Arc38 φ m) (h : GKRootedArcJoin38 φ m a b) :
    arcPrim φ m R a 1 = arcPrim φ m R b 0 := by
  simp only [arcPrim, h.1, h.2.1]

theorem middle_prim_telescopes
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (arcs : List (GKRootedC1Arc38 φ m)) :
    ∀ (a b : GKRootedC1Arc38 φ m),
      GKRootedArcChain38 φ m (a :: (arcs ++ [b])) →
      (∀ d ∈ arcs, (∫ t in (0 : ℝ)..1, GKRootedArcIntegrand38 n m F φ d t) =
        arcPrim φ m R d 1 - arcPrim φ m R d 0) →
      arcPrim φ m R a 1 + GKPathMiddleIntegral38 n m F φ arcs = arcPrim φ m R b 0 := by
  induction arcs with
  | nil =>
      intro a b hc hi
      simpa only [GKPathMiddleIntegral38, add_zero] using arcPrim_join φ m R a b hc.1
  | cons d tail ih =>
      intro a b hc hi
      have hjoin := arcPrim_join φ m R a d hc.1
      have hd := hi d List.mem_cons_self
      have htail := ih d b hc.2 (fun e he => hi e (List.mem_cons_of_mem _ he))
      calc
        arcPrim φ m R a 1 + GKPathMiddleIntegral38 n m F φ (d :: tail)
            = arcPrim φ m R d 1 + GKPathMiddleIntegral38 n m F φ tail := by
                  rw [GKPathMiddleIntegral38, hjoin, hd]
                  ring
        _ = arcPrim φ m R b 0 := htail

/-- The hypothesis shape of a truncated rooted path (compact integrability). -/
def ChainInt (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m) : Prop :=
  ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
    IntervalIntegrable (GKRootedArcIntegrand38 n m F φ f) volume ε 1 ∧
    (∀ a ∈ mids, IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 1) ∧
    IntervalIntegrable (GKRootedArcIntegrand38 n m F φ l) volume 0 (1 - η)

/-- The truncated chain integral. -/
def ChainTrunc (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m)
    (q : ℝ × ℝ) : ℂ :=
  (∫ t in q.1..(1 : ℝ), GKRootedArcIntegrand38 n m F φ f t) +
    GKPathMiddleIntegral38 n m F φ mids +
    (∫ t in (0 : ℝ)..(1 - q.2), GKRootedArcIntegrand38 n m F φ l t)

theorem trunc_prim (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m)
    (hchain : GKRootedArcChain38 φ m (f :: (mids ++ [l])))
    (hint : ChainInt n m F φ f mids l) (q : ℝ × ℝ) (hq : 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1) :
    ChainTrunc n m F φ f mids l q = arcPrim φ m R l (1 - q.2) - arcPrim φ m R f q.1 := by
  obtain ⟨hif, him, hil⟩ := hint q.1 q.2 hq.1 hq.2.1 hq.2.2
  have hf := arc_integral_of_prim n m F φ R hR hODE f q.1 1 hq.1.le
    (by linarith [hq.2.1, hq.2.2]) le_rfl hif
  have hl := arc_integral_of_prim n m F φ R hR hODE l 0 (1 - q.2) le_rfl
    (by linarith [hq.2.1, hq.2.2]) (by linarith [hq.2.1]) hil
  have hm := middle_prim_telescopes n m F φ R mids f l hchain
    (fun d hd => arc_integral_of_prim n m F φ R hR hODE d 0 1
      le_rfl zero_le_one le_rfl (him d hd))
  unfold ChainTrunc
  rw [hf, hl]
  calc
    _ = (arcPrim φ m R l (1 - q.2) - arcPrim φ m R f q.1) +
        (arcPrim φ m R f 1 + GKPathMiddleIntegral38 n m F φ mids -
          arcPrim φ m R l 0) := by ring
    _ = _ := by rw [hm, sub_self, add_zero]

/-- The filter of truncation parameters. -/
abbrev TruncFilter : Filter (ℝ × ℝ) :=
  nhdsWithin ((0 : ℝ), (0 : ℝ)) {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}

theorem trunc_fst_tendsto : Tendsto (fun q : ℝ × ℝ => q.1) TruncFilter (nhdsWithin 0 (Icc (0 : ℝ) 1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact ⟨hq.1.le, by linarith [hq.2.1, hq.2.2]⟩

theorem trunc_snd_tendsto : Tendsto (fun q : ℝ × ℝ => 1 - q.2) TruncFilter
    (nhdsWithin 1 (Icc (0 : ℝ) 1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hsnd : Tendsto (fun q : ℝ × ℝ => q.2) TruncFilter (nhds (0 : ℝ)) :=
      continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_zero] using (tendsto_const_nhds.sub hsnd :
      Tendsto (fun q : ℝ × ℝ => (1 : ℝ) - q.2) TruncFilter (nhds (1 - 0)))
  · filter_upwards [self_mem_nhdsWithin] with q hq
    constructor <;> linarith [hq.1, hq.2.1, hq.2.2]

/-- Off-diagonal limit: any improper chain integral equals the sheet value times the coefficient at the end. -/
theorem offdiag_limit (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m)
    (hchain : GKRootedArcChain38 φ m (f :: (mids ++ [l])))
    (hint : ChainInt n m F φ f mids l) (β : ℂ)
    (hlim : Tendsto (ChainTrunc n m F φ f mids l) TruncFilter (nhds β))
    (hstart : GKArcSheet38 f 0 = 0) :
    β = GKArcSheet38 l 1 * R (GKArcCurve38 l 1) := by
  letI : NeBot TruncFilter := rawBetaImproperApproachNeBot38
  have hgf := (arcPrim_continuousOn φ m R hR f 0 ⟨le_rfl, zero_le_one⟩).tendsto.comp trunc_fst_tendsto
  have hgl := (arcPrim_continuousOn φ m R hR l 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp trunc_snd_tendsto
  have hlim' := hgl.sub hgf
  have h0 : arcPrim φ m R f 0 = 0 := by simp only [arcPrim, hstart, zero_mul]
  rw [h0, sub_zero] at hlim'
  have hu : Tendsto (ChainTrunc n m F φ f mids l) TruncFilter
      (nhds (arcPrim φ m R l 1)) := by
    apply hlim'.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (trunc_prim n m F φ R hR hODE f mids l hchain hint q hq).symm
  exact tendsto_nhds_unique hlim hu


/-- A rooted chain with its endpoint data and a genuine improper limit `β`. -/
def ChainLim (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m)
    (c β : ℂ) : Prop :=
  GKRootedArcChain38 φ m (f :: (mids ++ [l])) ∧ ChainInt n m F φ f mids l ∧
    GKArcCurve38 f 0 = c ∧ GKArcCurve38 l 1 = muSeq φ.1 m ∧
    (muSeq φ.1 m ≠ lamMinus φ.1 m → muSeq φ.1 m ≠ lamPlus φ.1 m →
      GKArcSheet38 l 1 = antiDiscrim φ.1 (muSeq φ.1 m)) ∧
    Tendsto (ChainTrunc n m F φ f mids l) TruncFilter (nhds β)

theorem start_sheet_zero (φ : GKPotential38) (m : ℤ) (f : GKRootedC1Arc38 φ m) (c : ℂ)
    (hc : perChar φ.1 c = 0) (hstart : GKArcCurve38 f 0 = c) : GKArcSheet38 f 0 = 0 := by
  have hsq : GKArcSheet38 f 0 ^ 2 = perChar φ.1 (GKArcCurve38 f 0) :=
    f.2.2.2.2.1 0 ⟨le_rfl, zero_le_one⟩
  apply sq_eq_zero_iff.mp
  rw [hsq, hstart, hc]

theorem lamPlus_perChar_zero (φ : GKPotential38) (m : ℤ) : perChar φ.1 (lamPlus φ.1 m) = 0 :=
  (lamSeq_enumeration38 φ.1).1 (2 * m + 1)

theorem end_sheet_eq (φ : GKPotential38) (m : ℤ) (l : GKRootedC1Arc38 φ m)
    (hend : GKArcCurve38 l 1 = muSeq φ.1 m)
    (hterm : muSeq φ.1 m ≠ lamMinus φ.1 m → muSeq φ.1 m ≠ lamPlus φ.1 m →
      GKArcSheet38 l 1 = antiDiscrim φ.1 (muSeq φ.1 m)) :
    GKArcSheet38 l 1 = antiDiscrim φ.1 (muSeq φ.1 m) := by
  by_cases ht : muSeq φ.1 m = lamMinus φ.1 m ∨ muSeq φ.1 m = lamPlus φ.1 m
  · have hball : muSeq φ.1 m ∈ ball (discC φ.1 m) (discR φ.1 m) := by
      rw [← hend]
      exact l.2.2.2.2.2.1 1 ⟨zero_le_one, le_rfl⟩
    have hPzero := (rawBetaPerCharZeroInDiscIff38 φ m (muSeq φ.1 m) hball).mpr ht
    have hs0 : GKArcSheet38 l 1 = 0 := by
      apply sq_eq_zero_iff.mp
      have hsq : GKArcSheet38 l 1 ^ 2 = perChar φ.1 (GKArcCurve38 l 1) :=
        l.2.2.2.2.1 1 ⟨zero_le_one, le_rfl⟩
      rw [hsq, hend, hPzero]
    have hδ0 : antiDiscrim φ.1 (muSeq φ.1 m) = 0 :=
      sq_eq_zero_iff.mp ((rawBetaDirichletTerminalSquare38 φ m).trans hPzero)
    rw [hs0, hδ0]
  · exact hterm (fun h => ht (Or.inl h)) (fun h => ht (Or.inr h))

/-- Off-diagonal: the improper value of a chain starting at a tip is `antiDiscrim(mu) * R(mu)`. -/
theorem offdiag_of_chainLim (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m)
    (c β : ℂ) (hc : perChar φ.1 c = 0) (h : ChainLim n m F φ f mids l c β) :
    β = antiDiscrim φ.1 (muSeq φ.1 m) * R (muSeq φ.1 m) := by
  obtain ⟨hchain, hint, hstart, hend, hterm, hlim⟩ := h
  have := offdiag_limit n m F φ R hR hODE f mids l hchain hint β hlim
    (start_sheet_zero φ m f c hc hstart)
  rw [this, end_sheet_eq φ m l hend hterm, hend]

/-! ### Diagonal exponential model -/

theorem middle_model_transport
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (eps : ℂ) (R : ℂ → ℂ)
    (arcs : List (GKRootedC1Arc38 phi n)) :
    ∀ (a b : GKRootedC1Arc38 phi n),
      GKRootedArcChain38 phi n (a :: (arcs ++ [b])) →
      (∀ d ∈ arcs, gk16ArcExponentialModel38 phi n eps R d 1 =
        gk16ArcExponentialModel38 phi n eps R d 0 *
          Complex.exp ((-eps*Complex.I)*
            (∫ t in (0 : ℝ)..1, GKRootedArcIntegrand38 n n F phi d t))) →
      gk16ArcExponentialModel38 phi n eps R b 0 =
        gk16ArcExponentialModel38 phi n eps R a 1 *
          Complex.exp ((-eps*Complex.I)*GKPathMiddleIntegral38 n n F phi arcs) := by
  induction arcs with
  | nil =>
      intro a b hc hi
      simpa only [GKPathMiddleIntegral38,mul_zero,Complex.exp_zero,mul_one] using
        (gk16_arc_model_join38 phi n eps R a b hc.1).symm
  | cons d tail ih =>
      intro a b hc hi
      have hjoin := gk16_arc_model_join38 phi n eps R a d hc.1
      have hd := hi d List.mem_cons_self
      have htail := ih d b hc.2 (fun e he => hi e (List.mem_cons_of_mem _ he))
      rw [htail,hd,← hjoin,GKPathMiddleIntegral38,mul_assoc,← Complex.exp_add]
      congr 2
      ring

theorem diag_trunc_transport
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (s : Lib.L2Seq)
    (hnum : p6PsiNumerator38 n (F n) phi.1 = p2FullNumerator38 n s)
    (hperiod : abelianPeriod38 n phi.1
      (p6PsiNumerator38 n (F n) phi.1) = 2*(Real.pi : ℂ))
    (eps : ℂ) (heps : eps^2 = 1)
    (f : GKRootedC1Arc38 phi n) (mids : List (GKRootedC1Arc38 phi n)) (l : GKRootedC1Arc38 phi n)
    (hchain : GKRootedArcChain38 phi n (f :: (mids ++ [l])))
    (hint : ChainInt n n F phi f mids l) (q : ℝ × ℝ)
    (hq : 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1) :
    let R := gk16OwnCorrectionCoefficient38 phi.1 n s
      (discC phi.1 n) (discR phi.1 n)
    gk16ArcExponentialModel38 phi n eps R l (1-q.2) =
      gk16ArcExponentialModel38 phi n eps R f q.1 *
        Complex.exp ((-eps*Complex.I)*ChainTrunc n n F phi f mids l q) := by
  let R := gk16OwnCorrectionCoefficient38 phi.1 n s
    (discC phi.1 n) (discR phi.1 n)
  obtain ⟨hif,him,hil⟩ := hint q.1 q.2 hq.1 hq.2.1 hq.2.2
  have hf := gk16_diagonal_arc_transport38 n F phi s hnum hperiod eps heps
    f q.1 1 hq.1.le (by linarith [hq.2.1, hq.2.2]) le_rfl hif
  have hl := gk16_diagonal_arc_transport38 n F phi s hnum hperiod eps heps
    l 0 (1-q.2) le_rfl (by linarith [hq.2.1, hq.2.2]) (by linarith [hq.2.1]) hil
  have hm := middle_model_transport n F phi eps R mids f l hchain
    (fun d hd => gk16_diagonal_arc_transport38 n F phi s hnum hperiod eps heps
      d 0 1 le_rfl zero_le_one le_rfl (him d hd))
  change gk16ArcExponentialModel38 phi n eps R l (1-q.2) = _
  rw [hl,hm,hf,ChainTrunc,mul_assoc,mul_assoc,
    ← Complex.exp_add,← Complex.exp_add]
  congr 2
  ring

theorem diag_limit
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (s : Lib.L2Seq)
    (hnum : p6PsiNumerator38 n (F n) phi.1 = p2FullNumerator38 n s)
    (hperiod : abelianPeriod38 n phi.1
      (p6PsiNumerator38 n (F n) phi.1) = 2*(Real.pi : ℂ))
    (eps : ℂ) (heps : eps^2 = 1)
    (f : GKRootedC1Arc38 phi n) (mids : List (GKRootedC1Arc38 phi n)) (l : GKRootedC1Arc38 phi n)
    (hchain : GKRootedArcChain38 phi n (f :: (mids ++ [l])))
    (hint : ChainInt n n F phi f mids l) (β : ℂ)
    (hlim : Tendsto (ChainTrunc n n F phi f mids l) TruncFilter (nhds β)) :
    let R := gk16OwnCorrectionCoefficient38 phi.1 n s
      (discC phi.1 n) (discR phi.1 n)
    gk16ArcExponentialModel38 phi n eps R l 1 =
      gk16ArcExponentialModel38 phi n eps R f 0 * Complex.exp ((-eps*Complex.I)*β) := by
  intro R
  have hR := gk16_own_correction_coefficient38 phi.1 phi.2
    (discC phi.1) (discR phi.1) (isolating_family38 phi.1 phi.2) n s
    (by simpa only [hnum] using hperiod)
  letI : NeBot TruncFilter := rawBetaImproperApproachNeBot38
  have hgfirst := (gk16_arc_model_continuous38 phi n eps R hR.1 f
    0 ⟨le_rfl,zero_le_one⟩).tendsto.comp trunc_fst_tendsto
  have hglast := (gk16_arc_model_continuous38 phi n eps R hR.1 l
    1 ⟨zero_le_one,le_rfl⟩).tendsto.comp trunc_snd_tendsto
  have hscaled : Tendsto
      (fun q : ℝ × ℝ => (-eps*Complex.I)*ChainTrunc n n F phi f mids l q)
      TruncFilter (nhds ((-eps*Complex.I)*β)) := tendsto_const_nhds.mul hlim
  have hexp := hgfirst.mul hscaled.cexp
  apply tendsto_nhds_unique hglast
  apply hexp.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (diag_trunc_transport n F phi s hnum hperiod eps heps f mids l hchain hint q hq).symm

theorem diag_model_start (phi : GKPotential38) (n : ℤ) (eps : ℂ) (R : ℂ → ℂ)
    (f : GKRootedC1Arc38 phi n) (c : ℂ) (hs : GKArcSheet38 f 0 = 0)
    (hc : GKArcCurve38 f 0 = c) :
    gk16ArcExponentialModel38 phi n eps R f 0 = 2*((lamMinus phi.1 n+lamPlus phi.1 n)/2 - c) := by
  simp only [gk16ArcExponentialModel38,gk16ArcNormalizedSheet38,hs,hc,zero_div,mul_zero,zero_mul,
    Complex.exp_zero,sub_zero,mul_one]

theorem diag_model_end (phi : GKPotential38) (n : ℤ) (eps : ℂ) (R : ℂ → ℂ)
    (l : GKRootedC1Arc38 phi n) (hend : GKArcCurve38 l 1 = muSeq phi.1 n)
    (hs : GKArcSheet38 l 1 = antiDiscrim phi.1 (muSeq phi.1 n)) :
    gk16ArcExponentialModel38 phi n eps R l 1 =
      (2*((lamMinus phi.1 n+lamPlus phi.1 n)/2-muSeq phi.1 n)-
          2*eps*gk16TerminalRoot38 n phi.1) *
        Complex.exp (eps*gk16TerminalRoot38 n phi.1*R (muSeq phi.1 n)) := by
  simp only [gk16ArcExponentialModel38,gk16ArcNormalizedSheet38,gk16OwnSheetDenominator38,
    gk16TerminalRoot38,hs,hend]


theorem antiDiscrim_tip_zero (φ : GKPotential38) (m : ℤ)
    (ht : muSeq φ.1 m = lamMinus φ.1 m ∨ muSeq φ.1 m = lamPlus φ.1 m) :
    antiDiscrim φ.1 (muSeq φ.1 m) = 0 := by
  have hP : perChar φ.1 (muSeq φ.1 m) = 0 := by
    rcases ht with h | h
    · rw [h]; exact rawBetaPerCharLowerTipZero38 φ m
    · rw [h]; exact lamPlus_perChar_zero φ m
  exact sq_eq_zero_iff.mp ((rawBetaDirichletTerminalSquare38 φ m).trans hP)

/-- Off-diagonal: lower-start and upper-start chains with the same terminal data have equal improper values. -/
theorem offdiag_two_chains (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (f₁ : GKRootedC1Arc38 φ m) (mids₁ : List (GKRootedC1Arc38 φ m)) (l₁ : GKRootedC1Arc38 φ m)
    (f₂ : GKRootedC1Arc38 φ m) (mids₂ : List (GKRootedC1Arc38 φ m)) (l₂ : GKRootedC1Arc38 φ m)
    (a b : ℂ) (h₁ : ChainLim n m F φ f₁ mids₁ l₁ (lamMinus φ.1 m) a)
    (h₂ : ChainLim n m F φ f₂ mids₂ l₂ (lamPlus φ.1 m) b) : a = b := by
  rw [offdiag_of_chainLim n m F φ R hR hODE f₁ mids₁ l₁ _ a (rawBetaPerCharLowerTipZero38 φ m) h₁,
    offdiag_of_chainLim n m F φ R hR hODE f₂ mids₂ l₂ _ b (lamPlus_perChar_zero φ m) h₂]

/-- Diagonal: lower-start and upper-start chains with the same terminal data differ by `pi` modulo `2 pi`. -/
theorem diag_two_chains (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (s : Lib.L2Seq)
    (hnum : p6PsiNumerator38 n (F n) φ.1 = p2FullNumerator38 n s)
    (hperiod : abelianPeriod38 n φ.1 (p6PsiNumerator38 n (F n) φ.1) = 2*(Real.pi : ℂ))
    (hgap : lamMinus φ.1 n ≠ lamPlus φ.1 n)
    (f₁ : GKRootedC1Arc38 φ n) (mids₁ : List (GKRootedC1Arc38 φ n)) (l₁ : GKRootedC1Arc38 φ n)
    (f₂ : GKRootedC1Arc38 φ n) (mids₂ : List (GKRootedC1Arc38 φ n)) (l₂ : GKRootedC1Arc38 φ n)
    (a b : ℂ) (h₁ : ChainLim n n F φ f₁ mids₁ l₁ (lamMinus φ.1 n) a)
    (h₂ : ChainLim n n F φ f₂ mids₂ l₂ (lamPlus φ.1 n) b) :
    ∃ k : ℤ, a - b = (Real.pi : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
  obtain ⟨hch₁, hint₁, hst₁, hen₁, hte₁, hlim₁⟩ := h₁
  obtain ⟨hch₂, hint₂, hst₂, hen₂, hte₂, hlim₂⟩ := h₂
  have e₁ := diag_limit n F φ s hnum hperiod (-1) (by norm_num) f₁ mids₁ l₁ hch₁ hint₁ a hlim₁
  have e₂ := diag_limit n F φ s hnum hperiod (-1) (by norm_num) f₂ mids₂ l₂ hch₂ hint₂ b hlim₂
  simp only at e₁ e₂
  rw [diag_model_end φ n (-1) _ l₁ hen₁ (end_sheet_eq φ n l₁ hen₁ hte₁),
    diag_model_start φ n (-1) _ f₁ _ (start_sheet_zero φ n f₁ _ (rawBetaPerCharLowerTipZero38 φ n) hst₁) hst₁]
    at e₁
  rw [diag_model_end φ n (-1) _ l₂ hen₂ (end_sheet_eq φ n l₂ hen₂ hte₂),
    diag_model_start φ n (-1) _ f₂ _ (start_sheet_zero φ n f₂ _ (lamPlus_perChar_zero φ n) hst₂) hst₂]
    at e₂
  have hI : (-(-1 : ℂ) * Complex.I) = Complex.I := by ring
  rw [hI] at e₁ e₂
  have hgap' : lamPlus φ.1 n - lamMinus φ.1 n ≠ 0 := sub_ne_zero.mpr hgap.symm
  have hE : (lamPlus φ.1 n - lamMinus φ.1 n) * Complex.exp (Complex.I * a) =
      -(lamPlus φ.1 n - lamMinus φ.1 n) * Complex.exp (Complex.I * b) := by
    linear_combination e₂ - e₁
  have hexp : Complex.exp (Complex.I * a) = -Complex.exp (Complex.I * b) := by
    apply mul_left_cancel₀ hgap'
    linear_combination hE
  have hone : Complex.exp (Complex.I * (a - b - (Real.pi : ℂ))) = 1 := by
    have h1 : Complex.exp (Complex.I * (a - b - (Real.pi : ℂ))) =
        Complex.exp (Complex.I * a) * Complex.exp (-(Complex.I * b)) *
          Complex.exp (-((Real.pi : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    have hb : Complex.exp (Complex.I * b) * Complex.exp (-(Complex.I * b)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hpi : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [h1, hexp, hpi]
    linear_combination hb
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hone
  refine ⟨k, ?_⟩
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  apply mul_left_cancel₀ hI0
  linear_combination hk

end
end G3005C6
end NlsGge.GKDefinitionDesign
