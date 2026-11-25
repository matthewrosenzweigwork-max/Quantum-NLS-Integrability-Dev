                                                                                                                                                                                                 
                                                                                                                                              
                                                                                                                                               
                                                                                                                                          
                                                                                                                                          
                                                                                                                                  
import Mathlib

set_option autoImplicit false

                                                                                     
                                                                                                      
                                                                                                            
                                                                                         
                                                                                                 
                                                                                                                   
                                                                                                        
                                                                                          

open Set Metric MeasureTheory Filter
open scoped Topology Interval

namespace NlsGge.GK38.Lib.SlitContours
noncomputable section

                                                                                                                     
-- Replace by `import` of the shared SlitContours library once landed.
section ContourDefsBlock
open scoped unitInterval

def complexForm (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.mul ℂ ℂ (f z)

structure TimePartition where
  n : ℕ
  cut : Fin (n + 1) → I
  first : cut 0 = 0
  last : cut (Fin.last n) = 1
  strict : StrictMono cut

def PiecewiseC1 {a b : ℂ} (γ : Path a b) : Prop :=
  ∃ P : TimePartition, ∀ i : Fin P.n,
    ContDiffOn ℝ 1
      (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
      (Icc (0 : ℝ) 1)

def Admissible {a b : ℂ} (U : Set ℂ) (γ : Path a b) : Prop :=
  PiecewiseC1 γ ∧ range γ ⊆ U

def indexIntegral {a : ℂ} (γ : Path a a) (p : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    curveIntegral (complexForm (fun z => (z - p)⁻¹)) γ

def windingNumber {a : ℂ} (γ : Path a a) (p : ℂ) : ℤ :=
  ⌊(indexIntegral γ p).re⌋

def edgeIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  curveIntegral (complexForm f) (Path.segment a b)

def cellImage (H : C(I × I, ℂ)) (P Q : TimePartition)
    (i : Fin P.n) (j : Fin Q.n) : Set ℂ :=
  H '' (Icc (P.cut i.castSucc) (P.cut i.succ) ×ˢ
    Icc (Q.cut j.castSucc) (Q.cut j.succ))

def cellBoundary (f : ℂ → ℂ) (H : C(I × I, ℂ))
    (P Q : TimePartition) (i : Fin P.n) (j : Fin Q.n) : ℂ :=
  edgeIntegral f (H (P.cut i.castSucc, Q.cut j.castSucc))
    (H (P.cut i.succ, Q.cut j.castSucc)) +
  edgeIntegral f (H (P.cut i.succ, Q.cut j.castSucc))
    (H (P.cut i.succ, Q.cut j.succ)) -
  edgeIntegral f (H (P.cut i.castSucc, Q.cut j.succ))
    (H (P.cut i.succ, Q.cut j.succ)) -
  edgeIntegral f (H (P.cut i.castSucc, Q.cut j.castSucc))
    (H (P.cut i.castSucc, Q.cut j.succ))

def gridBoundary (f : ℂ → ℂ) (H : C(I × I, ℂ))
    (P Q : TimePartition) : ℂ :=
  (∑ i : Fin P.n, edgeIntegral f
    (H (P.cut i.castSucc, 0)) (H (P.cut i.succ, 0))) +
  (∑ j : Fin Q.n, edgeIntegral f
    (H (1, Q.cut j.castSucc)) (H (1, Q.cut j.succ))) -
  (∑ i : Fin P.n, edgeIntegral f
    (H (P.cut i.castSucc, 1)) (H (P.cut i.succ, 1))) -
  (∑ j : Fin Q.n, edgeIntegral f
    (H (0, Q.cut j.castSucc)) (H (0, Q.cut j.succ)))

def HasEndpointBound (f : ℂ → ℂ) (U : Set ℂ) (a : ℂ) : Prop :=
  ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
    ∀ z ∈ U, 0 < dist z a → dist z a < δ →
      ‖f z‖ ≤ C / Real.sqrt (dist z a)

end ContourDefsBlock
-- END PASTED SHARED LIBRARY BLOCK: CONTOUR_DEFS_GK38

                                                                                                                           
section CircleAdapterBlock
open scoped unitInterval

/-- The positive circle loop of 79.05 (design LIB-079 shared definitions). -/
def circleLoop (c : ℂ) (r : ℝ) : Path (c + r) (c + r) where
  toFun t := c + (r : ℂ) *
    ((Real.cos (2 * Real.pi * (t : ℝ)) : ℂ) +
      Complex.I * (Real.sin (2 * Real.pi * (t : ℝ)) : ℂ))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- Leaf 79.05-aux: the cosine/sine form of `circleMap`. -/
theorem circleMap_eq_cos_sin (c : ℂ) (r : ℝ) (θ : ℝ) :
    circleMap c r θ = c + (r : ℂ) *
      ((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) := by
  simp only [circleMap]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem circleLoop_extend_eq (c : ℂ) (r : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (circleLoop c r).extend t = circleMap c r (2 * Real.pi * t) := by
  have e : (circleLoop c r).extend t = circleLoop c r ⟨t, ht⟩ :=
    Path.extend_extends' _ ⟨t, ht⟩
  rw [e, circleMap_eq_cos_sin]
  rfl

theorem circleLoop_deriv_extend (c : ℂ) (r : ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    deriv (circleLoop c r).extend t =
      (2 * Real.pi : ℂ) * (circleMap 0 r (2 * Real.pi * t) * Complex.I) := by
  have hev : (circleLoop c r).extend =ᶠ[𝓝 t]
      fun s : ℝ => circleMap c r (2 * Real.pi * s) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact circleLoop_extend_eq c r (Ioo_subset_Icc_self hs)
  rw [hev.deriv_eq]
  have hD : HasDerivAt (fun s : ℝ => circleMap c r (2 * Real.pi * s))
      ((2 * Real.pi * 1 : ℝ) • (circleMap 0 r (2 * Real.pi * t) * Complex.I)) t :=
    (hasDerivAt_circleMap c r (2 * Real.pi * t)).scomp t
      ((hasDerivAt_id t).const_mul (2 * Real.pi))
  rw [hD.deriv, Complex.real_smul]
  push_cast
  ring

/-- Leaf 79.05: the circle loop integral is the circle integral (routine normalization). -/
theorem curveIntegral_circleLoop (f : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hf : ContinuousOn f (sphere c r)) :
    curveIntegral (complexForm f) (circleLoop c r) =
      circleIntegral f c r := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [complexForm, ContinuousLinearMap.mul_apply']
  have hint : ∫ t in (0 : ℝ)..1, f ((circleLoop c r).extend t) * deriv (circleLoop c r).extend t =
      ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℂ) *
        (f (circleMap c r (2 * Real.pi * t)) * (circleMap 0 r (2 * Real.pi * t) * Complex.I)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with x hx1 hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    rw [circleLoop_extend_eq c r (Ioo_subset_Icc_self hxI), circleLoop_deriv_extend c r hxI]
    ring
  have hc2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (f := fun θ : ℝ => f (circleMap c r θ) * (circleMap 0 r θ * Complex.I)) hc2
  simp only [mul_zero, mul_one] at hcomp
  have hR : circleIntegral f c r =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap c r θ) * (circleMap 0 r θ * Complex.I) := by
    unfold circleIntegral
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [deriv_circleMap, smul_eq_mul]
    ring
  rw [hint, intervalIntegral.integral_const_mul, hcomp, hR, Complex.real_smul]
  push_cast
  field_simp
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  ring

end CircleAdapterBlock
-- END PASTED SHARED LIBRARY BLOCK: 79.05 circle adapter

                                                                                                                         
section RemovabilityBlock
open scoped unitInterval

/-- Leaf 79.18: a square-root endpoint bound makes a punctured-disc holomorphic function removable. -/
theorem square_root_bound_removable (f : ℂ → ℂ) (a : ℂ)
    (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball a r \ {a}))
    (hbound : HasEndpointBound f (ball a r \ {a}) a) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball a r) ∧
      EqOn F f (ball a r \ {a}) := by
  obtain ⟨C, δ, hC, hδ, hB⟩ := hbound
  have hball : ∀ᶠ z in 𝓝 a, dist z a < min δ r :=
    Metric.eventually_nhds_iff.2 ⟨min δ r, lt_min hδ hr, fun z hz => hz⟩
  have hbd : ∀ᶠ z in 𝓝[≠] a, ‖f z * (z - a)‖ ≤ C * Real.sqrt (dist z a) := by
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hzne
    have hza : z ≠ a := hzne
    have hd0 : 0 < dist z a := dist_pos.2 hza
    have hdδ : dist z a < δ := lt_of_lt_of_le hz (min_le_left _ _)
    have hdr : dist z a < r := lt_of_lt_of_le hz (min_le_right _ _)
    have hfz := hB z ⟨by rw [mem_ball]; exact hdr, hza⟩ hd0 hdδ
    have hsd : 0 < Real.sqrt (dist z a) := Real.sqrt_pos.2 hd0
    rw [norm_mul, ← dist_eq_norm]
    calc ‖f z‖ * dist z a ≤ C / Real.sqrt (dist z a) * dist z a :=
          mul_le_mul_of_nonneg_right hfz hd0.le
      _ = C * Real.sqrt (dist z a) := by
          rw [div_mul_eq_mul_div, div_eq_iff hsd.ne', mul_assoc, Real.mul_self_sqrt hd0.le]
  have hlim : Tendsto (fun z : ℂ => C * Real.sqrt (dist z a)) (𝓝[≠] a) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => C * Real.sqrt (dist z a)) :=
      continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.dist continuous_const))
    have h := (hc.tendsto a).mono_left (nhdsWithin_le_nhds (s := ({a}ᶜ : Set ℂ)))
    simpa using h
  have hT : Tendsto (fun z => f z * (z - a)) (𝓝[≠] a) (𝓝 0) :=
    squeeze_zero_norm' hbd hlim
  have h2 : Tendsto (fun z => f a * (z - a)) (𝓝[≠] a) (𝓝 0) := by
    have hc2 : Continuous (fun z : ℂ => f a * (z - a)) :=
      continuous_const.mul (continuous_id.sub continuous_const)
    have h := (hc2.tendsto a).mono_left (nhdsWithin_le_nhds (s := ({a}ᶜ : Set ℂ)))
    have h' := h
    simpa using h'
  have hgf : ∀ᶠ z in 𝓝[≠] a, (z - a)⁻¹ = 0 → f z - f a = 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz h
    exact absurd h (inv_ne_zero (sub_ne_zero.2 hz))
  have hmain : Tendsto (fun z => (f z - f a) / (z - a)⁻¹) (𝓝[≠] a) (𝓝 0) := by
    have hsub := hT.sub h2
    rw [show ((0 : ℂ) - 0) = 0 from sub_zero 0] at hsub
    refine hsub.congr' ?_
    filter_upwards with z
    simp only [div_inv_eq_mul]
    ring
  have hls : (fun z => f z - f a) =o[𝓝[≠] a] fun z => (z - a)⁻¹ :=
    (Asymptotics.isLittleO_iff_tendsto' hgf).2 hmain
  have hdiff := Complex.differentiableOn_update_limUnder_of_isLittleO
    (Metric.ball_mem_nhds a hr) hf hls
  refine ⟨Function.update f a (limUnder (𝓝[≠] a) f), hdiff, fun z hz => ?_⟩
  exact Function.update_of_ne hz.2 _ f

end RemovabilityBlock
-- END PASTED SHARED LIBRARY BLOCK: 79.18 removability

-- LIB-015 proper begins here (opens below are unitInterval-free).


structure RealSlits (n : ℕ) where
  a : Fin n → ℝ
  b : Fin n → ℝ
  le : ∀ i, a i ≤ b i
  disjoint : ∀ i j, i ≠ j →
    b i < a j ∨ b j < a i

def RealSlits.carrier {n : ℕ} (S : RealSlits n) : Set ℂ :=
  ⋃ i : Fin n, Complex.ofReal '' Icc (S.a i) (S.b i)

def HasL1Trace (F : ℂ → ℂ) (v : ℝ → ℂ)
    (a b σ : ℝ) : Prop :=
  IntervalIntegrable v volume a b ∧
  (∀ ε : ℝ, 0 < ε →
    IntervalIntegrable
      (fun t : ℝ => F ((t : ℂ) + (σ * ε : ℝ) * Complex.I))
      volume a b) ∧
  Tendsto
    (fun ε : ℝ => ∫ t : ℝ in a..b,
      ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t‖)
    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))

def HasLocalUniformTrace (F : ℂ → ℂ) (v : ℝ → ℂ)
    (a b σ : ℝ) : Prop :=
  ∀ c d : ℝ, a < c → c ≤ d → d < b →
    TendstoUniformlyOn
      (fun ε : ℝ => fun t : ℝ =>
        F ((t : ℂ) + (σ * ε : ℝ) * Complex.I))
      v (𝓝[>] (0 : ℝ)) (Icc c d)

def DecaysAtInfinity (F : ℂ → ℂ) : Prop :=
  ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖F z‖ ≤ C / ‖z‖

structure SlitHolomorphicData {n : ℕ} (S : RealSlits n) where
  F : ℂ → ℂ
  upper : Fin n → ℝ → ℂ
  lower : Fin n → ℝ → ℂ
  jump : Fin n → ℝ → ℂ
  holomorphic : DifferentiableOn ℂ F S.carrierᶜ
  upper_trace : ∀ i, HasL1Trace F (upper i) (S.a i) (S.b i) 1
  lower_trace : ∀ i, HasL1Trace F (lower i) (S.a i) (S.b i) (-1)
  jump_ae : ∀ i, ∀ᵐ t : ℝ ∂volume.restrict (Icc (S.a i) (S.b i)),
    jump i t = upper i t - lower i t
  endpoint_left : ∀ i,
    HasEndpointBound F S.carrierᶜ (S.a i : ℂ)
  endpoint_right : ∀ i,
    HasEndpointBound F S.carrierᶜ (S.b i : ℂ)
  decay : DecaysAtInfinity F

def jumpIntegral {n : ℕ} (S : RealSlits n)
    (j : Fin n → ℝ → ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin n, ∫ t : ℝ in (S.a i)..(S.b i),
    j i t / ((t : ℂ) - z)

def rectIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f ((x : ℂ) + (c : ℂ) * Complex.I)) -
  (∫ x : ℝ in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I)) +
  Complex.I *
    (∫ y : ℝ in c..d, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
  Complex.I *
    (∫ y : ℝ in c..d, f ((a : ℂ) + (y : ℂ) * Complex.I))

def leftCap (f : ℂ → ℂ) (a ε : ℝ) : ℂ :=
  (∫ t : ℝ in (a - ε)..a, f ((t : ℂ) - (ε : ℂ) * Complex.I)) -
  (∫ t : ℝ in (a - ε)..a, f ((t : ℂ) + (ε : ℂ) * Complex.I)) -
  Complex.I *
    (∫ y : ℝ in (-ε)..ε, f ((a - ε : ℝ) + (y : ℂ) * Complex.I))

def rightCap (f : ℂ → ℂ) (b ε : ℝ) : ℂ :=
  (∫ t : ℝ in b..(b + ε), f ((t : ℂ) - (ε : ℂ) * Complex.I)) -
  (∫ t : ℝ in b..(b + ε), f ((t : ℂ) + (ε : ℂ) * Complex.I)) +
  Complex.I *
    (∫ y : ℝ in (-ε)..ε, f ((b + ε : ℝ) + (y : ℂ) * Complex.I))

def collarIntegral {n : ℕ} (S : RealSlits n)
    (F : ℂ → ℂ) (z : ℂ) (ε : ℝ) : ℂ :=
  ∑ i : Fin n, rectIntegral (fun w => F w / (w - z))
    (S.a i - ε) (S.b i + ε) (-ε) ε

/-! ### 15.01 -/

theorem slits_compact_and_separated {n : ℕ} (S : RealSlits n) :
    IsCompact S.carrier ∧ IsOpen S.carrierᶜ ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j : Fin n, i ≠ j →
      S.b i + 2 * δ < S.a j ∨ S.b j + 2 * δ < S.a i := by
  have hc : IsCompact S.carrier :=
    isCompact_iUnion fun i => isCompact_Icc.image Complex.continuous_ofReal
  refine ⟨hc, hc.isClosed.isOpen_compl, ?_⟩
  let g : Fin n × Fin n → ℝ := fun p =>
    if p.1 = p.2 then 1 else
      if S.b p.1 < S.a p.2 then S.a p.2 - S.b p.1 else S.a p.1 - S.b p.2
  have hg : ∀ p, 0 < g p := by
    intro p
    by_cases h : p.1 = p.2
    · simp [g, h]
    · by_cases h2 : S.b p.1 < S.a p.2
      · simp only [g, h, h2, if_true, if_false]
        linarith
      · have h3 := (S.disjoint p.1 p.2 h).resolve_left h2
        simp only [g, h, h2, if_false]
        linarith
  rcases isEmpty_or_nonempty (Fin n × Fin n) with hE | hN
  · refine ⟨1, one_pos, fun i j _ => ?_⟩
    exact (hE.false (i, j)).elim
  · obtain ⟨p0, hp0⟩ := Finite.exists_min g
    refine ⟨g p0 / 3, by have := hg p0; positivity, fun i j hij => ?_⟩
    have hle := hp0 (i, j)
    by_cases h2 : S.b i < S.a j
    · left
      have : g (i, j) = S.a j - S.b i := by simp [g, hij, h2]
      have := hg p0
      linarith
    · right
      have h3 := (S.disjoint i j hij).resolve_left h2
      have : g (i, j) = S.a i - S.b j := by simp [g, hij, h2]
      have := hg p0
      linarith

/-! ### 15.02 -/

theorem slit_denominator_lower_bound {n : ℕ} (S : RealSlits n)
    (z : ℂ) (hz : z ∉ S.carrier) :
    ∃ d : ℝ, 0 < d ∧
      ∀ i : Fin n, ∀ t ∈ Icc (S.a i) (S.b i),
        d ≤ ‖(t : ℂ) - z‖ := by
  have hc : IsCompact S.carrier := (slits_compact_and_separated S).1
  rcases S.carrier.eq_empty_or_nonempty with hE | hN
  · refine ⟨1, one_pos, fun i t ht => ?_⟩
    have : (t : ℂ) ∈ S.carrier :=
      mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩
    rw [hE] at this
    exact this.elim
  · obtain ⟨m, hm, hmin⟩ := hc.exists_isMinOn hN
      (f := fun w : ℂ => ‖w - z‖) (by fun_prop)
    refine ⟨‖m - z‖, norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hz (h ▸ hm)), fun i t ht => ?_⟩
    have : (t : ℂ) ∈ S.carrier := mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩
    exact hmin this

/-! ### 15.03, 15.04 -/

theorem jump_intervalIntegrable {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) (i : Fin n) :
    IntervalIntegrable (D.jump i) volume (S.a i) (S.b i) := by
  have hu := (D.upper_trace i).1
  have hl := (D.lower_trace i).1
  have hsub := hu.sub hl
  have hab := S.le i
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hsub ⊢
  refine hsub.congr ?_
  have h1 := D.jump_ae i
  have h2 : ∀ᵐ t ∂(volume.restrict (Ioc (S.a i) (S.b i))),
      D.jump i t = D.upper i t - D.lower i t :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self h1
  filter_upwards [h2] with t ht
  rw [ht]

theorem inv_sub_continuousOn {n : ℕ} (S : RealSlits n)
    (z : ℂ) (hz : z ∉ S.carrier) (i : Fin n) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) - z)⁻¹) (uIcc (S.a i) (S.b i)) := by
  rw [uIcc_of_le (S.le i)]
  apply ContinuousOn.inv₀
  · fun_prop
  · intro t ht h
    apply hz
    have : (t : ℂ) = z := sub_eq_zero.mp h
    rw [← this]
    exact mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩

theorem weighted_jump_intervalIntegrable {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) (z : ℂ) (hz : z ∉ S.carrier)
    (i : Fin n) :
    IntervalIntegrable
      (fun t : ℝ => D.jump i t / ((t : ℂ) - z))
      volume (S.a i) (S.b i) := by
  have := (jump_intervalIntegrable S D i).mul_continuousOn (inv_sub_continuousOn S z hz i)
  simpa [div_eq_mul_inv] using this

/-! ### 15.10, 15.11 -/

theorem rectangle_edges_and_zero (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc c d)) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I))
      volume a b ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      volume a b ∧
    IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I))
      volume c d ∧
    IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I))
      volume c d ∧
    rectIntegral f a b c d = 0 := by
  have hcont := hf.continuousOn
  have hH : ∀ y ∈ uIcc c d, ContinuousOn (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I))
      (uIcc a b) := by
    intro y hy
    refine hcont.comp (by fun_prop) fun x hx => ?_
    exact ⟨by simpa using hx, by simpa using hy⟩
  have hV : ∀ x ∈ uIcc a b, ContinuousOn (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I))
      (uIcc c d) := by
    intro x hx
    refine hcont.comp (by fun_prop) fun y hy => ?_
    exact ⟨by simpa using hx, by simpa using hy⟩
  refine ⟨(hH c left_mem_uIcc).intervalIntegrable, (hH d right_mem_uIcc).intervalIntegrable,
    (hV a left_mem_uIcc).intervalIntegrable, (hV b right_mem_uIcc).intervalIntegrable, ?_⟩
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + (c : ℂ) * Complex.I) ((b : ℂ) + (d : ℂ) * Complex.I) (by simpa using hf)
  simpa [rectIntegral, smul_eq_mul] using h

theorem rectIntegral_horizontal_split (f : ℂ → ℂ)
    (a m b c d : ℝ)
    (h₁ : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume a m)
    (h₂ : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume m b)
    (h₃ : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume a m)
    (h₄ : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume m b) :
    rectIntegral f a b c d =
      rectIntegral f a m c d + rectIntegral f m b c d := by
  unfold rectIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ h₂,
    ← intervalIntegral.integral_add_adjacent_intervals h₃ h₄]
  ring

theorem rectIntegral_vertical_split (f : ℂ → ℂ)
    (a b c m d : ℝ)
    (h₁ : IntervalIntegrable
      (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) volume c m)
    (h₂ : IntervalIntegrable
      (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) volume m d)
    (h₃ : IntervalIntegrable
      (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume c m)
    (h₄ : IntervalIntegrable
      (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume m d) :
    rectIntegral f a b c d =
      rectIntegral f a b c m + rectIntegral f a b m d := by
  unfold rectIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ h₂,
    ← intervalIntegral.integral_add_adjacent_intervals h₃ h₄]
  ring

/-! ### 15.05 -/

theorem continuousOn_jumpIntegral {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) :
    ContinuousOn (jumpIntegral S D.jump) S.carrierᶜ := by
  intro z0 hz0
  have hz0' : z0 ∉ S.carrier := hz0
  apply ContinuousAt.continuousWithinAt
  unfold jumpIntegral
  refine tendsto_finset_sum Finset.univ fun i _ => ?_
  obtain ⟨d, hd, hdb⟩ := slit_denominator_lower_bound S z0 hz0'
  have hj := jump_intervalIntegrable S D i
  have hab := S.le i
  have hj1 : IntegrableOn (D.jump i) (Ioc (S.a i) (S.b i)) volume := by
    have := hj
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at this
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun t => ‖D.jump i t‖ * (2 / d)) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [uIoc_of_le hab]
    have hm : Measurable fun t : ℝ => ((t : ℂ) - z)⁻¹ := by fun_prop
    have := hj1.aestronglyMeasurable.mul hm.aestronglyMeasurable
    simp only [div_eq_mul_inv]
    exact this
  · have hball : Metric.ball z0 (d / 2) ∈ 𝓝 z0 := Metric.ball_mem_nhds z0 (half_pos hd)
    filter_upwards [hball] with z hz
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le hab] at ht
    have htI : t ∈ Icc (S.a i) (S.b i) := Ioc_subset_Icc_self ht
    have h1 := hdb i t htI
    have h2 : ‖z0 - z‖ < d / 2 := by simpa [dist_eq_norm, norm_sub_rev] using hz
    have h3 : d / 2 ≤ ‖(t : ℂ) - z‖ := by
      have : ‖(t : ℂ) - z0‖ ≤ ‖(t : ℂ) - z‖ + ‖z0 - z‖ := by
        calc ‖(t : ℂ) - z0‖ = ‖((t : ℂ) - z) + (z - z0)‖ := by ring_nf
          _ ≤ ‖(t : ℂ) - z‖ + ‖z - z0‖ := norm_add_le _ _
          _ = _ := by rw [norm_sub_rev z z0]
      linarith
    have h4 : 0 < ‖(t : ℂ) - z‖ := by linarith
    rw [norm_div]
    calc ‖D.jump i t‖ / ‖(t : ℂ) - z‖ ≤ ‖D.jump i t‖ / (d / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) h3
      _ = ‖D.jump i t‖ * (2 / d) := by field_simp
  · exact (hj.norm).mul_const (2 / d)
  · refine Filter.Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le hab] at ht
    have htI : t ∈ Icc (S.a i) (S.b i) := Ioc_subset_Icc_self ht
    have h1 := hdb i t htI
    have hne : (t : ℂ) - z0 ≠ 0 := by
      intro h; rw [h, norm_zero] at h1; linarith
    exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) hne

/-! ### 15.06 -/

theorem real_segment_dist_pos (a b : ℝ) (hab : a ≤ b) (z : ℂ)
    (hz : z ∉ Complex.ofReal '' Icc a b) :
    ∃ d : ℝ, 0 < d ∧ ∀ t ∈ Icc a b, d ≤ ‖(t : ℂ) - z‖ := by
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    (f := fun t : ℝ => ‖(t : ℂ) - z‖) (by fun_prop)
  refine ⟨‖(m : ℂ) - z‖, norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hz ⟨m, hm, h⟩), fun t ht => ?_⟩
  exact hmin ht

theorem weighted_trace_tendsto (F : ℂ → ℂ) (v : ℝ → ℂ)
    (a b σ : ℝ) (hab : a ≤ b) (hσ : σ = 1 ∨ σ = -1)
    (htrace : HasL1Trace F v a b σ)
    (z : ℂ) (hz : z ∉ Complex.ofReal '' Icc a b) :
    Tendsto
      (fun ε : ℝ => ∫ t : ℝ in a..b,
        F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) /
          ((t : ℂ) + (σ * ε : ℝ) * Complex.I - z))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ in a..b, v t / ((t : ℂ) - z))) := by
  obtain ⟨d, hd, hdb⟩ := real_segment_dist_pos a b hab z hz
  obtain ⟨hv, hFi, htr⟩ := htrace
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hshift : ∀ ε : ℝ, 0 < ε → ‖(((σ * ε : ℝ) : ℂ)) * Complex.I‖ = ε := by
    intro ε hε
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_mul, hσabs,
      one_mul, abs_of_pos hε]
  have hden : ∀ ε : ℝ, 0 < ε → ε ≤ d / 2 → ∀ t ∈ Icc a b,
      d / 2 ≤ ‖(t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I - z‖ := by
    intro ε hε hεd t ht
    have h1 := hdb t ht
    have h3 : ‖(t : ℂ) - z‖ ≤ ‖(t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I - z‖ + ε := by
      calc ‖(t : ℂ) - z‖
          = ‖((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I - z) - ((σ * ε : ℝ) : ℂ) * Complex.I‖ := by
            ring_nf
        _ ≤ ‖(t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I - z‖ + ‖((σ * ε : ℝ) : ℂ) * Complex.I‖ :=
            norm_sub_le _ _
        _ = _ := by rw [hshift ε hε]
    linarith
  have hKcont : ∀ ε : ℝ, 0 < ε → ε ≤ d / 2 →
      ContinuousOn (fun t : ℝ => ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I - z)⁻¹) (uIcc a b) := by
    intro ε hε hεd
    rw [uIcc_of_le hab]
    apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht h0
      have := hden ε hε hεd t ht
      rw [h0, norm_zero] at this
      linarith
  have hK0cont : ContinuousOn (fun t : ℝ => ((t : ℂ) - z)⁻¹) (uIcc a b) := by
    rw [uIcc_of_le hab]
    apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht h0
      have := hdb t ht
      rw [h0, norm_zero] at this
      linarith
  have hvK : IntervalIntegrable (fun t : ℝ => v t / ((t : ℂ) - z)) volume a b := by
    have := hv.mul_continuousOn hK0cont
    simpa [div_eq_mul_inv] using this
  set M : ℝ := ∫ t : ℝ in a..b, ‖v t‖ with hM
  set L : ℂ := ∫ t : ℝ in a..b, v t / ((t : ℂ) - z) with hL
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ‖(∫ t : ℝ in a..b, F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) /
          ((t : ℂ) + (σ * ε : ℝ) * Complex.I - z)) - L‖ ≤
        (2 / d) * (∫ t : ℝ in a..b,
          ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t‖) + (2 * ε / d ^ 2) * M := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hd)] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεd : ε ≤ d / 2 := hε.2.le
    have hFe := hFi ε hε0
    have hG : IntervalIntegrable (fun t : ℝ => F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) /
          ((t : ℂ) + (σ * ε : ℝ) * Complex.I - z)) volume a b := by
      have := hFe.mul_continuousOn (hKcont ε hε0 hεd)
      simpa [div_eq_mul_inv] using this
    rw [← intervalIntegral.integral_sub hG hvK]
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
    have hn1 : IntervalIntegrable (fun t : ℝ =>
        ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t‖) volume a b := (hFe.sub hv).norm
    have hn2 : IntervalIntegrable (fun t : ℝ => ‖v t‖) volume a b := hv.norm
    have hrhs : (2 / d) * (∫ t : ℝ in a..b, ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t‖) +
        (2 * ε / d ^ 2) * M =
        ∫ t : ℝ in a..b, ((2 / d) * ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t‖ +
          (2 * ε / d ^ 2) * ‖v t‖) := by
      rw [intervalIntegral.integral_add (hn1.const_mul _) (hn2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [hrhs]
    apply intervalIntegral.integral_mono_on hab
    · exact (hG.sub hvK).norm
    · exact (hn1.const_mul _).add (hn2.const_mul _)
    · intro t ht
      have hA := hden ε hε0 hεd t ht
      have hB := hdb t ht
      set A : ℂ := (t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I - z with hAdef
      set B : ℂ := (t : ℂ) - z with hBdef
      have hApos : 0 < ‖A‖ := by linarith
      have hBpos : 0 < ‖B‖ := by linarith
      have hAne : A ≠ 0 := norm_pos_iff.mp hApos
      have hBne : B ≠ 0 := norm_pos_iff.mp hBpos
      have hdiff : ‖A⁻¹ - B⁻¹‖ ≤ 2 * ε / d ^ 2 := by
        have e : A⁻¹ - B⁻¹ = (B - A) / (A * B) := by field_simp
        have hBA : ‖B - A‖ = ε := by
          have : B - A = -(((σ * ε : ℝ) : ℂ) * Complex.I) := by
            simp only [hAdef, hBdef]; ring
          rw [this, norm_neg, hshift ε hε0]
        rw [e, norm_div, norm_mul, hBA]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hd hd, mul_le_mul hA hB (by positivity) (by positivity)]
      have hAinv : ‖A⁻¹‖ ≤ 2 / d := by
        rw [norm_inv]
        calc (‖A‖)⁻¹ ≤ (d / 2)⁻¹ := inv_anti₀ (by positivity) hA
          _ = 2 / d := by field_simp
      have hsplit : F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) / A - v t / B =
          (F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t) * A⁻¹ + v t * (A⁻¹ - B⁻¹) := by
        simp only [div_eq_mul_inv]; ring
      show ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) / A - v t / B‖ ≤ _
      rw [hsplit]
      calc ‖(F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t) * A⁻¹ + v t * (A⁻¹ - B⁻¹)‖
          ≤ ‖(F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t) * A⁻¹‖ + ‖v t * (A⁻¹ - B⁻¹)‖ :=
            norm_add_le _ _
        _ ≤ (2 / d) * ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t‖ +
              (2 * ε / d ^ 2) * ‖v t‖ := by
            rw [norm_mul, norm_mul]
            have h1 : ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t‖ * ‖A⁻¹‖ ≤
                ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t‖ * (2 / d) :=
              mul_le_mul_of_nonneg_left hAinv (norm_nonneg _)
            have h2 : ‖v t‖ * ‖A⁻¹ - B⁻¹‖ ≤ ‖v t‖ * (2 * ε / d ^ 2) :=
              mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
            nlinarith [h1, h2]
  have hlim : Tendsto (fun ε : ℝ => (2 / d) * (∫ t : ℝ in a..b,
          ‖F ((t : ℂ) + (σ * ε : ℝ) * Complex.I) - v t‖) + (2 * ε / d ^ 2) * M)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 := htr.const_mul (2 / d)
    have h2 : Tendsto (fun ε : ℝ => (2 * ε / d ^ 2) * M) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun ε : ℝ => (2 * ε / d ^ 2) * M := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    simpa using h1.add h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

/-! ### 15.12, 15.13 -/

theorem frame_edges (f : ℂ → ℂ)
    (a l r b c lo hi d : ℝ)
    (hleft : DifferentiableOn ℂ f (uIcc a l ×ℂ uIcc c d))
    (hright : DifferentiableOn ℂ f (uIcc r b ×ℂ uIcc c d))
    (hbottom : DifferentiableOn ℂ f (uIcc l r ×ℂ uIcc c lo))
    (htop : DifferentiableOn ℂ f (uIcc l r ×ℂ uIcc hi d)) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume a b ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume a l ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume a l ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume l b ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume l b := by
  obtain ⟨hL1, hL2, -, -, -⟩ := rectangle_edges_and_zero f a l c d hleft
  obtain ⟨hR1, hR2, -, -, -⟩ := rectangle_edges_and_zero f r b c d hright
  obtain ⟨hB1, -, -, -, -⟩ := rectangle_edges_and_zero f l r c lo hbottom
  obtain ⟨-, hT2, -, -, -⟩ := rectangle_edges_and_zero f l r hi d htop
  have hlb1 := hB1.trans hR1
  have hlb2 := hT2.trans hR2
  exact ⟨hL1.trans hlb1, hL2.trans hlb2, hL1, hL2, hlb1, hlb2⟩

theorem rectangular_frame_excision (f : ℂ → ℂ)
    (a l r b c lo hi d : ℝ)
    (hclo : c ≤ lo) (hlohi : lo ≤ hi) (hhid : hi ≤ d)
    (hleft : DifferentiableOn ℂ f (uIcc a l ×ℂ uIcc c d))
    (hright : DifferentiableOn ℂ f (uIcc r b ×ℂ uIcc c d))
    (hbottom : DifferentiableOn ℂ f (uIcc l r ×ℂ uIcc c lo))
    (htop : DifferentiableOn ℂ f (uIcc l r ×ℂ uIcc hi d)) :
    rectIntegral f a b c d = rectIntegral f l r lo hi := by
  obtain ⟨-, -, hc_al, hd_al, hc_lb, hd_lb⟩ :=
    frame_edges f a l r b c lo hi d hleft hright hbottom htop
  obtain ⟨-, -, -, hVl, hz_left⟩ := rectangle_edges_and_zero f a l c d hleft
  obtain ⟨-, -, hVr, -, hz_right⟩ := rectangle_edges_and_zero f r b c d hright
  obtain ⟨hc_lr, -, -, -, hz_bot⟩ := rectangle_edges_and_zero f l r c lo hbottom
  obtain ⟨-, hd_lr, -, -, hz_top⟩ := rectangle_edges_and_zero f l r hi d htop
  obtain ⟨hc_rb, hd_rb, -, -, -⟩ := rectangle_edges_and_zero f r b c d hright
  have e1 := rectIntegral_horizontal_split f a l b c d hc_al hc_lb hd_al hd_lb
  have e2 := rectIntegral_horizontal_split f l r b c d hc_lr hc_rb hd_lr hd_rb
  have sub : ∀ p q : ℝ, c ≤ p → p ≤ q → q ≤ d →
      IntervalIntegrable (fun y : ℝ => f ((l : ℂ) + (y : ℂ) * Complex.I)) volume p q ∧
      IntervalIntegrable (fun y : ℝ => f ((r : ℂ) + (y : ℂ) * Complex.I)) volume p q := by
    intro p q hp hpq hq
    have hsub : uIcc p q ⊆ uIcc c d := by
      apply uIcc_subset_uIcc
      · exact mem_uIcc.mpr (Or.inl ⟨hp, hpq.trans hq⟩)
      · exact mem_uIcc.mpr (Or.inl ⟨hp.trans hpq, hq⟩)
    exact ⟨hVl.mono_set hsub, hVr.mono_set hsub⟩
  obtain ⟨p1l, p1r⟩ := sub c lo le_rfl hclo (hlohi.trans hhid)
  obtain ⟨p2l, p2r⟩ := sub lo d hclo (hlohi.trans hhid) le_rfl
  obtain ⟨p3l, p3r⟩ := sub lo hi hclo hlohi hhid
  obtain ⟨p4l, p4r⟩ := sub hi d (hclo.trans hlohi) hhid le_rfl
  have e3 := rectIntegral_vertical_split f l r c lo d p1r p2r p1l p2l
  have e4 := rectIntegral_vertical_split f l r lo hi d p3r p4r p3l p4l
  rw [e1, e2, e3, e4, hz_left, hz_right, hz_bot, hz_top]
  ring

theorem finite_frame_edges (f : ℂ → ℂ) (N : ℕ)
    (a l r lo hi : ℕ → ℝ) (c d : ℝ)
    (hleft : ∀ k < N, DifferentiableOn ℂ f
      (uIcc (a k) (l k) ×ℂ uIcc c d))
    (hright : ∀ k < N, DifferentiableOn ℂ f
      (uIcc (r k) (a (k + 1)) ×ℂ uIcc c d))
    (hbottom : ∀ k < N, DifferentiableOn ℂ f
      (uIcc (l k) (r k) ×ℂ uIcc c (lo k)))
    (htop : ∀ k < N, DifferentiableOn ℂ f
      (uIcc (l k) (r k) ×ℂ uIcc (hi k) d)) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume (a 0) (a N) ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume (a 0) (a N) := by
  induction N with
  | zero => exact ⟨IntervalIntegrable.refl, IntervalIntegrable.refl⟩
  | succ N ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun k hk => hleft k (by omega)) (fun k hk => hright k (by omega))
      (fun k hk => hbottom k (by omega)) (fun k hk => htop k (by omega))
    obtain ⟨h1, h2, -⟩ := frame_edges f (a N) (l N) (r N) (a (N + 1)) c (lo N) (hi N) d
      (hleft N (by omega)) (hright N (by omega)) (hbottom N (by omega)) (htop N (by omega))
    exact ⟨ih1.trans h1, ih2.trans h2⟩

theorem finite_rectangular_frame_excision (f : ℂ → ℂ) (N : ℕ)
    (a l r lo hi : ℕ → ℝ) (c d : ℝ)
    (hclo : ∀ k < N, c ≤ lo k)
    (hlohi : ∀ k < N, lo k ≤ hi k)
    (hhid : ∀ k < N, hi k ≤ d)
    (hleft : ∀ k < N, DifferentiableOn ℂ f
      (uIcc (a k) (l k) ×ℂ uIcc c d))
    (hright : ∀ k < N, DifferentiableOn ℂ f
      (uIcc (r k) (a (k + 1)) ×ℂ uIcc c d))
    (hbottom : ∀ k < N, DifferentiableOn ℂ f
      (uIcc (l k) (r k) ×ℂ uIcc c (lo k)))
    (htop : ∀ k < N, DifferentiableOn ℂ f
      (uIcc (l k) (r k) ×ℂ uIcc (hi k) d)) :
    rectIntegral f (a 0) (a N) c d =
      ∑ k ∈ Finset.range N, rectIntegral f (l k) (r k) (lo k) (hi k) := by
  induction N with
  | zero => simp [rectIntegral]
  | succ N ih =>
    have ih' := ih (fun k hk => hclo k (by omega)) (fun k hk => hlohi k (by omega))
      (fun k hk => hhid k (by omega)) (fun k hk => hleft k (by omega))
      (fun k hk => hright k (by omega)) (fun k hk => hbottom k (by omega))
      (fun k hk => htop k (by omega))
    obtain ⟨e1, e2⟩ := finite_frame_edges f N a l r lo hi c d (fun k hk => hleft k (by omega))
      (fun k hk => hright k (by omega)) (fun k hk => hbottom k (by omega))
      (fun k hk => htop k (by omega))
    obtain ⟨g1, g2, -⟩ := frame_edges f (a N) (l N) (r N) (a (N + 1)) c (lo N) (hi N) d
      (hleft N (by omega)) (hright N (by omega)) (hbottom N (by omega)) (htop N (by omega))
    rw [rectIntegral_horizontal_split f (a 0) (a N) (a (N + 1)) c d e1 g1 e2 g2,
      ih', Finset.sum_range_succ]
    congr 1
    exact rectangular_frame_excision f (a N) (l N) (r N) (a (N + 1)) c (lo N) (hi N) d
      (hclo N (by omega)) (hlohi N (by omega)) (hhid N (by omega))
      (hleft N (by omega)) (hright N (by omega)) (hbottom N (by omega)) (htop N (by omega))

/-! ### 15.07 -/

theorem carrier_im_eq_zero {n : ℕ} (S : RealSlits n) {w : ℂ} (hw : w ∈ S.carrier) :
    w.im = 0 := by
  obtain ⟨i, ⟨t, -, rfl⟩⟩ := mem_iUnion.mp hw
  simp

theorem kernel_bound (F : ℂ → ℂ) (U : Set ℂ) (a z : ℂ) (C δ ρ ε : ℝ) (hC : 0 ≤ C)
    (hB : ∀ w ∈ U, 0 < dist w a → dist w a < δ → ‖F w‖ ≤ C / Real.sqrt (dist w a))
    (hρ : 0 < ρ) (hz : ρ ≤ ‖a - z‖) (hε : 0 < ε) (hεδ : 2 * ε < δ) (hερ : 4 * ε ≤ ρ)
    (w : ℂ) (hw : w ∈ U) (h1 : ε ≤ dist w a) (h2 : dist w a ≤ 2 * ε) :
    ‖F w / (w - z)‖ ≤ 2 * C / (ρ * Real.sqrt ε) := by
  have hs : 0 < dist w a := lt_of_lt_of_le hε h1
  have hFw := hB w hw hs (lt_of_le_of_lt h2 hεδ)
  have hsq : Real.sqrt ε ≤ Real.sqrt (dist w a) := Real.sqrt_le_sqrt h1
  have hsqpos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hF1 : ‖F w‖ ≤ C / Real.sqrt ε :=
    hFw.trans (div_le_div_of_nonneg_left hC hsqpos hsq)
  have hden : ρ / 2 ≤ ‖w - z‖ := by
    have h3 : ‖a - z‖ ≤ ‖w - z‖ + ‖w - a‖ := by
      calc ‖a - z‖ = ‖(w - z) - (w - a)‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖w - a‖ := norm_sub_le _ _
    have h4 : ‖w - a‖ = dist w a := (dist_eq_norm w a).symm
    linarith
  rw [norm_div]
  calc ‖F w‖ / ‖w - z‖ ≤ (C / Real.sqrt ε) / (ρ / 2) :=
        div_le_div₀ (by positivity) hF1 (by positivity) hden
    _ = 2 * C / (ρ * Real.sqrt ε) := by field_simp

theorem segment_norm_le (g : ℝ → ℂ) (lo hi B : ℝ) (hlh : lo ≤ hi)
    (hg : ∀ᵐ t : ℝ, t ∈ Ioc lo hi → ‖g t‖ ≤ B) :
    ‖∫ t in lo..hi, g t‖ ≤ B * (hi - lo) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (g := fun _ => B) hlh hg
    intervalIntegrable_const
  simpa [mul_comm] using h

theorem dist_bounds_aux (w : ℂ) (p : ℝ) (ε : ℝ)
    (hre : |w.re - p| ≤ ε) (him : |w.im| ≤ ε) (hone : |w.re - p| = ε ∨ |w.im| = ε) :
    ε ≤ dist w (p : ℂ) ∧ dist w (p : ℂ) ≤ 2 * ε := by
  rw [dist_eq_norm]
  have h1 : |(w - (p : ℂ)).re| ≤ ‖w - (p : ℂ)‖ := Complex.abs_re_le_norm _
  have h2 : |(w - (p : ℂ)).im| ≤ ‖w - (p : ℂ)‖ := Complex.abs_im_le_norm _
  have h3 : ‖w - (p : ℂ)‖ ≤ |(w - (p : ℂ)).re| + |(w - (p : ℂ)).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have e1 : (w - (p : ℂ)).re = w.re - p := by simp
  have e2 : (w - (p : ℂ)).im = w.im := by simp
  rw [e1] at h1 h3
  rw [e2] at h2 h3
  refine ⟨?_, by linarith⟩
  rcases hone with h | h
  · linarith
  · linarith

theorem endpoint_caps_tendsto_zero {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) (z : ℂ) (hz : z ∉ S.carrier)
    (i : Fin n) :
    Tendsto
      (fun ε : ℝ => leftCap (fun w => D.F w / (w - z)) (S.a i) ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto
      (fun ε : ℝ => rightCap (fun w => D.F w / (w - z)) (S.b i) ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hmem : ∀ t ∈ Icc (S.a i) (S.b i), (t : ℂ) ∈ S.carrier := fun t ht =>
    mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩
  have hnotin : ∀ w : ℂ, w.im ≠ 0 → w ∈ S.carrierᶜ := fun w hw hmem' =>
    hw (carrier_im_eq_zero S hmem')
  have hlim : ∀ (K : ℝ) (g : ℝ → ℂ), (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ‖g ε‖ ≤ K * Real.sqrt ε) →
      Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro K g hg
    have hc : Continuous fun ε : ℝ => K * Real.sqrt ε :=
      continuous_const.mul Real.continuous_sqrt
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simp only [Real.sqrt_zero, mul_zero] at h0
    exact squeeze_zero_norm' hg h0
  have hae0 : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), y ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  constructor
  · obtain ⟨C, δ, hC, hδ, hB⟩ := D.endpoint_left i
    have hpi : (S.a i : ℂ) ∈ S.carrier := hmem _ ⟨le_rfl, S.le i⟩
    set ρ : ℝ := ‖(S.a i : ℂ) - z‖ with hρdef
    have hρ : 0 < ρ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hz (h ▸ hpi))
    refine hlim (8 * C / ρ) _ ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min (half_pos hδ) (div_pos hρ (by norm_num : (0:ℝ) < 4)))]
      with ε hε
    have hε0 : 0 < ε := hε.1
    have hεδ : 2 * ε < δ := by have := hε.2; have := min_le_left (δ / 2) (ρ / 4); linarith
    have hερ : 4 * ε ≤ ρ := by have := hε.2; have := min_le_right (δ / 2) (ρ / 4); linarith
    have hK : ∀ w : ℂ, w ∈ S.carrierᶜ → ε ≤ dist w (S.a i : ℂ) → dist w (S.a i : ℂ) ≤ 2 * ε →
        ‖D.F w / (w - z)‖ ≤ 2 * C / (ρ * Real.sqrt ε) := fun w hw h1 h2 =>
      kernel_bound D.F S.carrierᶜ (S.a i : ℂ) z C δ ρ ε hC hB hρ le_rfl hε0 hεδ hερ w hw h1 h2
    have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
    set B : ℝ := 2 * C / (ρ * Real.sqrt ε) with hBdef
    have hI1 : ‖∫ t : ℝ in (S.a i - ε)..(S.a i),
        D.F ((t : ℂ) - (ε : ℂ) * Complex.I) / ((t : ℂ) - (ε : ℂ) * Complex.I - z)‖ ≤ B * ε := by
      have := segment_norm_le (fun t : ℝ =>
        D.F ((t : ℂ) - (ε : ℂ) * Complex.I) / ((t : ℂ) - (ε : ℂ) * Complex.I - z))
        (S.a i - ε) (S.a i) B (by linarith) (Filter.Eventually.of_forall fun t ht => ?_)
      · have e : (S.a i) - (S.a i - ε) = ε := by ring
        rw [e] at this
        exact this
      · have hre : ((t : ℂ) - (ε : ℂ) * Complex.I).re - (S.a i) = t - (S.a i) := by simp
        have him : ((t : ℂ) - (ε : ℂ) * Complex.I).im = -ε := by simp
        have hd := dist_bounds_aux ((t : ℂ) - (ε : ℂ) * Complex.I) (S.a i) ε
          (by rw [hre, abs_le]; constructor <;> linarith [ht.1, ht.2])
          (by rw [him, abs_neg, abs_of_pos hε0])
          (Or.inr (by rw [him, abs_neg, abs_of_pos hε0]))
        exact hK _ (hnotin _ (by rw [him]; exact neg_ne_zero.mpr hε0.ne')) hd.1 hd.2
    have hI2 : ‖∫ t : ℝ in (S.a i - ε)..(S.a i),
        D.F ((t : ℂ) + (ε : ℂ) * Complex.I) / ((t : ℂ) + (ε : ℂ) * Complex.I - z)‖ ≤ B * ε := by
      have := segment_norm_le (fun t : ℝ =>
        D.F ((t : ℂ) + (ε : ℂ) * Complex.I) / ((t : ℂ) + (ε : ℂ) * Complex.I - z))
        (S.a i - ε) (S.a i) B (by linarith) (Filter.Eventually.of_forall fun t ht => ?_)
      · have e : (S.a i) - (S.a i - ε) = ε := by ring
        rw [e] at this
        exact this
      · have hre : ((t : ℂ) + (ε : ℂ) * Complex.I).re - (S.a i) = t - (S.a i) := by simp
        have him : ((t : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp
        have hd := dist_bounds_aux ((t : ℂ) + (ε : ℂ) * Complex.I) (S.a i) ε
          (by rw [hre, abs_le]; constructor <;> linarith [ht.1, ht.2])
          (by rw [him, abs_of_pos hε0])
          (Or.inr (by rw [him, abs_of_pos hε0]))
        exact hK _ (hnotin _ (by rw [him]; exact hε0.ne')) hd.1 hd.2
    have hI3 : ‖∫ y : ℝ in (-ε)..ε,
        D.F (((S.a i - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
          (((S.a i - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I - z)‖ ≤ B * (2 * ε) := by
      have := segment_norm_le (fun y : ℝ =>
        D.F (((S.a i - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
          (((S.a i - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I - z))
        (-ε) ε B (by linarith) ?_
      · have e : ε - (-ε) = 2 * ε := by ring
        rw [e] at this
        exact this
      · filter_upwards [hae0] with y hy0 hy
        have hre : (((S.a i - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I).re - (S.a i) = -ε := by simp
        have him : (((S.a i - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
        have hd := dist_bounds_aux (((S.a i - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I) (S.a i) ε
          (by rw [hre]; rw [abs_neg, abs_of_pos hε0])
          (by rw [him, abs_le]; constructor <;> linarith [hy.1, hy.2])
          (Or.inl (by rw [hre]; rw [abs_neg, abs_of_pos hε0]))
        exact hK _ (hnotin _ (by rw [him]; exact hy0)) hd.1 hd.2
    unfold leftCap
    calc ‖_‖ ≤ ‖(∫ t : ℝ in (S.a i - ε)..(S.a i), D.F ((t : ℂ) - (ε : ℂ) * Complex.I) /
            ((t : ℂ) - (ε : ℂ) * Complex.I - z)) -
          (∫ t : ℝ in (S.a i - ε)..(S.a i), D.F ((t : ℂ) + (ε : ℂ) * Complex.I) /
            ((t : ℂ) + (ε : ℂ) * Complex.I - z))‖ +
          ‖Complex.I * ∫ y : ℝ in (-ε)..ε, D.F (((S.a i - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
            (((S.a i - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I - z)‖ := norm_sub_le _ _
      _ ≤ (B * ε + B * ε) + B * (2 * ε) := by
          rw [norm_mul, Complex.norm_I, one_mul]
          exact add_le_add ((norm_sub_le _ _).trans (add_le_add hI1 hI2)) hI3
      _ = 8 * C / ρ * Real.sqrt ε := by
          rw [hBdef]
          have : ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hε0.le).symm
          field_simp
          nlinarith [this]
  · obtain ⟨C, δ, hC, hδ, hB⟩ := D.endpoint_right i
    have hpi : (S.b i : ℂ) ∈ S.carrier := hmem _ ⟨S.le i, le_rfl⟩
    set ρ : ℝ := ‖(S.b i : ℂ) - z‖ with hρdef
    have hρ : 0 < ρ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hz (h ▸ hpi))
    refine hlim (8 * C / ρ) _ ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min (half_pos hδ) (div_pos hρ (by norm_num : (0:ℝ) < 4)))]
      with ε hε
    have hε0 : 0 < ε := hε.1
    have hεδ : 2 * ε < δ := by have := hε.2; have := min_le_left (δ / 2) (ρ / 4); linarith
    have hερ : 4 * ε ≤ ρ := by have := hε.2; have := min_le_right (δ / 2) (ρ / 4); linarith
    have hK : ∀ w : ℂ, w ∈ S.carrierᶜ → ε ≤ dist w (S.b i : ℂ) → dist w (S.b i : ℂ) ≤ 2 * ε →
        ‖D.F w / (w - z)‖ ≤ 2 * C / (ρ * Real.sqrt ε) := fun w hw h1 h2 =>
      kernel_bound D.F S.carrierᶜ (S.b i : ℂ) z C δ ρ ε hC hB hρ le_rfl hε0 hεδ hερ w hw h1 h2
    have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
    set B : ℝ := 2 * C / (ρ * Real.sqrt ε) with hBdef
    have hI1 : ‖∫ t : ℝ in (S.b i)..(S.b i + ε),
        D.F ((t : ℂ) - (ε : ℂ) * Complex.I) / ((t : ℂ) - (ε : ℂ) * Complex.I - z)‖ ≤ B * ε := by
      have := segment_norm_le (fun t : ℝ =>
        D.F ((t : ℂ) - (ε : ℂ) * Complex.I) / ((t : ℂ) - (ε : ℂ) * Complex.I - z))
        (S.b i) (S.b i + ε) B (by linarith) (Filter.Eventually.of_forall fun t ht => ?_)
      · have e : (S.b i + ε) - (S.b i) = ε := by ring
        rw [e] at this
        exact this
      · have hre : ((t : ℂ) - (ε : ℂ) * Complex.I).re - (S.b i) = t - (S.b i) := by simp
        have him : ((t : ℂ) - (ε : ℂ) * Complex.I).im = -ε := by simp
        have hd := dist_bounds_aux ((t : ℂ) - (ε : ℂ) * Complex.I) (S.b i) ε
          (by rw [hre, abs_le]; constructor <;> linarith [ht.1, ht.2])
          (by rw [him, abs_neg, abs_of_pos hε0])
          (Or.inr (by rw [him, abs_neg, abs_of_pos hε0]))
        exact hK _ (hnotin _ (by rw [him]; exact neg_ne_zero.mpr hε0.ne')) hd.1 hd.2
    have hI2 : ‖∫ t : ℝ in (S.b i)..(S.b i + ε),
        D.F ((t : ℂ) + (ε : ℂ) * Complex.I) / ((t : ℂ) + (ε : ℂ) * Complex.I - z)‖ ≤ B * ε := by
      have := segment_norm_le (fun t : ℝ =>
        D.F ((t : ℂ) + (ε : ℂ) * Complex.I) / ((t : ℂ) + (ε : ℂ) * Complex.I - z))
        (S.b i) (S.b i + ε) B (by linarith) (Filter.Eventually.of_forall fun t ht => ?_)
      · have e : (S.b i + ε) - (S.b i) = ε := by ring
        rw [e] at this
        exact this
      · have hre : ((t : ℂ) + (ε : ℂ) * Complex.I).re - (S.b i) = t - (S.b i) := by simp
        have him : ((t : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp
        have hd := dist_bounds_aux ((t : ℂ) + (ε : ℂ) * Complex.I) (S.b i) ε
          (by rw [hre, abs_le]; constructor <;> linarith [ht.1, ht.2])
          (by rw [him, abs_of_pos hε0])
          (Or.inr (by rw [him, abs_of_pos hε0]))
        exact hK _ (hnotin _ (by rw [him]; exact hε0.ne')) hd.1 hd.2
    have hI3 : ‖∫ y : ℝ in (-ε)..ε,
        D.F (((S.b i + ε : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
          (((S.b i + ε : ℝ) : ℂ) + (y : ℂ) * Complex.I - z)‖ ≤ B * (2 * ε) := by
      have := segment_norm_le (fun y : ℝ =>
        D.F (((S.b i + ε : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
          (((S.b i + ε : ℝ) : ℂ) + (y : ℂ) * Complex.I - z))
        (-ε) ε B (by linarith) ?_
      · have e : ε - (-ε) = 2 * ε := by ring
        rw [e] at this
        exact this
      · filter_upwards [hae0] with y hy0 hy
        have hre : (((S.b i + ε : ℝ) : ℂ) + (y : ℂ) * Complex.I).re - (S.b i) = ε := by simp
        have him : (((S.b i + ε : ℝ) : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
        have hd := dist_bounds_aux (((S.b i + ε : ℝ) : ℂ) + (y : ℂ) * Complex.I) (S.b i) ε
          (by rw [hre]; rw [abs_of_pos hε0])
          (by rw [him, abs_le]; constructor <;> linarith [hy.1, hy.2])
          (Or.inl (by rw [hre]; rw [abs_of_pos hε0]))
        exact hK _ (hnotin _ (by rw [him]; exact hy0)) hd.1 hd.2
    unfold rightCap
    calc ‖_‖ ≤ ‖(∫ t : ℝ in (S.b i)..(S.b i + ε), D.F ((t : ℂ) - (ε : ℂ) * Complex.I) /
            ((t : ℂ) - (ε : ℂ) * Complex.I - z)) -
          (∫ t : ℝ in (S.b i)..(S.b i + ε), D.F ((t : ℂ) + (ε : ℂ) * Complex.I) /
            ((t : ℂ) + (ε : ℂ) * Complex.I - z))‖ +
          ‖Complex.I * ∫ y : ℝ in (-ε)..ε, D.F (((S.b i + ε : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
            (((S.b i + ε : ℝ) : ℂ) + (y : ℂ) * Complex.I - z)‖ := norm_add_le _ _
      _ ≤ (B * ε + B * ε) + B * (2 * ε) := by
          rw [norm_mul, Complex.norm_I, one_mul]
          exact add_le_add ((norm_sub_le _ _).trans (add_le_add hI1 hI2)) hI3
      _ = 8 * C / ρ * Real.sqrt ε := by
          rw [hBdef]
          have : ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hε0.le).symm
          field_simp
          nlinarith [this]

/-! ### 15.08, 15.09 -/

theorem kappa_comp_continuous {n : ℕ} (S : RealSlits n) (D : SlitHolomorphicData S) (z : ℂ)
    (p : ℝ → ℂ) (hp : Continuous p) (him : ∀ x, (p x).im ≠ 0) (hz : ∀ x, p x ≠ z) :
    Continuous (fun x : ℝ => D.F (p x) / (p x - z)) := by
  have hopen : IsOpen S.carrierᶜ := (slits_compact_and_separated S).2.1
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hw : p x ∈ S.carrierᶜ := fun h => him x (carrier_im_eq_zero S h)
  have h1 : ContinuousAt D.F (p x) :=
    (D.holomorphic.differentiableAt (hopen.mem_nhds hw)).continuousAt
  have h2 : ContinuousAt (fun w : ℂ => D.F w / (w - z)) (p x) :=
    h1.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr (hz x))
  exact h2.comp hp.continuousAt

theorem rect_eq_caps (f : ℂ → ℂ) (a b ε : ℝ)
    (h1l : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) - (ε : ℂ) * Complex.I)) volume (a - ε) a)
    (h1m : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) - (ε : ℂ) * Complex.I)) volume a b)
    (h1r : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) - (ε : ℂ) * Complex.I)) volume b (b + ε))
    (h2l : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (ε : ℂ) * Complex.I)) volume (a - ε) a)
    (h2m : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (ε : ℂ) * Complex.I)) volume a b)
    (h2r : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (ε : ℂ) * Complex.I)) volume b (b + ε)) :
    rectIntegral f (a - ε) (b + ε) (-ε) ε =
      leftCap f a ε + rightCap f b ε +
        ((∫ x : ℝ in a..b, f ((x : ℂ) - (ε : ℂ) * Complex.I)) -
          ∫ x : ℝ in a..b, f ((x : ℂ) + (ε : ℂ) * Complex.I)) := by
  unfold rectIntegral leftCap rightCap
  have e1 : ∀ x : ℝ, f ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) =
      f ((x : ℂ) - (ε : ℂ) * Complex.I) := by
    intro x; congr 1; push_cast; ring
  simp only [e1]
  have s1 := intervalIntegral.integral_add_adjacent_intervals (h1l.trans h1m) h1r
  have s2 := intervalIntegral.integral_add_adjacent_intervals h1l h1m
  have s3 := intervalIntegral.integral_add_adjacent_intervals (h2l.trans h2m) h2r
  have s4 := intervalIntegral.integral_add_adjacent_intervals h2l h2m
  rw [← s1, ← s2, ← s3, ← s4]
  ring

theorem lines_avoid_eventually (z : ℂ) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ x : ℝ,
      ((x : ℂ) - (ε : ℂ) * Complex.I ≠ z) ∧ ((x : ℂ) + (ε : ℂ) * Complex.I ≠ z) := by
  by_cases hz0 : z.im = 0
  · filter_upwards [self_mem_nhdsWithin] with ε hε x
    have hε' : 0 < ε := hε
    constructor
    · intro h
      have him : ((x : ℂ) - (ε : ℂ) * Complex.I).im = -ε := by simp
      rw [h, hz0] at him
      linarith
    · intro h
      have him : ((x : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp
      rw [h, hz0] at him
      linarith
  · filter_upwards [Ioo_mem_nhdsGT (abs_pos.mpr hz0)] with ε hε x
    constructor
    · intro h
      have him : ((x : ℂ) - (ε : ℂ) * Complex.I).im = -ε := by simp
      rw [h] at him
      have : |z.im| = ε := by rw [him, abs_neg, abs_of_pos hε.1]
      linarith [hε.2]
    · intro h
      have him : ((x : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp
      rw [h] at him
      have : |z.im| = ε := by rw [him, abs_of_pos hε.1]
      linarith [hε.2]

theorem one_collar_tendsto {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) (z : ℂ) (hz : z ∉ S.carrier)
    (i : Fin n) :
    Tendsto
      (fun ε : ℝ => rectIntegral (fun w => D.F w / (w - z))
        (S.a i - ε) (S.b i + ε) (-ε) ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(∫ t : ℝ in (S.a i)..(S.b i),
        D.jump i t / ((t : ℂ) - z)))) := by
  obtain ⟨hcapL, hcapR⟩ := endpoint_caps_tendsto_zero S D z hz i
  have hab := S.le i
  have hzI : z ∉ Complex.ofReal '' Icc (S.a i) (S.b i) := by
    rintro ⟨t, ht, h⟩
    exact hz (h ▸ mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩)
  have hU := weighted_trace_tendsto D.F (D.upper i) (S.a i) (S.b i) 1 hab (Or.inl rfl)
    (D.upper_trace i) z hzI
  have hL := weighted_trace_tendsto D.F (D.lower i) (S.a i) (S.b i) (-1) hab (Or.inr rfl)
    (D.lower_trace i) z hzI
  have hU' : Tendsto (fun ε : ℝ => ∫ t : ℝ in (S.a i)..(S.b i),
      D.F ((t : ℂ) + (ε : ℂ) * Complex.I) / ((t : ℂ) + (ε : ℂ) * Complex.I - z))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t : ℝ in (S.a i)..(S.b i), D.upper i t / ((t : ℂ) - z))) := by
    refine hU.congr fun ε => ?_
    apply intervalIntegral.integral_congr
    intro t _
    have e : (t : ℂ) + ((1 * ε : ℝ) : ℂ) * Complex.I = (t : ℂ) + (ε : ℂ) * Complex.I := by
      push_cast; ring
    simp only [e]
  have hL' : Tendsto (fun ε : ℝ => ∫ t : ℝ in (S.a i)..(S.b i),
      D.F ((t : ℂ) - (ε : ℂ) * Complex.I) / ((t : ℂ) - (ε : ℂ) * Complex.I - z))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t : ℝ in (S.a i)..(S.b i), D.lower i t / ((t : ℂ) - z))) := by
    refine hL.congr fun ε => ?_
    apply intervalIntegral.integral_congr
    intro t _
    have e : (t : ℂ) + ((-1 * ε : ℝ) : ℂ) * Complex.I = (t : ℂ) - (ε : ℂ) * Complex.I := by
      push_cast; ring
    simp only [e]
  -- the jump integral
  have hcont : ContinuousOn (fun t : ℝ => ((t : ℂ) - z)⁻¹) (uIcc (S.a i) (S.b i)) :=
    inv_sub_continuousOn S z hz i
  have hUi : IntervalIntegrable (fun t : ℝ => D.upper i t / ((t : ℂ) - z)) volume
      (S.a i) (S.b i) := by
    simpa [div_eq_mul_inv] using (D.upper_trace i).1.mul_continuousOn hcont
  have hLi : IntervalIntegrable (fun t : ℝ => D.lower i t / ((t : ℂ) - z)) volume
      (S.a i) (S.b i) := by
    simpa [div_eq_mul_inv] using (D.lower_trace i).1.mul_continuousOn hcont
  have hJ : (∫ t : ℝ in (S.a i)..(S.b i), D.jump i t / ((t : ℂ) - z)) =
      (∫ t : ℝ in (S.a i)..(S.b i), D.upper i t / ((t : ℂ) - z)) -
        ∫ t : ℝ in (S.a i)..(S.b i), D.lower i t / ((t : ℂ) - z) := by
    rw [← intervalIntegral.integral_sub hUi hLi]
    apply intervalIntegral.integral_congr_ae
    have h1 := D.jump_ae i
    rw [ae_restrict_iff' measurableSet_Icc] at h1
    filter_upwards [h1] with t ht hmem
    rw [uIoc_of_le hab] at hmem
    rw [ht (Ioc_subset_Icc_self hmem), sub_div]
  have hM := hL'.sub hU'
  -- eventual identity
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      rectIntegral (fun w => D.F w / (w - z)) (S.a i - ε) (S.b i + ε) (-ε) ε =
        leftCap (fun w => D.F w / (w - z)) (S.a i) ε +
          rightCap (fun w => D.F w / (w - z)) (S.b i) ε +
          ((∫ x : ℝ in (S.a i)..(S.b i),
              D.F ((x : ℂ) - (ε : ℂ) * Complex.I) / ((x : ℂ) - (ε : ℂ) * Complex.I - z)) -
            ∫ x : ℝ in (S.a i)..(S.b i),
              D.F ((x : ℂ) + (ε : ℂ) * Complex.I) / ((x : ℂ) + (ε : ℂ) * Complex.I - z)) := by
    filter_upwards [lines_avoid_eventually z, self_mem_nhdsWithin] with ε hl hε
    have hε' : 0 < ε := hε
    have cm : Continuous (fun x : ℝ => D.F ((x : ℂ) - (ε : ℂ) * Complex.I) /
        ((x : ℂ) - (ε : ℂ) * Complex.I - z)) :=
      kappa_comp_continuous S D z (fun x : ℝ => (x : ℂ) - (ε : ℂ) * Complex.I) (by fun_prop)
        (fun x => by simp; exact hε'.ne') (fun x => (hl x).1)
    have cp : Continuous (fun x : ℝ => D.F ((x : ℂ) + (ε : ℂ) * Complex.I) /
        ((x : ℂ) + (ε : ℂ) * Complex.I - z)) :=
      kappa_comp_continuous S D z (fun x : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I) (by fun_prop)
        (fun x => by simp; exact hε'.ne') (fun x => (hl x).2)
    exact rect_eq_caps (fun w => D.F w / (w - z)) (S.a i) (S.b i) ε
      (cm.intervalIntegrable _ _) (cm.intervalIntegrable _ _) (cm.intervalIntegrable _ _)
      (cp.intervalIntegrable _ _) (cp.intervalIntegrable _ _) (cp.intervalIntegrable _ _)
  have hsum := (hcapL.add hcapR).add hM
  have hlim : (0 : ℂ) + 0 + ((∫ t : ℝ in (S.a i)..(S.b i), D.lower i t / ((t : ℂ) - z)) -
      ∫ t : ℝ in (S.a i)..(S.b i), D.upper i t / ((t : ℂ) - z)) =
      -(∫ t : ℝ in (S.a i)..(S.b i), D.jump i t / ((t : ℂ) - z)) := by
    rw [hJ]; ring
  rw [← hlim]
  exact hsum.congr' (hev.mono fun ε h => h.symm)

theorem collars_tendsto {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) (z : ℂ) (hz : z ∉ S.carrier) :
    Tendsto (collarIntegral S D.F z)
      (𝓝[>] (0 : ℝ)) (𝓝 (-jumpIntegral S D.jump z)) := by
  unfold collarIntegral jumpIntegral
  rw [← Finset.sum_neg_distrib]
  exact tendsto_finset_sum Finset.univ fun i _ => one_collar_tendsto S D z hz i

/-! ### rectangleLoop (design definition), 15.17 -/

def rectangleLoop (a b c d : ℝ) :
    Path ((a : ℂ) + (c : ℂ) * Complex.I)
      ((a : ℂ) + (c : ℂ) * Complex.I) :=
  (((Path.segment ((a : ℂ) + (c : ℂ) * Complex.I)
      ((b : ℂ) + (c : ℂ) * Complex.I)).trans
    (Path.segment ((b : ℂ) + (c : ℂ) * Complex.I)
      ((b : ℂ) + (d : ℂ) * Complex.I))).trans
    (Path.segment ((b : ℂ) + (d : ℂ) * Complex.I)
      ((a : ℂ) + (d : ℂ) * Complex.I))).trans
    (Path.segment ((a : ℂ) + (d : ℂ) * Complex.I)
      ((a : ℂ) + (c : ℂ) * Complex.I))

theorem outer_pt_bound (F : ℂ → ℂ) (C R₀ : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ w : ℂ, R₀ ≤ ‖w‖ → ‖F w‖ ≤ C / ‖w‖) (z : ℂ) (R : ℝ)
    (hR : 0 < R) (hR0 : R₀ ≤ R) (hz : ‖z‖ ≤ R / 2) (w : ℂ) (hw : R ≤ ‖w‖) :
    ‖F w / (w - z)‖ ≤ 2 * C / R ^ 2 := by
  have hF : ‖F w‖ ≤ C / R :=
    (hdec w (hR0.trans hw)).trans (div_le_div_of_nonneg_left hC hR hw)
  have hden : R / 2 ≤ ‖w - z‖ := by
    have h : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    linarith
  rw [norm_div]
  calc ‖F w‖ / ‖w - z‖ ≤ (C / R) / (R / 2) :=
        div_le_div₀ (by positivity) hF (by positivity) hden
    _ = 2 * C / R ^ 2 := by field_simp

theorem outer_square_tendsto_zero (F : ℂ → ℂ)
    (hdecay : DecaysAtInfinity F) (z : ℂ)
    (hcont : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ContinuousOn (fun w => F w / (w - z))
        (range (rectangleLoop (-R) R (-R) R))) :
    Tendsto
      (fun R : ℝ => rectIntegral (fun w => F w / (w - z))
        (-R) R (-R) R)
      atTop (𝓝 0) := by
  obtain ⟨C, R₀, hC, hR₀, hdec⟩ := hdecay
  have hev : ∀ᶠ R : ℝ in atTop, ‖rectIntegral (fun w => F w / (w - z)) (-R) R (-R) R‖ ≤
      16 * C / R := by
    filter_upwards [eventually_ge_atTop R₀, eventually_ge_atTop (2 * ‖z‖),
      eventually_gt_atTop (0 : ℝ)] with R hR0 hRz hR
    have hz : ‖z‖ ≤ R / 2 := by linarith
    have hpt := outer_pt_bound F C R₀ hC hdec z R hR hR0 hz
    have hhor : ∀ c : ℝ, |c| = R →
        ‖∫ x : ℝ in (-R)..R, F ((x : ℂ) + (c : ℂ) * Complex.I) /
          ((x : ℂ) + (c : ℂ) * Complex.I - z)‖ ≤ 2 * C / R ^ 2 * (R - (-R)) := by
      intro c hc
      refine segment_norm_le _ (-R) R _ (by linarith) (Filter.Eventually.of_forall fun x hx => ?_)
      apply hpt
      have h1 : |((x : ℂ) + (c : ℂ) * Complex.I).im| ≤ ‖(x : ℂ) + (c : ℂ) * Complex.I‖ :=
        Complex.abs_im_le_norm _
      have h2 : ((x : ℂ) + (c : ℂ) * Complex.I).im = c := by simp
      rw [h2, hc] at h1
      exact h1
    have hver : ∀ c : ℝ, |c| = R →
        ‖∫ y : ℝ in (-R)..R, F ((c : ℂ) + (y : ℂ) * Complex.I) /
          ((c : ℂ) + (y : ℂ) * Complex.I - z)‖ ≤ 2 * C / R ^ 2 * (R - (-R)) := by
      intro c hc
      refine segment_norm_le _ (-R) R _ (by linarith) (Filter.Eventually.of_forall fun y hy => ?_)
      apply hpt
      have h1 : |((c : ℂ) + (y : ℂ) * Complex.I).re| ≤ ‖(c : ℂ) + (y : ℂ) * Complex.I‖ :=
        Complex.abs_re_le_norm _
      have h2 : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
      rw [h2, hc] at h1
      exact h1
    have hR' : |(-R)| = R := by rw [abs_neg, abs_of_pos hR]
    have hR'' : |R| = R := abs_of_pos hR
    have e1 := hhor (-R) hR'
    have e2 := hhor R hR''
    have e3 := hver R hR''
    have e4 := hver (-R) hR'
    unfold rectIntegral
    calc ‖_‖ ≤ ‖(∫ x : ℝ in (-R)..R, F ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) /
            ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I - z)) -
          (∫ x : ℝ in (-R)..R, F ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I) /
            ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I - z)) +
          Complex.I * (∫ y : ℝ in (-R)..R, F (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
            (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I - z))‖ +
          ‖Complex.I * ∫ y : ℝ in (-R)..R, F (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
            (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I - z)‖ := norm_sub_le _ _
      _ ≤ 16 * C / R := by
          rw [norm_mul Complex.I, Complex.norm_I, one_mul]
          have h12 := norm_add_le
            ((∫ x : ℝ in (-R)..R, F ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) /
              ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I - z)) -
            (∫ x : ℝ in (-R)..R, F ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I) /
              ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I - z)))
            (Complex.I * (∫ y : ℝ in (-R)..R, F (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
              (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I - z)))
          rw [norm_mul Complex.I, Complex.norm_I, one_mul] at h12
          have h1 := norm_sub_le
            (∫ x : ℝ in (-R)..R, F ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) /
              ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I - z))
            (∫ x : ℝ in (-R)..R, F ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I) /
              ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I - z))
          have : 2 * C / R ^ 2 * (R - -R) * 4 = 16 * C / R := by field_simp; ring
          nlinarith [h12, h1, e1, e2, e3, e4]
  have hlim : Tendsto (fun R : ℝ => 16 * C / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hev hlim

/-! ### 15.15 -/

theorem inv_re_im_form (u t : ℝ) :
    ((u : ℂ) + (t : ℂ) * Complex.I)⁻¹ =
      ((u / (u ^ 2 + t ^ 2) : ℝ) : ℂ) - ((t / (u ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I := by
  have hc : (starRingEnd ℂ) ((u : ℂ) + (t : ℂ) * Complex.I) = (u : ℂ) - (t : ℂ) * Complex.I := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [Complex.inv_def, Complex.normSq_add_mul_I, hc]
  push_cast
  ring

theorem hasDerivAt_hor_antideriv (re t : ℝ) (ht : t ≠ 0) (x : ℝ) :
    HasDerivAt
      (fun x : ℝ => (((1 / 2 * Real.log ((x - re) ^ 2 + t ^ 2) : ℝ) : ℂ)) -
        ((Real.arctan ((x - re) / t) : ℝ) : ℂ) * Complex.I)
      ((((x - re : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹) x := by
  have hpos : 0 < (x - re) ^ 2 + t ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => (x - re) ^ 2 + t ^ 2) (2 * (x - re)) x := by
    have := (((hasDerivAt_id x).sub_const re).pow 2).add_const (t ^ 2)
    simpa using this
  have h2 := (h1.log hpos.ne').const_mul (1 / 2)
  have h4 : HasDerivAt (fun x : ℝ => (x - re) / t) (1 / t) x := by
    have := ((hasDerivAt_id x).sub_const re).div_const t
    simpa using this
  have h5 := h4.arctan
  have h6 := h2.ofReal_comp.sub (h5.ofReal_comp.mul_const Complex.I)
  convert h6 using 1
  rw [inv_re_im_form]
  have e1 : (1 / 2 * (2 * (x - re) / ((x - re) ^ 2 + t ^ 2)) : ℝ) =
      (x - re) / ((x - re) ^ 2 + t ^ 2) := by first | (field_simp; ring) | field_simp
  have e2 : (1 / (1 + ((x - re) / t) ^ 2) * (1 / t) : ℝ) = t / ((x - re) ^ 2 + t ^ 2) := by
    first | (field_simp; ring) | field_simp
  rw [e1, e2]

theorem hor_inv_integral (re t s : ℝ) (ht : t ≠ 0) :
    ∫ x : ℝ in (re - s)..(re + s), (((x - re : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹ =
      ((-(2 * Real.arctan (s / t)) : ℝ) : ℂ) * Complex.I := by
  have hcont : Continuous fun x : ℝ => (((x - re : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
    apply Continuous.inv₀ (by fun_prop)
    intro x h
    have := congrArg Complex.im h
    simp at this
    exact ht this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_hor_antideriv re t ht x) (hcont.intervalIntegrable _ _)]
  have e : (re + s - re) ^ 2 = (re - s - re) ^ 2 := by ring
  have e2 : (re - s - re) / t = -(s / t) := by ring
  simp only [e, e2, Real.arctan_neg]
  have e3 : (re + s - re) / t = s / t := by ring
  rw [e3]
  push_cast
  ring

theorem hasDerivAt_ver_antideriv (im u : ℝ) (hu : u ≠ 0) (y : ℝ) :
    HasDerivAt
      (fun y : ℝ => ((Real.arctan ((y - im) / u) : ℝ) : ℂ) -
        (((1 / 2 * Real.log (u ^ 2 + (y - im) ^ 2) : ℝ)) : ℂ) * Complex.I)
      (((u : ℂ) + ((y - im : ℝ) : ℂ) * Complex.I)⁻¹) y := by
  have hpos : 0 < u ^ 2 + (y - im) ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => u ^ 2 + (y - im) ^ 2) (2 * (y - im)) y := by
    have := (((hasDerivAt_id y).sub_const im).pow 2).const_add (u ^ 2)
    simpa using this
  have h2 := (h1.log hpos.ne').const_mul (1 / 2)
  have h4 : HasDerivAt (fun y : ℝ => (y - im) / u) (1 / u) y := by
    have := ((hasDerivAt_id y).sub_const im).div_const u
    simpa using this
  have h5 := h4.arctan
  have h6 := h5.ofReal_comp.sub (h2.ofReal_comp.mul_const Complex.I)
  convert h6 using 1
  rw [inv_re_im_form]
  have e1 : (1 / 2 * (2 * (y - im) / (u ^ 2 + (y - im) ^ 2)) : ℝ) =
      (y - im) / (u ^ 2 + (y - im) ^ 2) := by first | (field_simp; ring) | field_simp
  have e2 : (1 / (1 + ((y - im) / u) ^ 2) * (1 / u) : ℝ) = u / (u ^ 2 + (y - im) ^ 2) := by
    first | (field_simp; ring) | field_simp
  rw [e1, e2]

theorem ver_inv_integral (im u s : ℝ) (hu : u ≠ 0) :
    ∫ y : ℝ in (im - s)..(im + s), ((u : ℂ) + ((y - im : ℝ) : ℂ) * Complex.I)⁻¹ =
      ((2 * Real.arctan (s / u) : ℝ) : ℂ) := by
  have hcont : Continuous fun y : ℝ => ((u : ℂ) + ((y - im : ℝ) : ℂ) * Complex.I)⁻¹ := by
    apply Continuous.inv₀ (by fun_prop)
    intro y h
    have := congrArg Complex.re h
    simp at this
    exact hu this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_ver_antideriv im u hu y) (hcont.intervalIntegrable _ _)]
  have e : (im + s - im) ^ 2 = (im - s - im) ^ 2 := by ring
  have e2 : (im - s - im) / u = -(s / u) := by ring
  have e3 : (im + s - im) / u = s / u := by ring
  simp only [e, e2, e3, Real.arctan_neg]
  push_cast
  ring

theorem rect_inv_square (z : ℂ) (s : ℝ) (hs : 0 < s) :
    rectIntegral (fun w : ℂ => (w - z)⁻¹) (z.re - s) (z.re + s) (z.im - s) (z.im + s) =
      2 * Real.pi * Complex.I := by
  have hz : ∀ (c : ℝ) (x : ℝ), (x : ℂ) + (c : ℂ) * Complex.I - z =
      ((x - z.re : ℝ) : ℂ) + ((c - z.im : ℝ) : ℂ) * Complex.I := by
    intro c x
    apply Complex.ext <;> simp
  have hz2 : ∀ (e : ℝ) (y : ℝ), (e : ℂ) + (y : ℂ) * Complex.I - z =
      ((e - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * Complex.I := by
    intro e y
    apply Complex.ext <;> simp
  unfold rectIntegral
  simp only [hz, hz2]
  have h1 := hor_inv_integral z.re (z.im - s - z.im) s (by linarith : z.im - s - z.im ≠ 0)
  have h2 := hor_inv_integral z.re (z.im + s - z.im) s (by linarith : z.im + s - z.im ≠ 0)
  have h3 := ver_inv_integral z.im (z.re + s - z.re) s (by linarith : z.re + s - z.re ≠ 0)
  have h4 := ver_inv_integral z.im (z.re - s - z.re) s (by linarith : z.re - s - z.re ≠ 0)
  simp only [add_sub_cancel_left, sub_sub_cancel_left] at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4]
  have a1 : s / -s = -1 := by field_simp
  have a2 : s / s = 1 := div_self hs.ne'
  rw [a1, a2, Real.arctan_neg, Real.arctan_one]
  push_cast
  ring

/-! ### 15.15 (main statement), 15.16 -/

theorem inv_sub_differentiableOn (z : ℂ) (S : Set ℂ) (hS : ∀ w ∈ S, w ≠ z) :
    DifferentiableOn ℂ (fun w : ℂ => (w - z)⁻¹) S :=
  DifferentiableOn.inv (differentiableOn_id.sub_const z) fun w hw => sub_ne_zero.mpr (hS w hw)

theorem rectIntegral_inv (a b c d : ℝ) (z : ℂ)
    (hz : z ∈ Ioo a b ×ℂ Ioo c d) :
    rectIntegral (fun w : ℂ => (w - z)⁻¹) a b c d =
      2 * Real.pi * Complex.I := by
  obtain ⟨⟨hza, hzb⟩, ⟨hzc, hzd⟩⟩ := hz
  set s : ℝ := min (min (z.re - a) (b - z.re)) (min (z.im - c) (d - z.im)) / 2 with hsdef
  have hm1 : 0 < min (min (z.re - a) (b - z.re)) (min (z.im - c) (d - z.im)) := by
    apply lt_min
    · exact lt_min (by linarith) (by linarith)
    · exact lt_min (by linarith) (by linarith)
  have hs : 0 < s := by positivity
  have h1 : 2 * s ≤ z.re - a := by
    have := min_le_left (min (z.re - a) (b - z.re)) (min (z.im - c) (d - z.im))
    have := min_le_left (z.re - a) (b - z.re)
    linarith
  have h2 : 2 * s ≤ b - z.re := by
    have := min_le_left (min (z.re - a) (b - z.re)) (min (z.im - c) (d - z.im))
    have := min_le_right (z.re - a) (b - z.re)
    linarith
  have h3 : 2 * s ≤ z.im - c := by
    have := min_le_right (min (z.re - a) (b - z.re)) (min (z.im - c) (d - z.im))
    have := min_le_left (z.im - c) (d - z.im)
    linarith
  have h4 : 2 * s ≤ d - z.im := by
    have := min_le_right (min (z.re - a) (b - z.re)) (min (z.im - c) (d - z.im))
    have := min_le_right (z.im - c) (d - z.im)
    linarith
  have hne : ∀ w : ℂ, (w.re ≠ z.re ∨ w.im ≠ z.im) → w ≠ z := by
    intro w h hw
    rcases h with h | h
    · exact h (by rw [hw])
    · exact h (by rw [hw])
  have hex := rectangular_frame_excision (fun w : ℂ => (w - z)⁻¹) a (z.re - s) (z.re + s) b
    c (z.im - s) (z.im + s) d (by linarith) (by linarith) (by linarith)
    (by
      apply inv_sub_differentiableOn
      intro w hw
      apply hne
      left
      have := hw.1
      rw [uIcc_of_le (by linarith)] at this
      have := this.2
      intro h
      linarith)
    (by
      apply inv_sub_differentiableOn
      intro w hw
      apply hne
      left
      have := hw.1
      rw [uIcc_of_le (by linarith)] at this
      have := this.1
      intro h
      linarith)
    (by
      apply inv_sub_differentiableOn
      intro w hw
      apply hne
      right
      have := hw.2
      rw [uIcc_of_le (by linarith)] at this
      have := this.2
      intro h
      linarith)
    (by
      apply inv_sub_differentiableOn
      intro w hw
      apply hne
      right
      have := hw.2
      rw [uIcc_of_le (by linarith)] at this
      have := this.1
      intro h
      linarith)
  rw [hex]
  exact rect_inv_square z s hs

theorem rect_edges_integrable_of_continuousOn (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : ContinuousOn f (uIcc a b ×ℂ uIcc c d)) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume a b ∧
    IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume c d ∧
    IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) volume c d := by
  have hH : ∀ y ∈ uIcc c d, ContinuousOn (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I))
      (uIcc a b) := by
    intro y hy
    refine hf.comp (by fun_prop) fun x hx => ?_
    exact ⟨by simpa using hx, by simpa using hy⟩
  have hV : ∀ x ∈ uIcc a b, ContinuousOn (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I))
      (uIcc c d) := by
    intro x hx
    refine hf.comp (by fun_prop) fun y hy => ?_
    exact ⟨by simpa using hx, by simpa using hy⟩
  exact ⟨(hH c left_mem_uIcc).intervalIntegrable, (hH d right_mem_uIcc).intervalIntegrable,
    (hV a left_mem_uIcc).intervalIntegrable, (hV b right_mem_uIcc).intervalIntegrable⟩

theorem rectIntegral_congr_boundary (f g : ℂ → ℂ) (a b c d : ℝ)
    (hH : ∀ x ∈ uIcc a b, f ((x : ℂ) + (c : ℂ) * Complex.I) = g ((x : ℂ) + (c : ℂ) * Complex.I) ∧
      f ((x : ℂ) + (d : ℂ) * Complex.I) = g ((x : ℂ) + (d : ℂ) * Complex.I))
    (hV : ∀ y ∈ uIcc c d, f ((a : ℂ) + (y : ℂ) * Complex.I) = g ((a : ℂ) + (y : ℂ) * Complex.I) ∧
      f ((b : ℂ) + (y : ℂ) * Complex.I) = g ((b : ℂ) + (y : ℂ) * Complex.I)) :
    rectIntegral f a b c d = rectIntegral g a b c d := by
  unfold rectIntegral
  rw [intervalIntegral.integral_congr (fun x hx => (hH x hx).1),
    intervalIntegral.integral_congr (fun x hx => (hH x hx).2),
    intervalIntegral.integral_congr (fun y hy => (hV y hy).1),
    intervalIntegral.integral_congr (fun y hy => (hV y hy).2)]

theorem rectIntegral_add_const_mul (g k : ℂ → ℂ) (κ : ℂ) (a b c d : ℝ)
    (hg1 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b)
    (hg2 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (d : ℂ) * Complex.I)) volume a b)
    (hg3 : IntervalIntegrable (fun y : ℝ => g ((a : ℂ) + (y : ℂ) * Complex.I)) volume c d)
    (hg4 : IntervalIntegrable (fun y : ℝ => g ((b : ℂ) + (y : ℂ) * Complex.I)) volume c d)
    (hk1 : IntervalIntegrable (fun x : ℝ => k ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b)
    (hk2 : IntervalIntegrable (fun x : ℝ => k ((x : ℂ) + (d : ℂ) * Complex.I)) volume a b)
    (hk3 : IntervalIntegrable (fun y : ℝ => k ((a : ℂ) + (y : ℂ) * Complex.I)) volume c d)
    (hk4 : IntervalIntegrable (fun y : ℝ => k ((b : ℂ) + (y : ℂ) * Complex.I)) volume c d) :
    rectIntegral (fun w => g w + κ * k w) a b c d =
      rectIntegral g a b c d + κ * rectIntegral k a b c d := by
  unfold rectIntegral
  rw [intervalIntegral.integral_add hg1 (hk1.const_mul κ),
    intervalIntegral.integral_add hg2 (hk2.const_mul κ),
    intervalIntegral.integral_add hg3 (hk3.const_mul κ),
    intervalIntegral.integral_add hg4 (hk4.const_mul κ)]
  simp only [intervalIntegral.integral_const_mul]
  ring

theorem rectangular_cauchy_formula (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : DifferentiableOn ℂ f (Icc a b ×ℂ Icc c d))
    (z : ℂ) (hz : z ∈ Ioo a b ×ℂ Ioo c d) :
    rectIntegral (fun w => f w / (w - z)) a b c d =
      (2 * Real.pi * Complex.I) * f z := by
  obtain ⟨⟨hza, hzb⟩, ⟨hzc, hzd⟩⟩ := hz
  have hab : a < b := hza.trans hzb
  have hcd : c < d := hzc.trans hzd
  have hzmem : z ∈ Ioo a b ×ℂ Ioo c d := ⟨⟨hza, hzb⟩, ⟨hzc, hzd⟩⟩
  have hnhds : Icc a b ×ℂ Icc c d ∈ 𝓝 z := by
    refine Filter.mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hzmem) ?_
    intro w hw
    exact ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩
  have hfz : DifferentiableAt ℂ f z := hf.differentiableAt hnhds
  set g := dslope f z with hg
  have hgc : ContinuousOn g (Icc a b ×ℂ Icc c d) := by
    intro w hw
    by_cases hwz : w = z
    · subst hwz
      exact (continuousAt_dslope_same.2 hfz).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne hwz).2 (hf.continuousOn w hw)
  have hgc' : ContinuousOn g (uIcc a b ×ℂ uIcc c d) := by
    rwa [uIcc_of_le hab.le, uIcc_of_le hcd.le]
  -- zero integral of g
  have hzero : rectIntegral g a b c d = 0 := by
    have hre0 : ((a : ℂ) + (c : ℂ) * Complex.I).re = a := by simp
    have him0 : ((a : ℂ) + (c : ℂ) * Complex.I).im = c := by simp
    have hre1 : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by simp
    have him1 : ((b : ℂ) + (d : ℂ) * Complex.I).im = d := by simp
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable g
      ((a : ℂ) + (c : ℂ) * Complex.I) ((b : ℂ) + (d : ℂ) * Complex.I) {z}
      (Set.countable_singleton z)
      (by rw [hre0, him0, hre1, him1]; exact hgc')
      (by
        intro x hx
        rw [hre0, him0, hre1, him1, min_eq_left hab.le, max_eq_right hab.le,
          min_eq_left hcd.le, max_eq_right hcd.le] at hx
        have hxz : x ≠ z := hx.2
        have hxf : DifferentiableAt ℂ f x :=
          hf.differentiableAt (Filter.mem_of_superset
            ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1)
            (fun w hw => ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩))
        exact (differentiableAt_dslope_of_ne hxz).2 hxf)
    rw [hre0, him0, hre1, him1] at h
    simpa [rectIntegral, smul_eq_mul] using h
  -- edges of g
  obtain ⟨hg1, hg2, hg3, hg4⟩ := rect_edges_integrable_of_continuousOn g a b c d hgc'
  -- edges of the Cauchy kernel
  have hkH : ∀ y : ℝ, y ≠ z.im → IntervalIntegrable
      (fun x : ℝ => (((x : ℂ) + (y : ℂ) * Complex.I) - z)⁻¹) volume a b := by
    intro y hy
    refine Continuous.intervalIntegrable ?_ _ _
    apply Continuous.inv₀ (by fun_prop)
    intro x h
    have := congrArg Complex.im h
    simp at this
    exact hy (by linarith)
  have hkV : ∀ x : ℝ, x ≠ z.re → IntervalIntegrable
      (fun y : ℝ => (((x : ℂ) + (y : ℂ) * Complex.I) - z)⁻¹) volume c d := by
    intro x hx
    refine Continuous.intervalIntegrable ?_ _ _
    apply Continuous.inv₀ (by fun_prop)
    intro y h
    have := congrArg Complex.re h
    simp at this
    exact hx (by linarith)
  have hcz : c ≠ z.im := hzc.ne
  have hdz : d ≠ z.im := hzd.ne'
  have haz : a ≠ z.re := hza.ne
  have hbz : b ≠ z.re := hzb.ne'
  -- pointwise identity on the boundary
  have hid : ∀ w : ℂ, w ≠ z → f w / (w - z) = g w + f z * (w - z)⁻¹ := by
    intro w hw
    have hw' : w - z ≠ 0 := sub_ne_zero.mpr hw
    simp only [hg, dslope_of_ne f hw, slope_def_field]
    field_simp
    ring
  have hcongr : rectIntegral (fun w => f w / (w - z)) a b c d =
      rectIntegral (fun w => g w + f z * (w - z)⁻¹) a b c d := by
    apply rectIntegral_congr_boundary
    · intro x _
      constructor
      · apply hid
        intro h
        exact hcz (by have := congrArg Complex.im h; simpa using this)
      · apply hid
        intro h
        exact hdz (by have := congrArg Complex.im h; simpa using this)
    · intro y _
      constructor
      · apply hid
        intro h
        exact haz (by have := congrArg Complex.re h; simpa using this)
      · apply hid
        intro h
        exact hbz (by have := congrArg Complex.re h; simpa using this)
  rw [hcongr, rectIntegral_add_const_mul g (fun w => (w - z)⁻¹) (f z) a b c d hg1 hg2 hg3 hg4
    (hkH c hcz) (hkH d hdz) (hkV a haz) (hkV b hbz), hzero,
    rectIntegral_inv a b c d z hzmem]
  ring

/-! ### 15.18 -/

theorem ordered_collar_frame_aux {n : ℕ} (hn : 0 < n)
    (S : RealSlits n) (δ : ℝ)
    (hsep : ∀ i j : Fin n, i ≠ j → S.b i + 2 * δ < S.a j ∨ S.b j + 2 * δ < S.a i)
    (R : ℝ) (hsize : ∀ i : Fin n, |S.a i| + 1 < R ∧ |S.b i| + 1 < R)
    (ε : ℝ) (hε0 : 0 < ε) (hεδ : ε < δ) (hε1 : ε < 1) :
    ∃ x : Fin (n + 1) → ℝ, StrictMono x ∧
        x 0 = -R ∧ x (Fin.last n) = R ∧
        ∀ i : Fin n,
          x i.castSucc < S.a (Tuple.sort S.a i) - ε ∧
          S.b (Tuple.sort S.a i) + ε < x i.succ := by
  set e : Equiv.Perm (Fin n) := Tuple.sort S.a with he
  have hmono : Monotone (S.a ∘ e) := Tuple.monotone_sort S.a
  have hgap : ∀ i j : Fin n, i < j → S.b (e i) + 2 * ε < S.a (e j) := by
    intro i j hij
    have hne : e i ≠ e j := fun h => (ne_of_lt hij) (e.injective h)
    have hle : S.a (e i) ≤ S.a (e j) := hmono hij.le
    rcases hsep (e i) (e j) hne with h | h
    · linarith
    · have h1 := S.le (e j)
      have h2 := S.le (e i)
      linarith
  let A : ℕ → ℝ := fun k => if h : k < n then S.a (e ⟨k, h⟩) else 0
  let B : ℕ → ℝ := fun k => if h : k < n then S.b (e ⟨k, h⟩) else 0
  let sep : ℕ → ℝ := fun k => if k = 0 then -R else if k = n then R else (B (k - 1) + A k) / 2
  have hA : ∀ i : Fin n, A i.val = S.a (e i) := fun i => by simp [A, i.isLt]
  have hB : ∀ i : Fin n, B i.val = S.b (e i) := fun i => by simp [B, i.isLt]
  have hn0 : n ≠ 0 := hn.ne'
  have P1 : ∀ i : Fin n, sep i.val < S.a (e i) - ε := by
    intro i
    by_cases h0 : i.val = 0
    · simp only [sep, h0, if_true]
      have := hsize (e i)
      have h3 := neg_abs_le (S.a (e i))
      linarith
    · have hni : i.val ≠ n := i.isLt.ne
      simp only [sep, h0, hni, if_false]
      have hlt : (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n) < i := by
        rw [Fin.lt_def]; simp only; omega
      have hg := hgap _ _ hlt
      have e1 : B (i.val - 1) = S.b (e ⟨i.val - 1, by have := i.isLt; omega⟩) := by
        simp only [B]; rw [dif_pos (by have := i.isLt; omega)]
      rw [e1, hA i]
      linarith
  have P2 : ∀ i : Fin n, S.b (e i) + ε < sep (i.val + 1) := by
    intro i
    by_cases hl : i.val + 1 = n
    · simp only [sep, hl, hn0, if_true, if_false]
      have := hsize (e i)
      have h3 := le_abs_self (S.b (e i))
      linarith
    · have hlt' : i.val + 1 < n := lt_of_le_of_ne i.isLt hl
      simp only [sep, hl, if_false, Nat.succ_ne_zero, Nat.add_sub_cancel]
      have hlt : i < (⟨i.val + 1, hlt'⟩ : Fin n) := by
        rw [Fin.lt_def]; simp only; omega
      have hg := hgap _ _ hlt
      have e1 : A (i.val + 1) = S.a (e ⟨i.val + 1, hlt'⟩) := by simp [A, hlt']
      rw [e1, hB i]
      linarith
  refine ⟨fun k => sep k.val, ?_, ?_, ?_, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.2
    intro i
    simp only [Fin.val_castSucc, Fin.val_succ]
    have h1 := P1 i
    have h2 := P2 i
    have h3 := S.le (e i)
    linarith
  · simp [sep]
  · simp [sep, hn0]
  · intro i
    refine ⟨?_, ?_⟩
    · simpa using P1 i
    · simpa using P2 i

theorem exists_ordered_collar_frame {n : ℕ} (hn : 0 < n)
    (S : RealSlits n) (R : ℝ) (hR : 0 < R)
    (hsize : ∀ i : Fin n, |S.a i| + 1 < R ∧ |S.b i| + 1 < R) :
    ∃ e : Fin n ≃ Fin n, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ x : Fin (n + 1) → ℝ, StrictMono x ∧
        x 0 = -R ∧ x (Fin.last n) = R ∧
        ∀ i : Fin n,
          x i.castSucc < S.a (e i) - ε ∧
          S.b (e i) + ε < x i.succ := by
  obtain ⟨-, -, δ, hδ, hsep⟩ := slits_compact_and_separated S
  refine ⟨Tuple.sort S.a, min δ 1, lt_min hδ one_pos, fun ε hε0 hεlt => ?_⟩
  exact ordered_collar_frame_aux hn S δ hsep R hsize ε hε0
    (lt_of_lt_of_le hεlt (min_le_left _ _)) (lt_of_lt_of_le hεlt (min_le_right _ _))

/-! ### 15.19 -/

theorem mem_carrier_exists {n : ℕ} (S : RealSlits n) (e : Fin n ≃ Fin n) {w : ℂ}
    (hw : w ∈ S.carrier) :
    ∃ j : Fin n, ∃ t ∈ Icc (S.a (e j)) (S.b (e j)), w = (t : ℂ) := by
  obtain ⟨i, ⟨t, ht, rfl⟩⟩ := mem_iUnion.mp hw
  obtain ⟨j, rfl⟩ := e.surjective i
  exact ⟨j, t, ht, rfl⟩

theorem slit_cell {n : ℕ} (S : RealSlits n) (e : Fin n ≃ Fin n) (x : Fin (n + 1) → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hxi : ∀ i : Fin n, x i.castSucc < S.a (e i) - ε ∧ S.b (e i) + ε < x i.succ)
    (j : Fin n) {t : ℝ} (ht : t ∈ Icc (S.a (e j)) (S.b (e j))) :
    x j.castSucc < t ∧ t < x j.succ := by
  obtain ⟨h1, h2⟩ := hxi j
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem left_strip_avoids {n : ℕ} (S : RealSlits n) (e : Fin n ≃ Fin n) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (ε : ℝ) (hε : 0 < ε)
    (hxi : ∀ i : Fin n, x i.castSucc < S.a (e i) - ε ∧ S.b (e i) + ε < x i.succ)
    (k : Fin n) (w : ℂ) (h1 : x k.castSucc ≤ w.re) (h2 : w.re ≤ S.a (e k) - ε) :
    w ∉ S.carrier := by
  intro hw
  obtain ⟨j, t, ht, rfl⟩ := mem_carrier_exists S e hw
  simp only [Complex.ofReal_re] at h1 h2
  have hc := slit_cell S e x ε hε hxi j ht
  have hk := hxi k
  have hle := S.le (e k)
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · have hj := Fin.lt_def.1 hjk
    have : x j.succ ≤ x k.castSucc := hx.monotone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
    linarith [hc.2]
  · subst hjk
    linarith [ht.1]
  · have hj := Fin.lt_def.1 hjk
    have : x k.succ ≤ x j.castSucc := hx.monotone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
    linarith [hc.1]

theorem right_strip_avoids {n : ℕ} (S : RealSlits n) (e : Fin n ≃ Fin n) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (ε : ℝ) (hε : 0 < ε)
    (hxi : ∀ i : Fin n, x i.castSucc < S.a (e i) - ε ∧ S.b (e i) + ε < x i.succ)
    (k : Fin n) (w : ℂ) (h1 : S.b (e k) + ε ≤ w.re) (h2 : w.re ≤ x k.succ) :
    w ∉ S.carrier := by
  intro hw
  obtain ⟨j, t, ht, rfl⟩ := mem_carrier_exists S e hw
  simp only [Complex.ofReal_re] at h1 h2
  have hc := slit_cell S e x ε hε hxi j ht
  have hk := hxi k
  have hle := S.le (e k)
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · have hj := Fin.lt_def.1 hjk
    have : x j.succ ≤ x k.castSucc := hx.monotone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
    linarith [hc.2]
  · subst hjk
    linarith [ht.2]
  · have hj := Fin.lt_def.1 hjk
    have : x k.succ ≤ x j.castSucc := hx.monotone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
    linarith [hc.1]

theorem lower_frame_identity {n : ℕ} (hn : 0 < n) (S : RealSlits n)
    (D : SlitHolomorphicData S) (z : ℂ)
    (R ε c d : ℝ) (hε : 0 < ε) (e : Fin n ≃ Fin n) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (hx0 : x 0 = -R) (hxl : x (Fin.last n) = R)
    (hxi : ∀ i : Fin n, x i.castSucc < S.a (e i) - ε ∧ S.b (e i) + ε < x i.succ)
    (hc : c ≤ -ε) (hd : ε ≤ d) (hz : z.im < c ∨ d < z.im) :
    rectIntegral (fun w => D.F w / (w - z)) (-R) R c d = collarIntegral S D.F z ε := by
  have hcd : c ≤ d := by linarith
  let a' : ℕ → ℝ := fun k => if h : k < n + 1 then x ⟨k, h⟩ else 0
  let l' : ℕ → ℝ := fun k => (if h : k < n then S.a (e ⟨k, h⟩) else 0) - ε
  let r' : ℕ → ℝ := fun k => (if h : k < n then S.b (e ⟨k, h⟩) else 0) + ε
  let lo' : ℕ → ℝ := fun _ => -ε
  let hi' : ℕ → ℝ := fun _ => ε
  have ha' : ∀ k : ℕ, ∀ h : k < n + 1, a' k = x ⟨k, h⟩ := fun k h => by
    simp only [a']; rw [dif_pos h]
  have hl' : ∀ i : Fin n, l' i.val = S.a (e i) - ε := fun i => by
    simp only [l']; rw [dif_pos i.isLt]
  have hr' : ∀ i : Fin n, r' i.val = S.b (e i) + ε := fun i => by
    simp only [r']; rw [dif_pos i.isLt]
  have hdiff : ∀ U : Set ℂ, (∀ w ∈ U, w ∉ S.carrier) → (∀ w ∈ U, w ≠ z) →
      DifferentiableOn ℂ (fun w => D.F w / (w - z)) U := by
    intro U h1 h2
    exact (D.holomorphic.mono (fun w hw => h1 w hw)).div (differentiableOn_id.sub_const z)
      (fun w hw => sub_ne_zero.mpr (h2 w hw))
  have hzband : ∀ w : ℂ, c ≤ w.im → w.im ≤ d → w ≠ z := by
    intro w h1 h2 hw
    rw [hw] at h1 h2
    rcases hz with h | h <;> linarith
  have hleft : ∀ k < n, DifferentiableOn ℂ (fun w => D.F w / (w - z))
      (uIcc (a' k) (l' k) ×ℂ uIcc c d) := by
    intro k hk
    have hak : a' k = x (Fin.castSucc ⟨k, hk⟩) := by rw [ha' k (by omega)]; rfl
    have hlk : l' k = S.a (e ⟨k, hk⟩) - ε := hl' ⟨k, hk⟩
    have hlt : a' k ≤ l' k := by rw [hak, hlk]; exact (hxi ⟨k, hk⟩).1.le
    apply hdiff
    · intro w hw
      have h1 := hw.1
      rw [uIcc_of_le hlt] at h1
      exact left_strip_avoids S e x hx ε hε hxi ⟨k, hk⟩ w (by rw [← hak]; exact h1.1)
        (by rw [← hlk]; exact h1.2)
    · intro w hw
      have h2 := hw.2
      rw [uIcc_of_le hcd] at h2
      exact hzband w h2.1 h2.2
  have hright : ∀ k < n, DifferentiableOn ℂ (fun w => D.F w / (w - z))
      (uIcc (r' k) (a' (k + 1)) ×ℂ uIcc c d) := by
    intro k hk
    have hak : a' (k + 1) = x (Fin.succ ⟨k, hk⟩) := by rw [ha' (k + 1) (by omega)]; rfl
    have hrk : r' k = S.b (e ⟨k, hk⟩) + ε := hr' ⟨k, hk⟩
    have hlt : r' k ≤ a' (k + 1) := by rw [hak, hrk]; exact (hxi ⟨k, hk⟩).2.le
    apply hdiff
    · intro w hw
      have h1 := hw.1
      rw [uIcc_of_le hlt] at h1
      exact right_strip_avoids S e x hx ε hε hxi ⟨k, hk⟩ w (by rw [← hrk]; exact h1.1)
        (by rw [← hak]; exact h1.2)
    · intro w hw
      have h2 := hw.2
      rw [uIcc_of_le hcd] at h2
      exact hzband w h2.1 h2.2
  have hbottom : ∀ k < n, DifferentiableOn ℂ (fun w => D.F w / (w - z))
      (uIcc (l' k) (r' k) ×ℂ uIcc c (lo' k)) := by
    intro k hk
    apply hdiff
    · intro w hw hwc
      have h2 := hw.2
      have h2' : c ≤ -ε := hc
      rw [uIcc_of_le h2'] at h2
      have := carrier_im_eq_zero S hwc
      linarith [h2.2]
    · intro w hw
      have h2 := hw.2
      have h2' : c ≤ -ε := hc
      rw [uIcc_of_le h2'] at h2
      exact hzband w h2.1 (by linarith [h2.2])
  have htop : ∀ k < n, DifferentiableOn ℂ (fun w => D.F w / (w - z))
      (uIcc (l' k) (r' k) ×ℂ uIcc (hi' k) d) := by
    intro k hk
    apply hdiff
    · intro w hw hwc
      have h2 := hw.2
      have h2' : ε ≤ d := hd
      rw [uIcc_of_le h2'] at h2
      have := carrier_im_eq_zero S hwc
      linarith [h2.1]
    · intro w hw
      have h2 := hw.2
      have h2' : ε ≤ d := hd
      rw [uIcc_of_le h2'] at h2
      exact hzband w (by linarith [h2.1]) h2.2
  have hex := finite_rectangular_frame_excision (fun w => D.F w / (w - z)) n a' l' r' lo' hi'
    c d (fun k _ => hc) (fun k _ => by simp only [lo', hi']; linarith) (fun k _ => hd)
    hleft hright hbottom htop
  have ha0 : a' 0 = -R := by rw [ha' 0 (by omega)]; exact hx0
  have han : a' n = R := by rw [ha' n (by omega)]; exact hxl
  rw [ha0, han] at hex
  rw [hex, Finset.sum_range]
  unfold collarIntegral
  rw [← Equiv.sum_comp e (fun j => rectIntegral (fun w => D.F w / (w - z))
    (S.a j - ε) (S.b j + ε) (-ε) ε)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hl' i, hr' i, lo', hi']

theorem kappa_comp_continuous_of_notin {n : ℕ} (S : RealSlits n) (D : SlitHolomorphicData S)
    (z : ℂ) (p : ℝ → ℂ) (hp : Continuous p) (hw : ∀ x, p x ∉ S.carrier) (hz : ∀ x, p x ≠ z) :
    Continuous (fun x : ℝ => D.F (p x) / (p x - z)) := by
  have hopen : IsOpen S.carrierᶜ := (slits_compact_and_separated S).2.1
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hw' : p x ∈ S.carrierᶜ := hw x
  have h1 : ContinuousAt D.F (p x) :=
    (D.holomorphic.differentiableAt (hopen.mem_nhds hw')).continuousAt
  have h2 : ContinuousAt (fun w : ℂ => D.F w / (w - z)) (p x) :=
    h1.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr (hz x))
  exact h2.comp hp.continuousAt

theorem carrier_re_lt {n : ℕ} (S : RealSlits n) (R : ℝ)
    (hsize : ∀ i : Fin n, |S.a i| + 1 < R ∧ |S.b i| + 1 < R) {w : ℂ} (hw : w ∈ S.carrier) :
    |w.re| < R := by
  obtain ⟨i, ⟨t, ht, rfl⟩⟩ := mem_iUnion.mp hw
  have h1 := hsize i
  have h2 := neg_abs_le (S.a i)
  have h3 := le_abs_self (S.b i)
  simp only [Complex.ofReal_re]
  rw [abs_lt]
  constructor <;> linarith [ht.1, ht.2, abs_nonneg (S.a i), abs_nonneg (S.b i)]

theorem nonreal_outer_collar_identity {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ ε₀ R₀ : ℝ, 0 < ε₀ ∧ 0 < R₀ ∧
      ∀ ε R : ℝ, 0 < ε → ε < ε₀ → R₀ ≤ R →
        rectIntegral (fun w => D.F w / (w - z)) (-R) R (-R) R =
          collarIntegral S D.F z ε +
            (2 * Real.pi * Complex.I) * D.F z := by
  obtain ⟨-, -, δ, hδ, hsep⟩ := slits_compact_and_separated S
  have hzim : 0 < |z.im| := abs_pos.mpr hz
  refine ⟨min (min δ 1) (|z.im| / 2),
    |z.re| + |z.im| + ∑ i : Fin n, (|S.a i| + |S.b i|) + 2,
    lt_min (lt_min hδ one_pos) (by positivity), by positivity, ?_⟩
  intro ε R hε0 hεlt hRR
  have hεδ : ε < δ := lt_of_lt_of_le hεlt ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 := lt_of_lt_of_le hεlt ((min_le_left _ _).trans (min_le_right _ _))
  have hεz : ε < |z.im| / 2 := lt_of_lt_of_le hεlt (min_le_right _ _)
  have hsum : 0 ≤ ∑ i : Fin n, (|S.a i| + |S.b i|) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hRz1 : |z.re| < R := by linarith [abs_nonneg z.im]
  have hRz2 : |z.im| < R := by linarith [abs_nonneg z.re]
  have hsize : ∀ i : Fin n, |S.a i| + 1 < R ∧ |S.b i| + 1 < R := by
    intro i
    have h := Finset.single_le_sum (f := fun i : Fin n => |S.a i| + |S.b i|)
      (fun i _ => by positivity) (Finset.mem_univ i)
    constructor <;> linarith [abs_nonneg (S.a i), abs_nonneg (S.b i), abs_nonneg z.re,
      abs_nonneg z.im]
  have hR1 : 1 < R := by linarith [abs_nonneg z.re, abs_nonneg z.im]
  have hopen : IsOpen S.carrierᶜ := (slits_compact_and_separated S).2.1
  -- vertical edges are integrable (continuous)
  have hvert : ∀ x0 : ℝ, |x0| = R → ∀ p q : ℝ, IntervalIntegrable
      (fun y : ℝ => D.F ((x0 : ℂ) + (y : ℂ) * Complex.I) /
        (((x0 : ℂ) + (y : ℂ) * Complex.I) - z)) volume p q := by
    intro x0 hx0 p q
    refine Continuous.intervalIntegrable ?_ p q
    refine kappa_comp_continuous_of_notin S D z (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) (fun y hw => ?_) (fun y h => ?_)
    · have := carrier_re_lt S R hsize hw
      simp at this
      linarith
    · have := congrArg Complex.re h
      simp at this
      rw [this] at hx0
      linarith
  have hvR := hvert R (abs_of_pos (by linarith))
  have hvL := hvert (-R) (by rw [abs_neg, abs_of_pos (by linarith)])
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- no slits
    subst hn0
    have hcar : S.carrier = ∅ := by
      simp [RealSlits.carrier]
    have hf : DifferentiableOn ℂ D.F (Icc (-R) R ×ℂ Icc (-R) R) := by
      apply D.holomorphic.mono
      intro w _
      simp [hcar]
    have := rectangular_cauchy_formula D.F (-R) R (-R) R hf z
      ⟨⟨(abs_lt.1 hRz1).1, (abs_lt.1 hRz1).2⟩,
        ⟨(abs_lt.1 hRz2).1, (abs_lt.1 hRz2).2⟩⟩
    rw [this]
    simp [collarIntegral]
  · by_cases hpos : 0 < z.im
    · have hzabs : |z.im| = z.im := abs_of_pos hpos
      set m : ℝ := z.im / 2 with hm
      obtain ⟨x, hx, hx0, hxl, hxi⟩ := ordered_collar_frame_aux hn S δ hsep R hsize ε hε0 hεδ hε1
      have hlow := lower_frame_identity hn S D z R ε (-R) m hε0 (Tuple.sort S.a) x hx hx0 hxl hxi
        (by linarith) (by rw [hzabs] at hεz; linarith) (Or.inr (by rw [hm]; linarith))
      have hupf : DifferentiableOn ℂ D.F (Icc (-R) R ×ℂ Icc m R) := by
        apply D.holomorphic.mono
        intro w hw hwc
        have := carrier_im_eq_zero S hwc
        have := hw.2.1
        linarith
      have hup := rectangular_cauchy_formula D.F (-R) R m R hupf z
        ⟨⟨(abs_lt.1 hRz1).1, (abs_lt.1 hRz1).2⟩,
          ⟨by rw [hm]; linarith, by have := (abs_lt.1 hRz2).2; linarith⟩⟩
      rw [rectIntegral_vertical_split (fun w => D.F w / (w - z)) (-R) R (-R) m R (hvR (-R) m) (hvR m R) (hvL (-R) m) (hvL m R),
        hlow, hup]
    · have hneg : z.im < 0 := lt_of_le_of_ne (not_lt.1 hpos) hz
      have hzabs : |z.im| = -z.im := abs_of_neg hneg
      set m : ℝ := z.im / 2 with hm
      obtain ⟨x, hx, hx0, hxl, hxi⟩ := ordered_collar_frame_aux hn S δ hsep R hsize ε hε0 hεδ hε1
      have hlowf : DifferentiableOn ℂ D.F (Icc (-R) R ×ℂ Icc (-R) m) := by
        apply D.holomorphic.mono
        intro w hw hwc
        have := carrier_im_eq_zero S hwc
        have := hw.2.2
        linarith
      have hlow := rectangular_cauchy_formula D.F (-R) R (-R) m hlowf z
        ⟨⟨(abs_lt.1 hRz1).1, (abs_lt.1 hRz1).2⟩,
          ⟨by have := (abs_lt.1 hRz2).1; linarith, by rw [hm]; linarith⟩⟩
      have hup := lower_frame_identity hn S D z R ε m R hε0 (Tuple.sort S.a) x hx hx0 hxl hxi
        (by rw [hzabs] at hεz; rw [hm]; linarith) (by linarith) (Or.inl (by rw [hm]; linarith))
      rw [rectIntegral_vertical_split (fun w => D.F w / (w - z)) (-R) R (-R) m R (hvR (-R) m) (hvR m R) (hvL (-R) m) (hvL m R),
        hlow, hup]
      ring

/-! ### 15.20, 15.21, 15.23, 15.24 -/

theorem kappa_continuousAt {n : ℕ} (S : RealSlits n) (D : SlitHolomorphicData S) (z w : ℂ)
    (hw : w ∉ S.carrier) (hwz : w ≠ z) :
    ContinuousAt (fun w : ℂ => D.F w / (w - z)) w := by
  have hopen : IsOpen S.carrierᶜ := (slits_compact_and_separated S).2.1
  have h1 : ContinuousAt D.F w :=
    (D.holomorphic.differentiableAt (hopen.mem_nhds hw)).continuousAt
  exact h1.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hwz)

theorem segment_im_const {p q : ℂ} {c : ℝ} (hp : p.im = c) (hq : q.im = c) :
    segment ℝ p q ⊆ {w : ℂ | w.im = c} := by
  rintro w ⟨a, b, ha, hb, hab, rfl⟩
  simp only [Set.mem_setOf_eq, Complex.add_im, Complex.smul_im, smul_eq_mul, hp, hq]
  rw [← add_mul, hab, one_mul]

theorem segment_re_const {p q : ℂ} {c : ℝ} (hp : p.re = c) (hq : q.re = c) :
    segment ℝ p q ⊆ {w : ℂ | w.re = c} := by
  rintro w ⟨a, b, ha, hb, hab, rfl⟩
  simp only [Set.mem_setOf_eq, Complex.add_re, Complex.smul_re, smul_eq_mul, hp, hq]
  rw [← add_mul, hab, one_mul]

theorem rectLoop_range_subset (R : ℝ) :
    range (rectangleLoop (-R) R (-R) R) ⊆ {w : ℂ | w.im = -R ∨ w.re = R ∨ w.im = R ∨ w.re = -R} := by
  simp only [rectangleLoop, Path.trans_range, Path.range_segment]
  rintro w (((h | h) | h) | h)
  · left
    exact segment_im_const (by simp) (by simp) h
  · right; left
    exact segment_re_const (by simp) (by simp) h
  · right; right; left
    exact segment_im_const (by simp) (by simp) h
  · right; right; right
    exact segment_re_const (by simp) (by simp) h

theorem outer_loop_continuousOn {n : ℕ} (S : RealSlits n) (D : SlitHolomorphicData S) (z : ℂ)
    (R : ℝ) (hR : 0 < R) (hsize : ∀ i : Fin n, |S.a i| + 1 < R ∧ |S.b i| + 1 < R)
    (hz1 : |z.re| < R) (hz2 : |z.im| < R) :
    ContinuousOn (fun w => D.F w / (w - z)) (range (rectangleLoop (-R) R (-R) R)) := by
  intro w hw
  apply ContinuousAt.continuousWithinAt
  have hsub := rectLoop_range_subset R hw
  have hz1' := abs_lt.1 hz1
  have hz2' := abs_lt.1 hz2
  refine kappa_continuousAt S D z w ?_ ?_
  · intro hc
    have h := carrier_im_eq_zero S hc
    have h2 := carrier_re_lt S R hsize hc
    rcases hsub with h' | h' | h' | h'
    · rw [h] at h'; linarith
    · rw [h'] at h2; rw [abs_of_pos hR] at h2; linarith
    · rw [h] at h'; linarith
    · rw [h'] at h2; rw [abs_neg, abs_of_pos hR] at h2; linarith
  · intro hwz
    subst hwz
    rcases hsub with h' | h' | h' | h' <;> linarith [hz1'.1, hz1'.2, hz2'.1, hz2'.2]

theorem slit_cauchy_representation_nonreal {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) (z : ℂ) (hz : z.im ≠ 0) :
    D.F z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      jumpIntegral S D.jump z := by
  have hznot : z ∉ S.carrier := fun h => hz (carrier_im_eq_zero S h)
  obtain ⟨ε₀, R₀, hε₀, hR₀, hid⟩ := nonreal_outer_collar_identity S D z hz
  have hcol := collars_tendsto S D z hznot
  set R₁ : ℝ := |z.re| + |z.im| + ∑ i : Fin n, (|S.a i| + |S.b i|) + 2 with hR₁
  have hsum : 0 ≤ ∑ i : Fin n, (|S.a i| + |S.b i|) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hcont : ∃ R₂ : ℝ, ∀ R : ℝ, R₂ ≤ R →
      ContinuousOn (fun w => D.F w / (w - z)) (range (rectangleLoop (-R) R (-R) R)) := by
    refine ⟨R₁, fun R hR => ?_⟩
    have hsize : ∀ i : Fin n, |S.a i| + 1 < R ∧ |S.b i| + 1 < R := by
      intro i
      have h := Finset.single_le_sum (f := fun i : Fin n => |S.a i| + |S.b i|)
        (fun i _ => by positivity) (Finset.mem_univ i)
      constructor <;> linarith [abs_nonneg (S.a i), abs_nonneg (S.b i), abs_nonneg z.re,
        abs_nonneg z.im]
    exact outer_loop_continuousOn S D z R (by linarith [abs_nonneg z.re, abs_nonneg z.im])
      hsize (by linarith [abs_nonneg z.im]) (by linarith [abs_nonneg z.re])
  have hQ := outer_square_tendsto_zero D.F D.decay z hcont
  have hconst : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      collarIntegral S D.F z ε = -((2 * Real.pi * Complex.I) * D.F z) := by
    intro ε h1 h2
    have hev : ∀ᶠ R : ℝ in atTop,
        rectIntegral (fun w => D.F w / (w - z)) (-R) R (-R) R =
          collarIntegral S D.F z ε + (2 * Real.pi * Complex.I) * D.F z := by
      filter_upwards [eventually_ge_atTop R₀] with R hR
      exact hid ε R h1 h2 hR
    have hlim : Tendsto (fun R : ℝ => rectIntegral (fun w => D.F w / (w - z)) (-R) R (-R) R)
        atTop (𝓝 (collarIntegral S D.F z ε + (2 * Real.pi * Complex.I) * D.F z)) :=
      tendsto_const_nhds.congr' (hev.mono fun R h => h.symm)
    have := tendsto_nhds_unique hlim hQ
    linear_combination this
  have hlim2 : Tendsto (collarIntegral S D.F z) (𝓝[>] (0 : ℝ))
      (𝓝 (-((2 * Real.pi * Complex.I) * D.F z))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    exact (hconst ε hε.1 hε.2).symm
  have := tendsto_nhds_unique hcol hlim2
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  rw [neg_inj.1 this, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem slit_cauchy_representation {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) (z : ℂ) (hz : z ∉ S.carrier) :
    (∀ i : Fin n,
      IntervalIntegrable
        (fun t : ℝ => D.jump i t / ((t : ℂ) - z))
        volume (S.a i) (S.b i)) ∧
    D.F z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      jumpIntegral S D.jump z := by
  refine ⟨fun i => weighted_jump_intervalIntegrable S D z hz i, ?_⟩
  by_cases him : z.im = 0
  · -- approach z from above
    have hopen : IsOpen S.carrierᶜ := (slits_compact_and_separated S).2.1
    have hz' : z ∈ S.carrierᶜ := hz
    let zs : ℕ → ℂ := fun m => z + Complex.I * (((1 : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ)
    have hzs : Tendsto zs atTop (𝓝 z) := by
      have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun m : ℕ => z + Complex.I * (((1 : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ))
          atTop (𝓝 (z + Complex.I * ((0 : ℝ) : ℂ))) :=
        tendsto_const_nhds.add
          (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp h1))
      simp only [Complex.ofReal_zero, mul_zero, add_zero] at h2
      exact h2
    have hzsim : ∀ m : ℕ, (zs m).im ≠ 0 := by
      intro m
      have h : ∀ r : ℝ, (z + Complex.I * (r : ℂ)).im = r := by
        intro r; simp [him]
      show (z + Complex.I * (((1 : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ)).im ≠ 0
      rw [h]
      positivity
    have hF : Tendsto (fun m => D.F (zs m)) atTop (𝓝 (D.F z)) :=
      ((D.holomorphic.differentiableAt (hopen.mem_nhds hz')).continuousAt.tendsto).comp hzs
    have hJ : Tendsto (fun m => jumpIntegral S D.jump (zs m)) atTop
        (𝓝 (jumpIntegral S D.jump z)) :=
      (((continuousOn_jumpIntegral S D).continuousAt (hopen.mem_nhds hz')).tendsto).comp hzs
    have hlim := hF.congr fun m => slit_cauchy_representation_nonreal S D (zs m) (hzsim m)
    have hlim2 := hJ.const_mul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
    exact tendsto_nhds_unique hlim hlim2
  · exact slit_cauchy_representation_nonreal S D z him

theorem no_slits_zero (S : RealSlits 0) (D : SlitHolomorphicData S) :
    D.F = 0 := by
  funext z
  have hcar : S.carrier = ∅ := by simp [RealSlits.carrier]
  have h := (slit_cauchy_representation S D z (by simp [hcar])).2
  simp [jumpIntegral] at h
  simpa using h

theorem singleton_slit_removable {n : ℕ} (S : RealSlits n)
    (D : SlitHolomorphicData S) (i : Fin n)
    (hi : S.a i = S.b i) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F (ball (S.a i : ℂ) r) ∧
      EqOn F D.F (ball (S.a i : ℂ) r \ {(S.a i : ℂ)}) ∧
      ∀ z : ℂ, (∫ t : ℝ in (S.a i)..(S.b i),
        D.jump i t / ((t : ℂ) - z)) = 0 := by
  obtain ⟨-, -, δ, hδ, hsep⟩ := slits_compact_and_separated S
  have hsub : ball (S.a i : ℂ) δ \ {(S.a i : ℂ)} ⊆ S.carrierᶜ := by
    intro w hw hwc
    obtain ⟨⟨j, ⟨t, ht, rfl⟩⟩⟩ := (⟨mem_iUnion.mp hwc⟩ : Nonempty _)
    have hw1 := hw.1
    rw [mem_ball, Complex.dist_eq] at hw1
    have hw2 : (t : ℂ) ≠ (S.a i : ℂ) := hw.2
    by_cases hji : j = i
    · subst hji
      apply hw2
      have := S.le j
      have h1 := ht.1
      have h2 := ht.2
      have : t = S.a j := by linarith
      rw [this]
    · have hre : |t - S.a i| < δ := by
        have : ‖(t : ℂ) - (S.a i : ℂ)‖ = |t - S.a i| := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rwa [this] at hw1
      rcases hsep i j (Ne.symm hji) with h | h
      · have := ht.1; rw [abs_lt] at hre; linarith [hre.1, hre.2, S.le i]
      · have := ht.2; rw [abs_lt] at hre; linarith [hre.1, hre.2, S.le i]
  have hf : DifferentiableOn ℂ D.F (ball (S.a i : ℂ) δ \ {(S.a i : ℂ)}) :=
    D.holomorphic.mono hsub
  have hbound : HasEndpointBound D.F (ball (S.a i : ℂ) δ \ {(S.a i : ℂ)}) (S.a i : ℂ) := by
    obtain ⟨C, δ', hC, hδ', hB⟩ := D.endpoint_left i
    exact ⟨C, δ', hC, hδ', fun w hw => hB w (hsub hw)⟩
  obtain ⟨F, hFd, hFe⟩ := square_root_bound_removable D.F (S.a i : ℂ) δ hδ hf hbound
  refine ⟨δ, hδ, F, hFd, hFe, fun z => ?_⟩
  rw [← hi]
  simp

/-! ### 15.14 -/

theorem lineMap_horizontal (u v h t : ℝ) :
    AffineMap.lineMap ((u : ℂ) + (h : ℂ) * Complex.I) ((v : ℂ) + (h : ℂ) * Complex.I) t =
      (((v - u) * t + u : ℝ) : ℂ) + (h : ℂ) * Complex.I := by
  rw [AffineMap.lineMap_apply]
  simp only [Complex.real_smul, vsub_eq_sub, vadd_eq_add]
  push_cast
  ring

theorem lineMap_vertical (w u v t : ℝ) :
    AffineMap.lineMap ((w : ℂ) + (u : ℂ) * Complex.I) ((w : ℂ) + (v : ℂ) * Complex.I) t =
      (w : ℂ) + (((v - u) * t + u : ℝ) : ℂ) * Complex.I := by
  rw [AffineMap.lineMap_apply]
  simp only [Complex.real_smul, vsub_eq_sub, vadd_eq_add]
  push_cast
  ring

theorem seg_horizontal_integral (f : ℂ → ℂ) (u v h : ℝ) :
    ∫ t : ℝ in (0 : ℝ)..1,
      f (AffineMap.lineMap ((u : ℂ) + (h : ℂ) * Complex.I) ((v : ℂ) + (h : ℂ) * Complex.I) t) *
        (((v : ℂ) + (h : ℂ) * Complex.I) - ((u : ℂ) + (h : ℂ) * Complex.I)) =
      ∫ x : ℝ in u..v, f ((x : ℂ) + (h : ℂ) * Complex.I) := by
  by_cases hv : v = u
  · subst hv
    simp
  · have hne : (v - u) ≠ 0 := sub_ne_zero.mpr hv
    have e1 : ∀ t : ℝ, f (AffineMap.lineMap ((u : ℂ) + (h : ℂ) * Complex.I)
        ((v : ℂ) + (h : ℂ) * Complex.I) t) *
          (((v : ℂ) + (h : ℂ) * Complex.I) - ((u : ℂ) + (h : ℂ) * Complex.I)) =
        (fun x : ℝ => f ((x : ℂ) + (h : ℂ) * Complex.I)) ((v - u) * t + u) * ((v - u : ℝ) : ℂ) := by
      intro t
      rw [lineMap_horizontal]
      push_cast
      ring_nf
    simp only [e1]
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_comp_mul_add (fun x : ℝ => f ((x : ℂ) + (h : ℂ) * Complex.I)) hne u]
    simp only [mul_zero, zero_add, mul_one, Complex.real_smul]
    have : ((v - u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    push_cast at this ⊢
    rw [sub_add_cancel]
    field_simp

theorem seg_vertical_integral (f : ℂ → ℂ) (w u v : ℝ) :
    ∫ t : ℝ in (0 : ℝ)..1,
      f (AffineMap.lineMap ((w : ℂ) + (u : ℂ) * Complex.I) ((w : ℂ) + (v : ℂ) * Complex.I) t) *
        (((w : ℂ) + (v : ℂ) * Complex.I) - ((w : ℂ) + (u : ℂ) * Complex.I)) =
      Complex.I * ∫ y : ℝ in u..v, f ((w : ℂ) + (y : ℂ) * Complex.I) := by
  by_cases hv : v = u
  · subst hv
    simp
  · have hne : (v - u) ≠ 0 := sub_ne_zero.mpr hv
    have e1 : ∀ t : ℝ, f (AffineMap.lineMap ((w : ℂ) + (u : ℂ) * Complex.I)
        ((w : ℂ) + (v : ℂ) * Complex.I) t) *
          (((w : ℂ) + (v : ℂ) * Complex.I) - ((w : ℂ) + (u : ℂ) * Complex.I)) =
        (fun y : ℝ => f ((w : ℂ) + (y : ℂ) * Complex.I)) ((v - u) * t + u) *
          (Complex.I * ((v - u : ℝ) : ℂ)) := by
      intro t
      rw [lineMap_vertical]
      push_cast
      ring_nf
    simp only [e1]
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_comp_mul_add (fun y : ℝ => f ((w : ℂ) + (y : ℂ) * Complex.I)) hne u]
    simp only [mul_zero, zero_add, mul_one, Complex.real_smul]
    have : ((v - u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    push_cast at this ⊢
    rw [sub_add_cancel]
    field_simp
    congr 1
    funext x
    rw [mul_comm]

theorem curveIntegrable_segment_of_cont (f : ℂ → ℂ) (p q : ℂ)
    (hf : ContinuousOn f (segment ℝ p q)) :
    CurveIntegrable (complexForm f) (Path.segment p q) := by
  rw [curveIntegrable_segment]
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  have h1 : ContinuousOn (fun t : ℝ => f (AffineMap.lineMap p q t)) (Icc (0 : ℝ) 1) := by
    refine hf.comp (AffineMap.lineMap_continuous (R := ℝ) (p := p) (q := q)).continuousOn fun t ht => ?_
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  have h2 := h1.mul (continuousOn_const (c := q - p))
  have h3 : (fun t : ℝ => (complexForm f (AffineMap.lineMap p q t)) (q - p)) =
      (fun t : ℝ => f (AffineMap.lineMap p q t)) * fun _ => q - p := by
    funext t; simp [complexForm]
  rw [h3]
  exact h2

theorem curveIntegral_segment_complexForm (f : ℂ → ℂ) (p q : ℂ) :
    curveIntegral (complexForm f) (Path.segment p q) =
      ∫ t : ℝ in (0 : ℝ)..1, f (AffineMap.lineMap p q t) * (q - p) := by
  rw [curveIntegral_segment]
  simp [complexForm]

theorem rectIntegral_eq_curveIntegral (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : ContinuousOn f (range (rectangleLoop a b c d))) :
    CurveIntegrable (complexForm f) (rectangleLoop a b c d) ∧
    rectIntegral f a b c d =
      curveIntegral (complexForm f) (rectangleLoop a b c d) := by
  have hr : range (rectangleLoop a b c d) =
      ((segment ℝ ((a : ℂ) + (c : ℂ) * Complex.I) ((b : ℂ) + (c : ℂ) * Complex.I) ∪
        segment ℝ ((b : ℂ) + (c : ℂ) * Complex.I) ((b : ℂ) + (d : ℂ) * Complex.I)) ∪
        segment ℝ ((b : ℂ) + (d : ℂ) * Complex.I) ((a : ℂ) + (d : ℂ) * Complex.I)) ∪
        segment ℝ ((a : ℂ) + (d : ℂ) * Complex.I) ((a : ℂ) + (c : ℂ) * Complex.I) := by
    simp only [rectangleLoop, Path.trans_range, Path.range_segment]
  rw [hr] at hf
  have c1 := curveIntegrable_segment_of_cont f ((a : ℂ) + (c : ℂ) * Complex.I)
    ((b : ℂ) + (c : ℂ) * Complex.I) (hf.mono fun x hx => Or.inl (Or.inl (Or.inl hx)))
  have c2 := curveIntegrable_segment_of_cont f ((b : ℂ) + (c : ℂ) * Complex.I)
    ((b : ℂ) + (d : ℂ) * Complex.I) (hf.mono fun x hx => Or.inl (Or.inl (Or.inr hx)))
  have c3 := curveIntegrable_segment_of_cont f ((b : ℂ) + (d : ℂ) * Complex.I)
    ((a : ℂ) + (d : ℂ) * Complex.I) (hf.mono fun x hx => Or.inl (Or.inr hx))
  have c4 := curveIntegrable_segment_of_cont f ((a : ℂ) + (d : ℂ) * Complex.I)
    ((a : ℂ) + (c : ℂ) * Complex.I) (hf.mono fun x hx => Or.inr hx)
  have c12 := c1.trans c2
  have c123 := c12.trans c3
  refine ⟨c123.trans c4, ?_⟩
  unfold rectangleLoop
  rw [curveIntegral_trans c123 c4, curveIntegral_trans c12 c3, curveIntegral_trans c1 c2,
    curveIntegral_segment_complexForm, curveIntegral_segment_complexForm,
    curveIntegral_segment_complexForm, curveIntegral_segment_complexForm,
    seg_horizontal_integral, seg_vertical_integral, seg_horizontal_integral,
    seg_vertical_integral, intervalIntegral.integral_symm c d, intervalIntegral.integral_symm a b]
  unfold rectIntegral
  ring

/-! ### 15.22 -/

theorem inv_sqrt_left_integrable (A B K : ℝ) (hAB : A ≤ B) :
    IntervalIntegrable (fun t : ℝ => K / Real.sqrt (t - A)) volume A B := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB]
  have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 (B - A) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h1 := h0.comp_sub_right A
  simp only [zero_add, sub_add_cancel] at h1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB] at h1
  have h2 : IntegrableOn (fun x : ℝ => K * (x - A) ^ (-(1 / 2 : ℝ))) (Ioc A B) volume :=
    Integrable.const_mul h1 K
  refine IntegrableOn.congr_fun h2 (fun t ht => ?_) measurableSet_Ioc
  have hpos : 0 ≤ t - A := by linarith [ht.1]
  show K * (t - A) ^ (-(1 / 2 : ℝ)) = K / Real.sqrt (t - A)
  rw [Real.rpow_neg hpos, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

theorem inv_sqrt_right_integrable (A B K : ℝ) (hAB : A ≤ B) :
    IntervalIntegrable (fun t : ℝ => K / Real.sqrt (B - t)) volume A B := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB]
  have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 (B - A) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h1 := (h0.comp_sub_left B).symm
  simp only [sub_zero, sub_sub_cancel] at h1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB] at h1
  have h2 : IntegrableOn (fun x : ℝ => K * (B - x) ^ (-(1 / 2 : ℝ))) (Ioc A B) volume :=
    Integrable.const_mul h1 K
  refine IntegrableOn.congr_fun h2 (fun t ht => ?_) measurableSet_Ioc
  have hpos : 0 ≤ B - t := by linarith [ht.2]
  show K * (B - t) ^ (-(1 / 2 : ℝ)) = K / Real.sqrt (B - t)
  rw [Real.rpow_neg hpos, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

theorem endpoint_shift_bound (F : ℂ → ℂ) (U : Set ℂ) (P : ℝ) (C δ : ℝ) (hC : 0 ≤ C)
    (hB : ∀ z ∈ U, 0 < dist z (P : ℂ) → dist z (P : ℂ) < δ →
      ‖F z‖ ≤ C / Real.sqrt (dist z (P : ℂ)))
    (σ ε t η : ℝ) (hσ : σ = 1 ∨ σ = -1) (hε : 0 < ε) (hεη : ε < η) (hηδ : 2 * η ≤ δ)
    (hU : (t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I ∈ U)
    (hdt : |t - P| ≤ η) (hpos : 0 < |t - P|) :
    ‖F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I)‖ ≤ C / Real.sqrt |t - P| := by
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hsε : |σ * ε| = ε := by rw [abs_mul, hσabs, one_mul, abs_of_pos hε]
  set w : ℂ := (t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I with hw
  have h1 : |(w - (P : ℂ)).re| ≤ ‖w - (P : ℂ)‖ := Complex.abs_re_le_norm _
  have h3 : ‖w - (P : ℂ)‖ ≤ |(w - (P : ℂ)).re| + |(w - (P : ℂ)).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have e1 : (w - (P : ℂ)).re = t - P := by simp [hw]
  have e2 : (w - (P : ℂ)).im = σ * ε := by simp [hw]
  rw [e1] at h1 h3
  rw [e2, hsε] at h3
  have hd : dist w (P : ℂ) = ‖w - (P : ℂ)‖ := dist_eq_norm _ _
  have hlow : |t - P| ≤ dist w (P : ℂ) := by rw [hd]; exact h1
  have hup : dist w (P : ℂ) < δ := by rw [hd]; linarith
  have hdpos : 0 < dist w (P : ℂ) := lt_of_lt_of_le hpos hlow
  have := hB w hU hdpos hup
  refine this.trans ?_
  exact div_le_div_of_nonneg_left hC (Real.sqrt_pos.2 hpos) (Real.sqrt_le_sqrt hlow)

theorem localUniformTrace_to_L1 {n : ℕ} (S : RealSlits n)
    (F : ℂ → ℂ) (hf : DifferentiableOn ℂ F S.carrierᶜ)
    (i : Fin n) (v : ℝ → ℂ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (htrace : HasLocalUniformTrace F v (S.a i) (S.b i) σ)
    (ha : HasEndpointBound F S.carrierᶜ (S.a i : ℂ))
    (hb : HasEndpointBound F S.carrierᶜ (S.b i : ℂ)) :
    HasL1Trace F v (S.a i) (S.b i) σ := by
  have hopen : IsOpen S.carrierᶜ := (slits_compact_and_separated S).2.1
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  -- shifted points are off the carrier
  have hnot : ∀ (t ε : ℝ), 0 < ε → (t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I ∈ S.carrierᶜ := by
    intro t ε hε hc
    have := carrier_im_eq_zero S hc
    simp at this
    rcases this with h | h
    · exact hσne h
    · exact hε.ne' h
  -- continuity of shifted F
  have hcont : ∀ ε : ℝ, 0 < ε → Continuous (fun t : ℝ => F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I)) := by
    intro ε hε
    refine continuous_iff_continuousAt.2 fun t => ?_
    have h1 : ContinuousAt F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I) :=
      (hf.differentiableAt (hopen.mem_nhds (hnot t ε hε))).continuousAt
    exact h1.comp (f := fun t : ℝ => (t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I)
      (by fun_prop)
  have hAB : S.a i ≤ S.b i := S.le i
  rcases hAB.eq_or_lt with hEq | hlt
  · -- degenerate slit
    refine ⟨?_, fun ε hε => ?_, ?_⟩
    · first | (rw [← hEq]; done) | (rw [← hEq]; exact IntervalIntegrable.refl)
    · first | (rw [← hEq]; done) | (rw [← hEq]; exact IntervalIntegrable.refl)
    · rw [← hEq]
      simp only [intervalIntegral.integral_same]
      exact tendsto_const_nhds
  · set A := S.a i with hAdef
    set B := S.b i with hBdef
    obtain ⟨C, δ1, hC, hδ1, hBa⟩ := ha
    obtain ⟨C', δ2, hC', hδ2, hBb⟩ := hb
    set K : ℝ := C + C' with hK
    have hK0 : 0 ≤ K := add_nonneg hC hC'
    set δ0 : ℝ := min δ1 δ2 with hδ0
    set η : ℝ := min (δ0 / 2) ((B - A) / 2) with hηdef
    have hδ0pos : 0 < δ0 := lt_min hδ1 hδ2
    have hη : 0 < η := lt_min (by positivity) (by linarith)
    have hη1 : 2 * η ≤ δ1 := by
      have := min_le_left (δ0 / 2) ((B - A) / 2)
      have := min_le_left δ1 δ2
      linarith
    have hη2 : 2 * η ≤ δ2 := by
      have := min_le_left (δ0 / 2) ((B - A) / 2)
      have := min_le_right δ1 δ2
      linarith
    have hη3 : 2 * η ≤ B - A := by
      have := min_le_right (δ0 / 2) ((B - A) / 2)
      linarith
    -- bounds of the shifted function near the endpoints
    have hL : ∀ ε : ℝ, 0 < ε → ε < η → ∀ t : ℝ, A < t → t ≤ A + η →
        ‖F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I)‖ ≤ C / Real.sqrt (t - A) := by
      intro ε hε hεη t h1 h2
      have habs : |t - A| = t - A := abs_of_pos (by linarith)
      have := endpoint_shift_bound F S.carrierᶜ A C δ1 hC hBa σ ε t η hσ hε hεη hη1
        (hnot t ε hε) (by rw [habs]; linarith) (by rw [habs]; linarith)
      rwa [habs] at this
    have hR : ∀ ε : ℝ, 0 < ε → ε < η → ∀ t : ℝ, B - η ≤ t → t < B →
        ‖F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I)‖ ≤ C' / Real.sqrt (B - t) := by
      intro ε hε hεη t h1 h2
      have habs : |t - B| = B - t := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
      have := endpoint_shift_bound F S.carrierᶜ B C' δ2 hC' hBb σ ε t η hσ hε hεη hη2
        (hnot t ε hε) (by rw [habs]; linarith) (by rw [habs]; linarith)
      rwa [habs] at this
    -- pointwise limits
    have hlim : ∀ t ∈ Ioo A B, Tendsto (fun ε : ℝ => F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (v t)) := by
      intro t ht
      exact (htrace t t ht.1 le_rfl ht.2).tendsto_at (by simp)
    -- bounds for v near the endpoints
    have hvL : ∀ t : ℝ, A < t → t ≤ A + η → t < B → ‖v t‖ ≤ C / Real.sqrt (t - A) := by
      intro t h1 h2 h3
      refine le_of_tendsto (hlim t ⟨h1, h3⟩).norm ?_
      filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
      exact hL ε hε.1 hε.2 t h1 h2
    have hvR : ∀ t : ℝ, A < t → B - η ≤ t → t < B → ‖v t‖ ≤ C' / Real.sqrt (B - t) := by
      intro t h1 h2 h3
      refine le_of_tendsto (hlim t ⟨h1, h3⟩).norm ?_
      filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
      exact hR ε hε.1 hε.2 t h2 h3
    -- the middle part
    have hAc : A < A + η := by linarith
    have hdB : B - η < B := by linarith
    have hcd : A + η ≤ B - η := by linarith
    have hunif := Metric.tendstoUniformlyOn_iff.1 (htrace (A + η) (B - η) hAc hcd hdB) 1 one_pos
    obtain ⟨ε0, hε0u, hε0⟩ := (hunif.and (Ioo_mem_nhdsGT hη)).exists
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun t : ℝ => F ((t : ℂ) + ((σ * ε0 : ℝ) : ℂ) * Complex.I))
      (s := Icc (A + η) (B - η)) (hcont ε0 hε0.1).continuousOn
    have hvM : ∀ t ∈ Icc (A + η) (B - η), ‖v t‖ ≤ |M| + 1 := by
      intro t ht
      have h1 := hε0u t ht
      rw [dist_eq_norm] at h1
      have h2 := hM t ht
      have h3 : ‖v t‖ ≤ ‖F ((t : ℂ) + ((σ * ε0 : ℝ) : ℂ) * Complex.I)‖ +
          ‖v t - F ((t : ℂ) + ((σ * ε0 : ℝ) : ℂ) * Complex.I)‖ := by
        calc ‖v t‖ = ‖F ((t : ℂ) + ((σ * ε0 : ℝ) : ℂ) * Complex.I) +
            (v t - F ((t : ℂ) + ((σ * ε0 : ℝ) : ℂ) * Complex.I))‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith [le_abs_self M]
    -- integrable majorants
    have iL : ∀ K' : ℝ, IntervalIntegrable (fun t : ℝ => K' / Real.sqrt (t - A)) volume A B :=
      fun K' => inv_sqrt_left_integrable A B K' hAB
    have iR : ∀ K' : ℝ, IntervalIntegrable (fun t : ℝ => K' / Real.sqrt (B - t)) volume A B :=
      fun K' => inv_sqrt_right_integrable A B K' hAB
    have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ B := by
      rw [MeasureTheory.ae_iff]; simp
    -- measurability of v
    have hvmeas : AEStronglyMeasurable v (volume.restrict (Ioc A B)) := by
      let u : ℕ → ℝ → ℂ := fun m t =>
        F ((t : ℂ) + ((σ * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)
      refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ) (f := u) (fun m => ?_) ?_
      · exact (hcont _ (by positivity)).aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hae] with t ht htI
        have htB : t < B := lt_of_le_of_ne htI.2 ht
        have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
          tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
            Filter.Eventually.of_forall fun m => by
              show (0 : ℝ) < 1 / ((m : ℝ) + 1)
              positivity⟩
        exact (hlim t ⟨htI.1, htB⟩).comp h1
    -- integrability of v
    have hvint : IntervalIntegrable v volume A B := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB]
      have hΦ : IntervalIntegrable (fun t : ℝ => (|M| + 1) + K / Real.sqrt (t - A) +
          K / Real.sqrt (B - t)) volume A B :=
        ((intervalIntegrable_const (c := |M| + 1)).add (iL K)).add (iR K)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB] at hΦ
      refine hΦ.mono' hvmeas ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hae] with t ht htI
      have htB : t < B := lt_of_le_of_ne htI.2 ht
      have hpos1 : 0 ≤ K / Real.sqrt (t - A) := div_nonneg hK0 (Real.sqrt_nonneg _)
      have hpos2 : 0 ≤ K / Real.sqrt (B - t) := div_nonneg hK0 (Real.sqrt_nonneg _)
      have hpos0 : 0 ≤ |M| + 1 := by positivity
      by_cases h1 : t ≤ A + η
      · have := hvL t htI.1 h1 htB
        have h4 : C / Real.sqrt (t - A) ≤ K / Real.sqrt (t - A) :=
          div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
        linarith
      · by_cases h2 : B - η ≤ t
        · have := hvR t htI.1 h2 htB
          have h4 : C' / Real.sqrt (B - t) ≤ K / Real.sqrt (B - t) :=
            div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
          linarith
        · have := hvM t ⟨by linarith, by linarith⟩
          linarith
    -- the convergence of the L¹ distance
    have hconv : Tendsto (fun ε : ℝ => ∫ t : ℝ in A..B,
        ‖F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I) - v t‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (μ := volume) (l := 𝓝[>] (0 : ℝ)) (a := A) (b := B)
        (F := fun ε t => ‖F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I) - v t‖)
        (f := fun _ => (0 : ℝ))
        (fun t => 1 + 2 * K / Real.sqrt (t - A) + 2 * K / Real.sqrt (B - t)) ?_ ?_ ?_ ?_
      · simpa using this
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : 0 < ε := hε
        rw [uIoc_of_le hAB]
        exact (((hcont ε hε').aestronglyMeasurable).sub hvmeas).norm
      · filter_upwards [Ioo_mem_nhdsGT hη,
          Metric.tendstoUniformlyOn_iff.1 (htrace (A + η) (B - η) hAc hcd hdB) 1 one_pos]
          with ε hε hεu
        filter_upwards [hae] with t ht htI
        rw [uIoc_of_le hAB] at htI
        have htB : t < B := lt_of_le_of_ne htI.2 ht
        rw [norm_norm]
        have hpos1 : 0 ≤ 2 * K / Real.sqrt (t - A) := div_nonneg (by linarith) (Real.sqrt_nonneg _)
        have hpos2 : 0 ≤ 2 * K / Real.sqrt (B - t) := div_nonneg (by linarith) (Real.sqrt_nonneg _)
        by_cases h1 : t ≤ A + η
        · have e1 := hL ε hε.1 hε.2 t htI.1 h1
          have e2 := hvL t htI.1 h1 htB
          have h4 : C / Real.sqrt (t - A) ≤ K / Real.sqrt (t - A) :=
            div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
          have h5 : 2 * K / Real.sqrt (t - A) = 2 * (K / Real.sqrt (t - A)) := by ring
          calc ‖F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I) - v t‖
              ≤ ‖F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I)‖ + ‖v t‖ := norm_sub_le _ _
            _ ≤ 1 + 2 * K / Real.sqrt (t - A) + 2 * K / Real.sqrt (B - t) := by linarith
        · by_cases h2 : B - η ≤ t
          · have e1 := hR ε hε.1 hε.2 t h2 htB
            have e2 := hvR t htI.1 h2 htB
            have h4 : C' / Real.sqrt (B - t) ≤ K / Real.sqrt (B - t) :=
              div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
            have h5 : 2 * K / Real.sqrt (B - t) = 2 * (K / Real.sqrt (B - t)) := by ring
            calc ‖F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I) - v t‖
                ≤ ‖F ((t : ℂ) + ((σ * ε : ℝ) : ℂ) * Complex.I)‖ + ‖v t‖ := norm_sub_le _ _
              _ ≤ 1 + 2 * K / Real.sqrt (t - A) + 2 * K / Real.sqrt (B - t) := by linarith
          · have := hεu t ⟨by linarith, by linarith⟩
            rw [dist_eq_norm, norm_sub_rev] at this
            linarith
      · exact ((intervalIntegrable_const (c := (1 : ℝ))).add (iL (2 * K))).add (iR (2 * K))
      · filter_upwards [hae] with t ht htI
        rw [uIoc_of_le hAB] at htI
        have htB : t < B := lt_of_le_of_ne htI.2 ht
        have := ((hlim t ⟨htI.1, htB⟩).sub_const (v t)).norm
        simpa using this
    exact ⟨hvint, fun ε hε => (hcont ε hε).intervalIntegrable _ _, hconv⟩

end

end NlsGge.GK38.Lib.SlitContours
