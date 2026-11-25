import QuantumNLS.Ext025HGP08
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Round 27: the pushforward resolution is linked to the actual maximal
unbounded operator, including its values, rather than merely commuting sets. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology Function
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.Ext025GP08R27m
open BetheChargeResolution Ext025B6PVM Ext025B8SimpleCalculus Ext025B8BorelCalculus
open Ext025B9MaximalIntegral Ext025B9IntegralDomain Ext025B9IntegralCutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The candidate spectral measure of the real multiplier, constructed as a PVM. -/
def mapped (P : ProjectionMeasure E) (f : ℝ → ℝ) (hf : Measurable f) :
    ProjectionMeasure E where
  toFun s := P.toFun (f ⁻¹' s)
  empty := by simpa using P.empty
  univ := by simpa using P.univ
  selfAdjoint s hs := P.selfAdjoint _ (hf hs)
  inter s t hs ht := P.inter _ _ (hf hs) (hf ht)
  additive s hs hd x := by
    simpa only [Set.preimage_iUnion] using
      P.additive (fun n => f ⁻¹' s n) (fun n => hf (hs n))
        (fun i j hij => (hd hij).preimage f) x

 theorem scalar_mapped (P : ProjectionMeasure E) (f : ℝ → ℝ) (hf : Measurable f) (x : E) :
    scalarMeasure (mapped P f hf) x = Measure.map f (scalarMeasure P x) := by
  apply Measure.ext
  intro s hs
  rw [scalarMeasure_apply _ _ _ hs, Measure.map_apply hf hs,
    scalarMeasure_apply _ _ _ (hf hs)]
  rfl

 theorem simple_mapped (P : ProjectionMeasure E) (f : ℝ → ℝ) (hf : Measurable f)
    (a : SimpleFunc ℝ ℂ) : simple (mapped P f hf) a = simple P (a.comp f hf) := by
  apply eq_of_local (mapped P f hf) a
  intro c hc
  rw [simple_local (mapped P f hf) a _ (a.measurableSet_fiber c) c (fun t ht => ht)]
  change c • P.toFun (f ⁻¹' (a ⁻¹' {c})) =
    simple P (a.comp f hf) * P.toFun (f ⁻¹' (a ⁻¹' {c}))
  exact (simple_local P (a.comp f hf) _ (hf (a.measurableSet_fiber c)) c
    (fun t ht => ht)).symm

 theorem bounded_mapped (P : ProjectionMeasure E) (f : ℝ → ℝ) (hf : Measurable f)
    (a : ℝ → ℂ) (ha : Measurable a) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖a t‖ ≤ C) :
    bounded (mapped P f hf) a ha C hC hb =
      bounded P (a ∘ f) (ha.comp hf) C hC (fun t => hb (f t)) := by
  ext x
  have hl := approx_integral (mapped P f hf) a ha x
    (MemLp.of_bound ha.aestronglyMeasurable C (.of_forall hb))
  let A : ℕ → SimpleFunc ℝ ℂ := fun n => (approx a ha n).comp f hf
  have hA (n : ℕ) (t : ℝ) : ‖A n t‖ ≤ C := approx_bound a ha C hC hb n (f t)
  have hr := bounded_strong P (fun n => A n) (a ∘ f)
    (fun n => (A n).measurable) (ha.comp hf) C hC hA (fun t => hb (f t))
    (fun t => Ext025B8BorelLaws.approx_pointwise a ha (f t)) x
  apply tendsto_nhds_unique hl
  apply hr.congr'
  apply Eventually.of_forall
  intro n
  have hn : bounded P (A n) (A n).measurable C hC (hA n) =
      simple (mapped P f hf) (approx a ha n) :=
    (bounded_simple P (A n) C hC (hA n)).trans (simple_mapped P f hf (approx a ha n)).symm
  exact congrArg (fun B : E →L[ℂ] E => B x) hn

 theorem domain_mapped (P : ProjectionMeasure E) (f : ℝ → ℝ) (hf : Measurable f) (x : E) :
    x ∈ (operator (mapped P f hf) (fun t => (t : ℂ)) Complex.measurable_ofReal).domain ↔
      x ∈ (operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf)).domain := by
  change (∫⁻ t, ENNReal.ofReal (‖(t : ℂ)‖^2) ∂scalarMeasure (mapped P f hf) x) ≠ ⊤ ↔ _
  rw [scalar_mapped, lintegral_map (by fun_prop) hf]
  rfl

/-- Equality of the actual unbounded operators, including their maximal domains
and all values. Thus `mapped P f hf` is a spectral resolution of the operator. -/
 theorem operator_mapped (P : ProjectionMeasure E) (f : ℝ → ℝ) (hf : Measurable f)
    (x : E) (hx : x ∈ (operator P (fun t => (f t : ℂ))
      (Complex.measurable_ofReal.comp hf)).domain) :
    operator (mapped P f hf) (fun t => (t : ℂ)) Complex.measurable_ofReal
        ⟨x,(domain_mapped P f hf x).mpr hx⟩ =
      operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf) ⟨x,hx⟩ := by
  classical
  let Q := mapped P f hf
  let s : ℕ → Set ℝ := fun n => {t | ‖t‖ ≤ (n : ℝ)}
  have hs (n : ℕ) : MeasurableSet (s n) := by dsimp [s]; measurability
  have hm : Monotone s := by
    intro i j hij t ht
    change ‖t‖ ≤ (i : ℝ) at ht
    change ‖t‖ ≤ (j : ℝ)
    exact ht.trans (Nat.cast_le.mpr hij)
  have hu : ⋃ n, s n = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨n,hn⟩ := exists_nat_ge ‖t‖
    exact Set.mem_iUnion.mpr ⟨n,hn⟩
  have hxQ : x ∈ (operator Q (fun t => (t : ℂ)) Complex.measurable_ofReal).domain :=
    (domain_mapped P f hf x).mpr hx
  have he (n : ℕ) :
      Q.toFun (s n) (operator Q (fun t => (t : ℂ)) Complex.measurable_ofReal ⟨x,hxQ⟩) =
      Q.toFun (s n) (operator P (fun t => (f t : ℂ))
        (Complex.measurable_ofReal.comp hf) ⟨x,hx⟩) := by
    have hb : ∀ t ∈ s n, ‖(t : ℂ)‖ ≤ (n : ℝ) := by
      intro t ht
      change ‖t‖ ≤ (n : ℝ) at ht
      simpa only [Complex.norm_real, Real.norm_eq_abs] using ht
    let a : ℝ → ℂ := (s n).indicator (fun t => (t : ℂ))
    let c : ℝ → ℂ := (f ⁻¹' s n).indicator (fun t => (f t : ℂ))
    have ha : Measurable a := Complex.measurable_ofReal.indicator (hs n)
    have hc : Measurable c := (Complex.measurable_ofReal.comp hf).indicator (hf (hs n))
    have hba : ∀ t, ‖a t‖ ≤ (n : ℝ) := by
      intro t
      by_cases ht : t ∈ s n
      · simpa only [a, Set.indicator_of_mem ht] using hb t ht
      · simp only [a, Set.indicator_of_notMem ht, norm_zero]; positivity
    have hfun : a ∘ f = c := by
      ext t
      exact (Set.indicator_comp_right (s := s n) (g := fun t : ℝ => (t : ℂ)) f (x := t)).symm
    have hbc : ∀ t, ‖c t‖ ≤ (n : ℝ) := by
      intro t
      rw [← congrFun hfun t]
      exact hba (f t)
    have hnat : bounded Q a ha n (Nat.cast_nonneg n) hba =
        bounded P c hc n (Nat.cast_nonneg n) hbc :=
      (bounded_mapped P f hf a ha n (Nat.cast_nonneg n) hba).trans
        (Ext025HGP08.bounded_congr P hfun (ha.comp hf) hc n n
          (Nat.cast_nonneg n) (Nat.cast_nonneg n) (fun t => hba (f t)) hbc)
    calc
      _ = operator Q (fun t => (t : ℂ)) Complex.measurable_ofReal
          ⟨Q.toFun (s n) x, projection_mem Q _ (s n) (hs n) x hxQ⟩ :=
        (projection_commutes Q _ Complex.measurable_ofReal (s n) (hs n) x hxQ).symm
      _ = bounded Q a ha n (Nat.cast_nonneg n) hba x :=
        window_action Q _ Complex.measurable_ofReal (s n) (hs n) n (Nat.cast_nonneg n) hb x
      _ = bounded P c hc n (Nat.cast_nonneg n) hbc x := congrArg (fun B : E →L[ℂ] E => B x) hnat
      _ = operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf)
          ⟨P.toFun (f ⁻¹' s n) x, projection_mem P _ _ (hf (hs n)) x hx⟩ :=
        (window_action P _ (Complex.measurable_ofReal.comp hf) _ (hf (hs n)) n
          (Nat.cast_nonneg n) (fun t ht => hb (f t) ht) x).symm
      _ = _ := projection_commutes P _ (Complex.measurable_ofReal.comp hf) _ (hf (hs n)) x hx
  exact tendsto_nhds_unique
    (Ext025B7SpectralCompression.exhaustion_strong Q s hs hm hu _)
    ((Ext025B7SpectralCompression.exhaustion_strong Q s hs hm hu _).congr'
      (.of_forall fun n => (he n).symm))

def OriginalContract (P : ProjectionMeasure E) : Prop :=
    -- (1) real multipliers are selfadjoint on their exact maximal domains
    (∀ (f : ℝ → ℝ) (hf : Measurable f),
      IsSelfAdjoint (QuantumNLS.Ext025B9MaximalIntegral.operator P (fun t => (f t : ℂ))
        (Complex.measurable_ofReal.comp hf)) ∧
      ∀ x : E, x ∈ (QuantumNLS.Ext025B9MaximalIntegral.operator P (fun t => (f t : ℂ))
          (Complex.measurable_ofReal.comp hf)).domain ↔
        ∫⁻ t, ENNReal.ofReal (‖(f t : ℂ)‖ ^ 2) ∂(QuantumNLS.Ext025B6PVM.scalarMeasure P x) ≠ ⊤) ∧
    -- (2) bounded multipliers form a *-calculus
    (∀ (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
      (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D) (hfg : ∀ t, ‖(f + g) t‖ ≤ C + D),
      QuantumNLS.Ext025B8BorelCalculus.bounded P (f + g) (hf.add hg) (C + D) (add_nonneg hC hD) hfg =
        QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb +
          QuantumNLS.Ext025B8BorelCalculus.bounded P g hg D hD hc) ∧
    (∀ (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
      (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D) (hfg : ∀ t, ‖(f * g) t‖ ≤ C * D),
      QuantumNLS.Ext025B8BorelCalculus.bounded P (f * g) (hf.mul hg) (C * D) (mul_nonneg hC hD) hfg =
        QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb *
          QuantumNLS.Ext025B8BorelCalculus.bounded P g hg D hD hc) ∧
    (∀ (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C) (c : ℂ)
      (hm : Measurable (c • f)) (hcb : ∀ t, ‖(c • f) t‖ ≤ ‖c‖ * C),
      QuantumNLS.Ext025B8BorelCalculus.bounded P (c • f) hm (‖c‖ * C)
          (mul_nonneg (norm_nonneg _) hC) hcb =
        c • QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb) ∧
    (QuantumNLS.Ext025B8BorelCalculus.bounded P (fun _ => (1 : ℂ)) measurable_const 1 zero_le_one
        (fun _ => by simp) = 1) ∧
    (∀ (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C)
      (hm : Measurable (fun t => star (f t))) (hbs : ∀ t, ‖star (f t)‖ ≤ C),
      (QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb).adjoint =
        QuantumNLS.Ext025B8BorelCalculus.bounded P (fun t => star (f t)) hm C hC hbs) ∧
    -- (3) uniformly bounded pointwise convergence gives strong convergence
    (∀ {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
      (f : J → ℝ → ℂ) (g : ℝ → ℂ) (hf : ∀ j, Measurable (f j)) (hg : Measurable g)
      (C : ℝ) (hC : 0 ≤ C) (hb : ∀ j t, ‖f j t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ C)
      (hl : ∀ t, Tendsto (fun j => f j t) l (𝓝 (g t))) (x : E),
      Tendsto (fun j => QuantumNLS.Ext025B8BorelCalculus.bounded P (f j) (hf j) C hC (hb j) x) l
        (𝓝 (QuantumNLS.Ext025B8BorelCalculus.bounded P g hg C hC hc x))) ∧
    -- (4) functions of one common spectral resolution commute (strongly)
    (∀ (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C),
      QuantumNLS.Ext025B7PVMForms.Commutes P
        (QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb)) ∧
    (∀ (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
      (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D),
      QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb *
          QuantumNLS.Ext025B8BorelCalculus.bounded P g hg D hD hc =
        QuantumNLS.Ext025B8BorelCalculus.bounded P g hg D hD hc *
          QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb) ∧
    (∀ (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) (s t : Set ℝ),
      MeasurableSet s → MeasurableSet t →
      P.toFun (f ⁻¹' s) * P.toFun (g ⁻¹' t) = P.toFun (g ⁻¹' t) * P.toFun (f ⁻¹' s)) ∧
    -- (5) form-domain preservation, for BOUNDED common multipliers only
    (∀ (h : ℝ → ℝ) (_hh : ∀ t, 0 ≤ h t) (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
      (hb : ∀ t, ‖f t‖ ≤ C) (x : E),
      QuantumNLS.Ext025B7PVMForms.FormDomain P (fun t => ENNReal.ofReal (h t)) x →
      QuantumNLS.Ext025B7PVMForms.FormDomain P (fun t => ENNReal.ofReal (h t))
        (QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb x))

/-- The repaired GP-08 contract, with the original clauses retained and the
spectral resolution of every real maximal multiplier identified explicitly. -/
theorem contract_GP08_fixed (P : ProjectionMeasure E) :
    (∀ f hf, IsSelfAdjoint (operator (mapped P f hf) (fun t => (t : ℂ))
      Complex.measurable_ofReal) ∧
      (∀ x, x ∈ (operator (mapped P f hf) (fun t => (t : ℂ)) Complex.measurable_ofReal).domain ↔
        x ∈ (operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf)).domain) ∧
      (∀ x hx, operator (mapped P f hf) (fun t => (t : ℂ)) Complex.measurable_ofReal
          ⟨x,(domain_mapped P f hf x).mpr hx⟩ =
        operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf) ⟨x,hx⟩)) ∧
    (∀ f g hf hg s t, MeasurableSet s → MeasurableSet t →
      (mapped P f hf).toFun s * (mapped P g hg).toFun t =
        (mapped P g hg).toFun t * (mapped P f hf).toFun s) ∧
    OriginalContract P := by
  refine ⟨fun f hf => ⟨Ext025B9SelfAdjoint.real_selfAdjoint _ id measurable_id,
    domain_mapped P f hf, operator_mapped P f hf⟩, ?_, Ext025HGP08.contract_GP08 P⟩
  intro f g hf hg s t hs ht
  change P.toFun (f ⁻¹' s) * P.toFun (g ⁻¹' t) =
    P.toFun (g ⁻¹' t) * P.toFun (f ⁻¹' s)
  rw [P.inter _ _ (hf hs) (hg ht), P.inter _ _ (hg ht) (hf hs), Set.inter_comm]
end QuantumNLS.Ext025GP08R27m
#print axioms QuantumNLS.Ext025GP08R27m.contract_GP08_fixed
