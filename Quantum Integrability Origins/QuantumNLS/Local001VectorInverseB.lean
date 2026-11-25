import QuantumNLS.Local001ScalarInverseB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable (L : ℝ) [Fact (0 < L)]

theorem lopPt_zero_potential (κ : ℝ) (d g : E2) :
    lopPt κ 0 d g = (2 * Complex.I) • Jm d := by
  simp [LocalSpectral.lopPt, LocalSpectral.Jm, LocalSpectral.vec2]

#print axioms lopPt_zero_potential

theorem vectorH1_component {L : ℝ} [Fact (0 < L)] (f : VectorInterval L)
    (g h : ℝ → E2) (hf : LocalSpectral.IsH1Rep L f g h) (j : Fin 2) :
    IntervalH1Rep (vectorToComponentsLinear L f j)
      (fun x => g x j) (fun x => h x j) := by
  refine ⟨?_, ?_, ?_⟩
  · have hcoord :
        (vectorToComponentsLinear L f j : ℝ → ℂ) =ᵐ[μI L] fun x => (f x) j := by
      exact (fiberCoordinate j).coeFn_compLp f
    filter_upwards [hcoord, hf.1] with x hcoord hx
    rw [hcoord, hx]
  · exact MemLp.continuousLinearMap_comp hf.2.1 (fiberCoordinate j)
  · intro x hx
    have hhint : IntervalIntegrable h volume 0 L :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (Fact.out : 0 < L).le).2
        (hf.2.1.integrable (by norm_num))
    have hix : IntervalIntegrable h volume 0 x :=
      hhint.mono_set (by
        rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le (Fact.out : 0 < L).le]
        exact Set.Icc_subset_Icc_right hx.2)
    have hmap := ContinuousLinearMap.intervalIntegral_comp_comm (fiberCoordinate j) hix
    change (∫ s in (0 : ℝ)..x, (h s) j) = (∫ s in (0 : ℝ)..x, h s) j at hmap
    have hcoord := congrArg (fiberCoordinate j) (hf.2.2 x hx)
    change (g x).ofLp j = (g 0).ofLp j +
      (∫ s in (0 : ℝ)..x, h s).ofLp j at hcoord
    rw [← hmap] at hcoord
    exact hcoord


#print axioms vectorH1_component

theorem vectorH1_of_scalarComponents {L : ℝ} [Fact (0 < L)]
    (f : VectorInterval L) (g0 g1 h0 h1 : ℝ → ℂ)
    (hf0 : IntervalH1Rep (vectorToComponentsLinear L f 0) g0 h0)
    (hf1 : IntervalH1Rep (vectorToComponentsLinear L f 1) g1 h1) :
    LocalSpectral.IsH1Rep L f
      (fun x => WithLp.toLp 2 (fun j : Fin 2 => if j = 0 then g0 x else g1 x))
      (fun x => WithLp.toLp 2 (fun j : Fin 2 => if j = 0 then h0 x else h1 x)) := by
  let gV : ℝ → E2 := fun x => WithLp.toLp 2
    (fun j : Fin 2 => if j = 0 then g0 x else g1 x)
  let hV : ℝ → E2 := fun x => WithLp.toLp 2
    (fun j : Fin 2 => if j = 0 then h0 x else h1 x)
  have hVmem : MemLp hV 2 (μI L) := by
    change MemLp (fun x : ℝ => WithLp.toLp 2
      (fun j : Fin 2 => if j = 0 then h0 x else h1 x)) 2 (μI L)
    rw [MeasureTheory.memLp_piLp_iff]
    intro j
    fin_cases j
    · simpa using hf0.2.1
    · simpa using hf1.2.1
  refine ⟨?_, ?_, ?_⟩
  · have hcoord : ∀ᵐ (x : ℝ) ∂μI L, ∀ j : Fin 2,
        vectorToComponentsLinear L f j x = (f x) j := by
      rw [ae_all_iff]
      intro j
      exact (fiberCoordinate j).coeFn_compLp f
    filter_upwards [hcoord, hf0.1, hf1.1] with x hc h0x h1x
    have hvec : f x = gV x := by
      apply PiLp.ext
      intro j
      fin_cases j
      · simpa [gV] using (hc 0).symm.trans h0x
      · simpa [gV] using (hc 1).symm.trans h1x
    exact hvec
  · exact hVmem
  · intro x hx
    have hintL : IntegrableOn hV (Set.Ioc (0 : ℝ) L) volume := by
      simpa [IntegrableOn, LocalSpectral.μI] using hVmem.integrable (by norm_num)
    have hintx : IntegrableOn hV (Set.Ioc (0 : ℝ) x) volume :=
      hintL.mono_set (Set.Ioc_subset_Ioc_right hx.2)
    have hhint : IntervalIntegrable hV volume 0 x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).2 hintx
    have hmap0 := ContinuousLinearMap.intervalIntegral_comp_comm
      (fiberCoordinate (0 : Fin 2)) hhint
    have hmap1 := ContinuousLinearMap.intervalIntegral_comp_comm
      (fiberCoordinate (1 : Fin 2)) hhint
    change (∫ s in (0 : ℝ)..x, (hV s) 0) = (∫ s in (0 : ℝ)..x, hV s) 0 at hmap0
    change (∫ s in (0 : ℝ)..x, (hV s) 1) = (∫ s in (0 : ℝ)..x, hV s) 1 at hmap1
    apply PiLp.ext
    intro j
    fin_cases j
    · change g0 x = g0 0 + (∫ s in (0 : ℝ)..x, hV s) 0
      rw [← hmap0]
      simpa [hV] using hf0.2.2 x hx
    · change g1 x = g1 0 + (∫ s in (0 : ℝ)..x, hV s) 1
      rw [← hmap1]
      simpa [hV] using hf1.2.2 x hx


#print axioms vectorH1_of_scalarComponents

theorem freeResolventCandidate_range {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    {n : ℤ} {z : ℂ} (hz : OnGamma L r n z) (f : VectorInterval L) :
    ∃ g h, LocalSpectral.IsH1Rep L (freeResolventCandidate L n z f) g h ∧
      g L = (((LocalSpectral.parity n : ℤˣ) : ℤ) : ℂ) • g 0 ∧
      ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L,
        z • freeResolventCandidate L n z f x - f x =
          LocalSpectral.lopPt κ (0 : ℂ) (h x) (g x) := by
  let out := freeResolventCandidate L n z f
  obtain ⟨g0, h0, hrep0, hbound0, hact0⟩ :=
    scalarIntervalResolvent_range hL hr hsmall hz 0
      (vectorToComponentsLinear L f 0)
  obtain ⟨g1, h1, hrep1, hbound1, hact1⟩ :=
    scalarIntervalResolvent_range hL hr hsmall hz 1
      (vectorToComponentsLinear L f 1)
  let gV : ℝ → E2 := fun x => WithLp.toLp 2
    (fun j : Fin 2 => if j = 0 then g0 x else g1 x)
  let hV : ℝ → E2 := fun x => WithLp.toLp 2
    (fun j : Fin 2 => if j = 0 then h0 x else h1 x)
  have hrep0' : IntervalH1Rep (vectorToComponentsLinear L out 0) g0 h0 := by
    rw [freeResolventCandidate_component L n z f 0]
    exact hrep0
  have hrep1' : IntervalH1Rep (vectorToComponentsLinear L out 1) g1 h1 := by
    rw [freeResolventCandidate_component L n z f 1]
    exact hrep1
  have hH1 := vectorH1_of_scalarComponents (L := L) out g0 g1 h0 h1 hrep0' hrep1'
  have hboundary : gV L = (((LocalSpectral.parity n : ℤˣ) : ℤ) : ℂ) • gV 0 := by
    apply PiLp.ext
    intro j
    fin_cases j
    · simpa [gV, parityComplex] using hbound0
    · simpa [gV, parityComplex] using hbound1
  have hinput0 : (vectorToComponentsLinear L f 0 : ℝ → ℂ) =ᵐ[μI L]
      fun x => (f x) 0 := (fiberCoordinate 0).coeFn_compLp f
  have hinput1 : (vectorToComponentsLinear L f 1 : ℝ → ℂ) =ᵐ[μI L]
      fun x => (f x) 1 := (fiberCoordinate 1).coeFn_compLp f
  have houtput0 : (vectorToComponentsLinear L out 0 : ℝ → ℂ) =ᵐ[μI L]
      fun x => (out x) 0 := (fiberCoordinate 0).coeFn_compLp out
  have houtput1 : (vectorToComponentsLinear L out 1 : ℝ → ℂ) =ᵐ[μI L]
      fun x => (out x) 1 := (fiberCoordinate 1).coeFn_compLp out
  refine ⟨gV, hV, hH1, hboundary, ?_⟩
  have hfree : ∀ᵐ (x : ℝ) ∂μI L,
      z • out x - f x = (2 * Complex.I) • Jm (hV x) := by
    filter_upwards [hact0, hact1, hinput0, hinput1, houtput0, houtput1,
      hrep0.1, hrep1.1] with x ha0 ha1 hi0 hi1 ho0 ho1 hr0 hr1
    have hcoord0 :
        z * (out x) 0 - (f x) 0 = 2 * Complex.I * h0 x := by
      rw [← ho0, ← hi0]
      rw [freeResolventCandidate_component L n z f 0]
      simpa using ha0
    have hcoord1 :
        z * (out x) 1 - (f x) 1 = -(2 * Complex.I) * h1 x := by
      rw [← ho1, ← hi1]
      rw [freeResolventCandidate_component L n z f 1]
      simpa using ha1
    apply PiLp.ext
    intro j
    fin_cases j
    · simpa [hV, Jm, PiLp.smul_apply, PiLp.sub_apply] using hcoord0
    · simpa [hV, Jm, PiLp.smul_apply, PiLp.sub_apply] using hcoord1
  filter_upwards [hfree] with x hx
  simpa [lopPt_zero_potential, out] using hx


#print axioms freeResolventCandidate_range

theorem freeResolventCandidate_isResolvent {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    {n : ℤ} {z : ℂ} (hz : OnGamma L r n z) :
    LocalSpectral.IsResolvent L κ (fun _ => 0) (LocalSpectral.parity n) z
      (freeResolventCandidate L n z) := by
  constructor
  · intro f
    obtain ⟨g, h, hrep, hboundary, haction⟩ :=
      freeResolventCandidate_range (L := L) (κ := κ) hL hr hsmall hz f
    have hgraphAction : ∀ᵐ x ∂(LocalSpectral.μI L),
        ((z • freeResolventCandidate L n z f - f : VectorInterval L) : ℝ → E2) x =
          LocalSpectral.lopPt κ 0 (h x) (g x) := by
      have hsub := Lp.coeFn_sub (z • freeResolventCandidate L n z f) f
      have hsm := Lp.coeFn_smul z (freeResolventCandidate L n z f)
      filter_upwards [hsub, hsm, haction] with x hsubx hsmx hactx
      rw [hsubx, Pi.sub_apply, hsmx]
      exact hactx
    exact ⟨g, h, hrep, hboundary, hgraphAction⟩
  · intro p hp
    rcases hp with ⟨g, h, hrep, hboundary, hgraph⟩
    let q : VectorInterval L := z • p.1 - p.2
    have hqmap (j : Fin 2) : vectorToComponentsLinear L q j =
        z • vectorToComponentsLinear L p.1 j - vectorToComponentsLinear L p.2 j := by
      simp [q, map_sub, map_smul]
    have hqpoint (j : Fin 2) :
        ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L,
          vectorToComponentsLinear L q j x =
            z * vectorToComponentsLinear L p.1 j x -
              vectorToComponentsLinear L p.2 j x := by
      have hf := congrArg (fun a : ScalarInterval L => (a : ℝ → ℂ)) (hqmap j)
      filter_upwards [Lp.coeFn_smul z (vectorToComponentsLinear L p.1 j),
        Lp.coeFn_sub (z • vectorToComponentsLinear L p.1 j)
          (vectorToComponentsLinear L p.2 j)] with x hsm hsub
      have heq := congrFun hf x
      rw [hsub, Pi.sub_apply, hsm] at heq
      simpa [Pi.smul_apply] using heq
    have hsource :
        ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L,
          p.2 x = (2 * Complex.I) • Jm (h x) := by
      filter_upwards [hgraph] with x hx
      rw [hx]
      exact lopPt_zero_potential κ (h x) (g x)
    have hrep0 := vectorH1_component (L := L) p.1 g h hrep (0 : Fin 2)
    have hrep1 := vectorH1_component (L := L) p.1 g h hrep (1 : Fin 2)
    have hbound0 : g L 0 = parityComplex n * g 0 0 := by
      have hb := congrArg (fun v : E2 => v 0) hboundary
      simpa [parityComplex, PiLp.smul_apply] using hb
    have hbound1 : g L 1 = parityComplex n * g 0 1 := by
      have hb := congrArg (fun v : E2 => v 1) hboundary
      simpa [parityComplex, PiLp.smul_apply] using hb
    have hactionScalar (j : Fin 2) :
        ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L,
          (if j = 0 then Complex.I / 2 else -Complex.I / 2) *
              vectorToComponentsLinear L q j x =
            h x j - Complex.I * (if j = 0 then -z / 2 else z / 2) * g x j := by
      have hp1 : ∀ᵐ (x : ℝ) ∂μI L,
          vectorToComponentsLinear L p.1 j x = (p.1 x) j :=
        (fiberCoordinate j).coeFn_compLp p.1
      have hp2 : ∀ᵐ (x : ℝ) ∂μI L,
          vectorToComponentsLinear L p.2 j x = (p.2 x) j :=
        (fiberCoordinate j).coeFn_compLp p.2
      have hq := hqpoint j
      have hs := hsource
      have hsrc := hrep.1
      filter_upwards [hp1, hp2, hq, hs, hsrc] with x hp1x hp2x hqx hsx hsrcx
      have hcomponent : (p.2 x) j =
          (if j = 0 then 2 * Complex.I * h x j else -(2 * Complex.I) * h x j) := by
        have heq := congrArg (fun v : E2 => v j) hsx
        fin_cases j <;> simpa [Jm, LocalSpectral.Jm, vec2, PiLp.smul_apply] using heq
      have hp1val : vectorToComponentsLinear L p.1 j x = (g x) j := by
        exact hp1x.trans (congrArg (fun v : E2 => v j) hsrcx)
      have hp2val : vectorToComponentsLinear L p.2 j x = (p.2 x) j := hp2x
      have hqval : vectorToComponentsLinear L q j x =
          z * (g x j) - (p.2 x) j := by
        calc
          vectorToComponentsLinear L q j x =
              z * vectorToComponentsLinear L p.1 j x -
                vectorToComponentsLinear L p.2 j x := hqx
          _ = z * (g x j) - (p.2 x) j := by rw [hp1val, hp2val]
      rw [hqval, hcomponent]
      fin_cases j <;> simp <;> ring_nf <;> simp [Complex.I_sq]
    apply (vectorComponentsEquiv L).injective
    apply PiLp.ext
    intro j
    change vectorToComponentsLinear L (freeResolventCandidate L n z q) j =
      vectorToComponentsLinear L p.1 j
    rw [freeResolventCandidate_component L n z q j]
    fin_cases j
    · exact scalarIntervalResolvent_left_inverse hL hr hsmall hz 0
        (vectorToComponentsLinear L p.1 0) (vectorToComponentsLinear L q 0)
        (fun x => g x 0) (fun x => h x 0) hrep0 hbound0 (hactionScalar 0)
    · exact scalarIntervalResolvent_left_inverse hL hr hsmall hz 1
        (vectorToComponentsLinear L p.1 1) (vectorToComponentsLinear L q 1)
        (fun x => g x 1) (fun x => h x 1) hrep1 hbound1 (hactionScalar 1)


#print axioms freeResolventCandidate_isResolvent

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
