import NlsGge.GK38.PairAnalyticOp

/-!
# F3: joint analyticity of the fundamental solution and of the monodromy in `(φ, z)`

Source: Grébert-Kappeler book, Chapter I, section 1 (Theorem 1.1, analyticity statement).
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

/-- The constant identity matrix function, in `PairCont38`. -/
def idCont38 : PairCont38 := ContinuousMap.const _ (fun i j => if i = j then (1 : ℂ) else 0)

theorem freeFundP_eq (z : ℂ) : freeFundP z = mulFree38 z idCont38 := by
  ext t i j
  rw [mulFree38_apply]
  show freeE z t i j = freeE z t i i * (if i = j then (1 : ℂ) else 0)
  fin_cases i <;> fin_cases j <;> simp [freeE]

theorem analyticOnNhd_freeFundP : AnalyticOnNhd ℂ freeFundP Set.univ := by
  intro z hz
  have : freeFundP = fun z => mulFree38 z idCont38 := funext freeFundP_eq
  rw [this]
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := PairCont38 →L[ℂ] PairCont38)
    (F := PairCont38) (ContinuousLinearMap.apply ℂ PairCont38 idCont38) (mulFree38 z)).comp
      (analyticOnNhd_mulFree38 z hz)

theorem fundContP_eq (φ : PotPair) (z : ℂ) :
    fundContP φ z = Ring.inverse (1 - volterraP φ z) (freeFundP z) := rfl

/-- Evaluation of an operator on a vector is analytic jointly. -/
theorem analyticAt_apply_op38 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : E → PairCont38 →L[ℂ] PairCont38} {u : E → PairCont38} {p : E}
    (hT : AnalyticAt ℂ T p) (hu : AnalyticAt ℂ u p) : AnalyticAt ℂ (fun x => T x (u x)) p :=
  ((ContinuousLinearMap.id ℂ (PairCont38 →L[ℂ] PairCont38)).analyticAt_bilinear
    (T p, u p)).comp₂ hT hu

theorem analyticAt_ringInverse_one_sub_volterraP (p : PotPair × ℂ) :
    AnalyticAt ℂ (fun q : PotPair × ℂ => Ring.inverse (1 - volterraP q.1 q.2)) p := by
  have hV : AnalyticAt ℂ (fun q : PotPair × ℂ => (1 : PairCont38 →L[ℂ] PairCont38) -
      volterraP q.1 q.2) p :=
    analyticAt_const.sub (analyticOnNhd_volterraP p (Set.mem_univ _))
  have h0 : AnalyticAt ℂ Ring.inverse ((1 : PairCont38 →L[ℂ] PairCont38) - volterraP p.1 p.2) :=
    analyticAt_inverse (𝕜 := ℂ) (A := PairCont38 →L[ℂ] PairCont38)
      (IsUnit.unit (isUnit_one_sub_volterraP p.1 p.2))
  exact AnalyticAt.comp (g := Ring.inverse)
    (f := fun q : PotPair × ℂ => (1 : PairCont38 →L[ℂ] PairCont38) - volterraP q.1 q.2) h0 hV

/-- The fundamental solution, as a `C([0,1], M₂)`-valued map, is jointly analytic in `(φ, z)`. -/
theorem analyticOnNhd_fundContP :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => fundContP p.1 p.2) Set.univ := by
  intro p _
  exact analyticAt_apply_op38 (analyticAt_ringInverse_one_sub_volterraP p)
    ((analyticOnNhd_freeFundP p.2 (Set.mem_univ _)).comp analyticAt_snd)

/-- The entry `(i,j)` of `M(t, z, φ)`, as a function of `(φ, z)`. -/
def fundEntryL38 (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) : PairCont38 →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) j).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) i).comp
      (ContinuousMap.evalCLM ℂ t))

theorem analyticOnNhd_fundPair (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => fundPair p.1 p.2 t i j) Set.univ := fun p hp =>
  AnalyticAt.comp (f := fun q : PotPair × ℂ => fundContP q.1 q.2)
    (g := ⇑(fundEntryL38 t i j))
    (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := PairCont38) (F := ℂ) (fundEntryL38 t i j)
      (fundContP p.1 p.2)) (analyticOnNhd_fundContP p hp)

/-- F3, analyticity (book Thm 1.1): the entries of the monodromy matrix are analytic in `(φ, z)`
on all of `PotPair × ℂ`. -/
theorem analyticOnNhd_monodromyPair (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => monodromyPair p.1 p.2 i j) Set.univ :=
  analyticOnNhd_fundPair ⟨1, zero_le_one, le_rfl⟩ i j

end
end NlsGge.GK38
