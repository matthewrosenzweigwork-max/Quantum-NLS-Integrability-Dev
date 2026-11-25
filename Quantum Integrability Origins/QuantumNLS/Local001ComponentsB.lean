import QuantumNLS.Local001GaugeB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable (L : ℝ) [Fact (0 < L)]

abbrev ScalarPair (L : ℝ) := PiLp 2 (fun _ : Fin 2 => ScalarInterval L)


#print axioms ScalarPair

def fiberCoordinate (j : Fin 2) : E2 →L[ℂ] ℂ :=
  PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) (β := fun _ : Fin 2 => ℂ) j


#print axioms fiberCoordinate

def vectorToComponentsLinear : VectorInterval L →ₗ[ℂ] ScalarPair L where
  toFun f := WithLp.toLp 2 (fun j => (fiberCoordinate j).compLp f)
  map_add' f g := by
    apply PiLp.ext
    intro j
    exact (fiberCoordinate j).compLpL 2 (μI L) |>.map_add f g
  map_smul' c f := by
    apply PiLp.ext
    intro j
    exact (fiberCoordinate j).compLpL 2 (μI L) |>.map_smul c f


#print axioms vectorToComponentsLinear

def componentsToVector (v : ScalarPair L) : VectorInterval L := by
  let g : ℝ → E2 := fun x => WithLp.toLp 2 (fun j => v j x)
  have hg : MemLp g 2 (μI L) := by
    change MemLp (fun x : ℝ => (WithLp.toLp 2 (fun j => v j x) : E2)) 2 (μI L)
    rw [MeasureTheory.memLp_piLp_iff]
    intro j
    exact Lp.memLp (v j)
  exact hg.toLp g


#print axioms componentsToVector

def fiberInsertLinear (j : Fin 2) : ℂ →ₗ[ℂ] E2 where
  toFun a := PiLp.single (p := (2 : ℝ≥0∞)) (β := fun _ : Fin 2 => ℂ) j a
  map_add' a b := by simp [PiLp.single_add]
  map_smul' c a := by
    apply PiLp.ext
    intro i
    by_cases h : i = j
    · subst i
      simp
    · simp [h]


#print axioms fiberInsertLinear

def fiberInsert (j : Fin 2) : ℂ →ₗᵢ[ℂ] E2 where
  toLinearMap := fiberInsertLinear j
  norm_map' a := by
    change ‖PiLp.single (p := (2 : ℝ≥0∞)) (β := fun _ : Fin 2 => ℂ) j a‖ = ‖a‖
    exact PiLp.norm_single (2 : ℝ≥0∞) (fun _ : Fin 2 => ℂ) j a


#print axioms fiberInsert

def intervalFiberInsert (j : Fin 2) : ScalarInterval L →L[ℂ] VectorInterval L :=
  (fiberInsert j).toContinuousLinearMap.compLpL 2 (volume.restrict (Set.Ioc 0 L))


#print axioms intervalFiberInsert

def componentsToVectorLinear : ScalarPair L →ₗ[ℂ] VectorInterval L where
  toFun v := ∑ j : Fin 2, intervalFiberInsert L j (v j)
  map_add' v w := by
    simp only [PiLp.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [PiLp.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

#print axioms componentsToVectorLinear

theorem fiberInsert_sum (v : E2) :
    (∑ j : Fin 2, fiberInsert j (v j)) = v := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [fiberInsert, fiberInsertLinear]

#print axioms fiberInsert_sum

theorem component_intervalFiberInsert (i j : Fin 2) (f : ScalarInterval L) :
    vectorToComponentsLinear L (intervalFiberInsert L j f) i =
      if i = j then f else 0 := by
  by_cases hij : i = j
  · subst i
    simp
    change (fiberCoordinate j).compLp (intervalFiberInsert L j f) = f
    apply Lp.ext
    have h₁ := (fiberCoordinate j).coeFn_compLp (intervalFiberInsert L j f)
    have h₂ := (fiberInsert j).toContinuousLinearMap.coeFn_compLpL f
    have h₂' : (intervalFiberInsert L j f : VectorInterval L) =ᵐ[volume.restrict (Set.Ioc 0 L)]
        fun x => fiberInsert j (f x) := by
      filter_upwards [h₂] with x hx
      change ((fiberInsert j).toContinuousLinearMap.compLpL 2
        (volume.restrict (Set.Ioc 0 L)) f) x =
          (fiberInsert j).toContinuousLinearMap (f x) at hx
      exact hx
    filter_upwards [h₁, h₂'] with x h₁ h₂
    rw [h₁, h₂]
    simp [fiberCoordinate, fiberInsert, fiberInsertLinear]
    rfl
  · simp only [if_neg hij]
    change (fiberCoordinate i).compLp (intervalFiberInsert L j f) = 0
    apply Lp.ext
    have h₁ := (fiberCoordinate i).coeFn_compLp (intervalFiberInsert L j f)
    have h₂ := (fiberInsert j).toContinuousLinearMap.coeFn_compLpL f
    have h₂' : (intervalFiberInsert L j f : VectorInterval L) =ᵐ[volume.restrict (Set.Ioc 0 L)]
        fun x => fiberInsert j (f x) := by
      filter_upwards [h₂] with x hx
      change ((fiberInsert j).toContinuousLinearMap.compLpL 2
        (volume.restrict (Set.Ioc 0 L)) f) x =
          (fiberInsert j).toContinuousLinearMap (f x) at hx
      exact hx
    have hzero : ∀ᵐ (x : ℝ) ∂μI L, (0 : ScalarInterval L) x = (0 : ℂ) :=
      Lp.coeFn_zero ℂ 2 (μI L)
    filter_upwards [h₁, h₂', hzero] with x h₁ h₂ hzero
    rw [h₁, h₂]
    change (PiLp.single (p := (2 : ℝ≥0∞))
      (β := fun _ : Fin 2 => ℂ) j (f x)) i = (0 : ScalarInterval L) x
    rw [PiLp.ofLp_single, Pi.single_eq_of_ne' (fun hji => hij hji.symm)]
    rw [hzero]

#print axioms component_intervalFiberInsert

theorem vectorToComponents_componentsToVector (v : ScalarPair L) :
    vectorToComponentsLinear L (componentsToVectorLinear L v) = v := by
  apply PiLp.ext
  intro i
  change ((vectorToComponentsLinear L)
      (∑ j : Fin 2, intervalFiberInsert L j (v j))) i = v i
  rw [map_sum]
  fin_cases i <;> simp [component_intervalFiberInsert]

#print axioms vectorToComponents_componentsToVector

omit [Fact (0 < L)] in
theorem componentsToVector_vectorToComponents (f : VectorInterval L) :
    componentsToVectorLinear L (vectorToComponentsLinear L f) = f := by
  change (∑ j : Fin 2,
      intervalFiberInsert L j (vectorToComponentsLinear L f j)) = f
  apply Lp.ext
  have hcoord : ∀ᵐ (x : ℝ) ∂μI L, ∀ j : Fin 2,
      vectorToComponentsLinear L f j x = (f x) j := by
    rw [ae_all_iff]
    intro j
    have h := (fiberCoordinate j).coeFn_compLp f
    filter_upwards [h] with x hx
    change (fiberCoordinate j).compLp f x = (fiberCoordinate j) (f x)
    exact hx
  have hinsert : ∀ᵐ (x : ℝ) ∂μI L, ∀ j : Fin 2,
      intervalFiberInsert L j (vectorToComponentsLinear L f j) x =
        fiberInsert j (vectorToComponentsLinear L f j x) := by
    rw [ae_all_iff]
    intro j
    exact (fiberInsert j).toContinuousLinearMap.coeFn_compLpL
      (vectorToComponentsLinear L f j)
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : Fin 2 => intervalFiberInsert L j (vectorToComponentsLinear L f j))
  filter_upwards [hcoord, hinsert, hsum] with x hxcoord hxinsert hsum
  rw [hsum]
  calc
    (∑ j : Fin 2, intervalFiberInsert L j (vectorToComponentsLinear L f j) x) =
        ∑ j : Fin 2, fiberInsert j (vectorToComponentsLinear L f j x) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hxinsert j
    _ = ∑ j : Fin 2, fiberInsert j (f x j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hxcoord j]
    _ = f x := fiberInsert_sum (f x)


#print axioms componentsToVector_vectorToComponents

theorem vectorToComponents_inner (f g : VectorInterval L) :
    ⟪vectorToComponentsLinear L f, vectorToComponentsLinear L g⟫_ℂ = ⟪f, g⟫_ℂ := by
  classical
  have hcoordf : ∀ᵐ (x : ℝ) ∂μI L, ∀ j : Fin 2,
      vectorToComponentsLinear L f j x = (f x) j := by
    rw [ae_all_iff]
    intro j
    have h := (fiberCoordinate j).coeFn_compLp f
    filter_upwards [h] with x hx
    exact hx
  have hcoordg : ∀ᵐ (x : ℝ) ∂μI L, ∀ j : Fin 2,
      vectorToComponentsLinear L g j x = (g x) j := by
    rw [ae_all_iff]
    intro j
    have h := (fiberCoordinate j).coeFn_compLp g
    filter_upwards [h] with x hx
    exact hx
  have hpoint : (fun x : ℝ =>
      ∑ j : Fin 2, ⟪vectorToComponentsLinear L f j x,
        vectorToComponentsLinear L g j x⟫_ℂ) =ᵐ[μI L]
      fun x => ⟪f x, g x⟫_ℂ := by
    filter_upwards [hcoordf, hcoordg] with x hf hg
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hf j, hg j]
  have hInt : ∀ j : Fin 2, Integrable
      (fun x : ℝ => ⟪vectorToComponentsLinear L f j x,
        vectorToComponentsLinear L g j x⟫_ℂ) (μI L) := by
    intro j
    exact MeasureTheory.L2.integrable_inner _ _
  rw [PiLp.inner_apply]
  simp only [MeasureTheory.L2.inner_def]
  change (∑ j : Fin 2, ∫ x : ℝ,
      ⟪vectorToComponentsLinear L f j x, vectorToComponentsLinear L g j x⟫_ℂ ∂μI L) =
    ∫ x : ℝ, ⟪f x, g x⟫_ℂ ∂μI L
  rw [← integral_finsetSum Finset.univ (fun j hj => hInt j)]
  exact integral_congr_ae hpoint


#print axioms vectorToComponents_inner

def vectorComponentsEquiv : VectorInterval L ≃ₗ[ℂ] ScalarPair L where
  toFun := vectorToComponentsLinear L
  invFun := componentsToVectorLinear L
  left_inv := componentsToVector_vectorToComponents L
  right_inv := vectorToComponents_componentsToVector L
  map_add' := by
    intro f g
    exact (vectorToComponentsLinear L).map_add f g
  map_smul' := by
    intro c f
    exact (vectorToComponentsLinear L).map_smul c f


#print axioms vectorComponentsEquiv

def vectorComponentsIsometry : VectorInterval L ≃ₗᵢ[ℂ] ScalarPair L :=
  (vectorComponentsEquiv L).isometryOfInner (vectorToComponents_inner L)


#print axioms vectorComponentsIsometry

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
