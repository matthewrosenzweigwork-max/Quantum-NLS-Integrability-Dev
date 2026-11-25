import NlsGge.GK38.PoissonMixedDiscriminantColumns

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

def columnDirWedge38 (φ : PotPair) (z ζ : ℂ) (i j : Fin 2) (s : ℝ) : ℂ :=
  pairBracket38 (starProd38 (fundColumn38 φ ζ s i) (fundColumn38 φ ζ s j))
    (starProd38 (pairKernelExt38 (state φ z ![1,1]) s)
      (pairKernelExt38 (state φ z ![1,1]) s))

def weightedColumnDirIntegral38 (φ : PotPair) (z ζ : ℂ) : ℂ :=
  monodromyPair φ ζ 0 1 * (∫ s in (0 : ℝ)..1, columnDirWedge38 φ z ζ 0 0 s) +
  (monodromyPair φ ζ 1 1-monodromyPair φ ζ 0 0) *
    (∫ s in (0 : ℝ)..1, columnDirWedge38 φ z ζ 0 1 s) -
  monodromyPair φ ζ 1 0 * (∫ s in (0 : ℝ)..1, columnDirWedge38 φ z ζ 1 1 s)

theorem state_single_ext_eq_column38 (φ : PotPair) (ζ : ℂ) (j : Fin 2) (s : ℝ) :
    pairKernelExt38 (state φ ζ (Pi.single j (1 : ℂ) : PairVec38)) s = fundColumn38 φ ζ s j := by
  ext i
  fin_cases j <;> simp [state_ext,fundColumn38]

theorem column_isPairSolution38 (φ : PotPair) (ζ : ℂ) (j : Fin 2) :
    IsPairSolution38 φ ζ (fun s => fundColumn38 φ ζ s j) := by
  have h := state_isPairSolution38 φ ζ (Pi.single j (1 : ℂ) : PairVec38)
  have he : pairKernelExt38 (state φ ζ (Pi.single j (1 : ℂ) : PairVec38)) =
      fun s => fundColumn38 φ ζ s j := funext (state_single_ext_eq_column38 φ ζ j)
  rw [he] at h
  exact h

theorem intervalIntegrable_columnDirWedge38 (φ : PotPair) (z ζ : ℂ) (i j : Fin 2) :
    IntervalIntegrable (columnDirWedge38 φ z ζ i j) volume 0 1 :=
  intervalIntegrable_starBracket38 (column_isPairSolution38 φ ζ i)
    (state_isPairSolution38 φ z ![1,1]) (column_isPairSolution38 φ ζ j)
    (state_isPairSolution38 φ z ![1,1])

theorem columnDir_integral_identity38 (φ : PotPair) (z ζ : ℂ) (i j : Fin 2)
    (hr : dirichletChar φ z = 0) :
    (normingFactor φ z)^2 *
      ((Pi.single i (1 : ℂ) : PairVec38) 0*(monodromyPair φ ζ 0 0-monodromyPair φ ζ 1 0) +
        (Pi.single i (1 : ℂ) : PairVec38) 1*(monodromyPair φ ζ 0 1-monodromyPair φ ζ 1 1)) *
      ((Pi.single j (1 : ℂ) : PairVec38) 0*(monodromyPair φ ζ 0 0-monodromyPair φ ζ 1 0) +
        (Pi.single j (1 : ℂ) : PairVec38) 1*(monodromyPair φ ζ 0 1-monodromyPair φ ζ 1 1)) -
      ((Pi.single i (1 : ℂ) : PairVec38) 0-(Pi.single i (1 : ℂ) : PairVec38) 1)*
        ((Pi.single j (1 : ℂ) : PairVec38) 0-(Pi.single j (1 : ℂ) : PairVec38) 1) =
    2*Complex.I*(ζ-z) * ∫ s in (0 : ℝ)..1, columnDirWedge38 φ z ζ i j s := by
  have h := integrated_seed_dirichlet_star38 φ z ζ (Pi.single i (1 : ℂ) : PairVec38)
    (Pi.single j (1 : ℂ) : PairVec38) hr
  simpa only [state_single_ext_eq_column38,columnDirWedge38] using h

theorem weightedColumnDir_integral_identity38 (φ : PotPair) (z ζ : ℂ)
    (hr : dirichletChar φ z = 0) :
    -2*Complex.I*dirichletChar φ ζ*((normingFactor φ z)^2-1) =
      2*Complex.I*(ζ-z)*weightedColumnDirIntegral38 φ z ζ := by
  have h00 := columnDir_integral_identity38 φ z ζ 0 0 hr
  have h01 := columnDir_integral_identity38 φ z ζ 0 1 hr
  have h11 := columnDir_integral_identity38 φ z ζ 1 1 hr
  norm_num [Pi.single_apply] at h00 h01 h11
  have hw : monodromyPair φ ζ 0 1*
      ((monodromyPair φ ζ 0 0-monodromyPair φ ζ 1 0)^2*(normingFactor φ z)^2-1) +
    (monodromyPair φ ζ 1 1-monodromyPair φ ζ 0 0)*
      ((monodromyPair φ ζ 0 0-monodromyPair φ ζ 1 0)*
        (monodromyPair φ ζ 0 1-monodromyPair φ ζ 1 1)*(normingFactor φ z)^2+1) -
    monodromyPair φ ζ 1 0*
      ((monodromyPair φ ζ 0 1-monodromyPair φ ζ 1 1)^2*(normingFactor φ z)^2-1) =
    2*Complex.I*(ζ-z)*weightedColumnDirIntegral38 φ z ζ := by
    unfold weightedColumnDirIntegral38
    linear_combination monodromyPair φ ζ 0 1*h00 +
      (monodromyPair φ ζ 1 1-monodromyPair φ ζ 0 0)*h01 - monodromyPair φ ζ 1 0*h11
  rw [discriminant_column_endpoint_polynomial38 _ _ (monodromy_det_scalar φ ζ)] at hw
  rw [← hw,dirichletChar_eq]
  field_simp
  ring

end
end NlsGge.GK38.PoissonMixed38
