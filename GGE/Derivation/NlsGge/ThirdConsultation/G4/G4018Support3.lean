import Mathlib
/- H215_PRODRATIO01 (proof development, AUTHOR; not self-reviewed). Pro round 9 section 10, step 4.
   Ratio of two convergent products along a SummationFilter, with nonzero limit of the denominator:
   the termwise quotient converges to the quotient of the limits. Requires HasProd of both families
   (no identity is assumed). -/
set_option autoImplicit false

namespace NlsGge.G4018Support

theorem hasProd_div_of_hasProd {ι : Type*} (a b : ι → ℂ) (L : SummationFilter ι) (P Q : ℂ)
    (ha : HasProd a P L) (hb : HasProd b Q L) (hQ : Q ≠ 0) :
    HasProd (fun i => a i / b i) (P / Q) L := by
  have ha' : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, a i) L.filter (nhds P) := ha
  have hb' : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, b i) L.filter (nhds Q) := hb
  have hdiv : Filter.Tendsto (fun s : Finset ι => (∏ i ∈ s, a i) / (∏ i ∈ s, b i)) L.filter
      (nhds (P / Q)) := ha'.div hb' hQ
  refine hdiv.congr (fun s => ?_)
  rw [Finset.prod_div_distrib]

end NlsGge.G4018Support
