import Mathlib
                                                                                             
                                                                                                   
                                                                                                   
                               
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
