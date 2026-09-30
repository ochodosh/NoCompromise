module

public import NoCompromise.BV.Density

@[expose] public section

/-! # Cap density is unchanged by almost-everywhere local agreement -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace LiquidDrop

lemma densityRatio_eventuallyEq_of_ae_on_open {n : ℕ}
    {E F U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (hEF : E =ᵐ[volume.restrict U] F) :
    densityRatio E x =ᶠ[𝓝[>] (0 : ℝ)] densityRatio F x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hae := (ae_restrict_iff' hU.measurableSet).mp hEF
  filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hδ)] with r hr
  have hsub : ball x r ⊆ U := (ball_subset_ball hr.le).trans hball
  have he : (E ∩ ball x r : Set (EuclideanSpace ℝ (Fin n))) =ᵐ[volume]
      (F ∩ ball x r : Set (EuclideanSpace ℝ (Fin n))) := by
    filter_upwards [hae] with z hz
    apply propext
    constructor
    · intro hzE
      exact ⟨(hz (hsub hzE.2)).mp hzE.1, hzE.2⟩
    · intro hzF
      exact ⟨(hz (hsub hzF.2)).mpr hzF.1, hzF.2⟩
  simp only [densityRatio, measure_congr he]

lemma densityOne_mem_iff_of_ae_on_open {n : ℕ}
    {E F U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (hEF : E =ᵐ[volume.restrict U] F) : x ∈ densityOne E ↔ x ∈ densityOne F :=
  tendsto_congr' (densityRatio_eventuallyEq_of_ae_on_open hU hx hEF)

lemma densityZero_mem_iff_of_ae_on_open {n : ℕ}
    {E F U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (hEF : E =ᵐ[volume.restrict U] F) : x ∈ densityZero E ↔ x ∈ densityZero F :=
  tendsto_congr' (densityRatio_eventuallyEq_of_ae_on_open hU hx hEF)

end LiquidDrop
