import NoCompromise.Regularity.RepresentativeDensity

/-! # Openness of both pure-density phases of a quasiminimizer -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma mem_densityZero_of_measure_inter_ball_eq_zero {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hz : volume (E ∩ ball x r) = 0) : x ∈ densityZero E := by
  change Tendsto (densityRatio E x) (𝓝[>] (0 : ℝ)) (𝓝 0)
  apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
  filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hr)] with t ht
  have ht0 : volume (E ∩ ball x t) = 0 :=
    measure_mono_null (inter_subset_inter_right E (ball_subset_ball ht.le)) hz
  simp only [densityRatio, ht0, ENNReal.toReal_zero, zero_div]

lemma mem_densityOne_of_compl_inter_ball_eq_zero {E : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) {x : AmbientSpace} {r : ℝ}
    (hr : 0 < r) (hz : volume (Eᶜ ∩ ball x r) = 0) : x ∈ densityOne E := by
  have h := mem_densityZero_of_measure_inter_ball_eq_zero hr hz
  simpa only [← densityOne_compl hmE.compl, compl_compl] using h

lemma perimeterIn_eq_zero_of_disjoint_essentialBoundary {E U : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hU : IsOpen U) (hdisj : Disjoint U (essentialBoundary E)) : perimeterIn E U = 0 := by
  rw [perimeterIn_eq_reducedBoundary_area E hE hmE hU]
  have he : U ∩ reducedBoundary E hE hmE = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact disjoint_left.mp hdisj hx.1 (reducedBoundary_subset_essentialBoundary hE hmE hx.2)
  rw [he, measure_empty]

lemma compl_volume_eq_zero_of_zero_perimeter_ball {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ densityOne E) {r : ℝ} (hr : 0 < r)
    (hp : perimeterIn E (ball x r) = 0) : volume (Eᶜ ∩ ball x r) = 0 := by
  have he : volume (E ∩ ball x r) ≠ 0 := by
    intro hz
    exact disjoint_left.mp (disjoint_densityZero_densityOne E)
      (mem_densityZero_of_measure_inter_ball_eq_zero hr hz) hx
  have hfin : volume (E ∩ ball x r) < ∞ :=
    (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
  have hepos : 0 < (volume (E ∩ ball x r)).toReal := ENNReal.toReal_pos he hfin.ne
  by_contra hc
  have hfc : volume (Eᶜ ∩ ball x r) < ∞ :=
    (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
  have hcpos : 0 < (volume (Eᶜ ∩ ball x r)).toReal := ENNReal.toReal_pos hc hfc.ne
  obtain ⟨C, _, hI⟩ := relative_isoperimetric_ball_three_real
  have hi := hI E hE hmE x r hr
  rw [measureReal_def, canonicalPerimeterMeasure_open E hE hmE isOpen_ball, hp,
    ENNReal.toReal_zero, mul_zero, sdiff_eq_compl_inter] at hi
  exact (not_le.mpr (Real.rpow_pos_of_pos (lt_min hepos hcpos) _)) hi

theorem IsOmegaMinimal.isOpen_densityOne {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) : IsOpen (densityOne E) := by
  apply Metric.isOpen_iff.mpr
  intro x hx
  have hxc : x ∈ (essentialBoundary E)ᶜ := by exact fun h => h (Or.inr hx)
  obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp
    hE.isClosed_essentialBoundary.isOpen_compl x hxc
  have hd : Disjoint (ball x r) (essentialBoundary E) := disjoint_left.mpr
    (fun _ hz he => hs hz he)
  have hp := perimeterIn_eq_zero_of_disjoint_essentialBoundary hE.locallyFinite
    hE.nullMeasurable isOpen_ball hd
  have hv := compl_volume_eq_zero_of_zero_perimeter_ball hE.locallyFinite hE.nullMeasurable hx hr hp
  refine ⟨r, hr, fun z hz => ?_⟩
  obtain ⟨s, hs0, hsb⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
  exact mem_densityOne_of_compl_inter_ball_eq_zero hE.nullMeasurable hs0
    (measure_mono_null (inter_subset_inter_right Eᶜ hsb) hv)

theorem IsOmegaMinimal.isOpen_densityZero {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) : IsOpen (densityZero E) := by
  rw [← densityOne_compl hE.nullMeasurable]
  exact hE.compl.isOpen_densityOne

end LiquidDrop
