import NoCompromise.Regularity.ZeroExcessOrder

/-! # A binary height-ordered phase has one lower threshold -/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal
namespace LiquidDrop

lemma volume_inner_level_eq_zero {ν : AmbientSpace} (hν : ‖ν‖ = 1) (c : ℝ) :
    volume {x : AmbientSpace | inner ℝ ν x = c} = 0 := by
  have he : {x : AmbientSpace | inner ℝ ν x = c} =
      (fun x => (-c) • ν + x) ⁻¹' {x : AmbientSpace | inner ℝ ν x = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hν, one_pow, mul_one]
    constructor <;> intro h <;> linarith
  rw [he, measure_preimage_add]
  exact volume_inner_eq_zero_of_unit hν

/-- On a bounded region, binary height ordering gives either the empty phase
or a lower halfspace. A cutting plane outside the region covers the full phase. -/
theorem indicator_threshold_of_height_order {E S U : Set AmbientSpace} {ν : AmbientSpace}
    (hν : ‖ν‖ = 1) (hU : MeasurableSet U) (hbU : Bornology.IsBounded U)
    (hS : ∀ᵐ x : AmbientSpace, x ∈ S)
    (horder : ∀ x ∈ S ∩ U, ∀ y ∈ S ∩ U, inner ℝ ν x ≤ inner ℝ ν y →
      E.indicator (fun _ => (1 : ℝ)) y ≤ E.indicator (fun _ => (1 : ℝ)) x) :
    E =ᵐ[volume.restrict U] (∅ : Set AmbientSpace) ∨
      ∃ c : ℝ, E =ᵐ[volume.restrict U] {x : AmbientSpace | inner ℝ ν x < c} := by
  classical
  let H : Set ℝ := (fun x => inner ℝ ν x) '' ((S ∩ U) ∩ E)
  by_cases hH : H.Nonempty
  · right
    have hB : BddAbove H := by
      obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : AmbientSpace) |>.mp hbU
      refine ⟨R, ?_⟩
      rintro t ⟨x, hx, rfl⟩
      have hi := (le_abs_self (inner ℝ ν x)).trans (abs_real_inner_le_norm ν x)
      rw [hν, one_mul] at hi
      have hxR : ‖x‖ < R := by simpa only [mem_ball, dist_zero_right] using hR hx.1.2
      exact hi.trans hxR.le
    refine ⟨sSup H, ?_⟩
    have hplane : ∀ᵐ x : AmbientSpace, inner ℝ ν x ≠ sSup H := by
      rw [ae_iff]
      simpa using volume_inner_level_eq_zero hν (sSup H)
    filter_upwards [ae_restrict_of_ae hS, ae_restrict_mem hU, ae_restrict_of_ae hplane]
      with x hxS hxU hxP
    apply propext
    change x ∈ E ↔ inner ℝ ν x < sSup H
    constructor
    · intro hxE
      exact lt_of_le_of_ne (le_csSup hB ⟨x, ⟨⟨hxS, hxU⟩, hxE⟩, rfl⟩) hxP
    · intro hx
      obtain ⟨t, ⟨y, hy, rfl⟩, hxy⟩ := exists_lt_of_lt_csSup hH hx
      have ho := horder x ⟨hxS, hxU⟩ y hy.1 hxy.le
      by_contra hn
      simp only [indicator_of_mem hy.2, indicator_of_notMem hn] at ho
      norm_num at ho
  · left
    filter_upwards [ae_restrict_of_ae hS, ae_restrict_mem hU] with x hxS hxU
    apply propext
    constructor
    · intro hxE
      exact (hH ⟨inner ℝ ν x, ⟨x, ⟨⟨hxS, hxU⟩, hxE⟩, rfl⟩⟩).elim
    · exact fun h => h.elim

/-- The local distributional constant-normal classification. -/
theorem HasLocalConstantIndicatorPolar.classification
    {E U : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace}
    (h : HasLocalConstantIndicatorPolar E U μ ν) (hE : NullMeasurableSet E volume)
    (hν : ‖ν‖ = 1) (hU : IsOpen U) (hcU : Convex ℝ U)
    (hbU : Bornology.IsBounded U) :
    E =ᵐ[volume.restrict U] (∅ : Set AmbientSpace) ∨
      E =ᵐ[volume.restrict U] (univ : Set AmbientSpace) ∨
      ∃ c : ℝ, E =ᵐ[volume.restrict U] {x : AmbientSpace | inner ℝ ν x < c} := by
  obtain ⟨S, hS, ho⟩ := h.ae_height_order hE hU hcU
  rcases indicator_threshold_of_height_order hν hU.measurableSet hbU hS ho with he | he
  · exact Or.inl he
  · exact Or.inr (Or.inr he)

end LiquidDrop
