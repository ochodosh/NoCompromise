module

public import NoCompromise.Regularity.DeformationLimitProperties
public import NoCompromise.Regularity.DeformationWall

@[expose] public section

/-! # Assembling the disk, annulus, and zero-wall perimeter estimate -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace LiquidDrop

lemma cylindricalCore_cover (r σ τ : ℝ) :
    cylindricalCore r τ ⊆ cylindricalCore r σ ∪ cylindricalTransition r σ τ ∪
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ = σ ∧ |x 2| < r} := by
  intro x hx
  rcases lt_trichotomy ‖graphProjectionN 2 x‖ σ with hlt | he | hgt
  · exact Or.inl (Or.inl ⟨hlt, hx.2⟩)
  · exact Or.inr ⟨he, hx.2.2⟩
  · exact Or.inl (Or.inr ⟨⟨hgt, hx.1⟩, hx.2⟩)

theorem IsSlabCapConfiguration.compression_limit_perimeter_bound
    {E F : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    (hF : HasLocallyFinitePerimeter F) (hmF : NullMeasurableSet F volume)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ ≤ r)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hae : ∀ᵐ x : AmbientSpace ∂volume,
      Tendsto (fun j => (compressionCompetitor E r σ τ (ε j) c).indicator
        (fun _ => (1 : ℝ)) x) atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) x)))
    (hl1 : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ x in K,
        |(compressionCompetitor E r σ τ (ε j) c).indicator (fun _ => (1 : ℝ)) x -
          F.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0)) :
    perimeterIn F (cylindricalCore r τ) ≤
      perimeterIn E (cylindricalTransition r σ τ) + ENNReal.ofReal (Real.pi * σ ^ 2) +
        ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
          ∫⁻ x in standardCylinder r, ENNReal.ofReal ((x 2 - c) ^ 2)
            ∂canonicalPerimeterMeasure E hE hmE := by
  let μ := canonicalPerimeterMeasure F hF hmF
  have hcore := h.compression_limit_core hσ hst (hst.le.trans hτr) hε hε1 hεlim hae
  have hc : |c| < r := by
    have hp := mul_pos h.1.2.1 h.1.1
    linarith [h.1.2.2.2.1]
  have hdisk := perimeterIn_core_eq_disk_of_ae_phase hσ.le (hst.le.trans hτr) hc hcore
  have hann := h.compression_limit_annular_bound hmF hσ hst hτr hε hε1 hl1
  have hwall := compression_inner_wall_perimeter_zero hF hmF hσ hst (hst.trans_le hτr)
    (h.compression_limit_phases hσ hst hε hε1 hεlim hae)
  have hm : μ (cylindricalCore r τ) ≤ μ (cylindricalCore r σ) +
      μ (cylindricalTransition r σ τ) +
        μ {x : AmbientSpace | ‖graphProjectionN 2 x‖ = σ ∧ |x 2| < r} := by
    apply (measure_mono (cylindricalCore_cover r σ τ)).trans
    exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  rw [hwall, add_zero,
    canonicalPerimeterMeasure_open F hF hmF (isOpen_cylindricalCore r τ),
    canonicalPerimeterMeasure_open F hF hmF (isOpen_cylindricalCore r σ),
    canonicalPerimeterMeasure_open F hF hmF (isOpen_cylindricalTransition r σ τ), hdisk] at hm
  apply hm.trans
  calc
    _ ≤ ENNReal.ofReal (Real.pi * σ ^ 2) +
        (perimeterIn E (cylindricalTransition r σ τ) +
          ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
            ∫⁻ x in standardCylinder r, ENNReal.ofReal ((x 2 - c) ^ 2)
              ∂canonicalPerimeterMeasure E hE hmE) := add_le_add le_rfl hann
    _ = _ := by ac_rfl

end LiquidDrop
