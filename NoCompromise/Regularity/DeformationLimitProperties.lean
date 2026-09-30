module

public import NoCompromise.Regularity.DeformationCaps
public import NoCompromise.Regularity.DeformationDisk
public import NoCompromise.Regularity.DeformationAnnulus
public import NoCompromise.Regularity.DeformationLimitPhases

@[expose] public section

/-! # Core, caps, exterior agreement, and annular estimate of actual limits -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

theorem IsSlabCapConfiguration.compression_limit_core
    {E F : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hsr : σ ≤ r)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hlim : ∀ᵐ x : AmbientSpace ∂volume,
      Tendsto (fun j => (compressionCompetitor E r σ τ (ε j) c).indicator
        (fun _ => (1 : ℝ)) x) atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) x))) :
    F.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict (cylindricalCore r σ)]
      {x : AmbientSpace | x 2 < c}.indicator (fun _ => (1 : ℝ)) := by
  apply (ae_restrict_iff' (isOpen_cylindricalCore r σ).measurableSet).mpr
  filter_upwards [h.compression_core_ae_tendsto hσ hst hsr hε hε1 hεlim, hlim] with x hx hxl
  intro hxC
  exact tendsto_nhds_unique hxl
    (hx hxC.1 (abs_lt.mp hxC.2.2).1 (abs_lt.mp hxC.2.2).2)

theorem IsSlabCapConfiguration.compression_limit_caps
    {E F : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hlim : ∀ᵐ x : AmbientSpace ∂volume,
      Tendsto (fun j => (compressionCompetitor E r σ τ (ε j) c).indicator
        (fun _ => (1 : ℝ)) x) atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) x))) :
    hausdorffMeasure2 3 (cylindricalCap r (-r) \ densityOne F) = 0 ∧
      hausdorffMeasure2 3 (cylindricalCap r r \ densityZero F) = 0 := by
  obtain ⟨hL, hU⟩ := h.compression_limit_cap_columns hσ hst hε hε1 hlim
  have hl := ae_eq_set_of_indicator_one_ae hL
  have hu := ae_eq_set_of_indicator_one_ae hU
  have hgapL : -r < c - η * r := by linarith [neg_abs_le c, h.1.2.2.2.1]
  have hgapU : c + η * r < r := by linarith [le_abs_self c, h.1.2.2.2.1]
  constructor
  · apply measure_mono_null _ h.2.1
    rintro x ⟨⟨p, hp, rfl⟩, hn⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    intro hd
    apply hn
    apply (densityOne_mem_iff_of_ae_on_open (isOpen_lowerPhaseColumn r (c - η * r)) _ hl).mpr hd
    exact ⟨by simpa only [graphProjectionN_append, mem_ball, dist_zero_right] using hp,
      by simpa only [graphAppendN_height_three] using hgapL⟩
  · apply measure_mono_null _ h.2.2
    rintro x ⟨⟨p, hp, rfl⟩, hn⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    intro hd
    apply hn
    apply (densityZero_mem_iff_of_ae_on_open (isOpen_upperPhaseColumn r (c + η * r)) _ hu).mpr hd
    exact ⟨by simpa only [graphProjectionN_append, mem_ball, dist_zero_right] using hp,
      by simpa only [graphAppendN_height_three] using hgapU⟩

theorem compression_limit_exterior {E F : Set AmbientSpace} {r σ τ c : ℝ}
    (hst : σ < τ) (hτr : τ ≤ r) {ε : ℕ → ℝ}
    (hlim : ∀ᵐ x : AmbientSpace ∂volume,
      Tendsto (fun j => (compressionCompetitor E r σ τ (ε j) c).indicator
        (fun _ => (1 : ℝ)) x) atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) x))) :
    F.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict (cylindricalCore r τ)ᶜ]
      E.indicator (fun _ => (1 : ℝ)) := by
  apply (ae_restrict_iff' (isOpen_cylindricalCore r τ).measurableSet.compl).mpr
  have hplane : ∀ᵐ x : AmbientSpace ∂volume, x 2 ≠ -r := by
    have hh := (measure_eq_zero_iff_ae_notMem).mp (volume_flatHyperplane 2 (-r))
    simpa only [mem_ofPred_eq, show (Fin.last 2 : Fin 3) = 2 from rfl] using hh
  filter_upwards [hlim, hplane] with x hx hxp
  intro hxout
  have he (j : ℕ) : (compressionCompetitor E r σ τ (ε j) c).indicator
      (fun _ => (1 : ℝ)) x = E.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hp : τ ≤ ‖graphProjectionN 2 x‖
    · exact compressionCompetitor_indicator_outside_base E r σ τ (ε j) c hst hp
    · apply compressionCompetitor_indicator_outside_height
      intro hstrip
      apply hxout
      have hplt := lt_of_not_ge hp
      exact ⟨hplt, hplt.trans_le hτr,
        abs_lt.mpr ⟨lt_of_le_of_ne hstrip.1 (Ne.symm hxp), hstrip.2⟩⟩
  exact tendsto_nhds_unique hx (tendsto_const_nhds.congr'
    (Eventually.of_forall fun j => (he j).symm))

theorem IsSlabCapConfiguration.compression_limit_annular_bound
    {E F : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η) (hmF : NullMeasurableSet F volume)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ ≤ r)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ x in K,
        |(compressionCompetitor E r σ τ (ε j) c).indicator (fun _ => (1 : ℝ)) x -
          F.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0)) :
    perimeterIn F (cylindricalTransition r σ τ) ≤
      perimeterIn E (cylindricalTransition r σ τ) +
        ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
          ∫⁻ x in standardCylinder r, ENNReal.ofReal ((x 2 - c) ^ 2)
            ∂canonicalPerimeterMeasure E hE hmE := by
  have hls := perimeterIn_le_liminf_of_locally_l1 (isOpen_cylindricalTransition r σ τ)
    (fun j => (compressionCompetitor_locallyFinitePerimeter hE hmE h.1.1.le
      hσ hst (hε j) (hε1 j) c).2) hmF (fun K hK _ => hconv K hK)
  apply hls.trans
  have hh := liminf_le_liminf (f := atTop) (Eventually.of_forall fun j =>
    h.compression_annular_perimeter_bound hσ hst hτr (hε j) (hε1 j))
  simpa only [liminf_const] using hh

end LiquidDrop
