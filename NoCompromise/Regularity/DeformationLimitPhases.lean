import NoCompromise.Regularity.DeformationClearance

/-! # Phase constraints retained by genuine almost-everywhere limits -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LiquidDrop

lemma compressionBeta_tendsto {σ τ : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (p : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun j => compressionBeta σ τ (ε j) p) atTop (𝓝 (compressionProfile σ τ p)) := by
  simpa only [compressionBeta, zero_add, sub_zero, one_mul] using
    hε.add (((tendsto_const_nhds (x := (1 : ℝ))).sub hε).mul_const (compressionProfile σ τ p))

theorem IsSlabCapConfiguration.compression_limit_phases
    {E F : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hlim : ∀ᵐ x : AmbientSpace ∂volume,
      Tendsto (fun j => (compressionCompetitor E r σ τ (ε j) c).indicator
        (fun _ => (1 : ℝ)) x) atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) x))) :
    ∀ᵐ x : AmbientSpace ∂volume, x ∈ standardCylinder r →
      (x 2 < c - compressionProfile σ τ (graphProjectionN 2 x) * (η * r) →
        F.indicator (fun _ => (1 : ℝ)) x = 1) ∧
      (c + compressionProfile σ τ (graphProjectionN 2 x) * (η * r) < x 2 →
        F.indicator (fun _ => (1 : ℝ)) x = 0) := by
  have hall := ae_all_iff.mpr (fun j => h.compressed_extension_phases hσ hst (hε j) (hε1 j))
  filter_upwards [hall, hlim] with x hx hxl
  intro hxC
  have hstrip : -r ≤ x 2 ∧ x 2 < r :=
    ⟨(abs_lt.mp hxC.2).1.le, (abs_lt.mp hxC.2).2⟩
  have hb := (compressionBeta_tendsto (σ := σ) (τ := τ) hεlim
    (graphProjectionN 2 x)).mul_const (η * r)
  constructor
  · intro hy
    have he : ∀ᶠ j in atTop,
        (compressionCompetitor E r σ τ (ε j) c).indicator (fun _ => (1 : ℝ)) x = 1 := by
      filter_upwards [hb.eventually (gt_mem_nhds
        (show compressionProfile σ τ (graphProjectionN 2 x) * (η * r) < c - x 2 by linarith))]
        with j hj
      rw [compressionCompetitor_indicator_between E r σ τ (ε j) c hstrip]
      exact (hx j).1 hxC.1 (by linarith)
    exact tendsto_nhds_unique hxl (tendsto_const_nhds.congr' (he.mono fun _ hj => hj.symm))
  · intro hy
    have he : ∀ᶠ j in atTop,
        (compressionCompetitor E r σ τ (ε j) c).indicator (fun _ => (1 : ℝ)) x = 0 := by
      filter_upwards [hb.eventually (gt_mem_nhds
        (show compressionProfile σ τ (graphProjectionN 2 x) * (η * r) < x 2 - c by linarith))]
        with j hj
      rw [compressionCompetitor_indicator_between E r σ τ (ε j) c hstrip]
      exact (hx j).2 hxC.1 (by linarith)
    exact tendsto_nhds_unique hxl (tendsto_const_nhds.congr' (he.mono fun _ hj => hj.symm))

lemma ae_limit_eq_of_agreement_on_open
    {f : ℕ → AmbientSpace → ℝ} {g k : AmbientSpace → ℝ} {U : Set AmbientSpace}
    (hU : IsOpen U) (he : ∀ j, f j =ᵐ[volume.restrict U] k)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    g =ᵐ[volume.restrict U] k := by
  apply (ae_restrict_iff' hU.measurableSet).mpr
  have hall := ae_all_iff.mpr (fun j => (ae_restrict_iff' hU.measurableSet).mp (he j))
  filter_upwards [hall, hlim] with x hx hxl
  intro hxU
  exact tendsto_nhds_unique hxl (tendsto_const_nhds.congr'
    (Eventually.of_forall (fun j => (hx j hxU).symm)))

theorem IsSlabCapConfiguration.compression_limit_cap_columns
    {E F : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hlim : ∀ᵐ x : AmbientSpace ∂volume,
      Tendsto (fun j => (compressionCompetitor E r σ τ (ε j) c).indicator
        (fun _ => (1 : ℝ)) x) atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) x))) :
    (F.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict (lowerPhaseColumn r (c - η * r))]
      E.indicator (fun _ => (1 : ℝ))) ∧
    (F.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict (upperPhaseColumn r (c + η * r))]
      E.indicator (fun _ => (1 : ℝ))) := by
  exact ⟨ae_limit_eq_of_agreement_on_open (isOpen_lowerPhaseColumn _ _)
    (fun j => (h.compression_agrees_on_cap_columns hσ hst (hε j) (hε1 j)).1) hlim,
    ae_limit_eq_of_agreement_on_open (isOpen_upperPhaseColumn _ _)
    (fun j => (h.compression_agrees_on_cap_columns hσ hst (hε j) (hε1 j)).2) hlim⟩

end LiquidDrop
