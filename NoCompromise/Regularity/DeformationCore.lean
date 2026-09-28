import NoCompromise.Regularity.DeformationCompetitor
import NoCompromise.Regularity.DeformationPhases

/-! # The actual compressed competitors flatten in the core -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LiquidDrop

lemma compressionBeta_eq_epsilon {σ τ ε : ℝ} (hst : σ < τ)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : ‖p‖ ≤ σ) : compressionBeta σ τ ε p = ε := by
  have he : compressionProfile σ τ p = 0 := compressionRadialProfile_zero hst hp
  simp only [compressionBeta, he, mul_zero, add_zero]

lemma compressionCompetitor_indicator_between (E : Set AmbientSpace) (r σ τ ε c : ℝ)
    {x : AmbientSpace} (hx : -r ≤ x 2 ∧ x 2 < r) :
    (compressionCompetitor E r σ τ ε c).indicator (fun _ => (1 : ℝ)) x =
      (verticalCompression (compressionBeta σ τ ε) c '' verticalPhaseExtension E r).indicator
        (fun _ => (1 : ℝ)) x := by
  have he := replaceVerticalStrip_mem_between (E := E)
    (G := verticalCompression (compressionBeta σ τ ε) c '' verticalPhaseExtension E r) hx
  by_cases hh : x ∈ verticalCompression (compressionBeta σ τ ε) c '' verticalPhaseExtension E r
  · have hm : x ∈ compressionCompetitor E r σ τ ε c := he.mpr hh
    rw [indicator_of_mem hm, indicator_of_mem hh]
  · have hm : x ∉ compressionCompetitor E r σ τ ε c := mt he.mp hh
    rw [indicator_of_notMem hm, indicator_of_notMem hh]

/-- No regularity or convergence of vertical slices is assumed: the actual
phase bounds force almost-everywhere pointwise flattening in the core. -/
theorem IsSlabCapConfiguration.compression_core_ae_tendsto
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hsr : σ ≤ r)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ x : AmbientSpace ∂volume,
      ‖graphProjectionN 2 x‖ < σ → -r < x 2 → x 2 < r →
      Tendsto (fun j => (compressionCompetitor E r σ τ (ε j) c).indicator
        (fun _ => (1 : ℝ)) x) atTop
          (𝓝 ({y : AmbientSpace | y 2 < c}.indicator (fun _ => (1 : ℝ)) x)) := by
  have hall := ae_all_iff.mpr (fun j => h.compressed_extension_phases hσ hst (hε j) (hε1 j))
  have hplane : ∀ᵐ x : AmbientSpace ∂volume, x 2 ≠ c := by
    have hh := (measure_eq_zero_iff_ae_notMem).mp (volume_flatHyperplane 2 c)
    simpa only [mem_ofPred_eq, show (Fin.last 2 : Fin 3) = 2 from rfl] using hh
  have hδ : Tendsto (fun j => ε j * (η * r)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hεlim.mul_const (η * r)
  filter_upwards [hall, hplane] with x hx hxp
  intro hxs hxl hxu
  have hxr : ‖graphProjectionN 2 x‖ < r := hxs.trans_le hsr
  rcases lt_or_gt_of_ne hxp with hxc | hcx
  · rw [indicator_of_mem (show x ∈ {y : AmbientSpace | y 2 < c} from hxc)]
    apply tendsto_const_nhds.congr'
    filter_upwards [hδ.eventually (gt_mem_nhds (sub_pos.mpr hxc))] with j hj
    rw [compressionCompetitor_indicator_between E r σ τ (ε j) c ⟨hxl.le, hxu⟩]
    symm
    apply (hx j).1 hxr
    rw [compressionBeta_eq_epsilon hst hxs.le]
    linarith
  · rw [indicator_of_notMem (show x ∉ {y : AmbientSpace | y 2 < c} from hcx.not_gt)]
    apply tendsto_const_nhds.congr'
    filter_upwards [hδ.eventually (gt_mem_nhds (sub_pos.mpr hcx))] with j hj
    rw [compressionCompetitor_indicator_between E r σ τ (ε j) c ⟨hxl.le, hxu⟩]
    symm
    apply (hx j).2 hxr
    rw [compressionBeta_eq_epsilon hst hxs.le]
    linarith

end LiquidDrop
