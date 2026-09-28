import NoCompromise.Regularity.DensityAhlfors
import NoCompromise.DeGiorgi.Structure

/-!
# Density bounds and the closed essential boundary of a quasiminimizer

For each fixed positive radius the density ratio is continuous in its center.
Uniform two-sided bounds therefore persist on the closure of the essential
boundary, excluding both density-zero and density-one points there.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma volumeReal_ball_three (x : AmbientSpace) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball x r)).toReal = (4 * Real.pi / 3) * r ^ 3 := by
  simp only [EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

lemma densityRatio_eq_radialVolume_div (E : Set AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 ≤ r) :
    densityRatio E x r = radialVolume E x r / ((4 * Real.pi / 3) * r ^ 3) := by
  rw [densityRatio, volumeReal_ball_three x hr]
  rfl

lemma densityRatio_lower_of_radialVolume_lower {E : Set AmbientSpace}
    {x : AmbientSpace} {r c : ℝ} (hr : 0 < r)
    (hc : c * r ^ 3 ≤ radialVolume E x r) :
    c / (4 * Real.pi / 3) ≤ densityRatio E x r := by
  rw [densityRatio_eq_radialVolume_div E x hr.le]
  apply (le_div_iff₀ (by positivity : 0 < (4 * Real.pi / 3) * r ^ 3)).mpr
  have he : c / (4 * Real.pi / 3) * ((4 * Real.pi / 3) * r ^ 3) = c * r ^ 3 := by
    field_simp
  rwa [he]

lemma not_mem_densityZero_of_radial_lower {E : Set AmbientSpace} {x : AmbientSpace}
    {c : ℝ} (hc : 0 < c)
    (hl : ∀ᶠ r in 𝓝[>] (0 : ℝ), c * r ^ 3 ≤ radialVolume E x r) :
    x ∉ densityZero E := by
  intro hx
  have hb : ∀ᶠ r in 𝓝[>] (0 : ℝ), c / (4 * Real.pi / 3) ≤ densityRatio E x r := by
    filter_upwards [hl, self_mem_nhdsWithin] with r hr hr0
    exact densityRatio_lower_of_radialVolume_lower hr0 hr
  have h := ge_of_tendsto hx hb
  exact (not_le.mpr (by positivity : 0 < c / (4 * Real.pi / 3))) h

theorem reducedBoundary_subset_essentialBoundary {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    reducedBoundary E hE hmE ⊆ essentialBoundary E := by
  obtain ⟨c, hc, hlow⟩ := reduced_density_lower_bounds
  intro x hx
  obtain ⟨δ, hδ, hl⟩ := hlow E hE hmE x hx
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c * r ^ 3 ≤ radialVolume E x r ∧ c * r ^ 3 ≤ radialVolume Eᶜ x r := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds hδ)] with r hr0 hrd
    exact hl r hr0 hrd.le
  intro hz
  rcases hz with hz | ho
  · exact not_mem_densityZero_of_radial_lower hc (he.mono fun _ h => h.1) hz
  · have hz : x ∈ densityZero Eᶜ := by
      rw [← densityOne_compl hmE.compl, compl_compl]
      exact ho
    exact not_mem_densityZero_of_radial_lower hc (he.mono fun _ h => h.2) hz

theorem IsOmegaMinimal.densityRatio_bounds {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {x : AmbientSpace} (hx : x ∈ essentialBoundary E)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    quasiminimalDensityConstant ω / (4 * Real.pi / 3) ≤ densityRatio E x r ∧
      densityRatio E x r ≤ 1 - quasiminimalDensityConstant ω / (4 * Real.pi / 3) := by
  have hl := densityRatio_lower_of_radialVolume_lower hr (hE.radialVolume_lower_bound hx hr.le hr1)
  have hxc : x ∈ essentialBoundary Eᶜ := by rwa [essentialBoundary_compl hE.nullMeasurable]
  have hr' := densityRatio_lower_of_radialVolume_lower hr
    (hE.compl.radialVolume_lower_bound hxc hr.le hr1)
  rw [densityRatio_compl hE.nullMeasurable x hr] at hr'
  exact ⟨hl, by linarith⟩

theorem IsOmegaMinimal.isClosed_essentialBoundary {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) : IsClosed (essentialBoundary E) := by
  apply isClosed_of_closure_subset
  intro x hx
  let c := quasiminimalDensityConstant ω / (4 * Real.pi / 3)
  have hc : 0 < c := div_pos (quasiminimalDensityConstant_pos hE.nonneg) (by positivity)
  have hb (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
      c ≤ densityRatio E x r ∧ densityRatio E x r ≤ 1 - c := by
    have hcont := continuous_densityRatio hE.nullMeasurable r
    exact ⟨closure_minimal (fun _ hz => (hE.densityRatio_bounds hz hr hr1).1)
      (isClosed_le continuous_const hcont) hx,
      closure_minimal (fun _ hz => (hE.densityRatio_bounds hz hr hr1).2)
        (isClosed_le hcont continuous_const) hx⟩
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c ≤ densityRatio E x r ∧ densityRatio E x r ≤ 1 - c := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1))] with r hr hr1
    exact hb r hr hr1.le
  intro hz
  rcases hz with hz | ho
  · exact (not_le.mpr hc) (ge_of_tendsto hz (he.mono fun _ h => h.1))
  · have h := le_of_tendsto ho (he.mono fun _ h => h.2)
    linarith

end LiquidDrop
