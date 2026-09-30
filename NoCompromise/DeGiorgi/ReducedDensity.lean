module

public import NoCompromise.DeGiorgi.Reduced
public import NoCompromise.DeGiorgi.DensityFlux
public import NoCompromise.DeGiorgi.DensityODE
public import NoCompromise.BV.Algebra
public import NoCompromise.BV.RadialVolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-!
# Two-sided volume density at a reduced point

Every ball centered in the support of perimeter contains positive volume of the
set and of its complement. At reduced points the radial flux and relative
isoperimetric inequalities give uniform cubic lower bounds and positive lower
limits for both volume ratios.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma perimeterIn_eq_zero_of_volume_inter_eq_zero {n : ℕ}
    {E U : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (hzero : volume (E ∩ U) = 0) : perimeterIn E U = 0 := by
  have hm : (volume.restrict U) E = 0 := by
    rw [Measure.restrict_apply₀ (hE.mono Measure.restrict_le_self)]
    exact hzero
  have heq : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hm] with x hx
    exact indicator_of_notMem hx _
  rw [perimeterIn, variation_congr_ae U heq, variation_zero]

lemma volume_inter_pos_of_perimeterIn_pos {n : ℕ}
    {E U : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (hpos : 0 < perimeterIn E U) : 0 < volume (E ∩ U) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hp := perimeterIn_eq_zero_of_volume_inter_eq_zero hE hz
  exact hpos.ne' hp

/-- Both phases occur with positive volume in every ball about a perimeter-support point. -/
theorem volume_sides_pos_of_mem_perimeter_support (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ (canonicalPerimeterMeasure E hE hmE).support)
    {r : ℝ} (hr : 0 < r) :
    0 < volume (E ∩ ball x r) ∧ 0 < volume (ball x r \ E) := by
  have hμ : 0 < canonicalPerimeterMeasure E hE hmE (ball x r) :=
    ((canonicalPerimeterMeasure E hE hmE).mem_support_iff_forall x).mp hx
      (ball x r) (ball_mem_nhds x hr)
  rw [canonicalPerimeterMeasure_open E hE hmE isOpen_ball] at hμ
  refine ⟨volume_inter_pos_of_perimeterIn_pos hmE hμ, ?_⟩
  have hc : 0 < perimeterIn Eᶜ (ball x r) := by rw [perimeterIn_compl hmE isOpen_ball]; exact hμ
  have hv := volume_inter_pos_of_perimeterIn_pos hmE.compl hc
  simpa only [sdiff_eq_compl_inter] using hv

/-- The qualitative positive-volume prerequisite of the reduced-point density estimate. -/
theorem volume_sides_pos_at_reduced (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE) {r : ℝ} (hr : 0 < r) :
    0 < volume (E ∩ ball x r) ∧ 0 < volume (ball x r \ E) :=
  volume_sides_pos_of_mem_perimeter_support E hE hmE hx.1 hr

lemma radialVolume_le (E : Set AmbientSpace) (x : AmbientSpace) {r : ℝ}
    (hr : 0 ≤ r) : radialVolume E x r ≤ (Real.pi * 4 / 3) * r ^ 3 := by
  have hm : volume (ball x r) ≠ ∞ := measure_ball_lt_top.ne
  have h := ENNReal.toReal_mono hm
    (measure_mono (inter_subset_right : E ∩ ball x r ⊆ ball x r))
  simpa only [radialVolume, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3), mul_comm] using h

lemma radialVolume_pos_at_reduced (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE) {r : ℝ} (hr : 0 < r) :
    0 < radialVolume E x r ∧ 0 < radialVolume Eᶜ x r := by
  have hp := volume_sides_pos_at_reduced E hE hmE hx hr
  have hfin : volume (E ∩ ball x r) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hfin' : volume (Eᶜ ∩ ball x r) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  refine ⟨ENNReal.toReal_pos hp.1.ne' hfin, ENNReal.toReal_pos ?_ hfin'⟩
  simpa only [sdiff_eq_compl_inter] using hp.2.ne'

lemma le_liminf_radialVolume_ratio (E : Set AmbientSpace) (x : AmbientSpace) {κ : ℝ}
    (hκ : ∀ᶠ r in 𝓝[>] (0 : ℝ), κ * r ^ 3 ≤ radialVolume E x r) :
    κ ≤ liminf (fun r => radialVolume E x r / r ^ 3) (𝓝[>] (0 : ℝ)) := by
  have hb : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      (fun r => radialVolume E x r / r ^ 3) := by
    refine ⟨Real.pi * 4 / 3, ?_⟩
    change ∀ᶠ r in 𝓝[>] (0 : ℝ), radialVolume E x r / r ^ 3 ≤ Real.pi * 4 / 3
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (div_le_iff₀ (pow_pos hr 3)).mpr (radialVolume_le E x hr.le)
  apply le_liminf_of_le hb.isCoboundedUnder_ge
  filter_upwards [hκ, self_mem_nhdsWithin] with r hkr hr
  exact (le_div_iff₀ (pow_pos hr 3)).mpr hkr

/-- A universal positive density constant works at every reduced point, with a
point-dependent radius. Both phases satisfy the bound at every smaller radius. -/
theorem reduced_density_lower_bounds :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
      (hmE : NullMeasurableSet E volume) (x : AmbientSpace), x ∈ reducedBoundary E hE hmE →
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r ≤ δ →
        κ * r ^ 3 ≤ radialVolume E x r ∧ κ * r ^ 3 ≤ radialVolume Eᶜ x r := by
  obtain ⟨b, hb, c, hc, hdiff⟩ := exists_density_differential_inequalities
  refine ⟨densityCubicConstant b c, densityCubicConstant_pos hb hc,
    fun E hE hmE x hx => ?_⟩
  obtain ⟨δ, hδ, hd⟩ := hdiff E hE hmE x hx
  have hleft : ∀ᵐ r : ℝ, r ∈ Ioo 0 δ → radialVolume E x r ≤ b * r ^ 3 →
      c * radialVolume E x r ^ (2 / 3 : ℝ) ≤ deriv (radialVolume E x) r := by
    filter_upwards [hd] with r hr
    exact fun hrs => (hr hrs.1 hrs.2.le).1
  have hright : ∀ᵐ r : ℝ, r ∈ Ioo 0 δ → radialVolume Eᶜ x r ≤ b * r ^ 3 →
      c * radialVolume Eᶜ x r ^ (2 / 3 : ℝ) ≤ deriv (radialVolume Eᶜ x) r := by
    filter_upwards [hd] with r hr
    exact fun hrs => (hr hrs.1 hrs.2.le).2
  have hl := cubic_lower_barrier_of_lipschitz hb hc (lipschitzOnWith_radialVolume hmE x δ)
    (radialVolume_zero E x)
    (fun r hr _ => (radialVolume_pos_at_reduced E hE hmE hx hr).1) hleft
  have hr := cubic_lower_barrier_of_lipschitz hb hc
    (lipschitzOnWith_radialVolume hmE.compl x δ) (radialVolume_zero Eᶜ x)
    (fun r hr _ => (radialVolume_pos_at_reduced E hE hmE hx hr).2) hright
  exact ⟨δ, hδ, fun r hrpos hrd => ⟨hl r ⟨hrpos.le, hrd⟩, hr r ⟨hrpos.le, hrd⟩⟩⟩

/-- Blueprint `lem:reduced-density`: both lower volume ratios are strictly positive. -/
theorem reduced_density (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE) :
    0 < liminf (fun r => (volume (E ∩ ball x r)).toReal / r ^ 3) (𝓝[>] (0 : ℝ)) ∧
    0 < liminf (fun r => (volume (ball x r \ E)).toReal / r ^ 3) (𝓝[>] (0 : ℝ)) := by
  obtain ⟨κ, hκ, hb⟩ := reduced_density_lower_bounds
  obtain ⟨δ, hδ, hb⟩ := hb E hE hmE x hx
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      κ * r ^ 3 ≤ radialVolume E x r ∧ κ * r ^ 3 ≤ radialVolume Eᶜ x r := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with r hrd hr
    exact hb r hr hrd.le
  refine ⟨hκ.trans_le (le_liminf_radialVolume_ratio E x (he.mono fun _ h => h.1)), ?_⟩
  simpa only [radialVolume, sdiff_eq_compl_inter] using
    hκ.trans_le (le_liminf_radialVolume_ratio Eᶜ x (he.mono fun _ h => h.2))

end LiquidDrop
