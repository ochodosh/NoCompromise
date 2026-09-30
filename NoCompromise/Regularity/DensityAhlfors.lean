module

public import NoCompromise.Regularity.DensityEstimates

@[expose] public section

/-!
# Two-sided perimeter density for quasiminimizers

The lower estimate uses the actual relative isoperimetric inequality and the
proved phase densities. The upper estimate uses the actual good-radius cut
comparison, the area of a sphere, and monotonicity of the perimeter measure.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The upper quadratic perimeter bound needs no boundary-point hypothesis. -/
theorem IsOmegaMinimal.perimeterIn_ball_upper {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2) :
    (perimeterIn E (ball x r)).toReal ≤
      (4 * (4 * Real.pi + ω * (4 * Real.pi / 3))) * r ^ 2 := by
  let μ := canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable
  let : IsFiniteMeasureOnCompacts μ :=
    (canonicalPerimeterPolar E hE.locallyFinite hE.nullMeasurable).finiteOnCompacts
  have hC : 0 ≤ 4 * Real.pi + ω * (4 * Real.pi / 3) :=
    add_nonneg (by positivity) (mul_nonneg hE.nonneg (by positivity))
  have hbound : ∀ᵐ s : ℝ, 0 < s → s ≤ 1 →
      μ.real (ball x s) ≤ (4 * Real.pi + ω * (4 * Real.pi / 3)) * s ^ 2 := by
    filter_upwards [hE.ae_cut_comparison x, ae_deriv_radialVolume hE.nullMeasurable x]
      with s hc hd hs hs1
    have hcut := hc hs hs1
    have hD : deriv (radialVolume E x) s ≤ 4 * Real.pi * s ^ 2 := by
      rw [hd hs]
      exact radialSectionArea_le E x s
    have hvol : radialVolume E x s ≤ (4 * Real.pi / 3) * s ^ 3 := by
      have hsum := radialVolume_add_compl hE.nullMeasurable x hs.le
      have hn := radialVolume_nonneg Eᶜ x s
      linarith
    have hcube : s ^ 3 ≤ s ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hs1 (sq_nonneg s)
      nlinarith only [h]
    have hv : radialVolume E x s ≤ (4 * Real.pi / 3) * s ^ 2 :=
      hvol.trans (mul_le_mul_of_nonneg_left hcube (by positivity))
    have hw := mul_le_mul_of_nonneg_left hv hE.nonneg
    change (canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable).real (ball x s) ≤ _
    rw [measureReal_def,
      canonicalPerimeterMeasure_open E hE.locallyFinite hE.nullMeasurable isOpen_ball]
    nlinarith only [hcut, hD, hw]
  have h := measure_ball_quadratic_bound_of_ae μ x hC hbound hr hr1
  simpa only [μ, measureReal_def,
    canonicalPerimeterMeasure_open E hE.locallyFinite hE.nullMeasurable isOpen_ball] using h

/-- A positive lower perimeter coefficient is uniform over all sets with the same `ω`. -/
theorem quasiminimal_perimeter_lower_bound (ω : ℝ) (hω : 0 ≤ ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Set AmbientSpace), IsOmegaMinimal E ω →
      ∀ x ∈ essentialBoundary E, ∀ r : ℝ, 0 < r → r ≤ 1 →
        c * r ^ 2 ≤ (perimeterIn E (ball x r)).toReal := by
  obtain ⟨C, hC, hI⟩ := relative_isoperimetric_ball_three_real
  let d := quasiminimalDensityConstant ω
  have hd : 0 < d := quasiminimalDensityConstant_pos hω
  refine ⟨d ^ (2 / 3 : ℝ) / C, div_pos (Real.rpow_pos_of_pos hd _) hC, ?_⟩
  intro E hE x hx r hr hr1
  have hxc : x ∈ essentialBoundary Eᶜ := by rwa [essentialBoundary_compl hE.nullMeasurable]
  have hleft := hE.radialVolume_lower_bound hx hr.le hr1
  have hright := hE.compl.radialVolume_lower_bound hxc hr.le hr1
  have hmin : d * r ^ 3 ≤ min (radialVolume E x r) (radialVolume Eᶜ x r) :=
    le_min hleft hright
  have hi := hI E hE.locallyFinite hE.nullMeasurable x r hr
  have hset : ball x r \ E = Eᶜ ∩ ball x r := by
    ext y
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, and_comm]
  rw [hset, measureReal_def,
    canonicalPerimeterMeasure_open E hE.locallyFinite hE.nullMeasurable isOpen_ball] at hi
  change (min (radialVolume E x r) (radialVolume Eᶜ x r)) ^ (2 / 3 : ℝ) ≤
    C * (perimeterIn E (ball x r)).toReal at hi
  have hpowr : (r ^ 3) ^ (2 / 3 : ℝ) = r ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  have hp : d ^ (2 / 3 : ℝ) * r ^ 2 ≤ C * (perimeterIn E (ball x r)).toReal := by
    have h := (Real.rpow_le_rpow (mul_nonneg hd.le (pow_nonneg hr.le _)) hmin
      (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans hi
    rwa [Real.mul_rpow hd.le (pow_nonneg hr.le _), hpowr] at h
  have hdiv : (d ^ (2 / 3 : ℝ) * r ^ 2) / C ≤ (perimeterIn E (ball x r)).toReal :=
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hp)
  convert hdiv using 1
  ring

/-- Blueprint `lem:ahlfors`: genuine two-sided perimeter density, with constants
chosen from the quasiminimality coefficient alone. -/
theorem quasiminimal_ahlfors_bounds (ω : ℝ) (hω : 0 ≤ ω) :
    ∃ r_d c_P C_P : ℝ, 0 < r_d ∧ r_d ≤ 1 ∧ 0 < c_P ∧ c_P < C_P ∧
      ∀ (E : Set AmbientSpace), IsOmegaMinimal E ω → ∀ x ∈ essentialBoundary E,
        ∀ r : ℝ, 0 < r → r < r_d / 2 →
          c_P * r ^ 2 ≤ (perimeterIn E (ball x r)).toReal ∧
          (perimeterIn E (ball x r)).toReal ≤ C_P * r ^ 2 := by
  obtain ⟨c, hc, hlower⟩ := quasiminimal_perimeter_lower_bound ω hω
  let C := 4 * (4 * Real.pi + ω * (4 * Real.pi / 3)) + c + 1
  have hC : c < C := by
    have hnonneg : 0 ≤ 4 * (4 * Real.pi + ω * (4 * Real.pi / 3)) := by positivity
    dsimp [C]
    linarith
  refine ⟨1, c, C, by norm_num, le_rfl, hc, hC, ?_⟩
  intro E hE x hx r hr hr1
  refine ⟨hlower E hE x hx r hr (by linarith), ?_⟩
  apply (hE.perimeterIn_ball_upper x hr hr1.le).trans
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg r)

end LiquidDrop
