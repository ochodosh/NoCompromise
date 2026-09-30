module

public import NoCompromise.Regularity.MonotonicityAnnulus
public import NoCompromise.Regularity.DensityAhlfors
public import NoCompromise.Regularity.RepresentativeBoundary
public import NoCompromise.DeGiorgi.NoAtoms
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-!
# Almost-monotonicity and positive density of quasiminimal boundaries

The constants in the blueprint's monotonicity formula are both exactly one.
The annular estimate is proved for every center and uses the actual reduced
boundary, outward normal, and normalized Hausdorff area. Positive limiting
density at boundary points follows from the proved quasiminimal density bound.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual tilt integrand is integrable on every positive annulus. -/
lemma IsOmegaMinimal.integrableOn_annular_tilt {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) {σ ρ : ℝ}
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    IntegrableOn (radialTiltDensity ω x (reducedNormal E hE.locallyFinite hE.nullMeasurable))
      ((ball x ρ \ ball x σ) ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable)
      (hausdorffMeasure2 3) := by
  let μ := (hausdorffMeasure2 3).restrict (reducedBoundary E hE.locallyFinite hE.nullMeasurable)
  have hp := reducedBoundary_outwardPerimeterPolar E hE.locallyFinite hE.nullMeasurable
  let : IsFiniteMeasureOnCompacts μ := hp.finiteOnCompacts
  have hi := integrableOn_radialTiltDensity μ hp.measurable hp.norm_ae hE.nonneg x
    (a := σ / 2) (b := ρ + 1) (by linarith) (by linarith)
  have hs : ball x ρ \ ball x σ ⊆ {y : AmbientSpace | ‖y - x‖ ∈ Ioo (σ / 2) (ρ + 1)} := by
    intro y hy
    have hyl : σ ≤ ‖y - x‖ := by simpa only [mem_ball, dist_eq_norm, not_lt] using hy.2
    have hyr : ‖y - x‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hy.1
    exact ⟨by linarith, by linarith⟩
  have h := hi.mono_set hs
  simpa only [IntegrableOn, μ, Measure.restrict_restrict (isOpen_ball.measurableSet.diff
    isOpen_ball.measurableSet)] using h

/-- The quantitative almost-monotonicity formula, with no exceptional radii. -/
theorem IsOmegaMinimal.annular_monotonicity {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) {σ ρ : ℝ}
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ : ρ < 1) :
    (∫ y in (ball x ρ \ ball x σ) ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable,
      radialTiltDensity ω x (reducedNormal E hE.locallyFinite hE.nullMeasurable) y
        ∂hausdorffMeasure2 3) ≤
      Real.exp (ω * ρ) * (perimeterIn E (ball x ρ)).toReal / ρ ^ 2 -
        Real.exp (ω * σ) * (perimeterIn E (ball x σ)).toReal / σ ^ 2 := by
  let μ := (hausdorffMeasure2 3).restrict (reducedBoundary E hE.locallyFinite hE.nullMeasurable)
  have hp := reducedBoundary_outwardPerimeterPolar E hE.locallyFinite hE.nullMeasurable
  let : IsFiniteMeasureOnCompacts μ := hp.finiteOnCompacts
  have h := annular_monotonicity_of_bounded_first_variation μ hp.measurable hp.norm_ae
    hE.nonneg x (hp.measure_singleton x)
    (fun X hX hcX hsX => hE.bounded_first_variation hX hcX hsX) hσ hσρ hρ
  have hm (r : ℝ) : μ.real (ball x r) = (perimeterIn E (ball x r)).toReal :=
    congrArg ENNReal.toReal (hp.open_eq (ball x r) isOpen_ball)
  rw [hm, hm] at h
  simpa only [μ, Measure.restrict_restrict (isOpen_ball.measurableSet.diff
    isOpen_ball.measurableSet)] using h

/-- The exponentially corrected area ratio is nondecreasing on the full
unit interval; the center need not lie on the boundary. -/
theorem IsOmegaMinimal.monotoneOn_area_ratio {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) :
    MonotoneOn (fun r : ℝ => Real.exp (ω * r) * (perimeterIn E (ball x r)).toReal / r ^ 2)
      (Ioo 0 1) := by
  intro σ hσ ρ hρ hσρ
  have h := hE.annular_monotonicity x hσ.1 hσρ hρ.2
  have hn : 0 ≤ ∫ y in (ball x ρ \ ball x σ) ∩
      reducedBoundary E hE.locallyFinite hE.nullMeasurable,
      radialTiltDensity ω x (reducedNormal E hE.locallyFinite hE.nullMeasurable) y
        ∂hausdorffMeasure2 3 := integral_nonneg (radialTiltDensity_nonneg _ _ _)
  linarith

/-- The unweighted perimeter density has a finite nonnegative limit at every center. -/
theorem IsOmegaMinimal.exists_perimeter_density {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) :
    ∃ θ : ℝ, 0 ≤ θ ∧ Tendsto (fun r : ℝ => (perimeterIn E (ball x r)).toReal / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 θ) := by
  let f := fun r : ℝ => Real.exp (ω * r) * (perimeterIn E (ball x r)).toReal / r ^ 2
  have hn (r : ℝ) : 0 ≤ f r := by dsimp [f]; positivity
  have hne : (Ioo (0 : ℝ) 1).Nonempty := ⟨1 / 2, by norm_num, by norm_num⟩
  have hb : BddBelow (f '' Ioo 0 1) := ⟨0, fun y hy => by
    obtain ⟨r, _, rfl⟩ := hy
    exact hn r⟩
  have ht := MonotoneOn.tendsto_nhdsWithin_Ioo_right hne (hE.monotoneOn_area_ratio x) hb
  have hθ : 0 ≤ sInf (f '' Ioo 0 1) := le_csInf (hne.image f) fun y hy => by
    obtain ⟨r, _, rfl⟩ := hy
    exact hn r
  refine ⟨sInf (f '' Ioo 0 1), hθ, ?_⟩
  have he : Tendsto (fun r : ℝ => Real.exp (ω * r)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun r : ℝ => Real.exp (ω * r)) 0 := by fun_prop
    simpa only [mul_zero, Real.exp_zero] using hc.mono_left nhdsWithin_le_nhds
  have h := ht.div he (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  convert h using 1
  ext r
  dsimp [f]
  field_simp [Real.exp_ne_zero]

/-- The genuine Ahlfors lower bound makes the limiting density strictly positive
at every point of the essential boundary. -/
theorem IsOmegaMinimal.exists_pos_perimeter_density {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {x : AmbientSpace} (hx : x ∈ essentialBoundary E) :
    ∃ θ : ℝ, 0 < θ ∧ Tendsto (fun r : ℝ => (perimeterIn E (ball x r)).toReal / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 θ) := by
  obtain ⟨θ, _, ht⟩ := hE.exists_perimeter_density x
  obtain ⟨c, hc, hlower⟩ := quasiminimal_perimeter_lower_bound ω hE.nonneg
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), c ≤ (perimeterIn E (ball x r)).toReal / r ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (hlower E hE x hx r hr.1 hr.2.le)
  have hcθ : c ≤ θ := ge_of_tendsto ht he
  exact ⟨θ, hc.trans_le hcθ, ht⟩

/-- Blueprint `thm:monotonicity`, with absolute constants `c = c₀ = 1` and
the unit scale supplied by quasiminimality. This includes the quantitative
annular formula and the finite positive density at the topological boundary
of the canonical open representative. -/
theorem quasiminimal_monotonicity :
    ∃ c c₀ : ℝ, 0 < c ∧ 0 < c₀ ∧
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
        (∀ x : AmbientSpace, MonotoneOn
          (fun r : ℝ => Real.exp (c * ω * r) * (perimeterIn E (ball x r)).toReal / r ^ 2)
          (Ioo 0 1)) ∧
        (∀ (x : AmbientSpace) (σ ρ : ℝ), 0 < σ → σ ≤ ρ → ρ < 1 →
          c₀ * (∫ y in (ball x ρ \ ball x σ) ∩
            reducedBoundary E hE.locallyFinite hE.nullMeasurable,
            Real.exp (c * ω * ‖y - x‖) *
              (inner ℝ (y - x) (reducedNormal E hE.locallyFinite hE.nullMeasurable y)) ^ 2 /
                ‖y - x‖ ^ 4 ∂hausdorffMeasure2 3) ≤
            Real.exp (c * ω * ρ) * (perimeterIn E (ball x ρ)).toReal / ρ ^ 2 -
              Real.exp (c * ω * σ) * (perimeterIn E (ball x σ)).toReal / σ ^ 2) ∧
        ∀ x ∈ frontier (densityOne E), ∃ θ : ℝ, 0 < θ ∧
          Tendsto (fun r : ℝ => (perimeterIn E (ball x r)).toReal / r ^ 2)
            (𝓝[>] (0 : ℝ)) (𝓝 θ) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro E ω hE
  simp only [one_mul]
  refine ⟨hE.monotoneOn_area_ratio, ?_, ?_⟩
  · intro x σ ρ hσ hσρ hρ
    exact hE.annular_monotonicity x hσ hσρ hρ
  · intro x hx
    exact hE.exists_pos_perimeter_density (by rwa [hE.frontier_densityOne] at hx)

end LiquidDrop
