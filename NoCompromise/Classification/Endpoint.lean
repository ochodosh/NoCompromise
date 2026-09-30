module

public import NoCompromise.Classification.Subcritical
public import NoCompromise.Existence.Subcritical
public import NoCompromise.Value.Continuity
public import NoCompromise.Ball.Potential
public import NoCompromise.Energy.NullInvariance
public import NoCompromise.Energy.Scaling
public import NoCompromise.Threshold.Algebra

@[expose] public section

/-!
# Existence and uniqueness at the endpoint

Blueprint Chapter 35 (`ch:endpoint`), `prop:endpoint`.

In `endpoint_of_classification` the classification `prop:classification` (Chapter 34) enters
as the explicit hypothesis `hclass`; `endpoint` supplies it from `classification`, so that it
depends only on `SharpIsoperimetric`, `CapEstimateStatement` and
`IsoperimetricRigidityStatement`. Throughout, the sharp isoperimetric inequality enters as the
named predicate `SharpIsoperimetric` (`Value/Defs.lean`), which is the only input of
`prop:existence-subcritical` (`exists_minimizer_subcritical_of_sharp_isoperimetric`).
Following `rem:endpoint-route`, existence at `V_*` is obtained from `m(V) = 𝓔(B_V)` for
`0 < V < V_*` and continuity of `m` (`prop:m-continuous`, `valueFunction_continuousOn`) and of
the ball-energy formula `eq:ball-energy`, not from closedness of the set of volumes admitting
minimisers.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal symmDiff

namespace LiquidDrop

/-- A ball of volume `V > 0` has the radius `ballRadius V` prescribed in `not:BV`. -/
theorem radius_eq_ballRadius_of_volume {V : ℝ} (hV : 0 < V) {c : AmbientSpace} {r : ℝ}
    (hr : 0 < r) (hvol : volume (ball c r) = ENNReal.ofReal V) : r = ballRadius V := by
  have h1 : 4 * Real.pi * r ^ 3 / 3 = V := by
    rw [volume_ball_eq_ofReal c hr.le] at hvol
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) hV.le).mp hvol
  have hpi : (4 * Real.pi) ≠ 0 := by positivity
  have h2 : r ^ 3 = ballRadius V ^ 3 := by
    rw [ballRadius_cube hV, eq_div_iff hpi]
    linear_combination 3 * h1
  exact (pow_left_inj₀ hr.le (ballRadius_pos hV).le (by norm_num : (3 : ℕ) ≠ 0)).mp h2

/-- A set agreeing a.e. with a ball of volume `V` has volume `V`. -/
theorem IsLebesgueBallUpToNull.volume_eq {V : ℝ} {Ω : Set AmbientSpace}
    (h : IsLebesgueBallUpToNull V Ω) : volume Ω = ENNReal.ofReal V := by
  obtain ⟨-, c, r, -, hvol, hsd⟩ := h
  rw [measure_congr (measure_symmDiff_eq_zero_iff.mp hsd), hvol]

/-- A set agreeing a.e. with a ball of positive radius has finite perimeter. -/
theorem IsLebesgueBallUpToNull.perimeter_lt_top {V : ℝ} {Ω : Set AmbientSpace}
    (h : IsLebesgueBallUpToNull V Ω) : perimeter Ω < ∞ := by
  obtain ⟨-, c, r, hr, -, hsd⟩ := h
  rw [perimeter_congr_ae (measure_symmDiff_eq_zero_iff.mp hsd), perimeter_ball c hr]
  exact ENNReal.ofReal_lt_top

/-- A set agreeing a.e. with a translate of `B_V` has the energy `𝓔(B_V)` of
`cor:ball-energy` (`lem:null-invariance` and translation invariance). -/
theorem IsLebesgueBallUpToNull.energy_eq {V : ℝ} (hV : 0 < V) {Ω : Set AmbientSpace}
    (h : IsLebesgueBallUpToNull V Ω) : energy Ω = energy (ballByVolume V) := by
  obtain ⟨-, c, r, hr, hvol, hsd⟩ := h
  have hrV := radius_eq_ballRadius_of_volume hV hr hvol
  subst hrV
  rw [energy_congr_ae (measure_symmDiff_eq_zero_iff.mp hsd), ← image_add_ball_zero c,
    energy_translate measurableSet_ball.nullMeasurableSet]
  rfl

/-- If `m(V) = 𝓔(B_V)`, every set agreeing a.e. with a translate of `B_V` is a minimiser
(the converse direction in the proof of `thm:main`). -/
theorem isLebesgueFixedVolumeMinimizer_of_ballUpToNull {V : ℝ} (hV : 0 < V)
    (hm : valueFunction V = energy (ballByVolume V)) {Ω : Set AmbientSpace}
    (hΩ : IsLebesgueBallUpToNull V Ω) : IsLebesgueFixedVolumeMinimizer V Ω := by
  refine ⟨hΩ.1, hΩ.volume_eq, hΩ.perimeter_lt_top, fun F hF hvol => ?_⟩
  rw [hΩ.energy_eq hV, ← hm]
  exact valueFunction_le hF hvol

/-- The Borel form of `isLebesgueFixedVolumeMinimizer_of_ballUpToNull`. -/
theorem isFixedVolumeMinimizer_of_ballUpToNull {V : ℝ} (hV : 0 < V)
    (hm : valueFunction V = energy (ballByVolume V)) {Ω : Set AmbientSpace}
    (hΩ : IsBallUpToNull V Ω) : IsFixedVolumeMinimizer V Ω :=
  (isFixedVolumeMinimizer_iff_lebesgue V Ω hΩ.1).mpr
    (isLebesgueFixedVolumeMinimizer_of_ballUpToNull hV hm hΩ.toLebesgue)

/-- The first step of the proof of `prop:endpoint`: for `0 < V < V_*`,
`prop:existence-subcritical` and `prop:classification` give `m(V) = 𝓔(B_V)`. -/
theorem valueFunction_eq_ball_of_classification (hiso : SharpIsoperimetric)
    (hclass : ∀ V : ℝ, 0 < V → V ≤ criticalVolume → ∀ Ω : Set AmbientSpace,
      IsLebesgueFixedVolumeMinimizer V Ω → IsLebesgueBallUpToNull V Ω)
    {V : ℝ} (hV : 0 < V) (hVc : V < criticalVolume) :
    valueFunction V = energy (ballByVolume V) := by
  obtain ⟨Ω, -, hΩ, hE⟩ := exists_minimizer_subcritical_of_sharp_isoperimetric hiso hV hVc
  rw [← hE]
  exact (hclass V hV hVc.le Ω hΩ).energy_eq hV

/-- Continuity on `(0, ∞)` of the ball-energy formula `eq:ball-energy`,
`𝓔(B_V) = (V + 5)/5 · (36π)^{1/3} V^{2/3}`. -/
theorem energy_ballByVolume_toReal_continuousOn :
    ContinuousOn (fun V : ℝ => (energy (ballByVolume V)).toReal) (Ioi 0) := by
  have h : ContinuousOn
      (fun V : ℝ => (V + 5) / 5 * ((36 * Real.pi) ^ (1 / (3 : ℝ)) * V ^ (2 / (3 : ℝ))))
      (Ioi 0) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.mul continuousOn_const ?_)
    exact fun V hV =>
      (Real.continuousAt_rpow_const V _ (Or.inl (ne_of_gt hV))).continuousWithinAt
  refine h.congr fun V hV => ?_
  show (energy (ballByVolume V)).toReal = _
  rw [energy_ballByVolume_toReal hV, ballPerimeter_toReal_eq_rpow hV]

/-- Blueprint `prop:endpoint`: `m(V_*) = 𝓔(B_{V_*})`, the ball `B_{V_*}` is a fixed-volume
minimiser at volume `V_*` (in both measurability conventions), and it is the unique one up to
translation and null sets.  The classification `prop:classification` is the hypothesis
`hclass`; `prop:existence-subcritical` is used through `SharpIsoperimetric`. -/
theorem endpoint_of_classification (hiso : SharpIsoperimetric)
    (hclass : ∀ V : ℝ, 0 < V → V ≤ criticalVolume → ∀ Ω : Set AmbientSpace,
      IsLebesgueFixedVolumeMinimizer V Ω → IsLebesgueBallUpToNull V Ω) :
    valueFunction criticalVolume = energy (ballByVolume criticalVolume) ∧
      IsFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      IsLebesgueFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      ∀ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer criticalVolume Ω →
        IsLebesgueBallUpToNull criticalVolume Ω := by
  have hVc : 0 < criticalVolume := criticalVolume_pos
  have heq : EqOn (fun V => (valueFunction V).toReal)
      (fun V => (energy (ballByVolume V)).toReal) (Ioo 0 criticalVolume) := fun V hV => by
    show (valueFunction V).toReal = (energy (ballByVolume V)).toReal
    rw [valueFunction_eq_ball_of_classification hiso hclass hV.1 hV.2]
  have hsub : Ioc 0 criticalVolume ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hext := heq.of_subset_closure (valueFunction_continuousOn.mono hsub)
    (energy_ballByVolume_toReal_continuousOn.mono hsub) Ioo_subset_Ioc_self
    (by rw [closure_Ioo hVc.ne]; exact Ioc_subset_Icc_self)
  have h1 : (valueFunction criticalVolume).toReal =
      (energy (ballByVolume criticalVolume)).toReal := hext (right_mem_Ioc.mpr hVc)
  have hballtop : energy (ballByVolume criticalVolume) ≠ ∞ := by
    rw [energy_ballByVolume hVc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ballPerimeter_lt_top hVc).ne
  have hm : valueFunction criticalVolume = energy (ballByVolume criticalVolume) :=
    (ENNReal.toReal_eq_toReal_iff' (valueFunction_lt_top hVc).ne hballtop).mp h1
  have hball : IsBallUpToNull criticalVolume (ballByVolume criticalVolume) :=
    ⟨measurableSet_ball, 0, ballRadius criticalVolume, ballRadius_pos hVc,
      volume_ballByVolume hVc, by rw [ballByVolume, symmDiff_self, Set.bot_eq_empty,
        measure_empty]⟩
  exact ⟨hm, isFixedVolumeMinimizer_of_ballUpToNull hVc hm hball,
    isLebesgueFixedVolumeMinimizer_of_ballUpToNull hVc hm hball.toLebesgue,
    fun Ω hΩ => hclass _ hVc le_rfl Ω hΩ⟩

/-- Blueprint `prop:endpoint`, with `prop:classification` supplied by `classification`
(Classification/Subcritical.lean): modulo `SharpIsoperimetric` (`thm:sharp-isoperimetric`),
`CapEstimateStatement` (`prop:cap-estimate`) and `IsoperimetricRigidityStatement`
(`thm:isoperimetric-rigidity`). -/
theorem endpoint (hiso : SharpIsoperimetric) (hcap : CapEstimateStatement)
    (hrig : IsoperimetricRigidityStatement) :
    valueFunction criticalVolume = energy (ballByVolume criticalVolume) ∧
      IsFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      IsLebesgueFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      ∀ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer criticalVolume Ω →
        IsLebesgueBallUpToNull criticalVolume Ω :=
  endpoint_of_classification hiso fun _ hV hVc _ hΩ => classification hiso hcap hrig hV hVc hΩ

/-- Blueprint `prop:endpoint` modulo `ABPNeumannSolvable` (`lem:abp-neumann`),
`IsoperimetricEqualityRegularity` (Steps 1–2 of `thm:isoperimetric-rigidity`) and
`CapEstimateStatement` (`prop:cap-estimate`). -/
theorem endpoint_of_abpNeumann (hN : ABPNeumannSolvable) (hR : IsoperimetricEqualityRegularity)
    (hcap : CapEstimateStatement) :
    valueFunction criticalVolume = energy (ballByVolume criticalVolume) ∧
      IsFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      IsLebesgueFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      ∀ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer criticalVolume Ω →
        IsLebesgueBallUpToNull criticalVolume Ω :=
  endpoint (sharpIsoperimetric_of_abpNeumann hN) hcap
    (isoperimetricRigidityStatement_of_abpNeumann hN hR)

end LiquidDrop

#print axioms LiquidDrop.endpoint
#print axioms LiquidDrop.endpoint_of_abpNeumann
#print axioms LiquidDrop.radius_eq_ballRadius_of_volume
#print axioms LiquidDrop.IsLebesgueBallUpToNull.volume_eq
#print axioms LiquidDrop.IsLebesgueBallUpToNull.perimeter_lt_top
#print axioms LiquidDrop.IsLebesgueBallUpToNull.energy_eq
#print axioms LiquidDrop.isLebesgueFixedVolumeMinimizer_of_ballUpToNull
#print axioms LiquidDrop.isFixedVolumeMinimizer_of_ballUpToNull
#print axioms LiquidDrop.valueFunction_eq_ball_of_classification
#print axioms LiquidDrop.energy_ballByVolume_toReal_continuousOn
#print axioms LiquidDrop.endpoint_of_classification
