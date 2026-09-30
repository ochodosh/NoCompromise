module

public import NoCompromise.Classification.Endpoint
public import NoCompromise.Main
public import NoCompromise.Binding.Main
public import NoCompromise.Isoperimetric.Unconditional

@[expose] public section

/-!
# Chapters 34–38 modulo `prop:cap-estimate` only

`SharpIsoperimetric` (`thm:sharp-isoperimetric`, `sharpIsoperimetric_holds`) and
`IsoperimetricRigidityStatement` (`thm:isoperimetric-rigidity`,
`isoperimetricRigidityStatement_holds`, Isoperimetric/Unconditional.lean) hold unconditionally.
Substituting them into Classification/Subcritical.lean, Classification/Endpoint.lean, Main.lean
and Binding/Main.lean leaves `CapEstimateStatement` (`prop:cap-estimate`) as the only named
hypothesis of

* `prop:classification`: `classification_of_capEstimate`, `classification_borel_of_capEstimate`;
* `prop:endpoint`: `valueFunction_eq_ball_of_capEstimate` (its first step) and
  `endpoint_of_capEstimate`;
* `cor:nonexistence`: `nonexistence_of_capEstimate`, `nonexistence_borel_of_capEstimate`;
* `thm:main-binding`: `main_binding_of_capEstimate`;
* `thm:main`: `main_of_capEstimate`, whose conclusion is verbatim that of `LiquidDrop.main`
  (Showcase.lean, not imported here and left unchanged).

`isoDeficit_nonneg_unconditional` (`not:z-delta`) needs no hypothesis at all.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LiquidDrop

/-- Blueprint `not:z-delta` (`eq:z-delta`), without hypotheses: `δ ≥ 0` for a fixed-volume
minimiser. -/
theorem isoDeficit_nonneg_unconditional {V : ℝ} {Ω : Set AmbientSpace}
    (hV : 0 < V) (hmin : IsLebesgueFixedVolumeMinimizer V Ω) : 0 ≤ isoDeficit V Ω :=
  isoDeficit_nonneg sharpIsoperimetric_holds hV hmin

/-- Blueprint `prop:classification`, modulo `CapEstimateStatement` (`prop:cap-estimate`) only:
for `0 < V ≤ V_*`, every (Lebesgue) fixed-volume minimiser agrees up to a null set with a ball
of volume `V`. -/
theorem classification_of_capEstimate (hcap : CapEstimateStatement)
    {V : ℝ} (hV : 0 < V) (hVc : V ≤ criticalVolume)
    {Ω : Set AmbientSpace} (hΩ : IsLebesgueFixedVolumeMinimizer V Ω) :
    IsLebesgueBallUpToNull V Ω :=
  classification sharpIsoperimetric_holds hcap isoperimetricRigidityStatement_holds hV hVc hΩ

/-- Blueprint `prop:classification` in the original Borel formulation
(`IsFixedVolumeMinimizer`, `IsBallUpToNull`), modulo `CapEstimateStatement`
(`prop:cap-estimate`) only. -/
theorem classification_borel_of_capEstimate (hcap : CapEstimateStatement)
    {V : ℝ} (hV : 0 < V) (hVc : V ≤ criticalVolume)
    {Ω : Set AmbientSpace} (hΩ : IsFixedVolumeMinimizer V Ω) : IsBallUpToNull V Ω :=
  classification_borel_of_hypotheses sharpIsoperimetric_holds hcap noSingularPointsStatement
    isoperimetricRigidityStatement_holds hV hVc hΩ

/-- The first step of the proof of blueprint `prop:endpoint`, modulo `CapEstimateStatement`
(`prop:cap-estimate`) only: for `0 < V < V_*`, `m(V) = 𝓔(B_V)`. -/
theorem valueFunction_eq_ball_of_capEstimate (hcap : CapEstimateStatement)
    {V : ℝ} (hV : 0 < V) (hVc : V < criticalVolume) :
    valueFunction V = energy (ballByVolume V) :=
  valueFunction_eq_ball_of_classification sharpIsoperimetric_holds
    (fun _ hV' hVc' _ hΩ => classification_of_capEstimate hcap hV' hVc' hΩ) hV hVc

/-- Blueprint `prop:endpoint`, modulo `CapEstimateStatement` (`prop:cap-estimate`) only:
`m(V_*) = 𝓔(B_{V_*})`, the ball `B_{V_*}` is a fixed-volume minimiser at volume `V_*` (in both
measurability conventions), and it is the unique one up to translation and null sets. -/
theorem endpoint_of_capEstimate (hcap : CapEstimateStatement) :
    valueFunction criticalVolume = energy (ballByVolume criticalVolume) ∧
      IsFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      IsLebesgueFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      ∀ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer criticalVolume Ω →
        IsLebesgueBallUpToNull criticalVolume Ω :=
  endpoint sharpIsoperimetric_holds hcap isoperimetricRigidityStatement_holds

/-- Blueprint `cor:nonexistence`, modulo `CapEstimateStatement` (`prop:cap-estimate`) only: no
fixed-volume minimiser (Lebesgue-measurable convention) exists at any volume `V > V_*`. -/
theorem nonexistence_of_capEstimate (hcap : CapEstimateStatement) {V : ℝ}
    (hV : criticalVolume < V) :
    ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω :=
  nonexistence sharpIsoperimetric_holds hcap hV

/-- Blueprint `cor:nonexistence` in the Borel convention of `thm:main`, modulo
`CapEstimateStatement` (`prop:cap-estimate`) only. -/
theorem nonexistence_borel_of_capEstimate (hcap : CapEstimateStatement) {V : ℝ}
    (hV : criticalVolume < V) : ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω :=
  nonexistence_borel sharpIsoperimetric_holds hcap hV

/-- Blueprint `thm:main-binding`, modulo `CapEstimateStatement` (`prop:cap-estimate`) only: the
global energy-to-volume ratio infimum equals `3 (9π/5)^{1/3}`, it is attained, and every
optimiser is a translate of a ball of volume `5/2` up to a Lebesgue-null set. -/
theorem main_binding_of_capEstimate (hcap : CapEstimateStatement) :
    globalEnergyRatio = ENNReal.ofReal (3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ))) ∧
      (∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E) ∧
      ∀ E : Set AmbientSpace, IsGlobalRatioOptimizer E → IsLebesgueBallUpToNull (5 / 2) E :=
  main_binding sharpIsoperimetric_holds hcap isoperimetricRigidityStatement_holds

/-- Blueprint `thm:main`, modulo `CapEstimateStatement` (`prop:cap-estimate`) only. The
conclusion is verbatim that of `LiquidDrop.main` (Showcase.lean). -/
theorem main_of_capEstimate (hcap : CapEstimateStatement) (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω) :=
  main_of_sharp_of_capEstimate_of_rigidity sharpIsoperimetric_holds hcap
    isoperimetricRigidityStatement_holds V hV

end LiquidDrop
