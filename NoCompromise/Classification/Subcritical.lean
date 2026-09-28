import NoCompromise.Stationary.MinimizerStationary
import NoCompromise.Stationary.CapacitaryEstimate
import NoCompromise.Regularity.PenalizationQuasiminimal
import NoCompromise.Regularity.RepresentativeBounded
import NoCompromise.Regularity.RepresentativeOpen
import NoCompromise.Value.Defs
import NoCompromise.Energy.NullInvariance
import NoCompromise.Threshold.Algebra
import NoCompromise.Threshold.Ledger
import NoCompromise.Cones.NoSingular
import NoCompromise.Isoperimetric.Rigidity

/-!
# Classification at volumes at most `V_*`

Blueprint Chapter 34 (`ch:classification`).

Results of other chapters that are not yet formalised enter as explicit named
predicates, following the pattern of `SharpIsoperimetric` (`Value/Defs.lean`) and
`ABPNeumannSolvable` (`Isoperimetric/ABPNeumann.lean`):

* `CapEstimateStatement` is blueprint `prop:cap-estimate` (Chapter 33) verbatim;
* `NoSingularPointsStatement` is the regularity part of blueprint
  `prop:no-singular-points` (Chapter 26) used downstream: the density-one
  representative of a finite-volume `ω`-minimal set has `C¹` boundary in the
  one-sided graph convention of `HasC1Boundary` (it is implied by the blueprint's
  compact embedded `C^{1,1/2}` boundary);
* `IsoperimetricRigidityStatement` is the forward direction of blueprint
  `thm:isoperimetric-rigidity` (Chapter 27).

`NoSingularPointsStatement` is discharged (`noSingularPointsStatement`) by the proved
`prop:no-singular-points` (`no_singular_points`, Cones/NoSingular.lean), and
`IsoperimetricRigidityStatement` reduces (`isoperimetricRigidityStatement_of_abpNeumann`) to
the two named hypotheses `ABPNeumannSolvable` (`lem:abp-neumann`) and
`IsoperimetricEqualityRegularity` (Steps 1–2 of `thm:isoperimetric-rigidity`) of
`isoperimetric_rigidity` (Isoperimetric/Rigidity.lean). Hence `classification` depends only on
`SharpIsoperimetric`, `CapEstimateStatement` and `IsoperimetricRigidityStatement`, and
`classification_of_abpNeumann` only on `ABPNeumannSolvable`,
`IsoperimetricEqualityRegularity` and `CapEstimateStatement`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LiquidDrop

/-- Blueprint `prop:cap-estimate` (`eq:cap-estimate`) as a named hypothesis: every bounded
connected `C³` stationary domain (`IsStationaryDomain`, which bundles these properties) of
volume `V > 0` with multiplier `lam` satisfies `lam √(Per(Ω)/(4π)) ≥ V + 2` for `V ≤ 6`
and `≥ 4√(V - 2)` for `V ≥ 6`. -/
def CapEstimateStatement : Prop :=
  ∀ (V lam : ℝ) (Ω : Set AmbientSpace), 0 < V → IsStationaryDomain V lam Ω →
    (V ≤ 6 → V + 2 ≤ lam * Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi))) ∧
      (6 ≤ V → 4 * Real.sqrt (V - 2) ≤ lam * Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi)))

/-- The regularity assertion of blueprint `prop:no-singular-points` as a named hypothesis:
for an `ω`-minimal set `E` with `|E| < ∞`, every boundary point of the density-one
representative `Ω = densityOne E` is regular, i.e. `Ω` has `C¹` boundary charts
(`HasC1Boundary`). -/
def NoSingularPointsStatement : Prop :=
  ∀ (E : Set AmbientSpace) (ω : ℝ), IsOmegaMinimal E ω → volume E < ∞ →
    HasC1Boundary (densityOne E)

/-- Blueprint `thm:isoperimetric-rigidity` (forward direction) as a named hypothesis: a
Lebesgue-measurable `E` with `0 < |E| < ∞`, finite perimeter and
`Per(E) = c_I |E|^{2/3}`, `c_I = (36π)^{1/3}`, agrees up to a null set with a ball of
volume `|E|`. -/
def IsoperimetricRigidityStatement : Prop :=
  ∀ E : Set AmbientSpace, NullMeasurableSet E volume → 0 < volume E → volume E < ∞ →
    perimeter E < ∞ →
    perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ))) →
    IsLebesgueBallUpToNull (volume E).toReal E

/-- `NoSingularPointsStatement` holds: it is the `HasC1Boundary` assertion of the proved
blueprint `prop:no-singular-points` (`no_singular_points`). -/
theorem noSingularPointsStatement : NoSingularPointsStatement :=
  fun _ _ hE hV => (no_singular_points hE hV).2.2.1

/-- `IsoperimetricRigidityStatement` from `isoperimetric_rigidity` (the direct half of
`thm:isoperimetric-rigidity`), modulo its named hypotheses `ABPNeumannSolvable`
(`lem:abp-neumann`) and `IsoperimetricEqualityRegularity` (Steps 1–2). -/
theorem isoperimetricRigidityStatement_of_abpNeumann (hN : ABPNeumannSolvable)
    (hR : IsoperimetricEqualityRegularity) : IsoperimetricRigidityStatement :=
  fun _ hE hpos hfin _ heq => isoperimetric_rigidity hN hR hE hpos hfin heq

/-- The bounded open `C¹` representative of a fixed-volume minimiser (`not:minimizer-rep`),
from `lem:quasiminimal`, `lem:open-representative`, `lem:bounded-representative` and the
named regularity hypothesis `NoSingularPointsStatement` (`prop:no-singular-points`). -/
theorem IsLebesgueFixedVolumeMinimizer.minimizerRep_densityOne
    (hreg : NoSingularPointsStatement) {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hΩ : IsLebesgueFixedVolumeMinimizer V Ω) :
    MinimizerRep V (densityOne Ω) ∧ densityOne Ω =ᵐ[volume] Ω := by
  have hω := hΩ.isOmegaMinimal hV
  have hfin : volume Ω < ∞ := by rw [hΩ.2.1]; exact ENNReal.ofReal_lt_top
  have hae : densityOne Ω =ᵐ[volume] Ω := densityOne_ae_eq (by norm_num) hΩ.1
  refine ⟨⟨hV, hω.isOpen_densityOne, (quasiminimal_bounded_representative hω hfin).1,
    hreg Ω _ hω hfin, (isLebesgueFixedVolumeMinimizer_congr_ae V hae).mpr hΩ⟩, hae⟩

/-- Blueprint `not:z-delta` (`eq:z-delta`): the isoperimetric deficit parameter
`δ = √(Per(Ω)/P_B(V)) − 1`, so that `z = 1 + δ`. -/
def isoDeficit (V : ℝ) (Ω : Set AmbientSpace) : ℝ :=
  Real.sqrt ((perimeter Ω).toReal / (ballPerimeter V).toReal) - 1

/-- Blueprint `not:z-delta`: `z = 1 + δ = √(Per(Ω)/P_B(V))`. -/
theorem one_add_isoDeficit (V : ℝ) (Ω : Set AmbientSpace) :
    1 + isoDeficit V Ω = Real.sqrt ((perimeter Ω).toReal / (ballPerimeter V).toReal) := by
  rw [isoDeficit]
  ring

theorem one_add_isoDeficit_nonneg (V : ℝ) (Ω : Set AmbientSpace) : 0 ≤ 1 + isoDeficit V Ω := by
  rw [one_add_isoDeficit]
  exact Real.sqrt_nonneg _

/-- Blueprint `not:z-delta` (`eq:z-delta`): `δ ≥ 0` for a fixed-volume minimiser, by
`thm:sharp-isoperimetric` (the named hypothesis `SharpIsoperimetric`). -/
theorem isoDeficit_nonneg (hiso : SharpIsoperimetric) {V : ℝ} {Ω : Set AmbientSpace}
    (hV : 0 < V) (hmin : IsLebesgueFixedVolumeMinimizer V Ω) : 0 ≤ isoDeficit V Ω := by
  have hfin : volume Ω < ∞ := by rw [hmin.2.1]; exact ENNReal.ofReal_lt_top
  have hpos : 0 < volume Ω := by rw [hmin.2.1]; exact ENNReal.ofReal_pos.mpr hV
  have hreal : (volume Ω).toReal = V := by rw [hmin.2.1, ENNReal.toReal_ofReal hV.le]
  have hle := hiso.ballPerimeter_le hmin.1 hfin hpos
  rw [hreal] at hle
  have hPB : 0 < (ballPerimeter V).toReal :=
    ENNReal.toReal_pos (ballPerimeter_pos hV).ne' (ballPerimeter_lt_top hV).ne
  have hle' : (ballPerimeter V).toReal ≤ (perimeter Ω).toReal :=
    ENNReal.toReal_mono hmin.2.2.1.ne hle
  have h1 : 1 ≤ (perimeter Ω).toReal / (ballPerimeter V).toReal := by
    rw [le_div_iff₀ hPB]
    linarith
  have h2 : 1 ≤ Real.sqrt ((perimeter Ω).toReal / (ballPerimeter V).toReal) :=
    Real.one_le_sqrt.mpr h1
  rw [isoDeficit]
  linarith

/-- Blueprint `eq:z-identities`, first identity: `Per(Ω) = P_B z²`. -/
theorem perimeter_toReal_eq_isoDeficit {V : ℝ} (hV : 0 < V) (Ω : Set AmbientSpace) :
    (perimeter Ω).toReal = (ballPerimeter V).toReal * (1 + isoDeficit V Ω) ^ 2 := by
  have hPB : 0 < (ballPerimeter V).toReal :=
    ENNReal.toReal_pos (ballPerimeter_pos hV).ne' (ballPerimeter_lt_top hV).ne
  rw [one_add_isoDeficit, Real.sq_sqrt (div_nonneg ENNReal.toReal_nonneg hPB.le),
    mul_div_cancel₀ _ hPB.ne']

/-- Blueprint `eq:z-identities`, second identity: `√(Per(Ω)/(4π)) = R z`. -/
theorem sqrt_perimeter_eq_isoDeficit {V : ℝ} (hV : 0 < V) (Ω : Set AmbientSpace) :
    Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi)) = ballRadius V * (1 + isoDeficit V Ω) := by
  have hz0 := one_add_isoDeficit_nonneg V Ω
  have hR := ballRadius_pos hV
  have hpi : (4 * Real.pi) ≠ 0 := by positivity
  rw [perimeter_toReal_eq_isoDeficit hV Ω, ballPerimeter_toReal_eq_radius hV,
    show 4 * Real.pi * ballRadius V ^ 2 * (1 + isoDeficit V Ω) ^ 2 =
      4 * Real.pi * (ballRadius V * (1 + isoDeficit V Ω)) ^ 2 by ring,
    mul_div_cancel_left₀ _ hpi]
  exact Real.sqrt_sq (mul_nonneg hR.le hz0)

/-- Blueprint `lem:one-ball-upper` (`eq:one-ball-upper`) for the explicit multiplier
`λ = (2P + 5D)/(3V)` of the scaling identity (`prop:scaling-identity`):
`λ √(Per(Ω)/(4π)) ≤ (V + 5 - 3z²) z` with `z = 1 + δ`. -/
theorem one_ball_upper {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hmin : IsLebesgueFixedVolumeMinimizer V Ω) :
    minimizerMultiplier V Ω * Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi)) ≤
      (V + 5 - 3 * (1 + isoDeficit V Ω) ^ 2) * (1 + isoDeficit V Ω) := by
  have hvolfin : volume Ω < ∞ := by rw [hmin.2.1]; exact ENNReal.ofReal_lt_top
  have hEB : energy (ballByVolume V) < ∞ := by
    rw [energy_ballByVolume hV]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ballPerimeter_lt_top hV)
  -- `cor:ball-energy`: `𝓔(Ω) ≤ 𝓔(B_V) = (V + 5)/5 P_B`.
  have hle : (energy Ω).toReal ≤ (V + 5) / 5 * (ballPerimeter V).toReal := by
    rw [← energy_ballByVolume_toReal hV]
    exact ENNReal.toReal_mono hEB.ne
      (hmin.2.2.2 _ measurableSet_ball.nullMeasurableSet (volume_ballByVolume hV))
  have hE : (energy Ω).toReal = (perimeter Ω).toReal + (coulombEnergy Ω).toReal := by
    rw [energy, ENNReal.toReal_add hmin.2.2.1.ne (coulombEnergy_lt_top Ω hvolfin).ne]
  have hRP := radius_mul_ballPerimeter hV
  have hPz := perimeter_toReal_eq_isoDeficit hV Ω
  have hz0 := one_add_isoDeficit_nonneg V Ω
  have hR := ballRadius_pos hV
  rw [sqrt_perimeter_eq_isoDeficit hV Ω, minimizerMultiplier]
  set z := 1 + isoDeficit V Ω
  set P := (perimeter Ω).toReal
  set D := (coulombEnergy Ω).toReal
  set PB := (ballPerimeter V).toReal
  set R := ballRadius V
  have hnum : 2 * P + 5 * D ≤ PB * (V + 5 - 3 * z ^ 2) := by
    rw [hE] at hle
    nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  calc (2 * P + 5 * D) * (R * z) ≤ PB * (V + 5 - 3 * z ^ 2) * (R * z) :=
        mul_le_mul_of_nonneg_right hnum (mul_nonneg hR.le hz0)
    _ = (V + 5 - 3 * z ^ 2) * z * (3 * V) := by rw [← hRP]; ring

/-- Blueprint `lem:one-ball-upper` (`eq:one-ball-upper`) for any multiplier `λ` satisfying
the weak Euler--Lagrange equation; such `λ` is the explicit one by the uniqueness part of
`prop:scaling-identity`. -/
theorem one_ball_upper_of_weak_euler_lagrange {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hmin : IsLebesgueFixedVolumeMinimizer V Ω) (hb : Bornology.IsBounded Ω)
    (hP : HasLocallyFinitePerimeter Ω) {lam : ℝ}
    (hlam : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ (⊤ : ℕ∞) X → HasCompactSupport X →
      (∫ x in reducedBoundary Ω hP hmin.1,
          tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3) =
        ∫ x in reducedBoundary Ω hP hmin.1,
          (lam - (coulombPotential Ω x).toReal) *
            inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3) :
    lam * Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi)) ≤
      (V + 5 - 3 * (1 + isoDeficit V Ω) ^ 2) * (1 + isoDeficit V Ω) := by
  rw [eq_minimizerMultiplier_of_weak_euler_lagrange hV hmin hb hP hlam]
  exact one_ball_upper hV hmin

/-- Blueprint `prop:classification`: for `0 < V ≤ V_*`, every (Lebesgue) fixed-volume
minimiser agrees up to a null set with a ball of volume `V`. The inputs not yet formalised
enter as the named hypotheses `SharpIsoperimetric` (`thm:sharp-isoperimetric`),
`CapEstimateStatement` (`prop:cap-estimate`), `NoSingularPointsStatement`
(`prop:no-singular-points`) and `IsoperimetricRigidityStatement`
(`thm:isoperimetric-rigidity`). -/
theorem classification_of_hypotheses (hiso : SharpIsoperimetric) (hcap : CapEstimateStatement)
    (hreg : NoSingularPointsStatement) (hrig : IsoperimetricRigidityStatement)
    {V : ℝ} (hV : 0 < V) (hVc : V ≤ criticalVolume) {Ω : Set AmbientSpace}
    (hΩ : IsLebesgueFixedVolumeMinimizer V Ω) : IsLebesgueBallUpToNull V Ω := by
  obtain ⟨hrep, hae⟩ := hΩ.minimizerRep_densityOne hreg hV
  set Ω' := densityOne Ω with hΩ'
  have hmin := hrep.minimizer
  -- `lem:Vstar-bounds`: `V ≤ V_* < 4 < 6`.
  have hV4 : V < 4 := hVc.trans_lt criticalVolume_lt_four
  -- `cor:minimizer-stationary` and `prop:cap-estimate` (`eq:classification-lower`).
  have hlow := (hcap V _ Ω' hV hrep.isStationaryDomain.1).1 (by linarith)
  -- `lem:one-ball-upper` (`eq:one-ball-upper`).
  have hup := one_ball_upper hV hmin
  have hδ := isoDeficit_nonneg hiso hV hmin
  -- `lem:ledger-oneball`.
  have hled := ledger_oneball V (isoDeficit V Ω')
  have hδ0 : isoDeficit V Ω' = 0 := by
    by_contra hne
    have hpos : 0 < isoDeficit V Ω' := lt_of_le_of_ne hδ (Ne.symm hne)
    have hq : 0 < 4 - V + 9 * isoDeficit V Ω' + 3 * isoDeficit V Ω' ^ 2 := by
      nlinarith [sq_nonneg (isoDeficit V Ω')]
    have := mul_pos hpos hq
    linarith
  -- Equality in the isoperimetric inequality.
  have hPreal : (perimeter Ω').toReal = (ballPerimeter V).toReal := by
    rw [perimeter_toReal_eq_isoDeficit hV Ω', hδ0]
    ring
  have hPeq : perimeter Ω' = ballPerimeter V :=
    (ENNReal.toReal_eq_toReal_iff' hmin.2.2.1.ne (ballPerimeter_lt_top hV).ne).mp hPreal
  have hvolreal : (volume Ω').toReal = V := by rw [hmin.2.1, ENNReal.toReal_ofReal hV.le]
  -- `thm:isoperimetric-rigidity`.
  have hball := hrig Ω' hmin.1 (by rw [hmin.2.1]; exact ENNReal.ofReal_pos.mpr hV)
    (by rw [hmin.2.1]; exact ENNReal.ofReal_lt_top) hmin.2.2.1
    (by rw [hPeq, hvolreal, ballPerimeter_eq_rpow hV])
  rw [hvolreal] at hball
  exact (isLebesgueBallUpToNull_congr_ae V hae).mp hball

/-- Blueprint `prop:classification`, in the original Borel formulation
(`IsFixedVolumeMinimizer`, `IsBallUpToNull`). -/
theorem classification_borel_of_hypotheses (hiso : SharpIsoperimetric)
    (hcap : CapEstimateStatement) (hreg : NoSingularPointsStatement)
    (hrig : IsoperimetricRigidityStatement) {V : ℝ} (hV : 0 < V) (hVc : V ≤ criticalVolume)
    {Ω : Set AmbientSpace} (hΩ : IsFixedVolumeMinimizer V Ω) : IsBallUpToNull V Ω :=
  (isBallUpToNull_iff_lebesgue V Ω hΩ.1).mpr
    (classification_of_hypotheses hiso hcap hreg hrig hV hVc hΩ.toLebesgue)

/-- Blueprint `prop:classification` with `prop:no-singular-points` discharged: modulo
`SharpIsoperimetric` (`thm:sharp-isoperimetric`), `CapEstimateStatement` (`prop:cap-estimate`)
and `IsoperimetricRigidityStatement` (`thm:isoperimetric-rigidity`). -/
theorem classification (hiso : SharpIsoperimetric) (hcap : CapEstimateStatement)
    (hrig : IsoperimetricRigidityStatement) {V : ℝ} (hV : 0 < V) (hVc : V ≤ criticalVolume)
    {Ω : Set AmbientSpace} (hΩ : IsLebesgueFixedVolumeMinimizer V Ω) :
    IsLebesgueBallUpToNull V Ω :=
  classification_of_hypotheses hiso hcap noSingularPointsStatement hrig hV hVc hΩ

/-- Blueprint `prop:classification` modulo `ABPNeumannSolvable` (`lem:abp-neumann`, which gives
`thm:sharp-isoperimetric`), `IsoperimetricEqualityRegularity` (Steps 1–2 of
`thm:isoperimetric-rigidity`) and `CapEstimateStatement` (`prop:cap-estimate`). -/
theorem classification_of_abpNeumann (hN : ABPNeumannSolvable)
    (hR : IsoperimetricEqualityRegularity) (hcap : CapEstimateStatement) {V : ℝ} (hV : 0 < V)
    (hVc : V ≤ criticalVolume) {Ω : Set AmbientSpace} (hΩ : IsLebesgueFixedVolumeMinimizer V Ω) :
    IsLebesgueBallUpToNull V Ω :=
  classification (sharpIsoperimetric_of_abpNeumann hN) hcap
    (isoperimetricRigidityStatement_of_abpNeumann hN hR) hV hVc hΩ

end LiquidDrop

#print axioms LiquidDrop.noSingularPointsStatement
#print axioms LiquidDrop.isoperimetricRigidityStatement_of_abpNeumann
#print axioms LiquidDrop.classification
#print axioms LiquidDrop.classification_of_abpNeumann
#print axioms LiquidDrop.IsLebesgueFixedVolumeMinimizer.minimizerRep_densityOne
#print axioms LiquidDrop.one_add_isoDeficit
#print axioms LiquidDrop.one_add_isoDeficit_nonneg
#print axioms LiquidDrop.isoDeficit_nonneg
#print axioms LiquidDrop.perimeter_toReal_eq_isoDeficit
#print axioms LiquidDrop.sqrt_perimeter_eq_isoDeficit
#print axioms LiquidDrop.one_ball_upper
#print axioms LiquidDrop.one_ball_upper_of_weak_euler_lagrange
#print axioms LiquidDrop.classification_of_hypotheses
#print axioms LiquidDrop.classification_borel_of_hypotheses
