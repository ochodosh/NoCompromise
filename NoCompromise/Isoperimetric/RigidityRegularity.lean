import NoCompromise.Isoperimetric.Rigidity
import NoCompromise.Isoperimetric.RigidityMinimal
import NoCompromise.Cones.NoSingular
import NoCompromise.Regularity.RepresentativeOpen

/-!
# Steps 1–2 of isoperimetric rigidity: the regular representative of an equality set

Blueprint `thm:isoperimetric-rigidity`, Steps 1–2.

* Step 1. Equality `Per(E) = c_I |E|^{2/3}` makes `E` a perimeter minimiser among
  Lebesgue-measurable sets of its volume (`thm:sharp-isoperimetric`, hence modulo
  `ABPNeumannSolvable`), hence unit-scale `ω`-minimal (`Isoperimetric/RigidityMinimal.lean`:
  `lem:penalization` and `lem:quasiminimal` with the Coulomb terms deleted).
* Step 2, up to `C^{1,1/2}`. `prop:no-singular-points` (proved) and `lem:bounded-representative`
  give the density-one representative `Ω = E^{(1)}`: bounded, open, every boundary point regular
  (a one-sided `C^{1,1/2}` graph chart), compact `C¹` boundary, `Ω = int cl Ω`,
  `Per(Ω) = H²(∂Ω)`, `Ω = E` almost everywhere, and `Ω` is itself a perimeter minimiser
  (`isoperimetric_equality_regular_representative`).
* Step 2, smoothness. The bootstrap of `sec:bootstrap` (Chapter 28) with `v_Ω` replaced by `0`
  is formalised in Lean only for liquid-drop minimisers (`MinimizerRep`), and only up to `C³`
  (`prop:bootstrap-C3`); the blueprint's "makes it smooth" also needs the iteration of
  `thm:nondiv-schauder` to all orders. That remaining step enters as the named hypothesis
  `PerimeterMinimizerSmoothBootstrap`.

With these, `IsoperimetricEqualityRegularity` follows from `ABPNeumannSolvable` and
`PerimeterMinimizerSmoothBootstrap` (`isoperimetricEqualityRegularity_of_smoothBootstrap`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal symmDiff

namespace LiquidDrop

/-- Being a Lebesgue perimeter minimiser of volume `V` depends only on the almost-everywhere
class of the set, among null-measurable sets. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.congr_ae {V : ℝ} {E F : Set AmbientSpace}
    (hE : IsLebesgueFixedVolumePerimeterMinimizer V E) (hF : NullMeasurableSet F volume)
    (hEF : F =ᵐ[volume] E) : IsLebesgueFixedVolumePerimeterMinimizer V F := by
  refine ⟨hF, (measure_congr hEF).trans hE.2.1, (perimeter_congr_ae hEF).trans_lt hE.2.2.1, ?_⟩
  intro G hG hvG
  rw [perimeter_congr_ae hEF]
  exact hE.2.2.2 G hG hvG

/-- Blueprint `thm:isoperimetric-rigidity`, Step 1, first sentence: equality in the sharp
isoperimetric inequality makes `E` a perimeter minimiser among Lebesgue-measurable sets of its
volume. Uses `thm:sharp-isoperimetric`, hence `lem:abp-neumann`. -/
theorem isLebesgueFixedVolumePerimeterMinimizer_of_isoperimetric_eq
    (hN : ABPNeumannSolvable) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hfin : volume E < ∞)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueFixedVolumePerimeterMinimizer (volume E).toReal E := by
  refine ⟨hE, (ENNReal.ofReal_toReal hfin.ne).symm, ?_, ?_⟩
  · rw [heq]
    exact ENNReal.ofReal_lt_top
  · intro F hF hvF
    have hvF' : volume F = volume E := by rw [hvF, ENNReal.ofReal_toReal hfin.ne]
    have hFfin : volume F < ∞ := hvF' ▸ hfin
    have hsharp := sharp_isoperimetric hN hF hFfin
    rw [hvF'] at hsharp
    rw [heq]
    exact hsharp

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 1–2 up to `C^{1,1/2}`: for an equality set
`E` (`0 < |E| < ∞`, `Per(E) = c_I |E|^{2/3}`), the density-one representative `Ω = E^{(1)}` is
a bounded open perimeter minimiser of volume `|E|`, every boundary point of `Ω` is regular
(one-sided `C^{1,1/2}` graph chart), `∂Ω` is compact, `Ω` has `C¹` boundary, `Ω = int cl Ω`,
`Per(Ω) = H²(∂Ω)`, and `Ω = E` almost everywhere. Uses `lem:abp-neumann` only through
`thm:sharp-isoperimetric`. -/
theorem isoperimetric_equality_regular_representative (hN : ABPNeumannSolvable)
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hpos : 0 < volume E)
    (hfin : volume E < ∞)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueFixedVolumePerimeterMinimizer (volume E).toReal (densityOne E) ∧
      IsOpen (densityOne E) ∧ Bornology.IsBounded (densityOne E) ∧
      (∀ x ∈ frontier (densityOne E), IsRegularBoundaryPoint (densityOne E) x) ∧
      IsCompact (frontier (densityOne E)) ∧ HasC1Boundary (densityOne E) ∧
      densityOne E = interior (closure (densityOne E)) ∧
      perimeter (densityOne E) = hausdorffMeasure2 3 (frontier (densityOne E)) ∧
      densityOne E =ᵐ[volume] E := by
  have hmin := isLebesgueFixedVolumePerimeterMinimizer_of_isoperimetric_eq hN hE hfin heq
  have hV : 0 < (volume E).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hω := hmin.isOmegaMinimal_explicit hV
  obtain ⟨hreg, hc, hC1, -, hint, hper⟩ := no_singular_points hω hfin
  have hopen := hω.isOpen_densityOne
  have hae : densityOne E =ᵐ[volume] E := densityOne_ae_eq (by norm_num) hE
  exact ⟨hmin.congr_ae hopen.measurableSet.nullMeasurableSet hae, hopen,
    (quasiminimal_bounded_representative hω hfin).1, hreg, hc, hC1, hint, hper, hae⟩

/-- The remaining part of blueprint `thm:isoperimetric-rigidity`, Step 2, as a named
hypothesis: the smooth bootstrap of `sec:bootstrap` with `v_Ω` replaced by `0`, continued to
all orders. A bounded open perimeter minimiser `Ω` among Lebesgue sets of volume `V > 0`, whose
boundary points are all regular (one-sided `C^{1,1/2}` graph charts) and which has `C¹`
boundary, has smooth boundary.

Mathematically: in each chart the height solves the weak constant-mean-curvature equation
`div(∇f / √(1 + |∇f|²)) = ±λ` with `λ = 2 Per(Ω) / (3V)` (`lem:graph-PMC` with `v_Ω = 0`);
`prop:bootstrap-C2` and `prop:bootstrap-C3` give `C^{3,β}`, and repeating the differentiation
step of `prop:bootstrap-C3` with `thm:nondiv-schauder` gives every order. Lean has the
Chapter 28 bootstrap only for liquid-drop minimisers (`MinimizerRep`) and only up to `C³`. -/
def PerimeterMinimizerSmoothBootstrap : Prop :=
  ∀ (V : ℝ) (Ω : Set AmbientSpace), 0 < V → IsOpen Ω → Bornology.IsBounded Ω →
    (∀ x ∈ frontier Ω, IsRegularBoundaryPoint Ω x) → HasC1Boundary Ω →
    IsLebesgueFixedVolumePerimeterMinimizer V Ω → HasSmoothBoundary Ω

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 1–2: `IsoperimetricEqualityRegularity` from
`lem:abp-neumann` (through `thm:sharp-isoperimetric`) and the smooth Coulomb-free bootstrap
`PerimeterMinimizerSmoothBootstrap`. The representative is the density-one set `E^{(1)}`. -/
theorem isoperimetricEqualityRegularity_of_smoothBootstrap (hN : ABPNeumannSolvable)
    (hS : PerimeterMinimizerSmoothBootstrap) : IsoperimetricEqualityRegularity := by
  intro E hE hpos hfin _hper heq
  obtain ⟨hmin, hopen, hb, hreg, -, hC1, -, -, hae⟩ :=
    isoperimetric_equality_regular_representative hN hE hpos hfin heq
  exact ⟨densityOne E, hopen, hb,
    hS _ _ (ENNReal.toReal_pos hpos.ne' hfin.ne) hopen hb hreg hC1 hmin, hae⟩

/-- Blueprint `thm:isoperimetric-rigidity`, direct half, from `lem:abp-neumann` and the smooth
Coulomb-free bootstrap `PerimeterMinimizerSmoothBootstrap`. -/
theorem isoperimetric_rigidity_of_smoothBootstrap (hN : ABPNeumannSolvable)
    (hS : PerimeterMinimizerSmoothBootstrap) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hpos : 0 < volume E) (hfin : volume E < ∞)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueBallUpToNull (volume E).toReal E :=
  isoperimetric_rigidity hN (isoperimetricEqualityRegularity_of_smoothBootstrap hN hS)
    hE hpos hfin heq

/-- Blueprint `thm:isoperimetric-rigidity` as an equivalence, for `0 < |E| < ∞`, from
`lem:abp-neumann` and `PerimeterMinimizerSmoothBootstrap`. -/
theorem isoperimetric_rigidity_iff_of_smoothBootstrap (hN : ABPNeumannSolvable)
    (hS : PerimeterMinimizerSmoothBootstrap) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hpos : 0 < volume E) (hfin : volume E < ∞) :
    perimeter E =
        ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ))) ↔
      IsLebesgueBallUpToNull (volume E).toReal E :=
  isoperimetric_rigidity_iff hN (isoperimetricEqualityRegularity_of_smoothBootstrap hN hS)
    hE hpos hfin

/-- The `P_B(V)` form of `thm:isoperimetric-rigidity` used by `prop:classification`, from
`lem:abp-neumann` and `PerimeterMinimizerSmoothBootstrap`. -/
theorem isLebesgueBallUpToNull_of_perimeter_le_ballPerimeter_of_smoothBootstrap
    (hN : ABPNeumannSolvable) (hS : PerimeterMinimizerSmoothBootstrap) {V : ℝ} (hV : 0 < V)
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    (hvol : volume E = ENNReal.ofReal V) (hP : perimeter E ≤ ballPerimeter V) :
    IsLebesgueBallUpToNull V E :=
  isLebesgueBallUpToNull_of_perimeter_le_ballPerimeter hN
    (isoperimetricEqualityRegularity_of_smoothBootstrap hN hS) hV hE hvol hP

end LiquidDrop
