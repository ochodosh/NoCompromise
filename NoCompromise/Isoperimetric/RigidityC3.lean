module

public import NoCompromise.Isoperimetric.ComponentsC3
public import NoCompromise.Isoperimetric.BallSmoothBoundary
public import NoCompromise.Isoperimetric.RigidityBootstrap
public import NoCompromise.Isoperimetric.RigidityStatement

@[expose] public section

/-!
# Isoperimetric rigidity from the ABP Neumann problem on `C³` domains

Blueprint `thm:isoperimetric-rigidity`, with `lem:abp-neumann` in the strengthened form
`ABPNeumannSolvableC3` (`Isoperimetric/ABPNeumannC3.lean`) and with no other named hypothesis.

* Steps 3–5 for `C³` domains (`iso_C3_rigidity_connected`, `iso_C3_rigidity`): the equality
  argument of `Isoperimetric/RigiditySmooth.lean` uses only `C²` interior regularity, `C¹`
  regularity up to the boundary, the pointwise equation and the conormal condition, all supplied
  by `ABPNeumannSolvableC3`; the component step uses `cor:iso-smooth-components` for `C³`
  domains (`Isoperimetric/ComponentsC3.lean`).
* Steps 1–2 (`isoperimetric_equality_C3_representative`): the density-one representative of an
  equality set is a bounded open perimeter minimiser with `C³` boundary (`prop:bootstrap-C3` with
  `v_Ω = 0`, `IsLebesgueFixedVolumePerimeterMinimizer.hasCkBoundary_three`). The `C³`-to-smooth
  step (`CMCGraphSmoothStatement`) is not needed: Steps 3–5 apply at `C³`, and a ball has smooth
  boundary (`hasSmoothBoundary_ball`).

Consequently `IsoperimetricEqualityRegularity`, `IsoperimetricRigidityStatement` and
`PerimeterMinimizerSmoothBootstrap` all follow from `ABPNeumannSolvableC3` alone.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal symmDiff

namespace LiquidDrop

/-! ### Steps 3–5 for `C³` domains -/

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 4–5 for a bounded connected open set with `C³`
boundary, given `ABPNeumannSolvableC3`: `Per(G)^3 ≤ 36π|G|^2` forces `G` to be a ball. -/
theorem iso_C3_rigidity_connected (hN : ABPNeumannSolvableC3) {G : Set AmbientSpace}
    (hGo : IsOpen G) (hGb : Bornology.IsBounded G) (hGc : IsConnected G)
    (hG : HasCkBoundary 3 G)
    (heq : (perimeter G).toReal ^ 3 ≤ 36 * Real.pi * volume.real G ^ 2) :
    ∃ (p : AmbientSpace) (r : ℝ), 0 < r ∧ G = ball p r := by
  obtain ⟨z, hz2, hz1, hlap, hν⟩ := hN G hGo hGb hGc hG
  have hV : 0 < volume.real G :=
    ENNReal.toReal_pos_iff.mpr ⟨hGo.measure_pos volume hGc.nonempty, hGb.measure_lt_top⟩
  have hiso := iso_C3 hN hGo hGb hGc hG
  set P := (perimeter G).toReal with hP
  have hP0 : 0 < P := by
    have : 0 < P ^ 3 := lt_of_lt_of_le (by positivity) hiso
    have hP0' : 0 ≤ P := ENNReal.toReal_nonneg
    rcases hP0'.lt_or_eq with h | h
    · exact h
    · rw [← h] at this; norm_num at this
  set c := P / volume.real G with hc
  have hc0 : 0 < c := div_pos hP0 hV
  have hvol : volume G * ENNReal.ofReal ((c / 3) ^ 3) ≤ ENNReal.ofReal (4 * Real.pi / 3) := by
    rw [← ENNReal.ofReal_toReal hGb.measure_lt_top.ne,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    apply ENNReal.ofReal_le_ofReal
    change volume.real G * (c / 3) ^ 3 ≤ 4 * Real.pi / 3
    have he : volume.real G * (c / 3) ^ 3 = P ^ 3 / (27 * volume.real G ^ 2) := by
      rw [hc]; field_simp; ring
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith [heq]
  obtain ⟨p, hp⟩ := abp_equality_eq_ball hGb hGo hGc hz2 hz1.continuousOn
    (hG.hasC1Boundary.neumannOne hz1 hν) hc0 hlap hvol
  exact ⟨p, (c / 3)⁻¹, by positivity, hp⟩

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 3–5 for a bounded open set with `C³` boundary,
given `ABPNeumannSolvableC3`: if `0 < |S|` and `Per(S) ≤ (36π)^{1/3} |S|^{2/3}`, then `S` has one
component (`cor:iso-smooth-components`, strictness via `lem:concavity-23`) and is a ball. -/
theorem iso_C3_rigidity (hN : ABPNeumannSolvableC3) {S : Set AmbientSpace}
    (hSo : IsOpen S) (hSb : Bornology.IsBounded S) (hSs : HasCkBoundary 3 S)
    (hpos : 0 < volume S)
    (heq : perimeter S ≤
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ)))) :
    ∃ (p : AmbientSpace) (r : ℝ), 0 < r ∧ S = ball p r := by
  have hfin : volume S ≠ ∞ := hSb.measure_lt_top.ne
  have hcI : 0 < (36 * Real.pi) ^ (1 / (3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hrw : ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ)))
      = ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ))) * volume S ^ (2 / (3 : ℝ)) := by
    rw [ENNReal.ofReal_mul hcI.le,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hfin]
  -- Step 3: one component
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have hconn : IsConnected S := by
    have hK : connectedComponentIn S x = S := by
      by_contra hne
      obtain ⟨y, hyS, hyK⟩ : ∃ y ∈ S, y ∉ connectedComponentIn S x := by
        by_contra h
        push Not at h
        exact hne (Subset.antisymm (connectedComponentIn_subset S x) h)
      have hGH : connectedComponentIn S x ≠ connectedComponentIn S y := by
        intro h
        exact hyK (h ▸ mem_connectedComponentIn hyS)
      have hlt := volume_rpow_lt_tsum_openComponents hSo hSb ⟨x, hx, rfl⟩ ⟨y, hyS, rfl⟩ hGH
      obtain ⟨h1, -⟩ := iso_C3_components_of_abpNeumannSolvableC3 hN hSo hSb hSs
      have hc0 : ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ))) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hcI).ne'
      have hlt' := ENNReal.mul_lt_mul_right hc0 ENNReal.ofReal_ne_top hlt
      have := (hlt'.trans_le h1).trans_le heq
      rw [hrw] at this
      exact lt_irrefl _ this
    rw [← hK]
    exact isConnected_connectedComponentIn_iff.mpr hx
  apply iso_C3_rigidity_connected hN hSo hSb hconn hSs
  -- the cubic form of the equality
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top heq
  rw [ENNReal.toReal_ofReal (by positivity)] at hle
  have hc3 : ((36 * Real.pi) ^ (1 / (3 : ℝ))) ^ 3 = 36 * Real.pi := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hv3 : ((volume S).toReal ^ (2 / (3 : ℝ))) ^ 3 = volume.real S ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
    rfl
  calc
    (perimeter S).toReal ^ 3 ≤
        ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ))) ^ 3 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hle 3
    _ = 36 * Real.pi * volume.real S ^ 2 := by rw [mul_pow, hc3, hv3]

/-- The `P_B(V)` form of `iso_C3_rigidity`: a bounded open set with `C³` boundary, volume `V > 0`
and `Per(Ω) ≤ P_B(V)` is a ball of radius `ballRadius V`, given `ABPNeumannSolvableC3`. -/
theorem eq_ball_of_perimeter_le_ballPerimeter_C3 (hN : ABPNeumannSolvableC3) {V : ℝ}
    (hV : 0 < V) {Ω : Set AmbientSpace} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩs : HasCkBoundary 3 Ω) (hvol : volume Ω = ENNReal.ofReal V)
    (hP : perimeter Ω ≤ ballPerimeter V) :
    ∃ p : AmbientSpace, Ω = ball p (ballRadius V) := by
  have hreal : (volume Ω).toReal = V := by rw [hvol, ENNReal.toReal_ofReal hV.le]
  obtain ⟨p, r, hr, rfl⟩ := iso_C3_rigidity hN hΩo hΩb hΩs
    (by rw [hvol]; exact ENNReal.ofReal_pos.mpr hV)
    (by rw [hreal, ← ballPerimeter_eq_rpow hV]; exact hP)
  exact ⟨p, by rw [ballRadius_eq_of_volume_ball hr hvol]⟩

/-! ### Steps 1–2 at `C³` -/

/-- Blueprint `thm:isoperimetric-rigidity`, Step 1, first sentence, given
`ABPNeumannSolvableC3`: an equality set is a perimeter minimiser among Lebesgue-measurable sets
of its volume. -/
theorem isLebesgueFixedVolumePerimeterMinimizer_of_isoperimetric_eq_C3
    (hN : ABPNeumannSolvableC3) {E : Set AmbientSpace}
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
    have hsharp := sharp_isoperimetric_of_abpNeumannSolvableC3 hN hF hFfin
    rw [hvF'] at hsharp
    rw [heq]
    exact hsharp

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 1–2 up to `C³`, given `ABPNeumannSolvableC3`:
for an equality set `E` (`0 < |E| < ∞`, `Per(E) = c_I |E|^{2/3}`), the density-one representative
`Ω = E^{(1)}` is a bounded open perimeter minimiser of volume `|E|` with `C³` boundary, and
`Ω = E` almost everywhere. -/
theorem isoperimetric_equality_C3_representative (hN : ABPNeumannSolvableC3)
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hpos : 0 < volume E)
    (hfin : volume E < ∞)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueFixedVolumePerimeterMinimizer (volume E).toReal (densityOne E) ∧
      IsOpen (densityOne E) ∧ Bornology.IsBounded (densityOne E) ∧
      HasCkBoundary 3 (densityOne E) ∧ densityOne E =ᵐ[volume] E := by
  have hmin := isLebesgueFixedVolumePerimeterMinimizer_of_isoperimetric_eq_C3 hN hE hfin heq
  have hV : 0 < (volume E).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hω := hmin.isOmegaMinimal_explicit hV
  obtain ⟨-, -, hC1, -, -, -⟩ := no_singular_points hω hfin
  have hopen := hω.isOpen_densityOne
  have hae : densityOne E =ᵐ[volume] E := densityOne_ae_eq (by norm_num) hE
  have hminΩ := hmin.congr_ae hopen.measurableSet.nullMeasurableSet hae
  exact ⟨hminΩ, hopen, (quasiminimal_bounded_representative hω hfin).1,
    hminΩ.hasCkBoundary_three hV hopen hC1, hae⟩

/-! ### The rigidity theorem from `ABPNeumannSolvableC3` -/

/-- Blueprint `thm:isoperimetric-rigidity`, direct half, given `ABPNeumannSolvableC3` only: if
`0 < |E| < ∞` and `Per(E) = (36π)^{1/3} |E|^{2/3}`, then `E` is, up to a null set, a translate of
a ball of volume `|E|`. -/
theorem isoperimetric_rigidity_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3)
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hpos : 0 < volume E)
    (hfin : volume E < ∞)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueBallUpToNull (volume E).toReal E := by
  obtain ⟨-, hΩo, hΩb, hΩs, hΩE⟩ :=
    isoperimetric_equality_C3_representative hN hE hpos hfin heq
  have hvol : volume (densityOne E) = volume E := measure_congr hΩE
  have hperΩ : perimeter (densityOne E) = perimeter E := perimeter_congr_ae hΩE
  obtain ⟨p, r, hr, hΩ⟩ := iso_C3_rigidity hN hΩo hΩb hΩs (hvol ▸ hpos)
    (by rw [hperΩ, hvol, heq])
  rw [hΩ] at hvol hΩE
  refine ⟨hE, p, r, hr, by rw [hvol, ENNReal.ofReal_toReal hfin.ne], ?_⟩
  rw [measure_symmDiff_eq_zero_iff]
  exact hΩE.symm

/-- Blueprint `thm:isoperimetric-rigidity` as an equivalence, for `0 < |E| < ∞`, given
`ABPNeumannSolvableC3` only. -/
theorem isoperimetric_rigidity_iff_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3)
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hpos : 0 < volume E)
    (hfin : volume E < ∞) :
    perimeter E =
        ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ))) ↔
      IsLebesgueBallUpToNull (volume E).toReal E :=
  ⟨isoperimetric_rigidity_of_abpNeumannSolvableC3 hN hE hpos hfin,
    fun h => (perimeter_eq_of_isLebesgueBallUpToNull h).2.2⟩

/-- The `P_B(V)` form of `thm:isoperimetric-rigidity` used by `prop:classification`, given
`ABPNeumannSolvableC3` only. -/
theorem isLebesgueBallUpToNull_of_perimeter_le_ballPerimeter_of_abpNeumannSolvableC3
    (hN : ABPNeumannSolvableC3) {V : ℝ} (hV : 0 < V) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hvol : volume E = ENNReal.ofReal V)
    (hP : perimeter E ≤ ballPerimeter V) : IsLebesgueBallUpToNull V E := by
  have hreal : (volume E).toReal = V := by rw [hvol, ENNReal.toReal_ofReal hV.le]
  have hfin : volume E < ∞ := by rw [hvol]; exact ENNReal.ofReal_lt_top
  have hge := sharp_isoperimetric_of_abpNeumannSolvableC3 hN hE hfin
  rw [hreal, ← ballPerimeter_eq_rpow hV] at hge
  have h := isoperimetric_rigidity_of_abpNeumannSolvableC3 hN hE
    (by rw [hvol]; exact ENNReal.ofReal_pos.mpr hV) hfin
    (by rw [hreal, ← ballPerimeter_eq_rpow hV]; exact le_antisymm hP hge)
  rwa [hreal] at h

/-- `IsoperimetricRigidityStatement` (the form used by Chapters 34–35) from
`ABPNeumannSolvableC3` alone. -/
theorem isoperimetricRigidityStatement_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3) :
    IsoperimetricRigidityStatement :=
  fun _E hE hpos hfin _hper heq =>
    isoperimetric_rigidity_of_abpNeumannSolvableC3 hN hE hpos hfin heq

/-- `IsoperimetricEqualityRegularity` (Steps 1–2 with a smooth representative) from
`ABPNeumannSolvableC3` alone: by the rigidity theorem the equality set agrees a.e. with a ball,
which is open, bounded and has smooth boundary. -/
theorem isoperimetricEqualityRegularity_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3) :
    IsoperimetricEqualityRegularity := by
  intro E hE hpos hfin _hper heq
  obtain ⟨-, p, r, hr, -, hnull⟩ :=
    isoperimetric_rigidity_of_abpNeumannSolvableC3 hN hE hpos hfin heq
  exact ⟨ball p r, isOpen_ball, isBounded_ball, hasSmoothBoundary_ball p hr,
    ((measure_symmDiff_eq_zero_iff).mp hnull).symm⟩

/-- `PerimeterMinimizerSmoothBootstrap` from `ABPNeumannSolvableC3` alone: a bounded open
perimeter minimiser of volume `V > 0` with `C¹` boundary has `C³` boundary
(`prop:bootstrap-C3` with `v_Ω = 0`), satisfies `Per(Ω) ≤ P_B(V)` by comparison with a ball, and
is therefore a ball (`eq_ball_of_perimeter_le_ballPerimeter_C3`), whose boundary is smooth. -/
theorem perimeterMinimizerSmoothBootstrap_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3) :
    PerimeterMinimizerSmoothBootstrap := by
  intro V Ω hV hΩo hΩb _hreg hC1 hmin
  have hP : perimeter Ω ≤ ballPerimeter V :=
    hmin.2.2.2 (ballByVolume V) measurableSet_ball.nullMeasurableSet (volume_ballByVolume hV)
  obtain ⟨p, rfl⟩ := eq_ball_of_perimeter_le_ballPerimeter_C3 hN hV hΩo hΩb
    (hmin.hasCkBoundary_three hV hΩo hC1) hmin.2.1 hP
  exact hasSmoothBoundary_ball p (ballRadius_pos hV)

end LiquidDrop
