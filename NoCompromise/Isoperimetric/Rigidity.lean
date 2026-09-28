import NoCompromise.Isoperimetric.RigiditySmooth

/-!
# Isoperimetric rigidity

Blueprint `thm:isoperimetric-rigidity`: a set `E ⊂ ℝ³` with `0 < |E| < ∞`, finite perimeter
and `Per(E) = c_I |E|^{2/3}`, `c_I = (36π)^{1/3}`, is up to a null set a translate of a ball of
volume `|E|`; conversely balls give equality.

Steps 3–5 of the proof (one component, equality in the ABP chain, the ball) are proved in
`Isoperimetric/RigiditySmooth.lean`, modulo `ABPNeumannSolvable` (`lem:abp-neumann`). Steps 1–2
(the equality set is `ω`-minimal and has a bounded smooth representative) are the regularity
theory of Part II applied to the Coulomb-free functional, which is not yet available in Lean;
they enter as the named hypothesis `IsoperimetricEqualityRegularity`. The converse is proved
outright from `lem:ball-perimeter`.

For `prop:classification` (Chapter 34), `eq_ball_of_perimeter_le_ballPerimeter` gives the
smooth case directly (only `ABPNeumannSolvable` is needed), and
`isLebesgueBallUpToNull_of_perimeter_le_ballPerimeter` gives the general case.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal symmDiff

namespace LiquidDrop

/-- A ball of volume `V` has radius `ballRadius V`. -/
lemma ballRadius_eq_of_volume_ball {p : AmbientSpace} {r V : ℝ} (hr : 0 < r)
    (h : volume (ball p r) = ENNReal.ofReal V) : ballRadius V = r := by
  rw [volume_ball_eq_ofReal p hr.le] at h
  have hV : V = 4 * Real.pi * r ^ 3 / 3 :=
    ((ENNReal.ofReal_eq_ofReal_iff (by positivity) ?_).mp h).symm
  · rw [ballRadius, hV, show 3 * (4 * Real.pi * r ^ 3 / 3) / (4 * Real.pi) = r ^ 3 by
      field_simp, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  · by_contra hneg
    push Not at hneg
    rw [ENNReal.ofReal_of_nonpos hneg.le] at h
    exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < 4 * Real.pi * r ^ 3 / 3)).ne' h

/-- Blueprint `thm:isoperimetric-rigidity` for a bounded open set with smooth boundary, in the
`P_B(V)` form used by `prop:classification`: volume `V > 0` and `Per(Ω) ≤ P_B(V)` make `Ω` a
ball of radius `ballRadius V`. Given `lem:abp-neumann`. -/
theorem eq_ball_of_perimeter_le_ballPerimeter (hN : ABPNeumannSolvable) {V : ℝ} (hV : 0 < V)
    {Ω : Set AmbientSpace} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩs : HasSmoothBoundary Ω) (hvol : volume Ω = ENNReal.ofReal V)
    (hP : perimeter Ω ≤ ballPerimeter V) :
    ∃ p : AmbientSpace, Ω = ball p (ballRadius V) := by
  have hreal : (volume Ω).toReal = V := by rw [hvol, ENNReal.toReal_ofReal hV.le]
  obtain ⟨p, r, hr, rfl⟩ := iso_smooth_rigidity hN hΩo hΩb hΩs
    (by rw [hvol]; exact ENNReal.ofReal_pos.mpr hV)
    (by rw [hreal, ← ballPerimeter_eq_rpow hV]; exact hP)
  exact ⟨p, by rw [ballRadius_eq_of_volume_ball hr hvol]⟩

/-- The smooth form of `eq_ball_of_perimeter_le_ballPerimeter` as `IsBallUpToNull`. -/
theorem isBallUpToNull_of_perimeter_le_ballPerimeter (hN : ABPNeumannSolvable) {V : ℝ}
    (hV : 0 < V) {Ω : Set AmbientSpace} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩs : HasSmoothBoundary Ω) (hvol : volume Ω = ENNReal.ofReal V)
    (hP : perimeter Ω ≤ ballPerimeter V) : IsBallUpToNull V Ω := by
  obtain ⟨p, hp⟩ := eq_ball_of_perimeter_le_ballPerimeter hN hV hΩo hΩb hΩs hvol hP
  refine ⟨hΩo.measurableSet, p, ballRadius V, ballRadius_pos hV, ?_, ?_⟩
  · rw [← hp, hvol]
  · rw [← hp, symmDiff_self]; exact measure_empty

/-- Steps 1–2 of the proof of blueprint `thm:isoperimetric-rigidity`, as a named hypothesis:
a set `E` with `0 < |E| < ∞`, finite perimeter and `Per(E) = (36π)^{1/3} |E|^{2/3}` agrees
almost everywhere with a bounded open set with smooth boundary. In the blueprint this is the
regularity theory for `ω`-minimal sets applied to the Coulomb-free functional: the proofs of
`lem:penalization` and `lem:quasiminimal` with the Coulomb terms deleted, then Chapters
`ch:density`–`ch:no-singular` (ending with `prop:no-singular-points`) and the bootstrap of
`sec:bootstrap` with `v_Ω` replaced by `0`. None of this is yet available in Lean. -/
def IsoperimetricEqualityRegularity : Prop :=
  ∀ E : Set AmbientSpace, NullMeasurableSet E volume → 0 < volume E → volume E < ∞ →
    HasFinitePerimeter E →
    perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ))) →
    ∃ Ω : Set AmbientSpace, IsOpen Ω ∧ Bornology.IsBounded Ω ∧ HasSmoothBoundary Ω ∧
      Ω =ᵐ[volume] E

/-- Blueprint `thm:isoperimetric-rigidity`, direct half: if `0 < |E| < ∞` and
`Per(E) = (36π)^{1/3} |E|^{2/3}` (finite perimeter follows), then `E` is, up to a null set, a
translate of a ball of volume `|E|`. Steps 1–2 (regularity) enter as the named hypothesis
`IsoperimetricEqualityRegularity`, and `lem:abp-neumann` as `ABPNeumannSolvable`; Steps 3–5
are proved (`iso_smooth_rigidity`). -/
theorem isoperimetric_rigidity (hN : ABPNeumannSolvable)
    (hR : IsoperimetricEqualityRegularity) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hpos : 0 < volume E) (hfin : volume E < ∞)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueBallUpToNull (volume E).toReal E := by
  have hper : HasFinitePerimeter E := by
    change perimeterN E < ∞
    rw [perimeterN_eq_perimeter E hE, heq]
    exact ENNReal.ofReal_lt_top
  obtain ⟨Ω, hΩo, hΩb, hΩs, hΩE⟩ := hR E hE hpos hfin hper heq
  have hvol : volume Ω = volume E := measure_congr hΩE
  have hperΩ : perimeter Ω = perimeter E := perimeter_congr_ae hΩE
  obtain ⟨p, r, hr, hΩ⟩ := iso_smooth_rigidity hN hΩo hΩb hΩs (hvol ▸ hpos)
    (by rw [hperΩ, hvol, heq])
  subst hΩ
  refine ⟨hE, p, r, hr, by rw [hvol, ENNReal.ofReal_toReal hfin.ne], ?_⟩
  rw [measure_symmDiff_eq_zero_iff]
  exact hΩE.symm

/-- Blueprint `thm:isoperimetric-rigidity`, converse: a set agreeing almost everywhere with a
ball of volume `V` has volume `V > 0` and perimeter `(36π)^{1/3} V^{2/3}` (`lem:ball-perimeter`). -/
theorem perimeter_eq_of_isLebesgueBallUpToNull {V : ℝ} {E : Set AmbientSpace}
    (h : IsLebesgueBallUpToNull V E) :
    0 < V ∧ volume E = ENNReal.ofReal V ∧
      perimeter E = ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * V ^ (2 / (3 : ℝ))) := by
  obtain ⟨-, p, r, hr, hvol, hnull⟩ := h
  have hEB : E =ᵐ[volume] ball p r := (measure_symmDiff_eq_zero_iff).mp hnull
  have hV : 0 < V := by
    have : 0 < volume (ball p r) := measure_ball_pos volume p hr
    rw [hvol] at this
    exact ENNReal.ofReal_pos.mp this
  refine ⟨hV, (measure_congr hEB).trans hvol, ?_⟩
  rw [perimeter_congr_ae hEB, perimeter_ball p hr, ← ballRadius_eq_of_volume_ball hr hvol,
    ballPerimeter_radius_eq_rpow hV]

/-- Blueprint `thm:isoperimetric-rigidity` as an equivalence, for `0 < |E| < ∞`. -/
theorem isoperimetric_rigidity_iff (hN : ABPNeumannSolvable)
    (hR : IsoperimetricEqualityRegularity) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hpos : 0 < volume E) (hfin : volume E < ∞) :
    perimeter E =
        ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ))) ↔
      IsLebesgueBallUpToNull (volume E).toReal E :=
  ⟨isoperimetric_rigidity hN hR hE hpos hfin,
    fun h => (perimeter_eq_of_isLebesgueBallUpToNull h).2.2⟩

/-- The form of `thm:isoperimetric-rigidity` used by `prop:classification`: a set of volume
`V > 0` with `Per(E) ≤ P_B(V)` is a ball of volume `V` up to a null set. -/
theorem isLebesgueBallUpToNull_of_perimeter_le_ballPerimeter (hN : ABPNeumannSolvable)
    (hR : IsoperimetricEqualityRegularity) {V : ℝ} (hV : 0 < V) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hvol : volume E = ENNReal.ofReal V)
    (hP : perimeter E ≤ ballPerimeter V) : IsLebesgueBallUpToNull V E := by
  have hreal : (volume E).toReal = V := by rw [hvol, ENNReal.toReal_ofReal hV.le]
  have hfin : volume E < ∞ := by rw [hvol]; exact ENNReal.ofReal_lt_top
  have hge := sharp_isoperimetric hN hE hfin
  rw [hreal, ← ballPerimeter_eq_rpow hV] at hge
  have h := isoperimetric_rigidity hN hR hE (by rw [hvol]; exact ENNReal.ofReal_pos.mpr hV) hfin
    (by rw [hreal, ← ballPerimeter_eq_rpow hV]; exact le_antisymm hP hge)
  rwa [hreal] at h

end LiquidDrop
