module

public import NoCompromise.Energy.Scaling
public import NoCompromise.Ball.Potential
public import NoCompromise.Isoperimetric.ABP

@[expose] public section

/-!
# The value function

Blueprint `def:value` and the parts of `lem:m-finite` that do not need the
sharp isoperimetric inequality. The competitors are Lebesgue-measurable sets
of exactly the prescribed volume, matching `IsLebesgueFixedVolumeMinimizer`.

The sharp isoperimetric inequality (`thm:sharp-isoperimetric`, Chapter 13) is
still open, so it is carried here as the explicit named predicate
`SharpIsoperimetric`; every statement that needs it takes it as a hypothesis.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LiquidDrop

/-- Blueprint `def:value`: `m(V) = inf {𝓔(E) : |E| = V}`. -/
def valueFunction (V : ℝ) : ℝ≥0∞ :=
  ⨅ (E : Set AmbientSpace) (_ : NullMeasurableSet E volume)
    (_ : volume E = ENNReal.ofReal V), energy E

lemma valueFunction_le {V : ℝ} {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hvol : volume E = ENNReal.ofReal V) :
    valueFunction V ≤ energy E :=
  iInf_le_of_le E (iInf_le_of_le hE (iInf_le_of_le hvol le_rfl))

lemma valueFunction_le_ball {V : ℝ} (hV : 0 < V) :
    valueFunction V ≤ energy (ballByVolume V) :=
  valueFunction_le measurableSet_ball.nullMeasurableSet (volume_ballByVolume hV)

/-- Half of blueprint `lem:m-finite`: the ball competitor makes `m` finite. -/
theorem valueFunction_lt_top {V : ℝ} (hV : 0 < V) : valueFunction V < ∞ := by
  refine (valueFunction_le_ball hV).trans_lt ?_
  rw [energy_ballByVolume hV]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ballPerimeter_lt_top hV)

/-- Blueprint `eq:sharp-isoperimetric` as a named hypothesis. `thm:sharp-isoperimetric`
is Chapter 13 and is not yet formalised; statements below that need it take this
predicate as an explicit argument. -/
def SharpIsoperimetric : Prop :=
  ∀ E : Set AmbientSpace, NullMeasurableSet E volume → volume E < ∞ →
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))
      ≤ perimeter E

/-- The isoperimetric inequality in the `P_B` form used in Chapter 18. -/
theorem SharpIsoperimetric.ballPerimeter_le (h : SharpIsoperimetric)
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hfin : volume E < ∞)
    (hpos : 0 < volume E) : ballPerimeter (volume E).toReal ≤ perimeter E := by
  rw [ballPerimeter_eq_rpow (ENNReal.toReal_pos hpos.ne' hfin.ne)]
  exact h E hE hfin

/-- The other half of blueprint `lem:m-finite`, modulo `thm:sharp-isoperimetric`. -/
theorem valueFunction_pos (h : SharpIsoperimetric) {V : ℝ} (hV : 0 < V) :
    0 < valueFunction V := by
  refine lt_of_lt_of_le (b := ballPerimeter V) (ballPerimeter_pos hV) ?_
  refine le_iInf fun E => le_iInf fun hE => le_iInf fun hvol => ?_
  have hfin : volume E < ∞ := by rw [hvol]; exact ENNReal.ofReal_lt_top
  have hpos : 0 < volume E := by rw [hvol]; exact ENNReal.ofReal_pos.mpr hV
  have hreal : (volume E).toReal = V := by rw [hvol, ENNReal.toReal_ofReal hV.le]
  have := h.ballPerimeter_le hE hfin hpos
  rw [hreal] at this
  exact this.trans (le_add_right le_rfl)

/-- Blueprint `lem:m-finite`, modulo `thm:sharp-isoperimetric`. -/
theorem valueFunction_pos_lt_top (h : SharpIsoperimetric) {V : ℝ} (hV : 0 < V) :
    0 < valueFunction V ∧ valueFunction V ≤ energy (ballByVolume V) ∧
      energy (ballByVolume V) < ∞ :=
  ⟨valueFunction_pos h hV, valueFunction_le_ball hV, by
    rw [energy_ballByVolume hV]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ballPerimeter_lt_top hV)⟩

end LiquidDrop
