import NoCompromise.Binding.Splitting

namespace LiquidDrop

open scoped ENNReal

/-- Blueprint `prop:strict-binding`, quantitative form, modulo `thm:sharp-isoperimetric`. -/
theorem strict_binding_quantitative (hiso : SharpIsoperimetric) {V s : ℝ} (hV : 0 < V)
    (hVc : V < criticalVolume) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < (ballPerimeter V).toReal * splittingD s * ((criticalVolume - V) / 5) ∧
    (ballPerimeter V).toReal * splittingD s * ((criticalVolume - V) / 5) ≤
      (valueFunction (s * V)).toReal + (valueFunction ((1 - s) * V)).toReal -
        (valueFunction V).toReal := by
  have hp : 0 < (ballPerimeter V).toReal :=
    ENNReal.toReal_pos (ballPerimeter_pos hV).ne' (ballPerimeter_lt_top hV).ne
  have hd := splittingD_pos hs0 hs1
  have hgap : 0 < (criticalVolume - V) / 5 := by linarith
  refine ⟨mul_pos (mul_pos hp hd) hgap, ?_⟩
  have hfac : 0 ≤ (ballPerimeter V).toReal * splittingD s :=
    (mul_pos hp hd).le
  calc
    (ballPerimeter V).toReal * splittingD s * ((criticalVolume - V) / 5) =
        (ballPerimeter V).toReal * splittingD s * (criticalVolume / 5 - V / 5) :=
      by ring
    _ ≤ (ballPerimeter V).toReal * splittingD s * (splittingF s - V / 5) :=
      mul_le_mul_of_nonneg_left
        (by linarith [splittingF_ge hs0 hs1]) hfac
    _ ≤ _ := two_piece hiso hV hs0 hs1

/-- Blueprint `prop:strict-binding`, modulo `thm:sharp-isoperimetric`. -/
theorem strict_binding (hiso : SharpIsoperimetric) {V s : ℝ} (hV : 0 < V)
    (hVc : V < criticalVolume) (hs0 : 0 < s) (hs1 : s < 1) :
    valueFunction V < valueFunction (s * V) + valueFunction ((1 - s) * V) := by
  have hq := strict_binding_quantitative hiso hV hVc hs0 hs1
  have hr : (valueFunction V).toReal <
      (valueFunction (s * V)).toReal + (valueFunction ((1 - s) * V)).toReal := by
    linarith [hq.1, hq.2]
  have hsV : valueFunction (s * V) < ∞ := valueFunction_lt_top (mul_pos hs0 hV)
  have htV : valueFunction ((1 - s) * V) < ∞ :=
    valueFunction_lt_top (mul_pos (by linarith) hV)
  apply (ENNReal.toReal_lt_toReal (valueFunction_lt_top hV).ne
    (ENNReal.add_lt_top.mpr ⟨hsV, htV⟩).ne).mp
  rw [ENNReal.toReal_add hsV.ne htV.ne]
  exact hr

end LiquidDrop
