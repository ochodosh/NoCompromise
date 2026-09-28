import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The geometric recurrence in excess iteration

The recurrence coefficient is an arbitrary real number. Replacing it by its
nonnegative part gives a uniform constant that is independent of the contraction
factor, initial scale, error parameter, and sequence.
-/

namespace LiquidDrop

/-- A precise bound for the recurrence, valid even for a negative forcing coefficient. -/
theorem geometric_recurrence_bound {C θ ω r : ℝ} {E : ℕ → ℝ}
    (hθ : 0 ≤ θ) (hω : 0 ≤ ω) (hr : 0 ≤ r) (hE : 0 ≤ E 0)
    (hrec : ∀ j, E (j + 1) ≤ θ / 2 * E j + C * θ * ω * (θ ^ j * r))
    (j : ℕ) : E j ≤ θ ^ j * (E 0 + 2 * max C 0 * ω * r) := by
  have hD : 0 ≤ max C 0 := le_max_right _ _
  induction j with
  | zero =>
    simp only [pow_zero, one_mul]
    exact le_add_of_nonneg_right (by positivity)
  | succ j hj =>
    calc
      E (j + 1) ≤ θ / 2 * E j + C * θ * ω * (θ ^ j * r) := hrec j
      _ ≤ θ / 2 * (θ ^ j * (E 0 + 2 * max C 0 * ω * r)) +
          max C 0 * θ * ω * (θ ^ j * r) := by
        apply add_le_add (mul_le_mul_of_nonneg_left hj (by positivity))
        gcongr
        exact le_max_left _ _
      _ = θ ^ (j + 1) * (E 0 / 2 + 2 * max C 0 * ω * r) := by
        rw [pow_succ]
        ring
      _ ≤ θ ^ (j + 1) * (E 0 + 2 * max C 0 * ω * r) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hθ _)
        linarith

/-- Blueprint `lem:geometric-recurrence`. The positive constant depends only on `C`.
The hypotheses on the sequence are the blueprint's nonnegativity hypotheses;
the proof in fact only needs nonnegativity of its initial value. -/
theorem geometric_recurrence (C : ℝ) :
    ∃ C' > 0, ∀ (θ ω r : ℝ) (E : ℕ → ℝ), 0 < θ → θ < 1 →
      0 ≤ ω → 0 ≤ r → (∀ j, 0 ≤ E j) →
      (∀ j, E (j + 1) ≤ θ / 2 * E j + C * θ * ω * (θ ^ j * r)) →
      ∀ j, E j ≤ C' * θ ^ j * (E 0 + ω * r) := by
  refine ⟨1 + 2 * max C 0, by positivity, fun θ ω r E hθ _ hω hr hE hrec j => ?_⟩
  have ht := geometric_recurrence_bound hθ.le hω hr (hE 0) hrec j
  have hD : 0 ≤ 2 * max C 0 := by positivity
  have he : E 0 + 2 * max C 0 * ω * r ≤
      (1 + 2 * max C 0) * (E 0 + ω * r) := by
    nlinarith [mul_nonneg hD (hE 0), mul_nonneg hω hr]
  exact ht.trans ((mul_le_mul_of_nonneg_left he (pow_nonneg hθ.le j)).trans_eq (by ring))

/-- The excess plus its scale error obeys the same geometric bound. -/
theorem geometric_recurrence_with_error (C : ℝ) :
    ∃ C' > 0, ∀ (θ ω r : ℝ) (E : ℕ → ℝ), 0 < θ → θ < 1 →
      0 ≤ ω → 0 ≤ r → (∀ j, 0 ≤ E j) →
      (∀ j, E (j + 1) ≤ θ / 2 * E j + C * θ * ω * (θ ^ j * r)) →
      ∀ j, E j + ω * (θ ^ j * r) ≤ C' * θ ^ j * (E 0 + ω * r) := by
  obtain ⟨C', hC', hb⟩ := geometric_recurrence C
  refine ⟨C' + 1, by positivity, fun θ ω r E hθ hθ' hω hr hE hrec j => ?_⟩
  have ht := hb θ ω r E hθ hθ' hω hr hE hrec j
  have he : ω * (θ ^ j * r) ≤ θ ^ j * (E 0 + ω * r) := by
    nlinarith [mul_nonneg (pow_nonneg hθ.le j) (hE 0)]
  calc
    _ ≤ C' * θ ^ j * (E 0 + ω * r) + θ ^ j * (E 0 + ω * r) := add_le_add ht he
    _ = _ := by ring

end LiquidDrop
