import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# Campanato iteration

The scalar recurrence is iterated on geometric radii and extended to every
radius by monotonicity. All signs and the starting-radius dependence are
explicit; no regularity estimate is assumed.
-/

noncomputable section
open Set
namespace LiquidDrop

lemma campanato_geometric_bound {Φ : ℝ → ℝ} {θ r₀ β C M : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hr₀ : 0 < r₀)
    (hinit : Φ r₀ ≤ M * r₀ ^ β) (hforce : C ≤ (1 / 2 : ℝ) * θ ^ β * M)
    (hrec : ∀ r ∈ Ioc 0 r₀,
      Φ (θ * r) ≤ (1 / 2 : ℝ) * θ ^ β * Φ r + C * r ^ β) :
    ∀ j : ℕ, Φ (θ ^ j * r₀) ≤ M * (θ ^ j * r₀) ^ β := by
  intro j
  induction j with
  | zero => simpa only [pow_zero, one_mul] using hinit
  | succ j hj =>
    have hr : 0 < θ ^ j * r₀ := mul_pos (pow_pos hθ j) hr₀
    have hrle : θ ^ j * r₀ ≤ r₀ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (pow_le_one₀ hθ.le hθ1.le) hr₀.le
    have heq : θ ^ (j + 1) * r₀ = θ * (θ ^ j * r₀) := by rw [pow_succ]; ring
    rw [heq]
    calc
      _ ≤ (1 / 2 : ℝ) * θ ^ β * Φ (θ ^ j * r₀) + C * (θ ^ j * r₀) ^ β :=
        hrec _ ⟨hr, hrle⟩
      _ ≤ (1 / 2 : ℝ) * θ ^ β * (M * (θ ^ j * r₀) ^ β) +
          ((1 / 2 : ℝ) * θ ^ β * M) * (θ ^ j * r₀) ^ β :=
        add_le_add (mul_le_mul_of_nonneg_left hj (by positivity))
          (mul_le_mul_of_nonneg_right hforce (Real.rpow_nonneg hr.le β))
      _ = M * (θ * (θ ^ j * r₀)) ^ β := by
        rw [Real.mul_rpow hθ.le hr.le]
        ring

lemma campanato_bound_all_radii {Φ : ℝ → ℝ} {θ r₀ β M : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hr₀ : 0 < r₀) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hmono : MonotoneOn Φ (Ioc 0 r₀))
    (hgeom : ∀ j : ℕ, Φ (θ ^ j * r₀) ≤ M * (θ ^ j * r₀) ^ β) :
    ∀ ρ ∈ Ioc 0 r₀, Φ ρ ≤ (M / θ ^ β) * ρ ^ β := by
  intro ρ hρ
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hρ.1 hr₀) ((div_le_one hr₀).mpr hρ.2) hθ hθ1
  have hρj : ρ ≤ θ ^ j * r₀ := (div_le_iff₀ hr₀).mp hjhi
  have hjρ : θ * (θ ^ j * r₀) ≤ ρ := by
    have h := (lt_div_iff₀ hr₀).mp hjlo
    rw [pow_succ] at h
    nlinarith only [h]
  have hr : 0 < θ ^ j * r₀ := mul_pos (pow_pos hθ j) hr₀
  have hrle : θ ^ j * r₀ ≤ r₀ := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (pow_le_one₀ hθ.le hθ1.le) hr₀.le
  have hθβ : 0 < θ ^ β := Real.rpow_pos_of_pos hθ β
  calc
    Φ ρ ≤ Φ (θ ^ j * r₀) := hmono hρ ⟨hr, hrle⟩ hρj
    _ ≤ M * (θ ^ j * r₀) ^ β := hgeom j
    _ = (M / θ ^ β) * (θ * (θ ^ j * r₀)) ^ β := by
      rw [Real.mul_rpow hθ.le hr.le]
      field_simp
    _ ≤ (M / θ ^ β) * ρ ^ β :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_pos hθ hr).le hjρ hβ)
        (div_nonneg hM hθβ.le)

/-- Blueprint `lem:campanato-iteration`, with a general nonnegative decay
exponent. The final constant depends explicitly on the initial value, starting
radius, contraction factor and forcing constant. -/
theorem campanato_iteration {Φ : ℝ → ℝ} {θ r₀ β C : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hr₀ : 0 < r₀) (hβ : 0 ≤ β)
    (hnonneg : ∀ r ∈ Ioc 0 r₀, 0 ≤ Φ r) (hmono : MonotoneOn Φ (Ioc 0 r₀))
    (hrec : ∀ r ∈ Ioc 0 r₀,
      Φ (θ * r) ≤ (1 / 2 : ℝ) * θ ^ β * Φ r + C * r ^ β) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ ρ ∈ Ioc 0 r₀, Φ ρ ≤ C' * ρ ^ β := by
  let M := max (Φ r₀ / r₀ ^ β) (2 * C / θ ^ β)
  have hrβ : 0 < r₀ ^ β := Real.rpow_pos_of_pos hr₀ β
  have hθβ : 0 < θ ^ β := Real.rpow_pos_of_pos hθ β
  have hM : 0 ≤ M := (div_nonneg (hnonneg _ ⟨hr₀, le_rfl⟩) hrβ.le).trans (le_max_left _ _)
  have hinit : Φ r₀ ≤ M * r₀ ^ β :=
    (div_le_iff₀ hrβ).mp (le_max_left _ _)
  have hforce : C ≤ (1 / 2 : ℝ) * θ ^ β * M := by
    have h : 2 * C ≤ M * θ ^ β := (div_le_iff₀ hθβ).mp (le_max_right _ _)
    nlinarith only [h]
  exact ⟨M / θ ^ β, div_nonneg hM hθβ.le,
    campanato_bound_all_radii hθ hθ1 hr₀ hβ hM hmono
      (campanato_geometric_bound hθ hθ1 hr₀ hinit hforce hrec)⟩

end LiquidDrop
