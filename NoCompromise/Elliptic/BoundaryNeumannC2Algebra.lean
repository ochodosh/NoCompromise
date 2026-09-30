module

public import NoCompromise.Elliptic.BoundaryC2

@[expose] public section

/-!
# Hölder control in the algebraic normal-derivative step

These lemmas concern pointwise contractions. The pointwise PDE must be supplied
separately; no weak-to-classical implication is hidden in the hypotheses.
-/

noncomputable section
open Metric Set InnerProductSpace
open scoped BigOperators
namespace LiquidDrop

/-- Subtracting two pointwise equations controls the difference of their normal
entries, including the error caused by changing coefficients. -/
theorem normal_entry_sub_le_of_contractions {lam cap HA B T F t f g : ℝ}
    (hlam : 0 < lam) (hHA : 0 ≤ HA) (ht : 0 ≤ t)
    {A A' D D' : Fin 3 → Fin 3 → ℝ}
    (hell : lam ≤ A (Fin.last 2) (Fin.last 2))
    (hcap : ∀ i j, |A i j| ≤ cap)
    (hcoef : ∀ i j, |A i j - A' i j| ≤ HA * t)
    (hbound : ∀ i j, |D' i j| ≤ B)
    (htan : ∀ i j, ¬ (i = Fin.last 2 ∧ j = Fin.last 2) →
      |D i j - D' i j| ≤ T * t)
    (hsource : |f - g| ≤ F * t)
    (heq : ∑ i, ∑ j, A i j * D i j = f)
    (heq' : ∑ i, ∑ j, A' i j * D' i j = g) :
    |D (Fin.last 2) (Fin.last 2) - D' (Fin.last 2) (Fin.last 2)| ≤
      ((F + 9 * HA * B + 8 * cap * T) / lam) * t := by
  have hsum : |∑ i, ∑ j, (A i j - A' i j) * D' i j| ≤ 9 * HA * B * t := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |(A i j - A' i j) * D' i j| := by
        exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, HA * t * B := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hcoef i j) (hbound i j) (abs_nonneg _) (mul_nonneg hHA ht)
      _ = 9 * HA * B * t := by simp; ring
  have hdiff : ∑ i, ∑ j, A i j * (D i j - D' i j) =
      f - g - ∑ i, ∑ j, (A i j - A' i j) * D' i j := by
    have hid (i j : Fin 3) : A i j * (D i j - D' i j) =
        A i j * D i j - A' i j * D' i j - (A i j - A' i j) * D' i j := by ring
    simp_rw [hid, Finset.sum_sub_distrib, heq, heq']
  have hf : |f - g - ∑ i, ∑ j, (A i j - A' i j) * D' i j| ≤
      F * t + 9 * HA * B * t :=
    (abs_sub _ _).trans (add_le_add hsource hsum)
  apply (abs_normal_entry_le hlam hell hcap htan hdiff).trans
  apply (div_le_div_of_nonneg_right (add_le_add hf le_rfl) hlam.le).trans_eq
  ring

/-- Uniform bounds and Hölder estimates for the normal entry follow from a
pointwise contraction and the corresponding estimates on the other eight entries.
The displayed constants depend only on the supplied numerical bounds. -/
theorem normal_entry_holder_of_contraction {E : Type*} [PseudoMetricSpace E]
    {U : Set E} {α lam cap HA T F : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hT : 0 ≤ T) (hF : 0 ≤ F)
    {A D : E → Fin 3 → Fin 3 → ℝ} {f : E → ℝ}
    (hell : ∀ x ∈ U, lam ≤ A x (Fin.last 2) (Fin.last 2))
    (hAb : ∀ x ∈ U, ∀ i j, |A x i j| ≤ cap)
    (hAh : ∀ x ∈ U, ∀ y ∈ U, ∀ i j, |A x i j - A y i j| ≤ HA * dist x y ^ α)
    (hDb : ∀ x ∈ U, ∀ i j, ¬ (i = Fin.last 2 ∧ j = Fin.last 2) → |D x i j| ≤ T)
    (hDh : ∀ x ∈ U, ∀ y ∈ U, ∀ i j, ¬ (i = Fin.last 2 ∧ j = Fin.last 2) →
      |D x i j - D y i j| ≤ T * dist x y ^ α)
    (hfb : ∀ x ∈ U, |f x| ≤ F)
    (hfh : ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ F * dist x y ^ α)
    (heq : ∀ x ∈ U, ∑ i, ∑ j, A x i j * D x i j = f x) :
    (∀ x ∈ U, |D x (Fin.last 2) (Fin.last 2)| ≤ (F + 8 * cap * T) / lam) ∧
    ∀ x ∈ U, ∀ y ∈ U,
      |D x (Fin.last 2) (Fin.last 2) - D y (Fin.last 2) (Fin.last 2)| ≤
        ((F + 9 * HA * (T + (F + 8 * cap * T) / lam) + 8 * cap * T) / lam) *
          dist x y ^ α := by
  have hb : ∀ x ∈ U, |D x (Fin.last 2) (Fin.last 2)| ≤ (F + 8 * cap * T) / lam := by
    intro x hx
    exact (abs_normal_entry_le hlam (hell x hx) (hAb x hx) (hDb x hx) (heq x hx)).trans
      (div_le_div_of_nonneg_right (add_le_add (hfb x hx) le_rfl) hlam.le)
  refine ⟨hb, ?_⟩
  intro x hx y hy
  apply normal_entry_sub_le_of_contractions hlam hHA
    (Real.rpow_nonneg dist_nonneg _) (hell x hx) (hAb x hx) (hAh x hx y hy)
    _ (hDh x hx y hy) (hfh x hx y hy) (heq x hx) (heq y hy)
  intro i j
  by_cases hn : i = Fin.last 2 ∧ j = Fin.last 2
  · rcases hn with ⟨rfl, rfl⟩
    exact (hb y hy).trans (le_add_of_nonneg_left hT)
  · exact (hDb y hy i j hn).trans (le_add_of_nonneg_right (by positivity))

end LiquidDrop
