module

public import NoCompromise.Elliptic.BoundaryC1
public import NoCompromise.Elliptic.BoundaryHolderSharp

@[expose] public section

/-!
# Ingredients for boundary `C^{2,α}` regularity (divergence form)

The algebraic step of the proof of `thm:boundary-C2a` (and of `thm:boundary-nondiv`
and the last step of `thm:boundary-neumann`) is formalized here: under uniform
ellipticity the normal diagonal entry `a₃₃` is bounded below by the ellipticity
constant, so the pointwise equation `∑ A_ij H_ij = f` solves for `H₃₃` in terms of
the remaining entries, with the expected bound. The analytic steps (tangential
difference quotients, absorption of a scalar datum into a normal field, passage to
the limit) are not yet formalized, so `thm:boundary-C2a` is not claimed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace intervalIntegral
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-! ## The algebraic step: solving for the normal second derivative -/

/-- Uniform ellipticity bounds every diagonal entry of `A` from below by `lam`.  In
particular `a₃₃ ≥ lam > 0`, which is what lets the equation be solved for `∂₃₃w`. -/
lemma elliptic_diagonal_entry_ge {n : ℕ} {lam : ℝ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hA : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) (i : Fin n) :
    lam ≤ inner ℝ (A (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single i (1 : ℝ)) := by
  have h := hA (EuclideanSpace.single i (1 : ℝ))
  rwa [PiLp.norm_single, norm_one, one_pow, mul_one] at h

/-- The eight entries of a `3 × 3` index set other than the normal-normal one. -/
lemma card_erase_normal_pair :
    (((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).erase
      (Fin.last 2, Fin.last 2)).card = 8 := by decide

/-- Splitting the full contraction `∑_{i,j} A_ij H_ij` into the normal-normal term and
the remaining eight terms. -/
lemma contraction_eq_normal_add_rest (A H : Fin 3 → Fin 3 → ℝ) :
    ∑ i, ∑ j, A i j * H i j =
      A (Fin.last 2) (Fin.last 2) * H (Fin.last 2) (Fin.last 2) +
        ∑ p ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).erase
          (Fin.last 2, Fin.last 2), A p.1 p.2 * H p.1 p.2 := by
  have h1 : ∑ i, ∑ j, A i j * H i j = ∑ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ
      (Finset.univ : Finset (Fin 3)), A p.1 p.2 * H p.1 p.2 := by
    exact (Finset.sum_product (Finset.univ : Finset (Fin 3)) (Finset.univ : Finset (Fin 3))
      (fun p : Fin 3 × Fin 3 => A p.1 p.2 * H p.1 p.2)).symm
  rw [h1]
  exact (Finset.add_sum_erase _ (fun p : Fin 3 × Fin 3 => A p.1 p.2 * H p.1 p.2)
    (a := (Fin.last 2, Fin.last 2)) (Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _⟩)).symm

/-- **Algebraic solution for the normal second derivative.**  If the symmetric datum `H`
(to be read as the second-derivative matrix of `w`) satisfies the pointwise equation
`∑_{i,j} A_ij H_ij = f` and the normal diagonal entry of `A` is bounded below by
`lam > 0`, then `H₃₃` is determined by `f` and the remaining entries. -/
theorem normal_entry_eq_of_contraction {lam f : ℝ} (hlam : 0 < lam)
    {A H : Fin 3 → Fin 3 → ℝ} (hell : lam ≤ A (Fin.last 2) (Fin.last 2))
    (heq : ∑ i, ∑ j, A i j * H i j = f) :
    H (Fin.last 2) (Fin.last 2) =
      (f - ∑ p ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).erase
          (Fin.last 2, Fin.last 2), A p.1 p.2 * H p.1 p.2)
        / A (Fin.last 2) (Fin.last 2) := by
  have hpos : 0 < A (Fin.last 2) (Fin.last 2) := lt_of_lt_of_le hlam hell
  rw [eq_div_iff hpos.ne', mul_comm]
  rw [contraction_eq_normal_add_rest A H] at heq
  linarith

/-- **Quantitative form of the algebraic step.**  With `A` bounded by `cap` and every
second derivative carrying at least one tangential index bounded by `M`, the normal
second derivative obeys `lam * |H₃₃| ≤ |f| + 8 cap M`. -/
theorem lam_mul_abs_normal_entry_le {lam cap M f : ℝ} (hlam : 0 < lam)
    {A H : Fin 3 → Fin 3 → ℝ} (hell : lam ≤ A (Fin.last 2) (Fin.last 2))
    (hcap : ∀ i j, |A i j| ≤ cap)
    (hM : ∀ i j, ¬ (i = Fin.last 2 ∧ j = Fin.last 2) → |H i j| ≤ M)
    (heq : ∑ i, ∑ j, A i j * H i j = f) :
    lam * |H (Fin.last 2) (Fin.last 2)| ≤ |f| + 8 * cap * M := by
  classical
  have hcap0 : 0 ≤ cap := le_trans (abs_nonneg _) (hcap 0 0)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 0 (by decide))
  set s := ((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).erase
    (Fin.last 2, Fin.last 2) with hs
  have hterm : ∀ p ∈ s, |A p.1 p.2 * H p.1 p.2| ≤ cap * M := by
    intro p hp
    have hne : p ≠ (Fin.last 2, Fin.last 2) := Finset.ne_of_mem_erase hp
    have hne' : ¬ (p.1 = Fin.last 2 ∧ p.2 = Fin.last 2) := by
      intro h
      exact hne (Prod.ext h.1 h.2)
    rw [abs_mul]
    exact mul_le_mul (hcap _ _) (hM _ _ hne') (abs_nonneg _) hcap0
  have hsum : |∑ p ∈ s, A p.1 p.2 * H p.1 p.2| ≤ 8 * (cap * M) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul s (fun p => |A p.1 p.2 * H p.1 p.2|) (cap * M) hterm
    have hcard : s.card = 8 := by rw [hs]; exact card_erase_normal_pair
    rw [hcard, nsmul_eq_mul] at this
    calc _ ≤ _ := this
      _ = 8 * (cap * M) := by norm_num
  have hsplit := contraction_eq_normal_add_rest A H
  rw [hsplit] at heq
  have hkey : A (Fin.last 2) (Fin.last 2) * H (Fin.last 2) (Fin.last 2)
      = f - ∑ p ∈ s, A p.1 p.2 * H p.1 p.2 := by rw [hs]; linarith
  have habs : |A (Fin.last 2) (Fin.last 2)| * |H (Fin.last 2) (Fin.last 2)|
      ≤ |f| + 8 * (cap * M) := by
    rw [← abs_mul, hkey]
    exact (abs_sub _ _).trans (add_le_add le_rfl hsum)
  have hpos : 0 < A (Fin.last 2) (Fin.last 2) := lt_of_lt_of_le hlam hell
  have hEA : |A (Fin.last 2) (Fin.last 2)| = A (Fin.last 2) (Fin.last 2) := abs_of_pos hpos
  rw [hEA] at habs
  have hmono : lam * |H (Fin.last 2) (Fin.last 2)|
      ≤ A (Fin.last 2) (Fin.last 2) * |H (Fin.last 2) (Fin.last 2)| :=
    mul_le_mul_of_nonneg_right hell (abs_nonneg _)
  calc lam * |H (Fin.last 2) (Fin.last 2)| ≤ _ := hmono
    _ ≤ |f| + 8 * (cap * M) := habs
    _ = |f| + 8 * cap * M := by ring

/-- Divided form of the previous estimate. -/
theorem abs_normal_entry_le {lam cap M f : ℝ} (hlam : 0 < lam)
    {A H : Fin 3 → Fin 3 → ℝ} (hell : lam ≤ A (Fin.last 2) (Fin.last 2))
    (hcap : ∀ i j, |A i j| ≤ cap)
    (hM : ∀ i j, ¬ (i = Fin.last 2 ∧ j = Fin.last 2) → |H i j| ≤ M)
    (heq : ∑ i, ∑ j, A i j * H i j = f) :
    |H (Fin.last 2) (Fin.last 2)| ≤ (|f| + 8 * cap * M) / lam :=
  (le_div_iff₀' hlam).mpr (lam_mul_abs_normal_entry_le hlam hell hcap hM heq)

end LiquidDrop
