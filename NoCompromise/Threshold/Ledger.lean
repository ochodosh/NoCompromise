module

public import NoCompromise.Threshold.Algebra
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-! # Algebraic ledger

The seven `lem:ledger-*` items in blueprint Chapter 16. Identities are separated
from inequalities and equality cases so that later proofs can reuse each part.
-/

namespace LiquidDrop

/-- Blueprint `lem:ledger-six`: this identity holds for every real `V`. -/
theorem ledger_six (V : ℝ) : (V + 2) ^ 2 - 16 * (V - 2) = (V - 6) ^ 2 := by
  ring

/-- Blueprint `lem:ledger-oneball`. The identity does not require `0 ≤ δ`. -/
theorem ledger_oneball (V δ : ℝ) :
    V + 2 - (V + 5 - 3 * (1 + δ) ^ 2) * (1 + δ) =
      δ * (4 - V + 9 * δ + 3 * δ ^ 2) := by
  ring

/-- The derivative in blueprint `lem:ledger-Fprime`, including differentiability. -/
theorem ledger_F_hasDerivAt (p : ℝ) (hp : 1 < p) :
    HasDerivAt (fun p : ℝ => 3 * (p + 2) / ((p - 1) * (p ^ 3 + 3 * p ^ 2 + 6 * p + 5)))
      (-(9 * (p ^ 2 + p + 1) * (p ^ 2 + 3 * p + 1)) /
        ((p - 1) ^ 2 * (p ^ 3 + 3 * p ^ 2 + 6 * p + 5) ^ 2)) p := by
  have hp0 : 0 < p := by linarith
  have hpoly : 0 < p ^ 3 + 3 * p ^ 2 + 6 * p + 5 := by positivity
  have hden : (p - 1) * (p ^ 3 + 3 * p ^ 2 + 6 * p + 5) ≠ 0 :=
    mul_ne_zero (by linarith) (ne_of_gt hpoly)
  convert! (((hasDerivAt_id p).add_const 2).const_mul 3).div
    (((hasDerivAt_id p).sub_const 1).mul
      (((((hasDerivAt_id p).pow 3).add (((hasDerivAt_id p).pow 2).const_mul 3)).add
        ((hasDerivAt_id p).const_mul 6)).add_const 5)) hden using 1
  dsimp
  ring

theorem ledger_F_deriv_neg (p : ℝ) (hp : 1 < p) :
    deriv (fun p : ℝ => 3 * (p + 2) / ((p - 1) * (p ^ 3 + 3 * p ^ 2 + 6 * p + 5))) p < 0 := by
  rw [(ledger_F_hasDerivAt p hp).deriv]
  have hp0 : 0 < p := by linarith
  have hsub : 0 < p - 1 := by linarith
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos (by positivity)
  · positivity

/-- Rewrite the real power in `lem:ledger-cubic` as a polynomial in `√L`. -/
theorem rpow_three_halves (L : ℝ) (hL : 0 ≤ L) :
    L ^ ((3 : ℝ) / 2) = (Real.sqrt L) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num

/-- The exact factorization in blueprint `lem:ledger-cubic`. -/
theorem ledger_cubic_factorization (L x : ℝ) (hL : 0 < L) :
    2 * L ^ ((3 : ℝ) / 2) / 9 - (L * x - 3 * x ^ 3) =
      L ^ ((3 : ℝ) / 2) / 9 * (3 * x / Real.sqrt L - 1) ^ 2 *
        (3 * x / Real.sqrt L + 2) := by
  have hs : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL)
  have hsq : L = (Real.sqrt L) ^ 2 := (Real.sq_sqrt hL.le).symm
  rw [rpow_three_halves L hL.le]
  nth_rw 2 [hsq]
  field_simp
  ring

/-- The inequality in blueprint `lem:ledger-cubic`. -/
theorem ledger_cubic (L x : ℝ) (hL : 0 < L) (hx : 0 ≤ x) :
    L * x - 3 * x ^ 3 ≤ 2 * L ^ ((3 : ℝ) / 2) / 9 := by
  have h := ledger_cubic_factorization L x hL
  have hnonneg : 0 ≤ L ^ ((3 : ℝ) / 2) / 9 * (3 * x / Real.sqrt L - 1) ^ 2 *
      (3 * x / Real.sqrt L + 2) := by positivity
  linarith

/-- A reusable form of the identity in blueprint `lem:ledger-binding`. -/
theorem binding_factorization (a x : ℝ) (ha : 0 < a) (ha_cube : a ^ 3 = 5 / 2)
    (hx : 0 < x) :
    1 / x + x ^ 2 / 5 - 3 / (2 * a) = (x - a) ^ 2 * (x + 2 * a) / (2 * a ^ 3 * x) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [ha_cube]
  field_simp
  nlinarith [ha_cube]

theorem binding_nonneg (a x : ℝ) (ha : 0 < a) (ha_cube : a ^ 3 = 5 / 2)
    (hx : 0 < x) : 0 ≤ 1 / x + x ^ 2 / 5 - 3 / (2 * a) := by
  rw [binding_factorization a x ha ha_cube hx]
  positivity

theorem binding_eq_zero_iff (a x : ℝ) (ha : 0 < a) (ha_cube : a ^ 3 = 5 / 2)
    (hx : 0 < x) : 1 / x + x ^ 2 / 5 - 3 / (2 * a) = 0 ↔ x = a := by
  rw [binding_factorization a x ha ha_cube hx]
  have hsum : x + 2 * a ≠ 0 := by positivity
  have hden : 2 * a ^ 3 * x ≠ 0 := by positivity
  simp [div_eq_zero_iff, hden, hsum, sub_eq_zero]

/-- Blueprint `lem:ledger-binding`, with the specified cube root (no extra assumptions). -/
theorem ledger_binding (x : ℝ) (hx : 0 < x) :
    let a : ℝ := (5 / 2 : ℝ) ^ (1 / (3 : ℝ))
    (1 / x + x ^ 2 / 5 - 3 / (2 * a) = (x - a) ^ 2 * (x + 2 * a) / (2 * a ^ 3 * x)) ∧
      0 ≤ 1 / x + x ^ 2 / 5 - 3 / (2 * a) ∧
      (1 / x + x ^ 2 / 5 - 3 / (2 * a) = 0 ↔ x = a) := by
  dsimp only
  have ha : 0 < (5 / 2 : ℝ) ^ (1 / (3 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have ha_cube : ((5 / 2 : ℝ) ^ (1 / (3 : ℝ))) ^ 3 = 5 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5 / 2)]
    norm_num
  exact ⟨binding_factorization _ x ha ha_cube hx, binding_nonneg _ x ha ha_cube hx,
    binding_eq_zero_iff _ x ha ha_cube hx⟩

/-- Blueprint `lem:ledger-L5`. Its lower bound `0 < V` is not needed. -/
theorem ledger_L5 (V : ℝ) (hV : V ≤ 8) :
    ((q ^ 2)⁻¹ * (V + 10)) / 5 ≤ 18 / (5 * q ^ 2) ∧ 18 / (5 * q ^ 2) < q ^ 4 := by
  have hq := q_pos
  have hden : 0 < 5 * q ^ 2 := by positivity
  constructor
  · calc
      ((q ^ 2)⁻¹ * (V + 10)) / 5 = (V + 10) / (5 * q ^ 2) := by ring
      _ ≤ 18 / (5 * q ^ 2) := (div_le_div_iff_of_pos_right hden).2 (by linarith)
  · apply (div_lt_iff₀ hden).2
    have hcube_sq := congrArg (fun x : ℝ => x ^ 2) q_cube
    nlinarith [hcube_sq]

/-- The derivative in blueprint `lem:ledger-h`. -/
theorem ledger_h_hasDerivAt (V : ℝ) (hV : V ≠ 2) :
    HasDerivAt (fun V : ℝ => (V + 10) ^ 3 / (V - 2))
      (2 * (V + 10) ^ 2 * (V - 8) / (V - 2) ^ 2) V := by
  convert! (((hasDerivAt_id V).add_const 10).pow 3).div
    ((hasDerivAt_id V).sub_const 2) (sub_ne_zero.mpr hV) using 1
  dsimp
  ring

theorem ledger_h_deriv_nonpos (V : ℝ) (hV : V ∈ Set.Icc (6 : ℝ) 8) :
    deriv (fun V : ℝ => (V + 10) ^ 3 / (V - 2)) V ≤ 0 := by
  rw [(ledger_h_hasDerivAt V (by linarith [hV.1])).deriv]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hV.2])) (sq_nonneg _)

/-- The monotonicity asserted by blueprint `lem:ledger-h`. -/
theorem ledger_h_antitoneOn :
    AntitoneOn (fun V : ℝ => (V + 10) ^ 3 / (V - 2)) (Set.Icc 6 8) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 6 8)
  · intro V hV
    exact (ledger_h_hasDerivAt V (by linarith [hV.1])).continuousAt.continuousWithinAt
  · intro V hV
    have hmem := interior_subset hV
    exact (ledger_h_hasDerivAt V (by linarith [hmem.1])).differentiableAt.differentiableWithinAt
  · intro V hV
    exact ledger_h_deriv_nonpos V (interior_subset hV)

/-- The numerical bound in blueprint `lem:ledger-h`. -/
theorem ledger_h (V : ℝ) (hV : V ∈ Set.Icc (6 : ℝ) 8) :
    (V + 10) ^ 3 / (V - 2) ≤ 1024 ∧ (1024 : ℝ) < 1296 := by
  constructor
  · have h := ledger_h_antitoneOn (show (6 : ℝ) ∈ Set.Icc (6 : ℝ) 8 by norm_num) hV hV.1
    norm_num at h
    exact h
  · norm_num

end LiquidDrop
