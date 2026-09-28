import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! A quantitative nested-radius absorption argument. A finite outer bound is
used only to kill the residual geometric term; it does not enter the estimate. -/

noncomputable section
open Filter Set
open scoped Topology
namespace LiquidDrop

lemma schauder_absorb_sequence {q : ℕ} {a : ℕ → ℝ} {B C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ j, a j ≤ B)
    (hr : ∀ j, a j ≤ (2 * (2 : ℝ) ^ q)⁻¹ * a (j + 1) + C * ((2 : ℝ) ^ q) ^ j) :
    a 0 ≤ 2 * C := by
  let θ : ℝ := (2 * (2 : ℝ) ^ q)⁻¹
  have hpow : 0 < (2 : ℝ) ^ q := by positivity
  have hpow1 : 1 ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by
    dsimp [θ]
    apply (inv_lt_one₀ (by positivity : (0 : ℝ) < 2 * 2 ^ q)).mpr
    nlinarith only [hpow1]
  have hθpow : θ * (2 : ℝ) ^ q = 1 / 2 := by dsimp [θ]; field_simp
  have hi (j : ℕ) : a 0 ≤ θ ^ j * a j + 2 * C * (1 - (1 / 2 : ℝ) ^ j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hs := mul_le_mul_of_nonneg_left (hr j) (pow_nonneg hθ j)
      have he : θ ^ j * (C * ((2 : ℝ) ^ q) ^ j) = C * (1 / 2 : ℝ) ^ j := by
        rw [← hθpow, mul_pow]
        ring
      calc
        a 0 ≤ θ ^ j * a j + 2 * C * (1 - (1 / 2 : ℝ) ^ j) := ih
        _ ≤ θ ^ j * (θ * a (j + 1) + C * ((2 : ℝ) ^ q) ^ j) +
            2 * C * (1 - (1 / 2 : ℝ) ^ j) := add_le_add hs le_rfl
        _ = θ ^ (j + 1) * a (j + 1) + 2 * C * (1 - (1 / 2 : ℝ) ^ (j + 1)) := by
          rw [mul_add, he, pow_succ, pow_succ]
          ring
  have hj (j : ℕ) : a 0 ≤ θ ^ j * B + 2 * C := by
    apply (hi j).trans
    have ht := mul_le_mul_of_nonneg_left (hb j) (pow_nonneg hθ j)
    have hp := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j
    nlinarith only [ht, mul_nonneg hC hp]
  have hlim : Tendsto (fun j : ℕ => θ ^ j * B + 2 * C) atTop (𝓝 (2 * C)) := by
    simpa only [zero_mul, zero_add] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const B).add_const (2 * C)
  exact ge_of_tendsto hlim (Eventually.of_forall hj)

/-- Absorb an intermediate-radius term with a polynomial gap cost. Only a finite
outer bound is required; neither that bound nor X enters the resulting constant. -/
theorem schauder_absorption {q : ℕ} {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    {X : ℝ → ℝ} (hb : BddAbove (X '' Icc (1 / 2 : ℝ) (3 / 4)))
    (hr : ∀ r ∈ Icc (1 / 2 : ℝ) (3 / 4), ∀ s ∈ Icc (1 / 2 : ℝ) (3 / 4), r < s →
      X r ≤ (2 * (2 : ℝ) ^ q)⁻¹ * X s + K * ((s - r)⁻¹) ^ q * T) :
    X (1 / 2) ≤ 2 * K * (8 : ℝ) ^ q * T := by
  let r (j : ℕ) : ℝ := 3 / 4 - (1 / 4) * (1 / 2 : ℝ) ^ j
  have hm (j : ℕ) : r j ∈ Icc (1 / 2 : ℝ) (3 / 4) := by
    have hp : 0 ≤ (1 / 2 : ℝ) ^ j := pow_nonneg (by norm_num) j
    have hp1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [r]
    constructor <;> linarith
  have hgap (j : ℕ) : r (j + 1) - r j = (1 / 8) * (1 / 2 : ℝ) ^ j := by
    dsimp [r]
    rw [pow_succ]
    ring
  have hrlt (j : ℕ) : r j < r (j + 1) := by
    apply sub_pos.mp
    rw [hgap]
    positivity
  have hgapPow (j : ℕ) : ((r (j + 1) - r j)⁻¹) ^ q =
      (8 : ℝ) ^ q * ((2 : ℝ) ^ q) ^ j := by
    have he : (r (j + 1) - r j)⁻¹ = (8 : ℝ) * 2 ^ j := by
      rw [hgap, mul_inv_rev, ← inv_pow]
      norm_num
      ring
    rw [he, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm j q]
  obtain ⟨B, hB⟩ := hb
  have hbseq (j : ℕ) : X (r j) ≤ B := hB (mem_image_of_mem X (hm j))
  have hrec (j : ℕ) : X (r j) ≤ (2 * (2 : ℝ) ^ q)⁻¹ * X (r (j + 1)) +
      (K * 8 ^ q * T) * ((2 : ℝ) ^ q) ^ j := by
    have h := hr (r j) (hm j) (r (j + 1)) (hm (j + 1)) (hrlt j)
    rw [hgapPow] at h
    convert h using 1
    ring
  have h := schauder_absorb_sequence (by positivity : 0 ≤ K * (8 : ℝ) ^ q * T) hbseq hrec
  have hrzero : r 0 = 1 / 2 := by norm_num [r]
  rw [hrzero] at h
  convert h using 1
  ring

end LiquidDrop
