import NoCompromise.Elliptic.SchauderAbsorption

/-!
# Removing the lower derivative norm from the nested Schauder estimate

This is an algebraic absorption lemma. Its hypotheses are a polynomial
interpolation estimate, a fourth-power gap estimate, and a finite outer bound.
The analytic applications below establish each of these hypotheses separately.
-/

noncomputable section
open Set
namespace LiquidDrop

/-- Polynomial interpolation absorbs the actual C¹,α norm in the nested estimate.
The output constant is chosen before the norm functions and the data sizes. -/
theorem nondiv_schauder_absorb {p : ℕ} {K P : ℝ} (hK : 1 ≤ K) (hP : 0 < P) :
    ∃ C > 0, ∀ (X Y : ℝ → ℝ) (Z F : ℝ), 0 ≤ Z → 0 ≤ F →
      BddAbove (X '' Icc (1 / 2 : ℝ) (3 / 4)) →
      (∀ r ∈ Icc (1 / 2 : ℝ) (3 / 4), ∀ s ∈ Icc (1 / 2 : ℝ) (3 / 4), r < s →
        X r ≤ K * ((s - r)⁻¹) ^ 4 * (Y s + F)) →
      (∀ s ∈ Icc (1 / 2 : ℝ) (3 / 4), ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Y s ≤ ε * X s + P * (ε⁻¹) ^ p * Z) →
      X (1 / 2) ≤ C * (Z + F) := by
  let q : ℕ := 4 * (p + 1)
  let θ : ℝ := (2 * (2 : ℝ) ^ q)⁻¹
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := by
    apply (inv_le_one₀ (by positivity : 0 < 2 * (2 : ℝ) ^ q)).mpr
    have ht : 1 ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
    linarith
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let J : ℝ := K * P * (K / θ) ^ p + K
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨2 * J * (8 : ℝ) ^ q, by positivity, ?_⟩
  intro X Y Z F hZ hF hb hn hi
  apply schauder_absorption hJ.le (add_nonneg hZ hF) hb
  intro r hr s hs hrs
  let t : ℝ := (s - r)⁻¹
  have hd : 0 < s - r := sub_pos.mpr hrs
  have hd1 : s - r ≤ 1 := by linarith [hr.1, hs.2]
  have ht0 : 0 < t := inv_pos.mpr hd
  have ht1 : 1 ≤ t := (one_le_inv₀ hd).mpr hd1
  let ε : ℝ := θ / (K * t ^ 4)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    apply (div_le_one (by positivity : 0 < K * t ^ 4)).mpr
    have hp : 1 ≤ t ^ 4 := one_le_pow₀ ht1
    exact hθ1.trans (one_le_mul_of_one_le_of_one_le hK hp)
  have hcoef : K * t ^ 4 * ε = θ := by
    dsimp [ε]
    field_simp
  have hinv : ε⁻¹ = (K / θ) * t ^ 4 := by
    dsimp [ε]
    rw [inv_div]
    ring
  have hcost : K * t ^ 4 * P * (ε⁻¹) ^ p = K * P * (K / θ) ^ p * t ^ q := by
    rw [hinv, mul_pow]
    dsimp [q]
    rw [pow_mul, pow_succ]
    ring
  have hp : t ^ 4 ≤ t ^ q := by
    apply pow_le_pow_right₀ ht1
    dsimp [q]
    omega
  calc
    X r ≤ K * t ^ 4 * (Y s + F) := hn r hr s hs hrs
    _ ≤ K * t ^ 4 * (ε * X s + P * (ε⁻¹) ^ p * Z + F) :=
      mul_le_mul_of_nonneg_left (add_le_add (hi s hs ε hε hε1) le_rfl) (by positivity)
    _ = θ * X s + (K * P * (K / θ) ^ p * t ^ q * Z + K * t ^ 4 * F) := by
      calc
        _ = (K * t ^ 4 * ε) * X s +
            (K * t ^ 4 * P * (ε⁻¹) ^ p) * Z + K * t ^ 4 * F := by ring
        _ = _ := by rw [hcoef, hcost]; ring
    _ ≤ θ * X s + (K * P * (K / θ) ^ p * t ^ q * Z + K * t ^ q * F) := by
      gcongr
    _ ≤ θ * X s + J * t ^ q * (Z + F) := by
      have h₁ : 0 ≤ K * t ^ q * Z := by positivity
      have h₂ : 0 ≤ K * P * (K / θ) ^ p * t ^ q * F := by positivity
      dsimp [J]
      nlinarith only [h₁, h₂]

end LiquidDrop
