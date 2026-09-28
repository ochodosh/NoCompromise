import NoCompromise.Elliptic.CampanatoGrowthScalar

/-! Uniform power iteration for centered oscillations, with a separately
controlled noncentered energy error. -/

noncomputable section
open Set Filter Topology
open scoped Topology
namespace LiquidDrop

lemma campanato_fixed_power_growth_uniform {d b R C D M : ℝ}
    (hb : 0 ≤ b) (hbd : b < d) (hR : 0 < R)
    (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Φ : ℝ → ℝ,
      (∀ r ∈ Ioc 0 R, 0 ≤ Φ r) → MonotoneOn Φ (Ioc 0 R) →
      (∀ r ∈ Ioc 0 R, Φ r ≤ M) →
      (∀ r ∈ Ioc 0 R, ∀ θ : ℝ, 0 < θ → θ < 1 →
        Φ (θ * r) ≤ C * θ ^ d * Φ r + D * r ^ b) →
      ∀ r ∈ Ioc 0 R, Φ r ≤ K * r ^ b := by
  obtain ⟨θ, hθ, hθ1, hθpow⟩ := campanato_exists_small_power
    (sub_pos.mpr hbd) zero_lt_one (by norm_num : (0 : ℝ) < 1 / 2) (C := C)
  have hθb : 0 < θ ^ b := Real.rpow_pos_of_pos hθ b
  have hdec : C * θ ^ d ≤ (1 / 2 : ℝ) * θ ^ b := by
    have ht := mul_le_mul_of_nonneg_right hθpow.le hθb.le
    have heq : θ ^ (d - b) * θ ^ b = θ ^ d := by
      rw [← Real.rpow_add hθ]
      congr 1
      ring
    simpa only [mul_assoc, heq] using ht
  have hRb : 0 < R ^ b := Real.rpow_pos_of_pos hR b
  let L := max (M / R ^ b) (2 * D / θ ^ b)
  have hL : 0 ≤ L := (div_nonneg hM hRb.le).trans (le_max_left _ _)
  refine ⟨L / θ ^ b, div_nonneg hL hθb.le, ?_⟩
  intro Φ hnonneg hmono hbound hrec
  have hinit : Φ R ≤ L * R ^ b :=
    (hbound R ⟨hR, le_rfl⟩).trans ((div_le_iff₀ hRb).mp (le_max_left _ _))
  have hforce : D ≤ (1 / 2 : ℝ) * θ ^ b * L := by
    have hh : 2 * D ≤ L * θ ^ b := (div_le_iff₀ hθb).mp (le_max_right _ _)
    nlinarith only [hh]
  apply campanato_bound_all_radii hθ hθ1 hR hb hL hmono
  apply campanato_geometric_bound hθ hθ1 hR hinit hforce
  intro r hr
  exact (hrec r hr θ hθ hθ1).trans (add_le_add
    (mul_le_mul_of_nonneg_right hdec (hnonneg r hr)) le_rfl)

/-- A subcritical power bound for the true gradient energy upgrades the
centered oscillation exponent. All constants are uniform over both functions. -/
theorem campanato_oscillation_growth_from_energy {n a β R C D E M : ℝ}
    (hσ : 0 ≤ β + 2 * a) (hβn : β ≤ n) (hgap : β + 2 * a < n + 2)
    (hR : 0 < R) (hR1 : R ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Φ Ψ : ℝ → ℝ,
      (∀ r ∈ Ioc 0 R, 0 ≤ Φ r) → MonotoneOn Φ (Ioc 0 R) →
      (∀ r ∈ Ioc 0 R, Φ r ≤ M) →
      (∀ r ∈ Ioc 0 R, Ψ r ≤ E * r ^ β) →
      (∀ r ∈ Ioc 0 R, ∀ θ : ℝ, 0 < θ → θ < 1 →
        Φ (θ * r) ≤ C * θ ^ (n + 2) * Φ r +
          C * r ^ (2 * a) * Ψ r + D * r ^ (n + 2 * a)) →
      ∀ r ∈ Ioc 0 R, Φ r ≤ K * r ^ (β + 2 * a) := by
  obtain ⟨K, hK, hb⟩ := campanato_fixed_power_growth_uniform hσ hgap hR hM (D := C * E + D)
  refine ⟨K, hK, ?_⟩
  intro Φ Ψ hnonneg hmono hbound henergy hrec
  apply hb Φ hnonneg hmono hbound
  intro r hr θ hθ hθ1
  have hp : C * r ^ (2 * a) * Ψ r ≤ C * E * r ^ (β + 2 * a) := by
    calc
      _ ≤ C * r ^ (2 * a) * (E * r ^ β) :=
        mul_le_mul_of_nonneg_left (henergy r hr)
          (mul_nonneg hC (Real.rpow_nonneg hr.1.le _))
      _ = _ := by rw [Real.rpow_add hr.1]; ring
  have hq : D * r ^ (n + 2 * a) ≤ D * r ^ (β + 2 * a) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hr.1 (hr.2.trans hR1) (by linarith)) hD
  have hh := hrec r hr θ hθ hθ1
  nlinarith only [hh, hp, hq]

end LiquidDrop
