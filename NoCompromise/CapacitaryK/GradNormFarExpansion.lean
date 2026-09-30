module

public import NoCompromise.CapacitaryK.BochnerScalar
public import NoCompromise.CapacitaryK.BochnerInvariants

@[expose] public section

/-!
# Far-field expansion of `Δ|∇U|`

For an exterior harmonic `U = C/r + Q/r⁵ + W` with `Q` smooth, harmonic and 2-homogeneous and
`∇W = O(r⁻⁵)`, `D²W = O(r⁻⁶)`: `Δ|∇U| = 2C/r⁴ + 18 Q/r⁸ + O(r⁻⁷)` far out
(Bochner identity, `bochner_invariants_far`, `bochner_scalar_perturbation`).
-/

noncomputable section
open Real Set Filter Topology

namespace LiquidDrop.CapacitaryK

theorem gradNorm_laplacian_far_expansion {U Q : E3 → ℝ} {C R M : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U {x | R < ‖x‖}) (hUh : ∀ x : E3, R < ‖x‖ → laplacianN U x = 0)
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hQl : ∀ x : E3, laplacianN Q x = 0)
    (hW : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5) x‖ ≤ M / ‖x‖ ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5)) x‖ ≤ M / ‖x‖ ^ 6) :
    ∃ R' M' : ℝ, 0 < R' ∧ ∀ x : E3, R' ≤ ‖x‖ →
      0 < gradNorm U x ∧
      |laplacianN (gradNorm U) x - 2 * C / ‖x‖ ^ 4 - 18 * Q x / ‖x‖ ^ 8| ≤ M' / ‖x‖ ^ 7 := by
  obtain ⟨R₁, K, B, hR₁, hK, hB, hinv⟩ := bochner_invariants_far hC hR hU hQ hQh hQl hW
  obtain ⟨R₂, hR₂, hbo⟩ := gradNorm_far_bochner hC hU hUh hQ hQh (fun x hx => (hW x hx).1)
  obtain ⟨R₃, K', hR₃, hsc⟩ := bochner_scalar_perturbation hC hB hK
  refine ⟨max R₁ (max R₂ R₃), K', lt_of_lt_of_le hR₁ (le_max_left _ _), fun x hx => ?_⟩
  have hx1 : R₁ ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hx2 : R₂ ≤ ‖x‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx3 : R₃ ≤ ‖x‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨hh, hN, hP, hS⟩ := hinv x hx1
  obtain ⟨hpos, hlap⟩ := hbo x hx2
  obtain ⟨_, hmain⟩ := hsc ‖x‖ (farQuadrupole Q x) (hessNormSq U x) (hessGradNormSq U x)
    (gradNorm U x ^ 2) hx3 hh hN hP hS
  rw [Real.sqrt_sq hpos.le] at hmain
  refine ⟨hpos, ?_⟩
  rw [hlap]
  have hn : ‖x‖ ≠ 0 := (lt_of_lt_of_le hR₁ hx1).ne'
  have hq : 18 * Q x / ‖x‖ ^ 8 = 18 * farQuadrupole Q x / ‖x‖ ^ 3 := by
    simp only [farQuadrupole]
    field_simp
  rw [hq]
  exact hmain

end LiquidDrop.CapacitaryK
