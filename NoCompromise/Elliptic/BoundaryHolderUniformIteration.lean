module

public import NoCompromise.Elliptic.CampanatoHolderOscillation
public import NoCompromise.Elliptic.CampanatoHolderIteration

@[expose] public section

/-! Radius-independent oscillation iteration. Initial excess with the correct
power gives one constant for all interior balls, including balls approaching
the flat boundary. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_fixed_power_growth_uniform_radius {d b C D M : ℝ}
    (hb : 0 ≤ b) (hbd : b < d) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ Φ : ℝ → ℝ,
      (∀ r ∈ Ioc 0 R, 0 ≤ Φ r) → MonotoneOn Φ (Ioc 0 R) →
      Φ R ≤ M * R ^ b →
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
  let L := max M (2 * D / θ ^ b)
  have hL : 0 ≤ L := hM.trans (le_max_left _ _)
  refine ⟨L / θ ^ b, div_nonneg hL hθb.le, ?_⟩
  intro R hR Φ hnonneg hmono hbound hrec
  have hinit : Φ R ≤ L * R ^ b := hbound.trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hR.le b))
  have hforce : D ≤ (1 / 2 : ℝ) * θ ^ b * L := by
    have hh : 2 * D ≤ L * θ ^ b := (div_le_iff₀ hθb).mp (le_max_right _ _)
    nlinarith only [hh]
  apply campanato_bound_all_radii hθ hθ1 hR hb hL hmono
  apply campanato_geometric_bound hθ hθ1 hR hinit hforce
  intro r hr
  exact (hrec r hr θ hθ hθ1).trans (add_le_add
    (mul_le_mul_of_nonneg_right hdec (hnonneg r hr)) le_rfl)

/-- Genuine weak equations and an already proved cubic energy bound propagate
an initially sharp excess bound with a constant independent of the ball radius. -/
theorem boundary_interior_oscillation_uniform_radius {a lam cap HA HG M E : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : EuclideanSpace ℝ (Fin 3)) (R : ℝ), 0 < R →
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        ContinuousOn A (ball c R) → ContinuousOn G (ball c R) →
        (∀ x ∈ ball c R, ‖A x‖ ≤ cap) →
        (∀ x ∈ ball c R, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ ball c R, ∀ y ∈ ball c R,
          ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ ball c R, ∀ y ∈ ball c R,
          ‖G x - G y‖ ≤ HG * dist x y ^ a) →
        HasH1GradientOn u F (ball c R) → IsWeakDivergenceEquationOn A F G (ball c R) →
        MemLp G 2 (volume.restrict (ball c R)) →
        (∀ r ∈ Ioc 0 R, (∫ x in ball c r, ‖F x‖ ^ 2) ≤ E * r ^ (3 : ℝ)) →
        (∫ x in ball c R, ‖F x - ⨍ y in ball c R, F y‖ ^ 2) ≤ M * R ^ (3 + 2 * a) →
        ∀ r ∈ Ioc 0 R,
          (∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2) ≤ K * r ^ (3 + 2 * a) := by
  obtain ⟨C, hC, D, _, hstep⟩ := campanato_oscillation_recurrence_constants
    (by norm_num : 0 < 3) (by norm_num : 3 < 4) hlam hcap hHA hHG
  obtain ⟨K, hK, hscalar⟩ := boundary_fixed_power_growth_uniform_radius
    (show 0 ≤ 3 + 2 * a by positivity) (show 3 + 2 * a < 5 by linarith) hM
    (C := C) (D := C * E + D)
  refine ⟨K, hK, ?_⟩
  intro c R hR u F G A hA _ hbA hell hAh hGh hu hw hmG henergy hinit
  let Φ (r : ℝ) := ∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2
  refine hscalar R hR Φ (fun _ _ => integral_nonneg fun _ => sq_nonneg _) ?_ hinit ?_
  · intro s hs t ht hst
    exact campanato_oscillation_mono_radius
      (hu.memLp_gradient.mono_measure (Measure.restrict_mono (ball_subset_ball ht.2) le_rfl)) hst
  · intro r hr θ hθ hθ1
    have hsub := ball_subset_ball hr.2 (x := c)
    have hc : c ∈ ball c R := mem_ball_self hR
    have hμ := Measure.restrict_mono hsub (le_rfl (a := volume))
    have hBA : ∀ᵐ x ∂volume.restrict (ball c r), ‖A x‖ ≤ cap := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hbA x (hsub hx)
    have hoscA : ∀ᵐ x ∂volume.restrict (ball c r), ‖A x - A c‖ ≤ HA * r ^ a := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (hAh x (hsub hx) c hc).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (le_of_lt hx) ha.le) hHA)
    have hoscG : ∀ᵐ x ∂volume.restrict (ball c r), ‖G x - G c‖ ≤ HG * r ^ a := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (hGh x (hsub hx) c hc).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (le_of_lt hx) ha.le) hHG)
    have hh := hstep a c r hr.1 u F G A (hu.mono hsub) (hw.mono hsub)
      ((hA.mono hsub).aestronglyMeasurable measurableSet_ball) hBA
      (hmG.mono_measure hμ) (hell c hc) (hbA c hc) hoscA hoscG θ hθ hθ1
    have he := mul_le_mul_of_nonneg_left (henergy r hr)
      (mul_nonneg hC.le (Real.rpow_nonneg hr.1.le (2 * a)))
    have hp : C * r ^ (2 * a) * (E * r ^ (3 : ℝ)) = C * E * r ^ (3 + 2 * a) := by
      rw [Real.rpow_add hr.1]
      ring
    rw [hp] at he
    norm_num only [Nat.cast_ofNat, show (3 : ℝ) + 2 = 5 by norm_num] at hh
    dsimp only [Φ]
    nlinarith only [hh, he]

end LiquidDrop
