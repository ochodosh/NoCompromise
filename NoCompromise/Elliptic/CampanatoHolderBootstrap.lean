module

public import NoCompromise.Elliptic.CampanatoHolderStep
public import NoCompromise.Elliptic.CampanatoHolderPowers

@[expose] public section

/-! The two genuine elliptic bootstrap steps: subcritical energy growth first
produces a bounded continuous weak gradient, and the bounded gradient then yields
the full coefficient Hölder exponent. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_inner_ball_subset {n : ℕ} {c : EuclideanSpace ℝ (Fin n)}
    {s t r : ℝ} (hc : c ∈ ball 0 s) (hr : r + s ≤ t) : ball c r ⊆ ball 0 t := by
  intro x hx
  have ht := dist_triangle x c 0
  have hc' : dist c 0 < s := hc
  have hx' : dist x c < r := hx
  change dist x 0 < t
  linarith

/-- The first bootstrap gives a bounded Hölder representative of the original
weak gradient on B_(2/3), using only the actual H¹ equation and original energy. -/
theorem campanato_gradient_subcritical_holder {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {a lam cap HA HG M : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ),
        ContinuousOn A (ball 0 1) → ContinuousOn G (ball 0 1) →
        (∀ x ∈ ball 0 1, ‖A x‖ ≤ cap) →
        (∀ x ∈ ball 0 1, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1, ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1, ‖G x - G y‖ ≤ HG * dist x y ^ a) →
        HasH1GradientOn u F (ball 0 1) → IsWeakDivergenceEquationOn A F G (ball 0 1) →
        (∫ x in ball 0 1, ‖F x‖ ^ 2) ≤ M →
        ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
          F =ᵐ[volume.restrict (ball 0 (2 / 3 : ℝ))] H ∧
          ContinuousOn H (ball 0 (2 / 3 : ℝ)) ∧
          (∀ x ∈ ball 0 (2 / 3 : ℝ), ‖H x‖ ≤ P) ∧
          ∀ x ∈ ball 0 (2 / 3 : ℝ), ∀ y ∈ ball 0 (2 / 3 : ℝ),
            ‖H x - H y‖ ≤ C * dist x y ^ (a / 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  obtain ⟨E, _, henergy⟩ := campanato_energy_growth hn0 hn ha
    (show 0 < (n : ℝ) - a by linarith) (by linarith : (n : ℝ) - a < n)
    hlam hcap hHA hHG hM
  obtain ⟨K, hK, hosc⟩ := campanato_oscillation_growth_on_small_balls hn0 hn ha
    (show 0 ≤ (n : ℝ) - a + 2 * a by linarith)
    (show (n : ℝ) - a ≤ n by linarith)
    (show (n : ℝ) - a + 2 * a < n + 2 by linarith)
    (by norm_num : (0 : ℝ) < 1 / 48) (by norm_num : (1 / 48 : ℝ) ≤ 1 / 8)
    hlam hcap hHA hHG hM (E := E)
  obtain ⟨C, P, hC, hP, hrep⟩ := campanato_holder_representative_of_power
    (F := EuclideanSpace ℝ (Fin n)) hn0 hK
    (show 0 < a / 2 by positivity) (by norm_num : (0 : ℝ) < 1 / 48) (M := M)
  refine ⟨C, P, hC, hP, ?_⟩
  intro A G F u hA hG hbA hell hHA' hHG' hu hw hM'
  apply hrep F (ball 0 (2 / 3 : ℝ)) measurableSet_ball hu.memLp_gradient hM'
  · intro x hx
    exact campanato_inner_ball_subset hx (by norm_num)
  · intro c hc r hr
    have hc' : c ∈ ball 0 (3 / 4 : ℝ) := ball_subset_ball (by norm_num) hc
    have he : ∀ s ∈ Ioc 0 (1 / 48 : ℝ),
        (∫ x in ball c s, ‖F x‖ ^ 2) ≤ E * s ^ ((n : ℝ) - a) := by
      intro s hs
      apply henergy A G F u hA hG hbA hell hHA' hHG' hu hw hM' c s hs.1
      exact campanato_inner_ball_subset hc (by linarith [hs.2])
    have hb := hosc A G F u hA hG hbA hell hHA' hHG' hu hw hM' c hc' he r hr
    convert hb using 2
    congr 1
    ring


lemma campanato_gradient_energy_of_ae_bounded {n : ℕ}
    {F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} {P : ℝ}
    (hF : MemLp F 2 (volume.restrict U))
    (he : F =ᵐ[volume.restrict U] H) (hP : 0 ≤ P)
    (hb : ∀ x ∈ U, ‖H x‖ ≤ P)
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hs : ball c r ⊆ U) :
    (∫ x in ball c r, ‖F x‖ ^ 2) ≤ P ^ 2 * volume.real (ball c r) := by
  let : IsFiniteMeasure (volume.restrict (ball c r)) :=
    ⟨by simpa using (isBounded_ball (x := c) (r := r)).measure_lt_top⟩
  have hf := hF.mono_measure (Measure.restrict_mono hs le_rfl)
  have he' := ae_restrict_of_ae_restrict_of_subset hs he
  have hnorm : ∀ᵐ x ∂volume.restrict (ball c r), ‖F x‖ ≤ P := by
    filter_upwards [he', ae_restrict_mem measurableSet_ball] with x hx hxr
    rw [hx]
    exact hb x (hs hxr)
  simpa only [Measure.real, Measure.restrict_apply_univ] using
    campanato_integral_sq_le_measure hf hP hnorm

/-- The full exponent is obtained from the first genuine bounded-gradient
bootstrap. No continuity or differentiability of the original representative is assumed. -/
theorem campanato_gradient_holder {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {a lam cap HA HG M : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ),
        ContinuousOn A (ball 0 1) → ContinuousOn G (ball 0 1) →
        (∀ x ∈ ball 0 1, ‖A x‖ ≤ cap) →
        (∀ x ∈ ball 0 1, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1, ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1, ‖G x - G y‖ ≤ HG * dist x y ^ a) →
        HasH1GradientOn u F (ball 0 1) → IsWeakDivergenceEquationOn A F G (ball 0 1) →
        (∫ x in ball 0 1, ‖F x‖ ^ 2) ≤ M →
        ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
          F =ᵐ[volume.restrict (ball 0 (3 / 5 : ℝ))] H ∧
          ContinuousOn H (ball 0 (3 / 5 : ℝ)) ∧
          (∀ x ∈ ball 0 (3 / 5 : ℝ), ‖H x‖ ≤ P) ∧
          ∀ x ∈ ball 0 (3 / 5 : ℝ), ∀ y ∈ ball 0 (3 / 5 : ℝ),
            ‖H x - H y‖ ≤ C * dist x y ^ a := by
  obtain ⟨_, P₀, _, hP₀, hfirst⟩ :=
    campanato_gradient_subcritical_holder hn0 hn ha ha1 hlam hcap hHA hHG hM
  let E := P₀ ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  obtain ⟨K, hK, hosc⟩ := campanato_oscillation_growth_on_small_balls hn0 hn ha
    (show 0 ≤ (n : ℝ) + 2 * a by positivity) (le_rfl (a := (n : ℝ)))
    (show (n : ℝ) + 2 * a < n + 2 by linarith)
    (by norm_num : (0 : ℝ) < 1 / 48) (by norm_num : (1 / 48 : ℝ) ≤ 1 / 8)
    hlam hcap hHA hHG hM (E := E)
  obtain ⟨C, P, hC, hP, hrep⟩ := campanato_holder_representative_of_power
    (F := EuclideanSpace ℝ (Fin n)) hn0 hK ha
    (by norm_num : (0 : ℝ) < 1 / 48) (M := M)
  refine ⟨C, P, hC, hP, ?_⟩
  intro A G F u hA hG hbA hell hHA' hHG' hu hw hM'
  obtain ⟨H₀, he₀, _, hb₀, _⟩ := hfirst A G F u hA hG hbA hell hHA' hHG' hu hw hM'
  apply hrep F (ball 0 (3 / 5 : ℝ)) measurableSet_ball hu.memLp_gradient hM'
  · intro x hx
    exact campanato_inner_ball_subset hx (by norm_num)
  · intro c hc r hr
    have hc' : c ∈ ball 0 (3 / 4 : ℝ) := ball_subset_ball (by norm_num) hc
    have he : ∀ s ∈ Ioc 0 (1 / 48 : ℝ),
        (∫ x in ball c s, ‖F x‖ ^ 2) ≤ E * s ^ (n : ℝ) := by
      intro s hs
      have hb := campanato_gradient_energy_of_ae_bounded (c := c) (r := s)
        (hu.memLp_gradient.mono_measure
          (Measure.restrict_mono (ball_subset_ball (by norm_num : (2 / 3 : ℝ) ≤ 1)) le_rfl))
        he₀ hP₀ hb₀ (campanato_inner_ball_subset hc (by linarith [hs.2]))
      rw [frozen_real_volume_ball hn0 c hs.1.le] at hb
      simpa only [E, Real.rpow_natCast, mul_assoc, mul_comm, mul_left_comm] using hb
    exact hosc A G F u hA hG hbA hell hHA' hHG' hu hw hM' c hc' he r hr

end LiquidDrop
