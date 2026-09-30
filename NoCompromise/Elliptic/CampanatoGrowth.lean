module

public import NoCompromise.Elliptic.CampanatoGrowthScalar
public import NoCompromise.Elliptic.CampanatoGrowthStep

@[expose] public section

/-!
# Subcritical gradient-energy growth

This is blueprint `lem:campanato-energy-growth` for the actual H¹ weak solution.
The constant is chosen before the coefficient, datum, function, center, and
radius. Only the stated positive ellipticity, coefficient norm, Hölder
seminorm, and total gradient-energy bounds enter its choice.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_small_ball_subset_unit {n : ℕ} {c : EuclideanSpace ℝ (Fin n)}
    (hc : c ∈ ball 0 (3 / 4 : ℝ)) {r : ℝ} (hr : r ≤ 1 / 8) :
    ball c r ⊆ ball 0 1 := by
  intro x hx
  have hc' : dist c 0 < 3 / 4 := hc
  have hx' : dist x c < r := hx
  have ht := dist_triangle x c 0
  change dist x 0 < 1
  linarith

lemma campanato_memLp_of_holder_on_unit {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {G : EuclideanSpace ℝ (Fin n) → F} {a H : ℝ} (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hG : ContinuousOn G (ball 0 1))
    (hholder : ∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1, ‖G x - G y‖ ≤ H * dist x y ^ a) :
    MemLp G 2 (volume.restrict (ball 0 1)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    ⟨by simpa using (isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)).measure_lt_top⟩
  apply MemLp.of_bound (hG.aestronglyMeasurable measurableSet_ball) (H + ‖G 0‖)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have h₀ : (0 : EuclideanSpace ℝ (Fin n)) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have ht := hholder x hx 0 h₀
  have hp : dist x 0 ^ a ≤ 1 := Real.rpow_le_one (dist_nonneg) (le_of_lt hx) ha
  have hmul := mul_le_mul_of_nonneg_left hp hH
  have hnorm := norm_le_insert' (G x) (G 0)
  linarith

/-- Full subcritical energy growth in dimensions two and three (also valid in
one dimension). The displayed dependence on the gradient is its squared L²
norm bounded by `M`; no extra derivative-integrability premise is imposed. -/
theorem campanato_energy_growth {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {a β lam cap HA HG M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hβn : β < n)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧
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
        ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
          ball c (2 * r) ⊆ ball 0 (3 / 4 : ℝ) →
          (∫ x in ball c r, ‖F x‖ ^ 2) ≤ K * r ^ β := by
  obtain ⟨C, hC, D, hD, hstep⟩ :=
    campanato_energy_recurrence_constants hn0 hn hlam hcap hHA hHG
  obtain ⟨K₀, hK₀, hscalar⟩ := campanato_subcritical_growth_uniform
    (show 0 < 2 * a by positivity) hβ hβn
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1) hC.le hD hM
  let K := max K₀ (M / (1 / 8 : ℝ) ^ β) + 1
  have hK : 0 < K := by
    have ht : K₀ ≤ max K₀ (M / (1 / 8 : ℝ) ^ β) := le_max_left _ _
    dsimp [K]
    linarith only [ht, hK₀]
  refine ⟨K, hK, ?_⟩
  intro A G F u hA hG hbA hell hHA' hHG' hu hw henergy c r hr hballs
  have hc : c ∈ ball 0 (3 / 4 : ℝ) := hballs (mem_ball_self (by positivity))
  have hc1 : c ∈ ball 0 1 := ball_subset_ball (by norm_num) hc
  have hGr := campanato_memLp_of_holder_on_unit ha.le hHG hG hHG'
  have hFr := hu.memLp_gradient
  have hi := (memLp_two_iff_integrable_sq_norm hFr.aestronglyMeasurable).mp hFr
  let Φ (s : ℝ) := ∫ x in ball c s, ‖F x‖ ^ 2
  have hnonneg : ∀ s ∈ Ioc 0 (1 / 8 : ℝ), 0 ≤ Φ s :=
    fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  have hbound : ∀ s ∈ Ioc 0 (1 / 8 : ℝ), Φ s ≤ M := by
    intro s hs
    exact (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall (campanato_small_ball_subset_unit hc hs.2))).trans henergy
  have hmono : MonotoneOn Φ (Ioc 0 (1 / 8 : ℝ)) := by
    intro s hs t ht hst
    have hit := hi.mono_measure
      (Measure.restrict_mono (campanato_small_ball_subset_unit hc ht.2) le_rfl)
    exact setIntegral_mono_set hit (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall (ball_subset_ball hst))
  have hrec : ∀ s ∈ Ioc 0 (1 / 8 : ℝ), ∀ θ : ℝ, 0 < θ → θ < 1 →
      Φ (θ * s) ≤ C * (θ ^ (n : ℝ) + s ^ (2 * a)) * Φ s +
        D * s ^ ((n : ℝ) + 2 * a) := by
    intro s hs θ hθ hθ1
    have hsub := campanato_small_ball_subset_unit hc hs.2
    have hμ := Measure.restrict_mono hsub (le_rfl (a := volume))
    have hBA : ∀ᵐ x ∂volume.restrict (ball c s), ‖A x‖ ≤ cap := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hbA x (hsub hx)
    have hoscA : ∀ᵐ x ∂volume.restrict (ball c s), ‖A x - A c‖ ≤ HA * s ^ a := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (hHA' x (hsub hx) c hc1).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (le_of_lt hx) ha.le) hHA)
    have hoscG : ∀ᵐ x ∂volume.restrict (ball c s), ‖G x - G c‖ ≤ HG * s ^ a := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (hHG' x (hsub hx) c hc1).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (le_of_lt hx) ha.le) hHG)
    exact hstep a c s hs.1 u F G A (hu.mono hsub) (hw.mono hsub)
      ((hA.mono hsub).aestronglyMeasurable measurableSet_ball) hBA (hGr.mono_measure hμ)
      (hell c hc1) (hbA c hc1) hoscA hoscG θ hθ hθ1
  by_cases hrsmall : r ≤ 1 / 8
  · have hb := hscalar Φ hnonneg hmono hbound hrec r ⟨hr, hrsmall⟩
    exact hb.trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
      (Real.rpow_nonneg hr.le β))
  · have hsub : ball c r ⊆ ball 0 1 :=
      (ball_subset_ball (by linarith : r ≤ 2 * r)).trans
        (hballs.trans (ball_subset_ball (by norm_num)))
    have hb : (∫ x in ball c r, ‖F x‖ ^ 2) ≤ M :=
      (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall hsub)).trans henergy
    have hp : (1 / 8 : ℝ) ^ β ≤ r ^ β :=
      Real.rpow_le_rpow (by norm_num) (le_of_not_ge hrsmall) hβ.le
    have hpos : 0 < (1 / 8 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
    calc
      _ ≤ M := hb
      _ = (M / (1 / 8 : ℝ) ^ β) * (1 / 8 : ℝ) ^ β :=
        (div_mul_cancel₀ M hpos.ne').symm
      _ ≤ (M / (1 / 8 : ℝ) ^ β) * r ^ β :=
        mul_le_mul_of_nonneg_left hp (div_nonneg hM hpos.le)
      _ ≤ K * r ^ β := mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))
          (Real.rpow_nonneg hr.le β)

end LiquidDrop
