import NoCompromise.Elliptic.CampanatoHolderLimits
import NoCompromise.Elliptic.CampanatoHolderLebesgue

/-! A genuine Hölder representative is constructed from mean-oscillation bounds.
The proof compares limits of actual ball averages, including at non-Lebesgue points. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_continuousOn_of_holder_bound {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] {U : Set X} {g : X → F} {C γ : ℝ}
    (hC : 0 ≤ C) (hγ : 0 < γ)
    (hb : ∀ x ∈ U, ∀ y ∈ U, ‖g x - g y‖ ≤ C * dist x y ^ γ) :
    ContinuousOn g U := by
  intro x hx
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, _, hsmall⟩ := campanato_exists_small_power hγ zero_lt_one hε (C := C)
  refine ⟨δ, hδ, ?_⟩
  intro y hy hxy
  rw [dist_eq_norm]
  exact (hb y hy x hx).trans_lt ((mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow dist_nonneg hxy.le hγ.le) hC).trans_lt hsmall)

/-- The norm of a ball average is bounded by the total squared L² norm and
its true Euclidean volume, uniformly in the center. -/
lemma campanato_norm_average_le_global_energy {n : ℕ} (hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin n) → F} {x : EuclideanSpace ℝ (Fin n)} {R M : ℝ}
    (hR : 0 < R) (hf : MemLp f 2 (volume.restrict (ball 0 1)))
    (hsub : ball x R ⊆ ball 0 1) (hM : (∫ y in ball 0 1, ‖f y‖ ^ 2) ≤ M) :
    ‖⨍ y in ball x R, f y‖ ≤
      Real.sqrt (M / (R ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))) := by
  let : IsFiniteMeasure (volume.restrict (ball x R)) :=
    ⟨by simpa using (isBounded_ball (x := x) (r := R)).measure_lt_top⟩
  have hm : volume (ball x R) ≠ 0 := (measure_ball_pos volume x hR).ne'
  have hj := campanato_norm_average_sq_le (by simpa using hm)
    (hf.mono_measure (Measure.restrict_mono hsub le_rfl))
  simp only [Measure.real, Measure.restrict_apply_univ] at hj
  have htot : (∫ y in ball x R, ‖f y‖ ^ 2) ≤ M :=
    (setIntegral_mono_set ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall hsub)).trans hM
  have hb : ‖⨍ y in ball x R, f y‖ ^ 2 ≤ M / volume.real (ball x R) := by
    exact hj.trans (by simpa only [div_eq_inv_mul, Measure.real] using
      mul_le_mul_of_nonneg_left htot (inv_nonneg.mpr ENNReal.toReal_nonneg))
  rw [frozen_real_volume_ball hn x hR.le] at hb
  simpa only [abs_norm] using Real.abs_le_sqrt hb

/-- Campanato's mean-oscillation criterion on an interior set. Both constants
are selected before the function and the set, and the representative is proved
almost everywhere equal to the input, rather than assumed to exist. -/
theorem campanato_holder_representative {n : ℕ} (hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {B γ R M : ℝ} (hB : 0 ≤ B) (hγ : 0 < γ) (hR : 0 < R) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (f : EuclideanSpace ℝ (Fin n) → F) (U : Set (EuclideanSpace ℝ (Fin n))),
        MeasurableSet U → MemLp f 2 (volume.restrict (ball 0 1)) →
        (∫ x in ball 0 1, ‖f x‖ ^ 2) ≤ M →
        (∀ x ∈ U, ball x R ⊆ ball 0 1) →
        (∀ x ∈ U, ∀ r ∈ Ioc 0 R,
          (∫ y in ball x r, ‖f y - ⨍ z in ball x r, f z‖ ^ 2) ≤
            (B * r ^ γ) ^ 2 * volume.real (ball x r)) →
        ∃ g : EuclideanSpace ℝ (Fin n) → F,
          f =ᵐ[volume.restrict U] g ∧ ContinuousOn g U ∧
          (∀ x ∈ U, ‖g x‖ ≤ P) ∧
          ∀ x ∈ U, ∀ y ∈ U, ‖g x - g y‖ ≤ C * dist x y ^ γ := by
  classical
  obtain ⟨L, hL, hlimit⟩ := campanato_average_limit_constant (F := F) hn hB hγ
  let J := Real.sqrt ((2 : ℝ) ^ n) * B
  let P := L * R ^ γ +
    Real.sqrt (M / (R ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)))
  let C₁ := 2 * L + 2 * J * (2 : ℝ) ^ γ
  let C₂ := 2 * P / (R / 2) ^ γ
  let C := max C₁ C₂ + 1
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC : 0 < C := by
    have hh := le_max_left C₁ C₂
    dsimp [C]
    linarith only [hh, hC₁]
  have hc₁ : C₁ ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hc₂ : C₂ ≤ C := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨C, P, hC, hP, ?_⟩
  intro f U hU hf he hballs hosc
  have hex (x) (hx : x ∈ U) := hlimit f x R hR
    (hf.mono_measure (Measure.restrict_mono (hballs x hx) le_rfl)) (hosc x hx)
  let g (x : EuclideanSpace ℝ (Fin n)) : F := if hx : x ∈ U then (hex x hx).choose else 0
  have hg (x) (hx : x ∈ U) :
      Tendsto (fun j : ℕ => ⨍ y in ball x ((1 / 2 : ℝ) ^ j * R), f y) atTop (𝓝 (g x)) ∧
      ∀ r ∈ Ioc 0 R, ‖(⨍ y in ball x r, f y) - g x‖ ≤ L * r ^ γ := by
    simpa only [g, dite_eq_left hx] using (hex x hx).choose_spec
  have hnorm (x) (hx : x ∈ U) : ‖g x‖ ≤ P := by
    have havg := campanato_norm_average_le_global_energy hn hR hf (hballs x hx) he
    have hclose := (hg x hx).2 R ⟨hR, le_rfl⟩
    have ht := norm_le_insert' (g x) (⨍ y in ball x R, f y)
    rw [norm_sub_rev] at ht
    dsimp [P]
    linarith only [ht, hclose, havg]
  have hholder : ∀ x ∈ U, ∀ y ∈ U, ‖g x - g y‖ ≤ C * dist x y ^ γ := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, norm_zero, dist_self, Real.zero_rpow hγ.ne', mul_zero, le_refl]
    have hd : 0 < dist x y := dist_pos.mpr hxy
    by_cases hnear : dist x y ≤ R / 2
    · have hrad : 2 * dist x y ∈ Ioc 0 R := ⟨by positivity, by linarith⟩
      have hrsmall : dist x y ∈ Ioc 0 R := ⟨hd, by linarith⟩
      have hsubx : ball x (dist x y) ⊆ ball x (2 * dist x y) :=
        ball_subset_ball (by linarith)
      have hsuby : ball y (dist x y) ⊆ ball x (2 * dist x y) := by
        intro z hz
        have hh := dist_triangle z y x
        rw [dist_comm y x] at hh
        change dist z x < 2 * dist x y
        have hz' : dist z y < dist x y := hz
        linarith
      have hf' := hf.mono_measure (Measure.restrict_mono
        ((ball_subset_ball hrad.2).trans (hballs x hx)) le_rfl)
      have hxavg := campanato_average_half_radius_bound hn hrad.1 hB
        (by simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hsubx)
        hf' (hosc x hx _ hrad)
      have hyavg := campanato_average_half_radius_bound hn hrad.1 hB
        (by simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hsuby)
        hf' (hosc x hx _ hrad)
      have hmx : ‖(⨍ z in ball x (dist x y), f z) -
          ⨍ z in ball x (2 * dist x y), f z‖ ≤ J * (2 * dist x y) ^ γ := by
        simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hxavg
      have hmy : ‖(⨍ z in ball y (dist x y), f z) -
          ⨍ z in ball x (2 * dist x y), f z‖ ≤ J * (2 * dist x y) ^ γ := by
        simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hyavg
      have hxclose := (hg x hx).2 _ hrsmall
      have hyclose := (hg y hy).2 _ hrsmall
      have htri₁ : ‖g x - ⨍ z in ball x (2 * dist x y), f z‖ ≤
          ‖g x - ⨍ z in ball x (dist x y), f z‖ +
            ‖(⨍ z in ball x (dist x y), f z) - ⨍ z in ball x (2 * dist x y), f z‖ := by
        simpa only [dist_eq_norm (g x), dist_eq_norm (⨍ z in ball x (dist x y), f z)]
          using dist_triangle (g x) (⨍ z in ball x (dist x y), f z)
            (⨍ z in ball x (2 * dist x y), f z)
      have htri₂ : ‖g y - ⨍ z in ball x (2 * dist x y), f z‖ ≤
          ‖g y - ⨍ z in ball y (dist x y), f z‖ +
            ‖(⨍ z in ball y (dist x y), f z) - ⨍ z in ball x (2 * dist x y), f z‖ := by
        simpa only [dist_eq_norm (g y), dist_eq_norm (⨍ z in ball y (dist x y), f z)]
          using dist_triangle (g y) (⨍ z in ball y (dist x y), f z)
            (⨍ z in ball x (2 * dist x y), f z)
      have htri₃ : ‖g x - g y‖ ≤
          ‖g x - ⨍ z in ball x (2 * dist x y), f z‖ +
            ‖g y - ⨍ z in ball x (2 * dist x y), f z‖ := by
        simpa only [dist_eq_norm (g x),
          dist_eq_norm (⨍ z in ball x (2 * dist x y), f z),
          norm_sub_rev (⨍ z in ball x (2 * dist x y), f z) (g y)]
          using dist_triangle (g x) (⨍ z in ball x (2 * dist x y), f z) (g y)
      rw [norm_sub_rev (g x) (⨍ z in ball x (dist x y), f z)] at htri₁
      rw [norm_sub_rev (g y) (⨍ z in ball y (dist x y), f z)] at htri₂
      have hb : ‖g x - g y‖ ≤ C₁ * dist x y ^ γ := by
        dsimp [C₁]
        rw [Real.mul_rpow (by norm_num) hd.le] at hmx hmy
        nlinarith only [hxclose, hyclose, hmx, hmy, htri₁, htri₂, htri₃]
      exact hb.trans (mul_le_mul_of_nonneg_right hc₁ (Real.rpow_nonneg hd.le γ))
    · have hp : (R / 2) ^ γ ≤ dist x y ^ γ :=
        Real.rpow_le_rpow (by positivity) (le_of_not_ge hnear) hγ.le
      have hpos : 0 < (R / 2) ^ γ := Real.rpow_pos_of_pos (by positivity) γ
      have hb : ‖g x - g y‖ ≤ 2 * P :=
        (norm_sub_le _ _).trans (by linarith only [hnorm x hx, hnorm y hy])
      calc
        _ ≤ 2 * P := hb
        _ = C₂ * (R / 2) ^ γ := (div_mul_cancel₀ (2 * P) hpos.ne').symm
        _ ≤ C₂ * dist x y ^ γ :=
          mul_le_mul_of_nonneg_left hp (div_nonneg (by positivity) hpos.le)
        _ ≤ _ := mul_le_mul_of_nonneg_right hc₂ (Real.rpow_nonneg hd.le γ)
  exact ⟨g, campanato_ae_eq_of_dyadic_average_limit hU hR hf hballs (fun x hx => (hg x hx).1),
    campanato_continuousOn_of_holder_bound hC.le hγ hholder, hnorm, hholder⟩

end LiquidDrop
