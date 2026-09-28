import NoCompromise.Elliptic.NewtonianSchauderPotential

/-!
# Localizing a Hölder source

The fixed smooth cutoff is one on B₃/₄ and supported in B̄₇/₈. Multiplication
therefore turns a source known only on B₁ into a bounded compactly supported
globally Hölder source. No measurability or regularity outside B₁ is assumed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The source cutoff has a fixed gap between its support and the unit sphere. -/
def schauderSourceBump : ContDiffBump (0 : E₃) :=
  ⟨3 / 4, 7 / 8, by norm_num, by norm_num⟩

def schauderCutoffSource (f : E₃ → ℝ) (x : E₃) : ℝ := schauderSourceBump x * f x

lemma norm_schauderSourceBump_le (x : E₃) : ‖schauderSourceBump x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg schauderSourceBump.nonneg]
  exact schauderSourceBump.le_one

lemma schauderSourceBump_zero_of_notMem_unitBall {x : E₃} (hx : x ∉ ball (0 : E₃) 1) :
    schauderSourceBump x = 0 := by
  apply schauderSourceBump.zero_of_le_dist
  have hn : 1 ≤ ‖x‖ := not_lt.mp (by simpa using hx)
  change (7 / 8 : ℝ) ≤ dist x 0
  rw [dist_zero_right]
  linarith

lemma schauderCutoffSource_hasCompactSupport (f : E₃ → ℝ) :
    HasCompactSupport (schauderCutoffSource f) := schauderSourceBump.hasCompactSupport.mul_right

lemma schauderCutoffSource_tsupport (f : E₃ → ℝ) :
    tsupport (schauderCutoffSource f) ⊆ ball 0 1 := by
  apply tsupport_mul_subset_left.trans
  rw [schauderSourceBump.tsupport_eq]
  exact closedBall_subset_ball (by norm_num : (7 / 8 : ℝ) < 1)

lemma schauderCutoffSource_eqOn (f : E₃ → ℝ) :
    EqOn (schauderCutoffSource f) f (ball 0 (3 / 4)) := by
  intro x hx
  have hb : schauderSourceBump x = 1 :=
    schauderSourceBump.one_of_mem_closedBall (ball_subset_closedBall hx)
  simp only [schauderCutoffSource, hb, one_mul]

lemma exists_schauderSourceBump_holder_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ x y : E₃, ‖schauderSourceBump x - schauderSourceBump y‖ ≤ C * ‖x - y‖ ^ α := by
  have hc : ContDiff ℝ 1 (schauderSourceBump : E₃ → ℝ) := schauderSourceBump.contDiff
  obtain ⟨M, hM⟩ := (schauderSourceBump.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hc.continuous_fderiv (by norm_num))
  let L := max M 0 + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hder : ∀ x ∈ (univ : Set E₃), ‖fderiv ℝ schauderSourceBump x‖ ≤ L := by
    intro x _
    exact (hM x).trans (by dsimp [L]; linarith [le_max_left M 0])
  have hlip : ∀ x ∈ (univ : Set E₃), ∀ y ∈ univ,
      ‖schauderSourceBump x - schauderSourceBump y‖ ≤ L * ‖x - y‖ := by
    intro x _ y _
    exact (convex_univ : Convex ℝ (univ : Set E₃)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hc.differentiable one_ne_zero z) hder (mem_univ y) (mem_univ x)
  refine ⟨L + 2, by positivity, fun x y => ?_⟩
  by_cases hxy : x = y
  · simp [hxy, Real.zero_rpow hα.ne']
  have hden := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  apply (div_le_iff₀ hden).mp
  simpa only [Real.one_rpow, mul_one, div_one] using
    holderInterpolation_quotient_le hα hα1 (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 1) hL (fun z _ => norm_schauderSourceBump_le z)
      hlip (mem_univ x) (mem_univ y)

/-- Quantitative globalization of a local Hölder source. The source is unrestricted
outside the unit ball; the resulting cutoff source is genuinely continuous. -/
theorem exists_schauderCutoffSource_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : E₃ → ℝ), HasFiniteHolderNormOn α f (ball 0 1) →
      Continuous (schauderCutoffSource f) ∧
      (∀ x, ‖schauderCutoffSource f x‖ ≤ holderNorm α f (ball 0 1)) ∧
      ∀ x y, ‖schauderCutoffSource f x - schauderCutoffSource f y‖ ≤
        C * holderNorm α f (ball 0 1) * ‖x - y‖ ^ α := by
  obtain ⟨C, hC, hCb⟩ := exists_schauderSourceBump_holder_bound hα hα1
  refine ⟨1 + C + (8 : ℝ) ^ α, by positivity, fun f hf => ?_⟩
  let N := holderNorm α f (ball 0 1)
  have hN : 0 ≤ N := hf.norm_nonneg
  have hval : ∀ x ∈ ball (0 : E₃) 1, ‖f x‖ ≤ N :=
    fun x hx => (norm_le_holderUniformNorm hf.uniform_bounded hx).trans hf.uniformNorm_le
  have hloc : ∀ x ∈ ball (0 : E₃) 1, ∀ y ∈ ball (0 : E₃) 1,
      ‖f x - f y‖ ≤ N * ‖x - y‖ ^ α := by
    intro x hx y hy
    by_cases hxy : x = y
    · simp [hxy, Real.zero_rpow hα.ne']
    apply (schauder_norm_sub_le_holder hf hx hy hxy).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact le_add_of_nonneg_left (holderUniformNorm_nonneg hf.uniform_bounded)
  have hglobal (x : E₃) : ‖schauderCutoffSource f x‖ ≤ N := by
    by_cases hx : x ∈ ball (0 : E₃) 1
    · rw [schauderCutoffSource, norm_mul]
      simpa only [one_mul] using mul_le_mul (norm_schauderSourceBump_le x) (hval x hx)
        (norm_nonneg _) (by norm_num)
    · simp only [schauderCutoffSource, schauderSourceBump_zero_of_notMem_unitBall hx,
        zero_mul, norm_zero]
      exact hN
  have hcross (x : E₃) (_hx : x ∈ ball (0 : E₃) 1) (y : E₃) (hy : y ∉ ball (0 : E₃) 1) :
      ‖schauderCutoffSource f x - schauderCutoffSource f y‖ ≤
        (8 : ℝ) ^ α * N * ‖x - y‖ ^ α := by
    have hgy : schauderCutoffSource f y = 0 := by
      simp only [schauderCutoffSource, schauderSourceBump_zero_of_notMem_unitBall hy, zero_mul]
    rw [hgy, sub_zero]
    by_cases hb : schauderSourceBump x = 0
    · simp only [schauderCutoffSource, hb, zero_mul, norm_zero]
      positivity
    have hx' : ‖x‖ < 7 / 8 := by
      have h := Function.mem_support.mpr hb
      rw [schauderSourceBump.support_eq] at h
      simpa [schauderSourceBump] using h
    have hy' : 1 ≤ ‖y‖ := not_lt.mp (by simpa using hy)
    have ht : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      calc
        _ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have hd : 1 ≤ (8 : ℝ) * ‖x - y‖ := by linarith
    have hp : 1 ≤ (8 : ℝ) ^ α * ‖x - y‖ ^ α := by
      simpa only [Real.one_rpow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8)
        (norm_nonneg (x - y))] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hd hα.le
    have hh := mul_le_mul_of_nonneg_left hp hN
    nlinarith [hglobal x]
  have hinc (x y : E₃) : ‖schauderCutoffSource f x - schauderCutoffSource f y‖ ≤
      (1 + C + (8 : ℝ) ^ α) * N * ‖x - y‖ ^ α := by
    by_cases hx : x ∈ ball (0 : E₃) 1
    · by_cases hy : y ∈ ball (0 : E₃) 1
      · have he : schauderCutoffSource f x - schauderCutoffSource f y =
            schauderSourceBump x * (f x - f y) +
              (schauderSourceBump x - schauderSourceBump y) * f y := by
          dsimp [schauderCutoffSource]
          ring
        rw [he]
        calc
          _ ≤ ‖schauderSourceBump x‖ * ‖f x - f y‖ +
              ‖schauderSourceBump x - schauderSourceBump y‖ * ‖f y‖ := by
            simpa only [norm_mul] using norm_add_le
              (schauderSourceBump x * (f x - f y))
              ((schauderSourceBump x - schauderSourceBump y) * f y)
          _ ≤ 1 * (N * ‖x - y‖ ^ α) + (C * ‖x - y‖ ^ α) * N := add_le_add
            (mul_le_mul (norm_schauderSourceBump_le x) (hloc x hx y hy)
              (norm_nonneg _) (by norm_num))
            (mul_le_mul (hCb x y) (hval y hy) (norm_nonneg _) (by positivity))
          _ ≤ _ := by
            have hpos : 0 ≤ (8 : ℝ) ^ α * (N * ‖x - y‖ ^ α) := by positivity
            nlinarith
      · exact (hcross x hx y hy).trans (by gcongr; linarith)
    · by_cases hy : y ∈ ball (0 : E₃) 1
      · have h := hcross y hy x hx
        rw [norm_sub_rev (schauderCutoffSource f y), norm_sub_rev y] at h
        exact h.trans (by gcongr; linarith)
      · simp only [schauderCutoffSource, schauderSourceBump_zero_of_notMem_unitBall hx,
          schauderSourceBump_zero_of_notMem_unitBall hy, zero_mul, sub_self, norm_zero]
        positivity
  have hQ : 0 ≤ (1 + C + (8 : ℝ) ^ α) * N := by positivity
  have hh : HasFiniteHolderNormOn α (schauderCutoffSource f) univ := by
    apply HasFiniteHolderNormOn.of_bounds hN hQ (fun x _ => hglobal x)
    intro x _ y _
    by_cases hxy : x = y
    · simpa only [hxy, sub_self, norm_zero, zero_div] using hQ
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)).mpr
      (hinc x y)
  exact ⟨continuousOn_univ.mp (schauder_continuousOn_of_finiteHolder hα hh), hglobal, hinc⟩

/-- A local Hölder source has a quantitatively C²,α Newtonian part on B₃/₄. -/
theorem exists_schauderCutoffPotential_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : E₃ → ℝ), HasFiniteHolderNormOn α f (ball 0 1) →
      HasC2HolderOn α (schauderPotential (schauderCutoffSource f)) (ball 0 (3 / 4)) ∧
      schauderC2HolderNorm α (schauderPotential (schauderCutoffSource f)) (ball 0 (3 / 4)) ≤
        C * holderNorm α f (ball 0 1) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_schauderCutoffSource_bound hα hα1
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_schauderPotential_norm_bound hα hα1
    (by norm_num : (0 : ℝ) < 3 / 4)
  refine ⟨C₂ * (C₁ + 1), by positivity, fun f hf => ?_⟩
  obtain ⟨hc, hv, hi⟩ := hb₁ f hf
  obtain ⟨hu, hb⟩ := hb₂ (C₁ * holderNorm α f (ball 0 1)) (mul_nonneg hC₁.le hf.norm_nonneg)
    (holderNorm α f (ball 0 1)) hf.norm_nonneg (schauderCutoffSource f) hc.measurable
    (schauderCutoffSource_hasCompactSupport f) hv hi (schauderCutoffSource_tsupport f)
  exact ⟨hu, hb.trans_eq (by ring)⟩

end LiquidDrop
