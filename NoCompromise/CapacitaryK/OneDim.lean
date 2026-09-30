module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-!
# One-dimensional cores of `lem:K-h-monotone` and `prop:K-two-ineq` (chapter 31)

Representation: on `(0,1)`, `DF = p dt` is encoded as
`F b - F a = ∫ t in a..b, p t`, and the measure inequality `Dp ≥ g dt` is encoded as
`∫ t in a..b, g t ≤ p b - p a` for all `0 < a ≤ b < 1`.

The key analytic step is the fundamental theorem of calculus for `F · φ` with `φ` smooth on
`(0,1)`: `F` is differentiable with derivative `p` at every continuity point of `p`, and in both
statements `p` differs from a monotone function by a continuous one, so it is continuous off a
countable set.
-/

noncomputable section

open Real Set Filter MeasureTheory intervalIntegral Topology

namespace LiquidDrop.CapacitaryK

/-- The monotone quantity `h(t) = p(t) - 4F(t)/t + 8πt` (eq:K-h). -/
def levelH (F p : ℝ → ℝ) (t : ℝ) : ℝ := p t - 4 * F t / t + 8 * π * t

/-- A function monotone on `(0,1)` is continuous at all but countably many points of `(0,1)`. -/
lemma countable_not_continuousAt_of_monotoneOn {q : ℝ → ℝ} (hq : MonotoneOn q (Ioo 0 1)) :
    {x ∈ Ioo (0 : ℝ) 1 | ¬ContinuousAt q x}.Countable := by
  refine hq.countable_not_continuousWithinAt.mono ?_
  rintro x ⟨hx, hnc⟩
  exact ⟨hx, fun hc => hnc (hc.continuousAt (Ioo_mem_nhds hx.1 hx.2))⟩

section Primitive

variable {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
include hpint hF

/-- An indefinite integral is continuous. -/
lemma continuousOn_Icc_of_primitive {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ContinuousOn F (Icc a b) := by
  have h1 : ContinuousOn (fun x => F a + ∫ t in a..x, p t) (Icc a b) := by
    have := continuousOn_primitive_interval' (hpint a b ha hab hb) left_mem_uIcc
    rw [uIcc_of_le hab] at this
    exact continuousOn_const.add this
  refine h1.congr ?_
  intro x hx
  have := hF a x ha hx.1 (lt_of_le_of_lt hx.2 hb)
  simp only
  linarith

lemma continuousAt_of_primitive {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : ContinuousAt F x :=
  (continuousOn_Icc_of_primitive hpint hF (a := x / 2) (b := (x + 1) / 2) (by linarith)
    (by linarith) (by linarith)).continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- At a continuity point of `p`, the indefinite integral `F` has derivative `p`. -/
lemma hasDerivAt_of_primitive {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hc : ContinuousAt p x) :
    HasDerivAt F (p x) x := by
  have ha : 0 < x / 2 := by linarith
  have hax : x / 2 < x := by linarith
  have hxb : x < (x + 1) / 2 := by linarith
  have hb : (x + 1) / 2 < 1 := by linarith
  have hmeas : StronglyMeasurableAtFilter p (𝓝 x) := by
    refine ⟨Ioc (x / 2) ((x + 1) / 2),
      mem_of_superset (Ioo_mem_nhds hax hxb) Ioo_subset_Ioc_self, ?_⟩
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1
      (hpint _ _ ha (by linarith) hb)).aestronglyMeasurable
  have hd := (integral_hasDerivAt_right (hpint (x / 2) x ha hax.le hx1) hmeas hc).const_add
    (F (x / 2))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hax hx1] with u hu
  have := hF (x / 2) u ha hu.1.le hu.2
  linarith

end Primitive

/-- Fundamental theorem of calculus for `F · φ`, where `F` is differentiable with derivative `p`
off a countable set. -/
lemma integral_mul_eq_of_hasDerivAt_off_countable {F p φ φ' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    {s : Set ℝ} (hs : s.Countable) (hFc : ContinuousOn F (Icc a b))
    (hFd : ∀ x ∈ Ioo a b \ s, HasDerivAt F (p x) x) (hp : IntervalIntegrable p volume a b)
    (hφc : ContinuousOn φ (Icc a b)) (hφ'c : ContinuousOn φ' (Icc a b))
    (hφd : ∀ x ∈ Ioo a b, HasDerivAt φ (φ' x) x) :
    ∫ t in a..b, (p t * φ t + F t * φ' t) = F b * φ b - F a * φ a := by
  refine integral_eq_of_hasDerivAt_off_countable_of_le (fun t => F t * φ t) _ hab hs
    (hFc.mul hφc) (fun x hx => (hFd x hx).mul (hφd x hx.1)) ?_
  exact (hp.mul_continuousOn (by rwa [uIcc_of_le hab])).add
    ((hFc.mul hφ'c).intervalIntegrable_of_Icc hab)


/-- The distributional lower bound makes `p + 8πt` monotone. -/
lemma monotoneOn_p_add_linear {F p : ℝ → ℝ}
    (hFpos : ∀ t, 0 < t → t < 1 → 0 < F t)
    (hq : ∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (fun t => p t ^ 2 / F t) volume a b)
    (hDp : ∀ a b, 0 < a → a ≤ b → b < 1 →
      ∫ t in a..b, (p t ^ 2 / F t - 8 * π) ≤ p b - p a) :
    MonotoneOn (fun t => p t + 8 * π * t) (Ioo 0 1) := by
  intro a ha b hb hab
  have hi := hDp a b ha.1 hab hb.2
  rw [integral_sub (hq a b ha.1 hab hb.2) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hi
  have hn : 0 ≤ ∫ t in a..b, p t ^ 2 / F t :=
    integral_nonneg hab (fun t ht => div_nonneg (sq_nonneg _) (hFpos t
      (lt_of_lt_of_le ha.1 ht.1) (lt_of_le_of_lt ht.2 hb.2)).le)
  nlinarith

/-- The primitive identity for `4F/t`. -/
lemma integral_four_div_eq {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hc : {x ∈ Ioo (0 : ℝ) 1 | ¬ContinuousAt p x}.Countable)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ t in a..b, (4 * p t / t - 4 * F t / t ^ 2) = 4 * F b / b - 4 * F a / a := by
  have hn : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hφc : ContinuousOn (fun x : ℝ => 4 / x) (Icc a b) :=
    continuousOn_const.div continuousOn_id hn
  have hφ'c : ContinuousOn (fun x : ℝ => -(4 : ℝ) / x ^ 2) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun x hx => pow_ne_zero _ (hn x hx))
  have hi := integral_mul_eq_of_hasDerivAt_off_countable hab hc
    (continuousOn_Icc_of_primitive hpint hF ha hab hb)
    (fun x hx => hasDerivAt_of_primitive hpint hF (lt_trans ha hx.1.1)
      (lt_trans hx.1.2 hb) (by
        by_contra h
        exact hx.2 ⟨⟨lt_trans ha hx.1.1, lt_trans hx.1.2 hb⟩, h⟩))
    (hpint a b ha hab hb) hφc hφ'c (fun x hx => by
      refine ((hasDerivAt_const x (4 : ℝ)).div (hasDerivAt_id x)
        (hn x ⟨hx.1.le, hx.2.le⟩)).congr_deriv ?_
      change (0 * x - 4 * 1) / x ^ 2 = -(4 : ℝ) / x ^ 2
      ring)
  calc
    _ = ∫ t in a..b, (p t * (4 / t) + F t * (-4 / t ^ 2)) := by
      apply integral_congr
      intro x hx
      ring
    _ = F b * (4 / b) - F a * (4 / a) := hi
    _ = _ := by ring

theorem levelH_increment_ge {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hFpos : ∀ t, 0 < t → t < 1 → 0 < F t)
    (hq : ∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (fun t => p t ^ 2 / F t) volume a b)
    (hDp : ∀ a b, 0 < a → a ≤ b → b < 1 → ∫ t in a..b, (p t ^ 2 / F t - 8 * π) ≤ p b - p a)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ t in a..b, (p t / √(F t) - 2 * √(F t) / t) ^ 2 ≤ levelH F p b - levelH F p a := by
  have hc : {x ∈ Ioo (0 : ℝ) 1 | ¬ContinuousAt p x}.Countable := by
    refine (countable_not_continuousAt_of_monotoneOn
      (monotoneOn_p_add_linear hFpos hq hDp)).mono ?_
    rintro x ⟨hx, hnc⟩
    refine ⟨hx, fun hc => hnc ?_⟩
    convert hc.sub ((continuousAt_const (y := 8 * π)).mul continuousAt_id) using 1
    ext t
    dsimp
    ring
  have hn : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hFc := continuousOn_Icc_of_primitive hpint hF ha hab hb
  have hlin : IntervalIntegrable (fun t => 4 * p t / t - 4 * F t / t ^ 2) volume a b := by
    have h1 : IntervalIntegrable (fun t => p t * (4 / t)) volume a b :=
      (hpint a b ha hab hb).mul_continuousOn (by
        rw [uIcc_of_le hab]
        exact continuousOn_const.div continuousOn_id hn)
    have h2 : IntervalIntegrable (fun t => 4 * F t / t ^ 2) volume a b :=
      ((continuousOn_const.mul hFc).div (continuousOn_id.pow 2)
        (fun x hx => pow_ne_zero _ (hn x hx))).intervalIntegrable_of_Icc hab
    convert h1.sub h2 using 1
    ext t
    ring
  have heq : (∫ t in a..b, (p t / √(F t) - 2 * √(F t) / t) ^ 2) =
      (∫ t in a..b, p t ^ 2 / F t) - (4 * F b / b - 4 * F a / a) := by
    rw [← integral_four_div_eq hpint hF hc ha hab hb,
      ← integral_sub (hq a b ha hab hb) hlin]
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hFt := hFpos t (lt_of_lt_of_le ha ht.1) (lt_of_le_of_lt ht.2 hb)
    have hs := Real.sq_sqrt hFt.le
    have hsn : √(F t) ≠ 0 := Real.sqrt_ne_zero'.2 hFt
    calc
      _ = p t ^ 2 / (√(F t)) ^ 2 -
          (4 * p t / t - 4 * (√(F t)) ^ 2 / t ^ 2) := by
        field_simp [hn t ht, hsn]
        ring
      _ = _ := by rw [hs]
  rw [heq]
  have hi := hDp a b ha hab hb
  rw [integral_sub (hq a b ha hab hb) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hi
  dsimp [levelH]
  linarith

theorem levelH_monotoneOn {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hFpos : ∀ t, 0 < t → t < 1 → 0 < F t)
    (hq : ∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (fun t => p t ^ 2 / F t) volume a b)
    (hDp : ∀ a b, 0 < a → a ≤ b → b < 1 → ∫ t in a..b, (p t ^ 2 / F t - 8 * π) ≤ p b - p a) :
    MonotoneOn (levelH F p) (Ioo 0 1) := by
  intro a ha b hb hab
  have hi := levelH_increment_ge hpint hF hFpos hq hDp ha.1 hab hb.2
  have hn := integral_nonneg_of_forall (μ := volume) hab
    (fun t => sq_nonneg (p t / √(F t) - 2 * √(F t) / t))
  linarith


/-- A monotone function on `(0,1)` with right limit zero is nonnegative there. -/
lemma nonneg_of_monotoneOn_of_tendsto_zero {f : ℝ → ℝ}
    (hm : MonotoneOn f (Ioo 0 1)) (h0 : Tendsto f (𝓝[>] 0) (𝓝 0))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 ≤ f t := by
  apply le_of_tendsto h0
  filter_upwards [Ioo_mem_nhdsGT ht0] with x hx
  exact hm ⟨hx.1, lt_trans hx.2 ht1⟩ ⟨ht0, ht1⟩ hx.2.le

/-- Monotonicity of `h` gives the countable exceptional set needed for differentiating `F`. -/
lemma countable_not_continuousAt_of_levelH {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hm : MonotoneOn (levelH F p) (Ioo 0 1)) :
    {x ∈ Ioo (0 : ℝ) 1 | ¬ContinuousAt p x}.Countable := by
  refine (countable_not_continuousAt_of_monotoneOn hm).mono ?_
  rintro x ⟨hx, hnc⟩
  refine ⟨hx, fun hc => hnc ?_⟩
  have hFc := continuousAt_of_primitive hpint hF hx.1 hx.2
  have hc' := (hc.add (((continuousAt_const (y := (4 : ℝ))).mul hFc).div continuousAt_id
    (ne_of_gt hx.1))).sub ((continuousAt_const (y := 8 * π)).mul continuousAt_id)
  convert hc' using 1
  ext t
  dsimp [levelH]
  ring

/-- The integrating factor identity for `(F - 4πt²)/t⁴`. -/
lemma integral_levelH_div_four_eq {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hc : {x ∈ Ioo (0 : ℝ) 1 | ¬ContinuousAt p x}.Countable)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ t in a..b, levelH F p t / t ^ 4) =
      (F b - 4 * π * b ^ 2) / b ^ 4 - (F a - 4 * π * a ^ 2) / a ^ 4 := by
  have hn : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hFc := continuousOn_Icc_of_primitive hpint hF ha hab hb
  refine integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t => (F t - 4 * π * t ^ 2) / t ^ 4) (fun t => levelH F p t / t ^ 4)
    hab hc ?_ ?_ ?_
  · exact (hFc.sub (continuousOn_const.mul (continuousOn_id.pow 2))).div
      (continuousOn_id.pow 4) (fun x hx => pow_ne_zero _ (hn x hx))
  · intro x hx
    have hxn := hn x ⟨hx.1.1.le, hx.1.2.le⟩
    have hFd := hasDerivAt_of_primitive hpint hF (lt_trans ha hx.1.1)
      (lt_trans hx.1.2 hb) (by
        by_contra h
        exact hx.2 ⟨⟨lt_trans ha hx.1.1, lt_trans hx.1.2 hb⟩, h⟩)
    refine ((hFd.sub (((hasDerivAt_id x).pow 2).const_mul (4 * π))).div
      ((hasDerivAt_id x).pow 4) (pow_ne_zero _ hxn)).congr_deriv ?_
    dsimp [levelH]
    field_simp [hxn]
    ring
  · have h1 : IntervalIntegrable (fun t => p t * (1 / t ^ 4)) volume a b :=
      (hpint a b ha hab hb).mul_continuousOn (by
        rw [uIcc_of_le hab]
        exact continuousOn_const.div (continuousOn_id.pow 4)
          (fun x hx => pow_ne_zero _ (hn x hx)))
    have h2 : IntervalIntegrable (fun t => (-4 * F t / t + 8 * π * t) / t ^ 4)
        volume a b := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      exact (((continuousOn_const.mul hFc).div continuousOn_id hn).add
        (continuousOn_const.mul continuousOn_id)).div (continuousOn_id.pow 4)
          (fun x hx => pow_ne_zero _ (hn x hx))
    convert h1.add h2 using 1
    ext t
    dsimp [levelH]
    ring

theorem two_level_inequalities {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hmono : MonotoneOn (levelH F p) (Ioo 0 1))
    (hh0 : Tendsto (levelH F p) (𝓝[>] 0) (𝓝 0))
    (hz0 : Tendsto (fun t => (F t - 4 * π * t ^ 2) / t ^ 4) (𝓝[>] 0) (𝓝 0))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    4 * F t / t - 8 * π * t ≤ p t ∧ 4 * π * t ^ 2 ≤ F t := by
  have hh : ∀ x, 0 < x → x < 1 → 0 ≤ levelH F p x :=
    fun x hx0 hx1 => nonneg_of_monotoneOn_of_tendsto_zero hmono hh0 hx0 hx1
  refine ⟨?_, ?_⟩
  · have := hh t ht0 ht1
    dsimp [levelH] at this
    linarith
  · have hc := countable_not_continuousAt_of_levelH hpint hF hmono
    have hzmono : MonotoneOn (fun t => (F t - 4 * π * t ^ 2) / t ^ 4) (Ioo 0 1) := by
      intro a ha b hb hab
      have hi := integral_levelH_div_four_eq hpint hF hc ha.1 hab hb.2
      have hn : 0 ≤ ∫ x in a..b, levelH F p x / x ^ 4 :=
        integral_nonneg hab (fun x hx => div_nonneg
          (hh x (lt_of_lt_of_le ha.1 hx.1) (lt_of_le_of_lt hx.2 hb.2)) (by positivity))
      linarith
    have hz := nonneg_of_monotoneOn_of_tendsto_zero hzmono hz0 ht0 ht1
    have := (le_div_iff₀ (pow_pos ht0 4)).mp hz
    linarith

end LiquidDrop.CapacitaryK
