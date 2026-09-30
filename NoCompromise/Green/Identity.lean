module

public import NoCompromise.Elliptic.Newtonian
public import NoCompromise.Energy.PotentialRegularity
public import NoCompromise.Area.Sphere
public import NoCompromise.Elliptic.ClassicalKernelFluxLimits

@[expose] public section

noncomputable section
open Set MeasureTheory Metric InnerProductSpace
open scoped RealInnerProductSpace ENNReal
namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The real Coulomb potential, written as a scalar Newtonian potential. -/
def coulombPotentialReal (Ω : Set E₃) (x : E₃) : ℝ :=
  scalarNewtonianPotential (Ω.indicator fun _ => (1 : ℝ)) x

private lemma scalar_kernel_remainder (a b d h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 ≤ d)
    (hab : |a - b| ≤ d) (hhalf : b ≤ 2 * a)
    (hsq : a ^ 2 = b ^ 2 - 2 * h + d ^ 2) :
    |1 / a - 1 / b - h / b ^ 3| ≤ 3 * d ^ 2 / b ^ 3 := by
  have habsq : (a - b) ^ 2 ≤ d ^ 2 := by
    calc
      (a-b)^2 = |a-b|^2 := (sq_abs _).symm
      _ ≤ d^2 := (sq_le_sq₀ (abs_nonneg _) hd).2 hab
  have hnum : (a - b) ^ 2 * (2 * b + a) ≤ 5 * a * d ^ 2 := by
    have hfac : 2 * b + a ≤ 5 * a := by linarith
    have h1 := mul_le_mul_of_nonneg_left hfac (sq_nonneg (a-b))
    have h2 := mul_le_mul_of_nonneg_right habsq (by positivity : 0 ≤ 5*a)
    nlinarith [h1, h2]
  have heq : 1 / a - 1 / b - h / b ^ 3 =
      ((a-b)^2 * (2*b+a) - a*d^2) / (2*a*b^3) := by
    field_simp
    nlinarith [hsq]
  rw [heq]
  rw [abs_div]
  have hden : 0 < 2*a*b^3 := by positivity
  rw [abs_of_pos hden]
  apply (div_le_div_iff₀ hden (by positivity)).2
  have hlo : -(6 * a * d ^ 2) ≤ (a-b)^2*(2*b+a)-a*d^2 := by
    have : 0 ≤ (a-b)^2*(2*b+a) := by positivity
    nlinarith
  have hhi : (a-b)^2*(2*b+a)-a*d^2 ≤ 6*a*d^2 := by nlinarith
  have habs : |(a-b)^2*(2*b+a)-a*d^2| ≤ 6*a*d^2 := abs_le.mpr ⟨hlo, hhi⟩
  have hpow : 0 < b^3 := pow_pos hb 3
  nlinarith [mul_le_mul_of_nonneg_right habs hpow.le]

private lemma scalar_inv_cube_remainder (a b d h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 ≤ d)
    (hab : |a - b| ≤ d) (hhalf : b ≤ 2 * a)
    (hsq : a ^ 2 = b ^ 2 - 2 * h + d ^ 2) :
    |1/b^3 - 1/a^3 + 3*h/b^5| ≤ 25*d^2/b^5 := by
  let P := 3*a^3 + 6*a^2*b + 4*a*b^2 + 2*b^3
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hP : P ≤ 47*a^3 := by
    dsimp [P]
    calc
      _ ≤ 3*a^3 + 6*a^2*(2*a) + 4*a*(2*a)^2 + 2*(2*a)^3 := by gcongr
      _ = 47*a^3 := by ring
  have habsq : (a-b)^2 ≤ d^2 := by
    calc
      (a-b)^2 = |a-b|^2 := (sq_abs _).symm
      _ ≤ d^2 := (sq_le_sq₀ (abs_nonneg _) hd).2 hab
  have hnum : |3*a^3*d^2 - (a-b)^2*P| ≤ 50*a^3*d^2 := by
    apply abs_le.mpr
    constructor
    · have hp := mul_le_mul_of_nonneg_right hP (sq_nonneg (a-b))
      have hq := mul_le_mul_of_nonneg_right habsq hP0
      nlinarith [hp, hq]
    · have : 0 ≤ (a-b)^2*P := mul_nonneg (sq_nonneg _) hP0
      nlinarith
  have heq : 1/b^3 - 1/a^3 + 3*h/b^5 =
      (3*a^3*d^2 - (a-b)^2*P)/(2*a^3*b^5) := by
    dsimp [P]
    field_simp
    nlinarith [hsq]
  rw [heq, abs_div, abs_of_pos (by positivity : 0 < 2*a^3*b^5)]
  have hb5 : 0 < b^5 := pow_pos hb 5
  apply (div_le_div_iff₀ (by positivity : 0 < 2*a^3*b^5) hb5).2
  nlinarith [mul_le_mul_of_nonneg_right hnum hb5.le]

private lemma scalar_inv_cube_difference (a b d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 ≤ d)
    (hab : |a - b| ≤ d) (hhalf : b ≤ 2 * a) :
    |1/a^3 - 1/b^3| ≤ 14*d/b^4 := by
  let Q := b^2 + a*b + a^2
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQ : Q ≤ 7*a^2 := by
    dsimp [Q]
    calc
      _ ≤ (2*a)^2 + a*(2*a) + a^2 := by gcongr
      _ = 7*a^2 := by ring
  have heq : 1/a^3 - 1/b^3 = (b-a)*Q/(a^3*b^3) := by
    dsimp [Q]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (by positivity : 0 < a^3*b^3), abs_mul,
    abs_of_nonneg hQ0]
  have hba : |b-a| ≤ d := by simpa only [abs_sub_comm] using hab
  have hdq := mul_le_mul_of_nonneg_right hba hQ0
  have hprod : |b-a| * Q ≤ 7*a^2*d := by
    calc
      _ ≤ d*Q := hdq
      _ ≤ d*(7*a^2) := mul_le_mul_of_nonneg_left hQ hd
      _ = _ := by ring
  have hb3 : 0 < b^3 := pow_pos hb 3
  have hb4 : 0 < b^4 := pow_pos hb 4
  apply (div_le_div_iff₀ (by positivity : 0 < a^3*b^3) hb4).2
  have hmult : b*d ≤ 2*a*d := mul_le_mul_of_nonneg_right hhalf hd
  have hp := mul_le_mul_of_nonneg_right hprod hb4.le
  have hm := mul_le_mul_of_nonneg_right hmult (by positivity : 0 ≤ 7*a^2*b^3)
  nlinarith [hp, hm]

/-- A second-order far-field expansion of the Coulomb kernel. -/
theorem kernel_expansion_bound_three (R : ℝ) (hR : 0 < R)
    (x y : E₃) (hy : ‖y‖ ≤ R) (hx : 2 * R < ‖x‖) :
      |1 / ‖x - y‖ - 1 / ‖x‖ - ⟪x, y⟫_ℝ / ‖x‖ ^ 3| ≤
        3 * ‖y‖ ^ 2 / ‖x‖ ^ 3 := by
  have hb : 0 < ‖x‖ := by linarith
  have hdist : ‖x‖ ≤ ‖x-y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-y) y
  have ha : 0 < ‖x-y‖ := by
    have : ‖y‖ < ‖x‖ / 2 := by linarith
    linarith [norm_nonneg (x-y)]
  have hhalf : ‖x‖ ≤ 2 * ‖x-y‖ := by linarith
  have hab : |‖x-y‖ - ‖x‖| ≤ ‖y‖ := by
    simpa only [sub_sub_cancel_left, norm_neg] using
      (abs_norm_sub_norm_le (x-y) x)
  exact scalar_kernel_remainder _ _ _ _ ha hb (norm_nonneg y) hab hhalf
    (norm_sub_sq_real x y)

/-- The differentiated kernel has a uniform quadratic far-field remainder. -/
theorem kernel_gradient_expansion_bound_thirtynine (R : ℝ) (hR : 0 < R)
    (x y : E₃) (hy : ‖y‖ ≤ R) (hx : 2 * R < ‖x‖) :
      ‖-((‖x-y‖^3)⁻¹ • (x-y)) - (-((‖x‖^3)⁻¹ • x)) -
          ((‖x‖^3)⁻¹ • y - (3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) • x)‖ ≤
        39 * ‖y‖^2 / ‖x‖^4 := by
  have hb : 0 < ‖x‖ := by linarith
  have hdist : ‖x‖ ≤ ‖x-y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-y) y
  have ha : 0 < ‖x-y‖ := by
    have : ‖y‖ < ‖x‖ / 2 := by linarith
    linarith [norm_nonneg (x-y)]
  have hhalf : ‖x‖ ≤ 2 * ‖x-y‖ := by linarith
  have hab : |‖x-y‖ - ‖x‖| ≤ ‖y‖ := by
    simpa only [sub_sub_cancel_left, norm_neg] using
      (abs_norm_sub_norm_le (x-y) x)
  have hs := scalar_inv_cube_remainder _ _ _ _ ha hb (norm_nonneg y) hab hhalf
    (norm_sub_sq_real x y)
  have ht := scalar_inv_cube_difference _ _ _ ha hb (norm_nonneg y) hab hhalf
  let s : ℝ := 1/‖x‖^3 - 1/‖x-y‖^3 + 3*⟪x,y⟫_ℝ/‖x‖^5
  let t : ℝ := 1/‖x-y‖^3 - 1/‖x‖^3
  have heq : -((‖x-y‖^3)⁻¹ • (x-y)) - (-((‖x‖^3)⁻¹ • x)) -
      ((‖x‖^3)⁻¹ • y - (3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) • x) = s • x + t • y := by
    dsimp [s, t]
    simp only [div_eq_mul_inv]
    simp only [smul_sub, sub_smul, add_smul, mul_smul]
    module
  rw [heq]
  calc
    ‖s • x + t • y‖ ≤ ‖s • x‖ + ‖t • y‖ := norm_add_le _ _
    _ = |s| * ‖x‖ + |t| * ‖y‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ (25*‖y‖^2/‖x‖^5)*‖x‖ + (14*‖y‖/‖x‖^4)*‖y‖ := by
      dsimp [s, t]
      gcongr
    _ = 39*‖y‖^2/‖x‖^4 := by field_simp; ring

/-- The absolute constant in the gradient-kernel estimate is 39. -/
theorem kernel_gradient_expansion_bound (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, ∀ x y : E₃, ‖y‖ ≤ R → 2 * R < ‖x‖ →
      ‖-((‖x-y‖^3)⁻¹ • (x-y)) - (-((‖x‖^3)⁻¹ • x)) -
          ((‖x‖^3)⁻¹ • y - (3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) • x)‖ ≤
        C * ‖y‖^2 / ‖x‖^4 :=
  ⟨39, kernel_gradient_expansion_bound_thirtynine R hR⟩

lemma coulombPotentialReal_eq_setIntegral (Ω : Set E₃) (hΩ : MeasurableSet Ω)
    (x : E₃) :
    coulombPotentialReal Ω x = ∫ y in Ω, 1 / ‖x-y‖ := by
  rw [coulombPotentialReal, scalarNewtonianPotential, ← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Ω <;> simp [hy, Set.indicator, one_div]

/-- The absolute constant in the kernel estimate is 3. -/
theorem kernel_expansion_bound (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, ∀ x y : E₃, ‖y‖ ≤ R → 2 * R < ‖x‖ →
      |1 / ‖x-y‖ - 1 / ‖x‖ - ⟪x,y⟫_ℝ / ‖x‖^3| ≤
        C * ‖y‖^2 / ‖x‖^3 :=
  ⟨3, kernel_expansion_bound_three R hR⟩

private lemma integrableOn_id_bounded (Ω : Set E₃) (R : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R) : IntegrableOn (fun y : E₃ => y) Ω := by
  have hb : Bornology.IsBounded Ω := isBounded_closedBall.subset hΩ
  refine Measure.integrableOn_of_bounded (M := R) hb.measure_lt_top.ne
    continuous_id.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hΩm] with y hy
  simpa only [id_eq, mem_closedBall, dist_zero_right] using hΩ hy

private lemma coulombPotentialReal_remainder_integral (Ω : Set E₃) (R : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R) (x : E₃) :
    coulombPotentialReal Ω x - (volume Ω).toReal / ‖x‖ -
        ⟪∫ y in Ω, y, x⟫_ℝ / ‖x‖^3 =
      ∫ y in Ω, (1/‖x-y‖ - 1/‖x‖ - ⟪x,y⟫_ℝ/‖x‖^3) := by
  have hb : Bornology.IsBounded Ω := isBounded_closedBall.subset hΩ
  have hfinite : volume Ω < ∞ := hb.measure_lt_top
  have hi : IntegrableOn (fun y : E₃ => y) Ω := integrableOn_id_bounded Ω R hΩm hΩ
  have hk : IntegrableOn (fun y : E₃ => 1/‖x-y‖) Ω := by
    simpa only [one_div] using integrableOn_coulombKernel Ω hfinite x
  have hc : IntegrableOn (fun _ : E₃ => 1/‖x‖) Ω := integrableOn_const hfinite.ne
  have hh : IntegrableOn (fun y : E₃ => ⟪x,y⟫_ℝ/‖x‖^3) Ω := by
    have hh' : Integrable (fun y : E₃ => ⟪x,y⟫_ℝ) (volume.restrict Ω) := by
      exact (innerSL ℝ x).integrable_comp hi
    exact hh'.div_const _
  have hinter : (∫ y in Ω, ⟪x,y⟫_ℝ) = ⟪x, ∫ y in Ω, y⟫_ℝ := by
    simpa only [innerSL_apply_apply] using (innerSL ℝ x).integral_comp_comm hi
  have hsub : (∫ y in Ω, 1/‖x-y‖ - 1/‖x‖) =
      (∫ y in Ω, 1/‖x-y‖) - (∫ y in Ω, 1/‖x‖) := by
    simpa only [Pi.sub_apply] using (integral_sub hk hc)
  have hsplit : (∫ y in Ω, (1/‖x-y‖ - 1/‖x‖ - ⟪x,y⟫_ℝ/‖x‖^3)) =
      (∫ y in Ω, 1/‖x-y‖) - (∫ y in Ω, 1/‖x‖) -
        (∫ y in Ω, ⟪x,y⟫_ℝ/‖x‖^3) := by
    simpa only [Pi.sub_apply, hsub] using (integral_sub (hk.sub hc) hh)
  rw [hsplit, ← coulombPotentialReal_eq_setIntegral Ω hΩm x]
  simp only [setIntegral_const, smul_eq_mul, div_eq_mul_inv, integral_mul_const, hinter]
  rw [real_inner_comm]
  simp only [measureReal_def]
  ring

/-- The multipole expansion of a bounded measurable density with constant 3. -/
theorem coulombPotentialReal_expansion (Ω : Set E₃) (R : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R) (hR : 0 < R) :
    ∃ C : ℝ, ∀ x : E₃, 2*R < ‖x‖ →
      |coulombPotentialReal Ω x - (volume Ω).toReal/‖x‖ -
          ⟪∫ y in Ω, y, x⟫_ℝ/‖x‖^3| ≤
        C * (volume Ω).toReal * R^2 / ‖x‖^3 := by
  refine ⟨3, ?_⟩
  intro x hx
  rw [coulombPotentialReal_remainder_integral Ω R hΩm hΩ x]
  have hb : Bornology.IsBounded Ω := isBounded_closedBall.subset hΩ
  have hfinite : volume Ω < ∞ := hb.measure_lt_top
  have hbound : ∀ y ∈ Ω,
      |1/‖x-y‖ - 1/‖x‖ - ⟪x,y⟫_ℝ/‖x‖^3| ≤ 3*R^2/‖x‖^3 := by
    intro y hy
    have hyr : ‖y‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hΩ hy
    calc
      _ ≤ 3*‖y‖^2/‖x‖^3 := kernel_expansion_bound_three R hR x y hyr hx
      _ ≤ 3*R^2/‖x‖^3 := by gcongr
  have hnorm := norm_setIntegral_le_of_norm_le_const hfinite (f := fun y : E₃ =>
    1/‖x-y‖ - 1/‖x‖ - ⟪x,y⟫_ℝ/‖x‖^3) (by
      intro y hy
      rw [Real.norm_eq_abs]
      exact hbound y hy)
  rw [Real.norm_eq_abs] at hnorm
  calc
    _ ≤ (3*R^2/‖x‖^3)*(volume Ω).toReal := hnorm
    _ = 3*(volume Ω).toReal*R^2/‖x‖^3 := by ring

/-- The existing bounded-set regularity theorem supplies the genuine gradient. -/
lemma gradient_coulombPotentialReal (Ω : Set E₃) (R : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R) (x : E₃) :
    gradient (coulombPotentialReal Ω) x =
      ∫ y in Ω, -((‖x-y‖^3)⁻¹ • (x-y)) := by
  have hb : Bornology.IsBounded Ω := isBounded_closedBall.subset hΩ
  have hfinite : volume Ω < ∞ := hb.measure_lt_top
  have heq : coulombPotentialReal Ω = fun a => (coulombPotential Ω a).toReal := by
    funext a
    rw [coulombPotentialReal_eq_setIntegral Ω hΩm a,
      coulombPotential_toReal Ω hfinite a]
    simp only [one_div]
  rw [heq]
  simpa only [neg_smul] using gradient_coulombPotential_of_isBounded hb x

private lemma coulombPotentialReal_gradient_remainder_integral (Ω : Set E₃) (R : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R) (x : E₃) :
    gradient (coulombPotentialReal Ω) x -
        (-(((volume Ω).toReal * (‖x‖^3)⁻¹) • x)) -
        ((‖x‖^3)⁻¹ • (∫ y in Ω, y) -
          (3*⟪∫ y in Ω, y, x⟫_ℝ*(‖x‖^5)⁻¹) • x) =
      ∫ y in Ω, (-((‖x-y‖^3)⁻¹ • (x-y)) -
        (-((‖x‖^3)⁻¹ • x)) -
        ((‖x‖^3)⁻¹ • y - (3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) • x)) := by
  have hb : Bornology.IsBounded Ω := isBounded_closedBall.subset hΩ
  have hfinite : volume Ω < ∞ := hb.measure_lt_top
  have hi : IntegrableOn (fun y : E₃ => y) Ω := integrableOn_id_bounded Ω R hΩm hΩ
  have hg : IntegrableOn (fun y : E₃ => -((‖x-y‖^3)⁻¹ • (x-y))) Ω := by
    simpa only [neg_smul] using integrableOn_newtonGradientKernel Ω hfinite x
  have hc : IntegrableOn (fun _ : E₃ => -((‖x‖^3)⁻¹ • x)) Ω :=
    integrableOn_const hfinite.ne
  have hh0 : IntegrableOn (fun y : E₃ => ⟪x,y⟫_ℝ) Ω := by
    exact (innerSL ℝ x).integrable_comp hi
  have hh1 : IntegrableOn (fun y : E₃ => 3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) Ω := by
    have heq : (fun y : E₃ => 3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) =
        (fun y => (3*(‖x‖^5)⁻¹)*⟪x,y⟫_ℝ) := by
      funext y
      ring
    rw [heq]
    exact hh0.const_mul _
  have hiy : IntegrableOn (fun y : E₃ => (‖x‖^3)⁻¹ • y) Ω := by
    change Integrable ((‖x‖^3)⁻¹ • (fun y : E₃ => y)) (volume.restrict Ω)
    exact hi.smul _
  have hh : IntegrableOn (fun y : E₃ =>
      (‖x‖^3)⁻¹ • y - (3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) • x) Ω :=
    hiy.sub (hh1.smul_const x)
  have hinter : (∫ y in Ω, ⟪x,y⟫_ℝ) = ⟪x, ∫ y in Ω, y⟫_ℝ := by
    simpa only [innerSL_apply_apply] using (innerSL ℝ x).integral_comp_comm hi
  have hsub : (∫ y in Ω, -((‖x-y‖^3)⁻¹ • (x-y)) -
      (-((‖x‖^3)⁻¹ • x))) =
      (∫ y in Ω, -((‖x-y‖^3)⁻¹ • (x-y))) -
      (∫ y in Ω, -((‖x‖^3)⁻¹ • x)) := by
    simpa only [Pi.sub_apply] using integral_sub hg hc
  have hsplit : (∫ y in Ω, (-((‖x-y‖^3)⁻¹ • (x-y)) -
      (-((‖x‖^3)⁻¹ • x)) -
      ((‖x‖^3)⁻¹ • y - (3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) • x))) =
      (∫ y in Ω, -((‖x-y‖^3)⁻¹ • (x-y))) -
      (∫ y in Ω, -((‖x‖^3)⁻¹ • x)) -
      (∫ y in Ω, ((‖x‖^3)⁻¹ • y -
        (3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) • x)) := by
    simpa only [Pi.sub_apply, hsub] using integral_sub (hg.sub hc) hh
  rw [hsplit, ← gradient_coulombPotentialReal Ω R hΩm hΩ x]
  rw [integral_sub hiy (hh1.smul_const x)]
  have hmass : (∫ y in Ω, -((‖x‖^3)⁻¹ • x)) =
      -(((volume Ω).toReal*(‖x‖^3)⁻¹) • x) := by
    rw [setIntegral_const, measureReal_def]
    module
  have hmoment : (∫ y in Ω, (‖x‖^3)⁻¹ • y) =
      (‖x‖^3)⁻¹ • (∫ y in Ω, y) := integral_smul _ _
  have hdipole : (∫ y in Ω, (3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) • x) =
      (3*⟪∫ y in Ω, y, x⟫_ℝ*(‖x‖^5)⁻¹) • x := by
    rw [integral_smul_const]
    simp only [integral_const_mul, integral_mul_const, hinter]
    rw [real_inner_comm]
  rw [hmass, hmoment, hdipole]

/-- Differentiated multipole expansion of the real Coulomb potential. -/
theorem coulombPotentialReal_gradient_expansion (Ω : Set E₃) (R : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R) (hR : 0 < R) :
    ∃ C : ℝ, ∀ x : E₃, 2*R < ‖x‖ →
      ‖gradient (coulombPotentialReal Ω) x -
          (-(((volume Ω).toReal * (‖x‖^3)⁻¹) • x)) -
          ((‖x‖^3)⁻¹ • (∫ y in Ω, y) -
            (3*⟪∫ y in Ω, y, x⟫_ℝ*(‖x‖^5)⁻¹) • x)‖ ≤
        C * (volume Ω).toReal * R^2 / ‖x‖^4 := by
  refine ⟨39, ?_⟩
  intro x hx
  rw [coulombPotentialReal_gradient_remainder_integral Ω R hΩm hΩ x]
  have hb : Bornology.IsBounded Ω := isBounded_closedBall.subset hΩ
  have hfinite : volume Ω < ∞ := hb.measure_lt_top
  have hbound : ∀ y ∈ Ω,
      ‖-((‖x-y‖^3)⁻¹ • (x-y)) - (-((‖x‖^3)⁻¹ • x)) -
          ((‖x‖^3)⁻¹ • y - (3*⟪x,y⟫_ℝ*(‖x‖^5)⁻¹) • x)‖ ≤
        39*R^2/‖x‖^4 := by
    intro y hy
    have hyr : ‖y‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hΩ hy
    calc
      _ ≤ 39*‖y‖^2/‖x‖^4 :=
        kernel_gradient_expansion_bound_thirtynine R hR x y hyr hx
      _ ≤ 39*R^2/‖x‖^4 := by gcongr
  have hnorm := norm_setIntegral_le_of_norm_le_const hfinite hbound
  calc
    _ ≤ (39*R^2/‖x‖^4)*(volume Ω).toReal := hnorm
    _ = 39*(volume Ω).toReal*R^2/‖x‖^4 := by ring

end LiquidDrop

namespace LiquidDrop
open Filter
open scoped Topology
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The outer boundary term, with the radial derivative evaluated on radius `R`. -/
def outerWronskian (u v : E₃ → ℝ) (R : ℝ) : ℝ :=
  ∫ x in sphere (0 : E₃) R,
    (v x * (inner ℝ (gradient u x) x / R) -
      u x * (inner ℝ (gradient v x) x / R)) ∂(hausdorffMeasure2 3)

private lemma div_pow_succ_le {a r : ℝ} (ha : 0 ≤ a) (hr : 1 ≤ r) (n : ℕ) :
    a / r ^ (n + 1) ≤ a / r ^ n := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  apply div_le_div_of_nonneg_left ha (by positivity)
  calc
    r ^ n = r ^ n * 1 := by ring
    _ ≤ r ^ n * r := by gcongr
    _ = r ^ (n + 1) := (pow_succ _ _).symm

/-- The first moment is bounded by mass times the containing radius. -/
lemma norm_firstMoment_le (Ω : Set E₃) (R₀ : ℝ)
    (hΩ : Ω ⊆ closedBall 0 R₀) :
    ‖∫ y in Ω, y‖ ≤ (volume Ω).toReal * R₀ := by
  have hb : Bornology.IsBounded Ω := isBounded_closedBall.subset hΩ
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) hb.measure_lt_top
    (f := fun y : E₃ => y) (C := R₀) (by
      intro y hy
      simpa only [mem_closedBall, dist_zero_right] using hΩ hy)
  simpa only [measureReal_def, mul_comm] using h

/-- The proved multipole estimates imply the weaker monopole estimates used
in the Wronskian cancellation. -/
lemma coulombPotentialReal_monopole_bounds (Ω : Set E₃) (R₀ : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R₀) (hR₀ : 0 < R₀) :
    ∃ M ≥ 0, ∀ x : E₃, max (2 * R₀) 1 < ‖x‖ →
      |coulombPotentialReal Ω x - (volume Ω).toReal / ‖x‖| ≤ M / ‖x‖ ^ 2 ∧
      ‖gradient (coulombPotentialReal Ω) x +
        ((volume Ω).toReal / ‖x‖ ^ 3) • x‖ ≤ M / ‖x‖ ^ 3 := by
  obtain ⟨A, hA⟩ := coulombPotentialReal_expansion Ω R₀ hΩm hΩ hR₀
  obtain ⟨B, hB⟩ := coulombPotentialReal_gradient_expansion Ω R₀ hΩm hΩ hR₀
  let V := (volume Ω).toReal
  let b := ∫ y in Ω, y
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hb : ‖b‖ ≤ V * R₀ := norm_firstMoment_le Ω R₀ hΩ
  let M := |A| * V * R₀ ^ 2 + |B| * V * R₀ ^ 2 + 4 * V * R₀
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hx₀ : 2 * R₀ < ‖x‖ := lt_of_le_of_lt (le_max_left _ _) hx
  have hx₁ : 1 ≤ ‖x‖ := (lt_of_le_of_lt (le_max_right _ _) hx).le
  have hxpos : 0 < ‖x‖ := by linarith
  have hh : |⟪b, x⟫_ℝ| ≤ V * R₀ * ‖x‖ :=
    (abs_real_inner_le_norm _ _).trans (by gcongr)
  have hscalar : |⟪b, x⟫_ℝ / ‖x‖ ^ 3| ≤ V * R₀ / ‖x‖ ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos hxpos 3)]
    calc
      _ ≤ (V * R₀ * ‖x‖) / ‖x‖ ^ 3 := by gcongr
      _ = _ := by field_simp
  have hdipole : ‖(‖x‖ ^ 3)⁻¹ • b -
      (3 * ⟪b, x⟫_ℝ * (‖x‖ ^ 5)⁻¹) • x‖ ≤ 4 * V * R₀ / ‖x‖ ^ 3 := by
    calc
      _ ≤ ‖(‖x‖ ^ 3)⁻¹ • b‖ + ‖(3 * ⟪b, x⟫_ℝ * (‖x‖ ^ 5)⁻¹) • x‖ :=
        norm_sub_le _ _
      _ = (‖x‖ ^ 3)⁻¹ * ‖b‖ + (3 * |⟪b, x⟫_ℝ| * (‖x‖ ^ 5)⁻¹) * ‖x‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ ≤ (‖x‖ ^ 3)⁻¹ * (V * R₀) +
          (3 * (V * R₀ * ‖x‖) * (‖x‖ ^ 5)⁻¹) * ‖x‖ := by gcongr
      _ = _ := by field_simp; ring
  constructor
  · calc
      _ ≤ |coulombPotentialReal Ω x - V / ‖x‖ - ⟪b, x⟫_ℝ / ‖x‖ ^ 3| +
          |⟪b, x⟫_ℝ / ‖x‖ ^ 3| := by
        have h := abs_add_le
          (coulombPotentialReal Ω x - V / ‖x‖ - ⟪b, x⟫_ℝ / ‖x‖ ^ 3)
          (⟪b, x⟫_ℝ / ‖x‖ ^ 3)
        convert h using 1
        all_goals congr 1
        all_goals dsimp [V]
        all_goals ring
      _ ≤ |A| * V * R₀ ^ 2 / ‖x‖ ^ 3 + V * R₀ / ‖x‖ ^ 2 := by
        gcongr
        exact (hA x hx₀).trans (by dsimp [V]; gcongr; exact le_abs_self A)
      _ ≤ (|A| * V * R₀ ^ 2 + V * R₀) / ‖x‖ ^ 2 := by
        rw [add_div]
        exact add_le_add_left (div_pow_succ_le (a := |A| * V * R₀ ^ 2) (by positivity) hx₁ 2) _
      _ ≤ M / ‖x‖ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        dsimp [M]
        have hnonneg : 0 ≤ |B| * V * R₀ ^ 2 := by positivity
        have hmass : 0 ≤ V * R₀ := by positivity
        nlinarith
  · have heq : gradient (coulombPotentialReal Ω) x + (V / ‖x‖ ^ 3) • x =
        (gradient (coulombPotentialReal Ω) x - (-((V * (‖x‖ ^ 3)⁻¹) • x)) -
          ((‖x‖ ^ 3)⁻¹ • b - (3 * ⟪b,x⟫_ℝ * (‖x‖ ^ 5)⁻¹) • x)) +
        ((‖x‖ ^ 3)⁻¹ • b - (3 * ⟪b,x⟫_ℝ * (‖x‖ ^ 5)⁻¹) • x) := by
        simp [div_eq_mul_inv]
    rw [heq]
    calc
      _ ≤ ‖gradient (coulombPotentialReal Ω) x - (-((V * (‖x‖ ^ 3)⁻¹) • x)) -
          ((‖x‖ ^ 3)⁻¹ • b - (3 * ⟪b,x⟫_ℝ * (‖x‖ ^ 5)⁻¹) • x)‖ +
          ‖(‖x‖ ^ 3)⁻¹ • b - (3 * ⟪b,x⟫_ℝ * (‖x‖ ^ 5)⁻¹) • x‖ := norm_add_le _ _
      _ ≤ |B| * V * R₀ ^ 2 / ‖x‖ ^ 4 + 4 * V * R₀ / ‖x‖ ^ 3 := by
        gcongr
        exact (hB x hx₀).trans (by dsimp [V]; gcongr; exact le_abs_self B)
      _ ≤ (|B| * V * R₀ ^ 2 + 4 * V * R₀) / ‖x‖ ^ 3 := by
        rw [add_div]
        exact add_le_add_left (div_pow_succ_le (a := |B| * V * R₀ ^ 2) (by positivity) hx₁ 3) _
      _ ≤ M / ‖x‖ ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        dsimp [M]
        have hnonneg : 0 ≤ |A| * V * R₀ ^ 2 := by positivity
        linarith


private lemma radial_error_bound (f : E₃ → ℝ) (C M R : ℝ) (x : E₃)
    (hR : 0 < R) (hx : ‖x‖ = R)
    (h : ‖gradient f x + (C / R ^ 3) • x‖ ≤ M / R ^ 3) :
    |inner ℝ (gradient f x) x / R + C / R ^ 2| ≤ M / R ^ 3 := by
  have heq : inner ℝ (gradient f x) x / R + C / R ^ 2 =
      inner ℝ (gradient f x + (C / R ^ 3) • x) x / R := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hx]
    field_simp
  rw [heq, abs_div, abs_of_pos hR]
  calc
    _ ≤ (‖gradient f x + (C / R ^ 3) • x‖ * R) / R := by
      gcongr
      simpa only [hx] using abs_real_inner_le_norm (gradient f x + (C / R ^ 3) • x) x
    _ = ‖gradient f x + (C / R ^ 3) • x‖ := mul_div_cancel_right₀ _ hR.ne'
    _ ≤ M / R ^ 3 := h

private lemma scalar_wronskian_bound (u v du dv C V A B R : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hu : |u - C / R| ≤ A / R ^ 2) (hv : |v - V / R| ≤ B / R ^ 2)
    (hdu : |du + C / R ^ 2| ≤ A / R ^ 3)
    (hdv : |dv + V / R ^ 2| ≤ B / R ^ 3) :
    |v * du - u * dv| ≤
      (B * (|C| + A) + |V| * A + A * (|V| + B) + |C| * B) / R ^ 4 := by
  have hRp : 0 < R := by linarith
  have hdu' : |du| ≤ (|C| + A) / R ^ 2 := by
    calc
      _ ≤ |du + C / R ^ 2| + |C / R ^ 2| := by
        have h := abs_sub (du + C / R ^ 2) (C / R ^ 2)
        convert h using 1
        all_goals congr 1
        all_goals ring
      _ ≤ A / R ^ 3 + |C| / R ^ 2 := by
        rw [abs_div, abs_of_pos (pow_pos hRp 2)]
        gcongr
      _ ≤ A / R ^ 2 + |C| / R ^ 2 :=
        add_le_add_left (div_pow_succ_le hA hR 2) _
      _ = _ := by ring
  have hdv' : |dv| ≤ (|V| + B) / R ^ 2 := by
    calc
      _ ≤ |dv + V / R ^ 2| + |V / R ^ 2| := by
        have h := abs_sub (dv + V / R ^ 2) (V / R ^ 2)
        convert h using 1
        all_goals congr 1
        all_goals ring
      _ ≤ B / R ^ 3 + |V| / R ^ 2 := by
        rw [abs_div, abs_of_pos (pow_pos hRp 2)]
        gcongr
      _ ≤ B / R ^ 2 + |V| / R ^ 2 :=
        add_le_add_left (div_pow_succ_le hB hR 2) _
      _ = _ := by ring
  have heq : v * du - u * dv =
      (v - V / R) * du + (V / R) * (du + C / R ^ 2) -
        (u - C / R) * dv - (C / R) * (dv + V / R ^ 2) := by ring
  rw [heq]
  calc
    _ ≤ (|(v - V / R) * du + (V / R) * (du + C / R ^ 2)| +
        |(u - C / R) * dv|) + |(C / R) * (dv + V / R ^ 2)| :=
      (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ ((|(v - V / R) * du| + |(V / R) * (du + C / R ^ 2)|) +
        |(u - C / R) * dv|) + |(C / R) * (dv + V / R ^ 2)| := by
      gcongr
      exact abs_add_le _ _
    _ = ((|v - V / R| * |du| + (|V| / R) * |du + C / R ^ 2|) +
        |u - C / R| * |dv|) + (|C| / R) * |dv + V / R ^ 2| := by
      simp only [abs_mul, abs_div, abs_of_pos hRp]
    _ ≤ ((B / R ^ 2 * ((|C| + A) / R ^ 2) + (|V| / R) * (A / R ^ 3)) +
        A / R ^ 2 * ((|V| + B) / R ^ 2)) + (|C| / R) * (B / R ^ 3) := by
      gcongr
    _ = _ := by ring

/-- Blueprint `lem:wronskian`: the Kelvin expansion is the named external input. -/
theorem wronskian_bound_of_kelvin (Ω : Set E₃) (R₀ : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R₀) (hR₀ : 0 < R₀)
    (u : E₃ → ℝ) (C : ℝ)
    (hu_of_kelvin : ∃ M R₁, ∀ x : E₃, R₁ < ‖x‖ →
      |u x - C / ‖x‖| ≤ M / ‖x‖ ^ 2 ∧
        ‖gradient u x + (C / ‖x‖ ^ 3) • x‖ ≤ M / ‖x‖ ^ 3) :
    ∃ M R₂, ∀ R, R₂ < R →
      |outerWronskian u (coulombPotentialReal Ω) R| ≤ M / R ^ 2 := by
  obtain ⟨A, R₁, hu⟩ := hu_of_kelvin
  obtain ⟨B, hB, hv⟩ := coulombPotentialReal_monopole_bounds Ω R₀ hΩm hΩ hR₀
  let V := (volume Ω).toReal
  let K := B * (|C| + |A|) + |V| * |A| + |A| * (|V| + B) + |C| * B
  refine ⟨K * (4 * Real.pi), max R₁ (max (2 * R₀) 1), ?_⟩
  intro R hR
  have hR₁ : R₁ < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hR₂ : max (2 * R₀) 1 < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRone : 1 ≤ R := (lt_of_le_of_lt (le_max_right _ _) hR₂).le
  have hRpos : 0 < R := by linarith
  have hpoint : ∀ x ∈ sphere (0 : E₃) R,
      ‖coulombPotentialReal Ω x * (inner ℝ (gradient u x) x / R) -
        u x * (inner ℝ (gradient (coulombPotentialReal Ω) x) x / R)‖ ≤ K / R ^ 4 := by
    intro x hx
    have hxn : ‖x‖ = R := mem_sphere_zero_iff_norm.mp hx
    have hux := hu x (by simpa only [hxn] using hR₁)
    have hvx := hv x (by simpa only [hxn] using hR₂)
    rw [hxn] at hux hvx
    have hu₀ : |u x - C / R| ≤ |A| / R ^ 2 := hux.1.trans (by gcongr; exact le_abs_self A)
    have hu₁ : ‖gradient u x + (C / R ^ 3) • x‖ ≤ |A| / R ^ 3 :=
      hux.2.trans (by gcongr; exact le_abs_self A)
    rw [Real.norm_eq_abs]
    exact scalar_wronskian_bound (u x) (coulombPotentialReal Ω x)
      (inner ℝ (gradient u x) x / R)
      (inner ℝ (gradient (coulombPotentialReal Ω) x) x / R)
      C V |A| B R (abs_nonneg _) hB hRone hu₀ hvx.1
      (radial_error_bound u C |A| R x hRpos hxn hu₁)
      (radial_error_bound (coulombPotentialReal Ω) V B R x hRpos hxn hvx.2)
  have harea := hausdorffMeasure2_sphere_zero hRpos
  have hfinite : hausdorffMeasure2 3 (sphere (0 : E₃) R) < ∞ := by
    rw [harea]
    exact ENNReal.ofReal_lt_top
  have hi := norm_setIntegral_le_of_norm_le_const hfinite hpoint
  rw [measureReal_def, harea, ENNReal.toReal_ofReal (by positivity)] at hi
  change ‖outerWronskian u (coulombPotentialReal Ω) R‖ ≤ _ at hi
  rw [Real.norm_eq_abs] at hi
  calc
    _ ≤ K / R ^ 4 * (4 * Real.pi * R ^ 2) := hi
    _ = K * (4 * Real.pi) / R ^ 2 := by field_simp


/-- The quantitative Wronskian bound implies that the outer boundary term vanishes. -/
theorem wronskian_tendsto_zero_of_kelvin (Ω : Set E₃) (R₀ : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R₀) (hR₀ : 0 < R₀)
    (u : E₃ → ℝ) (C : ℝ)
    (hu_of_kelvin : ∃ M R₁, ∀ x : E₃, R₁ < ‖x‖ →
      |u x - C / ‖x‖| ≤ M / ‖x‖ ^ 2 ∧
        ‖gradient u x + (C / ‖x‖ ^ 3) • x‖ ≤ M / ‖x‖ ^ 3) :
    Tendsto (outerWronskian u (coulombPotentialReal Ω)) atTop (𝓝 0) := by
  obtain ⟨M, R₂, h⟩ := wronskian_bound_of_kelvin Ω R₀ hΩm hΩ hR₀ u C hu_of_kelvin
  apply squeeze_zero_norm' (a := fun R : ℝ => M / R ^ 2)
  · filter_upwards [eventually_gt_atTop R₂] with R hR
    simpa only [Real.norm_eq_abs] using h R hR
  · exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_div_atTop M

/-- Blueprint `thm:green-identity`, conditional on Green's second identity from
`thm:W11-gauss-green`, vanishing of the outer term, and `lem:interior-flux`.
The measure models the boundary, with `w = |∇u|`, `vb = v`, and `dv = ∂ν v`. -/
theorem green_identity_of_gauss_green {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w vb dv : X → ℝ) (W : ℝ → ℝ) (V : ℝ)
    (hgreen_second_of_W11_gauss_green : ∀ᶠ R in atTop,
      (∫ p, (vb p * w p + dv p) ∂μ) + W R = 0)
    (hW : Tendsto W atTop (𝓝 0))
    (hflux : ∫ p, dv p ∂μ = -4 * Real.pi * V)
    (hvw : Integrable (fun p => vb p * w p) μ) (hdv : Integrable dv μ) :
    (4 * Real.pi)⁻¹ * (∫ p, vb p * w p ∂μ) = V := by
  have hlim : Tendsto (fun R => (∫ p, (vb p * w p + dv p) ∂μ) + W R)
      atTop (𝓝 (∫ p, (vb p * w p + dv p) ∂μ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hW
  have hlimzero : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop
      (𝓝 (∫ p, (vb p * w p + dv p) ∂μ)) :=
    hlim.congr' hgreen_second_of_W11_gauss_green
  have hzero : (∫ p, (vb p * w p + dv p) ∂μ) = 0 :=
    tendsto_nhds_unique hlimzero tendsto_const_nhds
  rw [integral_add hvw hdv, hflux] at hzero
  have hmass : (∫ p, vb p * w p ∂μ) = (4 * Real.pi) * V := by linarith
  rw [hmass, ← mul_assoc, inv_mul_cancel₀ (by positivity : 4 * Real.pi ≠ 0), one_mul]

/-- The partial Coulomb--capacity identity uses the proved Wronskian limit.
The Kelvin expansion, second Green identity, and interior flux remain explicit
named hypotheses; no geometric boundary regularity is asserted here. -/
theorem green_identity_of_kelvin_of_gauss_green (Ω : Set E₃) (R₀ : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R₀) (hR₀ : 0 < R₀)
    (u : E₃ → ℝ) (C : ℝ)
    (hu_of_kelvin : ∃ M R₁, ∀ x : E₃, R₁ < ‖x‖ →
      |u x - C / ‖x‖| ≤ M / ‖x‖ ^ 2 ∧
        ‖gradient u x + (C / ‖x‖ ^ 3) • x‖ ≤ M / ‖x‖ ^ 3)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (w vb dv : X → ℝ)
    (hgreen_second_of_W11_gauss_green : ∀ᶠ R in atTop,
      (∫ p, (vb p * w p + dv p) ∂μ) +
        outerWronskian u (coulombPotentialReal Ω) R = 0)
    (hflux : ∫ p, dv p ∂μ = -4 * Real.pi * (volume Ω).toReal)
    (hvw : Integrable (fun p => vb p * w p) μ) (hdv : Integrable dv μ) :
    (4 * Real.pi)⁻¹ * (∫ p, vb p * w p ∂μ) = (volume Ω).toReal := by
  exact green_identity_of_gauss_green μ w vb dv
    (outerWronskian u (coulombPotentialReal Ω)) (volume Ω).toReal
    hgreen_second_of_W11_gauss_green
    (wronskian_tendsto_zero_of_kelvin Ω R₀ hΩm hΩ hR₀ u C hu_of_kelvin)
    hflux hvw hdv

end LiquidDrop

namespace LiquidDrop
open Filter
open scoped Topology
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private lemma interior_density_mass_limit {D : Set E₃} (hD : IsOpen D)
    {y : E₃} (hy : y ∈ D) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hp : ∀ j, 0 < ε j) :
    Tendsto (fun j => ∫ x in D, newtonApproximationDensity (ε j) (x - y))
      atTop (𝓝 (4 * Real.pi)) := by
  have he (j : ℕ) :
      (∫ x in D, newtonApproximationDensity (ε j) (x - y)) =
        ∫ x, newtonApproximationDensity 1 x *
          D.indicator (fun _ => (1 : ℝ)) (ε j • x + y) := by
    rw [← integral_newtonApproximationDensity_mul (hp j)
      (fun x => D.indicator (fun _ => (1 : ℝ)) (x + y))]
    rw [← integral_indicator hD.measurableSet]
    have ht := integral_add_right_eq_self (μ := (volume : Measure E₃))
      (D.indicator (fun x => newtonApproximationDensity (ε j) (x - y))) y
    rw [← ht]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x + y ∈ D <;> simp [hx]
  simp_rw [he]
  rw [← integral_newtonApproximationDensity_one]
  apply tendsto_integral_of_dominated_convergence (newtonApproximationDensity 1)
  · intro j
    have hm : Measurable (fun x : E₃ => D.indicator (fun _ => (1 : ℝ)) (ε j • x + y)) :=
      (measurable_const.indicator hD.measurableSet).comp (by fun_prop)
    exact ((continuous_newtonApproximationDensity (by norm_num : (0 : ℝ) < 1)).measurable.mul
      hm).aestronglyMeasurable
  · exact integrable_newtonApproximationDensity_one
  · intro j
    filter_upwards [] with x
    by_cases hx : ε j • x + y ∈ D
    · simp [hx, Real.norm_of_nonneg (newtonApproximationDensity_nonneg 1 x)]
    · simp [hx, newtonApproximationDensity_nonneg]
  · filter_upwards [] with x
    have ht : Tendsto (fun j => ε j • x + y) atTop (𝓝 y) := by
      simpa using (hε.smul_const x).add_const y
    have hm : ∀ᶠ j in atTop, ε j • x + y ∈ D := ht.eventually (hD.mem_nhds hy)
    apply tendsto_const_nhds.congr'
    filter_upwards [hm] with j hj
    simp [hj]

private lemma interior_laplacian_translate (u : E₃ → ℝ) (y x : E₃) :
    laplacianN (fun z => u (z - y)) x = laplacianN u (x - y) := by
  have hd (f : E₃ → ℝ) (i : Fin 3) :
      poissonCoordinateDerivative i (fun z => f (z - y)) =
        fun z => poissonCoordinateDerivative i f (z - y) := by
    funext z
    simp only [poissonCoordinateDerivative, sub_eq_add_neg, fderiv_comp_add_right]
  simp only [laplacianN, hd]

/-- Gauss law for one interior point charge, with the outward C¹ normal. -/
theorem point_charge_flux (D : Set E₃) (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    (y : E₃) (hy : y ∈ D) :
    (∫ x, inner ℝ (-((‖x - y‖ ^ 3)⁻¹ • (x - y))) (hC1.outwardNormal x)
      ∂(hausdorffMeasure2 3).restrict (frontier D)) = -4 * Real.pi := by
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hp : ∀ j, 0 < ε j := fun j => by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f (j : ℕ) (x : E₃) := regularizedNewtonKernel (ε j) (x - y)
  have hc (j) : ContDiff ℝ 2 (f j) :=
    ((contDiff_regularizedNewtonKernel (hp j)).of_le (by simp)).comp
      (contDiff_id.sub contDiff_const)
  have he (j) :
      (∫ x, inner ℝ (gradient (f j) x) (hC1.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict (frontier D)) =
      -(∫ x in D, newtonApproximationDensity (ε j) (x - y)) := by
    rw [← classical_gauss_green hD hbD hC1 (contDiff_gradient_of_contDiff_succ (hc j))]
    change (∫ x in D, divergenceN (gradient (f j)) x) = _
    simp_rw [← laplacianN_eq_divergenceN_gradient (hc j)]
    simp only [f, interior_laplacian_translate, laplacianN_regularizedNewtonKernel (hp j),
      integral_neg]
  have hv := (interior_density_mass_limit hD hy hε hp).neg
  have hs : Tendsto (fun j => ∫ x, inner ℝ (gradient (f j) x) (hC1.outwardNormal x)
      ∂(hausdorffMeasure2 3).restrict (frontier D)) atTop
      (𝓝 (∫ x, inner ℝ (classicalNewtonGradient (x - y)) (hC1.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict (frontier D))) := by
    let μ := (hausdorffMeasure2 3).restrict (frontier D)
    let : IsFiniteMeasure μ := finite_boundary_area hD hbD hC1
    obtain ⟨δ, hδ, hd⟩ := exists_pos_boundary_distance hD hy
    apply tendsto_integral_of_dominated_convergence (fun _ => (δ ^ 2)⁻¹)
    · intro j
      have hg := (contDiff_gradient_of_contDiff_succ (r := 1) (hc j)).continuous
      exact hg.aestronglyMeasurable.inner (hC1.aestronglyMeasurable_outwardNormal μ)
    · exact integrable_const _
    · intro j
      filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
      apply (norm_inner_le_norm _ _).trans
      rw [hC1.norm_outwardNormal hx, mul_one]
      calc
        ‖gradient (f j) x‖ = ‖regularizedNewtonDerivative (ε j) (x - y)‖ := by
          change ‖gradient (fun z => regularizedNewtonKernel (ε j) (z - y)) x‖ = _
          rw [gradient_regularizedNewtonKernel_sub (hp j), LinearIsometryEquiv.norm_map]
        _ ≤ (‖x - y‖ ^ 2)⁻¹ := (norm_regularizedNewtonDerivative_le (hp j) (x - y)).2
        _ ≤ (δ ^ 2)⁻¹ := inv_anti₀ (by positivity) (by gcongr; exact hd x hx)
    · filter_upwards [] with x
      exact (tendsto_gradient_regularizedNewtonKernel_sub hε hp x y).inner tendsto_const_nhds
  have hlim := tendsto_nhds_unique hs (hv.congr' (Eventually.of_forall fun j => (he j).symm))
  simpa only [classicalNewtonGradient, neg_smul, neg_mul] using hlim

end LiquidDrop

namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private lemma integrable_interior_flux_kernel (Ω D : Set E₃)
    (hΩ : volume Ω < ∞) (hD : IsOpen D) (hbD : Bornology.IsBounded D)
    (hC1 : HasC1Boundary D) :
    Integrable (fun p : E₃ × E₃ =>
      inner ℝ (-((‖p.1 - p.2‖ ^ 3)⁻¹ • (p.1 - p.2))) (hC1.outwardNormal p.1))
      (((hausdorffMeasure2 3).restrict (frontier D)).prod (volume.restrict Ω)) := by
  let μ := (hausdorffMeasure2 3).restrict (frontier D)
  let : IsFiniteMeasure μ := finite_boundary_area hD hbD hC1
  have hm : Measurable (fun p : E₃ × E₃ => ENNReal.ofReal ((‖p.1 - p.2‖ ^ 2)⁻¹)) := by
    fun_prop
  have hfin : (∫⁻ p, ENNReal.ofReal ((‖p.1 - p.2‖ ^ 2)⁻¹)
      ∂μ.prod (volume.restrict Ω)) < ∞ := by
    rw [lintegral_prod _ hm.aemeasurable]
    apply lt_of_le_of_lt (lintegral_mono fun x => lintegral_inv_norm_sq_le Ω x)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top
      (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hΩ⟩) (measure_lt_top μ Set.univ)
  have hi : Integrable (fun p : E₃ × E₃ => (‖p.1 - p.2‖ ^ 2)⁻¹)
      (μ.prod (volume.restrict Ω)) := by
    have ht := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin.ne
    simpa only [ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg _))] using! ht
  have hpair : Measurable (fun p : E₃ × E₃ =>
      inner ℝ (-((‖p.1 - p.2‖ ^ 3)⁻¹ • (p.1 - p.2))) (hC1.outwardNormal p.1)) := by
    apply Measurable.inner
    · fun_prop
    · exact hC1.measurable_outwardNormal.comp measurable_fst
  apply hi.mono' hpair.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    calc
      _ ≤ ‖-((‖p.1 - p.2‖ ^ 3)⁻¹ • (p.1 - p.2))‖ * ‖hC1.outwardNormal p.1‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖-((‖p.1 - p.2‖ ^ 3)⁻¹ • (p.1 - p.2))‖ * 1 := by
        gcongr
        exact hC1.norm_outwardNormal_le p.1
      _ = (‖p.1 - p.2‖ ^ 2)⁻¹ := by
        rw [mul_one, ← neg_smul]
        change ‖classicalNewtonGradient (p.1 - p.2)‖ = _
        rw [← (toDual ℝ E₃).norm_map, toDual_classicalNewtonGradient,
          norm_newtonDerivativeKernel]

/-- Blueprint `lem:interior-flux`: the Coulomb flux through the enclosing C¹ boundary. -/
theorem interior_flux (Ω D : Set E₃) (R₀ : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R₀)
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    (hΩD : volume (Ω \ D) = 0) :
    (∫ x, inner ℝ (gradient (coulombPotentialReal Ω) x) (hC1.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict (frontier D)) = -4 * Real.pi * (volume Ω).toReal := by
  let μ := (hausdorffMeasure2 3).restrict (frontier D)
  let : IsFiniteMeasure μ := finite_boundary_area hD hbD hC1
  have hfinite : volume Ω < ∞ := (isBounded_closedBall.subset hΩ).measure_lt_top
  have hmem : ∀ᵐ y ∂volume.restrict Ω, y ∈ D := by
    rw [ae_iff]
    change (volume.restrict Ω) Dᶜ = 0
    rw [Measure.restrict_apply hD.measurableSet.compl]
    simpa only [Set.sdiff_eq, Set.inter_comm] using hΩD
  calc
    _ = ∫ x, (∫ y in Ω,
        inner ℝ (-((‖x - y‖ ^ 3)⁻¹ • (x - y))) (hC1.outwardNormal x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [gradient_coulombPotentialReal Ω R₀ hΩm hΩ]
      have hi : IntegrableOn (fun y : E₃ => -((‖x - y‖ ^ 3)⁻¹ • (x - y))) Ω := by
        simpa only [neg_smul] using integrableOn_newtonGradientKernel Ω hfinite x
      simpa only [real_inner_comm] using (integral_inner hi (hC1.outwardNormal x)).symm
    _ = ∫ y in Ω, ∫ x,
        inner ℝ (-((‖x - y‖ ^ 3)⁻¹ • (x - y))) (hC1.outwardNormal x) ∂μ :=
      integral_integral_swap (integrable_interior_flux_kernel Ω D hfinite hD hbD hC1)
    _ = ∫ _y in Ω, (-4 * Real.pi) := by
      apply integral_congr_ae
      filter_upwards [hmem] with y hy
      exact point_charge_flux D hD hbD hC1 y hy
    _ = _ := by simp [measureReal_def, mul_comm]

end LiquidDrop

namespace LiquidDrop
open Filter
open scoped Topology
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The normal derivative of `v_Ω` is integrable on the boundary of a bounded C¹ domain. -/
lemma integrable_normal_derivative_coulombPotentialReal (Ω D : Set E₃) (R₀ : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R₀)
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D) :
    Integrable
      (fun x => inner ℝ (gradient (coulombPotentialReal Ω) x) (hC1.outwardNormal x))
      ((hausdorffMeasure2 3).restrict (frontier D)) := by
  have hb : Bornology.IsBounded Ω := isBounded_closedBall.subset hΩ
  have heq : coulombPotentialReal Ω = fun a => (coulombPotential Ω a).toReal := by
    funext a
    rw [coulombPotentialReal_eq_setIntegral Ω hΩm a,
      coulombPotential_toReal Ω hb.measure_lt_top a]
    simp only [one_div]
  have hcont : Continuous (gradient (coulombPotentialReal Ω)) := by
    rw [heq]
    exact (InnerProductSpace.toDual ℝ E₃).symm.continuous.comp
      ((contDiff_one_coulombPotential_of_isBounded hb).continuous_fderiv one_ne_zero)
  have : IsFiniteMeasure ((hausdorffMeasure2 3).restrict (frontier D)) :=
    finite_boundary_area hD hbD hC1
  have hK : IsCompact (frontier D) :=
    hbD.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine Integrable.mono' (integrable_const C)
    (hcont.aestronglyMeasurable.inner (hC1.aestronglyMeasurable_outwardNormal _)) ?_
  filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
  calc ‖inner ℝ (gradient (coulombPotentialReal Ω) x) (hC1.outwardNormal x)‖
      ≤ ‖gradient (coulombPotentialReal Ω) x‖ * ‖hC1.outwardNormal x‖ :=
        norm_inner_le_norm _ _
    _ ≤ C * 1 := mul_le_mul (hC x hx) (hC1.norm_outwardNormal_le x) (norm_nonneg _)
        ((norm_nonneg _).trans (hC x hx))
    _ = C := mul_one C

/-- Blueprint `thm:green-identity` (eq:green-identity) on the boundary of `D = int K`.

The interior flux is `interior_flux` (lem:interior-flux) and the outer Wronskian limit is
`wronskian_tendsto_zero_of_kelvin` (lem:wronskian).  The remaining external inputs are named:
`hu_of_kelvin` (the expansion of `u` from lem:kelvin / thm:capacitary-potential),
`hgreen_second_of_W11_gauss_green` (eq:green-second on `B_R \ K`, from thm:W11-gauss-green, with
`w = ∂_{-ν_K} u = |∇u|` on `∂K` as in not:w), and the boundary integrability `hvw` of `v w`.
The hull data `hD hbD hC1 hΩD` are the conclusions of
lem:hull-properties. -/
theorem green_identity (Ω D : Set E₃) (R₀ : ℝ)
    (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ closedBall 0 R₀) (hR₀ : 0 < R₀)
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    (hΩD : volume (Ω \ D) = 0)
    (u : E₃ → ℝ) (C : ℝ)
    (hu_of_kelvin : ∃ M R₁, ∀ x : E₃, R₁ < ‖x‖ →
      |u x - C / ‖x‖| ≤ M / ‖x‖ ^ 2 ∧
        ‖gradient u x + (C / ‖x‖ ^ 3) • x‖ ≤ M / ‖x‖ ^ 3)
    (w : E₃ → ℝ)
    (hgreen_second_of_W11_gauss_green : ∀ᶠ R in atTop,
      (∫ x, (coulombPotentialReal Ω x * w x +
          inner ℝ (gradient (coulombPotentialReal Ω) x) (hC1.outwardNormal x))
          ∂(hausdorffMeasure2 3).restrict (frontier D)) +
        outerWronskian u (coulombPotentialReal Ω) R = 0)
    (hvw : Integrable (fun x => coulombPotentialReal Ω x * w x)
      ((hausdorffMeasure2 3).restrict (frontier D))) :
    (4 * Real.pi)⁻¹ * (∫ x, coulombPotentialReal Ω x * w x
      ∂(hausdorffMeasure2 3).restrict (frontier D)) = (volume Ω).toReal :=
  green_identity_of_kelvin_of_gauss_green Ω R₀ hΩm hΩ hR₀ u C hu_of_kelvin
    ((hausdorffMeasure2 3).restrict (frontier D)) w (coulombPotentialReal Ω)
    (fun x => inner ℝ (gradient (coulombPotentialReal Ω) x) (hC1.outwardNormal x))
    hgreen_second_of_W11_gauss_green
    (interior_flux Ω D R₀ hΩm hΩ hD hbD hC1 hΩD) hvw
    (integrable_normal_derivative_coulombPotentialReal Ω D R₀ hΩm hΩ hD hbD hC1)

end LiquidDrop
