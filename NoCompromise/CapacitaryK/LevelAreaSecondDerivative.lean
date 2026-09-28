import NoCompromise.CapacitaryK.LevelAreaDerivatives

/-!
# Second derivatives of the quotient correction to level area

The area quotient is the square root of one plus the squared tangential-to-radial
ratio of the potential gradient. The estimates below use two derivatives of this
ratio, hence at most three derivatives of the potential and two of the radius.

`levelAreaSecond_remainder_bound_of_components` reduces the desired area Hessian
bound to explicit radial and tangential gradient estimates. The uniform estimates
for these components on capacitary levels, and the full theorem
`capacitary_level_area_derivatives`, are proved in `LevelAreaComponents.lean`.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- The scalar product rule for the second ambient derivative. -/
theorem levelAreaSecond_fderiv_two_mul {a b : E3 → ℝ} {x : E3}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => a y * b y)) x e f =
      a x * fderiv ℝ (fderiv ℝ b) x e f +
        fderiv ℝ a x e * fderiv ℝ b x f +
        fderiv ℝ a x f * fderiv ℝ b x e +
        fderiv ℝ (fderiv ℝ a) x e f * b x := by
  have had := ha.differentiableAt (by norm_num)
  have hbd := hb.differentiableAt (by norm_num)
  have hDa := (ha.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDb := (hb.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDc := ((ha.mul hb).fderiv_right (m := 1)
    (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun z => a z * b z) y f) =ᶠ[𝓝 x]
      (fun y => a y * fderiv ℝ b y f + fderiv ℝ a y f * b y) := by
    filter_upwards [ha.eventually (by norm_num), hb.eventually (by norm_num)] with y hy hz
    change fderiv ℝ (a * b) y f = _
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.mul
      (hz.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    simp [mul_comm]
  have hleft := hDc.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (had.hasFDerivAt.mul
    (hDb.hasFDerivAt.clm_apply (hasFDerivAt_const f x))).add
      ((hDa.hasFDerivAt.clm_apply (hasFDerivAt_const f x)).mul hbd.hasFDerivAt)
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simpa [add_assoc, mul_comm] using hid

/-- A second-derivative product bound in terms of the two factors' jets. -/
theorem levelAreaSecond_fderiv_two_mul_bound {a b : E3 → ℝ} {x : E3}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    ‖fderiv ℝ (fderiv ℝ (fun y => a y * b y)) x‖ ≤
      |a x| * ‖fderiv ℝ (fderiv ℝ b) x‖ +
        2 * ‖fderiv ℝ a x‖ * ‖fderiv ℝ b x‖ +
        ‖fderiv ℝ (fderiv ℝ a) x‖ * |b x| := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro f hf
  have hDa (w : E3) (hw : ‖w‖ = 1) : |fderiv ℝ a x w| ≤ ‖fderiv ℝ a x‖ := by
    simpa [hw] using (fderiv ℝ a x).le_opNorm w
  have hDb (w : E3) (hw : ‖w‖ = 1) : |fderiv ℝ b x w| ≤ ‖fderiv ℝ b x‖ := by
    simpa [hw] using (fderiv ℝ b x).le_opNorm w
  have hDDa : |fderiv ℝ (fderiv ℝ a) x e f| ≤ ‖fderiv ℝ (fderiv ℝ a) x‖ := by
    simpa [he, hf] using (fderiv ℝ (fderiv ℝ a) x).le_opNorm₂ e f
  have hDDb : |fderiv ℝ (fderiv ℝ b) x e f| ≤ ‖fderiv ℝ (fderiv ℝ b) x‖ := by
    simpa [he, hf] using (fderiv ℝ (fderiv ℝ b) x).le_opNorm₂ e f
  rw [levelAreaSecond_fderiv_two_mul ha hb, Real.norm_eq_abs]
  calc
    _ ≤ |a x| * |fderiv ℝ (fderiv ℝ b) x e f| +
        |fderiv ℝ a x e| * |fderiv ℝ b x f| +
        |fderiv ℝ a x f| * |fderiv ℝ b x e| +
        |fderiv ℝ (fderiv ℝ a) x e f| * |b x| := by
      simp only [← abs_mul]
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ |a x| * ‖fderiv ℝ (fderiv ℝ b) x‖ +
        ‖fderiv ℝ a x‖ * ‖fderiv ℝ b x‖ +
        ‖fderiv ℝ a x‖ * ‖fderiv ℝ b x‖ +
        ‖fderiv ℝ (fderiv ℝ a) x‖ * |b x| := by
      gcongr
      · exact hDa e he
      · exact hDb f hf
      · exact hDa f hf
      · exact hDb e he
    _ = _ := by ring

/-- The Hessian of a squared vector norm uses only two derivatives of the vector. -/
theorem levelAreaSecond_fderiv_two_norm_sq {V : E3 → E3} {x : E3}
    (hV : ContDiffAt ℝ 2 V x) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => ‖V y‖ ^ 2)) x e f =
      2 * ⟪fderiv ℝ V x e, fderiv ℝ V x f⟫ +
        2 * ⟪V x, fderiv ℝ (fderiv ℝ V) x e f⟫ := by
  have hVd := hV.differentiableAt (by norm_num)
  have hDV := (hV.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDc := ((hV.norm_sq (𝕜 := ℝ)).fderiv_right (m := 1)
    (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun z => ‖V z‖ ^ 2) y f) =ᶠ[𝓝 x]
      (fun y => 2 * ⟪V y, fderiv ℝ V y f⟫) := by
    filter_upwards [hV.eventually (by norm_num)] with y hy
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.norm_sq).fderiv]
    simp
  have hleft := hDc.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (hVd.hasFDerivAt.inner ℝ
    (hDV.hasFDerivAt.clm_apply (hasFDerivAt_const f x))).const_mul 2
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simpa [mul_add, add_comm] using hid

/-- Pythagoras rewrites the gradient quotient as a quadratic tangential correction. -/
theorem levelAreaSecond_norm_quotient {g n : E3} (hn : ‖n‖ = 1)
    (hgn : ⟪g, n⟫ ≠ 0) :
    ‖g‖ / |⟪g, n⟫| =
      Real.sqrt (1 + ‖⟪g, n⟫⁻¹ • (g - ⟪g, n⟫ • n)‖ ^ 2) := by
  have hpy : ‖g - ⟪g, n⟫ • n‖ ^ 2 = ‖g‖ ^ 2 - ⟪g, n⟫ ^ 2 := by
    rw [norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, hn, mul_one, inner_smul_right,
      sq_abs]
    ring
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hpy, div_pow, sq_abs]
  field_simp
  ring

/-- The square-root correction is quadratic in its vector argument, including
its first two derivatives. No third derivative of the vector argument occurs. -/
theorem levelAreaSecond_sqrt_norm_sq_bounds {V : E3 → E3} {x : E3}
    (hV : ContDiffAt ℝ 2 V x) :
    |Real.sqrt (1 + ‖V x‖ ^ 2) - 1| ≤ ‖V x‖ ^ 2 ∧
      ‖fderiv ℝ (fun y => Real.sqrt (1 + ‖V y‖ ^ 2) - 1) x‖ ≤
        ‖V x‖ * ‖fderiv ℝ V x‖ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => Real.sqrt (1 + ‖V y‖ ^ 2) - 1)) x‖ ≤
        ‖fderiv ℝ V x‖ ^ 2 + ‖V x‖ * ‖fderiv ℝ (fderiv ℝ V) x‖ +
          ‖V x‖ ^ 2 * ‖fderiv ℝ V x‖ ^ 2 := by
  let H : E3 → ℝ := fun y => Real.sqrt (1 + ‖V y‖ ^ 2)
  have hp (y : E3) : 0 < 1 + ‖V y‖ ^ 2 := by positivity
  have hH : ContDiffAt ℝ 2 H x :=
    (contDiffAt_const.add (hV.norm_sq (𝕜 := ℝ))).sqrt (hp x).ne'
  have hHsq (y : E3) : H y ^ 2 = 1 + ‖V y‖ ^ 2 := Real.sq_sqrt (hp y).le
  have hH1 : 1 ≤ H x := by
    have := Real.sqrt_nonneg (1 + ‖V x‖ ^ 2)
    have := hHsq x
    dsimp only [H] at *
    nlinarith [sq_nonneg ‖V x‖]
  have hHpos : 0 < H x := lt_of_lt_of_le zero_lt_one hH1
  have hHd (e : E3) : fderiv ℝ H x e = ⟪V x, fderiv ℝ V x e⟫ / H x := by
    have hd := (((hV.differentiableAt (by norm_num)).hasFDerivAt.norm_sq).const_add 1).sqrt
      (hp x).ne'
    change HasFDerivAt H _ x at hd
    rw [hd.fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      smul_eq_mul, H]
    ring
  have hD : ‖fderiv ℝ H x‖ ≤ ‖V x‖ * ‖fderiv ℝ V x‖ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    rw [hHd, Real.norm_eq_abs, abs_div, abs_of_pos hHpos]
    apply (div_le_self (abs_nonneg _) hH1).trans
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (by simpa [he] using (fderiv ℝ V x).le_opNorm e)
        (norm_nonneg _))
  have hDD (e f : E3) :
      H x * fderiv ℝ (fderiv ℝ H) x e f =
        ⟪fderiv ℝ V x e, fderiv ℝ V x f⟫ +
          ⟪V x, fderiv ℝ (fderiv ℝ V) x e f⟫ -
          fderiv ℝ H x e * fderiv ℝ H x f := by
    have heq : (fun y => H y ^ 2) = fun y => 1 + ‖V y‖ ^ 2 := funext hHsq
    have h := levelArea_fderiv_two_square hH e f
    rw [heq] at h
    have hc : fderiv ℝ (fun y => 1 + ‖V y‖ ^ 2) =
        fderiv ℝ (fun y => ‖V y‖ ^ 2) := by
      funext y
      exact fderiv_const_add 1
    rw [hc, levelAreaSecond_fderiv_two_norm_sq hV] at h
    linarith
  refine ⟨?_, ?_, ?_⟩
  · change |H x - 1| ≤ _
    rw [abs_of_nonneg (by linarith)]
    nlinarith [hHsq x]
  · have heq : fderiv ℝ (fun y => H y - 1) = fderiv ℝ H := by
      funext y
      exact fderiv_sub_const 1
    change ‖fderiv ℝ (fun y => H y - 1) x‖ ≤ _
    rw [heq]
    exact hD
  · have heq : fderiv ℝ (fun y => H y - 1) = fderiv ℝ H := by
      funext y
      exact fderiv_sub_const 1
    change ‖fderiv ℝ (fderiv ℝ (fun y => H y - 1)) x‖ ≤ _
    rw [heq]
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have hVe : ‖fderiv ℝ V x e‖ ≤ ‖fderiv ℝ V x‖ := by
      simpa [he] using (fderiv ℝ V x).le_opNorm e
    have hVf : ‖fderiv ℝ V x f‖ ≤ ‖fderiv ℝ V x‖ := by
      simpa [hf] using (fderiv ℝ V x).le_opNorm f
    have hVV : ‖fderiv ℝ (fderiv ℝ V) x e f‖ ≤ ‖fderiv ℝ (fderiv ℝ V) x‖ := by
      simpa [he, hf] using (fderiv ℝ (fderiv ℝ V) x).le_opNorm₂ e f
    have hHe : |fderiv ℝ H x e| ≤ ‖V x‖ * ‖fderiv ℝ V x‖ := by
      apply le_trans _ hD
      simpa [he] using (fderiv ℝ H x).le_opNorm e
    have hHf : |fderiv ℝ H x f| ≤ ‖V x‖ * ‖fderiv ℝ V x‖ := by
      apply le_trans _ hD
      simpa [hf] using (fderiv ℝ H x).le_opNorm f
    rw [Real.norm_eq_abs]
    calc
      _ ≤ H x * |fderiv ℝ (fderiv ℝ H) x e f| := by
        nlinarith [abs_nonneg (fderiv ℝ (fderiv ℝ H) x e f)]
      _ = |H x * fderiv ℝ (fderiv ℝ H) x e f| := by
        rw [abs_mul, abs_of_pos hHpos]
      _ ≤ |⟪fderiv ℝ V x e, fderiv ℝ V x f⟫| +
          |⟪V x, fderiv ℝ (fderiv ℝ V) x e f⟫| +
          |fderiv ℝ H x e| * |fderiv ℝ H x f| := by
        rw [hDD, ← abs_mul]
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ ‖fderiv ℝ V x‖ * ‖fderiv ℝ V x‖ +
          ‖V x‖ * ‖fderiv ℝ (fderiv ℝ V) x‖ +
          (‖V x‖ * ‖fderiv ℝ V x‖) * (‖V x‖ * ‖fderiv ℝ V x‖) := by
        gcongr
        · exact (abs_real_inner_le_norm _ _).trans (by gcongr)
        · exact (abs_real_inner_le_norm _ _).trans (by gcongr)
      _ = _ := by ring

/-- Bounds for the first two derivatives of the squared radius. -/
theorem levelAreaSecond_square_bounds {s : E3 → ℝ} {x : E3}
    (hs : ContDiffAt ℝ 2 s x) :
    ‖fderiv ℝ (fun y => s y ^ 2) x‖ ≤ 2 * |s x| * ‖fderiv ℝ s x‖ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => s y ^ 2)) x‖ ≤
        2 * |s x| * ‖fderiv ℝ (fderiv ℝ s) x‖ + 2 * ‖fderiv ℝ s x‖ ^ 2 := by
  constructor
  · rw [((hs.differentiableAt (by norm_num)).hasFDerivAt.pow 2).fderiv]
    simp [norm_smul, mul_assoc]
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have hDe : |fderiv ℝ s x e| ≤ ‖fderiv ℝ s x‖ := by
      simpa [he] using (fderiv ℝ s x).le_opNorm e
    have hDf : |fderiv ℝ s x f| ≤ ‖fderiv ℝ s x‖ := by
      simpa [hf] using (fderiv ℝ s x).le_opNorm f
    have hDD : |fderiv ℝ (fderiv ℝ s) x e f| ≤ ‖fderiv ℝ (fderiv ℝ s) x‖ := by
      simpa [he, hf] using (fderiv ℝ (fderiv ℝ s) x).le_opNorm₂ e f
    rw [levelArea_fderiv_two_square hs, Real.norm_eq_abs]
    calc
      _ ≤ |2 * s x * fderiv ℝ (fderiv ℝ s) x e f| +
          |2 * fderiv ℝ s x e * fderiv ℝ s x f| := abs_add_le _ _
      _ ≤ 2 * |s x| * ‖fderiv ℝ (fderiv ℝ s) x‖ +
          2 * ‖fderiv ℝ s x‖ * ‖fderiv ℝ s x‖ := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
      _ = _ := by ring

/-- The Hessian of the quotient correction in terms of the radius and the
normalized tangential gradient. This estimate contains no third radius derivative. -/
theorem levelAreaSecond_correction_bound {s : E3 → ℝ} {V : E3 → E3} {x : E3}
    (hs : ContDiffAt ℝ 2 s x) (hV : ContDiffAt ℝ 2 V x) :
    ‖fderiv ℝ (fderiv ℝ
      (fun y => s y ^ 2 * (Real.sqrt (1 + ‖V y‖ ^ 2) - 1))) x‖ ≤
      s x ^ 2 * (‖fderiv ℝ V x‖ ^ 2 + ‖V x‖ * ‖fderiv ℝ (fderiv ℝ V) x‖ +
        ‖V x‖ ^ 2 * ‖fderiv ℝ V x‖ ^ 2) +
      4 * |s x| * ‖fderiv ℝ s x‖ * (‖V x‖ * ‖fderiv ℝ V x‖) +
      (2 * |s x| * ‖fderiv ℝ (fderiv ℝ s) x‖ + 2 * ‖fderiv ℝ s x‖ ^ 2) *
        ‖V x‖ ^ 2 := by
  have hH : ContDiffAt ℝ 2 (fun y => Real.sqrt (1 + ‖V y‖ ^ 2) - 1) x :=
    ((contDiffAt_const.add (hV.norm_sq (𝕜 := ℝ))).sqrt (by positivity)).sub contDiffAt_const
  obtain ⟨hval, hD, hDD⟩ := levelAreaSecond_sqrt_norm_sq_bounds hV
  obtain ⟨hsD, hsDD⟩ := levelAreaSecond_square_bounds hs
  apply (levelAreaSecond_fderiv_two_mul_bound (hs.pow 2) hH).trans
  rw [abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ s x ^ 2 * (‖fderiv ℝ V x‖ ^ 2 + ‖V x‖ * ‖fderiv ℝ (fderiv ℝ V) x‖ +
          ‖V x‖ ^ 2 * ‖fderiv ℝ V x‖ ^ 2) +
        2 * (2 * |s x| * ‖fderiv ℝ s x‖) * (‖V x‖ * ‖fderiv ℝ V x‖) +
        (2 * |s x| * ‖fderiv ℝ (fderiv ℝ s) x‖ + 2 * ‖fderiv ℝ s x‖ ^ 2) *
          ‖V x‖ ^ 2 := by gcongr
    _ = _ := by ring

/-- A quantitative small-level bound for the quotient correction. Coarse `S/t`
bounds for the radius and its two derivatives suffice once all three tangential
ratio jets are bounded by `B*t²`. -/
theorem levelAreaSecond_correction_bound_small {s : E3 → ℝ} {V : E3 → E3} {x : E3}
    {S B t : ℝ} (hS : 0 ≤ S) (hB : 0 ≤ B) (ht : 0 < t) (ht1 : t ≤ 1)
    (hs : ContDiffAt ℝ 2 s x) (hV : ContDiffAt ℝ 2 V x)
    (hs0 : |s x| ≤ S / t) (hs1 : ‖fderiv ℝ s x‖ ≤ S / t)
    (hs2 : ‖fderiv ℝ (fderiv ℝ s) x‖ ≤ S / t)
    (hV0 : ‖V x‖ ≤ B * t ^ 2) (hV1 : ‖fderiv ℝ V x‖ ≤ B * t ^ 2)
    (hV2 : ‖fderiv ℝ (fderiv ℝ V) x‖ ≤ B * t ^ 2) :
    ‖fderiv ℝ (fderiv ℝ
      (fun y => s y ^ 2 * (Real.sqrt (1 + ‖V y‖ ^ 2) - 1))) x‖ ≤
      S ^ 2 * (10 * B ^ 2 + B ^ 4) * t ^ 2 := by
  have hs0' : s x ^ 2 ≤ (S / t) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (s x)) hs0 2
  have ht6 : t ^ 6 ≤ t ^ 2 := by
    calc
      _ = t ^ 2 * t ^ 4 := by ring
      _ ≤ t ^ 2 * 1 := by gcongr; exact pow_le_one₀ ht.le ht1
      _ = _ := mul_one _
  apply (levelAreaSecond_correction_bound hs hV).trans
  calc
    _ ≤ (S / t) ^ 2 * ((B * t ^ 2) ^ 2 +
          (B * t ^ 2) * (B * t ^ 2) + (B * t ^ 2) ^ 2 * (B * t ^ 2) ^ 2) +
        4 * (S / t) * (S / t) * ((B * t ^ 2) * (B * t ^ 2)) +
        (2 * (S / t) * (S / t) + 2 * (S / t) ^ 2) * (B * t ^ 2) ^ 2 := by
      gcongr
    _ = 10 * S ^ 2 * B ^ 2 * t ^ 2 + S ^ 2 * B ^ 4 * t ^ 6 := by
      field_simp
      ring
    _ ≤ 10 * S ^ 2 * B ^ 2 * t ^ 2 + S ^ 2 * B ^ 4 * t ^ 2 := by gcongr
    _ = _ := by ring

/-- The tangential component of the potential gradient divided by its radial
component, evaluated on the translated radial graph. -/
def levelAreaSecond_tangentialRatio (u v ρ : E3 → ℝ) (y : E3) : E3 :=
  let n := ‖y‖⁻¹ • y
  let g := gradient u (ρ y • n + (v 0)⁻¹ • gradient v 0)
  ⟪g, n⟫⁻¹ • (g - ⟪g, n⟫ • n)

/-- Two derivatives along the radial graph require two radius derivatives and
three potential derivatives. -/
theorem levelAreaSecond_gradient_composition_contDiffAt {u v ρ : E3 → ℝ} {x : E3}
    (hx : x ≠ 0) (hρ : ContDiffAt ℝ 2 ρ x)
    (hu : ContDiffAt ℝ 3 u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0)) :
    ContDiffAt ℝ 2
      (fun y => gradient u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0)) x := by
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) x :=
    (levelRadius_normalize_contDiffAt hx).of_le (by simp)
  have hg : ContDiffAt ℝ 2 (gradient u)
      (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0) :=
    (toDual ℝ E3).symm.contDiff.contDiffAt.comp _ (hu.fderiv_right (by norm_num))
  have hF : ContDiffAt ℝ 2
      (fun y => ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0) x :=
    (hρ.smul hn).add contDiffAt_const
  exact ContDiffAt.comp x (g := gradient u) hg hF

/-- The tangential ratio is twice differentiable wherever the radial gradient
is nonzero, using no derivative of the radius above order two. -/
theorem levelAreaSecond_tangentialRatio_contDiffAt {u v ρ : E3 → ℝ} {x : E3}
    (hx : x ≠ 0) (hρ : ContDiffAt ℝ 2 ρ x)
    (hu : ContDiffAt ℝ 3 u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0))
    (hr : ⟪gradient u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0),
      ‖x‖⁻¹ • x⟫ ≠ 0) :
    ContDiffAt ℝ 2 (levelAreaSecond_tangentialRatio u v ρ) x := by
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) x :=
    (levelRadius_normalize_contDiffAt hx).of_le (by simp)
  have hg := levelAreaSecond_gradient_composition_contDiffAt hx hρ hu
  have ha := hg.inner ℝ hn
  exact (ha.inv hr).smul (hg.sub (ha.smul hn))

/-- The area remainder separates into the squared-radius remainder and the
quadratic quotient correction. This is an identity off the origin. -/
theorem levelAreaSecond_remainder_eq {u v ρ : E3 → ℝ} {t : ℝ} {x : E3}
    (hx : x ≠ 0)
    (hr : ⟪gradient u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0),
      ‖x‖⁻¹ • x⟫ ≠ 0) :
    levelAreaRemainder u v t ρ x =
      (ρ x ^ 2 - ((v 0) ^ 2 / t ^ 2 +
        2 * kelvinTranslatedQuadrupole v (‖x‖⁻¹ • x) / v 0)) +
      ρ x ^ 2 * (Real.sqrt (1 + ‖levelAreaSecond_tangentialRatio u v ρ x‖ ^ 2) - 1) := by
  have hn : ‖‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hx]
  have he := levelAreaSecond_norm_quotient hn hr
  dsimp only [levelAreaRemainder, gradNorm, levelAreaSecond_tangentialRatio]
  rw [mul_div_assoc, he]
  ring

/-- The second derivative of a sum of scalar functions. -/
theorem levelAreaSecond_fderiv_two_add {a b : E3 → ℝ} {x : E3}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    fderiv ℝ (fderiv ℝ (fun y => a y + b y)) x =
      fderiv ℝ (fderiv ℝ a) x + fderiv ℝ (fderiv ℝ b) x := by
  have he : fderiv ℝ (fun y => a y + b y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ a y + fderiv ℝ b y) := by
    filter_upwards [ha.eventually (by norm_num), hb.eventually (by norm_num)] with y hy hz
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.add
      (hz.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  rw [he.fderiv_eq]
  exact (((ha.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt.add
    ((hb.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt).fderiv

/-- An exact Hessian decomposition of the area remainder into the known radius
term and the quotient correction. -/
theorem levelAreaSecond_remainder_fderiv_two {u v ρ : E3 → ℝ} {t : ℝ} {x : E3}
    (hx : x ≠ 0) (hρ : ContDiffAt ℝ 2 ρ x)
    (hu : ContDiffAt ℝ 3 u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0))
    (hr : ⟪gradient u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0),
      ‖x‖⁻¹ • x⟫ ≠ 0) :
    fderiv ℝ (fderiv ℝ (levelAreaRemainder u v t ρ)) x =
      fderiv ℝ (fderiv ℝ (fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
        2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0))) x +
      fderiv ℝ (fderiv ℝ (fun y => ρ y ^ 2 *
        (Real.sqrt (1 + ‖levelAreaSecond_tangentialRatio u v ρ y‖ ^ 2) - 1))) x := by
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) x :=
    (levelRadius_normalize_contDiffAt hx).of_le (by simp)
  have hg := levelAreaSecond_gradient_composition_contDiffAt hx hρ hu
  have hne := (hg.inner ℝ hn).continuousAt.eventually_ne hr
  have he : levelAreaRemainder u v t ρ =ᶠ[𝓝 x] fun y =>
      (ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
        2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0)) +
      ρ y ^ 2 * (Real.sqrt (1 + ‖levelAreaSecond_tangentialRatio u v ρ y‖ ^ 2) - 1) := by
    filter_upwards [isOpen_ne.mem_nhds hx, hne] with y hy hz
    exact levelAreaSecond_remainder_eq hy hz
  have hq := ((translated_quadrupole_contDiff v).contDiffAt.of_le
    (by simp : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).comp x hn
  have hs : ContDiffAt ℝ 2 (fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
      2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0)) x :=
    (hρ.pow 2).sub (contDiffAt_const.add ((contDiffAt_const.mul hq).div_const _))
  have hV := levelAreaSecond_tangentialRatio_contDiffAt hx hρ hu hr
  have hc : ContDiffAt ℝ 2 (fun y => ρ y ^ 2 *
      (Real.sqrt (1 + ‖levelAreaSecond_tangentialRatio u v ρ y‖ ^ 2) - 1)) x :=
    (hρ.pow 2).mul (((contDiffAt_const.add (hV.norm_sq (𝕜 := ℝ))).sqrt
      (by positivity)).sub contDiffAt_const)
  rw [he.fderiv.fderiv_eq, levelAreaSecond_fderiv_two_add hs hc]

/-- Reduction of the area Hessian estimate to the known squared-radius estimate
and bounds for the tangential ratio. All auxiliary bounds are explicit hypotheses. -/
theorem levelAreaSecond_remainder_bound_of_ratio {u v ρ : E3 → ℝ} {x : E3}
    {A S B t : ℝ} (hx : x ≠ 0) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (ht : 0 < t) (ht1 : t ≤ 1) (hρ : ContDiffAt ℝ 2 ρ x)
    (hu : ContDiffAt ℝ 3 u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0))
    (hr : ⟪gradient u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0),
      ‖x‖⁻¹ • x⟫ ≠ 0)
    (hsq : ‖fderiv ℝ (fderiv ℝ (fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
      2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0))) x‖ ≤ A * t)
    (hρ0 : |ρ x| ≤ S / t) (hρ1 : ‖fderiv ℝ ρ x‖ ≤ S / t)
    (hρ2 : ‖fderiv ℝ (fderiv ℝ ρ) x‖ ≤ S / t)
    (hV0 : ‖levelAreaSecond_tangentialRatio u v ρ x‖ ≤ B * t ^ 2)
    (hV1 : ‖fderiv ℝ (levelAreaSecond_tangentialRatio u v ρ) x‖ ≤ B * t ^ 2)
    (hV2 : ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_tangentialRatio u v ρ)) x‖ ≤ B * t ^ 2) :
    ‖fderiv ℝ (fderiv ℝ (levelAreaRemainder u v t ρ)) x‖ ≤
      (A + S ^ 2 * (10 * B ^ 2 + B ^ 4)) * t := by
  have hV := levelAreaSecond_tangentialRatio_contDiffAt hx hρ hu hr
  have hc := levelAreaSecond_correction_bound_small hS hB ht ht1 hρ hV
    hρ0 hρ1 hρ2 hV0 hV1 hV2
  rw [levelAreaSecond_remainder_fderiv_two hx hρ hu hr]
  apply (norm_add_le (E := E3 →L[ℝ] E3 →L[ℝ] ℝ) _ _).trans
  calc
    _ ≤ A * t + S ^ 2 * (10 * B ^ 2 + B ^ 4) * t ^ 2 := add_le_add hsq hc
    _ ≤ A * t + S ^ 2 * (10 * B ^ 2 + B ^ 4) * t := by
      gcongr
      nlinarith
    _ = _ := by ring

/-- The derivative of a reciprocal, in scalar application form. -/
theorem levelAreaSecond_fderiv_inv {a : E3 → ℝ} {x : E3}
    (ha : DifferentiableAt ℝ a x) (h0 : a x ≠ 0) (e : E3) :
    fderiv ℝ (fun y => (a y)⁻¹) x e = -(a x)⁻¹ ^ 2 * fderiv ℝ a x e := by
  have hd := (hasDerivAt_inv h0).comp_hasFDerivAt x ha.hasFDerivAt
  change HasFDerivAt (fun y => (a y)⁻¹) _ x at hd
  rw [hd.fderiv]
  simp [inv_pow]

/-- The reciprocal Hessian uses the first two denominator derivatives. -/
theorem levelAreaSecond_fderiv_two_inv {a : E3 → ℝ} {x : E3}
    (ha : ContDiffAt ℝ 2 a x) (h0 : a x ≠ 0) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => (a y)⁻¹)) x e f =
      2 * (a x)⁻¹ ^ 3 * fderiv ℝ a x e * fderiv ℝ a x f -
        (a x)⁻¹ ^ 2 * fderiv ℝ (fderiv ℝ a) x e f := by
  have hi : ContDiffAt ℝ 2 (fun y => (a y)⁻¹) x := ha.inv h0
  have hDa := (ha.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDi := (hi.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he : (fun y => fderiv ℝ (fun z => (a z)⁻¹) y f) =ᶠ[𝓝 x]
      (fun y => -(a y)⁻¹ ^ 2 * fderiv ℝ a y f) := by
    filter_upwards [ha.eventually (by norm_num), ha.continuousAt.eventually_ne h0]
      with y hy hz
    exact levelAreaSecond_fderiv_inv (hy.differentiableAt (by norm_num)) hz f
  have hleft := hDi.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (((hi.differentiableAt (by norm_num)).hasFDerivAt.pow 2).neg).mul
    (hDa.hasFDerivAt.clm_apply (hasFDerivAt_const f x))
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e)
    ((hleft.congr_of_eventuallyEq he.symm).unique hright)
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply,
    inv_pow, Pi.neg_apply, neg_smul, Nat.add_one_sub_one, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat, smul_neg, add_apply, neg_apply, smul_apply, smul_eq_mul] at hid
  rw [levelAreaSecond_fderiv_inv (ha.differentiableAt (by norm_num)) h0] at hid
  convert hid using 1
  ring

/-- Norm bounds for the first two reciprocal derivatives. -/
theorem levelAreaSecond_inv_bounds {a : E3 → ℝ} {x : E3}
    (ha : ContDiffAt ℝ 2 a x) (h0 : a x ≠ 0) :
    ‖fderiv ℝ (fun y => (a y)⁻¹) x‖ ≤ |(a x)⁻¹| ^ 2 * ‖fderiv ℝ a x‖ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => (a y)⁻¹)) x‖ ≤
        2 * |(a x)⁻¹| ^ 3 * ‖fderiv ℝ a x‖ ^ 2 +
          |(a x)⁻¹| ^ 2 * ‖fderiv ℝ (fderiv ℝ a) x‖ := by
  constructor
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    rw [levelAreaSecond_fderiv_inv (ha.differentiableAt (by norm_num)) h0,
      Real.norm_eq_abs, abs_mul, abs_neg, abs_pow]
    gcongr
    simpa [he] using (fderiv ℝ a x).le_opNorm e
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have hDe : |fderiv ℝ a x e| ≤ ‖fderiv ℝ a x‖ := by
      simpa [he] using (fderiv ℝ a x).le_opNorm e
    have hDf : |fderiv ℝ a x f| ≤ ‖fderiv ℝ a x‖ := by
      simpa [hf] using (fderiv ℝ a x).le_opNorm f
    have hDD : |fderiv ℝ (fderiv ℝ a) x e f| ≤ ‖fderiv ℝ (fderiv ℝ a) x‖ := by
      simpa [he, hf] using (fderiv ℝ (fderiv ℝ a) x).le_opNorm₂ e f
    rw [levelAreaSecond_fderiv_two_inv ha h0, Real.norm_eq_abs]
    calc
      _ ≤ |2 * (a x)⁻¹ ^ 3 * fderiv ℝ a x e * fderiv ℝ a x f| +
          |(a x)⁻¹ ^ 2 * fderiv ℝ (fderiv ℝ a) x e f| := abs_sub _ _
      _ ≤ 2 * |(a x)⁻¹| ^ 3 * ‖fderiv ℝ a x‖ * ‖fderiv ℝ a x‖ +
          |(a x)⁻¹| ^ 2 * ‖fderiv ℝ (fderiv ℝ a) x‖ := by
        simp only [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
      _ = _ := by ring

/-- Product estimates for a scalar times a vector, through second order. -/
theorem levelAreaSecond_smul_bounds {a : E3 → ℝ} {V : E3 → E3} {x : E3}
    (ha : ContDiffAt ℝ 2 a x) (hV : ContDiffAt ℝ 2 V x) :
    ‖fderiv ℝ (fun y => a y • V y) x‖ ≤
      |a x| * ‖fderiv ℝ V x‖ + ‖fderiv ℝ a x‖ * ‖V x‖ ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => a y • V y)) x‖ ≤
      |a x| * ‖fderiv ℝ (fderiv ℝ V) x‖ +
        2 * ‖fderiv ℝ a x‖ * ‖fderiv ℝ V x‖ +
        ‖fderiv ℝ (fderiv ℝ a) x‖ * ‖V x‖ := by
  have hDa (e : E3) (he : ‖e‖ = 1) : |fderiv ℝ a x e| ≤ ‖fderiv ℝ a x‖ := by
    simpa [he] using (fderiv ℝ a x).le_opNorm e
  have hDV (e : E3) (he : ‖e‖ = 1) : ‖fderiv ℝ V x e‖ ≤ ‖fderiv ℝ V x‖ := by
    simpa [he] using (fderiv ℝ V x).le_opNorm e
  constructor
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    have hd := (ha.differentiableAt (by norm_num)).hasFDerivAt.smul
      (hV.differentiableAt (by norm_num)).hasFDerivAt
    change HasFDerivAt (fun y => a y • V y) _ x at hd
    rw [hd.fderiv]
    change ‖a x • fderiv ℝ V x e + fderiv ℝ a x e • V x‖ ≤ _
    apply (norm_add_le _ _).trans
    simp only [norm_smul, Real.norm_eq_abs]
    gcongr
    · exact hDV e he
    · exact hDa e he
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have hDDa : |fderiv ℝ (fderiv ℝ a) x e f| ≤ ‖fderiv ℝ (fderiv ℝ a) x‖ := by
      simpa [he, hf] using (fderiv ℝ (fderiv ℝ a) x).le_opNorm₂ e f
    have hDDV : ‖fderiv ℝ (fderiv ℝ V) x e f‖ ≤ ‖fderiv ℝ (fderiv ℝ V) x‖ := by
      simpa [he, hf] using (fderiv ℝ (fderiv ℝ V) x).le_opNorm₂ e f
    rw [levelRadius_fderiv_two_smul ha hV]
    calc
      _ ≤ ‖a x • fderiv ℝ (fderiv ℝ V) x e f‖ +
          ‖fderiv ℝ a x e • fderiv ℝ V x f‖ +
          ‖fderiv ℝ a x f • fderiv ℝ V x e‖ +
          ‖fderiv ℝ (fderiv ℝ a) x e f • V x‖ := by
        exact (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ |a x| * ‖fderiv ℝ (fderiv ℝ V) x‖ +
          ‖fderiv ℝ a x‖ * ‖fderiv ℝ V x‖ +
          ‖fderiv ℝ a x‖ * ‖fderiv ℝ V x‖ +
          ‖fderiv ℝ (fderiv ℝ a) x‖ * ‖V x‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
        gcongr
        · exact hDa e he
        · exact hDV f hf
        · exact hDa f hf
        · exact hDV e he
      _ = _ := by ring

/-- The vector quotient bound separates numerator estimates from denominator
estimates and a lower bound for the absolute denominator. -/
theorem levelAreaSecond_quotient_bounds {a : E3 → ℝ} {V : E3 → E3} {x : E3}
    (ha : ContDiffAt ℝ 2 a x) (hV : ContDiffAt ℝ 2 V x) (h0 : a x ≠ 0) :
    ‖fderiv ℝ (fun y => (a y)⁻¹ • V y) x‖ ≤
      |(a x)⁻¹| * ‖fderiv ℝ V x‖ + |(a x)⁻¹| ^ 2 * ‖fderiv ℝ a x‖ * ‖V x‖ ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => (a y)⁻¹ • V y)) x‖ ≤
      |(a x)⁻¹| * ‖fderiv ℝ (fderiv ℝ V) x‖ +
        2 * (|(a x)⁻¹| ^ 2 * ‖fderiv ℝ a x‖) * ‖fderiv ℝ V x‖ +
        (2 * |(a x)⁻¹| ^ 3 * ‖fderiv ℝ a x‖ ^ 2 +
          |(a x)⁻¹| ^ 2 * ‖fderiv ℝ (fderiv ℝ a) x‖) * ‖V x‖ := by
  obtain ⟨hi1, hi2⟩ := levelAreaSecond_inv_bounds ha h0
  have hi : ContDiffAt ℝ 2 (fun y => (a y)⁻¹) x := ha.inv h0
  obtain ⟨hm1, hm2⟩ := levelAreaSecond_smul_bounds hi hV
  exact ⟨hm1.trans (by gcongr), hm2.trans (by gcongr)⟩

/-- An `O(t⁴)` tangential numerator and an `O(t²)` radial denominator give an
`O(t²)` quotient through two derivatives, with an explicit common constant. -/
theorem levelAreaSecond_quotient_bounds_small {a : E3 → ℝ} {V : E3 → E3} {x : E3}
    {D B t : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B) (ht : 0 < t)
    (ha : ContDiffAt ℝ 2 a x) (hV : ContDiffAt ℝ 2 V x) (h0 : a x ≠ 0)
    (hi : |(a x)⁻¹| ≤ D / t ^ 2)
    (ha1 : ‖fderiv ℝ a x‖ ≤ D * t ^ 2)
    (ha2 : ‖fderiv ℝ (fderiv ℝ a) x‖ ≤ D * t ^ 2)
    (hV0 : ‖V x‖ ≤ B * t ^ 4) (hV1 : ‖fderiv ℝ V x‖ ≤ B * t ^ 4)
    (hV2 : ‖fderiv ℝ (fderiv ℝ V) x‖ ≤ B * t ^ 4) :
    ‖(a x)⁻¹ • V x‖ ≤ B * (D + 3 * D ^ 3 + 2 * D ^ 5) * t ^ 2 ∧
      ‖fderiv ℝ (fun y => (a y)⁻¹ • V y) x‖ ≤
        B * (D + 3 * D ^ 3 + 2 * D ^ 5) * t ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => (a y)⁻¹ • V y)) x‖ ≤
        B * (D + 3 * D ^ 3 + 2 * D ^ 5) * t ^ 2 := by
  obtain ⟨hq1, hq2⟩ := levelAreaSecond_quotient_bounds ha hV h0
  have hD0 : D ≤ D + 3 * D ^ 3 + 2 * D ^ 5 := by
    have : 0 ≤ 3 * D ^ 3 + 2 * D ^ 5 := by positivity
    linarith
  have hD1 : D + D ^ 3 ≤ D + 3 * D ^ 3 + 2 * D ^ 5 := by
    have : 0 ≤ D ^ 3 := by positivity
    have : 0 ≤ D ^ 5 := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (D / t ^ 2) * (B * t ^ 4) := by gcongr
      _ = B * D * t ^ 2 := by field_simp
      _ ≤ _ := by gcongr
  · apply hq1.trans
    calc
      _ ≤ (D / t ^ 2) * (B * t ^ 4) +
          (D / t ^ 2) ^ 2 * (D * t ^ 2) * (B * t ^ 4) := by gcongr
      _ = B * (D + D ^ 3) * t ^ 2 := by field_simp
      _ ≤ _ := by gcongr
  · apply hq2.trans
    calc
      _ ≤ (D / t ^ 2) * (B * t ^ 4) +
          2 * ((D / t ^ 2) ^ 2 * (D * t ^ 2)) * (B * t ^ 4) +
          (2 * (D / t ^ 2) ^ 3 * (D * t ^ 2) ^ 2 +
            (D / t ^ 2) ^ 2 * (D * t ^ 2)) * (B * t ^ 4) := by gcongr
      _ = _ := by field_simp; ring

/-- The vector-valued second derivative chain rule. -/
theorem levelAreaSecond_fderiv_two_comp {F G : E3 → E3} {x : E3}
    (hF : ContDiffAt ℝ 2 F x) (hG : ContDiffAt ℝ 2 G (F x)) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => G (F y))) x e f =
      fderiv ℝ (fderiv ℝ G) (F x) (fderiv ℝ F x e) (fderiv ℝ F x f) +
        fderiv ℝ G (F x) (fderiv ℝ (fderiv ℝ F) x e f) := by
  have hFd := hF.differentiableAt (by norm_num)
  have he : (fun y => fderiv ℝ (fun z => G (F z)) y f) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ G (F y) (fderiv ℝ F y f)) := by
    filter_upwards [hF.eventually (by norm_num),
      hFd.continuousAt.eventually (hG.eventually (by norm_num))] with y hy hz
    rw [fderiv_fun_comp y (hz.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num))]
    rfl
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDG := (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDc := ((hG.comp x hF).fderiv_right (m := 1)
    (by norm_num)).differentiableAt one_ne_zero
  have hleft := hDc.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (hDG.hasFDerivAt.comp x hFd.hasFDerivAt).clm_apply
    (hDF.hasFDerivAt.clm_apply (hasFDerivAt_const f x))
  have hid := congrArg (fun L : E3 →L[ℝ] E3 => L e)
    ((hleft.congr_of_eventuallyEq he.symm).unique hright)
  simpa [add_comm, Function.comp_def] using hid

/-- Spatial derivative bounds pass to angular derivatives with only the first
two derivatives of the level parametrization. -/
theorem levelAreaSecond_comp_bounds {F G : E3 → E3} {x : E3}
    (hF : ContDiffAt ℝ 2 F x) (hG : ContDiffAt ℝ 2 G (F x)) :
    ‖fderiv ℝ (fun y => G (F y)) x‖ ≤
      ‖fderiv ℝ G (F x)‖ * ‖fderiv ℝ F x‖ ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => G (F y))) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ G) (F x)‖ * ‖fderiv ℝ F x‖ ^ 2 +
        ‖fderiv ℝ G (F x)‖ * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
  constructor
  · rw [fderiv_fun_comp x (hG.differentiableAt (by norm_num))
      (hF.differentiableAt (by norm_num))]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have hFe : ‖fderiv ℝ F x e‖ ≤ ‖fderiv ℝ F x‖ := by
      simpa [he] using (fderiv ℝ F x).le_opNorm e
    have hFf : ‖fderiv ℝ F x f‖ ≤ ‖fderiv ℝ F x‖ := by
      simpa [hf] using (fderiv ℝ F x).le_opNorm f
    have hFF : ‖fderiv ℝ (fderiv ℝ F) x e f‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ := by
      simpa [he, hf] using (fderiv ℝ (fderiv ℝ F) x).le_opNorm₂ e f
    rw [levelAreaSecond_fderiv_two_comp hF hG]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ G) (F x) (fderiv ℝ F x e) (fderiv ℝ F x f)‖ +
          ‖fderiv ℝ G (F x) (fderiv ℝ (fderiv ℝ F) x e f)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ G) (F x)‖ * ‖fderiv ℝ F x e‖ * ‖fderiv ℝ F x f‖ +
          ‖fderiv ℝ G (F x)‖ * ‖fderiv ℝ (fderiv ℝ F) x e f‖ :=
        add_le_add ((fderiv ℝ (fderiv ℝ G) (F x)).le_opNorm₂ _ _)
          ((fderiv ℝ G (F x)).le_opNorm _)
      _ ≤ ‖fderiv ℝ (fderiv ℝ G) (F x)‖ * ‖fderiv ℝ F x‖ * ‖fderiv ℝ F x‖ +
          ‖fderiv ℝ G (F x)‖ * ‖fderiv ℝ (fderiv ℝ F) x‖ := by gcongr
      _ = _ := by ring

/-- Riesz duality identifies every gradient derivative norm with the next
scalar derivative norm, including for total derivatives. -/
theorem levelAreaSecond_norm_iterated_gradient (U : E3 → ℝ) (x : E3) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (gradient U) x‖ = ‖iteratedFDeriv ℝ (k + 1) U x‖ := by
  have he : (toDual ℝ E3) ∘ gradient U = fderiv ℝ U :=
    funext fun _ => toDual_gradient
  rw [← norm_iteratedFDeriv_fderiv, ← he]
  exact ((toDual ℝ E3).norm_iteratedFDeriv_comp_left (gradient U) x k).symm

/-- The second derivative of the gradient is exactly controlled by the third
iterated derivative already present in the exterior harmonic decay estimate. -/
theorem levelAreaSecond_norm_fderiv_two_gradient (U : E3 → ℝ) (x : E3) :
    ‖fderiv ℝ (fderiv ℝ (gradient U)) x‖ = ‖iteratedFDeriv ℝ 3 U x‖ := by
  rw [← norm_iteratedFDeriv_one (fderiv ℝ (gradient U)),
    norm_iteratedFDeriv_fderiv, levelAreaSecond_norm_iterated_gradient]

/-- Two angular derivatives of the potential gradient along a parametrization
use exactly the second and third spatial potential derivatives. -/
theorem levelAreaSecond_gradient_comp_bounds {F : E3 → E3} {U : E3 → ℝ} {x : E3}
    (hF : ContDiffAt ℝ 2 F x) (hU : ContDiffAt ℝ 3 U (F x)) :
    ‖fderiv ℝ (fun y => gradient U (F y)) x‖ ≤
      ‖iteratedFDeriv ℝ 2 U (F x)‖ * ‖fderiv ℝ F x‖ ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => gradient U (F y))) x‖ ≤
      ‖iteratedFDeriv ℝ 3 U (F x)‖ * ‖fderiv ℝ F x‖ ^ 2 +
        ‖iteratedFDeriv ℝ 2 U (F x)‖ * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
  have hg : ContDiffAt ℝ 2 (gradient U) (F x) :=
    (toDual ℝ E3).symm.contDiff.contDiffAt.comp _ (hU.fderiv_right (by norm_num))
  have hnorm : ‖fderiv ℝ (gradient U) (F x)‖ = ‖iteratedFDeriv ℝ 2 U (F x)‖ := by
    rw [← norm_iteratedFDeriv_one, levelAreaSecond_norm_iterated_gradient]
  simpa only [hnorm, levelAreaSecond_norm_fderiv_two_gradient] using
    levelAreaSecond_comp_bounds hF hg

/-- Exterior derivative decay remains of the same order after two derivatives
of an angular parametrization whose first two derivatives are `O(r)`. -/
theorem levelAreaSecond_gradient_comp_decay {F : E3 → E3} {U : E3 → ℝ} {x : E3}
    {r L M : ℝ} (hr : 0 < r) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hF : ContDiffAt ℝ 2 F x) (hU : ContDiffAt ℝ 3 U (F x))
    (hF1 : ‖fderiv ℝ F x‖ ≤ L * r)
    (hF2 : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ L * r)
    (hU1 : ‖iteratedFDeriv ℝ 1 U (F x)‖ ≤ M / r ^ 5)
    (hU2 : ‖iteratedFDeriv ℝ 2 U (F x)‖ ≤ M / r ^ 6)
    (hU3 : ‖iteratedFDeriv ℝ 3 U (F x)‖ ≤ M / r ^ 7) :
    ‖gradient U (F x)‖ ≤ M / r ^ 5 ∧
      ‖fderiv ℝ (fun y => gradient U (F y)) x‖ ≤ M * L / r ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => gradient U (F y))) x‖ ≤
        M * (L ^ 2 + L) / r ^ 5 := by
  obtain ⟨hD, hDD⟩ := levelAreaSecond_gradient_comp_bounds hF hU
  refine ⟨?_, hD.trans ?_, hDD.trans ?_⟩
  · simpa only [gradient, (toDual ℝ E3).symm.norm_map, norm_iteratedFDeriv_one] using hU1
  · calc
      _ ≤ (M / r ^ 6) * (L * r) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M / r ^ 7) * (L * r) ^ 2 + (M / r ^ 6) * (L * r) := by gcongr
      _ = _ := by field_simp

/-- The radial potential derivative evaluated on the translated level graph. -/
def levelAreaSecond_radialGradient (u v ρ : E3 → ℝ) (y : E3) : ℝ :=
  ⟪gradient u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0), ‖y‖⁻¹ • y⟫

/-- The tangential potential gradient evaluated on the translated level graph. -/
def levelAreaSecond_tangentialGradient (u v ρ : E3 → ℝ) (y : E3) : E3 :=
  gradient u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0) -
    levelAreaSecond_radialGradient u v ρ y • (‖y‖⁻¹ • y)

/-- The quotient components require only two radius derivatives and three
potential derivatives. -/
theorem levelAreaSecond_components_contDiffAt {u v ρ : E3 → ℝ} {x : E3}
    (hx : x ≠ 0) (hρ : ContDiffAt ℝ 2 ρ x)
    (hu : ContDiffAt ℝ 3 u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0)) :
    ContDiffAt ℝ 2 (levelAreaSecond_radialGradient u v ρ) x ∧
      ContDiffAt ℝ 2 (levelAreaSecond_tangentialGradient u v ρ) x := by
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) x :=
    (levelRadius_normalize_contDiffAt hx).of_le (by simp)
  have hg := levelAreaSecond_gradient_composition_contDiffAt hx hρ hu
  exact ⟨hg.inner ℝ hn, hg.sub ((hg.inner ℝ hn).smul hn)⟩

/-- Componentwise decay estimates suffice for all three tangential-ratio bounds.
This isolates the exterior asymptotic estimates still needed for capacitary levels. -/
theorem levelAreaSecond_tangentialRatio_bounds_small {u v ρ : E3 → ℝ} {x : E3}
    {D B t : ℝ} (hx : x ≠ 0) (hD : 0 ≤ D) (hB : 0 ≤ B) (ht : 0 < t)
    (hρ : ContDiffAt ℝ 2 ρ x)
    (hu : ContDiffAt ℝ 3 u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0))
    (hr : levelAreaSecond_radialGradient u v ρ x ≠ 0)
    (hi : |(levelAreaSecond_radialGradient u v ρ x)⁻¹| ≤ D / t ^ 2)
    (ha1 : ‖fderiv ℝ (levelAreaSecond_radialGradient u v ρ) x‖ ≤ D * t ^ 2)
    (ha2 : ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_radialGradient u v ρ)) x‖ ≤ D * t ^ 2)
    (hV0 : ‖levelAreaSecond_tangentialGradient u v ρ x‖ ≤ B * t ^ 4)
    (hV1 : ‖fderiv ℝ (levelAreaSecond_tangentialGradient u v ρ) x‖ ≤ B * t ^ 4)
    (hV2 : ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_tangentialGradient u v ρ)) x‖ ≤
      B * t ^ 4) :
    ‖levelAreaSecond_tangentialRatio u v ρ x‖ ≤
        B * (D + 3 * D ^ 3 + 2 * D ^ 5) * t ^ 2 ∧
      ‖fderiv ℝ (levelAreaSecond_tangentialRatio u v ρ) x‖ ≤
        B * (D + 3 * D ^ 3 + 2 * D ^ 5) * t ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_tangentialRatio u v ρ)) x‖ ≤
        B * (D + 3 * D ^ 3 + 2 * D ^ 5) * t ^ 2 := by
  obtain ⟨ha, hV⟩ := levelAreaSecond_components_contDiffAt hx hρ hu
  have he : levelAreaSecond_tangentialRatio u v ρ = fun y =>
      (levelAreaSecond_radialGradient u v ρ y)⁻¹ •
        levelAreaSecond_tangentialGradient u v ρ y := rfl
  rw [he]
  exact levelAreaSecond_quotient_bounds_small hD hB ht ha hV hr hi ha1 ha2 hV0 hV1 hV2

/-- The desired area Hessian bound follows quantitatively from the squared-radius
bound and the stated radial and tangential component estimates. -/
theorem levelAreaSecond_remainder_bound_of_components {u v ρ : E3 → ℝ} {x : E3}
    {A S D B t : ℝ} (hx : x ≠ 0) (hS : 0 ≤ S) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (ht : 0 < t) (ht1 : t ≤ 1) (hρ : ContDiffAt ℝ 2 ρ x)
    (hu : ContDiffAt ℝ 3 u (ρ x • (‖x‖⁻¹ • x) + (v 0)⁻¹ • gradient v 0))
    (hr : levelAreaSecond_radialGradient u v ρ x ≠ 0)
    (hsq : ‖fderiv ℝ (fderiv ℝ (fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
      2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0))) x‖ ≤ A * t)
    (hρ0 : |ρ x| ≤ S / t) (hρ1 : ‖fderiv ℝ ρ x‖ ≤ S / t)
    (hρ2 : ‖fderiv ℝ (fderiv ℝ ρ) x‖ ≤ S / t)
    (hi : |(levelAreaSecond_radialGradient u v ρ x)⁻¹| ≤ D / t ^ 2)
    (ha1 : ‖fderiv ℝ (levelAreaSecond_radialGradient u v ρ) x‖ ≤ D * t ^ 2)
    (ha2 : ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_radialGradient u v ρ)) x‖ ≤ D * t ^ 2)
    (hV0 : ‖levelAreaSecond_tangentialGradient u v ρ x‖ ≤ B * t ^ 4)
    (hV1 : ‖fderiv ℝ (levelAreaSecond_tangentialGradient u v ρ) x‖ ≤ B * t ^ 4)
    (hV2 : ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_tangentialGradient u v ρ)) x‖ ≤
      B * t ^ 4) :
    let N := B * (D + 3 * D ^ 3 + 2 * D ^ 5)
    ‖fderiv ℝ (fderiv ℝ (levelAreaRemainder u v t ρ)) x‖ ≤
      (A + S ^ 2 * (10 * N ^ 2 + N ^ 4)) * t := by
  obtain ⟨h0, h1, h2⟩ := levelAreaSecond_tangentialRatio_bounds_small hx hD hB ht hρ hu
    hr hi ha1 ha2 hV0 hV1 hV2
  exact levelAreaSecond_remainder_bound_of_ratio hx hS (by positivity) ht ht1 hρ hu hr
    hsq hρ0 hρ1 hρ2 h0 h1 h2

/-- Under the original capacitary hypotheses, the squared-radius part of the
area expansion has a uniform `O(t)` second ambient derivative on unit directions. -/
theorem levelAreaSecond_capacitary_radius_square_bound
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ ρ : E3 → ℝ,
        (∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y)) →
        (∀ θ : E3, ‖θ‖ = 1 →
          0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t) →
        ContDiffOn ℝ (⊤ : ℕ∞) ρ {y | y ≠ 0} ∧
        ∀ θ : E3, ‖θ‖ = 1 →
          ‖fderiv ℝ (fderiv ℝ (fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
            2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0))) θ‖ ≤ A * t := by
  obtain ⟨v, r, hr, hv, he, hv0, A, hA, hev⟩ :=
    capacitary_level_radius_derivatives hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨B, hB, hBb⟩ := farQuadrupole_derivative_bounds
    (translated_quadrupole_contDiff v) (kelvinTranslatedQuadrupole_smul v)
  let L := A + B / (v 0) ^ 2
  let P := A + 10 * B / (v 0) ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨v, r, hr, hv, he, hv0,
    2 * A * (v 0 + L) + 2 * P ^ 2 + 2 * L * (10 * B) / (v 0) ^ 2,
    by positivity, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT one_pos] with t htR htr
  have ht : 0 < t := htr.1
  have ht1 : t ≤ 1 := htr.2.le
  intro ρ hhom hroot
  obtain ⟨hρSmooth, hρb⟩ := htR ρ hhom hroot
  refine ⟨hρSmooth, fun θ hθ => ?_⟩
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hρ : ContDiffAt ℝ 2 ρ θ :=
    (hρSmooth.contDiffAt (isOpen_ne.mem_nhds hθ0)).of_le (by simp)
  obtain ⟨hE, hED, hEDD⟩ := hρb θ hθ
  have hq : |kelvinTranslatedQuadrupole v θ| ≤ B := by
    simpa only [farQuadrupole, hθ, one_pow, div_one] using (hBb θ hθ0).1
  have hqD : ‖fderiv ℝ (farQuadrupole (kelvinTranslatedQuadrupole v)) θ‖ ≤ B := by
    simpa only [hθ, one_pow, div_one] using (hBb θ hθ0).2.1
  have hqDD : ‖fderiv ℝ (fderiv ℝ (farQuadrupole (kelvinTranslatedQuadrupole v))) θ‖ ≤
      B := by simpa only [hθ, one_pow, div_one] using (hBb θ hθ0).2.2
  have hρD := (levelArea_radius_derivative_bounds ht.le ht1 hA hB.le hθ hρ
    hqD hqDD hED hEDD).1
  have hcoarse : |ρ θ - v 0 / t| ≤ L := by
    have hterm : |t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| ≤ B / (v 0) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos ht, abs_of_nonneg (sq_nonneg (v 0))]
      exact div_le_div_of_nonneg_right
        ((mul_le_mul ht1 hq (abs_nonneg _) zero_le_one).trans_eq (one_mul B))
        (sq_nonneg _)
    have hE' : |ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| ≤
        A * t ^ 2 := by simpa only [levelRadiusRemainder, hθ, inv_one, one_smul] using hE
    calc
      _ = |(ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)) +
          t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ A * t ^ 2 + B / (v 0) ^ 2 := add_le_add hE' hterm
      _ ≤ L := by dsimp [L]; nlinarith [pow_le_one₀ ht.le ht1 (n := 2)]
  have hqAngular := levelRadius_angular_fderiv_two_bound
    (translated_quadrupole_contDiff v) hB.le hθ hqD hqDD
  exact levelArea_radius_square_fderiv_two_bound hv0 ht ht1 hA (by positivity)
    hL hP hθ0 hρ (hroot θ hθ).1 hcoarse hρD hEDD hqAngular

set_option maxSynthPendingDepth 8 in
-- Three nested continuous-linear-map spaces require deeper instance synthesis.
/-- The quadrupole's third spatial derivative has degree minus six. This
supplies the model counterpart of the translated harmonic error estimate. -/
theorem levelAreaSecond_farQuadrupole_third_derivative_bound {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : E3, x ≠ 0 →
      ‖iteratedFDeriv ℝ 3 (farQuadrupole Q) x‖ ≤ B / ‖x‖ ^ 6 := by
  have hc : ContinuousOn (fderiv ℝ (fderiv ℝ (fderiv ℝ (farQuadrupole Q))))
      (sphere 0 1) := by
    intro x hx
    have hx0 : x ≠ 0 := by intro he; simp [he] at hx
    have h1 := (contDiffAt_farQuadrupole hQ hx0).fderiv_right (m := 2) (by simp)
    have h2 := h1.fderiv_right (m := 1) (by norm_num)
    exact (h2.fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hh (c : ℝ) (hc : 0 < c) (x : E3) :
      fderiv ℝ (fderiv ℝ (fderiv ℝ (farQuadrupole Q))) (c • x) =
        (c ^ 6)⁻¹ • fderiv ℝ (fderiv ℝ (fderiv ℝ (farQuadrupole Q))) x :=
    fderiv_smul_of_negative_homogeneous
      (f := fderiv ℝ (fderiv ℝ (farQuadrupole Q))) (k := 5)
      (fun _ hc x => fderiv_two_farQuadrupole_smul hQh hc x) hc x
  obtain ⟨B, hB, hb⟩ := bound_of_negative_homogeneous
    (f := fderiv ℝ (fderiv ℝ (fderiv ℝ (farQuadrupole Q)))) (k := 6) hc hh
  refine ⟨B, hB, fun x hx => ?_⟩
  have he : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (farQuadrupole Q))) x‖ =
      ‖iteratedFDeriv ℝ 3 (farQuadrupole Q) x‖ := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ (fderiv ℝ (farQuadrupole Q))),
      norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  rw [← he]
  exact hb x hx

end LiquidDrop.CapacitaryK
