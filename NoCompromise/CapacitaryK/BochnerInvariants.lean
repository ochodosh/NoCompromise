module

public import NoCompromise.CapacitaryK.GradNormExpansion

@[expose] public section

/-!
# Far-field bounds for the Bochner invariants

Quantitative remainder estimates for Chapter 31, `eq:K-p-expansion`.
All differential decompositions below are used strictly outside the radius `R`.
-/

noncomputable section
open Filter Set Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

private lemma decay_mono {r A : ℝ} (hr : 1 ≤ r) (hA : 0 ≤ A)
    {p q : ℕ} (hpq : p ≤ q) : A / r ^ q ≤ A / r ^ p := by
  exact div_le_div_of_nonneg_left hA (by positivity)
    (pow_le_pow_right₀ hr hpq)

private lemma decay_mul {r a b A B : ℝ} {p q : ℕ}
    (hr : 0 < r) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : |a| ≤ A / r ^ p) (hb : |b| ≤ B / r ^ q) :
    |a * b| ≤ (A * B) / r ^ (p + q) := by
  rw [abs_mul]
  calc
    _ ≤ (A / r ^ p) * (B / r ^ q) :=
      mul_le_mul ha hb (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

private lemma square_remainder_bound {r a b e A B D : ℝ} {p q s t : ℕ}
    (hr : 1 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (ha : |a| ≤ A / r ^ p) (hb : |b| ≤ B / r ^ q)
    (he : |e| ≤ D / r ^ s) (hqs : q ≤ s) (ht₁ : t ≤ p + s)
    (ht₂ : t ≤ q + q) :
    |(a + b + e) ^ 2 - (a ^ 2 + 2 * a * b)| ≤
      (2 * A * D + (B + D) ^ 2) / r ^ t := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbe : |b + e| ≤ (B + D) / r ^ q := by
    calc
      _ ≤ |b| + |e| := abs_add_le _ _
      _ ≤ B / r ^ q + D / r ^ q :=
        add_le_add hb (he.trans (decay_mono hr hD hqs))
      _ = _ := by ring
  have hae := (decay_mul hr0 hA hD ha he).trans
    (decay_mono hr (mul_nonneg hA hD) ht₁)
  have hbe₂ := (decay_mul hr0 (add_nonneg hB hD) (add_nonneg hB hD) hbe hbe).trans
    (decay_mono hr (mul_nonneg (add_nonneg hB hD) (add_nonneg hB hD)) ht₂)
  calc
    _ = |2 * (a * e) + (b + e) * (b + e)| := by congr 1; ring
    _ ≤ |2 * (a * e)| + |(b + e) * (b + e)| := abs_add_le _ _
    _ ≤ 2 * (A * D / r ^ t) + (B + D) * (B + D) / r ^ t := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hae (by norm_num)) hbe₂
    _ = _ := by ring

private lemma gradient_coord_bound (u : E3 → ℝ) (x : E3) (i : Fin 3) :
    |gradient u x i| ≤ ‖fderiv ℝ u x‖ := by
  rw [gradient_apply_eq_fderiv_basisVec]
  simpa [basisVec] using (fderiv ℝ u x).le_opNorm (basisVec i)

private lemma gradient_sub_coord {f g : E3 → ℝ} {x : E3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    gradient (fun y => f y - g y) x i = gradient f x i - gradient g x i := by
  simp only [gradient_apply_eq_fderiv_basisVec, fderiv_fun_sub hf hg,
    sub_apply]

private lemma hess_sub_coord {f g : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (i j : Fin 3) :
    hess (fun y => f y - g y) x i j = hess f x i j - hess g x i j := by
  have he : fderiv ℝ (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y - fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hz
    exact fderiv_fun_sub (hy.differentiableAt (by norm_num))
      (hz.differentiableAt (by norm_num))
  rw [hess_eq_fderiv_two (hf.sub hg), hess_eq_fderiv_two hf, hess_eq_fderiv_two hg,
    he.fderiv_eq, fderiv_fun_sub
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
      ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)]
  rfl

/-- The gradient-square part of the far-field invariant expansion. Only the
first derivative of the remainder is needed for this estimate. -/
theorem gradNorm_sq_far_expansion {U Q : E3 → ℝ} {C R M : ℝ} (hC : 0 < C)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U {x | R < ‖x‖})
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hW : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5) x‖ ≤ M / ‖x‖ ^ 5) :
    ∃ R' K B : ℝ, 0 < R' ∧ 0 ≤ K ∧ 0 ≤ B ∧ ∀ x : E3, R' ≤ ‖x‖ →
      |farQuadrupole Q x| ≤ B / ‖x‖ ^ 3 ∧
      |gradNorm U x ^ 2 - (C ^ 2 / ‖x‖ ^ 4 +
        6 * C * farQuadrupole Q x / ‖x‖ ^ 3)| ≤ K / ‖x‖ ^ 7 := by
  obtain ⟨B, hB, hb⟩ := farQuadrupole_derivative_bounds hQ hQh
  refine ⟨max (R + 1) 1, 3 * (2 * C * |M| + (B + |M|) ^ 2), B,
    zero_lt_one.trans_le (le_max_right _ _), by positivity, hB.le, ?_⟩
  intro x hx
  have hr : 1 ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hr0 : 0 < ‖x‖ := zero_lt_one.trans_le hr
  have hx0 : x ≠ 0 := norm_pos_iff.mp hr0
  have hrR : R < ‖x‖ := lt_of_lt_of_le (by linarith : R < R + 1)
    ((le_max_left _ _).trans hx)
  have hdU :=
    (hU.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hrR)).differentiableAt
      (by simp)
  have hdm := (contDiffAt_monopole C hx0).differentiableAt (by simp)
  have hdq := (contDiffAt_farQuadrupole hQ hx0).differentiableAt (by simp)
  let W := fun y : E3 => U y - C / ‖y‖ - farQuadrupole Q y
  have hg (i : Fin 3) : gradient U x i = gradient (fun y : E3 => C / ‖y‖) x i +
      gradient (farQuadrupole Q) x i + gradient W x i := by
    dsimp [W]
    rw [gradient_sub_coord (f := fun y => U y - C / ‖y‖) (hdU.sub hdm) hdq,
      gradient_sub_coord hdU hdm]
    ring
  have hm (i : Fin 3) : |gradient (fun y : E3 => C / ‖y‖) x i| ≤ C / ‖x‖ ^ 2 := by
    exact (gradient_coord_bound _ _ _).trans_eq
      ((gradNorm_eq_norm_fderiv _ _).symm.trans (gradNorm_monopole hC.le hx0))
  have hq (i : Fin 3) : |gradient (farQuadrupole Q) x i| ≤ B / ‖x‖ ^ 4 :=
    (gradient_coord_bound _ _ _).trans (hb x hx0).2.1
  have hw (i : Fin 3) : |gradient W x i| ≤ |M| / ‖x‖ ^ 5 := by
    exact (gradient_coord_bound _ _ _).trans ((hW x hrR.le).trans
      (div_le_div_of_nonneg_right (le_abs_self M) (by positivity)))
  have hc : (∑ i : Fin 3, gradient (fun y : E3 => C / ‖y‖) x i *
      gradient (farQuadrupole Q) x i) = 3 * C * farQuadrupole Q x / ‖x‖ ^ 3 := by
    have hi := monopole_farQuadrupole_gradient_inner C hQ hQh hx0
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      mul_comm] using hi
  have he : gradNorm U x ^ 2 - (C ^ 2 / ‖x‖ ^ 4 +
      6 * C * farQuadrupole Q x / ‖x‖ ^ 3) =
      ∑ i : Fin 3, ((gradient (fun y : E3 => C / ‖y‖) x i +
        gradient (farQuadrupole Q) x i + gradient W x i) ^ 2 -
        (gradient (fun y : E3 => C / ‖y‖) x i ^ 2 +
          2 * gradient (fun y : E3 => C / ‖y‖) x i * gradient (farQuadrupole Q) x i)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [← gradNorm_sq, gradNorm_monopole hC.le hx0, hc, gradNorm_sq]
    simp_rw [hg]
    ring
  refine ⟨(hb x hx0).1, ?_⟩
  rw [he]
  calc
    _ ≤ ∑ i : Fin 3, |(gradient (fun y : E3 => C / ‖y‖) x i +
        gradient (farQuadrupole Q) x i + gradient W x i) ^ 2 -
        (gradient (fun y : E3 => C / ‖y‖) x i ^ 2 +
          2 * gradient (fun y : E3 => C / ‖y‖) x i * gradient (farQuadrupole Q) x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, (2 * C * |M| + (B + |M|) ^ 2) / ‖x‖ ^ 7 := by
      exact Finset.sum_le_sum fun i _ => square_remainder_bound hr hC.le hB.le
        (abs_nonneg M) (hm i) (hq i) (hw i) (by norm_num) (by norm_num) (by norm_num)
    _ = _ := by simp; ring


private lemma sum_three_abs_le {f : Fin 3 → ℝ} {A : ℝ}
    (h : ∀ i, |f i| ≤ A) : |∑ i, f i| ≤ 3 * A := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, A := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

private lemma monopole_hess_coord_bound {C : ℝ} (hC : 0 ≤ C) {x : E3}
    (hx : x ≠ 0) (i j : Fin 3) :
    |hess (fun y : E3 => C / ‖y‖) x i j| ≤ 4 * C / ‖x‖ ^ 3 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  have hj : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
  have hij : |x i * x j| ≤ ‖x‖ ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
  rw [hess_monopole C hx, abs_mul, abs_of_nonneg hC]
  calc
    _ ≤ C * (|3 * x i * x j / ‖x‖ ^ 5| +
        |(if i = j then (1 : ℝ) else 0) / ‖x‖ ^ 3|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hC
    _ ≤ C * (3 * ‖x‖ ^ 2 / ‖x‖ ^ 5 + 1 / ‖x‖ ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add
      · rw [show 3 * x i * x j = 3 * (x i * x j) by ring, abs_div,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
          abs_of_pos (pow_pos hn 5)]
        gcongr
      · split_ifs <;> simp [abs_of_pos (pow_pos hn 3)]
    _ = _ := by field_simp; ring

/-- The Hilbert--Schmidt Hessian-square part of the far-field expansion. -/
theorem hessNormSq_far_expansion {U Q : E3 → ℝ} {C R M : ℝ} (hC : 0 < C)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U {x | R < ‖x‖})
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hQl : ∀ x : E3, laplacianN Q x = 0)
    (hW : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5)) x‖
        ≤ M / ‖x‖ ^ 6) :
    ∃ R' K : ℝ, 0 < R' ∧ 0 ≤ K ∧ ∀ x : E3, R' ≤ ‖x‖ →
      |hessNormSq U x - (6 * C ^ 2 / ‖x‖ ^ 6 +
        72 * C * farQuadrupole Q x / ‖x‖ ^ 5)| ≤ K / ‖x‖ ^ 9 := by
  obtain ⟨B, hB, hb⟩ := farQuadrupole_derivative_bounds hQ hQh
  refine ⟨max (R + 1) 1, 9 * (2 * (4 * C) * |M| + (B + |M|) ^ 2),
    zero_lt_one.trans_le (le_max_right _ _), by positivity, ?_⟩
  intro x hx
  have hr : 1 ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hr)
  have hrR : R < ‖x‖ := lt_of_lt_of_le (by linarith : R < R + 1)
    ((le_max_left _ _).trans hx)
  have hu : ContDiffAt ℝ 2 U x :=
    (hU.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hrR)).of_le (by simp)
  have hm : ContDiffAt ℝ 2 (fun y : E3 => C / ‖y‖) x :=
    (contDiffAt_monopole C hx0).of_le (by simp)
  have hq : ContDiffAt ℝ 2 (farQuadrupole Q) x :=
    (contDiffAt_farQuadrupole hQ hx0).of_le (by simp)
  let W := fun y : E3 => U y - C / ‖y‖ - farQuadrupole Q y
  have hw : ContDiffAt ℝ 2 W x := (hu.sub hm).sub hq
  have hsplit (i j : Fin 3) : hess U x i j = hess (fun y : E3 => C / ‖y‖) x i j +
      hess (farQuadrupole Q) x i j + hess W x i j := by
    dsimp [W]
    rw [hess_sub_coord (f := fun y => U y - C / ‖y‖) (hu.sub hm) hq,
      hess_sub_coord hu hm]
    ring
  have hmb (i j : Fin 3) := monopole_hess_coord_bound hC.le hx0 i j
  have hqb (i j : Fin 3) : |hess (farQuadrupole Q) x i j| ≤ B / ‖x‖ ^ 5 :=
    (abs_hess_le_norm_fderiv_two hq i j).trans (hb x hx0).2.2
  have hwb (i j : Fin 3) : |hess W x i j| ≤ |M| / ‖x‖ ^ 6 :=
    (abs_hess_le_norm_fderiv_two hw i j).trans ((hW x hrR.le).trans
      (div_le_div_of_nonneg_right (le_abs_self M) (by positivity)))
  have he : hessNormSq U x - (6 * C ^ 2 / ‖x‖ ^ 6 +
      72 * C * farQuadrupole Q x / ‖x‖ ^ 5) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ((hess (fun y : E3 => C / ‖y‖) x i j + hess (farQuadrupole Q) x i j +
          hess W x i j) ^ 2 - (hess (fun y : E3 => C / ‖y‖) x i j ^ 2 +
            2 * hess (fun y : E3 => C / ‖y‖) x i j * hess (farQuadrupole Q) x i j)) := by
    simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← hessNormSq, hessNormSq_monopole C hx0,
      monopole_farQuadrupole_hess_pairing C hQ hQh hQl hx0, hessNormSq]
    simp_rw [hsplit]
    ring
  rw [he]
  have hi (i j : Fin 3) := square_remainder_bound (t := 9) hr
    (by positivity : 0 ≤ 4 * C) hB.le (abs_nonneg M)
    (hmb i j) (hqb i j) (hwb i j) (by norm_num) (by norm_num) (by norm_num)
  exact (sum_three_abs_le fun i => sum_three_abs_le fun j => hi i j).trans_eq (by ring)


private lemma decay_add {r a b A B : ℝ} {p : ℕ}
    (ha : |a| ≤ A / r ^ p) (hb : |b| ≤ B / r ^ p) :
    |a + b| ≤ (A + B) / r ^ p := by
  exact ((abs_add_le _ _).trans (add_le_add ha hb)).trans_eq (by ring)

private lemma decay_mul_to {r a b A B : ℝ} {p q t : ℕ}
    (hr : 1 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a| ≤ A / r ^ p) (hb : |b| ≤ B / r ^ q) (ht : t ≤ p + q) :
    |a * b| ≤ A * B / r ^ t :=
  (decay_mul (zero_lt_one.trans_le hr) hA hB ha hb).trans
    (decay_mono hr (mul_nonneg hA hB) ht)

/-- The Hessian-gradient-square part of the far-field expansion. Harmonicity
of the quadrupole is not needed for this invariant. -/
theorem hessGradNormSq_far_expansion {U Q : E3 → ℝ} {C R M : ℝ} (hC : 0 < C)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U {x | R < ‖x‖})
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hW : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5) x‖ ≤ M / ‖x‖ ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5)) x‖
        ≤ M / ‖x‖ ^ 6) :
    ∃ R' K : ℝ, 0 < R' ∧ 0 ≤ K ∧ ∀ x : E3, R' ≤ ‖x‖ →
      |hessGradNormSq U x - (4 * C ^ 4 / ‖x‖ ^ 10 +
        72 * C ^ 3 * farQuadrupole Q x / ‖x‖ ^ 9)| ≤ K / ‖x‖ ^ 13 := by
  obtain ⟨B, hB, hb⟩ := farQuadrupole_derivative_bounds hQ hQh
  let D := 3 * (5 * C * |M| + (B + |M|) ^ 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨max (R + 1) 1, 3 * (2 * (12 * C ^ 2) * D + (15 * C * B + D) ^ 2),
    zero_lt_one.trans_le (le_max_right _ _), by positivity, ?_⟩
  intro x hx
  have hr : 1 ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hr)
  have hrR : R < ‖x‖ := lt_of_lt_of_le (by linarith : R < R + 1)
    ((le_max_left _ _).trans hx)
  let m := fun y : E3 => C / ‖y‖
  let q := farQuadrupole Q
  let W := fun y : E3 => U y - m y - q y
  have hu : ContDiffAt ℝ 2 U x :=
    (hU.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hrR)).of_le (by simp)
  have hm : ContDiffAt ℝ 2 m x := (contDiffAt_monopole C hx0).of_le (by simp)
  have hq : ContDiffAt ℝ 2 q x := (contDiffAt_farQuadrupole hQ hx0).of_le (by simp)
  have hw : ContDiffAt ℝ 2 W x := (hu.sub hm).sub hq
  have hgsplit (i : Fin 3) : gradient U x i = gradient m x i + gradient q x i +
      gradient W x i := by
    dsimp [W]
    rw [gradient_sub_coord (f := fun y => U y - m y)
      ((hu.sub hm).differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num)),
      gradient_sub_coord (hu.differentiableAt (by norm_num))
        (hm.differentiableAt (by norm_num))]
    ring
  have hsplit (i j : Fin 3) : hess U x i j = hess m x i j + hess q x i j + hess W x i j := by
    dsimp [W]
    rw [hess_sub_coord (f := fun y => U y - m y) (hu.sub hm) hq, hess_sub_coord hu hm]
    ring
  have hma (i : Fin 3) : |gradient m x i| ≤ C / ‖x‖ ^ 2 :=
    (gradient_coord_bound _ _ _).trans_eq
      ((gradNorm_eq_norm_fderiv _ _).symm.trans (gradNorm_monopole hC.le hx0))
  have hqa (i : Fin 3) : |gradient q x i| ≤ B / ‖x‖ ^ 4 :=
    (gradient_coord_bound _ _ _).trans (hb x hx0).2.1
  have hwa (i : Fin 3) : |gradient W x i| ≤ |M| / ‖x‖ ^ 5 :=
    (gradient_coord_bound _ _ _).trans (((hW x hrR.le).1).trans
      (div_le_div_of_nonneg_right (le_abs_self M) (by positivity)))
  have hmA (i j : Fin 3) : |hess m x i j| ≤ (4 * C) / ‖x‖ ^ 3 :=
    monopole_hess_coord_bound hC.le hx0 i j
  have hqA (i j : Fin 3) : |hess q x i j| ≤ B / ‖x‖ ^ 5 :=
    (abs_hess_le_norm_fderiv_two hq i j).trans (hb x hx0).2.2
  have hwA (i j : Fin 3) : |hess W x i j| ≤ |M| / ‖x‖ ^ 6 :=
    (abs_hess_le_norm_fderiv_two hw i j).trans (((hW x hrR.le).2).trans
      (div_le_div_of_nonneg_right (le_abs_self M) (by positivity)))
  let b := fun i : Fin 3 => (∑ j, hess q x i j * gradient m x j) +
    (∑ j, hess m x i j * gradient q x j)
  let e := fun i : Fin 3 => ∑ j,
    (hess m x i j * gradient W x j + hess q x i j * gradient q x j +
      hess q x i j * gradient W x j + hess W x i j * gradient m x j +
      hess W x i j * gradient q x j + hess W x i j * gradient W x j)
  have he (i : Fin 3) : hessGrad U x i = hessGrad m x i + b i + e i := by
    simp only [hessGrad, hsplit, hgsplit, b, e, Fin.sum_univ_three]
    ring
  have ha (i : Fin 3) : |hessGrad m x i| ≤ (12 * C ^ 2) / ‖x‖ ^ 5 := by
    exact (sum_three_abs_le fun j => decay_mul_to hr (by positivity) hC.le
      (hmA i j) (hma j) (by norm_num : 5 ≤ 3 + 2)).trans_eq (by ring)
  have hbb (i : Fin 3) : |b i| ≤ (15 * C * B) / ‖x‖ ^ 7 := by
    exact ((abs_add_le _ _).trans (add_le_add
      (sum_three_abs_le fun j => decay_mul_to hr hB.le hC.le (hqA i j) (hma j)
        (by norm_num : 7 ≤ 5 + 2))
      (sum_three_abs_le fun j => decay_mul_to hr (by positivity) hB.le (hmA i j) (hqa j)
        (by norm_num : 7 ≤ 3 + 4)))).trans_eq (by ring)
  have heb (i : Fin 3) : |e i| ≤ D / ‖x‖ ^ 8 := by
    have hij (j : Fin 3) := decay_add (decay_add (decay_add (decay_add (decay_add
      (decay_mul_to hr (by positivity) (abs_nonneg M) (hmA i j) (hwa j)
        (by norm_num : 8 ≤ 3 + 5))
      (decay_mul_to hr hB.le hB.le (hqA i j) (hqa j) (by norm_num : 8 ≤ 5 + 4)))
      (decay_mul_to hr hB.le (abs_nonneg M) (hqA i j) (hwa j) (by norm_num : 8 ≤ 5 + 5)))
      (decay_mul_to hr (abs_nonneg M) hC.le (hwA i j) (hma j) (by norm_num : 8 ≤ 6 + 2)))
      (decay_mul_to hr (abs_nonneg M) hB.le (hwA i j) (hqa j) (by norm_num : 8 ≤ 6 + 4)))
      (decay_mul_to hr (abs_nonneg M) (abs_nonneg M) (hwA i j) (hwa j)
        (by norm_num : 8 ≤ 6 + 5))
    exact (sum_three_abs_le hij).trans_eq (by dsimp [D]; ring)
  have hid : hessGradNormSq U x - (4 * C ^ 4 / ‖x‖ ^ 10 +
      72 * C ^ 3 * farQuadrupole Q x / ‖x‖ ^ 9) =
      ∑ i : Fin 3, ((hessGrad m x i + b i + e i) ^ 2 -
        (hessGrad m x i ^ 2 + 2 * hessGrad m x i * b i)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [← hessGradNormSq, hessGradNormSq_monopole C hx0]
    have hp : (∑ i, hessGrad m x i * b i) =
        36 * C ^ 3 * farQuadrupole Q x / ‖x‖ ^ 9 :=
      monopole_farQuadrupole_hessGrad_pairing C hQ hQh hx0
    rw [hp, hessGradNormSq]
    simp_rw [he]
    ring
  rw [hid]
  exact (sum_three_abs_le fun i => square_remainder_bound (t := 13) hr
    (by positivity : 0 ≤ 12 * C ^ 2) (by positivity : 0 ≤ 15 * C * B) hD
    (ha i) (hbb i) (heb i) (by norm_num) (by norm_num) (by norm_num)).trans_eq (by ring)


/-- Simultaneous far-field expansions of the three invariants in the Bochner
formula, with one radius and one nonnegative remainder constant. -/
theorem bochner_invariants_far {U Q : E3 → ℝ} {C R M : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U {x | R < ‖x‖})
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hQl : ∀ x : E3, laplacianN Q x = 0)
    (hW : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5) x‖ ≤ M / ‖x‖ ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5)) x‖ ≤ M / ‖x‖ ^ 6) :
    ∃ R' K B : ℝ, 0 < R' ∧ 0 ≤ K ∧ 0 ≤ B ∧ ∀ x : E3, R' ≤ ‖x‖ →
      |farQuadrupole Q x| ≤ B / ‖x‖ ^ 3 ∧
      |hessNormSq U x - (6 * C ^ 2 / ‖x‖ ^ 6 + 72 * C * farQuadrupole Q x / ‖x‖ ^ 5)|
        ≤ K / ‖x‖ ^ 9 ∧
      |hessGradNormSq U x - (4 * C ^ 4 / ‖x‖ ^ 10 + 72 * C ^ 3 * farQuadrupole Q x / ‖x‖ ^ 9)|
        ≤ K / ‖x‖ ^ 13 ∧
      |gradNorm U x ^ 2 - (C ^ 2 / ‖x‖ ^ 4 + 6 * C * farQuadrupole Q x / ‖x‖ ^ 3)|
        ≤ K / ‖x‖ ^ 7 := by
  obtain ⟨Rg, Kg, B, _, hKg, hB, hg⟩ :=
    gradNorm_sq_far_expansion hC hU hQ hQh (fun x hx => (hW x hx).1)
  obtain ⟨RH, KH, _, _, hH⟩ :=
    hessNormSq_far_expansion hC hU hQ hQh hQl (fun x hx => (hW x hx).2)
  obtain ⟨RHg, KHg, _, _, hHg⟩ := hessGradNormSq_far_expansion hC hU hQ hQh hW
  refine ⟨max R (max Rg (max RH RHg)), max Kg (max KH KHg), B,
    hR.trans_le (le_max_left _ _), hKg.trans (le_max_left _ _), hB, ?_⟩
  intro x hx
  have hxg : Rg ≤ ‖x‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxH : RH ≤ ‖x‖ :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hxHg : RHg ≤ ‖x‖ :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  refine ⟨(hg x hxg).1, (hH x hxH).trans ?_, (hHg x hxHg).trans ?_, (hg x hxg).2.trans ?_⟩
  · exact div_le_div_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
  · exact div_le_div_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
  · exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

end LiquidDrop.CapacitaryK
