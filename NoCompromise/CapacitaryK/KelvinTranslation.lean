module

public import NoCompromise.Conventions
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic

@[expose] public section

/-!
# Translation of the Kelvin kernels

Chapter 31, `lem:K-normalization`: the translation step removing the dipole.
The estimates use exact algebraic remainders and the reverse triangle inequality.
-/

namespace LiquidDrop.CapacitaryK

open scoped InnerProductSpace

private theorem monopole_scalar (r v q p : ℝ) (hr : 0 < r) (hv : 0 ≤ v)
    (hq : r / 2 ≤ q) (hd : |q - r| ≤ v) (hp : |p| ≤ v * r)
    (hsq : q ^ 2 = r ^ 2 + 2 * p + v ^ 2) :
    |1 / q - 1 / r + p / r ^ 3 - (3 * p ^ 2 - v ^ 2 * r ^ 2) / (2 * r ^ 5)| ≤
      5 * v ^ 3 / r ^ 4 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hd2 : (q - r) ^ 2 ≤ v ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hv] using hd)
  have hfactor : |r * (q - r) - p| ≤ v ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (q - r)]
  have hsum : |r * (q - r) + p| ≤ 2 * r * v := by
    calc
      _ ≤ |r * (q - r)| + |p| := abs_add_le _ _
      _ = r * |q - r| + |p| := by rw [abs_mul, abs_of_pos hr]
      _ ≤ r * v + v * r := add_le_add (mul_le_mul_of_nonneg_left hd hr.le) hp
      _ = _ := by ring
  have hid : 1 / q - 1 / r + p / r ^ 3 -
      (3 * p ^ 2 - v ^ 2 * r ^ 2) / (2 * r ^ 5) =
      -(q - r) ^ 3 / (q * r ^ 3) +
        3 * (r * (q - r) - p) * (r * (q - r) + p) / (2 * r ^ 5) := by
    have hp' : p = (q ^ 2 - r ^ 2 - v ^ 2) / 2 := by linarith
    rw [hp']
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |-(q - r) ^ 3 / (q * r ^ 3)| +
        |3 * (r * (q - r) - p) * (r * (q - r) + p) / (2 * r ^ 5)| := abs_add_le _ _
    _ = |q - r| ^ 3 / (q * r ^ 3) +
        3 * |r * (q - r) - p| * |r * (q - r) + p| / (2 * r ^ 5) := by
      simp only [abs_div, abs_neg, abs_pow, abs_mul, abs_of_pos hr,
        abs_of_pos hq0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ v ^ 3 / ((r / 2) * r ^ 3) + 3 * v ^ 2 * (2 * r * v) / (2 * r ^ 5) := by
      gcongr
    _ = 5 * v ^ 3 / r ^ 4 := by field_simp; ring

/-- The monopole expansion, with absolute remainder constant `5`. -/
theorem inv_norm_add_expansion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x z : E) (hsmall : 2 * ‖z‖ ≤ ‖x‖) (hx : x ≠ 0) :
    |1 / ‖x + z‖ - 1 / ‖x‖ + ⟪z, x⟫_ℝ / ‖x‖ ^ 3 -
      (3 * ⟪z, x⟫_ℝ ^ 2 - ‖z‖ ^ 2 * ‖x‖ ^ 2) / (2 * ‖x‖ ^ 5)| ≤
      5 * ‖z‖ ^ 3 / ‖x‖ ^ 4 := by
  have hd : |‖x + z‖ - ‖x‖| ≤ ‖z‖ := by
    simpa using (abs_norm_sub_norm_le (x + z) x)
  apply monopole_scalar _ _ _ _ (norm_pos_iff.mpr hx) (norm_nonneg z)
  · have := (abs_le.mp hd).1
    linarith
  · exact hd
  · exact abs_real_inner_le_norm z x
  · simpa [real_inner_comm x z] using norm_add_sq_real x z

private theorem cube_difference (r v q : ℝ) (hr : 0 < r) (hv : 0 ≤ v)
    (hq : r / 2 ≤ q) (hd : |q - r| ≤ v) :
    |1 / q ^ 3 - 1 / r ^ 3| ≤ 14 * v / r ^ 4 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hrq : r ≤ 2 * q := by linarith
  have hid : 1 / q ^ 3 - 1 / r ^ 3 =
      -(q - r) * (q ^ 2 + q * r + r ^ 2) / (q ^ 3 * r ^ 3) := by
    field_simp; ring
  rw [hid, abs_div, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ q ^ 2 + q * r + r ^ 2),
    abs_of_pos (by positivity : 0 < q ^ 3 * r ^ 3)]
  calc
    _ ≤ v * (q ^ 2 + q * (2 * q) + (2 * q) ^ 2) / (q ^ 3 * r ^ 3) := by gcongr
    _ = 7 * v / (q * r ^ 3) := by field_simp; ring
    _ ≤ 7 * v / ((r / 2) * r ^ 3) := by gcongr
    _ = 14 * v / r ^ 4 := by field_simp; ring

private theorem cube_remainder (r v q p : ℝ) (hr : 0 < r) (hv : 0 ≤ v)
    (hq : r / 2 ≤ q) (hd : |q - r| ≤ v)
    (hsq : q ^ 2 = r ^ 2 + 2 * p + v ^ 2) :
    |1 / q ^ 3 - 1 / r ^ 3 + 3 * p / r ^ 5| ≤ 25 * v ^ 2 / r ^ 5 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hrq : r ≤ 2 * q := by linarith
  have hd2 : (q - r) ^ 2 ≤ v ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hv] using hd)
  have hfactor : |p - r * (q - r)| ≤ v ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (q - r)]
  have hid : 1 / q ^ 3 - 1 / r ^ 3 + 3 * p / r ^ 5 =
      (q - r) ^ 2 * (3 * q ^ 2 + 2 * q * r + r ^ 2) / (q ^ 3 * r ^ 4) +
        3 * (p - r * (q - r)) / r ^ 5 := by field_simp; ring
  rw [hid]
  calc
    _ ≤ |(q - r) ^ 2 * (3 * q ^ 2 + 2 * q * r + r ^ 2) / (q ^ 3 * r ^ 4)| +
        |3 * (p - r * (q - r)) / r ^ 5| := abs_add_le _ _
    _ = (q - r) ^ 2 * (3 * q ^ 2 + 2 * q * r + r ^ 2) / (q ^ 3 * r ^ 4) +
        3 * |p - r * (q - r)| / r ^ 5 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (q - r) ^ 2 *
        (3 * q ^ 2 + 2 * q * r + r ^ 2) / (q ^ 3 * r ^ 4))]
      simp [abs_div, abs_mul, abs_of_pos hr]
    _ ≤ v ^ 2 * (3 * q ^ 2 + 2 * q * (2 * q) + (2 * q) ^ 2) /
        (q ^ 3 * r ^ 4) + 3 * v ^ 2 / r ^ 5 := by gcongr
    _ = 11 * v ^ 2 / (q * r ^ 4) + 3 * v ^ 2 / r ^ 5 := by field_simp; ring
    _ ≤ 11 * v ^ 2 / ((r / 2) * r ^ 4) + 3 * v ^ 2 / r ^ 5 := by gcongr
    _ = 25 * v ^ 2 / r ^ 5 := by field_simp; ring

/-- The dipole expansion, with absolute remainder constant `39`. -/
theorem dipole_add_expansion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a x z : E) (hsmall : 2 * ‖z‖ ≤ ‖x‖) (hx : x ≠ 0) :
    |⟪a, x + z⟫_ℝ / ‖x + z‖ ^ 3 - ⟪a, x⟫_ℝ / ‖x‖ ^ 3 -
      (⟪a, z⟫_ℝ * ‖x‖ ^ 2 - 3 * ⟪a, x⟫_ℝ * ⟪z, x⟫_ℝ) / ‖x‖ ^ 5| ≤
      39 * ‖a‖ * ‖z‖ ^ 2 / ‖x‖ ^ 4 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr0 : ‖x‖ ≠ 0 := ne_of_gt hr
  have hd : |‖x + z‖ - ‖x‖| ≤ ‖z‖ := by
    simpa using (abs_norm_sub_norm_le (x + z) x)
  have hq : ‖x‖ / 2 ≤ ‖x + z‖ := by have := (abs_le.mp hd).1; linarith
  have hq0 : ‖x + z‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hq)
  have hsq : ‖x + z‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪z, x⟫_ℝ + ‖z‖ ^ 2 := by
    simpa [real_inner_comm x z] using norm_add_sq_real x z
  have hc := cube_difference ‖x‖ ‖z‖ ‖x + z‖ hr (norm_nonneg _) hq hd
  have he := cube_remainder ‖x‖ ‖z‖ ‖x + z‖ ⟪z, x⟫_ℝ hr (norm_nonneg _) hq hd hsq
  have hid : ⟪a, x + z⟫_ℝ / ‖x + z‖ ^ 3 - ⟪a, x⟫_ℝ / ‖x‖ ^ 3 -
      (⟪a, z⟫_ℝ * ‖x‖ ^ 2 - 3 * ⟪a, x⟫_ℝ * ⟪z, x⟫_ℝ) / ‖x‖ ^ 5 =
      ⟪a, x⟫_ℝ * (1 / ‖x + z‖ ^ 3 - 1 / ‖x‖ ^ 3 + 3 * ⟪z, x⟫_ℝ / ‖x‖ ^ 5) +
      ⟪a, z⟫_ℝ * (1 / ‖x + z‖ ^ 3 - 1 / ‖x‖ ^ 3) := by
    rw [inner_add_right]
    field_simp; ring
  rw [hid]
  calc
    _ ≤ |⟪a, x⟫_ℝ| * |1 / ‖x + z‖ ^ 3 - 1 / ‖x‖ ^ 3 + 3 * ⟪z, x⟫_ℝ / ‖x‖ ^ 5| +
        |⟪a, z⟫_ℝ| * |1 / ‖x + z‖ ^ 3 - 1 / ‖x‖ ^ 3| := by
      rw [← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    _ ≤ (‖a‖ * ‖x‖) * (25 * ‖z‖ ^ 2 / ‖x‖ ^ 5) +
        (‖a‖ * ‖z‖) * (14 * ‖z‖ / ‖x‖ ^ 4) := by
      gcongr
      · exact abs_real_inner_le_norm a x
      · exact abs_real_inner_le_norm a z
    _ = _ := by field_simp; ring

private theorem fifth_difference (r v q : ℝ) (hr : 0 < r) (hv : 0 ≤ v)
    (hq : r / 2 ≤ q) (hd : |q - r| ≤ v) :
    |1 / q ^ 5 - 1 / r ^ 5| ≤ 62 * v / r ^ 6 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hrq : r ≤ 2 * q := by linarith
  have hid : 1 / q ^ 5 - 1 / r ^ 5 =
      -(q - r) * (q ^ 4 + q ^ 3 * r + q ^ 2 * r ^ 2 + q * r ^ 3 + r ^ 4) /
        (q ^ 5 * r ^ 5) := by field_simp; ring
  rw [hid, abs_div, abs_mul, abs_neg,
    abs_of_nonneg (by positivity :
      0 ≤ q ^ 4 + q ^ 3 * r + q ^ 2 * r ^ 2 + q * r ^ 3 + r ^ 4),
    abs_of_pos (by positivity : 0 < q ^ 5 * r ^ 5)]
  calc
    _ ≤ v * (q ^ 4 + q ^ 3 * (2 * q) + q ^ 2 * (2 * q) ^ 2 +
        q * (2 * q) ^ 3 + (2 * q) ^ 4) / (q ^ 5 * r ^ 5) := by gcongr
    _ = 31 * v / (q * r ^ 5) := by field_simp; ring
    _ ≤ 31 * v / ((r / 2) * r ^ 5) := by gcongr
    _ = 62 * v / r ^ 6 := by field_simp; ring

/-- The quadrupole translation bound, with absolute constant `158`.
Symmetry of the continuous bilinear form is not required. -/
theorem quadrupole_add_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (x z : E)
    (hsmall : 2 * ‖z‖ ≤ ‖x‖) (hx : x ≠ 0) :
    |B (x + z) (x + z) / ‖x + z‖ ^ 5 - B x x / ‖x‖ ^ 5| ≤
      158 * ‖B‖ * ‖z‖ / ‖x‖ ^ 4 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr0 : ‖x‖ ≠ 0 := ne_of_gt hr
  have hz : ‖z‖ ≤ ‖x‖ := by linarith [norm_nonneg z]
  have hd : |‖x + z‖ - ‖x‖| ≤ ‖z‖ := by
    simpa using (abs_norm_sub_norm_le (x + z) x)
  have hq : ‖x‖ / 2 ≤ ‖x + z‖ := by have := (abs_le.mp hd).1; linarith
  have hqpos : 0 < ‖x + z‖ := lt_of_lt_of_le (by positivity) hq
  have hq0 : ‖x + z‖ ≠ 0 := ne_of_gt hqpos
  have hf := fifth_difference ‖x‖ ‖z‖ ‖x + z‖ hr (norm_nonneg _) hq hd
  have hB (u v : E) : |B u v| ≤ ‖B‖ * ‖u‖ * ‖v‖ := by
    simpa only [Real.norm_eq_abs] using B.le_opNorm₂ u v
  have hnum : |B (x + z) (x + z) - B x x| ≤ 3 * ‖B‖ * ‖x‖ * ‖z‖ := by
    have hid : B (x + z) (x + z) - B x x = B x z + B z x + B z z := by
      simp only [map_add, add_apply]
      ring
    rw [hid]
    calc
      _ ≤ |B x z + B z x| + |B z z| := abs_add_le _ _
      _ ≤ |B x z| + |B z x| + |B z z| :=
        add_le_add (abs_add_le (B x z) (B z x)) le_rfl
      _ ≤ ‖B‖ * ‖x‖ * ‖z‖ + ‖B‖ * ‖z‖ * ‖x‖ + ‖B‖ * ‖z‖ * ‖z‖ := by
        gcongr <;> apply hB
      _ ≤ ‖B‖ * ‖x‖ * ‖z‖ + ‖B‖ * ‖z‖ * ‖x‖ + ‖B‖ * ‖x‖ * ‖z‖ := by gcongr
      _ = _ := by ring
  have hid : B (x + z) (x + z) / ‖x + z‖ ^ 5 - B x x / ‖x‖ ^ 5 =
      (B (x + z) (x + z) - B x x) / ‖x + z‖ ^ 5 +
        B x x * (1 / ‖x + z‖ ^ 5 - 1 / ‖x‖ ^ 5) := by ring
  rw [hid]
  calc
    _ ≤ |(B (x + z) (x + z) - B x x) / ‖x + z‖ ^ 5| +
        |B x x * (1 / ‖x + z‖ ^ 5 - 1 / ‖x‖ ^ 5)| := abs_add_le _ _
    _ = |B (x + z) (x + z) - B x x| / ‖x + z‖ ^ 5 +
        |B x x| * |1 / ‖x + z‖ ^ 5 - 1 / ‖x‖ ^ 5| := by
      rw [abs_div, abs_pow, abs_of_pos hqpos, abs_mul]
    _ ≤ (3 * ‖B‖ * ‖x‖ * ‖z‖) / (‖x‖ / 2) ^ 5 +
        (‖B‖ * ‖x‖ * ‖x‖) * (62 * ‖z‖ / ‖x‖ ^ 6) := by
      gcongr
      exact hB x x
    _ = _ := by field_simp; ring

/-- Translating by `C⁻¹ • a` cancels the dipole exactly. -/
theorem translation_dipole_cancellation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a x : E) (C : ℝ) (hC : C ≠ 0) :
    C * (-⟪C⁻¹ • a, x⟫_ℝ / ‖x‖ ^ 3) + ⟪a, x⟫_ℝ / ‖x‖ ^ 3 = 0 := by
  rw [real_inner_smul_left]
  field_simp
  ring

/-- The degree-two coefficients left by the monopole and dipole translations combine
into the quadrupole with the opposite sign and coefficient `1 / (2 * C)`. -/
theorem translation_quadrupole_coefficient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a x : E) (C : ℝ) (hC : C ≠ 0) :
    C * ((3 * ⟪C⁻¹ • a, x⟫_ℝ ^ 2 - ‖C⁻¹ • a‖ ^ 2 * ‖x‖ ^ 2) / 2) +
      (⟪a, C⁻¹ • a⟫_ℝ * ‖x‖ ^ 2 - 3 * ⟪a, x⟫_ℝ * ⟪C⁻¹ • a, x⟫_ℝ) =
      -(3 * ⟪a, x⟫_ℝ ^ 2 - ‖a‖ ^ 2 * ‖x‖ ^ 2) / (2 * C) := by
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

/-- Coordinate polynomial produced by translating the dipole by `C⁻¹ • a`. -/
noncomputable def translationQuadrupolePolynomial (a : Fin 3 → ℝ) (C : ℝ)
    (x : Fin 3 → ℝ) : ℝ :=
  -(3 * (∑ i, a i * x i) ^ 2 - (∑ i, a i ^ 2) * (∑ i, x i ^ 2)) / (2 * C)

/-- The coordinate polynomial is the invariant quadrupole expression on Euclidean space. -/
theorem translationQuadrupolePolynomial_eq (a x : EuclideanSpace ℝ (Fin 3)) (C : ℝ) :
    translationQuadrupolePolynomial (fun i => a i) C (fun i => x i) =
      -(3 * ⟪a, x⟫_ℝ ^ 2 - ‖a‖ ^ 2 * ‖x‖ ^ 2) / (2 * C) := by
  simp [translationQuadrupolePolynomial, PiLp.inner_apply,
    EuclideanSpace.real_norm_sq_eq, mul_comm]

private theorem second_deriv_quadratic (A B D t : ℝ) :
    deriv (deriv (fun s : ℝ => A * s ^ 2 + B * s + D)) t = 2 * A := by
  have hfirst : deriv (fun s : ℝ => A * s ^ 2 + B * s + D) =
      fun s => 2 * A * s + B := by
    funext s
    convert! ((((hasDerivAt_id s).pow 2).const_mul A).add
      ((hasDerivAt_id s).const_mul B) |>.add_const D).deriv using 1
    simp only [id_eq]
    ring
  rw [hfirst]
  convert! (((hasDerivAt_id t).const_mul (2 * A)).add_const B).deriv using 1
  ring

/-- The sum of the second coordinate partials of the translated quadrupole is zero.
A coordinate partial is expressed by varying that coordinate with `Function.update`. -/
theorem translationQuadrupolePolynomial_laplacian (a x : Fin 3 → ℝ) (C : ℝ) :
    (∑ i : Fin 3, deriv (deriv (fun t : ℝ =>
      translationQuadrupolePolynomial a C (Function.update x i t))) (x i)) = 0 := by
  have hslice (i : Fin 3) :
      (fun t : ℝ => translationQuadrupolePolynomial a C (Function.update x i t)) =
      (fun t : ℝ => (-(3 * a i ^ 2 - ∑ j, a j ^ 2) / (2 * C)) * t ^ 2 +
        (-(6 * a i * (∑ j, a j * (Function.update x i 0) j)) / (2 * C)) * t +
        translationQuadrupolePolynomial a C (Function.update x i 0)) := by
    funext t
    fin_cases i <;> simp [translationQuadrupolePolynomial, Fin.sum_univ_three,
      Function.update] <;> ring
  simp_rw [hslice, second_deriv_quadratic, Fin.sum_univ_three]
  ring

end LiquidDrop.CapacitaryK
