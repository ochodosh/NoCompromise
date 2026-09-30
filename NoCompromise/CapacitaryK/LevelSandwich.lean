module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# `lem:K-level-asymptotics` (`eq:K-rt`, two-sided form): small levels lie between two radial graphs

For a positive continuous `U` on `ℝ³` with `U(y) = C/|y| + q(y)/|y|⁵ + O(|y|⁻⁴)`, `q` continuous
and 2-homogeneous (for the translated capacitary potential, `q = Q` is the quadrupole of
`eq:K-expansion`), the sublevel set `{U ≤ t}` lies, for small `t`, between the exterior radial
graphs `|y| ≥ C/t + t q(θ)/C² ± A t²`, `θ = y/|y|`, i.e.
`r_t(θ) = (C/t)(1 + q(θ) t²/C³ + O(t³))` (`eq:K-rt`) in the form used by the volume route to
`eq:K-p-expansion`.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace LiquidDrop.CapacitaryK.LevelSandwich

/-- The bracket in `φ(a) - φ(b) = (a - b) · bracket` for `φ(s) = s⁴ - C s³ - κ t² s`. -/
lemma bracket_pos {C κ t a b : ℝ} (hC : 0 < C) (hb : 7 * C / 8 ≤ b) (hab : b ≤ a)
    (hκ : |κ| * t ^ 2 ≤ C ^ 3 / 8) :
    0 < (a - C) * (a ^ 2 + a * b + b ^ 2) + b ^ 3 - κ * t ^ 2 := by
  have hκ' : κ * t ^ 2 ≤ C ^ 3 / 8 :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self κ) (sq_nonneg t)) hκ
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  have hb3 : (7 * C / 8) ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ (by positivity) hb 3
  have hC3 : 0 < C ^ 3 := pow_pos hC 3
  have h2 : 0 ≤ a ^ 2 + a * b + b ^ 2 := by positivity
  have h78 : (7 * C / 8) ^ 3 = 343 / 512 * C ^ 3 := by ring
  rcases le_or_gt C a with h | h
  · have : 0 ≤ (a - C) * (a ^ 2 + a * b + b ^ 2) := mul_nonneg (by linarith) h2
    linarith
  · have h1 : a ^ 2 + a * b + b ^ 2 ≤ 3 * C ^ 2 := by nlinarith
    have h3 : -(C / 8) * (a ^ 2 + a * b + b ^ 2) ≤ (a - C) * (a ^ 2 + a * b + b ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    have h4 : (C / 8) * (a ^ 2 + a * b + b ^ 2) ≤ (C / 8) * (3 * C ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : (C / 8) * (3 * C ^ 2) = 3 / 8 * C ^ 3 := by ring
    linarith

lemma phi_sub (C κ t a b : ℝ) :
    (a ^ 4 - C * a ^ 3 - κ * t ^ 2 * a) - (b ^ 4 - C * b ^ 3 - κ * t ^ 2 * b) =
      (a - b) * ((a - C) * (a ^ 2 + a * b + b ^ 2) + b ^ 3 - κ * t ^ 2) := by ring

/-- Value of `φ` at the model radius `s = C + e`, `e = t²κ/C² + E`: the `t³` term. -/
lemma phi_at (C κ t E : ℝ) (hC : C ≠ 0) :
    let e := t ^ 2 * κ / C ^ 2 + E
    let s := C + e
    s ^ 4 - C * s ^ 3 - κ * t ^ 2 * s = κ * t ^ 2 * s * e * (s + C) / C ^ 2 + E * s ^ 3 := by
  intro e s
  simp only [s, e]
  field_simp
  ring

/-- Inner inclusion, real form: above the upper radial graph, `C σ³ + κ t² σ + M t³ ≤ σ⁴`. -/
lemma inner_real {C M κ t σ : ℝ} (hC : 0 < C) (hM : 0 ≤ M) (ht : 0 < t)
    (hκ : |κ| * t ^ 2 ≤ C ^ 3 / 8)
    (he : |t ^ 2 * κ / C ^ 2 + 2 * (M + 1) / C ^ 3 * t ^ 3| ≤ C / 8)
    (hsmall : 3 * |κ| * t ^ 2 * |t ^ 2 * κ / C ^ 2 + 2 * (M + 1) / C ^ 3 * t ^ 3| ≤ t ^ 3 / 2)
    (hσ : C + (t ^ 2 * κ / C ^ 2 + 2 * (M + 1) / C ^ 3 * t ^ 3) ≤ σ) :
    C * σ ^ 3 + κ * t ^ 2 * σ + M * t ^ 3 ≤ σ ^ 4 := by
  set E := 2 * (M + 1) / C ^ 3 * t ^ 3 with hE
  set e := t ^ 2 * κ / C ^ 2 + E with he_def
  set s := C + e with hs_def
  have hphi := phi_at C κ t E hC.ne'
  simp only at hphi
  rw [← he_def, ← hs_def] at hphi
  have hs1 : 7 * C / 8 ≤ s := by
    have := neg_abs_le e; simp only [hs_def]; linarith
  have hs2 : s ≤ 9 * C / 8 := by
    have := le_abs_self e; simp only [hs_def]; linarith
  have hs0 : 0 < s := by linarith
  -- the error term
  have hq : s * (s + C) / C ^ 2 ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hq0 : 0 ≤ s * (s + C) / C ^ 2 := by positivity
  have herr : |κ * t ^ 2 * s * e * (s + C) / C ^ 2| ≤ t ^ 3 / 2 := by
    have : κ * t ^ 2 * s * e * (s + C) / C ^ 2 = (κ * e * t ^ 2) * (s * (s + C) / C ^ 2) := by
      ring
    rw [this, abs_mul, abs_of_nonneg hq0, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg t)]
    calc |κ| * |e| * t ^ 2 * (s * (s + C) / C ^ 2) ≤ |κ| * |e| * t ^ 2 * 3 :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = 3 * |κ| * t ^ 2 * |e| := by ring
      _ ≤ t ^ 3 / 2 := hsmall
  have hs3 : C ^ 3 / 2 ≤ s ^ 3 := by
    have : (7 * C / 8) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by positivity) hs1 3
    nlinarith [pow_pos hC 3]
  have hEs : (M + 1) * t ^ 3 ≤ E * s ^ 3 := by
    have hE' : E = 2 * (M + 1) * t ^ 3 / C ^ 3 := by rw [hE]; ring
    rw [hE', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : 0 ≤ 2 * (M + 1) * t ^ 3 := by positivity
    nlinarith
  have hphis : M * t ^ 3 ≤ s ^ 4 - C * s ^ 3 - κ * t ^ 2 * s := by
    rw [hphi]; have := neg_abs_le (κ * t ^ 2 * s * e * (s + C) / C ^ 2); nlinarith
  have hmono := phi_sub C κ t σ s
  have hbr := bracket_pos hC hs1 hσ hκ
  have : 0 ≤ (σ - s) * ((σ - C) * (σ ^ 2 + σ * s + s ^ 2) + s ^ 3 - κ * t ^ 2) :=
    mul_nonneg (by linarith) hbr.le
  nlinarith


/-- Outer inclusion, real form, near the model radius. -/
lemma outer_real {C M κ t σ : ℝ} (hC : 0 < C) (hM : 0 ≤ M) (ht : 0 < t)
    (hκ : |κ| * t ^ 2 ≤ C ^ 3 / 8)
    (he : |t ^ 2 * κ / C ^ 2 + -(2 * (M + 1) / C ^ 3 * t ^ 3)| ≤ C / 8)
    (hsmall : 3 * |κ| * t ^ 2 * |t ^ 2 * κ / C ^ 2 + -(2 * (M + 1) / C ^ 3 * t ^ 3)| ≤ t ^ 3 / 2)
    (hσ7 : 7 * C / 8 ≤ σ)
    (hσ : σ < C + (t ^ 2 * κ / C ^ 2 + -(2 * (M + 1) / C ^ 3 * t ^ 3))) :
    σ ^ 4 + M * t ^ 3 < C * σ ^ 3 + κ * t ^ 2 * σ := by
  set E := -(2 * (M + 1) / C ^ 3 * t ^ 3) with hE
  set e := t ^ 2 * κ / C ^ 2 + E with he_def
  set s := C + e with hs_def
  have hphi := phi_at C κ t E hC.ne'
  simp only at hphi
  rw [← he_def, ← hs_def] at hphi
  have hs1 : 7 * C / 8 ≤ s := by
    have := neg_abs_le e; simp only [hs_def]; linarith
  have hs2 : s ≤ 9 * C / 8 := by
    have := le_abs_self e; simp only [hs_def]; linarith
  have hs0 : 0 < s := by linarith
  have hq : s * (s + C) / C ^ 2 ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hq0 : 0 ≤ s * (s + C) / C ^ 2 := by positivity
  have herr : |κ * t ^ 2 * s * e * (s + C) / C ^ 2| ≤ t ^ 3 / 2 := by
    have : κ * t ^ 2 * s * e * (s + C) / C ^ 2 = (κ * e * t ^ 2) * (s * (s + C) / C ^ 2) := by
      ring
    rw [this, abs_mul, abs_of_nonneg hq0, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg t)]
    calc |κ| * |e| * t ^ 2 * (s * (s + C) / C ^ 2) ≤ |κ| * |e| * t ^ 2 * 3 :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = 3 * |κ| * t ^ 2 * |e| := by ring
      _ ≤ t ^ 3 / 2 := hsmall
  have hs3 : C ^ 3 / 2 ≤ s ^ 3 := by
    have : (7 * C / 8) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by positivity) hs1 3
    nlinarith [pow_pos hC 3]
  have hEs : E * s ^ 3 ≤ -((M + 1) * t ^ 3) := by
    have hE' : E = -(2 * (M + 1) * t ^ 3 / C ^ 3) := by rw [hE]; ring
    rw [hE', neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : 0 ≤ 2 * (M + 1) * t ^ 3 := by positivity
    nlinarith
  have hphis : s ^ 4 - C * s ^ 3 - κ * t ^ 2 * s < -(M * t ^ 3) := by
    rw [hphi]; have := le_abs_self (κ * t ^ 2 * s * e * (s + C) / C ^ 2)
    have : 0 < t ^ 3 := pow_pos ht 3
    nlinarith
  have hmono := phi_sub C κ t s σ
  have hbr := bracket_pos hC hσ7 hσ.le hκ
  have : 0 ≤ (s - σ) * ((s - C) * (s ^ 2 + s * σ + σ ^ 2) + σ ^ 3 - κ * t ^ 2) :=
    mul_nonneg (by linarith) hbr.le
  nlinarith

/-- Outer inclusion, real form, far below the model radius. -/
lemma outer_small {C M κ t σ R : ℝ} (hM : 0 ≤ M) (ht : 0 < t) (hR : 0 < R)
    (hσ0 : t * R ≤ σ) (hσ7 : σ ≤ 7 * C / 8)
    (hRb : |κ| / R ^ 2 + M / R ^ 3 < C / 8) :
    σ ^ 4 + M * t ^ 3 < C * σ ^ 3 + κ * t ^ 2 * σ := by
  have hσ : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have htσ : t ≤ σ / R := by rw [le_div_iff₀ hR]; linarith
  have ht2 : t ^ 2 ≤ (σ / R) ^ 2 := pow_le_pow_left₀ ht.le htσ 2
  have ht3 : t ^ 3 ≤ (σ / R) ^ 3 := pow_le_pow_left₀ ht.le htσ 3
  have hk1 : -(κ * t ^ 2 * σ) ≤ |κ| * (σ / R) ^ 2 * σ := by
    have h1 : -(κ * t ^ 2 * σ) ≤ |κ| * t ^ 2 * σ := by
      have := neg_abs_le κ
      have h0 : 0 ≤ t ^ 2 * σ := by positivity
      nlinarith
    have h2 : |κ| * t ^ 2 * σ ≤ |κ| * (σ / R) ^ 2 * σ := by
      apply mul_le_mul_of_nonneg_right _ hσ.le
      exact mul_le_mul_of_nonneg_left ht2 (abs_nonneg κ)
    linarith
  have hm1 : M * t ^ 3 ≤ M * (σ / R) ^ 3 := mul_le_mul_of_nonneg_left ht3 hM
  have hsum : |κ| * (σ / R) ^ 2 * σ + M * (σ / R) ^ 3 = σ ^ 3 * (|κ| / R ^ 2 + M / R ^ 3) := by
    field_simp
  have hσ3 : 0 < σ ^ 3 := pow_pos hσ 3
  have hlt : σ ^ 3 * (|κ| / R ^ 2 + M / R ^ 3) < σ ^ 3 * (C / 8) :=
    mul_lt_mul_of_pos_left hRb hσ3
  have h4 : σ ^ 4 ≤ 7 * C / 8 * σ ^ 3 := by
    have : σ ^ 4 = σ * σ ^ 3 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hσ7 hσ3.le
  nlinarith

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A continuous 2-homogeneous function is bounded by `B |y|²`. -/
lemma exists_quadratic_bound {q : E₃ → ℝ} (hqc : Continuous q)
    (hqh : ∀ (c : ℝ) (y : E₃), q (c • y) = c ^ 2 * q y) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : E₃, |q y| ≤ B * ‖y‖ ^ 2 := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : E₃) 1).exists_bound_of_continuousOn hqc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · have h0 : q 0 = 0 := by
      have := hqh 0 0; simpa using this
    simp [h0]
  · have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hθ : ‖y‖⁻¹ • y ∈ sphere (0 : E₃) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hyθ : q y = ‖y‖ ^ 2 * q (‖y‖⁻¹ • y) := by
      rw [← hqh, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [hyθ, abs_mul, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _ ▸ hB _ hθ).trans (le_max_left _ _))
      (by positivity)


/-- Eventual smallness of a continuous function vanishing at `0`, along `𝓝[>] 0`. -/
lemma eventually_lt_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) {c : ℝ}
    (hc : 0 < c) : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < c := by
  have : ∀ᶠ t in 𝓝 (0 : ℝ), f t < c :=
    hf.continuousAt.eventually_lt continuousAt_const (by rw [h0]; exact hc)
  exact nhdsWithin_le_nhds this

end LiquidDrop.CapacitaryK.LevelSandwich

namespace LiquidDrop.CapacitaryK

open LevelSandwich

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- `lem:K-level-asymptotics`, `eq:K-rt` in two-sided form. If `U > 0` is continuous on `ℝ³`
and `U(y) = C/|y| + q(y)/|y|⁵ + O(|y|⁻⁴)` with `q` continuous and 2-homogeneous, then for some
`A` and all small `t > 0` the sublevel set `{U ≤ t}` contains the exterior of the radial graph
`|y| = C/t + t q(θ)/C² + A t²` and is contained in the exterior of `|y| = C/t + t q(θ)/C² - A t²`,
where `q(θ) = q(y)/|y|²`, `θ = y/|y|`. -/
theorem level_sandwich {U q : E₃ → ℝ} (hUc : Continuous U) (hUpos : ∀ y, 0 < U y)
    (hqc : Continuous q) (hqh : ∀ (c : ℝ) (y : E₃), q (c • y) = c ^ 2 * q y)
    {C R M : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hU : ∀ y : E₃, R ≤ ‖y‖ → |U y - C / ‖y‖ - q y / ‖y‖ ^ 5| ≤ M / ‖y‖ ^ 4) :
    ∃ A : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∀ y : E₃, y ≠ 0 → C / t + t * q y / (C ^ 2 * ‖y‖ ^ 2) + A * t ^ 2 ≤ ‖y‖ → U y ≤ t) ∧
      (∀ y : E₃, U y ≤ t → y ≠ 0 ∧ C / t + t * q y / (C ^ 2 * ‖y‖ ^ 2) - A * t ^ 2 ≤ ‖y‖) := by
  set M' := max M 0 with hM'def
  have hM' : 0 ≤ M' := le_max_right _ _
  have hU' : ∀ y : E₃, R ≤ ‖y‖ → |U y - C / ‖y‖ - q y / ‖y‖ ^ 5| ≤ M' / ‖y‖ ^ 4 := by
    intro y hy
    have hn : 0 < ‖y‖ := lt_of_lt_of_le hR hy
    exact (hU y hy).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨B, hB0, hB⟩ := exists_quadratic_bound hqc hqh
  -- the radius beyond which the far-field inequality handles the small-`σ` range
  have hRlim : Tendsto (fun r : ℝ => B / r ^ 2 + M' / r ^ 3) atTop (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ => B / r ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    have h3 : Tendsto (fun r : ℝ => M' / r ^ 3) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    simpa using h2.add h3
  obtain ⟨R₂, hR₂R, hR₂b⟩ := ((eventually_ge_atTop (max R 1)).and
    (hRlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < C / 8)))).exists
  have hR₂ : R ≤ R₂ := (le_max_left _ _).trans hR₂R
  have hR₂0 : 0 < R₂ := hR.trans_le hR₂
  -- the minimum of `U` on the closed ball of radius `R₂`
  obtain ⟨y₀, -, hy₀⟩ := (isCompact_closedBall (0 : E₃) R₂).exists_isMinOn
    ⟨0, mem_closedBall_self hR₂0.le⟩ hUc.continuousOn
  set m := U y₀
  have hm : 0 < m := hUpos y₀
  set A := 2 * (M' + 1) / C ^ 3 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A, ?_⟩
  have e1 := eventually_lt_of_continuous (f := fun t => t) continuous_id rfl hm
  have e2 := eventually_lt_of_continuous (f := fun t => B * t ^ 2) (by fun_prop) (by simp)
    (by positivity : (0 : ℝ) < C ^ 3 / 8)
  have e3 := eventually_lt_of_continuous (f := fun t => t ^ 2 * B / C ^ 2 + A * t ^ 3)
    (by fun_prop) (by simp) (by positivity : (0 : ℝ) < C / 8)
  have e4 := eventually_lt_of_continuous (f := fun t => 6 * B * (t * B / C ^ 2 + A * t ^ 2))
    (by fun_prop) (by simp) one_pos
  have e5 := eventually_lt_of_continuous (f := fun t => 8 * R₂ * t) (by fun_prop) (by simp)
    (by positivity : (0 : ℝ) < 7 * C)
  filter_upwards [self_mem_nhdsWithin, e1, e2, e3, e4, e5] with t ht ht1 ht2 ht3 ht4 ht5
  simp only [mem_Ioi] at ht
  -- the angular coefficient `κ = q(y)/|y|²`
  have hκ : ∀ y : E₃, |q y / ‖y‖ ^ 2| ≤ B := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [hB0]
    · have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
      rw [abs_div, abs_of_pos (pow_pos hn 2), div_le_iff₀ (pow_pos hn 2)]
      exact hB y
  have hκt : ∀ κ : ℝ, |κ| ≤ B → |κ| * t ^ 2 ≤ C ^ 3 / 8 := fun κ hκB =>
    le_trans (mul_le_mul_of_nonneg_right hκB (sq_nonneg t)) ht2.le
  have heb : ∀ κ : ℝ, |κ| ≤ B → ∀ E : ℝ, |E| ≤ A * t ^ 3 →
      |t ^ 2 * κ / C ^ 2 + E| ≤ t ^ 2 * B / C ^ 2 + A * t ^ 3 := by
    intro κ hκB E hE
    refine (abs_add_le _ _).trans (add_le_add ?_ hE)
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg t), abs_of_pos (by positivity : (0:ℝ) < C ^ 2)]
    gcongr
  have hsm : ∀ κ : ℝ, |κ| ≤ B → ∀ E : ℝ, |E| ≤ A * t ^ 3 →
      3 * |κ| * t ^ 2 * |t ^ 2 * κ / C ^ 2 + E| ≤ t ^ 3 / 2 := by
    intro κ hκB E hE
    have h1 := heb κ hκB E hE
    calc 3 * |κ| * t ^ 2 * |t ^ 2 * κ / C ^ 2 + E|
        ≤ 3 * B * t ^ 2 * (t ^ 2 * B / C ^ 2 + A * t ^ 3) := by gcongr
      _ = t ^ 3 / 2 * (6 * B * (t * B / C ^ 2 + A * t ^ 2)) := by ring
      _ ≤ t ^ 3 / 2 * 1 := by gcongr
      _ = t ^ 3 / 2 := mul_one _
  have hAt : |A * t ^ 3| ≤ A * t ^ 3 := (abs_of_nonneg (by positivity)).le
  have hAt' : |-(A * t ^ 3)| ≤ A * t ^ 3 := by rw [abs_neg]; exact hAt
  -- scaling identity for the radial graph
  have hscale : ∀ (y : E₃) (s : ℝ), t * (C / t + t * q y / (C ^ 2 * ‖y‖ ^ 2) + s * t ^ 2) =
      C + (t ^ 2 * (q y / ‖y‖ ^ 2) / C ^ 2 + s * t ^ 3) := by
    intro y s
    rcases eq_or_ne ‖y‖ 0 with h | h
    · simp [h]; field_simp
    · field_simp; ring
  constructor
  · -- inner inclusion
    intro y hy hle
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set κ := q y / ‖y‖ ^ 2 with hκdef
    set σ := t * ‖y‖ with hσdef
    have hσ : C + (t ^ 2 * κ / C ^ 2 + A * t ^ 3) ≤ σ := by
      rw [← hscale y A]; exact mul_le_mul_of_nonneg_left hle ht.le
    have he := heb κ (hκ y) _ hAt
    have hreal := inner_real (M := M') hC hM' ht (hκt κ (hκ y)) (he.trans ht3.le)
      (hsm κ (hκ y) _ hAt) hσ
    -- `|y|` is in the far-field range
    have hσ7 : 7 * C / 8 ≤ σ := by
      have := neg_abs_le (t ^ 2 * κ / C ^ 2 + A * t ^ 3); linarith
    have hyR : R ≤ ‖y‖ := by
      refine hR₂.trans ?_
      by_contra hlt
      have hlt := lt_of_not_ge hlt
      have : σ < t * R₂ := mul_lt_mul_of_pos_left hlt ht
      linarith
    have hval := hU' y hyR
    have hqy : q y / ‖y‖ ^ 5 = κ / ‖y‖ ^ 3 := by rw [hκdef]; field_simp
    rw [hqy] at hval
    have hup : U y ≤ C / ‖y‖ + κ / ‖y‖ ^ 3 + M' / ‖y‖ ^ 4 := by
      have := le_abs_self (U y - C / ‖y‖ - κ / ‖y‖ ^ 3); linarith
    refine hup.trans ?_
    have hr4 : 0 < ‖y‖ ^ 4 := by positivity
    have key : C * ‖y‖ ^ 3 + κ * ‖y‖ + M' ≤ t * ‖y‖ ^ 4 := by
      have h := hreal
      rw [hσdef] at h
      have ht3 : 0 < t ^ 3 := pow_pos ht 3
      have : t ^ 3 * (C * ‖y‖ ^ 3 + κ * ‖y‖ + M') ≤ t ^ 3 * (t * ‖y‖ ^ 4) := by
        nlinarith
      exact le_of_mul_le_mul_left this ht3
    have hsplit : C / ‖y‖ + κ / ‖y‖ ^ 3 + M' / ‖y‖ ^ 4 =
        (C * ‖y‖ ^ 3 + κ * ‖y‖ + M') / ‖y‖ ^ 4 := by field_simp
    rw [hsplit, div_le_iff₀ hr4]
    exact key
  · -- outer inclusion
    intro y hy
    have hyR₂ : R₂ < ‖y‖ := by
      by_contra hle
      have hle := le_of_not_gt hle
      have hmin : m ≤ U y := hy₀ (mem_closedBall_zero_iff.mpr hle)
      linarith
    have hn : 0 < ‖y‖ := hR₂0.trans hyR₂
    refine ⟨norm_pos_iff.mp hn, ?_⟩
    set κ := q y / ‖y‖ ^ 2 with hκdef
    set σ := t * ‖y‖ with hσdef
    by_contra hlt
    have hlt := lt_of_not_ge hlt
    have hσ : σ < C + (t ^ 2 * κ / C ^ 2 + -(A * t ^ 3)) := by
      have := mul_lt_mul_of_pos_left hlt ht
      rw [show C / t + t * q y / (C ^ 2 * ‖y‖ ^ 2) - A * t ^ 2 =
        C / t + t * q y / (C ^ 2 * ‖y‖ ^ 2) + (-A) * t ^ 2 by ring, hscale y (-A)] at this
      rw [hσdef]; linarith
    have hreal : σ ^ 4 + M' * t ^ 3 < C * σ ^ 3 + κ * t ^ 2 * σ := by
      rcases le_or_gt (7 * C / 8) σ with h7 | h7
      · have he := heb κ (hκ y) _ hAt'
        exact outer_real hC hM' ht (hκt κ (hκ y)) (he.trans ht3.le) (hsm κ (hκ y) _ hAt') h7 hσ
      · exact outer_small hM' ht hR₂0 (mul_le_mul_of_nonneg_left hyR₂.le ht.le) h7.le
          (lt_of_le_of_lt (by gcongr; exact hκ y) hR₂b)
    have hval := hU' y (hR₂.trans hyR₂.le)
    have hqy : q y / ‖y‖ ^ 5 = κ / ‖y‖ ^ 3 := by rw [hκdef]; field_simp
    rw [hqy] at hval
    have hlow : C / ‖y‖ + κ / ‖y‖ ^ 3 - M' / ‖y‖ ^ 4 ≤ U y := by
      have := neg_abs_le (U y - C / ‖y‖ - κ / ‖y‖ ^ 3); linarith
    have hr4 : 0 < ‖y‖ ^ 4 := by positivity
    have key : t * ‖y‖ ^ 4 < C * ‖y‖ ^ 3 + κ * ‖y‖ - M' := by
      have h := hreal
      rw [hσdef] at h
      have ht3 : 0 < t ^ 3 := pow_pos ht 3
      have : t ^ 3 * (t * ‖y‖ ^ 4) < t ^ 3 * (C * ‖y‖ ^ 3 + κ * ‖y‖ - M') := by
        nlinarith
      exact lt_of_mul_lt_mul_left this ht3.le
    have hsplit : C / ‖y‖ + κ / ‖y‖ ^ 3 - M' / ‖y‖ ^ 4 =
        (C * ‖y‖ ^ 3 + κ * ‖y‖ - M') / ‖y‖ ^ 4 := by field_simp
    rw [hsplit, div_le_iff₀ hr4] at hlow
    have : U y * ‖y‖ ^ 4 ≤ t * ‖y‖ ^ 4 := mul_le_mul_of_nonneg_right hy hr4.le
    linarith

end LiquidDrop.CapacitaryK
