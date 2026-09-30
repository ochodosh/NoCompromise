module

public import NoCompromise.Sobolev.H1Density
public import NoCompromise.Sobolev.H1FlatExtension

@[expose] public section

/-!
# Smooth positive-part approximations

The explicit nonnegative regularization has derivative in `[0,1]` and uniform
error at most `ε/2`. Its classical chain rule gives an H¹ gradient contraction
and the stronger energy inequality. On finite measures these approximations
converge in L² even when their input functions vary strongly in L².
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A nonnegative smooth approximation of the positive part. -/
def smoothPositivePart (ε s : ℝ) : ℝ :=
  (Real.sqrt (s ^ 2 + ε ^ 2) + s) / 2

/-- Its derivative, which takes values in the unit interval. -/
def smoothPositivePartSlope (ε s : ℝ) : ℝ :=
  (1 + s / Real.sqrt (s ^ 2 + ε ^ 2)) / 2

lemma smoothPositivePart_sqrt_bounds {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    |s| ≤ Real.sqrt (s ^ 2 + ε ^ 2) ∧
      Real.sqrt (s ^ 2 + ε ^ 2) ≤ |s| + ε := by
  have hp : 0 < s ^ 2 + ε ^ 2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have ha := sq_abs s
  have hn := Real.sqrt_nonneg (s ^ 2 + ε ^ 2)
  constructor <;> nlinarith [abs_nonneg s, sq_nonneg ε, mul_nonneg (abs_nonneg s) hε.le]

lemma smoothPositivePart_nonneg {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ smoothPositivePart ε s := by
  have h := (smoothPositivePart_sqrt_bounds hε s).1
  unfold smoothPositivePart
  linarith [neg_abs_le s]

lemma smoothPositivePart_sub_max_bounds {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ smoothPositivePart ε s - max s 0 ∧
      smoothPositivePart ε s - max s 0 ≤ ε / 2 := by
  obtain ⟨hl, hu⟩ := smoothPositivePart_sqrt_bounds hε s
  unfold smoothPositivePart
  rcases le_total 0 s with hs | hs
  · rw [max_eq_left hs, abs_of_nonneg hs] at *
    constructor <;> linarith
  · rw [max_eq_right hs, abs_of_nonpos hs] at *
    constructor <;> linarith

lemma norm_smoothPositivePart_sub_max_le {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ‖smoothPositivePart ε s - max s 0‖ ≤ ε / 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothPositivePart_sub_max_bounds hε s).1]
  exact (smoothPositivePart_sub_max_bounds hε s).2

lemma smoothPositivePartSlope_mem_Icc {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    smoothPositivePartSlope ε s ∈ Icc (0 : ℝ) 1 := by
  have hp : 0 < Real.sqrt (s ^ 2 + ε ^ 2) := by positivity
  have hs := (smoothPositivePart_sqrt_bounds hε s).1
  have hu : s / Real.sqrt (s ^ 2 + ε ^ 2) ≤ 1 :=
    (div_le_one hp).mpr ((le_abs_self s).trans hs)
  have hl : -1 ≤ s / Real.sqrt (s ^ 2 + ε ^ 2) := by
    apply (le_div_iff₀ hp).mpr
    linarith [neg_abs_le s]
  constructor <;> dsimp [smoothPositivePartSlope] <;> linarith

lemma hasDerivAt_smoothPositivePart {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (smoothPositivePart ε) (smoothPositivePartSlope ε s) s := by
  have hp : 0 < s ^ 2 + ε ^ 2 := by positivity
  have hd := (((((hasDerivAt_id s).pow 2).add_const (ε ^ 2)).sqrt hp.ne').add
    (hasDerivAt_id s)).div_const 2
  convert! hd using 1
  simp only [smoothPositivePartSlope, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one]
  ring

lemma contDiff_smoothPositivePart {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPositivePart ε) := by
  exact ((((contDiff_id.pow 2).add contDiff_const).sqrt
    (fun s => (show 0 < s ^ 2 + ε ^ 2 by positivity).ne')).add contDiff_id).div_const 2

lemma gradient_smoothPositivePart_comp {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => smoothPositivePart ε (f y)) x =
      smoothPositivePartSlope ε (f x) • gradient f x := by
  have hd := (hasDerivAt_smoothPositivePart hε (f x)).comp_hasFDerivAt x
    ((hf.differentiable one_ne_zero x).hasFDerivAt)
  change (toDual ℝ _).symm (fderiv ℝ (fun y => smoothPositivePart ε (f y)) x) = _
  have hd' : HasFDerivAt (fun y => smoothPositivePart ε (f y))
      (smoothPositivePartSlope ε (f x) • fderiv ℝ f x) x := hd
  rw [hd'.fderiv, map_smul]
  rfl

lemma norm_gradient_smoothPositivePart_comp_le {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (fun y => smoothPositivePart ε (f y)) x‖ ≤ ‖gradient f x‖ := by
  rw [gradient_smoothPositivePart_comp hε hf, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (smoothPositivePartSlope_mem_Icc hε _).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (smoothPositivePartSlope_mem_Icc hε _).2

lemma gradient_smoothPositivePart_energy_le {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (fun y => smoothPositivePart ε (f y)) x‖ ^ 2 ≤
      inner ℝ (gradient f x) (gradient (fun y => smoothPositivePart ε (f y)) x) := by
  rw [gradient_smoothPositivePart_comp hε hf, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (smoothPositivePartSlope_mem_Icc hε _).1,
    inner_smul_right, real_inner_self_eq_norm_sq, mul_pow]
  have ha := smoothPositivePartSlope_mem_Icc hε (f x)
  exact mul_le_mul_of_nonneg_right (by nlinarith [ha.1, ha.2]) (sq_nonneg _)

lemma memLp_real_positivePart {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {f : α → ℝ} (hf : MemLp f p μ) : MemLp (fun x => max (f x) 0) p μ := by
  apply hf.norm.mono'
    ((continuous_id.max continuous_const).comp_aestronglyMeasurable hf.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  simpa only [Real.norm_eq_abs, id_eq] using max_le (le_abs_self (f x)) (abs_nonneg (f x))

lemma memLp_smoothPositivePart_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {p : ℝ≥0∞} {f : α → ℝ} (hf : MemLp f p μ)
    {ε : ℝ} (hε : 0 < ε) : MemLp (fun x => smoothPositivePart ε (f x)) p μ := by
  have hm : MemLp (fun x => ‖f x‖ + ε / 2) p μ := hf.norm.add (memLp_const _)
  apply hm.mono' ((contDiff_smoothPositivePart hε).continuous.comp_aestronglyMeasurable
    hf.aestronglyMeasurable)
  filter_upwards [] with x
  have hs := smoothPositivePart_sub_max_bounds hε (f x)
  have hm : max (f x) 0 ≤ ‖f x‖ := by
    rw [Real.norm_eq_abs]
    exact max_le (le_abs_self _) (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothPositivePart_nonneg hε _)]
  linarith

lemma hasH1GradientOn_smoothPositivePart_comp {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hH : HasH1GradientOn f (gradient f) D) {ε : ℝ} (hε : 0 < ε) :
    HasH1GradientOn (fun x => smoothPositivePart ε (f x))
      (gradient (fun x => smoothPositivePart ε (f x))) D := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  have hc : ContDiff ℝ 1 (fun x => smoothPositivePart ε (f x)) :=
    ((contDiff_smoothPositivePart hε).of_le (by simp)).comp hf
  refine ⟨hasWeakGradientOn_of_contDiffOn hD hc.contDiffOn,
    memLp_smoothPositivePart_comp hH.memLp_function hε, ?_⟩
  exact hH.memLp_gradient.norm.mono' (continuous_gradient_of_contDiff hc).aestronglyMeasurable
    (Eventually.of_forall (norm_gradient_smoothPositivePart_comp_le hε hf))

lemma lpNorm_smoothPositivePart_sub_max_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {ε : ℝ} (hε : 0 < ε) :
    lpNorm (fun x => smoothPositivePart ε (f x) - max (g x) 0) 2 μ ≤
      lpNorm (f - g) 2 μ + (ε / 2) * μ.real univ ^ (1 / 2 : ℝ) := by
  have hm : MemLp (fun x => ‖f x - g x‖ + ε / 2) 2 μ :=
    (hf.sub hg).norm.add (memLp_const _)
  have hb (x) : ‖smoothPositivePart ε (f x) - max (g x) 0‖ ≤
      ‖f x - g x‖ + ε / 2 := by
    have hl := (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul (f x) (g x)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] at hl
    have ht := norm_sub_le_norm_sub_add_norm_sub (smoothPositivePart ε (f x))
      (max (f x) 0) (max (g x) 0)
    have hs := norm_smoothPositivePart_sub_max_le hε (f x)
    simp only [Real.norm_eq_abs] at *
    linarith
  have hle := lpNorm_mono_real hm hb
  have ha := lpNorm_add_le (hf.sub hg).norm (g := fun _ => ε / 2) (by norm_num)
  change lpNorm (fun x => ‖f x - g x‖ + ε / 2) 2 μ ≤
    lpNorm (fun x => ‖f x - g x‖) 2 μ + lpNorm (fun _ : α => ε / 2) 2 μ at ha
  have he : lpNorm (fun x => ‖f x - g x‖) 2 μ = lpNorm (f - g) 2 μ := by
    convert! lpNorm_norm (hf.sub hg).aestronglyMeasurable 2 using 1
  rw [he] at ha
  simp only [lpNorm_const' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞), Real.norm_eq_abs,
    abs_of_pos (half_pos hε), ENNReal.toReal_ofNat,
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at ha
  exact hle.trans ha

lemma tendsto_lpNorm_smoothPositivePart_sub_max {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ)
    (hfg : Tendsto (fun j => lpNorm (f j - g) 2 μ) atTop (𝓝 0))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j) :
    Tendsto (fun j => lpNorm
      (fun x => smoothPositivePart (ε j) (f j x) - max (g x) 0) 2 μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => lpNorm_nonneg) (fun j =>
    lpNorm_smoothPositivePart_sub_max_le (hf j) hg (hεpos j))
  simpa using hfg.add ((hε.div_const 2).mul_const (μ.real univ ^ (1 / 2 : ℝ)))

lemma lpNorm_smoothPositivePart_comp_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    lpNorm (fun x => smoothPositivePart ε (f x)) 2 μ ≤
      lpNorm f 2 μ + (ε / 2) * μ.real univ ^ (1 / 2 : ℝ) := by
  have h := lpNorm_smoothPositivePart_sub_max_le hf (memLp_const (0 : ℝ)) hε
  have hz : f - (fun _ : α => (0 : ℝ)) = f := by funext x; simp
  simpa only [max_self, sub_zero, hz] using h

lemma norm_gradientLp_smoothPositivePart_le {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hH : HasH1GradientOn f (gradient f) D) {ε : ℝ} (hε : 0 < ε) :
    ‖(H1Space.ofFunction _ _
      (hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε)).gradientLp‖ ≤
      ‖(H1Space.ofFunction f (gradient f) hH).gradientLp‖ := by
  change ‖(hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε).memLp_gradient.toLp _‖ ≤
    ‖hH.memLp_gradient.toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp,
    toReal_eLpNorm,
    toReal_eLpNorm]
  have hb := lpNorm_mono_real hH.memLp_gradient.norm
    (norm_gradient_smoothPositivePart_comp_le hε hf)
  simpa only [lpNorm_norm hH.memLp_gradient.aestronglyMeasurable] using hb

lemma gradientLp_smoothPositivePart_energy_le {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hH : HasH1GradientOn f (gradient f) D) {ε : ℝ} (hε : 0 < ε) :
    ‖(H1Space.ofFunction _ _
      (hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε)).gradientLp‖ ^ 2 ≤
      inner ℝ (H1Space.ofFunction f (gradient f) hH).gradientLp
        (H1Space.ofFunction _ _
          (hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε)).gradientLp := by
  let v := H1Space.ofFunction _ _
    (hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε)
  let u := H1Space.ofFunction f (gradient f) hH
  change ‖v.gradientLp‖ ^ 2 ≤ inner ℝ u.gradientLp v.gradientLp
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  apply integral_mono_ae (L2.integrable_inner _ _) (L2.integrable_inner _ _)
  filter_upwards [H1Space.gradientLp_ofFunction f (gradient f) hH,
    H1Space.gradientLp_ofFunction _ _
      (hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε)] with x hx hu
  change inner ℝ (v.gradientLp x) (v.gradientLp x) ≤
    inner ℝ (u.gradientLp x) (v.gradientLp x)
  change u.gradientLp x = gradient f x at hx
  change v.gradientLp x = gradient (fun y => smoothPositivePart ε (f y)) x at hu
  rw [hx, hu, real_inner_self_eq_norm_sq]
  exact gradient_smoothPositivePart_energy_le hε hf x

lemma norm_h1_smoothPositivePart_le {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hH : HasH1GradientOn f (gradient f) D) {ε : ℝ} (hε : 0 < ε) :
    ‖H1Space.ofFunction _ _ (hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε)‖ ≤
      2 * ‖H1Space.ofFunction f (gradient f) hH‖ +
        (ε / 2) * (volume D).toReal ^ (1 / 2 : ℝ) := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  let v := H1Space.ofFunction _ _
    (hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε)
  let u := H1Space.ofFunction f (gradient f) hH
  have hfB : ‖v.toLp‖ ≤ ‖u.toLp‖ + (ε / 2) * (volume D).toReal ^ (1 / 2 : ℝ) := by
    change ‖(hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε).memLp_function.toLp _‖ ≤
      ‖hH.memLp_function.toLp _‖ + _
    rw [Lp.norm_toLp, Lp.norm_toLp,
      toReal_eLpNorm,
      toReal_eLpNorm]
    simpa only [Measure.real, Measure.restrict_apply_univ] using
      lpNorm_smoothPositivePart_comp_le hH.memLp_function hε
  have hGB := norm_gradientLp_smoothPositivePart_le hD hvol hf hH hε
  change ‖v.gradientLp‖ ≤ ‖u.gradientLp‖ at hGB
  have hv := v.norm_le_sum
  have hu := u.sum_norm_le
  change ‖v‖ ≤ 2 * ‖u‖ + _
  linarith

end LiquidDrop
