import NoCompromise.Sobolev.H1PositivePart
import NoCompromise.Sobolev.H1Zero

/-!
# Nonnegative smooth testing in H¹₀

A cutoff of the smooth positive-part regularization stays inside the domain.
The explicit cutoff gradient error can be made arbitrarily small. Applying
this construction to the defining smooth approximation of H¹₀ gives nonnegative
interior tests converging weakly in H¹. Distributional inequalities therefore
extend to all nonnegative H¹₀ tests.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma smoothPositivePart_zero {ε : ℝ} (hε : 0 < ε) :
    smoothPositivePart ε 0 = ε / 2 := by
  simp [smoothPositivePart, Real.sqrt_sq hε.le]

lemma cutoff_smoothPositivePart_eq {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ∀ᶠ x in 𝓝ˢ (tsupport f), χ x = 1) {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin n)) :
    χ x * smoothPositivePart ε (f x) =
      smoothPositivePart ε (f x) + (ε / 2) * (χ x - 1) := by
  by_cases hx : x ∈ tsupport f
  · have he : χ x = 1 := (hχ.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
    simp [he]
  · rw [image_eq_zero_of_notMem_tsupport hx, smoothPositivePart_zero hε]
    ring

lemma gradient_cutoff_smoothPositivePart {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hcχ : ContDiff ℝ 1 χ) (hχ : ∀ᶠ x in 𝓝ˢ (tsupport f), χ x = 1)
    {ε : ℝ} (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => χ y * smoothPositivePart ε (f y)) x =
      gradient (fun y => smoothPositivePart ε (f y)) x + (ε / 2) • gradient χ x := by
  have hp : ContDiff ℝ 1 (fun y => smoothPositivePart ε (f y)) :=
    ((contDiff_smoothPositivePart hε).of_le (by simp)).comp hf
  rw [gradient_mul hcχ hp]
  by_cases hx : x ∈ tsupport f
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := hχ.filter_mono (nhds_le_nhdsSet hx)
    have hgrad : gradient χ x = 0 := by
      rw [he.gradient_eq, gradient_fun_const]
    rw [he.self_of_nhds, hgrad]
    simp
  · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hgrad : gradient f x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hx (tsupport_gradient_subset f hh))
    rw [gradient_smoothPositivePart_comp hε hf, hgrad, smul_zero, smul_zero,
      zero_add, hz, smoothPositivePart_zero hε, zero_add]

lemma lpNorm_cutoff_smoothPositivePart_sub_le {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hvol : volume D < ∞)
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ∀ᶠ x in 𝓝ˢ (tsupport f), χ x = 1)
    (hbχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    lpNorm (fun x => χ x * smoothPositivePart ε (f x) - smoothPositivePart ε (f x))
      2 (volume.restrict D) ≤ (ε / 2) * (volume D).toReal ^ (1 / 2 : ℝ) := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  have hb (x) : ‖χ x * smoothPositivePart ε (f x) - smoothPositivePart ε (f x)‖ ≤
      ε / 2 := by
    rw [cutoff_smoothPositivePart_eq hχ hε, add_sub_cancel_left, norm_mul,
      Real.norm_eq_abs, abs_of_pos (half_pos hε), Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hbχ x).2)]
    have hh : -(χ x - 1) ≤ 1 := by linarith [(hbχ x).1]
    exact mul_le_of_le_one_right (half_pos hε).le hh
  have h := lpNorm_mono_real (memLp_const (p := 2) (μ := volume.restrict D) (ε / 2)) hb
  simpa only [lpNorm_const' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞), Real.norm_eq_abs, abs_of_pos (half_pos hε),
    ENNReal.toReal_ofNat, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
    Measure.real, Measure.restrict_apply_univ] using h

lemma lpNorm_gradient_cutoff_smoothPositivePart_le {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hH : HasH1GradientOn f (gradient f) D) (hcχ : ContDiff ℝ 1 χ)
    (hχ : ∀ᶠ x in 𝓝ˢ (tsupport f), χ x = 1) {ε : ℝ} (hε : 0 < ε) :
    lpNorm (gradient (fun x => χ x * smoothPositivePart ε (f x))) 2 (volume.restrict D) ≤
      lpNorm (gradient f) 2 (volume.restrict D) +
        (ε / 2) * lpNorm (gradient χ) 2 (volume.restrict D) := by
  have hp := hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε
  have he : gradient (fun x => χ x * smoothPositivePart ε (f x)) =
      gradient (fun x => smoothPositivePart ε (f x)) + (ε / 2) • gradient χ :=
    funext (gradient_cutoff_smoothPositivePart hf hcχ hχ hε)
  rw [he]
  apply (lpNorm_add_le hp.memLp_gradient (by norm_num)).trans
  rw [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
  apply add_le_add _ le_rfl
  have h := lpNorm_mono_real hH.memLp_gradient.norm
    (norm_gradient_smoothPositivePart_comp_le hε hf)
  simpa only [lpNorm_norm hH.memLp_gradient.aestronglyMeasurable] using h

lemma norm_h1_cutoff_smoothPositivePart_le {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hH : HasH1GradientOn f (gradient f) D) (hcχ : ContDiff ℝ 1 χ)
    (hχ : ∀ᶠ x in 𝓝ˢ (tsupport f), χ x = 1) (hbχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (hP : HasH1GradientOn (fun x => χ x * smoothPositivePart ε (f x))
      (gradient (fun x => χ x * smoothPositivePart ε (f x))) D) :
    ‖H1Space.ofFunction _ _ hP‖ ≤ 2 * ‖H1Space.ofFunction f (gradient f) hH‖ +
      (ε / 2) * ((volume D).toReal ^ (1 / 2 : ℝ) +
        lpNorm (gradient χ) 2 (volume.restrict D)) := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  have hp := hasH1GradientOn_smoothPositivePart_comp hD hvol hf hH hε
  have hF : lpNorm (fun x => χ x * smoothPositivePart ε (f x)) 2 (volume.restrict D) ≤
      lpNorm f 2 (volume.restrict D) + (ε / 2) * (volume D).toReal ^ (1 / 2 : ℝ) := by
    have hb := lpNorm_mono_real hp.memLp_function (f := fun x =>
      χ x * smoothPositivePart ε (f x)) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (hbχ x).1 (smoothPositivePart_nonneg hε _))]
      exact mul_le_of_le_one_left (smoothPositivePart_nonneg hε _) (hbχ x).2)
    apply hb.trans
    simpa only [Measure.real, Measure.restrict_apply_univ] using
      lpNorm_smoothPositivePart_comp_le hH.memLp_function hε
  have hG := lpNorm_gradient_cutoff_smoothPositivePart_le hD hvol hf hH hcχ hχ hε
  have hh := H1Space.norm_ofFunction_le _ _ hP
  have hu := (H1Space.ofFunction f (gradient f) hH).sum_norm_le
  change ‖hH.memLp_function.toLp f‖ + ‖hH.memLp_gradient.toLp (gradient f)‖ ≤ _ at hu
  rw [Lp.norm_toLp, Lp.norm_toLp, toReal_eLpNorm,
    toReal_eLpNorm] at hu
  nlinarith only [hF, hG, hh, hu]

/-- The defining H¹ closure supplies a genuine smooth interior approximating sequence. -/
lemma H1ZeroSpace.exists_smooth_interior_approximation {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (u : H1ZeroSpace hD) :
    ∃ f : ℕ → h1ZeroTestFunctions D,
      Tendsto (fun j => h1ZeroTestFunctions.toH1Space hD (f j)) atTop (𝓝 u.val) := by
  obtain ⟨w, hw, ht⟩ := mem_closure_iff_seq_limit.mp u.property
  choose f hf using hw
  refine ⟨f, ?_⟩
  simpa only [hf] using ht

/-- Nonnegative H¹₀ functions are weak H¹ limits of nonnegative smooth
compactly supported interior tests, with no trace-kernel premise. -/
theorem H1ZeroSpace.exists_nonneg_smooth_weak_approximation {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    (u : H1ZeroSpace hD) (hu : ∀ᵐ x ∂volume.restrict D, 0 ≤ u.val x) :
    ∃ f : ℕ → h1ZeroTestFunctions D,
      (∀ j x, 0 ≤ (f j).val x) ∧
      ∀ ℓ : H1Space D →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (h1ZeroTestFunctions.toH1Space hD (f j)))
          atTop (𝓝 (ℓ u.val)) := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  obtain ⟨f, hconv⟩ := exists_smooth_interior_approximation hD u
  let w (j : ℕ) := h1ZeroTestFunctions.toH1Space hD (f j)
  change Tendsto w atTop (𝓝 u.val) at hconv
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto w hconv).exists_norm_le
  have hwC (j : ℕ) : ‖w j‖ ≤ C := hC _ (mem_range_self j)
  have hcut (j : ℕ) := exists_smooth_cutoff_one_near_compact
    (f j).property.2.1 hD (f j).property.2.2
  choose χ hcχ hkχ hsχ hχ hbχ using hcut
  let L (j : ℕ) := lpNorm (gradient (χ j)) 2 (volume.restrict D)
  have hL (j : ℕ) : 0 ≤ L j := lpNorm_nonneg
  let δ (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  let ε (j : ℕ) : ℝ := δ j / (1 + L j)
  have hδpos (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδle (j : ℕ) : δ j ≤ 1 := by
    dsimp [δ]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hεpos (j : ℕ) : 0 < ε j := div_pos (hδpos j) (by linarith [hL j])
  have hεle (j : ℕ) : ε j ≤ δ j := by
    apply (div_le_iff₀ (by linarith [hL j] : 0 < 1 + L j)).mpr
    nlinarith [hδpos j, hL j]
  have hεL (j : ℕ) : ε j * L j ≤ 1 := by
    have he : ε j * (1 + L j) = δ j := by
      dsimp [ε]
      exact div_mul_cancel₀ _ (by linarith [hL j] : 1 + L j ≠ 0)
    have hb : ε j * L j ≤ δ j := by nlinarith [hεpos j]
    exact hb.trans (hδle j)
  have hε : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero (fun j => (hεpos j).le) hεle tendsto_one_div_add_atTop_nhds_zero_nat
  let q (j : ℕ) : h1ZeroTestFunctions D :=
    ⟨fun x => χ j x * smoothPositivePart (ε j) ((f j).val x),
      (hcχ j).mul ((contDiff_smoothPositivePart (hεpos j)).comp (f j).property.1),
      (hkχ j).mul_right, tsupport_mul_subset_left.trans (hsχ j)⟩
  have hqnonneg (j : ℕ) (x) : 0 ≤ (q j).val x :=
    mul_nonneg (hbχ j x).1 (smoothPositivePart_nonneg (hεpos j) _)
  let z (j : ℕ) := h1ZeroTestFunctions.toH1Space hD (q j)
  have hzB (j) : ‖z j‖ ≤ 2 * C +
      ((volume D).toReal ^ (1 / 2 : ℝ) + 1) / 2 := by
    have hh := norm_h1_cutoff_smoothPositivePart_le hD hvol
      ((f j).property.1.of_le (by simp)) (h1ZeroTestFunctions.hasH1GradientOn (f j) hD)
      ((hcχ j).of_le (by simp)) (hχ j) (hbχ j) (hεpos j)
      (h1ZeroTestFunctions.hasH1GradientOn (q j) hD)
    change ‖z j‖ ≤ 2 * ‖w j‖ + (ε j / 2) *
      ((volume D).toReal ^ (1 / 2 : ℝ) + L j) at hh
    have he1 : ε j * (volume D).toReal ^ (1 / 2 : ℝ) ≤
        (volume D).toReal ^ (1 / 2 : ℝ) :=
      mul_le_of_le_one_left (by positivity) ((hεle j).trans (hδle j))
    have he2 := hεL j
    have hw := hwC j
    nlinarith only [hh, he1, he2, hw]
  obtain ⟨v, σ, hσ, _, hweak, hweakf, _⟩ :=
    exists_subseq_weakly_tendsto_h1_components z hzB
  have hfH (j) := h1ZeroTestFunctions.hasH1GradientOn (f j) hD
  have hqH (j) := h1ZeroTestFunctions.hasH1GradientOn (q j) hD
  have hfstrong : Tendsto (fun j => lpNorm
      ((f j).val - (u.val : EuclideanSpace ℝ (Fin n) → ℝ)) 2 (volume.restrict D))
      atTop (𝓝 0) := by
    apply tendsto_lpNorm_sub_of_toLp_tendsto (fun j => (hfH j).memLp_function)
      (Lp.memLp u.val.toLp)
    rw [Lp.toLp_coeFn]
    exact (H1Space.toLpCLM.continuous.tendsto u.val).comp hconv
  have hum : MemLp (fun x => max (u.val x) 0) 2 (volume.restrict D) :=
    memLp_real_positivePart (Lp.memLp u.val.toLp)
  let p (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :=
    smoothPositivePart (ε j) ((f j).val x)
  have hpH (j) := hasH1GradientOn_smoothPositivePart_comp hD hvol
    ((f j).property.1.of_le (by simp)) (hfH j) (hεpos j)
  have hpstrong : Tendsto (fun j => lpNorm
      (p j - fun x => max (u.val x) 0) 2 (volume.restrict D)) atTop (𝓝 0) :=
    tendsto_lpNorm_smoothPositivePart_sub_max (fun j => (hfH j).memLp_function)
      (Lp.memLp u.val.toLp) hfstrong hε hεpos
  have herr : Tendsto (fun j => lpNorm ((q j).val - p j) 2 (volume.restrict D))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => lpNorm_nonneg) (fun j =>
      lpNorm_cutoff_smoothPositivePart_sub_le hvol (hχ j) (hbχ j) (hεpos j))
    simpa using (hε.div_const 2).mul_const ((volume D).toReal ^ (1 / 2 : ℝ))
  have hqstrong : Tendsto (fun j => lpNorm
      ((q j).val - fun x => max (u.val x) 0) 2 (volume.restrict D)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => lpNorm_nonneg) (fun j =>
      lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hqH j).memLp_function
        (hpH j).memLp_function (by norm_num))
    simpa using herr.add hpstrong
  have hstrong := toLp_tendsto_of_lpNorm_sub (fun j => (hqH j).memLp_function) hum hqstrong
  have hveq : hum.toLp (fun x => max (u.val x) 0) = v.toLp := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro ℓ
    exact tendsto_nhds_unique
      ((ℓ.continuous.tendsto _).comp (hstrong.comp hσ.tendsto_atTop)) (hweakf ℓ)
  have hvu : v = u.val := by
    apply H1Space.ext_ae hD
    have he := (Lp.ext_iff.mp hveq).symm.trans hum.coeFn_toLp
    filter_upwards [he, hu] with x hx hxpos
    exact hx.trans (max_eq_left hxpos)
  refine ⟨fun j => q (σ j), fun j => hqnonneg (σ j), ?_⟩
  simpa only [hvu] using hweak

/-- A continuous H¹ functional that is nonpositive on nonnegative smooth
interior tests is nonpositive on every nonnegative H¹₀ class. -/
theorem H1ZeroSpace.le_zero_of_nonnegative_smooth_tests {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    (ℓ : H1Space D →L[ℝ] ℝ)
    (hℓ : ∀ f : h1ZeroTestFunctions D, (∀ x, 0 ≤ f.val x) →
      ℓ (h1ZeroTestFunctions.toH1Space hD f) ≤ 0)
    (u : H1ZeroSpace hD) (hu : ∀ᵐ x ∂volume.restrict D, 0 ≤ u.val x) : ℓ u.val ≤ 0 := by
  obtain ⟨f, hf, ht⟩ := exists_nonneg_smooth_weak_approximation hD hvol u hu
  exact le_of_tendsto (ht ℓ) (Eventually.of_forall fun j => hℓ (f j) (hf j))

/-- The genuine distributional subharmonic inequality extends to nonnegative
H¹₀ tests by the proved nonnegative smooth approximation. -/
theorem H1ZeroSpace.inner_gradient_le_zero_of_smooth_tests {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    (u : H1Space D)
    (hu : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ D →
      (∀ x, 0 ≤ φ x) → (∫ x in D, inner ℝ (u.gradientLp x) (gradient φ x)) ≤ 0)
    (v : H1ZeroSpace hD) (hv : ∀ᵐ x ∂volume.restrict D, 0 ≤ v.val x) :
    inner ℝ u.gradientLp v.val.gradientLp ≤ 0 := by
  apply le_zero_of_nonnegative_smooth_tests hD hvol
    ((innerSL ℝ u.gradientLp).comp H1Space.gradientCLM) ?_ v hv
  intro φ hφ
  change inner ℝ u.gradientLp (h1ZeroTestFunctions.toH1Space hD φ).gradientLp ≤ 0
  rw [L2.inner_def]
  have he : (∫ x in D, inner ℝ (u.gradientLp x)
      ((h1ZeroTestFunctions.toH1Space hD φ).gradientLp x)) =
      ∫ x in D, inner ℝ (u.gradientLp x) (gradient φ.val x) := by
    apply integral_congr_ae
    filter_upwards [H1Space.gradientLp_ofFunction φ.val (gradient φ.val)
      (h1ZeroTestFunctions.hasH1GradientOn φ hD)] with x hx
    exact congrArg (fun z => inner ℝ (u.gradientLp x) z) hx
  rw [he]
  exact hu φ.val φ.property.1 φ.property.2.1 φ.property.2.2 hφ

end LiquidDrop
