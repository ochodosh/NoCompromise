import NoCompromise.Variation.StraightDiffeo
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Interpolation of inverse straight perturbations

The inverse of the affine interpolation of two globally Lipschitz C¹ fields is
jointly C¹ wherever the perturbation is small. On the unit parameter interval,
a bound on the field difference on an open neighborhood gives the sharp
parameter - speed bound used in BV stability. The final fundamental - theorem - of-
calculus estimate is local along the actual inverse trajectories.
-/

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology NNReal
namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine interpolation from `Y` to `X`. -/
def interpolatedField (X Y : E → E) (s : ℝ) (x : E) : E :=
  (1 - s) • Y x + s • X x

@[simp] lemma interpolatedField_zero (X Y : E → E) : interpolatedField X Y 0 = Y := by
  ext x
  simp [interpolatedField]
@[simp] lemma interpolatedField_one (X Y : E → E) : interpolatedField X Y 1 = X := by
  ext x
  simp [interpolatedField]

lemma lipschitzWith_interpolatedField {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y) (s : ℝ) :
    LipschitzWith ((‖1 - s‖₊ + ‖s‖₊) * L) (interpolatedField X Y s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have he : interpolatedField X Y s x - interpolatedField X Y s y =
      (1 - s) • (Y x - Y y) + s • (X x - X y) := by
    simp only [interpolatedField, smul_sub]; abel
  rw [he]
  calc
    _ ≤ ‖(1 - s) • (Y x - Y y)‖ + ‖s • (X x - X y)‖ := norm_add_le _ _
    _ ≤ |1 - s| * (L * ‖x - y‖) + |s| * (L * ‖x - y‖) := by
      simp only [norm_smul, Real.norm_eq_abs]
      gcongr
      · exact hY.norm_sub_le x y
      · exact hX.norm_sub_le x y
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_add, coe_nnnorm, Real.norm_eq_abs]; ring

lemma lipschitzWith_interpolatedField_Icc {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y) {s : ℝ} (hs : s ∈ Icc 0 1) :
    LipschitzWith L (interpolatedField X Y s) := by
  have he : ‖1 - s‖₊ + ‖s‖₊ = (1 : ℝ≥0) := by
    apply NNReal.eq
    simp only [NNReal.coe_add, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one,
      abs_of_nonneg hs.1, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    ring
  simpa only [he, one_mul] using lipschitzWith_interpolatedField hX hY s

/-- Total inverse choice, equal to the unique inverse on the small-derivative range. -/
def interpolatedInverse (X Y : E → E) (t s : ℝ) : E → E :=
  invFun (straightPerturbation (interpolatedField X Y s) t)

variable [CompleteSpace E] [Nontrivial E]

lemma interpolatedInverse_eq_homeomorph {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y) {t s : ℝ}
    (ht : |t| * L < 1) (hs : s ∈ Icc 0 1) :
    interpolatedInverse X Y t s =
      (straightPerturbationHomeomorph (lipschitzWith_interpolatedField_Icc hX hY hs) ht).symm := by
  apply invFun_eq_of_injective_of_rightInverse
  · exact (straightPerturbation_bijective
      (lipschitzWith_interpolatedField_Icc hX hY hs) ht).1
  · exact (straightPerturbationHomeomorph
      (lipschitzWith_interpolatedField_Icc hX hY hs) ht).apply_symm_apply

lemma eventually_bijective_interpolatedField {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y) {t s : ℝ}
    (ht : |t| * ((|1 - s| + |s|) * L) < 1) :
    ∀ᶠ q in 𝓝 s, Bijective (straightPerturbation (interpolatedField X Y q) t) := by
  have hc : Continuous (fun q : ℝ => |t| * ((|1 - q| + |q|) * L)) := by fun_prop
  filter_upwards [hc.continuousAt.eventually_lt_const ht] with q hq
  exact straightPerturbation_bijective (lipschitzWith_interpolatedField hX hY q)
    (by simpa using hq)

/-- A parameterwise bijective implicit equation has a continuously differentiable inverse branch. -/
lemma contDiffAt_implicit_of_eventually_bijective
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {F : P × E → E} {p : P} {q : E}
    (hF : ContDiffAt ℝ 1 F (p, q))
    (hi : (fderiv ℝ F (p, q) ∘L ContinuousLinearMap.inr ℝ P E).IsInvertible)
    (hb : ∀ᶠ a in 𝓝 p, Bijective (fun x => F (a, x))) :
    ContDiffAt ℝ 1 (fun a => invFun (fun x => F (a, x)) (F (p, q))) p := by
  let ψ := hF.implicitFunction (by norm_num) hi
  have he : (fun a => invFun (fun x => F (a, x)) (F (p, q))) =ᶠ[𝓝 p] ψ := by
    filter_upwards [hb, hF.eventually_apply_implicitFunction (by norm_num) hi] with a ha hψ
    apply ha.1
    exact (rightInverse_invFun ha.2 _).trans hψ.symm
  exact (hF.contDiffAt_implicitFunction (by norm_num) hi).congr_of_eventuallyEq he

omit [Nontrivial E] in
lemma contDiffAt_of_implicit_eq
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {F : P × E → E} {g : P → E} {p : P}
    (hF : ContDiffAt ℝ 1 F (p, g p))
    (hi : (fderiv ℝ F (p, g p) ∘L ContinuousLinearMap.inr ℝ P E).IsInvertible)
    (hb : ∀ᶠ a in 𝓝 p, Injective (fun x => F (a, x)))
    (he : ∀ᶠ a in 𝓝 p, F (a, g a) = F (p, g p)) :
    ContDiffAt ℝ 1 g p := by
  have hge : g =ᶠ[𝓝 p] hF.implicitFunction (by norm_num) hi := by
    filter_upwards [hb, he, hF.eventually_apply_implicitFunction (by norm_num) hi]
      with a ha hea hψ
    exact ha (hea.trans hψ.symm)
  exact (hF.contDiffAt_implicitFunction (by norm_num) hi).congr_of_eventuallyEq hge

omit [CompleteSpace E] [Nontrivial E] in
lemma contDiff_interpolatedField {X Y : E → E}
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) :
    ContDiff ℝ 1 (fun p : ℝ × E => interpolatedField X Y p.1 p.2) := by
  unfold interpolatedField
  exact ((contDiff_const.sub contDiff_fst).smul (hY.comp contDiff_snd)).add
    (contDiff_fst.smul (hX.comp contDiff_snd))

lemma contDiffAt_interpolatedInverse {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t s : ℝ} {z : E}
    (ht : |t| * ((|1 - s| + |s|) * L) < 1) :
    ContDiffAt ℝ 1 (fun p : ℝ × E => interpolatedInverse X Y t p.1 p.2) (s, z) := by
  let g : ℝ × E → E := fun p => interpolatedInverse X Y t p.1 p.2
  let F : (ℝ × E) × E → E := fun p =>
    straightPerturbation (interpolatedField X Y p.1.1) t p.2 - p.1.2
  have hF : ContDiff ℝ 1 F := by
    dsimp [F, straightPerturbation]
    exact (contDiff_snd.add
      (((contDiff_interpolatedField hXC hYC).comp
        (contDiff_fst.fst.prodMk contDiff_snd)).const_smul t)).sub contDiff_fst.snd
  have hb : ∀ᶠ a : ℝ × E in 𝓝 (s, z),
      Bijective (straightPerturbation (interpolatedField X Y a.1) t) :=
    continuous_fst.continuousAt.tendsto.eventually
      (eventually_bijective_interpolatedField hX hY ht)
  have hsol : ∀ᶠ a in 𝓝 (s, z), F (a, g a) = 0 := by
    filter_upwards [hb] with a ha
    exact sub_eq_zero.mpr (rightInverse_invFun ha.2 a.2)
  have hs0 : F ((s, z), g (s, z)) = 0 := hsol.self_of_nhds
  apply contDiffAt_of_implicit_eq hF.contDiffAt ?_ ?_ ?_
  · let A : E →L[ℝ] E := ContinuousLinearMap.id ℝ E +
      t • fderiv ℝ (interpolatedField X Y s) (g (s, z))
    have hc : ContDiff ℝ 1 (interpolatedField X Y s) :=
      (hYC.const_smul (1 - s)).add (hXC.const_smul s)
    have hd : HasFDerivAt (fun x => F ((s, z), x)) A (g (s, z)) := by
      exact (hasFDerivAt_straightPerturbation
        ((hc.differentiable (by norm_num) (g (s, z))).hasFDerivAt) t).sub_const z
    have he : fderiv ℝ F ((s, z), g (s, z)) ∘L ContinuousLinearMap.inr ℝ (ℝ × E) E = A := by
      have hd' := (hF.differentiable (by norm_num) ((s, z), g (s, z))).hasFDerivAt
      exact (hd'.comp (g (s, z))
        ((hasFDerivAt_const (s, z) (g (s, z))).prodMk (hasFDerivAt_id _))).unique hd
    rw [he]
    have ht' : |t| * ↑((‖1 - s‖₊ + ‖s‖₊) * L) < 1 := by simpa using ht
    exact ⟨straightPerturbationDerivativeEquiv (lipschitzWith_interpolatedField hX hY s)
      ht' (g (s, z)), coe_straightPerturbationDerivativeEquiv _ _ _⟩
  · filter_upwards [hb] with a ha x y hxy
    exact ha.1 (sub_left_inj.mp hxy)
  · change ∀ᶠ a in 𝓝 (s, z), F (a, g a) = F ((s, z), g (s, z))
    simpa only [hs0] using hsol

lemma contDiffAt_interpolatedInverse_Icc {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t s : ℝ} {z : E}
    (ht : |t| * L < 1) (hs : s ∈ Icc 0 1) :
    ContDiffAt ℝ 1 (fun p : ℝ × E => interpolatedInverse X Y t p.1 p.2) (s, z) := by
  apply contDiffAt_interpolatedInverse hX hY hXC hYC
  simpa only [abs_of_nonneg hs.1, abs_of_nonneg (sub_nonneg.mpr hs.2),
    sub_add_cancel, one_mul] using ht

lemma norm_interpolatedInverse_sub_le {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y) {t s v : ℝ} (z : E)
    (ht : |t| * L < 1 / 2) (hs : s ∈ Icc 0 1)
    (hv : Bijective (straightPerturbation (interpolatedField X Y v) t)) :
    ‖interpolatedInverse X Y t v z - interpolatedInverse X Y t s z‖ ≤
      2 * |t| * |v - s| * ‖X (interpolatedInverse X Y t v z) -
        Y (interpolatedInverse X Y t v z)‖ := by
  let q := interpolatedInverse X Y t
  have ht1 : |t| * L < 1 := lt_trans ht (by norm_num)
  have hs0 : straightPerturbation (interpolatedField X Y s) t (q s z) = z :=
    rightInverse_invFun (straightPerturbation_bijective
      (lipschitzWith_interpolatedField_Icc hX hY hs) ht1).2 z
  have hv0 : straightPerturbation (interpolatedField X Y v) t (q v z) = z :=
    rightInverse_invFun hv.2 z
  have he : straightPerturbation (interpolatedField X Y s) t (q v z) -
      straightPerturbation (interpolatedField X Y s) t (q s z) =
      (t * (s - v)) • (X (q v z) - Y (q v z)) := by
    calc
      _ = straightPerturbation (interpolatedField X Y s) t (q v z) - z := by rw [hs0]
      _ = straightPerturbation (interpolatedField X Y s) t (q v z) -
          straightPerturbation (interpolatedField X Y v) t (q v z) :=
        congrArg (straightPerturbation (interpolatedField X Y s) t (q v z) - ·) hv0.symm
      _ = _ := by simp only [straightPerturbation, interpolatedField]; module
  have hn := norm_sub_straightPerturbation_ge
    (lipschitzWith_interpolatedField_Icc hX hY hs) t (q v z) (q s z)
  rw [he, norm_smul, Real.norm_eq_abs, abs_mul, abs_sub_comm s v] at hn
  have hnon := norm_nonneg (q v z - q s z)
  change ‖q v z - q s z‖ ≤ _
  nlinarith

lemma norm_deriv_interpolatedInverse_le {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t s : ℝ} (z : E)
    (ht : |t| * L < 1 / 2) (hs : s ∈ Icc 0 1)
    {V : Set E} (hV : IsOpen V) (hq : interpolatedInverse X Y t s z ∈ V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M) :
    ‖deriv (fun a => interpolatedInverse X Y t a z) s‖ ≤ 2 * |t| * M := by
  have ht1 : |t| * L < 1 := lt_trans ht (by norm_num)
  have hc := (contDiffAt_interpolatedInverse_Icc hX hY hXC hYC ht1 hs (z := z)).comp s
    (contDiffAt_id.prodMk contDiffAt_const)
  have hqv : ∀ᶠ a in 𝓝 s, interpolatedInverse X Y t a z ∈ V :=
    hc.continuousAt.eventually (hV.mem_nhds hq)
  have ht' : |t| * ((|1 - s| + |s|) * L) < 1 := by
    simpa only [abs_of_nonneg hs.1, abs_of_nonneg (sub_nonneg.mpr hs.2),
      sub_add_cancel, one_mul] using ht1
  apply norm_deriv_le_of_lip' (by positivity)
  filter_upwards [hqv, eventually_bijective_interpolatedField hX hY ht'] with a ha hb
  calc
    _ ≤ 2 * |t| * |a - s| * ‖X (interpolatedInverse X Y t a z)-
        Y (interpolatedInverse X Y t a z)‖ := norm_interpolatedInverse_sub_le hX hY z ht hs hb
    _ ≤ 2 * |t| * |a - s| * M := mul_le_mul_of_nonneg_left (hbound _ ha) (by positivity)
    _ = _ := by rw [Real.norm_eq_abs]; ring

lemma contDiffOn_interpolatedInverse_Icc {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1) :
    ContDiffOn ℝ 1 (fun p : ℝ × E => interpolatedInverse X Y t p.1 p.2)
      (Icc 0 1 ×ˢ univ) := by
  intro p hp
  exact (contDiffAt_interpolatedInverse_Icc hX hY hXC hYC ht hp.1).contDiffWithinAt

lemma enorm_comp_interpolatedInverse_sub_le {X Y : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ} (z : E)
    (ht : |t| * L < 1 / 2) {V : Set E} (hV : IsOpen V)
    {u : E → ℝ} (hu : ContDiffOn ℝ 1 u V)
    (hpath : ∀ s ∈ Icc 0 1, interpolatedInverse X Y t s z ∈ V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M) :
    ‖u (interpolatedInverse X Y t 1 z) - u (interpolatedInverse X Y t 0 z)‖ₑ ≤
      ENNReal.ofReal (2 * |t| * M) *
        ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal ‖fderiv ℝ u (interpolatedInverse X Y t s z)‖ := by
  have ht1 : |t| * L < 1 := lt_trans ht (by norm_num)
  let q := fun s => interpolatedInverse X Y t s z
  have hq (s : ℝ) (hs : s ∈ Icc 0 1) : ContDiffAt ℝ 1 q s :=
    (contDiffAt_interpolatedInverse_Icc hX hY hXC hYC ht1 hs).comp s
      (contDiffAt_id.prodMk contDiffAt_const)
  have huq (s : ℝ) (hs : s ∈ Icc 0 1) : ContDiffAt ℝ 1 (u ∘ q) s :=
    (hu.contDiffAt (hV.mem_nhds (hpath s hs))).comp s (hq s hs)
  have hbd (s : ℝ) (hs : s ∈ Icc 0 1) :
      ‖deriv (u ∘ q) s‖ ≤ (2 * |t| * M) * ‖fderiv ℝ u (q s)‖ := by
    have hd := (hu.contDiffAt (hV.mem_nhds (hpath s hs))).differentiableAt one_ne_zero
    rw [(hd.hasFDerivAt.comp_hasDerivAt s
      ((hq s hs).differentiableAt one_ne_zero).hasDerivAt).deriv]
    calc
      _ ≤ ‖fderiv ℝ u (q s)‖ * ‖deriv q s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ u (q s)‖ * (2 * |t| * M) := mul_le_mul_of_nonneg_left
        (norm_deriv_interpolatedInverse_le hX hY hXC hYC z ht hs hV (hpath s hs) hM hbound)
        (norm_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ ≤ ∫⁻ s in Icc (0 : ℝ) 1, ‖deriv (u ∘ q) s‖ₑ :=
      enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
        (fun s hs => (huq s hs).contDiffWithinAt) zero_le_one
    _ ≤ ∫⁻ s in Icc (0 : ℝ) 1,
        ENNReal.ofReal (2 * |t| * M) * ENNReal.ofReal ‖fderiv ℝ u (q s)‖ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      simpa only [← ofReal_norm, ← ENNReal.ofReal_mul (show 0 ≤ 2 * |t| * M by positivity)]
        using ENNReal.ofReal_le_ofReal (hbd s hs)
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end LiquidDrop
