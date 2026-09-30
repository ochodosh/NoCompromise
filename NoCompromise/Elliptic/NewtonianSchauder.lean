module

public import NoCompromise.Elliptic.NewtonianSchauderCutoff
public import NoCompromise.Elliptic.NewtonianSchauderHarmonic

@[expose] public section

/-!
# Interior Newtonian Schauder estimate

The solution is represented by the actual cutoff Newtonian potential plus a
smooth representative of its distributionally harmonic remainder. The C²,α norm
is `schauderC2HolderNorm`, the sum of the Hölder norms of orders zero, one and two.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

lemma schauder_holder_quotient_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f x - f y‖ / ‖x - y‖ ^ α ≤ holderSeminorm α f U :=
  le_csSup hf.seminorm_bounded
    (mem_insert_of_mem 0 (mem_image_of_mem _ (show (x, y) ∈ U ×ˢ U from ⟨hx, hy⟩)))

lemma schauder_holder_mono {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f : E → F} {U V : Set E} (hf : HasFiniteHolderNormOn α f V) (hUV : U ⊆ V) :
    HasFiniteHolderNormOn α f U ∧ holderNorm α f U ≤ holderNorm α f V := by
  have hA := holderUniformNorm_nonneg hf.uniform_bounded
  have hB := hf.seminorm_nonneg
  have hv : ∀ x ∈ U, ‖f x‖ ≤ holderUniformNorm f V :=
    fun x hx => norm_le_holderUniformNorm hf.uniform_bounded (hUV hx)
  have hh : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ / ‖x - y‖ ^ α ≤ holderSeminorm α f V :=
    fun x hx y hy => schauder_holder_quotient_le hf (hUV hx) (hUV hy)
  exact ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hh, holderNorm_le hA hB hv hh⟩

lemma schauder_holder_add {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f g : E → F} {U : Set E}
    (hf : HasFiniteHolderNormOn α f U) (hg : HasFiniteHolderNormOn α g U) :
    HasFiniteHolderNormOn α (fun x => f x + g x) U ∧
      holderNorm α (fun x => f x + g x) U ≤ holderNorm α f U + holderNorm α g U := by
  have hA := add_nonneg (holderUniformNorm_nonneg hf.uniform_bounded)
    (holderUniformNorm_nonneg hg.uniform_bounded)
  have hB := add_nonneg hf.seminorm_nonneg hg.seminorm_nonneg
  have hv : ∀ x ∈ U, ‖f x + g x‖ ≤ holderUniformNorm f U + holderUniformNorm g U :=
    fun x hx => (norm_add_le _ _).trans (add_le_add
      (norm_le_holderUniformNorm hf.uniform_bounded hx)
      (norm_le_holderUniformNorm hg.uniform_bounded hx))
  have hh : ∀ x ∈ U, ∀ y ∈ U, ‖(f x + g x) - (f y + g y)‖ / ‖x - y‖ ^ α ≤
      holderSeminorm α f U + holderSeminorm α g U := by
    intro x hx y hy
    have he : (f x + g x) - (f y + g y) = (f x - f y) + (g x - g y) := by abel
    rw [he]
    calc
      _ ≤ (‖f x - f y‖ + ‖g x - g y‖) / ‖x - y‖ ^ α :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (by positivity)
      _ = ‖f x - f y‖ / ‖x - y‖ ^ α + ‖g x - g y‖ / ‖x - y‖ ^ α := add_div _ _ _
      _ ≤ _ := add_le_add (schauder_holder_quotient_le hf hx hy)
        (schauder_holder_quotient_le hg hx hy)
  refine ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hh, (holderNorm_le hA hB hv hh).trans_eq ?_⟩
  dsimp [holderNorm]
  ring

lemma schauderC2HolderNorm_function_bound {n : ℕ} {α : ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasC2HolderOn α u U) : ∀ x ∈ U, ‖u x‖ ≤ schauderC2HolderNorm α u U := by
  intro x hx
  apply ((norm_le_holderUniformNorm hu.function_holder.uniform_bounded hx).trans
    hu.function_holder.uniformNorm_le).trans
  dsimp [schauderC2HolderNorm]
  linarith [hu.derivative_holder.norm_nonneg, hu.hessian_holder.norm_nonneg]

lemma schauderC2HolderNorm_lpNorm_top_le {n : ℕ} {α : ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hu : HasC2HolderOn α u U) :
    lpNorm u ∞ (volume.restrict U) ≤ schauderC2HolderNorm α u U := by
  have hm := hu.memLp_top hU
  have hb : ∀ᵐ x ∂volume.restrict U, ‖u x‖ ≤ schauderC2HolderNorm α u U := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact schauderC2HolderNorm_function_bound hu x hx
  rw [← toReal_eLpNorm, eLpNorm_exponent_top hm.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hb)).trans_eq
    (ENNReal.toReal_ofReal (schauderC2HolderNorm_nonneg hu))

lemma schauder_lpNorm_top_mono {f : E₃ → ℝ} {U V : Set E₃}
    (hf : MemLp f ∞ (volume.restrict V)) (hUV : U ⊆ V) :
    MemLp f ∞ (volume.restrict U) ∧ lpNorm f ∞ (volume.restrict U) ≤
      lpNorm f ∞ (volume.restrict V) := by
  have hm := Measure.restrict_mono hUV (le_refl volume)
  have hfu := hf.mono_measure hm
  refine ⟨hfu, ?_⟩
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f hm)

lemma schauder_lpNorm_top_ae_eq {f g : E₃ → ℝ} {U : Set E₃}
    (hf : MemLp f ∞ (volume.restrict U)) (he : f =ᵐ[volume.restrict U] g) :
    MemLp g ∞ (volume.restrict U) ∧ lpNorm g ∞ (volume.restrict U) =
      lpNorm f ∞ (volume.restrict U) := by
  have hg := (memLp_congr_ae he).mp hf
  refine ⟨hg, ?_⟩
  rw [← toReal_eLpNorm, ← toReal_eLpNorm,
    eLpNorm_congr_ae he]

lemma schauder_fderiv_two_add {u v : E₃ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    fderiv ℝ (fderiv ℝ (fun x => u x + v x)) =
      fun x => fderiv ℝ (fderiv ℝ u) x + fderiv ℝ (fderiv ℝ v) x := by
  have he : fderiv ℝ (fun x => u x + v x) = fun x => fderiv ℝ u x + fderiv ℝ v x :=
    funext fun x => fderiv_add (hu.differentiable (by norm_num) x)
      (hv.differentiable (by norm_num) x)
  rw [he]
  funext x
  exact fderiv_add ((hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)

lemma hasDistributionalLaplacianOn_schauderPotential {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f) (hb : ∀ x, ‖f x‖ ≤ B) :
    HasDistributionalLaplacianOn (schauderPotential f) f univ := by
  have h := (hasDistributionalLaplacianOn_scalarNewtonianPotential hf hcf hb).const_mul
    (-(4 * Real.pi)⁻¹)
  have he : (fun x => -(4 * Real.pi)⁻¹ * (-(4 * Real.pi) * f x)) = f := by
    funext x
    field_simp
  rwa [he] at h

lemma hasDistributionalLaplacianOn_schauderCutoffPotential {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {f : E₃ → ℝ} (hf : HasFiniteHolderNormOn α f (ball 0 1)) :
    HasDistributionalLaplacianOn (schauderPotential (schauderCutoffSource f)) f
      (ball 0 (3 / 4)) := by
  obtain ⟨_, _, hb⟩ := exists_schauderCutoffSource_bound hα hα1
  obtain ⟨hc, hv, _⟩ := hb f hf
  apply ((hasDistributionalLaplacianOn_schauderPotential hc.aestronglyMeasurable
    (schauderCutoffSource_hasCompactSupport f) hv).mono (subset_univ _)).congr_ae EventuallyEq.rfl
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact schauderCutoffSource_eqOn f hx


/-- The finite-norm interior Schauder estimate for an actual distributional solution.
The representative is globally C², agrees with the solution almost everywhere on
B₁/₂, and its C²,α norm uses the actual first and second Fréchet derivatives. -/
theorem newtonian_schauder {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (z f : E₃ → ℝ),
      HasDistributionalLaplacianOn z f (ball 0 1) →
      MemLp z ∞ (volume.restrict (ball 0 1)) →
      HasFiniteHolderNormOn α f (ball 0 1) →
      ∃ w : E₃ → ℝ, ContDiff ℝ 2 w ∧
        w =ᵐ[volume.restrict (ball 0 (1 / 2))] z ∧
        HasC2HolderOn α w (ball 0 (1 / 2)) ∧
        schauderC2HolderNorm α w (ball 0 (1 / 2)) ≤
          C * (lpNorm z ∞ (volume.restrict (ball 0 1)) + holderNorm α f (ball 0 1)) := by
  obtain ⟨CP, hCP, hPot⟩ := exists_schauderCutoffPotential_bound hα hα1
  obtain ⟨CH, hCH, hHarm⟩ := exists_schauder_harmonic_hessian_bound hα hα1
  obtain ⟨CL, hCL, hLift⟩ := exists_schauderC2HolderNorm_le hα hα1
    (by norm_num : (0 : ℝ) < 1 / 2) (0 : E₃)
  refine ⟨CL * (1 + CH + (1 + CH) * CP), by positivity, ?_⟩
  intro z f hz hzm hf
  let P := schauderPotential (schauderCutoffSource f)
  let Z := lpNorm z ∞ (volume.restrict (ball (0 : E₃) 1))
  let F := holderNorm α f (ball (0 : E₃) 1)
  have hZ : 0 ≤ Z := lpNorm_nonneg
  have hF : 0 ≤ F := hf.norm_nonneg
  obtain ⟨hP, hPb⟩ := hPot f hf
  obtain ⟨CS, hCS, hSource⟩ := exists_schauderCutoffSource_bound hα hα1
  obtain ⟨hcS, hvS, hiS⟩ := hSource f hf
  have hPc : ContDiff ℝ 2 P := contDiff_two_schauderPotential hα hα1
    (mul_nonneg hCS.le hF) hF hcS.measurable (schauderCutoffSource_hasCompactSupport f)
    hvS hiS
  have hPd := hasDistributionalLaplacianOn_schauderCutoffPotential hα hα1 hf
  have hs₁ : ball (0 : E₃) (3 / 4) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have hs₂ : ball (0 : E₃) (2 / 3) ⊆ ball 0 (3 / 4) := ball_subset_ball (by norm_num)
  have hs₃ : ball (0 : E₃) (1 / 2) ⊆ ball 0 (2 / 3) := ball_subset_ball (by norm_num)
  let v := fun x => z x - P x
  have hvd : HasDistributionalLaplacianOn v (fun _ => 0) (ball 0 (3 / 4)) := by
    simpa only [sub_self] using (hz.mono hs₁).sub hPd
  obtain ⟨hzm₁, hzb₁⟩ := schauder_lpNorm_top_mono hzm hs₁
  have hPm := hP.memLp_top isOpen_ball
  have hvm : MemLp v ∞ (volume.restrict (ball 0 (3 / 4))) := hzm₁.sub hPm
  have hvb : lpNorm v ∞ (volume.restrict (ball 0 (3 / 4))) ≤ Z + CP * F := by
    apply (lpNorm_sub_le hzm₁ (by simp : (1 : ℝ≥0∞) ≤ ∞)).trans
    exact add_le_add hzb₁ ((schauderC2HolderNorm_lpNorm_top_le isOpen_ball hP).trans hPb)
  let : IsFiniteMeasure (volume.restrict (ball (0 : E₃) (3 / 4))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  obtain ⟨h, hhc, hhe, _⟩ := interior_harmonic_smooth (by norm_num : 3 < 4) (0 : E₃)
    (by norm_num : (2 / 3 : ℝ) < 3 / 4) hvd (hvm.mono_exponent le_top)
  obtain ⟨hvm₂, hvb₂⟩ := schauder_lpNorm_top_mono hvm hs₂
  obtain ⟨hhm, hhb⟩ := schauder_lpNorm_top_ae_eq hvm₂ hhe.symm
  have hhb' : lpNorm h ∞ (volume.restrict (ball 0 (2 / 3))) ≤ Z + CP * F :=
    hhb.le.trans (hvb₂.trans hvb)
  have hhd := (hvd.mono hs₂).congr_ae hhe.symm EventuallyEq.rfl
  obtain ⟨hH, hHb⟩ := hHarm h hhc hhd hhm
  have hHb' : holderNorm α (fderiv ℝ (fderiv ℝ h)) (ball 0 (1 / 2)) ≤
      CH * (Z + CP * F) := hHb.trans (mul_le_mul_of_nonneg_left hhb' hCH.le)
  let w := fun x => P x + h x
  have hhc₂ : ContDiff ℝ 2 h := hhc.of_le (by simp)
  have hwc : ContDiff ℝ 2 w := hPc.add hhc₂
  have hwe : w =ᵐ[volume.restrict (ball 0 (1 / 2))] z := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs₃ hhe] with x hx
    dsimp [w, v] at *
    rw [hx]
    ring
  obtain ⟨hzm₃, hzb₃⟩ := schauder_lpNorm_top_mono hzm (hs₃.trans (hs₂.trans hs₁))
  obtain ⟨hwm, hwb⟩ := schauder_lpNorm_top_ae_eq hzm₃ hwe.symm
  have hwb' : lpNorm w ∞ (volume.restrict (ball 0 (1 / 2))) ≤ Z := hwb.le.trans hzb₃
  obtain ⟨hPH, hPHb⟩ := schauder_holder_mono hP.hessian_holder (hs₃.trans hs₂)
  have hPHb' : holderNorm α (fderiv ℝ (fderiv ℝ P)) (ball 0 (1 / 2)) ≤ CP * F := by
    apply hPHb.trans (le_trans ?_ hPb)
    dsimp [schauderC2HolderNorm]
    linarith [hP.function_holder.norm_nonneg, hP.derivative_holder.norm_nonneg]
  obtain ⟨hwH, hwHb⟩ := schauder_holder_add hPH hH
  have heH := schauder_fderiv_two_add hPc hhc₂
  change fderiv ℝ (fderiv ℝ w) = _ at heH
  rw [← heH] at hwH hwHb
  have hwHb' : holderNorm α (fderiv ℝ (fderiv ℝ w)) (ball 0 (1 / 2)) ≤
      CP * F + CH * (Z + CP * F) := hwHb.trans (add_le_add hPHb' hHb')
  obtain ⟨hwHolder, hwNorm⟩ := hLift w hwc.contDiffOn hwm hwH
  refine ⟨w, hwc, hwe, hwHolder, hwNorm.trans ?_⟩
  calc
    _ ≤ CL * (Z + (CP * F + CH * (Z + CP * F))) :=
      mul_le_mul_of_nonneg_left (add_le_add hwb' hwHb') hCL.le
    _ = CL * ((1 + CH) * Z + ((1 + CH) * CP) * F) := by ring
    _ ≤ CL * ((1 + CH) * (Z + F) + ((1 + CH) * CP) * (Z + F)) := by
      apply mul_le_mul_of_nonneg_left _ hCL.le
      exact add_le_add (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hF) (by positivity))
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hZ) (by positivity))
    _ = _ := by dsimp [Z, F]; ring

end LiquidDrop
