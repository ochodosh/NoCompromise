module

public import NoCompromise.BV.Rellich
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

/-!
# The Hilbert space H¹

The weak-gradient graph is a closed linear subspace of the Hilbert product of
scalar and vector-valued L² spaces. Its defining continuous linear equations are
the coordinate integration-by-parts identities against compactly supported C¹ tests.
-/

noncomputable section

open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal Topology Gradient

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- The scalar and vector L² pair, with the Hilbert product norm. -/
abbrev H1Ambient {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :=
  WithLp 2 (Lp ℝ 2 (volume.restrict U) ×
    Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict U))

/-- A coordinate test for the weak-gradient equation. -/
structure H1TestFunction {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) where
  normal : Fin n
  toFun : EuclideanSpace ℝ (Fin n) → ℝ
  contDiff : ContDiff ℝ 1 toFun
  hasCompactSupport : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ U

namespace H1TestFunction

variable {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

lemma memLp_derivative (t : H1TestFunction U) :
    MemLp (fun x => fderiv ℝ t.toFun x (EuclideanSpace.single t.normal (1 : ℝ)))
      2 (volume.restrict U) :=
  ((t.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
    (t.hasCompactSupport.fderiv_apply ℝ _)

lemma memLp_vector (t : H1TestFunction U) :
    MemLp (fun x => t.toFun x • EuclideanSpace.single t.normal (1 : ℝ))
      2 (volume.restrict U) :=
  (t.contDiff.continuous.smul continuous_const).memLp_of_hasCompactSupport
    t.hasCompactSupport.smul_right

/-- Pair a test derivative with the corresponding test vector field. -/
def pair (t : H1TestFunction U) : H1Ambient U :=
  WithLp.toLp 2 (t.memLp_derivative.toLp _, t.memLp_vector.toLp _)

lemma inner_pair (t : H1TestFunction U) (u : H1Ambient U) :
    inner ℝ t.pair u =
      (∫ x in U, u.fst x * fderiv ℝ t.toFun x (EuclideanSpace.single t.normal (1 : ℝ))) +
        ∫ x in U, t.toFun x * u.snd x t.normal := by
  change (∫ x in U, inner ℝ (t.memLp_derivative.toLp _ x) (u.fst x)) +
      (∫ x in U, inner ℝ (t.memLp_vector.toLp _ x) (u.snd x)) = _
  congr 1
  · apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp t.memLp_derivative] with x hx
    rw [hx, Real.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp t.memLp_vector] with x hx
    rw [hx]
    simp [real_inner_smul_left, EuclideanSpace.inner_single_left]

end H1TestFunction

/-- The weak-gradient graph, expressed as an intersection of continuous linear kernels. -/
def h1Submodule {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (H1Ambient U) :=
  ⨅ t : H1TestFunction U, (innerSL ℝ t.pair).ker

lemma mem_h1Submodule_iff {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (u : H1Ambient U) : u ∈ h1Submodule U ↔ HasH1GradientOn u.fst u.snd U := by
  simp only [h1Submodule, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hu
    apply hasH1GradientOn_of_memLp_test (Lp.memLp u.fst) (Lp.memLp u.snd)
    intro i φ hφ hcφ hsφ
    let t : H1TestFunction U := ⟨i, φ, hφ, hcφ, hsφ⟩
    have ht := hu t
    change inner ℝ t.pair u = 0 at ht
    rw [t.inner_pair] at ht
    change (∫ x in U, u.fst x * fderiv ℝ φ x (EuclideanSpace.single i 1)) +
      (∫ x in U, φ x * u.snd x i) = 0 at ht
    linarith
  · intro hu t
    change inner ℝ t.pair u = 0
    rw [t.inner_pair]
    have ht := hu.test_eq t.normal t.toFun t.contDiff t.hasCompactSupport t.support_subset
    linarith

/-- Closedness uses only continuity of the L² test-pair functionals. -/
theorem isClosed_h1Submodule {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    IsClosed (h1Submodule U : Set (H1Ambient U)) := by
  rw [h1Submodule, Submodule.coe_iInf]
  exact isClosed_iInter fun t => (innerSL ℝ t.pair).isClosed_ker

/-- Null changes of either representative preserve the H¹ weak-gradient relation. -/
lemma HasH1GradientOn.congr_ae {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hfg : f =ᵐ[volume.restrict U] g)
    (hGH : G =ᵐ[volume.restrict U] H) : HasH1GradientOn g H U :=
  ⟨hf.toHasWeakGradientOn.congr_ae hfg hGH,
    hf.memLp_function.ae_eq hfg, hf.memLp_gradient.ae_eq hGH⟩

/-- Strong L² limits of a function and its weak gradient retain the weak-gradient relation. -/
theorem hasH1GradientOn_of_tendsto_Lp {n : ℕ} {α : Type*} {l : Filter α} [l.NeBot]
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : α → Lp ℝ 2 (volume.restrict U)}
    {G : α → Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict U)}
    {g : Lp ℝ 2 (volume.restrict U)}
    {H : Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict U)}
    (hf : ∀ a, HasH1GradientOn (f a) (G a) U)
    (htf : Tendsto f l (𝓝 g)) (htG : Tendsto G l (𝓝 H)) :
    HasH1GradientOn g H U := by
  have ht : Tendsto (fun a => WithLp.toLp 2 (f a, G a)) l
      (𝓝 (WithLp.toLp 2 (g, H))) :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp (htf.prodMk_nhds htG)
  apply (mem_h1Submodule_iff (WithLp.toLp 2 (g, H))).mp
  exact (isClosed_h1Submodule U).mem_of_tendsto ht
    (Eventually.of_forall fun a => (mem_h1Submodule_iff _).mpr (hf a))

/-- H¹ classes, including their unique weak L² gradients on open domains. -/
def H1Space {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) := ↥(h1Submodule U)

namespace H1Space

variable {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

instance : NormedAddCommGroup (H1Space U) :=
  inferInstanceAs (NormedAddCommGroup ↥(h1Submodule U))

instance : InnerProductSpace ℝ (H1Space U) :=
  inferInstanceAs (InnerProductSpace ℝ ↥(h1Submodule U))

instance : CompleteSpace (H1Space U) := (isClosed_h1Submodule U).completeSpace_coe

/-- Forget the weak-gradient equation and retain the L² pair. -/
def toAmbient (u : H1Space U) : H1Ambient U := u.val

/-- The scalar L² class of an H¹ element. -/
def toLp (u : H1Space U) : Lp ℝ 2 (volume.restrict U) := u.toAmbient.fst

/-- The vector-valued L² class of its weak gradient. -/
def gradientLp (u : H1Space U) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict U) := u.toAmbient.snd

instance : CoeFun (H1Space U) (fun _ => EuclideanSpace ℝ (Fin n) → ℝ) :=
  ⟨fun u => u.toLp⟩

lemma hasH1GradientOn (u : H1Space U) : HasH1GradientOn u u.gradientLp U :=
  (mem_h1Submodule_iff u.toAmbient).mp u.property

/-- The inherited Hilbert norm is exactly the square-sum H¹ norm. -/
lemma norm_sq (u : H1Space U) : ‖u‖ ^ 2 = ‖u.toLp‖ ^ 2 + ‖u.gradientLp‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.toAmbient

/-- The scalar projection norm equals the L² norm of its chosen representative. -/
lemma norm_toLp_eq_lpNorm (u : H1Space U) : ‖u.toLp‖ = lpNorm u 2 (volume.restrict U) := by
  rw [Lp.norm_def, toReal_eLpNorm]

/-- The gradient projection norm equals the L² norm of its chosen representative. -/
lemma norm_gradientLp_eq_lpNorm (u : H1Space U) :
    ‖u.gradientLp‖ = lpNorm u.gradientLp 2 (volume.restrict U) := by
  rw [Lp.norm_def, toReal_eLpNorm]

/-- The scalar projection is continuous and linear. -/
def toLpCLM : H1Space U →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
  (WithLp.fstL 2 ℝ _ _).comp (h1Submodule U).subtypeL

/-- The weak-gradient projection is continuous and linear. -/
def gradientCLM : H1Space U →L[ℝ] Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict U) :=
  (WithLp.sndL 2 ℝ _ _).comp (h1Submodule U).subtypeL

lemma norm_toLp_le (u : H1Space U) : ‖u.toLp‖ ≤ ‖u‖ :=
  WithLp.norm_fst_le _ u.toAmbient

lemma norm_gradientLp_le (u : H1Space U) : ‖u.gradientLp‖ ≤ ‖u‖ :=
  WithLp.norm_snd_le _ u.toAmbient

/-- The sum-of-component norms and the Hilbert norm are quantitatively equivalent. -/
lemma norm_le_sum (u : H1Space U) : ‖u‖ ≤ ‖u.toLp‖ + ‖u.gradientLp‖ := by
  nlinarith [u.norm_sq, norm_nonneg u, norm_nonneg u.toLp, norm_nonneg u.gradientLp,
    mul_nonneg (norm_nonneg u.toLp) (norm_nonneg u.gradientLp)]

lemma sum_norm_le (u : H1Space U) : ‖u.toLp‖ + ‖u.gradientLp‖ ≤ 2 * ‖u‖ := by
  linarith [u.norm_toLp_le, u.norm_gradientLp_le]

/-- Pass from an actual H¹ representative and weak gradient to their Hilbert-space class. -/
def ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G U) : H1Space U :=
  ⟨WithLp.toLp 2 (hf.memLp_function.toLp f, hf.memLp_gradient.toLp G),
    (mem_h1Submodule_iff _).mpr (hf.congr_ae
      (MemLp.coeFn_toLp hf.memLp_function).symm
      (MemLp.coeFn_toLp hf.memLp_gradient).symm)⟩

lemma coeFn_ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G U) :
    ⇑(ofFunction f G hf) =ᵐ[volume.restrict U] f :=
  MemLp.coeFn_toLp hf.memLp_function

lemma gradientLp_ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G U) :
    ⇑(ofFunction f G hf).gradientLp =ᵐ[volume.restrict U] G :=
  MemLp.coeFn_toLp hf.memLp_gradient

/-- The norm of a represented function is the usual H¹ square-sum norm. -/
lemma norm_ofFunction_sq (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G U) :
    ‖ofFunction f G hf‖ ^ 2 =
      (lpNorm f 2 (volume.restrict U)) ^ 2 + (lpNorm G 2 (volume.restrict U)) ^ 2 := by
  rw [norm_sq]
  change ‖hf.memLp_function.toLp f‖ ^ 2 + ‖hf.memLp_gradient.toLp G‖ ^ 2 = _
  rw [Lp.norm_toLp, Lp.norm_toLp,
    toReal_eLpNorm, toReal_eLpNorm]

/-- A bound for the sum of the two L² norms controls the Hilbert-space norm. -/
lemma norm_ofFunction_le (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G U) :
    ‖ofFunction f G hf‖ ≤ lpNorm f 2 (volume.restrict U) + lpNorm G 2 (volume.restrict U) := by
  have h := (ofFunction f G hf).norm_le_sum
  change ‖ofFunction f G hf‖ ≤ ‖hf.memLp_function.toLp f‖ + ‖hf.memLp_gradient.toLp G‖ at h
  simpa only [Lp.norm_toLp, toReal_eLpNorm,
    toReal_eLpNorm] using h

/-- On an open domain the scalar class uniquely determines the H¹ pair. -/
lemma ext_ae (hU : IsOpen U) {u v : H1Space U}
    (huv : u =ᵐ[volume.restrict U] v) : u = v := by
  have hG : ⇑u.gradientLp =ᵐ[volume.restrict U] v.gradientLp :=
    HasWeakGradientOn.unique hU
      (u.hasH1GradientOn.toHasWeakGradientOn.congr_ae huv Filter.EventuallyEq.rfl)
      v.hasH1GradientOn.toHasWeakGradientOn
  apply Subtype.ext
  apply WithLp.ofLp_injective
  exact Prod.ext (Lp.ext huv) (Lp.ext hG)

/-- Scalar projection is injective on open domains. -/
lemma toLp_injective (hU : IsOpen U) : Function.Injective (toLp (U := U)) := by
  intro u v huv
  apply ext_ae hU
  exact Lp.ext_iff.mp huv

end H1Space

end LiquidDrop
