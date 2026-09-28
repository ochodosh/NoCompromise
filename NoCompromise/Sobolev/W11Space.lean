import NoCompromise.Sobolev.W11Algebra

/-!
# The normed space of W¹,¹ classes

Elements are actual weak-gradient pairs of scalar and vector L¹ classes. The
norm is the maximum of their two L¹ norms, equivalent to their sum with factors
one and two. On open domains the scalar class determines the gradient uniquely.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

abbrev W11Ambient {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :=
  Lp ℝ 1 (volume.restrict U) × Lp (EuclideanSpace ℝ (Fin n)) 1 (volume.restrict U)

def w11Submodule {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (W11Ambient U) where
  carrier := {p | HasW11GradientOn p.1 p.2 U}
  zero_mem' := (HasW11GradientOn.zero U).congr_ae
    (Lp.coeFn_zero ℝ 1 (volume.restrict U)).symm
    (Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 1 (volume.restrict U)).symm
  add_mem' hp hq := (hp.add hq).congr_ae (Lp.coeFn_add _ _).symm (Lp.coeFn_add _ _).symm
  smul_mem' c _ hp := (hp.const_mul c).congr_ae
    (Lp.coeFn_smul c _).symm (Lp.coeFn_smul c _).symm

abbrev W11Space {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) := ↥(w11Submodule U)

namespace W11Space
variable {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

def toLp (u : W11Space U) : Lp ℝ 1 (volume.restrict U) := u.val.1

def gradientLp (u : W11Space U) : Lp (EuclideanSpace ℝ (Fin n)) 1 (volume.restrict U) := u.val.2

instance : CoeFun (W11Space U) (fun _ => EuclideanSpace ℝ (Fin n) → ℝ) := ⟨fun u => u.toLp⟩

lemma hasW11GradientOn (u : W11Space U) : HasW11GradientOn u u.gradientLp U := u.property

lemma norm_eq (u : W11Space U) : ‖u‖ = max ‖u.toLp‖ ‖u.gradientLp‖ := rfl

lemma norm_toLp_eq_lpNorm (u : W11Space U) : ‖u.toLp‖ = lpNorm u 1 (volume.restrict U) := by
  rw [Lp.norm_def, toReal_eLpNorm]

lemma norm_gradientLp_eq_lpNorm (u : W11Space U) :
    ‖u.gradientLp‖ = lpNorm u.gradientLp 1 (volume.restrict U) := by
  rw [Lp.norm_def, toReal_eLpNorm]

lemma norm_toLp_le (u : W11Space U) : ‖u.toLp‖ ≤ ‖u‖ := le_max_left _ _

lemma norm_gradientLp_le (u : W11Space U) : ‖u.gradientLp‖ ≤ ‖u‖ := le_max_right _ _

lemma norm_le_sum (u : W11Space U) : ‖u‖ ≤ ‖u.toLp‖ + ‖u.gradientLp‖ := by
  rw [norm_eq]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

lemma sum_norm_le (u : W11Space U) : ‖u.toLp‖ + ‖u.gradientLp‖ ≤ 2 * ‖u‖ := by
  linarith [u.norm_toLp_le, u.norm_gradientLp_le]

def ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasW11GradientOn f G U) : W11Space U :=
  ⟨(hf.memLp_function.toLp f, hf.memLp_gradient.toLp G), hf.congr_ae
    (MemLp.coeFn_toLp hf.memLp_function).symm (MemLp.coeFn_toLp hf.memLp_gradient).symm⟩

lemma coeFn_ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasW11GradientOn f G U) :
    ⇑(ofFunction f G hf) =ᵐ[volume.restrict U] f := MemLp.coeFn_toLp hf.memLp_function

lemma gradientLp_ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasW11GradientOn f G U) :
    ⇑(ofFunction f G hf).gradientLp =ᵐ[volume.restrict U] G := MemLp.coeFn_toLp hf.memLp_gradient

lemma norm_ofFunction_le (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasW11GradientOn f G U) :
    ‖ofFunction f G hf‖ ≤ lpNorm f 1 (volume.restrict U) + lpNorm G 1 (volume.restrict U) := by
  have h := (ofFunction f G hf).norm_le_sum
  change ‖ofFunction f G hf‖ ≤ ‖hf.memLp_function.toLp f‖ + ‖hf.memLp_gradient.toLp G‖ at h
  simpa only [Lp.norm_toLp, toReal_eLpNorm,
    toReal_eLpNorm] using h

lemma ext_ae (hU : IsOpen U) {u v : W11Space U}
    (huv : u =ᵐ[volume.restrict U] v) : u = v := by
  have hG : ⇑u.gradientLp =ᵐ[volume.restrict U] v.gradientLp :=
    HasWeakGradientOn.unique hU
      (u.hasW11GradientOn.toHasWeakGradientOn.congr_ae huv Filter.EventuallyEq.rfl)
      v.hasW11GradientOn.toHasWeakGradientOn
  exact Subtype.ext (Prod.ext (Lp.ext huv) (Lp.ext hG))

lemma coeFn_add (u v : W11Space U) :
    ⇑(u + v) =ᵐ[volume.restrict U] fun x => u x + v x := Lp.coeFn_add u.toLp v.toLp

lemma coeFn_smul (c : ℝ) (u : W11Space U) :
    ⇑(c • u) =ᵐ[volume.restrict U] fun x => c * u x := Lp.coeFn_smul c u.toLp

lemma coeFn_sub (u v : W11Space U) :
    ⇑(u - v) =ᵐ[volume.restrict U] fun x => u x - v x := Lp.coeFn_sub u.toLp v.toLp

lemma norm_ofFunction_sub_le (hU : IsOpen U) {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) (hg : HasW11GradientOn g H U) :
    ‖ofFunction f G hf - ofFunction g H hg‖ ≤
      lpNorm (f - g) 1 (volume.restrict U) + lpNorm (G - H) 1 (volume.restrict U) := by
  have heq : ofFunction f G hf - ofFunction g H hg =
      ofFunction (f - g) (G - H) (hf.sub hg) := by
    apply ext_ae hU
    filter_upwards [coeFn_sub (ofFunction f G hf) (ofFunction g H hg),
      coeFn_ofFunction f G hf, coeFn_ofFunction g H hg,
      coeFn_ofFunction (f - g) (G - H) (hf.sub hg)] with x h1 h2 h3 h4
    rw [h2, h3] at h1
    exact h1.trans h4.symm
  rw [heq]
  exact norm_ofFunction_le _ _ _

end W11Space
end LiquidDrop
