module

public import NoCompromise.BV.Algebra
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

/-!
# The normed space of BV classes

BV functions are represented by their almost-everywhere classes in L¹ on the
specified region. The norm is the L¹ norm plus total variation. The construction
is defined for every region; its usual analytic interpretation uses an open region.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- The L¹ classes with finite variation form a real submodule. -/
def bvSubmodule {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (Lp ℝ 1 (volume.restrict U)) where
  carrier := {f | variation f U < ∞}
  zero_mem' := by
    change variation (0 : Lp ℝ 1 (volume.restrict U)) U < ∞
    rw [variation_congr_ae U (Lp.coeFn_zero ℝ 1 (volume.restrict U))]
    exact (IsBVOn.zero U).2
  add_mem' := by
    intro f g hf hg
    change variation (f + g) U < ∞
    rw [variation_congr_ae U (Lp.coeFn_add f g)]
    exact (variation_add_le
      (IntegrableOn.locallyIntegrableOn (memLp_one_iff_integrable.mp (Lp.memLp f)))
      (IntegrableOn.locallyIntegrableOn (memLp_one_iff_integrable.mp (Lp.memLp g)))).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hf, hg⟩)
  smul_mem' := by
    intro c f hf
    change variation (c • f) U < ∞
    rw [variation_congr_ae U (Lp.coeFn_smul c f)]
    change variation (fun x => c * f x) U < ∞
    rw [variation_const_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

/-- BV classes on `U`. The distinct type carries the BV norm, not the ambient L¹ norm. -/
def BVSpace {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) := ↥(bvSubmodule U)

namespace BVSpace

variable {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

instance : AddCommGroup (BVSpace U) := inferInstanceAs (AddCommGroup ↥(bvSubmodule U))
instance : Module ℝ (BVSpace U) := inferInstanceAs (Module ℝ ↥(bvSubmodule U))

/-- Forget the variation finiteness and retain the L¹ class. -/
def toLp (f : BVSpace U) : Lp ℝ 1 (volume.restrict U) := f.val

instance : CoeFun (BVSpace U) (fun _ => EuclideanSpace ℝ (Fin n) → ℝ) :=
  ⟨fun f => f.toLp⟩

@[simp]
theorem toLp_zero : (0 : BVSpace U).toLp = 0 := rfl

@[simp]
theorem toLp_add (f g : BVSpace U) : (f + g).toLp = f.toLp + g.toLp := rfl

@[simp]
theorem toLp_smul (c : ℝ) (f : BVSpace U) : (c • f).toLp = c • f.toLp := rfl

@[ext]
theorem ext {f g : BVSpace U} (h : f.toLp = g.toLp) : f = g := Subtype.ext h

theorem ext_ae {f g : BVSpace U} (h : f =ᵐ[volume.restrict U] g) : f = g :=
  ext (Lp.ext h)

theorem coeFn_zero : ⇑(0 : BVSpace U) =ᵐ[volume.restrict U] 0 :=
  Lp.coeFn_zero ℝ 1 (volume.restrict U)

theorem coeFn_add (f g : BVSpace U) :
    ⇑(f + g) =ᵐ[volume.restrict U] fun x => f x + g x :=
  Lp.coeFn_add f.toLp g.toLp

theorem coeFn_smul (c : ℝ) (f : BVSpace U) :
    ⇑(c • f) =ᵐ[volume.restrict U] fun x => c * f x :=
  Lp.coeFn_smul c f.toLp

/-- Every representative selected for a BV class is an integrable BV function. -/
theorem isBVOn (f : BVSpace U) : IsBVOn f U :=
  ⟨memLp_one_iff_integrable.mp (Lp.memLp f.toLp), f.property⟩

/-- Pass from an actual BV function to its almost-everywhere class. -/
def ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsBVOn f U) : BVSpace U :=
  ⟨(memLp_one_iff_integrable.mpr hf.1).toLp f, by
    change variation ((memLp_one_iff_integrable.mpr hf.1).toLp f) U < ∞
    rw [variation_congr_ae U (MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf.1))]
    exact hf.2⟩

theorem coeFn_ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsBVOn f U) :
    ⇑(ofFunction f hf) =ᵐ[volume.restrict U] f :=
  MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf.1)

theorem ofFunction_congr {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : IsBVOn f U) (hg : IsBVOn g U) (h : f =ᵐ[volume.restrict U] g) :
    ofFunction f hf = ofFunction g hg :=
  ext_ae ((coeFn_ofFunction f hf).trans (h.trans (coeFn_ofFunction g hg).symm))

@[simp]
theorem ofFunction_coeFn (f : BVSpace U) : ofFunction f f.isBVOn = f :=
  ext_ae (coeFn_ofFunction f f.isBVOn)

instance : Norm (BVSpace U) where
  norm f := ‖f.toLp‖ + (variation f U).toReal

/-- The BV norm is the L¹ norm plus variation. -/
theorem norm_def (f : BVSpace U) : ‖f‖ = ‖f.toLp‖ + (variation f U).toReal := rfl

/-- The L¹ part of the BV norm is the integral of the absolute value. -/
theorem norm_toLp_eq_integral (f : BVSpace U) : ‖f.toLp‖ = ∫ x in U, ‖f x‖ := by
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f.toLp),
    integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f.toLp)]

/-- The norm formula in terms of the chosen function representative. -/
theorem norm_eq_integral_add_variation (f : BVSpace U) :
    ‖f‖ = (∫ x in U, ‖f x‖) + (variation f U).toReal := by
  rw [norm_def, norm_toLp_eq_integral]

/-- Elementary BV inequalities supply the normed-space axioms. -/
theorem normedSpaceCore : NormedSpace.Core ℝ (BVSpace U) where
  norm_nonneg f := add_nonneg (norm_nonneg f.toLp) ENNReal.toReal_nonneg
  norm_smul c f := by
    rw [norm_def, toLp_smul, variation_congr_ae U (Lp.coeFn_smul c f.toLp)]
    change ‖c • f.toLp‖ + (variation (fun x => c * f x) U).toReal = ‖c‖ * ‖f‖
    rw [variation_const_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg c), norm_smul, norm_def,
      Real.norm_eq_abs, mul_add]
  norm_triangle f g := by
    have hv := variation_add_le f.isBVOn.1.locallyIntegrableOn g.isBVOn.1.locallyIntegrableOn
    have hv' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨f.isBVOn.2.ne, g.isBVOn.2.ne⟩) hv
    rw [ENNReal.toReal_add f.isBVOn.2.ne g.isBVOn.2.ne] at hv'
    rw [norm_def, toLp_add, variation_congr_ae U (Lp.coeFn_add f.toLp g.toLp),
      norm_def f, norm_def g]
    change ‖f.toLp + g.toLp‖ + (variation (fun x => f x + g x) U).toReal ≤
      (‖f.toLp‖ + (variation f U).toReal) + (‖g.toLp‖ + (variation g U).toReal)
    linarith [norm_add_le f.toLp g.toLp]
  norm_eq_zero_iff f := by
    constructor
    · intro hf
      apply ext
      rw [toLp_zero]
      apply norm_eq_zero.mp
      rw [norm_def] at hf
      exact le_antisymm (by linarith [ENNReal.toReal_nonneg (a := variation f U)])
        (norm_nonneg f.toLp)
    · rintro rfl
      rw [norm_def, toLp_zero,
        variation_congr_ae U (Lp.coeFn_zero ℝ 1 (volume.restrict U))]
      change ‖(0 : Lp ℝ 1 (volume.restrict U))‖ +
        (variation (fun _ => (0 : ℝ)) U).toReal = 0
      simp

instance : NormedAddCommGroup (BVSpace U) := NormedAddCommGroup.ofCore normedSpaceCore
instance : NormedSpace ℝ (BVSpace U) := NormedSpace.ofCore normedSpaceCore

/-- Passing from a BV function to its class preserves the full BV norm. -/
theorem norm_ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsBVOn f U) :
    ‖ofFunction f hf‖ = (∫ x in U, ‖f x‖) + (variation f U).toReal := by
  rw [norm_eq_integral_add_variation, variation_congr_ae U (coeFn_ofFunction f hf)]
  congr 1
  exact integral_congr_ae
    (by filter_upwards [coeFn_ofFunction f hf] with x hx using congrArg norm hx)

/-- A function-level linear map descends to BV classes if it preserves BV and respects
almost-everywhere equality of BV inputs. The source and target dimensions may differ. -/
def liftLinearMap {m : ℕ} {V : Set (EuclideanSpace ℝ (Fin m))}
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
    (hBV : ∀ f, IsBVOn f U → IsBVOn (T f) V)
    (hAE : ∀ f g, IsBVOn f U → IsBVOn g U → f =ᵐ[volume.restrict U] g →
      T f =ᵐ[volume.restrict V] T g) : BVSpace U →ₗ[ℝ] BVSpace V where
  toFun f := ofFunction (T f) (hBV f f.isBVOn)
  map_add' f g := by
    apply ext_ae
    have hsum : T (⇑(f + g)) =ᵐ[volume.restrict V] fun x => T f x + T g x := by
      have h := hAE (⇑(f + g)) (fun x => f x + g x) (f + g).isBVOn
        (f.isBVOn.add g.isBVOn) (coeFn_add f g)
      change T (⇑(f + g)) =ᵐ[volume.restrict V] T (⇑f + ⇑g) at h
      rw [map_add] at h
      exact h
    filter_upwards [coeFn_ofFunction (T (⇑(f + g))) (hBV (⇑(f + g)) (f + g).isBVOn),
      coeFn_add (ofFunction (T f) (hBV f f.isBVOn))
        (ofFunction (T g) (hBV g g.isBVOn)),
      coeFn_ofFunction (T f) (hBV f f.isBVOn),
      coeFn_ofFunction (T g) (hBV g g.isBVOn), hsum] with x hx hsum' hf hg hT
    simp only [hx, hsum', hf, hg, hT]
  map_smul' c f := by
    apply ext_ae
    have hsmul : T (⇑(c • f)) =ᵐ[volume.restrict V] fun x => c * T f x := by
      have h := hAE (⇑(c • f)) (fun x => c * f x) (c • f).isBVOn
        (f.isBVOn.const_mul c) (coeFn_smul c f)
      change T (⇑(c • f)) =ᵐ[volume.restrict V] T (c • ⇑f) at h
      rw [map_smul] at h
      exact h
    filter_upwards [coeFn_ofFunction (T (⇑(c • f))) (hBV (⇑(c • f)) (c • f).isBVOn),
      coeFn_smul c (ofFunction (T f) (hBV f f.isBVOn)),
      coeFn_ofFunction (T f) (hBV f f.isBVOn), hsmul] with x hx hsmul' hf hT
    simp only [RingHom.id_apply, hx, hsmul', hf, hT]

/-- The lifted map has the expected representative almost everywhere. -/
theorem coeFn_liftLinearMap {m : ℕ} {V : Set (EuclideanSpace ℝ (Fin m))}
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
    (hBV : ∀ f, IsBVOn f U → IsBVOn (T f) V)
    (hAE : ∀ f g, IsBVOn f U → IsBVOn g U → f =ᵐ[volume.restrict U] g →
      T f =ᵐ[volume.restrict V] T g) (f : BVSpace U) :
    ⇑(liftLinearMap T hBV hAE f) =ᵐ[volume.restrict V] T f :=
  coeFn_ofFunction (T f) (hBV f f.isBVOn)

/-- Lifting commutes with passage from any actual BV representative to its class. -/
theorem liftLinearMap_ofFunction {m : ℕ} {V : Set (EuclideanSpace ℝ (Fin m))}
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
    (hBV : ∀ f, IsBVOn f U → IsBVOn (T f) V)
    (hAE : ∀ f g, IsBVOn f U → IsBVOn g U → f =ᵐ[volume.restrict U] g →
      T f =ᵐ[volume.restrict V] T g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsBVOn f U) :
    liftLinearMap T hBV hAE (ofFunction f hf) = ofFunction (T f) (hBV f hf) := by
  exact ofFunction_congr (hBV (ofFunction f hf) (ofFunction f hf).isBVOn) (hBV f hf)
    (hAE (ofFunction f hf) f (ofFunction f hf).isBVOn hf (coeFn_ofFunction f hf))

section ContinuousLift

variable {m : ℕ} {V : Set (EuclideanSpace ℝ (Fin m))}
  (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
  (hBV : ∀ f, IsBVOn f U → IsBVOn (T f) V)
  (hAE : ∀ f g, IsBVOn f U → IsBVOn g U → f =ᵐ[volume.restrict U] g →
    T f =ᵐ[volume.restrict V] T g)
  (C : ℝ)
  (hbound : ∀ f, IsBVOn f U →
    (∫ x in V, ‖T f x‖) + (variation (T f) V).toReal ≤
      C * ((∫ x in U, ‖f x‖) + (variation f U).toReal))

include hbound

/-- A bound on function representatives is exactly a norm bound on BV classes. -/
theorem norm_liftLinearMap_le (f : BVSpace U) :
    ‖liftLinearMap T hBV hAE f‖ ≤ C * ‖f‖ := by
  change ‖ofFunction (T f) (hBV f f.isBVOn)‖ ≤ C * ‖f‖
  rw [norm_ofFunction, norm_eq_integral_add_variation]
  exact hbound f f.isBVOn

/-- A bounded function-level linear operator descends to a continuous linear operator
between the corresponding normed BV spaces. -/
def liftContinuousLinearMap : BVSpace U →L[ℝ] BVSpace V :=
  (liftLinearMap T hBV hAE).mkContinuous C (norm_liftLinearMap_le T hBV hAE C hbound)

/-- The continuous lift has the expected representative almost everywhere. -/
theorem coeFn_liftContinuousLinearMap (f : BVSpace U) :
    ⇑(liftContinuousLinearMap T hBV hAE C hbound f) =ᵐ[volume.restrict V] T f :=
  coeFn_liftLinearMap T hBV hAE f

/-- The continuous lift acts on the class of any BV representative as expected. -/
theorem liftContinuousLinearMap_ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsBVOn f U) :
    liftContinuousLinearMap T hBV hAE C hbound (ofFunction f hf) =
      ofFunction (T f) (hBV f hf) :=
  liftLinearMap_ofFunction T hBV hAE f hf

/-- The operator norm of the continuous lift satisfies the original nonnegative bound. -/
theorem norm_liftContinuousLinearMap_le (hC : 0 ≤ C) :
    ‖liftContinuousLinearMap T hBV hAE C hbound‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC (norm_liftLinearMap_le T hBV hAE C hbound)

end ContinuousLift

end BVSpace

end LiquidDrop
