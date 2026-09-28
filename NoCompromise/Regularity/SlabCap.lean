import NoCompromise.Regularity.Cylinders
import NoCompromise.Regularity.CompressionLinear
import NoCompromise.DeGiorgi.Structure

/-! # Slab-and-cap configurations for the standard cylinder -/

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace LiquidDrop

def standardCylinder (r : ℝ) : Set AmbientSpace :=
  {x | ‖graphProjectionN 2 x‖ < r ∧ |x 2| < r}

def cylindricalCap (r s : ℝ) : Set AmbientSpace :=
  (fun p : EuclideanSpace ℝ (Fin 2) => graphAppendN p s) '' ball 0 r

lemma standardCylinder_eq_cylinder (r : ℝ) :
    standardCylinder r = cylinder 0 r (EuclideanSpace.single 2 1) := by
  have hp (x : AmbientSpace) : cylinderProjection (EuclideanSpace.single 2 1) x =
      graphAppendN (graphProjectionN 2 x) 0 := by
    ext i
    fin_cases i <;> simp [cylinderProjection, graphAppendN, graphBaseN,
      graphProjectionN, Fin.sum_univ_two, EuclideanSpace.inner_single_left]
  have hn (x : AmbientSpace) :
      ‖cylinderProjection (EuclideanSpace.single 2 1) x‖ = ‖graphProjectionN 2 x‖ := by
    rw [hp]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [norm_graphAppendN_sq, zero_pow (by decide : 2 ≠ 0), add_zero]
  ext x
  simp only [standardCylinder, cylinder, mem_ofPred_eq, sub_zero, hn,
    EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]

lemma isOpen_standardCylinder (r : ℝ) : IsOpen (standardCylinder r) := by
  rw [standardCylinder_eq_cylinder]
  exact isOpen_cylinder _ _ _

lemma isBounded_standardCylinder (r : ℝ) : Bornology.IsBounded (standardCylinder r) := by
  rw [standardCylinder_eq_cylinder]
  exact isBounded_cylinder _ _ (by simp)

/-- The actual reduced boundary lies in the cleared slab inside the cylinder. -/
def HasCylindricalSlab (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (r c η : ℝ) : Prop :=
  0 < r ∧ 0 < η ∧ η < 1 ∧ |c| + η * r < r ∧
    ∀ x ∈ reducedBoundary E hE hmE ∩ standardCylinder r, |x 2 - c| < η * r

/-- Blueprint `def:slab-cap`: the cap statements use actual density-one and
density-zero representatives, modulo normalized H² on the two cap disks. -/
def IsSlabCapConfiguration (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (r c η : ℝ) : Prop :=
  HasCylindricalSlab E hE hmE r c η ∧
    hausdorffMeasure2 3 (cylindricalCap r (-r) \ densityOne E) = 0 ∧
    hausdorffMeasure2 3 (cylindricalCap r r \ densityZero E) = 0

/-- The reversed configuration exchanges the two cap phases. -/
def IsReversedSlabCapConfiguration (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (r c η : ℝ) : Prop :=
  HasCylindricalSlab E hE hmE r c η ∧
    hausdorffMeasure2 3 (cylindricalCap r (-r) \ densityZero E) = 0 ∧
    hausdorffMeasure2 3 (cylindricalCap r r \ densityOne E) = 0

end LiquidDrop
