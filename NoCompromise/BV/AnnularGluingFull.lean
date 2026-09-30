module

public import NoCompromise.BV.AnnularGluingDiagonal

@[expose] public section

/-!
# All clauses of the annular gluing proposition

These proof aliases collect the exact coarea identity, the common almost-everywhere
gluing inequalities, radius selection from actual L¹ convergence, and the explicit
expanding-annulus diagonal construction in the blueprint's assigned module.
-/

namespace LiquidDrop

abbrev annular_gluing_coarea := @spherical_mismatch_coarea

abbrev annular_gluing_ae := @ae_annular_gluing_perimeter

abbrev annular_gluing_selection := @exists_annular_gluing_radii

abbrev annular_gluing_diagonal := @exists_diagonal_annular_gluing_radii

end LiquidDrop
