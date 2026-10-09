import FiniteAsdim.Theorem

/-!
# Kernel dependency audit

Compile this file and retain its output. `scripts/audit.py --axiom-log`
checks that these declarations use only Lean's standard logical axioms.
The source scan is an additional safeguard; it does not replace compilation.
-/

#print axioms FiniteAsdim.theorem1_1
#print axioms FiniteAsdim.theorem1_1_closed
#print axioms FiniteAsdim.theorem1_1_statement
#print axioms FiniteAsdim.lattice_bound

#print axioms FiniteAsdim.uniform_cancellation
#print axioms FiniteAsdim.completion_image_reduction
#print axioms FiniteAsdim.generating_reduction_to_lattice
#print axioms FiniteAsdim.reduction_to_lattice
#print axioms FiniteAsdim.collision_reduction_data
#print axioms FiniteAsdim.collisionImage_rank
#print axioms FiniteAsdim.torsion_subgroup_finite
#print axioms FiniteAsdim.torsion_quotient_rank
#print axioms FiniteAsdim.cyclic_group_quotient_rank_drop
#print axioms FiniteAsdim.torsionFree_equiv_lattice

#print axioms FiniteAsdim.Schreier.near_iff_common_future
#print axioms FiniteAsdim.Schreier.quotient_boundedToOneAction
#print axioms FiniteAsdim.fiber_pair_graph_coloring
#print axioms FiniteAsdim.finite_window_local_rule
#print axioms FiniteAsdim.finite_pattern_compression
#print axioms FiniteAsdim.local_freeness_witness
#print axioms FiniteAsdim.asdimLE_finite_union
#print axioms FiniteAsdim.rank_step
