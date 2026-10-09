import FiniteAsdim.CollisionReduction
import FiniteAsdim.ScalarQuotient

namespace FiniteAsdim

universe u v

/-- The collision subspace is represented by an actual bounded-to-one action
of the image monoid in the cyclic group quotient, with a finite generating
set and equality of every asymptotic dimension bound. The separate rank
calculation only needs the collision scalars to be distinct in a lattice. -/
theorem collision_reduction_data {Γ : Type u} [AddCommGroup Γ]
    (P : AddSubmonoid Γ) [AddMonoid.FG P]
    {X : Type v} [AddAction P X] (hbounded : Schreier.BoundedToOneAction P X)
    (S : Finset P) (hS : AddSubmonoid.closure (S : Set P) = ⊤) (p q : P) :
    ∃ Y : Type v, ∃ I : AddAction (AddMonoidHom.mrange (collisionGroupMap P p q)) Y,
      ∃ T : Finset (AddMonoidHom.mrange (collisionGroupMap P p q)),
      letI := I
      Schreier.BoundedToOneAction (AddMonoidHom.mrange (collisionGroupMap P p q)) Y ∧
      AddSubmonoid.closure (T : Set (AddMonoidHom.mrange (collisionGroupMap P p q))) = ⊤ ∧
      ∀ n : ℕ,
        AsdimLE ((Schreier.natMetric (X := X) (S : Set P)).restrict (collisionSet p q)) n ↔
          AsdimLE (Schreier.natMetric (X := Y)
            (T : Set (AddMonoidHom.mrange (collisionGroupMap P p q)))) n := by
  classical
  let A := collisionSet (X := X) p q
  have hA : Schreier.Invariant (M := P) A := collisionSet_invariant p q
  letI : AddAction P A := Schreier.addActionOn A hA
  have hbA : Schreier.BoundedToOneAction P A :=
    boundedToOneAction_of_injective_equivariant Subtype.val Subtype.val_injective
      (fun _ _ => rfl) hbounded
  have hpqA : ∀ x : A, p +ᵥ x = q +ᵥ x := fun x => Subtype.ext x.property
  obtain ⟨c, I, hI⟩ := collision_image_action (X := A) P p q hpqA
  let φ := (collisionGroupMap P p q).mrangeRestrict
  let T : Finset (AddMonoidHom.mrange (collisionGroupMap P p q)) := S.image φ
  have hT : AddSubmonoid.closure (T : Set (AddMonoidHom.mrange (collisionGroupMap P p q))) = ⊤ :=
    scalar_finset_generators φ (collisionGroupMap P p q).mrangeRestrict_surjective S hS
  have hred := image_reduction_coarse (X := A) c I φ
    (collisionGroupMap P p q).mrangeRestrict_surjective hI hbA S hS
  refine ⟨ForwardImage (X := A) c, I, T, hred.1, hT, ?_⟩
  intro n
  rw [← invariant_metric_eq A hA]
  simpa only [T, Finset.coe_image] using hred.2 n

end FiniteAsdim
