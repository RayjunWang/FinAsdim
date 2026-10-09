import FiniteAsdim.Algebra
import FiniteAsdim.Generators
import FiniteAsdim.Reductions

namespace FiniteAsdim
namespace Schreier

variable {M N X : Type*} [AddCommMonoid M] [AddCommMonoid N]
variable [AddAction M X] [AddAction N X]

/-- Changing scalars through a surjection preserves the generator graph exactly. -/
theorem edge_scalar_iff (φ : M →+ N)
    (hφ : ∀ m : M, ∀ x : X, φ m +ᵥ x = m +ᵥ x) (S : Set M) (x y : X) :
    Edge (φ '' S) x y ↔ Edge S x y := by
  constructor
  · rintro ⟨n, ⟨m, hm, rfl⟩, h | h⟩
    · exact ⟨m, hm, Or.inl (by simpa only [hφ] using h)⟩
    · exact ⟨m, hm, Or.inr (by simpa only [hφ] using h)⟩
  · rintro ⟨m, hm, h | h⟩
    · exact ⟨φ m, ⟨m, hm, rfl⟩, Or.inl (by simpa only [hφ] using h)⟩
    · exact ⟨φ m, ⟨m, hm, rfl⟩, Or.inr (by simpa only [hφ] using h)⟩

theorem path_scalar_iff (φ : M →+ N)
    (hφ : ∀ m : M, ∀ x : X, φ m +ᵥ x = m +ᵥ x)
    (S : Set M) (n : ℕ) (x y : X) :
    Path (φ '' S) n x y ↔ Path S n x y := by
  constructor
  · intro h
    induction h with
    | nil x => exact Path.nil x
    | cons e h ih => exact Path.cons ((edge_scalar_iff φ hφ S _ _).mp e) ih
  · intro h
    induction h with
    | nil x => exact Path.nil x
    | cons e h ih => exact Path.cons ((edge_scalar_iff φ hφ S _ _).mpr e) ih

theorem near_scalar_iff (φ : M →+ N)
    (hφ : ∀ m : M, ∀ x : X, φ m +ᵥ x = m +ᵥ x)
    (S : Set M) (n : ℕ) (x y : X) :
    Near (φ '' S) n x y ↔ Near S n x y := by
  constructor <;> rintro ⟨k, hk, hp⟩
  · exact ⟨k, hk, (path_scalar_iff φ hφ S k x y).mp hp⟩
  · exact ⟨k, hk, (path_scalar_iff φ hφ S k x y).mpr hp⟩

theorem scalar_metric_eq (φ : M →+ N)
    (hφ : ∀ m : M, ∀ x : X, φ m +ᵥ x = m +ᵥ x) (S : Set M) :
    natMetric (X := X) (φ '' S) = natMetric (X := X) S := by
  apply NatMetric.ext
  exact near_scalar_iff φ hφ S

theorem scalar_boundedToOneAction (φ : M →+ N) (hsurj : Function.Surjective φ)
    (hφ : ∀ m : M, ∀ x : X, φ m +ᵥ x = m +ᵥ x)
    (hX : BoundedToOneAction M X) : BoundedToOneAction N X := by
  intro n
  obtain ⟨m, rfl⟩ := hsurj n
  obtain ⟨k, hk⟩ := hX m
  refine ⟨k, ?_⟩
  intro y
  simpa only [hφ] using hk y

end Schreier

/-- Surjective scalar homomorphisms preserve finite generation. -/
theorem scalar_finitely_generated {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [AddMonoid.FG M] (φ : M →+ N) (hsurj : Function.Surjective φ) : AddMonoid.FG N :=
  AddMonoid.fg_of_surjective φ hsurj

/-- The image of a generating set generates the scalar quotient. -/
theorem scalar_generators {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (φ : M →+ N) (hsurj : Function.Surjective φ) (S : Set M)
    (hS : AddSubmonoid.closure S = ⊤) : AddSubmonoid.closure (φ '' S) = ⊤ := by
  apply top_unique
  intro n htop
  clear htop
  obtain ⟨m, rfl⟩ := hsurj n
  have hm : m ∈ AddSubmonoid.closure S := by rw [hS]; trivial
  induction hm using AddSubmonoid.closure_induction with
  | mem m hm => exact AddSubmonoid.subset_closure ⟨m, hm, rfl⟩
  | zero =>
      rw [map_zero]
      exact (AddSubmonoid.closure (φ '' S)).zero_mem
  | add a b ha hb iha ihb => simpa using (AddSubmonoid.closure (φ '' S)).add_mem iha ihb

theorem scalar_finset_generators {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [DecidableEq N]
    (φ : M →+ N) (hsurj : Function.Surjective φ) (S : Finset M)
    (hS : AddSubmonoid.closure (S : Set M) = ⊤) :
    AddSubmonoid.closure (S.image φ : Set N) = ⊤ := by
  classical
  simpa only [Finset.coe_image] using scalar_generators φ hsurj (S : Set M) hS

/-- An equivariantly embedded invariant subspace inherits bounded fibers. -/
theorem boundedToOneAction_of_injective_equivariant {M X Y : Type*} [AddCommMonoid M]
    [AddAction M X] [AddAction M Y] (f : Y → X) (hinj : Function.Injective f)
    (heq : Schreier.Equivariant (M := M) f)
    (hX : Schreier.BoundedToOneAction M X) : Schreier.BoundedToOneAction M Y := by
  intro m
  obtain ⟨k, hk⟩ := hX m
  refine ⟨k, ?_⟩
  intro y
  calc
    ((fun z : Y => m +ᵥ z) ⁻¹' {y}).encard
        ≤ ((fun z : X => m +ᵥ z) ⁻¹' {f y}).encard := by
      apply Set.encard_le_encard_of_injOn (f := f)
      · intro z hz
        change m +ᵥ f z = f y
        rw [← heq]
        change m +ᵥ z = y at hz
        exact congrArg f hz
      · exact hinj.injOn
    _ ≤ (k : ℕ∞) := hk (f y)

/-- The intrinsic graph on a forward image equals its restricted ambient graph. -/
theorem forwardImage_metric_eq {M X : Type*} [AddCommMonoid M] [AddAction M X]
    (c : M) (S : Set M) :
    letI := forwardImageAction (X := X) c
    Schreier.natMetric (X := ForwardImage (X := X) c) S =
      (Schreier.natMetric (X := X) S).restrict (Set.range (fun x : X => c +ᵥ x)) := by
  letI := forwardImageAction (X := X) c
  apply NatMetric.ext
  intro s x y
  change Schreier.Near S s x y ↔ Schreier.Near S s x.val y.val
  rw [Schreier.near_iff_common_future, Schreier.near_iff_common_future]
  constructor
  · rintro ⟨l, k, a, b, ha, hb, hlen, hab⟩
    exact ⟨l, k, a, b, ha, hb, hlen, congrArg Subtype.val hab⟩
  · rintro ⟨l, k, a, b, ha, hb, hlen, hab⟩
    exact ⟨l, k, a, b, ha, hb, hlen, Subtype.ext hab⟩

/-- A forward-image action whose scalars descend through a surjection has
the same asymptotic dimension as the original action and retains bounded fibers. -/
theorem image_reduction_coarse {M N X : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [AddAction M X] (c : M) (I : AddAction N (ForwardImage (X := X) c))
    (φ : M →+ N) (hsurj : Function.Surjective φ)
    (hφ : ∀ m : M, ∀ y : ForwardImage (X := X) c,
      @VAdd.vadd _ _ I.toVAdd (φ m) y =
        @VAdd.vadd _ _ (forwardImageAction c).toVAdd m y)
    (hbounded : Schreier.BoundedToOneAction M X)
    (S : Finset M) (hS : AddSubmonoid.closure (S : Set M) = ⊤) :
    letI := I
    Schreier.BoundedToOneAction N (ForwardImage (X := X) c) ∧
      ∀ n : ℕ, AsdimLE (Schreier.natMetric (X := X) (S : Set M)) n ↔
        AsdimLE (Schreier.natMetric (X := ForwardImage (X := X) c) (φ '' (S : Set M))) n := by
  letI := forwardImageAction (X := X) c
  letI := I
  have hbM : Schreier.BoundedToOneAction M (ForwardImage (X := X) c) :=
    boundedToOneAction_of_injective_equivariant Subtype.val Subtype.val_injective
      (fun _ _ => rfl) hbounded
  refine ⟨Schreier.scalar_boundedToOneAction φ hsurj hφ hbM, ?_⟩
  intro n
  rw [Schreier.scalar_metric_eq φ hφ, forwardImage_metric_eq c]
  obtain ⟨R, hc⟩ := Schreier.exists_word_of_generates hS c
  exact asdimLE_forward_image (S : Set M) hc n

/-- Cancellation reduction, with its actual quotient action, bounded fibers,
and equality of all finite asymptotic dimension bounds. -/
theorem cancellation_reduction_coarse {M X : Type*} [AddCommMonoid M]
    [AddMonoid.FG M] [AddAction M X] (θ : AddCon M)
    (hθ : ∀ a b : M, θ a b → ∀ x : X, a +ᵥ x = b +ᵥ x)
    (hbounded : Schreier.BoundedToOneAction M X)
    (S : Finset M) (hS : AddSubmonoid.closure (S : Set M) = ⊤) :
    ∃ c : M, ∃ I : AddAction (cancellativeClosure θ).Quotient (ForwardImage (X := X) c),
      letI := I
      Schreier.BoundedToOneAction (cancellativeClosure θ).Quotient (ForwardImage (X := X) c) ∧
        ∀ n : ℕ, AsdimLE (Schreier.natMetric (X := X) (S : Set M)) n ↔
          AsdimLE (Schreier.natMetric (X := ForwardImage (X := X) c)
            ((cancellativeClosure θ).mk' '' (S : Set M))) n := by
  obtain ⟨c, I, hI⟩ := exists_cancellative_closure_action θ hθ
  exact ⟨c, I, image_reduction_coarse c I (cancellativeClosure θ).mk'
    (cancellativeClosure θ).mk'_surjective hI hbounded S hS⟩
end FiniteAsdim



