import FiniteAsdim.Coarse
import FiniteAsdim.Quotient

namespace FiniteAsdim

variable {M X : Type*} [AddCommMonoid M] [AddAction M X]

/-- The metric identification for forward-invariant subsets. -/
theorem invariant_metric_eq (A : Set X) (hA : Schreier.Invariant (M := M) A) (S : Set M) :
    letI := Schreier.addActionOn A hA
    Schreier.natMetric (X := A) S = (Schreier.natMetric (X := X) S).restrict A := by
  letI := Schreier.addActionOn A hA
  apply NatMetric.ext
  intro s x y
  exact Schreier.invariant_near_iff A hA S s x y

/-- Passing to a forward image is a quasi-isometry, expressed as equality
of every finite dimension bound. -/
theorem asdimLE_forward_image (S : Set M) {c : M} {R : ℕ}
    (hc : Schreier.Word S R c) (n : ℕ) :
    AsdimLE (Schreier.natMetric (X := X) S) n ↔
      AsdimLE ((Schreier.natMetric (X := X) S).restrict (Set.range (fun x : X => c +ᵥ x))) n := by
  let d := Schreier.natMetric (X := X) S
  let A := Set.range (fun x : X => c +ᵥ x)
  let f : A → X := Subtype.val
  have he : CoarseEmbedding (d.restrict A) d f :=
    { a := 1
      b := 0
      forward := fun h => by simpa using h
      backward := fun h => by simpa using h }
  have hdense : ∀ x : X, ∃ y : A, d.near R x (f y) := by
    intro x
    exact ⟨⟨c +ᵥ x, ⟨x, rfl⟩⟩, Schreier.word_near hc x⟩
  exact (asdimLE_iff_of_quasiIsometry (d.restrict A) d he R hdense n).symm

/-- Lemma 3.2's quasi-isometry conclusion. The equivalence relation has
uniformly bounded diameter; its finite size is needed separately for
the bounded-to-one conclusion in `Quotient.lean`. -/
theorem asdimLE_quotient (E : Setoid X) (hE : Schreier.SetoidInvariant (M := M) E)
    (S : Set M) (D : ℕ) (hD : ∀ x y, E.r x y → Schreier.Near S D x y) (n : ℕ) :
    letI := Schreier.quotientAddAction E hE
    AsdimLE (Schreier.natMetric (X := X) S) n ↔
      AsdimLE (Schreier.natMetric (X := Quotient E) S) n := by
  letI := Schreier.quotientAddAction E hE
  let d := Schreier.natMetric (X := X) S
  let e := Schreier.natMetric (X := Quotient E) S
  let f : X → Quotient E := Quotient.mk E
  have he : CoarseEmbedding d e f :=
    { a := 1
      b := D
      forward := fun {s x y} h =>
        Schreier.near_mono (by simp) (Schreier.quotient_near E hE S h)
      backward := fun h => by simpa using Schreier.quotient_near_reflects E hE S D hD h }
  have hdense : ∀ y : Quotient E, ∃ x : X, e.near 0 y (f x) := by
    intro y
    obtain ⟨x, rfl⟩ := Schreier.quotient_projection_surjective E y
    exact ⟨x, Schreier.near_refl S _⟩
  exact asdimLE_iff_of_quasiIsometry d e he 0 hdense n

end FiniteAsdim
