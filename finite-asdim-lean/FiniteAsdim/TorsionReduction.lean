import FiniteAsdim.Torsion
import FiniteAsdim.ScalarQuotient

namespace FiniteAsdim

private lemma torsion_encard_union {I X : Type*} (s : Finset I) (A : I → Set X) :
    (⋃ i ∈ s, A i).encard ≤ ∑ i ∈ s, (A i).encard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have heq : (⋃ j ∈ insert i s, A j) = A i ∪ (⋃ j ∈ s, A j) := by ext x; simp
    rw [heq, Finset.sum_insert hi]
    exact (Set.encard_union_le _ _).trans (add_le_add (le_refl _) ih)

/-- The actual torsion quotient and descended image action preserve every
finite asymptotic dimension bound. The finite subgroup may be any `T`;
using the full torsion subgroup is the rank-preserving specialization. -/
theorem torsion_reduction_coarse {Γ X : Type*} [AddCommGroup Γ]
    (P : AddSubmonoid Γ) [AddAction P X] (T : AddSubgroup Γ) [Fintype T]
    (b : Γ) (B : T → P) (hB : ∀ t : T, (B t : Γ) = b + (t : Γ))
    (hbounded : Schreier.BoundedToOneAction P X)
    (S : Finset P) (hS : AddSubmonoid.closure (S : Set P) = ⊤) :
    let E := positiveTranslateSetoid (X := X) P T B
    letI : AddAction P (Quotient E) := quotientAddAction E (positiveTranslateSetoid_invariant P T B)
    ∃ I : AddAction (AddMonoidHom.mrange (torsionScalarHom P T))
      (ForwardImage (X := Quotient E) (B 0)),
      letI := I
      Schreier.BoundedToOneAction (AddMonoidHom.mrange (torsionScalarHom P T))
        (ForwardImage (X := Quotient E) (B 0)) ∧
      ∀ n : ℕ, AsdimLE (Schreier.natMetric (X := X) (S : Set P)) n ↔
        AsdimLE (Schreier.natMetric (X := ForwardImage (X := Quotient E) (B 0))
          ((torsionScalarHom P T).mrangeRestrict '' (S : Set P))) n := by
  classical
  let E := positiveTranslateSetoid (X := X) P T B
  letI : AddAction P (Quotient E) := quotientAddAction E (positiveTranslateSetoid_invariant P T B)
  have hinv : Schreier.SetoidInvariant (M := P) E := by
    intro p x y h
    exact positiveTranslateSetoid_invariant P T B p x y h
  have hshift := positiveTranslateFamily_shift (X := X) P T b B hB
  choose k hk using fun t : T => hbounded (B t)
  let C := ∑ t, k t
  have hC : ∀ x : X, {y : X | E y x}.encard ≤ (C : ℕ∞) := by
    intro x
    let A : T → Set X := fun t => (fun y : X => B t +ᵥ y) ⁻¹' {B 0 +ᵥ x}
    have hsub : {y : X | E y x} ⊆ ⋃ t, A t := by
      intro y hy
      obtain ⟨t, ht⟩ := eqvGen_torsion_common_future (positiveTranslateFamily P T B)
        hshift (E.symm hy)
      exact Set.mem_iUnion.mpr ⟨t, ht.symm⟩
    calc
      _ ≤ (⋃ t, A t).encard := Set.encard_le_encard hsub
      _ ≤ ∑ t, (A t).encard := by simpa using torsion_encard_union Finset.univ A
      _ ≤ ∑ t, (k t : ℕ∞) := Finset.sum_le_sum (fun t _ => hk t (B 0 +ᵥ x))
      _ = (C : ℕ∞) := by dsimp [C]; rw [Nat.cast_sum]
  have hbQ : Schreier.BoundedToOneAction P (Quotient E) :=
    Schreier.quotient_boundedToOneAction E hinv C hC hbounded
  have hwords : ∀ t : T, ∃ n, Schreier.Word (S : Set P) n (B t) :=
    fun t => Schreier.exists_word_of_generates hS (B t)
  choose len hlen using hwords
  let D := len 0 + (Finset.univ : Finset T).sup len
  have hD : ∀ x y : X, E x y → Schreier.Near (S : Set P) D x y := by
    intro x y hxy
    obtain ⟨t, ht⟩ := eqvGen_torsion_common_future (positiveTranslateFamily P T B) hshift hxy
    apply Schreier.near_iff_common_future.mpr
    exact ⟨len 0, len t, B 0, B t, hlen 0, hlen t,
      Nat.add_le_add_left (Finset.le_sup (Finset.mem_univ t)) _, ht⟩
  have hQI : ∀ n, AsdimLE (Schreier.natMetric (X := X) (S : Set P)) n ↔
      AsdimLE (Schreier.natMetric (X := Quotient E) (S : Set P)) n :=
    fun n => asdimLE_quotient E hinv (S : Set P) D hD n
  obtain ⟨I, hI⟩ := torsion_image_action (X := X) P T b B hB
  refine ⟨I, ?_⟩
  have hforward := image_reduction_coarse (X := Quotient E) (B 0) I
    (torsionScalarHom P T).mrangeRestrict
    (torsionScalarHom P T).mrangeRestrict_surjective hI hbQ S hS
  exact ⟨hforward.1, fun n => (hQI n).trans (hforward.2 n)⟩

end FiniteAsdim
