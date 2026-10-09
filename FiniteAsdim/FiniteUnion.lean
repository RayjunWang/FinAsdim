import FiniteAsdim.ColoredCover
import FiniteAsdim.Coarse

namespace FiniteAsdim

universe u
variable {X : Type u} (d : NatMetric X)

/-- The saturation construction in Lemma 2.3. -/
theorem coloredCover_union {A B : Set X} {s n : ℕ}
    (hA : ColoredCover d A s n)
    (hB : ∀ t : ℕ, ColoredCover d B t n) : ColoredCover d (A ∪ B) s n := by
  classical
  obtain ⟨I, U, cU, D, coverU, boundU, sepU⟩ := hA
  obtain ⟨J, V, cV, E, coverV, boundV, sepV⟩ := hB (D + 3 * s)
  let attach : I → J → Prop := fun i j =>
    cU i = cV j ∧ ∃ x ∈ U i, ∃ y ∈ V j, d.near s x y
  let newU (i : I) : Set X := {x | x ∈ U i ∧ ∀ j, ¬attach i j}
  let newV (j : J) : Set X := V j ∪ {x | ∃ i, attach i j ∧ x ∈ U i}
  have unique (i : I) (j k : J) (hij : attach i j) (hik : attach i k) : j = k := by
    by_contra hjk
    obtain ⟨x, hx, y, hy, hxy⟩ := hij.2
    obtain ⟨z, hz, w, hw, hzw⟩ := hik.2
    have h := d.triangle (d.triangle (d.symm hxy) (boundU i x z hx hz)) hzw
    apply sepV j k (hij.1.symm.trans hik.1) hjk y hy w hw
    exact d.mono (by omega : s + D + s ≤ D + 3 * s) h
  have satWitness (j : J) (x : X) (hx : x ∈ newV j) :
      ∃ y ∈ V j, d.near (D + s) x y := by
    rcases hx with hx | ⟨i, hi, hx⟩
    · exact ⟨x, hx, d.mono (Nat.zero_le _) (d.refl x)⟩
    · obtain ⟨z, hz, y, hy, hzy⟩ := hi.2
      exact ⟨y, hy, d.triangle (boundU i x z hx hz) hzy⟩
  have V_U_separated (j k : J) (i : I) (hij : attach i k)
      (hcolor : cV j = cV k) (hne : j ≠ k)
      (x : X) (hx : x ∈ V j) (y : X) (hy : y ∈ U i) : ¬d.near s x y := by
    intro hxy
    obtain ⟨z, hz, w, hw, hzw⟩ := hij.2
    have h := d.triangle (d.triangle hxy (boundU i y z hy hz)) hzw
    exact sepV j k hcolor hne x hx w hw (d.mono (by omega : s + D + s ≤ D + 3 * s) h)
  let piece : Sum I J → Set X := Sum.elim newU newV
  let color : Sum I J → Fin (n + 1) := Sum.elim cU cV
  let L := (D + s) + E + (D + s)
  refine ⟨Sum I J, piece, color, L, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨i, hi⟩ := coverU x hx
      by_cases hj : ∃ j, attach i j
      · obtain ⟨j, hj⟩ := hj
        exact ⟨Sum.inr j, Or.inr ⟨i, hj, hi⟩⟩
      · exact ⟨Sum.inl i, hi, fun j hj' => hj ⟨j, hj'⟩⟩
    · obtain ⟨j, hj⟩ := coverV x hx
      exact ⟨Sum.inr j, Or.inl hj⟩
  · intro p x y hx hy
    rcases p with i | j
    · exact d.mono (by dsimp [L]; omega) (boundU i x y hx.1 hy.1)
    · obtain ⟨v, hv, hxv⟩ := satWitness j x hx
      obtain ⟨w, hw, hyw⟩ := satWitness j y hy
      exact d.triangle (d.triangle hxv (boundV j v w hv hw)) (d.symm hyw)
  · intro p q hcolor hne x hx y hy hxy
    rcases p with i | j <;> rcases q with k | l
    · exact sepU i k hcolor (fun he => hne (congrArg Sum.inl he)) x hx.1 y hy.1 hxy
    · change cU i = cV l at hcolor
      rcases hy with hy | ⟨k, hkl, hy⟩
      · exact hx.2 l ⟨hcolor, x, hx.1, y, hy, hxy⟩
      · by_cases hik : i = k
        · subst k
          exact hx.2 l hkl
        · exact sepU i k (hcolor.trans hkl.1.symm) hik x hx.1 y hy hxy
    · change cV j = cU k at hcolor
      rcases hx with hx | ⟨i, hij, hx⟩
      · exact hy.2 j ⟨hcolor.symm, y, hy.1, x, hx, d.symm hxy⟩
      · by_cases hik : i = k
        · subst k
          exact hy.2 j hij
        · exact sepU i k (hij.1.trans hcolor) hik x hx y hy.1 hxy
    · change cV j = cV l at hcolor
      have hjl : j ≠ l := fun he => hne (congrArg Sum.inr he)
      rcases hx with hx | ⟨i, hij, hx⟩ <;> rcases hy with hy | ⟨k, hkl, hy⟩
      · exact sepV j l hcolor hjl x hx y hy (d.mono (by omega) hxy)
      · exact V_U_separated j l k hkl hcolor hjl x hx y hy hxy
      · exact V_U_separated l j i hij hcolor.symm hjl.symm y hy x hx (d.symm hxy)
      · by_cases hik : i = k
        · subst k
          exact hjl (unique i j l hij hkl)
        · exact sepU i k (hij.1.trans (hcolor.trans hkl.1.symm)) hik x hx y hy hxy

/-- Lift a colored cover on a subspace to the ambient metric. -/
theorem coloredCover_lift {A : Set X} {s n : ℕ}
    (h : ColoredCover (d.restrict A) Set.univ s n) : ColoredCover d A s n := by
  obtain ⟨I, piece, color, D, hc, hD, hsep⟩ := h
  refine ⟨I, fun i => Subtype.val '' piece i, color, D, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hc ⟨x, hx⟩ (Set.mem_univ _)
    exact ⟨i, ⟨x, hx⟩, hi, rfl⟩
  · intro i x y hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hD i a b ha hb
  · intro i j hij hne x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hsep i j hij hne a ha b hb hxy

/-- Restrict an ambient colored cover to its covered subspace. -/
theorem coloredCover_restrict {A : Set X} {s n : ℕ}
    (h : ColoredCover d A s n) : ColoredCover (d.restrict A) Set.univ s n := by
  obtain ⟨I, piece, color, D, hc, hD, hsep⟩ := h
  refine ⟨I, fun i => Subtype.val ⁻¹' piece i, color, D, ?_, ?_, ?_⟩
  · intro x hx
    exact hc x.val x.property
  · intro i x y hx hy
    exact hD i x.val y.val hx hy
  · intro i j hij hne x hx y hy hxy
    exact hsep i j hij hne x.val hx y.val hy hxy

theorem coloredCover_of_asdimLE {A : Set X} {n s : ℕ} (hs : 1 ≤ s)
    (h : AsdimLE (d.restrict A) n) : ColoredCover d A s n := by
  have ht : 1 ≤ (n + 1) * s := Nat.mul_pos (by omega) (by omega)
  exact coloredCover_lift d (coloredCover_of_scalePartition (d.restrict A) (h _ ht))

/-- Finite unions preserve the maximum dimension bound (Lemma 2.3). -/
theorem asdimLE_union {A B : Set X} {n : ℕ}
    (hA : AsdimLE (d.restrict A) n) (hB : AsdimLE (d.restrict B) n) :
    AsdimLE (d.restrict (A ∪ B)) n := by
  intro s hs
  have hcA := coloredCover_of_asdimLE d (by omega : 1 ≤ 2 * s) hA
  have hcB : ∀ t : ℕ, ColoredCover d B t n := by
    intro t
    obtain ⟨I, piece, color, D, hc, hD, hsep⟩ :=
      coloredCover_of_asdimLE d (show 1 ≤ max 1 t from le_max_left _ _) hB
    refine ⟨I, piece, color, D, hc, hD, ?_⟩
    intro i j hij hne x hx y hy hxy
    exact hsep i j hij hne x hx y hy (d.mono (le_max_right _ _) hxy)
  exact scalePartition_of_coloredCover (d.restrict (A ∪ B))
    (coloredCover_restrict d (coloredCover_union d hcA hcB))

/-- Passing to a subspace cannot increase asymptotic dimension. -/
theorem asdimLE_subspace {A B : Set X} (hAB : A ⊆ B) {n : ℕ}
    (hB : AsdimLE (d.restrict B) n) : AsdimLE (d.restrict A) n := by
  let f : A → B := fun x => ⟨x.val, hAB x.property⟩
  have he : CoarseEmbedding (d.restrict A) (d.restrict B) f :=
    { a := 1
      b := 0
      forward := fun h => by simpa using h
      backward := fun h => by simpa using h }
  exact asdimLE_of_embedding _ _ he hB

theorem asdimLE_empty (n : ℕ) : AsdimLE (d.restrict (∅ : Set X)) n := by
  intro s hs
  refine ⟨(∅ : Set X), id, 0, ?_, ?_⟩
  · intro x y hxy
    exact False.elim x.property
  · intro x
    exact False.elim x.property

/-- The finite-family version needed for all collision pairs in a fixed window. -/
theorem asdimLE_finite_union {I : Type*} (F : Finset I) (A : I → Set X) (n : ℕ)
    (h : ∀ i ∈ F, AsdimLE (d.restrict (A i)) n) :
    AsdimLE (d.restrict (⋃ i ∈ F, A i)) n := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      have he : (⋃ i ∈ (∅ : Finset I), A i) = ∅ := by ext x; simp
      rw [he]
      exact asdimLE_empty d n
  | @insert i F hi ih =>
      have hAi := h i (Finset.mem_insert_self i F)
      have hF := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have he : (⋃ j ∈ insert i F, A j) = A i ∪ (⋃ j ∈ F, A j) := by ext x; simp
      rw [he]
      exact asdimLE_union d hAi hF

end FiniteAsdim
