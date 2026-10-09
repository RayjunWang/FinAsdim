import FiniteAsdim.Algebra
import FiniteAsdim.FiniteWindow
import FiniteAsdim.GraphColoring
import Mathlib.Algebra.Group.Action.Basic

namespace FiniteAsdim

private lemma finite_cube_set (r R : ℕ) : {v : Lattice r | InCube R v}.Finite :=
  by
    letI : Finite {v : Lattice r // v ∈ {v | InCube R v}} := cubeFinite r R
    exact Set.toFinite _

private lemma finite_lattice_bound {r : ℕ} (P : AddSubmonoid (Lattice r)) (F : Finset P) :
    ∃ R : ℕ, ∀ m ∈ F, InCube R m.val := by
  classical
  let f : P → ℕ := fun m => (Finset.univ : Finset (Fin r)).sup (fun i => (m.val i).natAbs)
  refine ⟨F.sup f, ?_⟩
  intro m hm i
  have hh : (m.val i).natAbs ≤ F.sup f :=
    (Finset.le_sup (f := fun j : Fin r => (m.val j).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := f) hm)
  rw [← Int.natCast_natAbs]
  exact Int.ofNat_le.mpr hh

/-- Lemma 6.2: finite-pattern compression for a bounded-to-one lattice monoid action.
The count concerns monoid elements, before applying them to `x`. -/
theorem finite_pattern_compression {r : ℕ} (P : AddSubmonoid (Lattice r))
    (hgen : AddSubgroup.closure (P : Set (Lattice r)) = ⊤)
    {X : Type*} [AddAction P X]
    (hbounded : ∀ p : P, ∃ k : ℕ, ∀ y : X,
      ((fun x : X => p +ᵥ x) ⁻¹' {y}).encard ≤ (k : ℕ∞)) (F : Finset P) :
    ∃ K L : Finset P, ∃ lambda : X → P,
      (∀ y, lambda y ∈ L) ∧
      (∀ x : X, (K : Set P).InjOn (fun p => p +ᵥ x) →
        (F.image (fun m => m + lambda (m +ᵥ x))).card ≤ 3 ^ r) := by
  classical
  obtain ⟨R, hF⟩ := finite_lattice_bound P F
  obtain ⟨a, ha, hapos⟩ := finite_set_translates P hgen
    {v | InCube (2 * R) v} (finite_cube_set r (2 * R))
  let aP : P := ⟨a, ha⟩
  let p : Cube r (2 * R) → P := fun v => ⟨a + v.val, hapos v.val v.property⟩
  let f : Cube r (2 * R) → X → X := fun _ x => aP +ᵥ x
  let g : Cube r (2 * R) → X → X := fun v x => p v +ᵥ x
  obtain ⟨q, hq, c, hc⟩ := fiber_pair_graph_coloring f g
    (fun _ => hbounded aP) (fun v => hbounded (p v))
  let V := R + windowRadius R q
  obtain ⟨b, hb, hbpos⟩ := finite_set_translates P hgen
    ((fun v : Lattice r => v - a) '' {v | InCube V v})
    ((finite_cube_set r V).image _)
  have hbminus : ∀ v, InCube V v → b + v - a ∈ P := by
    intro v hv
    have hh := hbpos (v - a) ⟨v, hv, rfl⟩
    simpa [add_sub_assoc] using hh
  have hbplus : ∀ v, InCube V v → b + v ∈ P := by
    intro v hv
    have hh := P.add_mem ha (hbminus v hv)
    have heq : a + (b + v - a) = b + v := by abel
    rwa [heq] at hh
  have hW : 2 * R ≤ windowRadius R q := by
    dsimp [windowRadius]
    simpa using Nat.mul_le_mul_left (2 * R) (show 1 ≤ q + 1 by omega)
  have h2RV : 2 * R ≤ V := hW.trans (Nat.le_add_left _ _)
  have h3RV : 3 * R ≤ V := by
    dsimp [V]
    omega
  have hWV : windowRadius R q ≤ V := Nat.le_add_left _ _
  let windowP : Cube r V → P := fun v => ⟨b + v.val, hbplus v.val v.property⟩
  let smallP : Cube r (2 * R) → P := fun v =>
    ⟨b + v.val, hbplus v.val (inCube_mono h2RV v.property)⟩
  let pattern (y : X) : Cube r (windowRadius R q) → Fin q := fun v =>
    c ((⟨b + v.val, hbplus v.val (inCube_mono hWV v.property)⟩ : P) +ᵥ y)
  let lambda : X → P := fun y => smallP (latticeRule hq (pattern y))
  let K : Finset P := Finset.univ.image windowP
  let L : Finset P := Finset.univ.image smallP
  refine ⟨K, L, lambda, ?_, ?_⟩
  · intro y
    exact Finset.mem_image.mpr ⟨latticeRule hq (pattern y), Finset.mem_univ _, rfl⟩
  intro x hx
  let cx : Lattice r → Fin q := fun v =>
    if h : b + v ∈ P then c ((⟨b + v, h⟩ : P) +ᵥ x) else ⟨0, hq⟩
  have hcx : ∀ v, InCube (3 * R) v → ∀ w, InCube (3 * R) w →
      latticeAdj R v w → cx v ≠ cx w := by
    intro v hv w hw hadj
    have hvV := inCube_mono h3RV hv
    have hwV := inCube_mono h3RV hw
    let pv : P := ⟨b + v, hbplus v hvV⟩
    let pw : P := ⟨b + w, hbplus w hwV⟩
    have hkv : pv ∈ K := Finset.mem_image.mpr ⟨⟨v, hvV⟩, Finset.mem_univ _, rfl⟩
    have hkw : pw ∈ K := Finset.mem_image.mpr ⟨⟨w, hwV⟩, Finset.mem_univ _, rfl⟩
    have hne : pv +ᵥ x ≠ pw +ᵥ x := by
      intro heq
      have helem := congrArg Subtype.val (hx hkv hkw heq)
      apply hadj.1
      exact add_left_cancel helem
    let i : Cube r (2 * R) := ⟨w - v, fun j => by simpa [abs_sub_comm] using hadj.2 j⟩
    let z : X := (⟨b + v - a, hbminus v hvV⟩ : P) +ᵥ x
    have hf : f i z = pv +ᵥ x := by
      dsimp [f, z]
      rw [← add_vadd]
      congr 1
      apply Subtype.ext
      dsimp [aP, pv]
      abel
    have hg : g i z = pw +ᵥ x := by
      dsimp [g, z]
      rw [← add_vadd]
      congr 1
      apply Subtype.ext
      dsimp [p, pw, i]
      abel
    have hh := hc (pv +ᵥ x) (pw +ᵥ x) ⟨hne, i, z, Or.inl ⟨hf, hg⟩⟩
    simpa [cx, hbplus v hvV, hbplus w hwV, pv, pw] using hh
  have hcompression := finite_window_local_rule hq cx hcx
  have hpattern : ∀ m ∈ F, pattern (m +ᵥ x) =
      (fun v : Cube r (windowRadius R q) => cx (m.val + v.val)) := by
    intro m hm
    funext v
    have hmV : InCube V (m.val + v.val) := inCube_add (hF m hm) v.property
    have hpos := hbplus (m.val + v.val) hmV
    dsimp [pattern, cx]
    rw [dif_pos hpos]
    congr 1
    rw [← add_vadd]
    congr 1
    apply Subtype.ext
    change b + v.val + m.val = b + (m.val + v.val)
    abel
  have heq : ∀ m ∈ F, (m + lambda (m +ᵥ x)).val =
      b + latticeMarker (R := R) hq cx m.val := by
    intro m hm
    dsimp [lambda, smallP, latticeMarker]
    rw [hpattern m hm]
    abel
  have hcard : (F.image (fun m => m + lambda (m +ᵥ x))).card ≤
      ((Finset.univ : Finset (Cube r R)).image
        (fun v => b + latticeMarker (R := R) hq cx v.val)).card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · rintro y hy
      rcases Finset.mem_image.mp hy with ⟨m, hm, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨m.val, hF m hm⟩, Finset.mem_univ _, (heq m hm).symm⟩
    · intro y _ z _ hyz
      exact Subtype.ext hyz
  have htrans : ((Finset.univ : Finset (Cube r R)).image
      (fun v => b + latticeMarker (R := R) hq cx v.val)).card =
      ((Finset.univ : Finset (Cube r R)).image
        (fun v => latticeMarker (R := R) hq cx v.val)).card := by
    change ((Finset.univ : Finset (Cube r R)).image
      ((fun z : Lattice r => b + z) ∘ (fun v => latticeMarker (R := R) hq cx v.val))).card = _
    rw [← Finset.image_image]
    exact Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)
  exact hcard.trans (htrans ▸ hcompression)

end FiniteAsdim



