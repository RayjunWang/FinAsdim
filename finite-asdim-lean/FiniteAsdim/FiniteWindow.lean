import FiniteAsdim.LatticePacking

namespace FiniteAsdim

abbrev Lattice (r : ℕ) := Fin r → ℤ

def InCube {r : ℕ} (R : ℕ) (v : Lattice r) : Prop := ∀ i, |v i| ≤ (R : ℤ)

abbrev Cube (r R : ℕ) := {v : Lattice r // InCube R v}

lemma zero_inCube (r R : ℕ) : InCube R (0 : Lattice r) := by
  intro i
  simp

lemma inCube_mono {r R T : ℕ} {v : Lattice r} (hRT : R ≤ T)
    (hv : InCube R v) : InCube T v := by
  intro i
  exact (hv i).trans (Int.ofNat_le.mpr hRT)

lemma inCube_add {r R T : ℕ} {v w : Lattice r}
    (hv : InCube R v) (hw : InCube T w) : InCube (R + T) (v + w) := by
  intro i
  have hh := abs_add_le (v i) (w i)
  have hv' := hv i
  have hw' := hw i
  change |v i + w i| ≤ ((R + T : ℕ) : ℤ)
  push_cast
  omega

noncomputable instance cubeFinite (r R : ℕ) : Finite (Cube r R) := by
  let f : Cube r R → (Fin r → Fin (2 * R + 1)) := fun v i =>
    ⟨(v.val i + R).toNat, by
      have hv := (abs_le.mp (v.property i))
      omega⟩
  apply Finite.of_injective f
  intro v w h
  apply Subtype.ext
  funext i
  have hval := congrArg Fin.val (congrFun h i)
  have hv := abs_le.mp (v.property i)
  have hw := abs_le.mp (w.property i)
  dsimp [f] at hval
  omega

/-- Lattice graph used for selection; its edge radius is `2R`. -/
def latticeAdj {r : ℕ} (R : ℕ) (v w : Lattice r) : Prop :=
  v ≠ w ∧ ∀ i, |v i - w i| ≤ (2 * R : ℕ)

lemma latticeAdj_symm {r R : ℕ} (v w : Lattice r)
    (h : latticeAdj R v w) : latticeAdj R w v := by
  refine ⟨Ne.symm h.1, ?_⟩
  intro i
  simpa [abs_sub_comm] using h.2 i

/-- Selection at stage `n` is determined by the coloring in the `2Rn` window. -/
lemma greedy_lattice_local {r R q : ℕ} (c d : Lattice r → Fin q)
    (n : ℕ) (v : Lattice r)
    (hlocal : ∀ w, InCube (2 * R * n) (w - v) → c w = d w) :
    v ∈ greedySelected (latticeAdj R) c n ↔
      v ∈ greedySelected (latticeAdj R) d n := by
  induction n generalizing v with
  | zero => simp [greedySelected]
  | succ n ih =>
    have hc : c v = d v := by
      apply hlocal
      simpa using zero_inCube r (2 * R * (n + 1))
    have hold := ih v (fun w hw => hlocal w
      (inCube_mono (Nat.mul_le_mul_left (2 * R) (Nat.le_succ n)) hw))
    have hn : ∀ w, latticeAdj R v w →
        (w ∈ greedySelected (latticeAdj R) c n ↔
         w ∈ greedySelected (latticeAdj R) d n) := by
      intro w hadj
      apply ih
      intro z hz
      apply hlocal
      have hw : InCube (2 * R) (w - v) := by
        intro i
        simpa [abs_sub_comm] using hadj.2 i
      have hh := inCube_add hz hw
      have heq : z - w + (w - v) = z - v := by
        funext i
        change z i - w i + (w i - v i) = z i - v i
        omega
      rw [heq] at hh
      simpa [Nat.mul_add, Nat.mul_one] using hh
    change (_ ∨ ((c v).val = n ∧ ∀ w, latticeAdj R v w → _)) ↔
      (_ ∨ ((d v).val = n ∧ ∀ w, latticeAdj R v w → _))
    rw [hc, hold]
    constructor <;> intro h
    · rcases h with h | ⟨hcolor, hnone⟩
      · exact Or.inl h
      · exact Or.inr ⟨hcolor, fun w hw => (hn w hw).not.mp (hnone w hw)⟩
    · rcases h with h | ⟨hcolor, hnone⟩
      · exact Or.inl h
      · exact Or.inr ⟨hcolor, fun w hw => (hn w hw).not.mpr (hnone w hw)⟩

lemma greedySelected_equiv {V W : Type*} {q : ℕ}
    (e : V ≃ W) (adj : V → V → Prop) (adj' : W → W → Prop)
    (c : V → Fin q) (c' : W → Fin q)
    (hcolor : ∀ v, c v = c' (e v))
    (hadj : ∀ v w, adj v w ↔ adj' (e v) (e w))
    (n : ℕ) (v : V) :
    v ∈ greedySelected adj c n ↔ e v ∈ greedySelected adj' c' n := by
  induction n generalizing v with
  | zero => simp [greedySelected]
  | succ n ih =>
    change (_ ∨ ((c v).val = n ∧ ∀ w, adj v w → _)) ↔
      (_ ∨ ((c' (e v)).val = n ∧ ∀ w, adj' (e v) w → _))
    rw [ih, hcolor]
    constructor <;> intro h
    · rcases h with h | ⟨hc, hn⟩
      · exact Or.inl h
      · refine Or.inr ⟨hc, ?_⟩
        intro w hw hs
        have hadj' : adj v (e.symm w) := by
          apply (hadj v (e.symm w)).mpr
          simpa using hw
        apply hn (e.symm w) hadj'
        apply (ih (e.symm w)).mpr
        simpa using hs
    · rcases h with h | ⟨hc, hn⟩
      · exact Or.inl h
      · refine Or.inr ⟨hc, ?_⟩
        intro w hw hs
        exact hn (e w) ((hadj v w).mp hw) ((ih w).mp hs)

lemma latticeAdj_add {r R : ℕ} (g v w : Lattice r) :
    latticeAdj R v w ↔ latticeAdj R (g + v) (g + w) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro heq
      apply h.1
      exact add_left_cancel heq
    · intro i
      simpa using h.2 i
  · intro h
    refine ⟨?_, ?_⟩
    · intro heq
      apply h.1
      rw [heq]
    · intro i
      simpa using h.2 i

lemma greedySelected_translate {r R q : ℕ} (c : Lattice r → Fin q)
    (n : ℕ) (g v : Lattice r) :
    v ∈ greedySelected (latticeAdj R) (fun w => c (g + w)) n ↔
      g + v ∈ greedySelected (latticeAdj R) c n := by
  let e : Lattice r ≃ Lattice r :=
    ⟨fun w => g + w, fun w => w - g,
      fun w => by simp, fun w => by simp⟩
  exact greedySelected_equiv e (latticeAdj R) (latticeAdj R)
    (fun w => c (g + w)) c (fun _ => rfl) (latticeAdj_add g) n v

def windowRadius (R q : ℕ) := 2 * R * (q + 1)

noncomputable def extendPattern {r R q : ℕ} (hq : 0 < q)
    (pattern : Cube r (windowRadius R q) → Fin q) : Lattice r → Fin q := by
  classical
  exact fun v => if h : InCube (windowRadius R q) v then pattern ⟨v, h⟩ else ⟨0, hq⟩

/-- Choose a displacement using only the finite input pattern. -/
noncomputable def latticeRule {r R q : ℕ} (hq : 0 < q)
    (pattern : Cube r (windowRadius R q) → Fin q) : Cube r (2 * R) := by
  classical
  exact if h : ∃ v : Cube r (2 * R),
      v.val ∈ greedySelected (latticeAdj R) (extendPattern hq pattern) q
  then Classical.choose h
  else ⟨0, zero_inCube r (2 * R)⟩

lemma pattern_selection_local {r R q : ℕ} (hq : 0 < q)
    (c : Lattice r → Fin q) (v : Cube r (2 * R)) :
    v.val ∈ greedySelected (latticeAdj R)
      (extendPattern hq (fun w : Cube r (windowRadius R q) => c w.val)) q ↔
    v.val ∈ greedySelected (latticeAdj R) c q := by
  apply greedy_lattice_local
  intro w hw
  have hh := inCube_add hw v.property
  have heq : w - v.val + v.val = w := sub_add_cancel w v.val
  rw [heq] at hh
  have hwindow : InCube (windowRadius R q) w := by
    simpa [windowRadius, Nat.mul_add, Nat.mul_one] using hh
  simp [extendPattern, hwindow]

lemma latticeRule_selected {r R q : ℕ} (hq : 0 < q)
    (c : Lattice r → Fin q) :
    (latticeRule hq (fun w : Cube r (windowRadius R q) => c w.val)).val ∈
      greedySelected (latticeAdj R) c q := by
  have hex : ∃ v : Cube r (2 * R), v.val ∈ greedySelected (latticeAdj R) c q := by
    rcases greedySelected_dominates_processed (latticeAdj R) c q 0 (c 0).isLt with
      hzero | ⟨v, hadj, hsel⟩
    · exact ⟨⟨0, zero_inCube r (2 * R)⟩, hzero⟩
    · refine ⟨⟨v, ?_⟩, hsel⟩
      intro i
      simpa using hadj.2 i
  have hex' : ∃ v : Cube r (2 * R),
      v.val ∈ greedySelected (latticeAdj R)
        (extendPattern hq (fun w : Cube r (windowRadius R q) => c w.val)) q := by
    rcases hex with ⟨v, hv⟩
    exact ⟨v, (pattern_selection_local hq c v).mpr hv⟩
  unfold latticeRule
  rw [dif_pos hex']
  exact (pattern_selection_local hq c (Classical.choose hex')).mp
    (Classical.choose_spec hex')
noncomputable instance cubeFintype (r R : ℕ) : Fintype (Cube r R) := Fintype.ofFinite _

noncomputable def latticeMarker {r R q : ℕ} (hq : 0 < q)
    (c : Lattice r → Fin q) (g : Lattice r) : Lattice r :=
  g + (latticeRule hq (fun w : Cube r (windowRadius R q) => c (g + w.val))).val

lemma latticeMarker_selected {r R q : ℕ} (hq : 0 < q) (c : Lattice r → Fin q)
    (g : Lattice r) : latticeMarker (R := R) hq c g ∈
      greedySelected (latticeAdj R) c q := by
  unfold latticeMarker
  apply (greedySelected_translate c q g _).mp
  exact latticeRule_selected hq (fun w => c (g + w))

lemma latticeMarker_inCube {r R q : ℕ} (hq : 0 < q) (c : Lattice r → Fin q)
    (g : Cube r R) : InCube (3 * R) (latticeMarker (R := R) hq c g.val) := by
  unfold latticeMarker
  have hh := inCube_add g.property
    (latticeRule hq (fun w : Cube r (windowRadius R q) => c (g.val + w.val))).property
  have hR : R + 2 * R = 3 * R := by omega
  simpa [hR] using hh

/-- The complete finite-window rule of Lemma 6.1.
The input and output are literal finite lattice windows. The degree condition
from the paper is only needed to produce proper colors, so this version needs
only a positive number of colors. -/
theorem finite_window_lattice_rule (r R q : ℕ) (hq : 0 < q) :
    ∃ A : (Cube r (windowRadius R q) → Fin q) → Cube r (2 * R),
      ∀ c : Lattice r → Fin q,
        (∀ v w, latticeAdj R v w → c v ≠ c w) →
        ((Finset.univ : Finset (Cube r R)).image
          (fun g => g.val + (A (fun w => c (g.val + w.val))).val)).card ≤ 3 ^ r := by
  classical
  refine ⟨latticeRule hq, ?_⟩
  intro c hproper
  change ((Finset.univ : Finset (Cube r R)).image
    (fun g => latticeMarker (R := R) hq c g.val)).card ≤ 3 ^ r
  apply lattice_packing (R := (R : ℤ)) (by omega)
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨g, _, rfl⟩
    intro i
    have hh := abs_le.mp (latticeMarker_inCube hq c g i)
    simpa using hh
  · intro v hv w hw hclose
    rcases Finset.mem_image.mp hv with ⟨gv, _, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨gw, _, rfl⟩
    by_contra hne
    apply greedySelected_independent (latticeAdj R) c (latticeAdj_symm) hproper q
      (latticeMarker (R := R) hq c gv.val) (latticeMarker_selected hq c gv.val)
      (latticeMarker (R := R) hq c gw.val) (latticeMarker_selected hq c gw.val)
    exact ⟨hne, fun i => by simpa using hclose i⟩
/-- The same bound only needs proper colors on the cube containing the
chosen marker outputs; no extension of a partial proper coloring is needed. -/
theorem finite_window_local_rule {r R q : ℕ} (hq : 0 < q) (c : Lattice r → Fin q)
    (hproper : ∀ v, InCube (3 * R) v → ∀ w, InCube (3 * R) w →
      latticeAdj R v w → c v ≠ c w) :
    ((Finset.univ : Finset (Cube r R)).image
      (fun g => latticeMarker (R := R) hq c g.val)).card ≤ 3 ^ r := by
  classical
  apply lattice_packing (R := (R : ℤ)) (by omega)
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨g, _, rfl⟩
    intro i
    simpa using abs_le.mp (latticeMarker_inCube hq c g i)
  · intro v hv w hw hclose
    rcases Finset.mem_image.mp hv with ⟨gv, _, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨gw, _, rfl⟩
    by_contra hne
    apply greedySelected_independent_on (latticeAdj R) c {v | InCube (3 * R) v}
      latticeAdj_symm hproper q
      (latticeMarker (R := R) hq c gv.val) (latticeMarker_inCube hq c gv)
      (latticeMarker_selected hq c gv.val)
      (latticeMarker (R := R) hq c gw.val) (latticeMarker_inCube hq c gw)
      (latticeMarker_selected hq c gw.val)
    exact ⟨hne, fun i => by simpa using hclose i⟩
end FiniteAsdim






