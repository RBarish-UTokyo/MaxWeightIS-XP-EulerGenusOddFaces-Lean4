module

public import WeightedMIS.ExecutableAllHalf
public import WeightedMIS.RegisterWordFilter
public import WeightedMIS.GraphReachEncoded

/-!
# Encoded assembly of the all-half components

For each computed root the local output of the component solver is a list of
local vertex words; the words of the corresponding original vertices are read
off by walking the local range words and the component vertex words in
lockstep (`RegisterWordFilter.selectFilter`). The outputs of all roots are
collected by a left fold that prepends each reversed list, and the words of
the range that occur in the collection are exactly `setWords` of
`ExecutableReduction.allHalfSolve`. The component solver is the canonical-root
branch `halfSolve`, which is `connectedSolve` on every computed component.
-/

@[expose] public section

namespace WeightedMIS.AllHalfEncoded

open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterWordFilter
open WeightedMIS.ComputedComponents WeightedMIS.EmbeddingFaces

/-- The two fixed-width encodings of numbers agree. -/
theorem word_eq (W i : ℕ) : GraphReachEncoded.word W i = RibbonTable.word W i := rfl

theorem rangeWords_eq (W n : ℕ) :
    GraphReachEncoded.rangeWords W n = RibbonTable.rangeWords W n := by
  rw [GraphReachEncoded.rangeWords_eq_range]
  rfl

theorem setWords_length_le {W k : ℕ} (S : Finset (Fin k)) :
    (GraphReachEncoded.setWords W S).length ≤ k := by
  simpa [GraphReachEncoded.setWords] using List.length_filter_le _ (List.finRange k)

theorem mem_setWords {W k : ℕ} (hk : k < 2 ^ W) (S : Finset (Fin k)) (i : Fin k) :
    word W i.val ∈ GraphReachEncoded.setWords W S ↔ i ∈ S := by
  rw [GraphReachEncoded.setWords]
  change word W i.val ∈ ((List.finRange k).filter (· ∈ S)).map (fun v => word W v.val) ↔ _
  rw [mem_map_word hk]
  simp

/-! ## Reading local words back -/

theorem zip_range_map {β : Type*} {W : ℕ} {γ : Type*} (L : List γ) (f : γ → β) :
    (rangeWords W L.length).zip (L.map f) =
      (List.finRange L.length).map (fun i => (word W i.val, f (L.get i))) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zip]

/-- Membership in the words read back through a vertex list. -/
theorem mem_selectFilter {W n : ℕ} (hn : n < 2 ^ W) (L : List (Fin n)) (hL : L.length < 2 ^ W)
    (J : Finset (Fin L.length)) (v : Fin n) :
    word W v.val ∈ selectFilter (rangeWords W L.length) (L.map (fun u => word W u.val))
        (GraphReachEncoded.setWords W J) ↔ ∃ i ∈ J, L.get i = v := by
  rw [selectFilter, zip_range_map, List.filterMap_map, List.mem_filterMap]
  constructor
  · rintro ⟨i, -, hi⟩
    simp only [Function.comp_apply] at hi
    split_ifs at hi with hJ
    · simp only [Option.some.injEq] at hi
      exact ⟨i, (mem_setWords hL J i).mp hJ, (word_fin_inj hn).mp hi⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, List.mem_finRange i, ?_⟩
    simp [(mem_setWords hL J i).mpr hi]

theorem selectFilter_length_le {α : Type*} {W : ℕ} (rs : List (Bits W)) (ws : List α)
    (ks : List (Bits W)) : (selectFilter rs ws ks).length ≤ ws.length := by
  rw [selectFilter]
  exact (List.length_filterMap_le _ _).trans (by simp)

/-! ## Components -/

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The local weights of the component of `root`. -/
def localWeights (left right : Fin m → Fin n) (w : Fin n → ℚ) (root : Fin n) :
    Fin (vertices left right root).length → ℚ :=
  fun v => w (vertexEquiv left right root v).val

/-- The local solution of the component of `root`. -/
def localSolve (R : Ribbon left right) (w : Fin n → ℚ) (root : Fin n) :
    Finset (Fin (vertices left right root).length) :=
  ExecutableReduction.connectedSolve (componentRibbon left right root R)
    (localWeights left right w root)

/-- On a computed component the solver is the branch at the canonical root. -/
theorem localSolve_eq (R : Ribbon left right) (w : Fin n → ℚ) (root : Fin n) :
    localSolve R w root =
      ExecutableReduction.halfSolve (componentRibbon left right root R)
        (localWeights left right w root) ⟨0, vertices_length_pos left right root⟩ := by
  rw [localSolve, ExecutableReduction.connectedSolve,
    dite_eq_left_of_eq_true (eq_true (vertices_length_pos left right root))]

/-- Words of the original vertices selected in the component of `root`. -/
def globalWords (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (root : Fin n) :
    List (Bits W) :=
  selectFilter (rangeWords W (vertices left right root).length)
    ((vertices left right root).map (fun u => word W u.val))
    (GraphReachEncoded.setWords W (localSolve R w root))

theorem globalWords_length_le (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (root : Fin n) :
    (globalWords W R w root).length ≤ n := by
  refine (selectFilter_length_le _ _ _).trans ?_
  simpa using vertices_length_le left right root

theorem mem_globalWords {W : ℕ} (hn : n < 2 ^ W) (R : Ribbon left right) (w : Fin n → ℚ)
    (root v : Fin n) :
    word W v.val ∈ globalWords W R w root ↔
      ∃ i ∈ localSolve R w root, (vertexEquiv left right root i).val = v := by
  rw [globalWords, mem_selectFilter hn _ (lt_of_le_of_lt (vertices_length_le left right root) hn)]
  rfl

/-- The fold step: prepend the reversed words of one component. -/
def step (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (acc : List (Bits W)) (root : Fin n) :
    List (Bits W) :=
  (globalWords W R w root).reverse ++ acc

/-- The collected words of a list of roots. -/
def collect (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (roots : List (Fin n)) :
    List (Bits W) :=
  roots.foldl (step W R w) []

theorem mem_foldl_step (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (roots : List (Fin n))
    (acc : List (Bits W)) (x : Bits W) :
    x ∈ roots.foldl (step W R w) acc ↔ x ∈ acc ∨ ∃ r ∈ roots, x ∈ globalWords W R w r := by
  induction roots generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.mem_append, List.mem_reverse, List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_collect (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (roots : List (Fin n))
    (x : Bits W) :
    x ∈ collect W R w roots ↔ ∃ r ∈ roots, x ∈ globalWords W R w r := by
  rw [collect, mem_foldl_step]
  simp

theorem collect_length_le (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ)
    (roots : List (Fin n)) : (collect W R w roots).length ≤ n * roots.length := by
  have key : ∀ (rs : List (Fin n)) (acc : List (Bits W)),
      (rs.foldl (step W R w) acc).length ≤ acc.length + n * rs.length := by
    intro rs
    induction rs with
    | nil => simp
    | cons r rs ih =>
      intro acc
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      simp only [step, List.length_append, List.length_reverse, List.length_cons]
      have := globalWords_length_le W R w r
      nlinarith
  simpa [collect] using key roots []

/-- A vertex belongs to the assembled all-half output exactly when its word
is collected from the component of some computed root. -/
theorem mem_allHalfSolve_iff {W : ℕ} (hn : n < 2 ^ W) (R : Ribbon left right) (w : Fin n → ℚ)
    (v : Fin n) :
    v ∈ ExecutableReduction.allHalfSolve R w ↔ word W v.val ∈ collect W R w (roots left right) := by
  rw [mem_collect]
  simp only [ExecutableReduction.allHalfSolve, ComponentAssembly.assemble, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hfix := representative_idempotent left right v
  simp only [ExecutableReduction.fiberSolve, dite_eq_left_of_eq_true (eq_true hfix),
    GraphRelabeling.mem_mapSet]
  constructor
  · intro hv
    refine ⟨representative left right v, representative_mem_roots left right v, ?_⟩
    rw [mem_globalWords hn]
    refine ⟨_, hv, ?_⟩
    rw [← representativeFiberEquiv_val left right _ hfix, Equiv.apply_symm_apply]
  · rintro ⟨r, hr, hx⟩
    rw [mem_globalWords hn] at hx
    obtain ⟨i, hi, hiv⟩ := hx
    have hrep : representative left right v = r := by
      have hc := (vertexEquiv left right r i).property
      rw [hiv, Incidence.componentOf_eq_iff] at hc
      rw [representative_eq_of_reachable left right hc]
      exact (mem_roots left right r).mp hr
    subst hrep
    have he : (representativeFiberEquiv left right _ hfix).symm ⟨v, rfl⟩ = i := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext hiv.symm
    rw [he]
    exact hi

/-- The range words that occur in the collection are the words of the
assembled all-half output, in increasing order. -/
theorem filter_collect (W : ℕ) (hn : n < 2 ^ W) (R : Ribbon left right) (w : Fin n → ℚ) :
    (rangeWords W n).filter (fun x => decide (x ∈ collect W R w (roots left right))) =
      GraphReachEncoded.setWords W (ExecutableReduction.allHalfSolve R w) := by
  rw [← rangeWords_eq, GraphReachEncoded.filter_rangeWords, GraphReachEncoded.setWords]
  congr 1
  apply List.filter_congr
  intro v _
  rw [word_eq]
  exact decide_eq_decide.mpr (mem_allHalfSolve_iff hn R w v).symm

end WeightedMIS.AllHalfEncoded
