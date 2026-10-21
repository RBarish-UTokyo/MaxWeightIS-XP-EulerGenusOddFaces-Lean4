module

public import WeightedMIS.RegisterIncidenceRows
public import WeightedMIS.SignedWords

/-!
# Word-level support-cycle search and integer generators

Every orientation of an edge is stored as an arc word: its active flag, its
orientation bit, the edge index word, and the source and target states
`(sign, vertex word)` of the signed-stub construction. The arc words of all
edges are produced in numeric edge order, two per edge.

`searchW` follows first supported successors exactly as
`CycleSearch.search`, but keeps the already visited arcs in reverse order and
returns the repeated arc followed by the visited arcs after its first
occurrence. This list is a permutation of the cycle returned by
`DeterministicKernel.cycle`. The integer generator only depends on the edge
counts of that cycle, so the generator words computed from the permuted list
denote `DeterministicKernel.generator` exactly. All comparisons are the
binary comparator equality `eqb` and Boolean flag tests.
-/

@[expose] public section

namespace WeightedMIS.SupportCycleWords

open BinaryRational RationalWordRows RationalWidth EfficientSearch DeterministicKernel Walks
open RegisterIncidenceRows (eqb eqb_word)
open GraphReachEncoded (word)

/-- A state word: the sign bit followed by the vertex word. -/
abbrev StateW (W : ℕ) := Bits (W + 1)

/-- One oriented edge of the signed support graph; its key is the orientation
bit followed by the edge index word. -/
structure ArcW (W : ℕ) where
  active : Bool
  key : Bits (W + 1)
  source : StateW W
  target : StateW W

/-- An edge table entry: index word and the two endpoint words. -/
abbrev EdgeW (W : ℕ) := Bits W × (Bits W × Bits W)

variable {W N : ℕ}

/-! ## Reference functions -/

/-- The binary zero test of a stored rational. -/
def zeroW (q : BinaryRational.Word N) : Bool := (isZero q).1

/-- The sign `0 ≤ q`, robust against a negative zero. -/
def signW (q : BinaryRational.Word N) : Bool := !q.negative || zeroW q

def activeW (q : BinaryRational.Word N) : Bool := !zeroW q

/-- The two arcs of one edge with coordinate word `q`. -/
def arcPairW (q : BinaryRational.Word N) (t : EdgeW W) : ArcW W × ArcW W :=
  (⟨activeW q, .cons false t.1, .cons (!signW q) t.2.1, .cons (signW q) t.2.2⟩,
    ⟨activeW q, .cons true t.1, .cons (!signW q) t.2.2, .cons (signW q) t.2.1⟩)

def pairsW (xs : List (BinaryRational.Word N)) (table : List (EdgeW W)) :
    List (ArcW W × ArcW W) :=
  List.zipWith arcPairW xs table

def arcsW (pairs : List (ArcW W × ArcW W)) : List (ArcW W) := pairs.flatMap fun p => [p.1, p.2]

/-- Successor predicate: active and starting at the state `t`. -/
def succPred (t : StateW W) (b : ArcW W) : Bool := b.active && eqb b.source t

/-- Arc identity: equal keys (orientation and index word). -/
def samePred (a b : ArcW W) : Bool := eqb b.key a.key

/-- The leading bit of a nonempty word. -/
def headBit {k : ℕ} : Bits (k + 1) → Bool
  | .cons b _ => b

def succW (arcs : List (ArcW W)) (a : ArcW W) : ArcW W :=
  (arcs.find? (succPred a.target)).getD a

/-- Successor search with reversed visited arcs; the fuel is a list length. -/
def searchW (arcs : List (ArcW W)) : List (ArcW W) → ArcW W → List (ArcW W) → List (ArcW W)
  | [], _, _ => []
  | _ :: fuel, a, rs =>
      if (rs.find? (samePred a)).isSome then a :: rs.takeWhile (fun b => !samePred a b)
      else searchW arcs fuel (succW arcs a) (a :: rs)

def cycleW (arcs : List (ArcW W)) : List (ArcW W) :=
  match arcs.find? (fun a => a.active) with
  | none => []
  | some a => searchW arcs (a :: arcs) a []

/-- Generator word of one edge from cycle membership of its two arcs; the
constants are the magnitude words `(zero, one, two)`. -/
def genW (k : Bits N × Bits N × Bits N) (C : List (ArcW W)) (p : ArcW W × ArcW W) :
    RegisterPotentialStep.Word N :=
  (headBit p.1.source,
    if (C.find? (samePred p.1)).isSome then
      (if (C.find? (samePred p.2)).isSome then k.2.2 else k.2.1)
    else (if (C.find? (samePred p.2)).isSome then k.2.1 else k.1))

/-- A signed integer word viewed as a rational word with denominator `one`. -/
def ratW (one : Bits N) (g : RegisterPotentialStep.Word N) : BinaryRational.Word N :=
  ⟨g.1, g.2, one⟩

def pivotPred (pr : BinaryRational.Word N × BinaryRational.Word N) : Bool := !zeroW pr.2

/-- Word-level support decomposition, one round per fuel item. -/
def decomposeW {β : Type*} (k : Bits N × Bits N × Bits N) (table : List (EdgeW W)) :
    List β → List (BinaryRational.Word N) → List (List (RegisterPotentialStep.Word N))
  | [], _ => []
  | _ :: fuel, xs =>
      let pairs := pairsW xs table
      let gs := pairs.map (genW k (cycleW (arcsW pairs)))
      let gq := gs.map (ratW k.2.1)
      match (List.zipWith Prod.mk xs gq).find? pivotPred with
      | none => []
      | some pr => gs :: decomposeW k table fuel (scaleSubW (divide pr.1 pr.2).1 xs gq)

/-- Integer rows as signed words: each word denotes the coordinate. -/
def IntRowRep {m : ℕ} (l : List (RegisterPotentialStep.Word N)) (g : Fin m → ℤ) : Prop :=
  List.Forall₂ (fun w z => RegisterPotentialStep.value w = z) l (List.ofFn g)

/-! ## Word-level length facts -/

theorem searchW_length (arcs : List (ArcW W)) :
    ∀ (fuel : List (ArcW W)) (a : ArcW W) (rs : List (ArcW W)),
      (searchW arcs fuel a rs).length ≤ rs.length + fuel.length
  | [], _, _ => by simp [searchW]
  | _ :: fuel, a, rs => by
      unfold searchW
      split
      · have := (List.takeWhile_sublist (p := fun b => !samePred a b) (l := rs)).length_le
        simp only [List.length_cons]
        omega
      · have := searchW_length arcs fuel (succW arcs a) (a :: rs)
        simp only [List.length_cons] at this ⊢
        omega

theorem cycleW_length (arcs : List (ArcW W)) : (cycleW arcs).length ≤ arcs.length + 1 := by
  unfold cycleW
  split
  · simp
  · next a _ =>
    have := searchW_length arcs (a :: arcs) a []
    simpa using this

theorem arcsW_length (pairs : List (ArcW W × ArcW W)) :
    (arcsW pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p ps ih => simp [arcsW, List.flatMap_cons] at ih ⊢; omega

theorem pairsW_length (xs : List (BinaryRational.Word N)) (table : List (EdgeW W)) :
    (pairsW xs table).length = min xs.length table.length := by
  simp [pairsW]

/-! ## Generic search refinement -/

section Generic

variable {A : Type*} [DecidableEq A]

theorem search_nodup (next : A → A) :
    ∀ (fuel : ℕ) (a : A) (seen : List A), seen.Nodup →
      (CycleSearch.search next fuel a seen).Nodup
  | 0, _, _, _ => by simp [CycleSearch.search]
  | fuel + 1, a, seen, hs => by
      unfold CycleSearch.search
      split
      · exact hs.sublist (CycleSearch.cycleSuffix_sublist a seen)
      · next ha =>
        apply search_nodup next fuel
        simp only [List.nodup_append, hs, List.nodup_singleton, true_and, List.mem_singleton,
          forall_eq, ne_eq]
        intro b hb hba
        exact ha (hba ▸ hb)

theorem suffix_perm (a : A) (seen : List A) (hs : seen.Nodup) (ha : a ∈ seen) :
    (a :: seen.reverse.takeWhile (fun b => !decide (b = a))).Perm
      (CycleSearch.cycleSuffix a seen) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  have hnd := List.nodup_middle.mp hs
  have has : a ∉ s := fun h => (List.nodup_cons.mp hnd).1 (List.mem_append_left _ h)
  have hat : a ∉ t := fun h => (List.nodup_cons.mp hnd).1 (List.mem_append_right _ h)
  have hdrop : CycleSearch.cycleSuffix a (s ++ a :: t) = a :: t := by
    unfold CycleSearch.cycleSuffix
    rw [List.dropWhile_append_of_pos (fun b hb => by
      simpa using fun h : b = a => has (h ▸ hb))]
    simp
  have htake : (s ++ a :: t).reverse.takeWhile (fun b => !decide (b = a)) = t.reverse := by
    rw [List.reverse_append, List.reverse_cons, List.append_assoc,
      List.takeWhile_append_of_pos (fun b hb => by
        simpa using fun h : b = a => hat (h ▸ List.mem_reverse.mp hb))]
    simp
  rw [hdrop, htake]
  exact (List.reverse_perm t).cons a

/-- The word search with reversed visited arcs returns, up to the encoding,
a permutation of the cycle found by `CycleSearch.search`. -/
theorem searchW_perm (arcs : List (ArcW W)) (next : A → A) (enc : A → ArcW W)
    (hsame : ∀ a b, samePred (enc a) (enc b) = decide (b = a))
    (hsucc : ∀ a, succW arcs (enc a) = enc (next a)) :
    ∀ (fuel : List (ArcW W)) (a : A) (seen : List A), seen.Nodup →
      ∃ l : List A, searchW arcs fuel (enc a) (seen.reverse.map enc) = l.map enc ∧
        l.Perm (CycleSearch.search next fuel.length a seen)
  | [], _, _, _ => ⟨[], by simp [searchW, CycleSearch.search]⟩
  | _ :: fuel, a, seen, hs => by
      have hpred : (fun b => samePred (enc a) b) ∘ enc = fun b => decide (b = a) := by
        funext b
        exact hsame a b
      have hfind : ((seen.reverse.map enc).find? (samePred (enc a))).isSome =
          decide (a ∈ seen) := by
        rw [List.find?_map, Option.isSome_map]
        have hp : samePred (enc a) ∘ enc = fun b => decide (b = a) := hpred
        rw [hp]
        by_cases ha : a ∈ seen
        · simp only [ha, decide_true]
          exact List.find?_isSome.mpr ⟨a, List.mem_reverse.mpr ha, by simp⟩
        · simp only [ha, decide_false]
          rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
          apply List.find?_eq_none.mpr
          intro b hb
          simpa using fun h : b = a => ha (h ▸ List.mem_reverse.mp hb)
      simp only [List.length_cons]
      unfold searchW CycleSearch.search
      rw [hfind]
      by_cases ha : a ∈ seen
      · simp only [ha, decide_true, ↓reduceIte]
        refine ⟨a :: seen.reverse.takeWhile (fun b => !decide (b = a)), ?_,
          suffix_perm a seen hs ha⟩
        rw [List.takeWhile_map, List.map_cons]
        have hq : (fun b => !samePred (enc a) b) ∘ enc = fun b => !decide (b = a) := by
          funext b
          simp [hsame]
        rw [hq]
      · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hs' : (seen ++ [a]).Nodup := by
          simp only [List.nodup_append, hs, List.nodup_singleton, true_and, List.mem_singleton,
            forall_eq, ne_eq]
          intro b hb hba
          exact ha (hba ▸ hb)
        obtain ⟨l, hl, hp⟩ := searchW_perm arcs next enc hsame hsucc fuel (next a) (seen ++ [a]) hs'
        refine ⟨l, ?_, hp⟩
        rw [hsucc]
        simpa using hl

end Generic

/-! ## Encoding of the mathematical arcs -/

section Encoding

variable {n m : ℕ}

/-- Edge table: index word and endpoint words, in edge order. -/
def tableW (W : ℕ) (left right : Fin m → Fin n) : List (EdgeW W) :=
  List.ofFn fun e : Fin m => (word W e.val, (word W (left e).val, word W (right e).val))

theorem tableW_eq_zip (W : ℕ) (left right : Fin m → Fin n) :
    tableW W left right =
      List.zip (GraphReachEncoded.rangeWords W m) (GraphReachEncoded.edgeWords W left right) := by
  simp [tableW, GraphReachEncoded.rangeWords, GraphReachEncoded.edgeWords, List.ofFn_eq_map,
    List.zip_map']

def encState (W : ℕ) : State (Fin n) → StateW W
  | none => .cons false (word W 0)
  | some (v, s) => .cons s (word W v.val)

def arcEnc (W : ℕ) (left right : Fin m → Fin n) (x : Fin m → ℚ) (a : OrientedEdge m) :
    ArcW W :=
  ⟨active x a, .cons a.2 (word W a.1.val), encState W (DeterministicKernel.arcSource left right x a),
    encState W (DeterministicKernel.arcTarget left right x a)⟩

theorem arcSource_eq (left right : Fin m → Fin n) (x : Fin m → ℚ) (a : OrientedEdge m) :
    DeterministicKernel.arcSource left right x a =
      some (if a.2 then right a.1 else left a.1, !SparseKernel.rationalSign x a.1) := by
  rcases a with ⟨e, b⟩
  cases b <;>
    simp [DeterministicKernel.arcSource, Walks.source, liftArc, KernelBasis.columns, opposite]

theorem arcTarget_eq (left right : Fin m → Fin n) (x : Fin m → ℚ) (a : OrientedEdge m) :
    DeterministicKernel.arcTarget left right x a =
      some (if a.2 then left a.1 else right a.1, SparseKernel.rationalSign x a.1) := by
  rcases a with ⟨e, b⟩
  cases b <;> simp [DeterministicKernel.arcTarget, Walks.target, liftArc, KernelBasis.columns]

theorem bits_value_injective : ∀ {k : ℕ} (a b : Bits k), a.value = b.value → a = b
  | _, .nil, .nil, _ => rfl
  | _ + 1, .cons x t, .cons y u, h => by
    have ht := Bits.value_lt t
    have hu := Bits.value_lt u
    simp only [Bits.value] at h
    cases x <;> cases y <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h
    · rw [bits_value_injective t u h]
    · omega
    · omega
    · rw [bits_value_injective t u (by omega)]

theorem eqb_eq {k : ℕ} (a b : Bits k) : eqb a b = decide (a = b) := by
  unfold eqb
  rw [decide_eq_decide, (Bits.compare_correct a b).2.1]
  exact ⟨bits_value_injective a b, fun h => h ▸ rfl⟩

theorem samePred_enc (hm : m < 2 ^ W) (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (a b : OrientedEdge m) :
    samePred (arcEnc W left right x a) (arcEnc W left right x b) = decide (b = a) := by
  rcases a with ⟨e, o⟩
  rcases b with ⟨f, q⟩
  simp only [samePred, arcEnc, eqb_eq, Bits.cons.injEq, Prod.mk.injEq]
  have hw : word W f.val = word W e.val ↔ f = e :=
    ⟨fun h => GraphReachEncoded.word_injective hm h, fun h => h ▸ rfl⟩
  rw [decide_eq_decide, hw, and_comm]

theorem succPred_enc (hn : n < 2 ^ W) (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (a b : OrientedEdge m) :
    succPred (arcEnc W left right x a).target (arcEnc W left right x b) =
      (active x b && decide (DeterministicKernel.arcSource left right x b =
        DeterministicKernel.arcTarget left right x a)) := by
  simp only [succPred, arcEnc, eqb_eq, arcSource_eq, arcTarget_eq, encState, Bits.cons.injEq,
    Option.some.injEq, Prod.mk.injEq]
  congr 1
  have hw (v w : Fin n) : word W v.val = word W w.val ↔ v = w :=
    ⟨fun h => GraphReachEncoded.word_injective hn h, fun h => h ▸ rfl⟩
  rw [decide_eq_decide, hw, and_comm]

theorem arcsW_ofFn (left right : Fin m → Fin n) (x : Fin m → ℚ) :
    arcsW (List.ofFn fun e : Fin m =>
        (arcEnc W left right x (e, false), arcEnc W left right x (e, true))) =
      (arcList m).map (arcEnc W left right x) := by
  simp [arcsW, arcList, List.ofFn_eq_map, List.flatMap_map, List.map_flatMap]

theorem succW_enc (hn : n < 2 ^ W) (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (a : OrientedEdge m) :
    succW ((arcList m).map (arcEnc W left right x)) (arcEnc W left right x a) =
      arcEnc W left right x (CycleSearch.successor (DeterministicKernel.arcSource left right x)
        (DeterministicKernel.arcTarget left right x) (active x) (arcList m) a) := by
  unfold succW CycleSearch.successor
  rw [List.find?_map]
  have hp : succPred (arcEnc W left right x a).target ∘ arcEnc W left right x =
      fun b => active x b && decide (DeterministicKernel.arcSource left right x b =
        DeterministicKernel.arcTarget left right x a) := by
    funext b
    exact succPred_enc hn left right x a b
  rw [hp, Option.getD_map]

/-- The word cycle is, up to the encoding, a permutation of the actual cycle. -/
theorem cycleW_perm (hn : n < 2 ^ W) (hm : m < 2 ^ W) (left right : Fin m → Fin n)
    (x : Fin m → ℚ) :
    ∃ l : List (OrientedEdge m),
      cycleW ((arcList m).map (arcEnc W left right x)) = l.map (arcEnc W left right x) ∧
        l.Perm (cycle left right x) := by
  unfold cycleW cycle
  rw [List.find?_map]
  have hp : (fun a : ArcW W => a.active) ∘ arcEnc W left right x = active x := rfl
  rw [hp]
  rcases hf : (arcList m).find? (active x) with _ | a
  · exact ⟨[], by simp⟩
  · simp only [Option.map_some]
    obtain ⟨l, hl, hperm⟩ := searchW_perm ((arcList m).map (arcEnc W left right x))
      (CycleSearch.successor (DeterministicKernel.arcSource left right x)
        (DeterministicKernel.arcTarget left right x) (active x)
        (arcList m)) (arcEnc W left right x) (samePred_enc hm left right x)
      (succW_enc hn left right x) (arcEnc W left right x a :: (arcList m).map
        (arcEnc W left right x)) a [] List.nodup_nil
    refine ⟨l, by simpa using hl, ?_⟩
    simpa [CycleSearch.findCycle] using hperm

theorem cycle_nodup (left right : Fin m → Fin n) (x : Fin m → ℚ) :
    (cycle left right x).Nodup := by
  unfold cycle
  split
  · exact List.nodup_nil
  · exact search_nodup _ _ _ _ List.nodup_nil

/-- In a list of distinct arcs, an edge occurs once per present orientation. -/
theorem count_fst (l : List (OrientedEdge m)) (hl : l.Nodup) (e : Fin m) :
    (l.map Prod.fst).count e =
      (if (e, false) ∈ l then 1 else 0) + (if (e, true) ∈ l then 1 else 0) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    obtain ⟨hb, hl'⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.count_cons, ih hl']
    rcases b with ⟨f, o⟩
    by_cases hf : f = e
    · subst hf
      cases o
      · have : (f, false) ∉ l := hb
        simp [this]
        try omega
      · have : (f, true) ∉ l := hb
        simp [this]
        try omega
    · have h1 : (e, false) ≠ (f, o) := fun h => hf (congrArg Prod.fst h).symm
      have h2 : (e, true) ≠ (f, o) := fun h => hf (congrArg Prod.fst h).symm
      simp [hf, h1, h2]

theorem generator_eq (left right : Fin m → Fin n) (x : Fin m → ℚ) (e : Fin m) :
    generator left right x e = signValue (SparseKernel.rationalSign x e) *
      ((if (e, false) ∈ cycle left right x then 1 else 0) +
        (if (e, true) ∈ cycle left right x then 1 else 0) : ℕ) := by
  unfold generator
  rw [count_fst _ (cycle_nodup left right x) e]

theorem generator_abs_le (left right : Fin m → Fin n) (x : Fin m → ℚ) (e : Fin m) :
    |generator left right x e| ≤ 2 := by
  rw [generator_eq]
  cases SparseKernel.rationalSign x e <;> split_ifs <;> simp [signValue]

theorem find_samePred (hm : m < 2 ^ W) (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (l : List (OrientedEdge m)) (a : OrientedEdge m) :
    ((l.map (arcEnc W left right x)).find? (samePred (arcEnc W left right x a))).isSome =
      decide (a ∈ l) := by
  rw [List.find?_map, Option.isSome_map]
  have hp : samePred (arcEnc W left right x a) ∘ arcEnc W left right x =
      fun b => decide (b = a) := by
    funext b
    exact samePred_enc hm left right x a b
  rw [hp]
  by_cases ha : a ∈ l
  · simp only [ha, decide_true]
    exact List.find?_isSome.mpr ⟨a, ha, by simp⟩
  · simp only [ha, decide_false]
    rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    apply List.find?_eq_none.mpr
    intro b hb
    simpa using fun h : b = a => ha (h ▸ hb)

theorem signed_not (s : Bool) (c : ℕ) :
    BinaryRational.signed (!s) c = signValue s * (c : ℤ) := by
  cases s <;> simp [BinaryRational.signed, signValue]

/-- The generator word of every edge denotes the actual integer generator. -/
theorem genW_value (hn : n < 2 ^ W) (hm : m < 2 ^ W) (left right : Fin m → Fin n)
    (x : Fin m → ℚ) (k : Bits N × Bits N × Bits N)
    (hk : k.1.value = 0 ∧ k.2.1.value = 1 ∧ k.2.2.value = 2) (e : Fin m) :
    RegisterPotentialStep.value (genW k (cycleW ((arcList m).map (arcEnc W left right x)))
      (arcEnc W left right x (e, false), arcEnc W left right x (e, true))) =
      generator left right x e := by
  obtain ⟨l, hl, hperm⟩ := cycleW_perm hn hm left right x
  rw [hl, generator_eq]
  have hmem (a : OrientedEdge m) : a ∈ cycle left right x ↔ a ∈ l := hperm.mem_iff.symm
  simp only [genW]
  rw [find_samePred hm, find_samePred hm]
  simp only [RegisterPotentialStep.value, arcEnc, arcSource_eq, encState, hmem, headBit]
  rw [signed_not]
  congr 2
  by_cases h0 : (e, false) ∈ l <;> by_cases h1 : (e, true) ∈ l <;> simp [h0, h1, hk]

end Encoding

end WeightedMIS.SupportCycleWords
