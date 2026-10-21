module

public import WeightedMIS.RegisterAdjacencyTable
public import WeightedMIS.RegisterPotentialStep

/-!
# Word-level parity search and the computed odd row

The parity double cover is searched by the generic word-level residual search
on a table built by `RegisterAdjacencyTable.tableW` from parity edge records:
each edge record `((l, r), i)` gives the two records `((l⁰, r¹), i)` and
`((l¹, r⁰), i)`, where the superscript is the leading parity bit. The table is
the filtered product of the parity vertices in the order of
`ComputedOddRow.parityNodes`, so the stored reverse route of the odd copy of
the root is exactly the reversed route of `ComputedOddRow.paritySearch`.

The odd row is then recomputed from the stored route arcs: for every edge
index word, a left fold over the route arcs looks up the first edge joining
the two underlying vertex words and, when that edge carries the index word,
adds the signed unit given by the parity bit of the arc source. The result
has value `ComputedOddRow.oddRow`.
-/

@[expose] public section

namespace WeightedMIS.ParityReachRefinement

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords WeightedMIS.RegisterPotentialStep
open WeightedMIS.GraphReachEncoded WeightedMIS.RegisterFirstEdge
open WeightedMIS.RegisterIncidenceRows (eqb eqb_word)
open WeightedMIS.ResidualCrossingRefinement (encodeArc)

variable {W K G : ℕ}

/-! ## Word helpers -/

theorem eqb_iff (a b : Bits W) : eqb a b = decide (a = b) := by
  unfold eqb
  apply decide_eq_decide.mpr
  rw [(Bits.compare_correct a b).2.1]
  exact ⟨fun h => ResidualListReach.bits_value_inj h, fun h => h ▸ rfl⟩

/-- The leading (parity) bit of a parity word. -/
def lead : Bits (W + 1) → Bool
  | .cons b _ => b

/-- The underlying vertex word of a parity word. -/
def base : Bits (W + 1) → Bits W
  | .cons _ v => v

@[simp] theorem lead_parityWord (b : Bool) (v : Bits W) : lead (parityWord b v) = b := rfl

@[simp] theorem base_parityWord (b : Bool) (v : Bits W) : base (parityWord b v) = v := rfl

/-! ## Parity records and the parity table -/

/-- The two parity records of an edge record. -/
def parityPair (r : Record W K) : List (Record (W + 1) K) :=
  [((parityWord false r.1.1, parityWord true r.1.2), r.2),
   ((parityWord true r.1.1, parityWord false r.1.2), r.2)]

def parityRecords (recs : List (Record W K)) : List (Record (W + 1) K) :=
  recs.flatMap parityPair

/-- The parity search table built from the parity records. -/
def parityTableW (recs : List (Record W K)) (nodes : List (Bits W)) : List (Arc (W + 1) 1) :=
  RegisterAdjacencyTable.tableW one (parityRecords recs) (parityNodeWords nodes)

theorem tableW_map {V : Type*} (one' : Bits 1) (recs : List (Record W K)) (enc : V → Bits W)
    (l : List V) :
    RegisterAdjacencyTable.tableW one' recs (l.map enc) =
      ((l.product l).filter (fun a => (recs.find? (pred (enc a.1, enc a.2))).isSome)).map
        (encodeArc enc (fun _ _ => one')) := by
  unfold RegisterAdjacencyTable.tableW List.product
  rw [List.filter_flatMap, List.map_flatMap, List.flatMap_map]
  congr 1
  funext u
  rw [List.flatMap_map, RegisterAdjacencyTable.filter_map_eq_flatMap, List.flatMap_map]
  congr 1

section Graph

variable {n m : ℕ} (left right : Fin m → Fin n)

theorem parityNodeWords_eq (W : ℕ) :
    parityNodeWords (rangeWords W n) =
      (ComputedOddRow.parityNodes (List.finRange n)).map (parityEnc W) := by
  unfold parityNodeWords rangeWords ComputedOddRow.parityNodes List.product
  rw [List.flatMap_map, List.map_flatMap]
  rfl

theorem eqb_parity (hn : n < 2 ^ W) (x y : Bool) (u v : Fin n) :
    eqb (parityWord x (word W u.val)) (parityWord y (word W v.val)) = decide (x = y ∧ u = v) := by
  rw [eqb_iff]
  apply decide_eq_decide.mpr
  rw [parityWord_eq_iff, word_eq_iff hn]

theorem any_parityPair (hn : n < 2 ^ W) (yw : Fin m → Bits K) (e : Fin m)
    (a c : Fin n × Bool) :
    (parityPair (((word W (left e).val, word W (right e).val), yw e) : Record W K)).any
        (pred (parityEnc W a, parityEnc W c)) =
      decide (((left e = a.1 ∧ right e = c.1) ∨ (left e = c.1 ∧ right e = a.1)) ∧
        c.2 = !a.2) := by
  obtain ⟨u, b⟩ := a
  obtain ⟨v, d⟩ := c
  simp only [parityPair, List.any_cons, List.any_nil, pred, matchW_eq, parityEnc,
    eqb_parity hn, Bool.or_false]
  cases b <;> cases d <;> simp [Bool.or_comm]

theorem parity_isSome (hn : n < 2 ^ W) (yw : Fin m → Bits K) (a c : Fin n × Bool) :
    ((parityRecords (records W left right yw)).find? (pred (parityEnc W a, parityEnc W c))).isSome =
      decide (ComputedOddRow.AdjacentParity left right (List.finRange m) a c) := by
  rw [List.isSome_find?, parityRecords, List.any_flatMap, records, List.any_map]
  simp only [ComputedOddRow.AdjacentParity, GraphSearch.Adjacent, GraphSearch.edgeBetween,
    List.isSome_find?, Function.comp_def, any_parityPair left right hn]
  by_cases hc : c.2 = !a.2
  · apply Bool.eq_iff_iff.mpr
    simp [hc, List.any_eq_true]
  · simp [hc]

/-- The parity relation of the graph. -/
abbrev rel : Fin n × Bool → Fin n × Bool → Prop :=
  ComputedOddRow.AdjacentParity left right (List.finRange m)

theorem parityTable_eq (hn : n < 2 ^ W) (yw : Fin m → Bits K) :
    parityTableW (records W left right yw) (rangeWords W n) =
      (((ComputedOddRow.parityNodes (List.finRange n)).product
          (ComputedOddRow.parityNodes (List.finRange n))).filter
        (fun a => decide (rel left right a.1 a.2))).map
        (encodeArc (parityEnc W) (fun _ _ => one)) := by
  rw [parityTableW, parityNodeWords_eq, tableW_map]
  congr 1
  apply List.filter_congr
  intro a _
  exact parity_isSome left right hn yw a.1 a.2

theorem parityEnc_value_injective (hn : n < 2 ^ W) :
    Function.Injective (fun a : Fin n × Bool => (parityEnc W a).value) :=
  fun _ _ h => parityEnc_injective hn (ResidualListReach.bits_value_inj h)

theorem parity_crossing (hn : n < 2 ^ W) (yw : Fin m → Bits K) (seen : List (Fin n × Bool)) :
    RegisterResidualCrossing.crossing (seen.map (parityEnc W)) one
        (parityTableW (records W left right yw) (rangeWords W n)) =
      (MaxFlowReach.crossing (rel left right) (ComputedOddRow.parityNodes (List.finRange n))
        seen.toFinset).map (encodeArc (parityEnc W) (fun _ _ => one)) := by
  rw [parityTable_eq left right hn yw]
  exact ResidualReachGeneric.crossing_filter _ (parityEnc_value_injective hn) _ _ _ one
    (fun _ _ => le_refl _) seen

end Graph

/-! ## The word-level parity search -/

/-- The word-level search from the even copy of the root word. -/
def searchW (recs : List (Record W K)) (nodes : List (Bits W)) (root : Bits W) :
    ResidualListReach.State (W + 1) 1 :=
  ResidualListReach.explore (parityTableW recs nodes) one (parityNodeWords nodes).length
    (ResidualListReach.initial (parityWord false root))

section Search

variable {n m : ℕ} (left right : Fin m → Fin n)

theorem parityNodeWords_length (W : ℕ) :
    (parityNodeWords (rangeWords W n)).length = Fintype.card (Fin n × Bool) := by
  rw [parityNodeWords_eq]
  unfold ComputedOddRow.parityNodes List.product
  simp [List.length_flatMap]

theorem searchW_eq (hn : n < 2 ^ W) (yw : Fin m → Bits K) (root : Fin n) :
    searchW (records W left right yw) (rangeWords W n) (word W root.val) =
      ResidualListReach.encodeState (parityEnc W) one
        (MaxFlowListReach.explore (rel left right) (ComputedOddRow.parityNodes (List.finRange n))
          (Fintype.card (Fin n × Bool)) (MaxFlowListReach.initial (root, false))) := by
  rw [searchW, parityNodeWords_length]
  exact ResidualReachGeneric.explore_encoded_rel (parityEnc W) (parityEnc_value_injective hn)
    (rel left right) _ (fun _ _ => one) one _ (parity_crossing left right hn yw) _
    (MaxFlowListReach.initial (root, false))

/-- The stored reverse route of the odd root copy is the reversed parity route. -/
theorem parity_lookup (hn : n < 2 ^ W) (yw : Fin m → Bits K) (root : Fin n) :
    RegisterRouteLookup.lookup (parityWord true (word W root.val))
        (searchW (records W left right yw) (rangeWords W n) (word W root.val)).routes =
      ((ComputedOddRow.paritySearch left right (List.finRange m) (List.finRange n) root).route
        (root, true)).reverse.map (encodeArc (parityEnc W) (fun _ _ => one)) := by
  rw [searchW, parityNodeWords_length]
  exact ResidualReachGeneric.lookup_explore (parityEnc W) (parityEnc_value_injective hn)
    (rel left right) _ (fun _ _ => one) one _ (parity_crossing left right hn yw) _
    (root, false) (root, true)

theorem found_map {V : Type*} [DecidableEq V] {k : ℕ} (enc : V → Bits k)
    (hinj : Function.Injective (fun v => (enc v).value)) (x : V) (l : List V) :
    RegisterMembership.found (enc x) (l.map enc) = decide (x ∈ l) := by
  apply Bool.eq_iff_iff.mpr
  rw [RegisterMembership.found_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨key, hk, hv⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hk
    exact (hinj hv) ▸ hy
  · intro hx
    exact ⟨enc x, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- The membership flag of the odd root copy is the branch test of `halfSolve`. -/
theorem parity_found (hn : n < 2 ^ W) (yw : Fin m → Bits K) (root : Fin n) :
    RegisterMembership.found (parityWord true (word W root.val))
        (searchW (records W left right yw) (rangeWords W n) (word W root.val)).seen =
      decide ((root, true) ∈
        (ComputedOddRow.paritySearch left right (List.finRange m) (List.finRange n) root).seen) := by
  rw [searchW_eq left right hn yw root]
  change RegisterMembership.found (parityEnc W (root, true)) (List.map (parityEnc W) _) = _
  rw [found_map _ (parityEnc_value_injective hn)]
  have hd := MaxFlowListReach.explore_refines (rel left right)
    (ComputedOddRow.parityNodes (List.finRange n)) (Fintype.card (Fin n × Bool))
    (MaxFlowListReach.initial (root, false))
  rw [MaxFlowListReach.decode_initial] at hd
  have hs := congrArg MaxFlowReach.State.seen hd
  simp only [MaxFlowListReach.decode] at hs
  unfold ComputedOddRow.paritySearch
  rw [← hs]
  simp

theorem lookup_length (yw : Fin m → Bits K) (root : Fin n) (x : Bits (W + 1)) :
    (RegisterRouteLookup.lookup x
      (searchW (records W left right yw) (rangeWords W n) (word W root.val)).routes).length ≤
        2 * n := by
  have h := ResidualListReach.search_lookup_length
    (parityTableW (records W left right yw) (rangeWords W n)) one
    (parityNodeWords (rangeWords W n)) (parityWord false (word W root.val)) x
  rw [parityNodeWords_length] at h
  simpa [searchW, parityNodeWords_length, Nat.mul_comm] using h

end Search

/-! ## The row computed from the stored route -/

/-- One route arc: add the signed unit of the source parity when the first
edge joining the underlying vertex words carries the index word. -/
def stepW (recs : List (Record W K)) (idx : Bits K) (oneG : Bits G) (acc : Word G)
    (a : Arc (W + 1) 1) : Word G :=
  match recs.find? (pred (base a.source, base a.target)) with
  | some r => if eqb r.2 idx then (BinaryRational.signedAdd acc.1 (lead a.source) acc.2 oneG).1
      else acc
  | none => acc

def rowW (recs : List (Record W K)) (idx : Bits K) (oneG zero : Bits G)
    (route : List (Arc (W + 1) 1)) : Word G :=
  route.foldl (stepW recs idx oneG) (false, zero)

section Row

variable {n m : ℕ} (left right : Fin m → Fin n)

theorem row_append (l₁ l₂ : List ((Fin n × Bool) × (Fin n × Bool))) (e : Fin m) :
    ComputedOddRow.row left right (List.finRange m) (l₁ ++ l₂) e =
      ComputedOddRow.row left right (List.finRange m) l₁ e +
        ComputedOddRow.row left right (List.finRange m) l₂ e := by
  induction l₁ with
  | nil => simp [ComputedOddRow.row]
  | cons a l ih =>
    simp only [List.cons_append, ComputedOddRow.row, ih]
    ring

theorem row_reverse (l : List ((Fin n × Bool) × (Fin n × Bool))) (e : Fin m) :
    ComputedOddRow.row left right (List.finRange m) l.reverse e =
      ComputedOddRow.row left right (List.finRange m) l e := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, row_append, ih]
    simp only [ComputedOddRow.row]
    ring

/-- One step adds exactly the contribution of the arc to the row. -/
theorem stepW_value (hn : n < 2 ^ W) (hm : m < 2 ^ K) (oneG : Bits G) (hone : oneG.value = 1)
    (e : Fin m) (acc : Word G) (hacc : acc.2.value + 1 < 2 ^ G)
    (a : (Fin n × Bool) × (Fin n × Bool)) :
    value (stepW (records W left right (fun e => word K e.val)) (word K e.val) oneG acc
        (encodeArc (parityEnc W) (fun _ _ => one) a)) =
      value acc + ComputedOddRow.row left right (List.finRange m) [a] e := by
  obtain ⟨⟨u, b⟩, ⟨v, c⟩⟩ := a
  simp only [stepW, encodeArc, parityEnc, base_parityWord, lead_parityWord,
    find_records hn, ComputedOddRow.row, add_zero]
  cases he : GraphSearch.edgeBetween left right (List.finRange m) u v with
  | none => simp
  | some f =>
    simp only [Option.map_some, eqb_word hm, Option.some.injEq]
    by_cases hf : f = e
    · subst hf
      simp only [decide_true, ↓reduceIte]
      have hv := BinaryRational.signedAdd_value acc.1 b acc.2 oneG (by omega)
      unfold value
      rw [hv, hone]
      cases b <;> simp [BinaryRational.signed, ComputedOddRow.sign]
    · simp [hf]

theorem stepW_natAbs (hn : n < 2 ^ W) (hm : m < 2 ^ K) (oneG : Bits G) (hone : oneG.value = 1)
    (e : Fin m) (acc : Word G) (hacc : acc.2.value + 1 < 2 ^ G)
    (a : (Fin n × Bool) × (Fin n × Bool)) :
    (stepW (records W left right (fun e => word K e.val)) (word K e.val) oneG acc
        (encodeArc (parityEnc W) (fun _ _ => one) a)).2.value ≤ acc.2.value + 1 := by
  have h := stepW_value left right hn hm oneG hone e acc hacc a
  have hr := ComputedOddRow.row_natAbs_le left right (List.finRange m) [a] e
  rw [← value_natAbs, ← value_natAbs, h]
  simp only [List.length_singleton] at hr
  have := Int.natAbs_add_le (value acc) (ComputedOddRow.row left right (List.finRange m) [a] e)
  omega

theorem fold_value (hn : n < 2 ^ W) (hm : m < 2 ^ K) (oneG : Bits G) (hone : oneG.value = 1)
    (e : Fin m) (l : List ((Fin n × Bool) × (Fin n × Bool))) (acc : Word G)
    (hacc : acc.2.value + l.length < 2 ^ G) :
    value ((l.map (encodeArc (parityEnc W) (fun _ _ => one))).foldl
        (stepW (records W left right (fun e => word K e.val)) (word K e.val) oneG) acc) =
      value acc + ComputedOddRow.row left right (List.finRange m) l e := by
  induction l generalizing acc with
  | nil => simp [ComputedOddRow.row]
  | cons a l ih =>
    simp only [List.length_cons] at hacc
    simp only [List.map_cons, List.foldl_cons]
    have h1 := stepW_natAbs left right hn hm oneG hone e acc (by omega) a
    rw [ih _ (by omega), stepW_value left right hn hm oneG hone e acc (by omega) a]
    have hc : ComputedOddRow.row left right (List.finRange m) (a :: l) e =
        ComputedOddRow.row left right (List.finRange m) [a] e +
          ComputedOddRow.row left right (List.finRange m) l e := by
      simp only [ComputedOddRow.row]
      ring
    rw [hc]
    ring

/-- The row word of an edge index has the value of the computed odd row. -/
theorem rowW_value (hn : n < 2 ^ W) (hm : m < 2 ^ K) (hG : 2 * n < 2 ^ G) (oneG zero : Bits G)
    (hone : oneG.value = 1) (hzero : zero.value = 0) (root : Fin n) (e : Fin m) :
    value (rowW (records W left right (fun e => word K e.val)) (word K e.val) oneG zero
        (RegisterRouteLookup.lookup (parityWord true (word W root.val))
          (searchW (records W left right (fun e => word K e.val)) (rangeWords W n)
            (word W root.val)).routes)) =
      ComputedOddRow.oddRow left right (List.finRange m) (List.finRange n) root e := by
  have hlen := lookup_length left right (fun e => word K e.val) root
    (parityWord true (word W root.val))
  rw [parity_lookup left right hn] at hlen ⊢
  rw [List.length_map] at hlen
  unfold rowW
  rw [fold_value left right hn hm oneG hone e _ _ (by simp only [hzero]; omega), row_reverse]
  simp [value, BinaryRational.signed, hzero, ComputedOddRow.oddRow]

end Row

end WeightedMIS.ParityReachRefinement
