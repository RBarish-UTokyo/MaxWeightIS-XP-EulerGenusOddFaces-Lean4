module

public import WeightedMIS.HardSolveReference
public import WeightedMIS.RegisterAdjacencyTable
public import WeightedMIS.RegisterResidualSearch
public import WeightedMIS.RegisterRootValue
public import WeightedMIS.RegisterThresholdVertices

/-!
# The compiled recovery stage of the hard-component solver

Inputs are the stored edge endpoint words of a graph, the stored vertex words
`rangeWords W n`, the root word, the stored signed coefficients `πw`, the
stored unsigned counts `yw` (all of the recovery width `B`), the unit word of
width one, and the unit and zero words of width `B`. The procedure

1. zips edges and counts into edge-count records,
2. builds the adjacency search table of all ordered adjacent pairs,
3. runs the compiled residual search from the root word with unit threshold,
   obtaining the stored reverse routes of `GraphSearch.search`,
4. computes the root value `(1 - Σ π e y e) / 2`,
5. keeps every vertex word whose route-propagated value is at least one.

The output is exactly the ascending word list of
`HardSolveReference.thresholdFrom left right root π y`, under explicit
hypotheses: injective vertex words (`n < 2 ^ W`), an even root numerator,
and one recovery width bound covering the dot product and every route
propagation. `width_of_bounds` derives the width bound from coefficient
bounds `|π e| < 2 n` (as given by `ComputedOddRow.oddRow_natAbs_lt`) and a
bound on the total count.
-/

@[expose] public section

namespace WeightedMIS.RegisterHardRecovery

open scoped BigOperators
open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.RegisterPotentialStep WeightedMIS.RegisterFirstEdge WeightedMIS.GraphReachEncoded
open WeightedMIS.RegisterIncidenceRows (EdgeAt)

variable {W B n m : ℕ}

/-! ## Reference data -/

/-- The stored reverse routes of the adjacency search from the root word. -/
def routesOf (W : ℕ) (left right : Fin m → Fin n) (root : Fin n) :
    List (RegisterRouteLookup.Route W 1) :=
  (ResidualListReach.explore (ResidualReachGeneric.adjTable left right W) one
    (rangeWords W n).length (ResidualListReach.initial (word W root.val))).routes

/-- The data passed to the vertex filter. -/
def dataOf (W : ℕ) (left right : Fin m → Fin n) (root : Fin n) (πw : Fin m → Word B)
    (yw : Fin m → Bits B) (oneB : Bits B) : RegisterThresholdVertices.Data W B :=
  ⟨routesOf W left right root, records W left right yw, Bits.zero B, oneB,
    RegisterRootValue.rootWord oneB ((List.finRange m).map πw) ((List.finRange m).map yw)⟩

/-- The integer coefficients and counts denoted by the stored words. -/
def coeffs (πw : Fin m → Word B) : Fin m → ℤ := fun e => value (πw e)

def counts (yw : Fin m → Bits B) : Fin m → ℤ := fun e => ((yw e).value : ℤ)

/-- The width bound used by the dot product and every route propagation. -/
def WidthFits (B n : ℕ) (πw : Fin m → Word B) (yw : Fin m → Bits B) : Prop :=
  1 + ∑ e, (πw e).2.value * (yw e).value + n * (1 + ∑ e, (yw e).value) < 2 ^ B

/-! ## Semantics -/

theorem sum_map_le {α : Type*} (l : List α) (f : α → ℕ) (Y : ℕ) (h : ∀ x ∈ l, f x ≤ Y) :
    (l.map f).sum ≤ l.length * Y := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := h a List.mem_cons_self
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem countOf_le (left right : Fin m → Fin n) (yw : Fin m → Bits B) (u v : Bits W) :
    (RegisterRouteCounts.countOf (Bits.zero B) (records W left right yw) u v).value ≤
      ∑ e, (yw e).value := by
  unfold RegisterRouteCounts.countOf
  cases hf : (records W left right yw).find? (pred (u, v)) with
  | none => simp
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hr
    simp only [Option.map_some, Option.getD_some]
    exact Finset.single_le_sum (f := fun e => (yw e).value) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ e)

/-- The refilled arc of an adjacent route pair carries the count of the first
joining edge. -/
theorem refill_carries (hn : n < 2 ^ W) (left right : Fin m → Fin n) (yw : Fin m → Bits B)
    (a : Fin n × Fin n) (ha : GraphSearch.Adjacent left right (List.finRange m) a.1 a.2) :
    HardSolveReference.Carries left right (List.finRange m) (counts yw)
      (RegisterRouteCounts.refill (Bits.zero B) (records W left right yw)
        (ResidualCrossingRefinement.encodeArc (fun v : Fin n => word W v.val)
          (fun _ _ => one) a)) a := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp ha
  refine ⟨e, he, ?_⟩
  simp only [RegisterRouteCounts.refill, RegisterRouteCounts.countOf,
    ResidualCrossingRefinement.encodeArc, find_records hn, he, Option.map_some,
    Option.getD_some, counts]

theorem route_eq (hn : n < 2 ^ W) (left right : Fin m → Fin n) (root : Fin n)
    (πw : Fin m → Word B) (yw : Fin m → Bits B) (oneB : Bits B) (v : Fin n) :
    RegisterThresholdVertices.route (dataOf W left right root πw yw oneB) (word W v.val) =
      (((GraphSearch.search left right (List.finRange m) (List.finRange n) root).route v).map
        (fun a => RegisterRouteCounts.refill (Bits.zero B) (records W left right yw)
          (ResidualCrossingRefinement.encodeArc (fun v : Fin n => word W v.val)
            (fun _ _ => one) a))).reverse := by
  unfold RegisterThresholdVertices.route dataOf routesOf
  simp only
  rw [ResidualReachGeneric.lookup_search left right hn root v, List.map_map, List.map_reverse]
  rfl

theorem rootWord_value (πw : Fin m → Word B) (yw : Fin m → Bits B) (oneB : Bits B)
    (hone : oneB.value = 1) (hfit : WidthFits B n πw yw)
    (heven : Even (HardSolveReference.rootNumerator (coeffs πw) (counts yw))) :
    value (RegisterRootValue.rootWord oneB ((List.finRange m).map πw) ((List.finRange m).map yw)) =
        ComputedRecovery.rootValue (coeffs πw) (counts yw) ∧
      (RegisterRootValue.rootWord oneB ((List.finRange m).map πw)
        ((List.finRange m).map yw)).2.value ≤ 1 + ∑ e, (πw e).2.value * (yw e).value := by
  have hnum : 1 - RegisterSignedDot.integerDot ((List.finRange m).map πw)
      ((List.finRange m).map yw) = HardSolveReference.rootNumerator (coeffs πw) (counts yw) := by
    rw [RegisterRootValue.integerDot_map]
    rfl
  have hmass := RegisterRootValue.mass_map πw yw
  unfold WidthFits at hfit
  obtain ⟨hv, hm⟩ := RegisterRootValue.rootWord_value oneB ((List.finRange m).map πw)
    ((List.finRange m).map yw) hone (by omega) (by rw [hnum]; exact heven)
  refine ⟨?_, by omega⟩
  rw [hv, hnum, HardSolveReference.rootValue_eq_div]

/-- The filter keeps a vertex word exactly when the vertex is in the threshold set. -/
theorem keep_word (hn : n < 2 ^ W) (left right : Fin m → Fin n) (root : Fin n)
    (πw : Fin m → Word B) (yw : Fin m → Bits B) (oneB : Bits B) (hone : oneB.value = 1)
    (hfit : WidthFits B n πw yw)
    (heven : Even (HardSolveReference.rootNumerator (coeffs πw) (counts yw))) (v : Fin n) :
    RegisterThresholdVertices.keep (dataOf W left right root πw yw oneB) (word W v.val) =
      decide (v ∈ HardSolveReference.thresholdFrom left right root (coeffs πw) (counts yw)) := by
  let d := dataOf W left right root πw yw oneB
  let route := (GraphSearch.search left right (List.finRange m) (List.finRange n) root).route v
  have hroute := route_eq hn left right root πw yw oneB v
  obtain ⟨hrv, hrm⟩ := rootWord_value πw yw oneB hone hfit heven
  -- the route length and the count mass
  have hlen : (RegisterThresholdVertices.route d (word W v.val)).length ≤ n := by
    have hl := ResidualListReach.search_lookup_length (ResidualReachGeneric.adjTable left right W)
      one (rangeWords W n) (word W root.val) (word W v.val)
    simpa [RegisterThresholdVertices.route, d, dataOf, routesOf, rangeWords] using hl
  have hcaps : ((RegisterThresholdVertices.route d (word W v.val)).map
      (fun a => a.capacity.value)).sum ≤ n * ∑ e, (yw e).value := by
    have hs := sum_map_le (RegisterThresholdVertices.route d (word W v.val))
      (fun a => a.capacity.value) (∑ e, (yw e).value) (by
        intro a ha
        simp only [RegisterThresholdVertices.route, List.mem_map] at ha
        obtain ⟨b, -, rfl⟩ := ha
        exact countOf_le left right yw _ _)
    exact hs.trans (Nat.mul_le_mul_right _ hlen)
  have hwidth : d.root.2.value + RegisterPotentialRoute.mass
      (RegisterThresholdVertices.route d (word W v.val)) < 2 ^ B := by
    unfold RegisterPotentialRoute.mass
    unfold WidthFits at hfit
    change (RegisterRootValue.rootWord oneB _ _).2.value + _ < _
    have : n * (1 + ∑ e, (yw e).value) = n + n * ∑ e, (yw e).value := by ring
    omega
  have hrec := (RegisterPotentialRoute.recover_correct d.one
    (RegisterThresholdVertices.route d (word W v.val)) d.root hone hwidth).1
  have hcarry : ∀ a ∈ route, HardSolveReference.Carries left right (List.finRange m) (counts yw)
      (RegisterRouteCounts.refill (Bits.zero B) (records W left right yw)
        (ResidualCrossingRefinement.encodeArc (fun v : Fin n => word W v.val)
          (fun _ _ => one) a)) a :=
    fun a ha => refill_carries hn left right yw a
      (ResidualReachGeneric.search_supported left right root v a ha)
  have hprop := HardSolveReference.propagate_map_reverse left right (List.finRange m) (counts yw)
    _ route hcarry (ComputedRecovery.rootValue (coeffs πw) (counts yw))
  have hval : value (RegisterThresholdVertices.final d (word W v.val)) =
      ComputedRecovery.recover left right (List.finRange m) (List.finRange n) root
        (coeffs πw) (counts yw) v := by
    unfold RegisterThresholdVertices.final
    rw [hrec]
    change RegisterPotentialRoute.propagate (RegisterThresholdVertices.route d (word W v.val))
      (value (RegisterRootValue.rootWord oneB _ _)) = _
    rw [hrv, hroute, hprop]
    rfl
  apply Bool.eq_iff_iff.mpr
  change RegisterThresholdVertices.positive oneB (RegisterThresholdVertices.final d (word W v.val))
    = true ↔ _
  rw [RegisterThresholdVertices.positive_iff _ _ hone, hval,
    decide_eq_true_iff, HardSolveReference.thresholdFrom, Slack.threshold]
  simp

theorem filter_eq (hn : n < 2 ^ W) (left right : Fin m → Fin n) (root : Fin n)
    (πw : Fin m → Word B) (yw : Fin m → Bits B) (oneB : Bits B) (hone : oneB.value = 1)
    (hfit : WidthFits B n πw yw)
    (heven : Even (HardSolveReference.rootNumerator (coeffs πw) (counts yw))) :
    (rangeWords W n).filter (RegisterThresholdVertices.keep (dataOf W left right root πw yw oneB)) =
      setWords W (HardSolveReference.thresholdFrom left right root (coeffs πw) (counts yw)) := by
  rw [filter_rangeWords, setWords]
  congr 1
  apply List.filter_congr
  intro v _
  exact keep_word hn left right root πw yw oneB hone hfit heven v

/-- Width bound from a coefficient bound `|π e| < 2 n` and a total count bound. -/
theorem width_of_bounds (πw : Fin m → Word B) (yw : Fin m → Bits B) (S : ℕ)
    (hπ : ∀ e, (value (πw e)).natAbs < 2 * n) (hS : ∑ e, (yw e).value ≤ S)
    (hB : (3 * n + 1) * (S + 1) < 2 ^ B) : WidthFits B n πw yw := by
  unfold WidthFits
  have h1 : ∑ e, (πw e).2.value * (yw e).value ≤ ∑ e, 2 * n * (yw e).value := by
    apply Finset.sum_le_sum
    intro e _
    have := hπ e
    rw [value_natAbs] at this
    exact Nat.mul_le_mul_right _ this.le
  rw [← Finset.mul_sum] at h1
  have h2 := Nat.mul_le_mul_left (2 * n) hS
  have h3 := Nat.mul_le_mul_left n hS
  have h4 : (3 * n + 1) * (S + 1) = 3 * n * S + 3 * n + S + 1 := by ring
  have h5 : 2 * n * S + n * S = 3 * n * S := by ring
  rw [Nat.mul_add n 1]
  omega

/-! ## Instantiation for the hard component -/

section Hard

variable {left right : Fin m → Fin n}

/-- Stored words denoting the actual odd row and the actual projected label
counts satisfy the evenness hypothesis, identify the output with
`ExecutableReduction.hardSolve`, and obey the coefficient and count bounds. -/
theorem hard_instance (R : EmbeddingFaces.Ribbon left right) (weights : Fin n → ℚ) (root : Fin n)
    (hc : Incidence.Connected left right) (hnb : ¬Incidence.Bipartite left right)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2))
    (πw : Fin m → Word B) (yw : Fin m → Bits B)
    (hπw : ∀ e, value (πw e) = ExecutableReduction.parityRow (left := left) (right := right) root e)
    (hyw : ∀ e, ((yw e).value : ℤ) = HardSolveReference.hardCounts R weights root e) :
    Even (HardSolveReference.rootNumerator (coeffs πw) (counts yw)) ∧
      HardSolveReference.thresholdFrom left right root (coeffs πw) (counts yw) =
        ExecutableReduction.hardSolve R weights root ∧
      (∀ e, (value (πw e)).natAbs < 2 * n) ∧
      ∑ e, (yw e).value = (ExecutableReduction.hardLabels R weights root).length := by
  have hπ : coeffs πw = ExecutableReduction.parityRow (left := left) (right := right) root :=
    funext hπw
  have hy : counts yw = HardSolveReference.hardCounts R weights root := funext hyw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hπ, hy, HardSolveReference.hardLabels_even R weights root hc hnb hw ho]
    exact even_two_mul _
  · rw [hπ, hy, HardSolveReference.hardSolve_eq]
  · intro e
    rw [hπw]
    have h := ComputedOddRow.oddRow_natAbs_lt left right (List.finRange m)
      (fun e => List.mem_finRange e) (List.finRange n) (fun v => List.mem_finRange v) root hc hnb e
    simpa [ExecutableReduction.parityRow] using h
  · rw [← HardSolveReference.projection_sum_eq_length]
    apply Finset.sum_congr rfl
    intro e _
    have h := hyw e
    simp only [HardSolveReference.hardCounts] at h
    exact_mod_cast h

end Hard

/-! ## Procedure -/

variable {p : ℕ}

/-- Arguments: edges, vertex words, root word, coefficients, counts, unit word of
width one, unit word, zero word. Result: the threshold vertex words. -/
def recoveryBody (zip table search root filter : Fin p) : Command p :=
  .call zip [.register 0, .register 4, .null] [8]
    (.call table [.register 1, .register 8, .register 5] [9]
      (.call search [.register 9, .register 5, .register 1, .register 2] [10, 11]
        (.call root [.register 3, .register 4, .register 7, .register 6] [12, 13]
          (.allocate 14 (.bit (.register 12) (.register 13))
            (.allocate 15 (.pair (.register 6) (.register 14))
              (.allocate 12 (.pair (.register 8) (.register 7))
                (.allocate 13 (.pair (.register 12) (.register 15))
                  (.allocate 14 (.pair (.register 11) (.register 13))
                    (.call filter [.register 1, .register 14] [15] (.ret [.register 15]))))))))))

structure Procedures (p : ℕ) where
  table : RegisterAdjacencyTable.Procedures p
  search : RegisterResidualSearch.Procedures p
  searchEntry : Fin p
  root : RegisterRootValue.Procedures p
  vertices : RegisterThresholdVertices.Procedures p
  self : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.table.Matches code ∧ d.search.Matches code ∧
  code d.searchEntry = RegisterResidualSearch.searchBody d.search.reach d.search.prepend ∧
  d.root.Matches code ∧ d.vertices.Matches code ∧
  code d.self = recoveryBody d.table.edge.zip d.table.self d.searchEntry d.root.self
    d.vertices.filter

def budget (W B n m : ℕ) : ℕ :=
  (56 * m + 23) + RegisterAdjacencyTable.budget W m n +
    RegisterResidualSearch.budget W 1 (n * n) n + RegisterRootValue.budget B m +
    RegisterThresholdVertices.budget W B (n + 1) m n n + 120

theorem search_budget_mono (W k T T' : ℕ) (hT : T ≤ T') :
    RegisterResidualSearch.budget W 1 T k ≤ RegisterResidualSearch.budget W 1 T' k := by
  unfold RegisterResidualSearch.budget RegisterResidualReach.budget RegisterResidualReach.stepBudget
    RegisterResidualCrossing.budget
  have h1 := Nat.mul_le_mul_left (RegisterResidualPredicate.budget W 1 (k + 1) + 40) hT
  have h2 := Nat.mul_le_mul_right k (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right h1 17) (RegisterRouteLookup.budget W (k + 1))) 130)
  omega

theorem adjTable_length (left right : Fin m → Fin n) :
    (ResidualReachGeneric.adjTable left right W).length ≤ n * n := by
  unfold ResidualReachGeneric.adjTable
  rw [List.length_map]
  refine (List.length_filter_le _ _).trans ?_
  unfold List.product
  simp [List.length_flatMap]

/-- The compiled recovery: the output is the ascending word list of the
threshold set of the recovered integer vector. -/
theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    (left right : Fin m → Fin n) (root : Fin n) (πw : Fin m → Word B) (yw : Fin m → Bits B)
    (oneB : Bits B) (hn : n < 2 ^ W) (hone : oneB.value = 1) (hfit : WidthFits B n πw yw)
    (heven : Even (HardSolveReference.rootNumerator (coeffs πw) (counts yw)))
    {h : Heap} (hh : Valid h) {ep np rp ap yp op1 opB zp : Ptr}
    (he : ListRep EdgeAt h ep (edgeWords W left right))
    (hnodes : WordsAt h np (rangeWords W n)) (hroot : BitsAt h rp (word W root.val))
    (hπ : SignedWords.ListAt h ap ((List.finRange m).map πw))
    (hy : WordsAt h yp ((List.finRange m).map yw))
    (ho1 : BitsAt h op1 one) (hoB : BitsAt h opB oneB) (hz : BitsAt h zp (Bits.zero B)) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q
        (setWords W (HardSolveReference.thresholdFrom left right root (coeffs πw) (counts yw))) ∧
      Within code h (initialRegisters [.pointer ep, .pointer np, .pointer rp, .pointer ap,
          .pointer yp, .pointer op1, .pointer opB, .pointer zp])
        (code d.self) [.pointer q] out (budget W B n m) := by
  obtain ⟨htab, hsearch, hentry, hroot', hvert, hself⟩ := hm
  -- records
  obtain ⟨H1, recp, e1, v1, hrec, zrun⟩ := records_compiled code d.table.edge htab.1 left right yw
    hh he hy
  -- adjacency table
  obtain ⟨H2, tp, e2, v2, htable, trun⟩ := RegisterAdjacencyTable.compiled code d.table htab v1
    (hnodes.mono e1) hrec (ho1.mono e1)
  rw [RegisterAdjacencyTable.tableW_eq hn] at htable
  -- search
  obtain ⟨H3, seenp, routep, e3, v3, -, hroutes, srun⟩ := RegisterResidualSearch.compiled code
    d.search hsearch v2 htable (ho1.mono (e1.trans e2)) (hnodes.mono (e1.trans e2))
    (hroot.mono (e1.trans e2))
  have e13 := e1.trans (e2.trans e3)
  -- root value
  obtain ⟨H4, magp, e4, v4, hmag, rrun⟩ := RegisterRootValue.compiled code d.root hroot' v3
    (hπ.mono e13) (hy.mono e13) (hz.mono e13) (hoB.mono e13) (by simp)
  have e14 := e13.trans e4
  let rw := RegisterRootValue.rootWord oneB ((List.finRange m).map πw) ((List.finRange m).map yw)
  -- data cells
  let H5 := H4 ++ [Cell.bit rw.1 magp]
  let H6 := H5 ++ [Cell.pair opB H4.length]
  let H7 := H6 ++ [Cell.pair recp zp]
  let H8 := H7 ++ [Cell.pair H6.length H5.length]
  let H9 := H8 ++ [Cell.pair routep H7.length]
  obtain ⟨e5, v5, q5⟩ := allocate_fits v4 (bit_fits (b := rw.1) hmag.allocated)
  obtain ⟨e6, v6, q6⟩ := allocate_fits v5 (pair_fits (h := H5) (a := opB) (b := H4.length)
    (lt_of_ext (e14.trans e5) hoB.allocated) (by simp [H5]))
  obtain ⟨e7, v7, q7⟩ := allocate_fits v6 (pair_fits (h := H6) (a := recp) (b := zp)
    (lt_of_ext (e2.trans (e3.trans (e4.trans (e5.trans e6)))) (ListRep.allocated hrec))
    (lt_of_ext (e14.trans (e5.trans e6)) hz.allocated))
  obtain ⟨e8, v8, q8⟩ := allocate_fits v7 (pair_fits (h := H7) (a := H6.length) (b := H5.length)
    (by simp [H7, H6]) (by simp [H7, H6, H5]))
  obtain ⟨e9, v9, q9⟩ := allocate_fits v8 (pair_fits (h := H8) (a := routep) (b := H7.length)
    (lt_of_ext (e4.trans (e5.trans (e6.trans (e7.trans e8)))) hroutes.allocated)
    (by simp [H8, H7]))
  have e49 : Extends H4 H9 := e5.trans (e6.trans (e7.trans (e8.trans e9)))
  have hdata : RegisterThresholdVertices.DataAt H9 H8.length
      (dataOf W left right root πw yw oneB) := by
    refine ⟨routep, H7.length, H6.length, H5.length, opB, H4.length, q9, e9.lookup q8,
      (e7.trans (e8.trans e9)).lookup q6, (hroutes.mono e4).mono e49,
      ⟨recp, zp, (e8.trans e9).lookup q7,
        (hrec.mono (e2.trans (e3.trans e4))).mono e49, (hz.mono e14).mono e49⟩,
      (hoB.mono e14).mono e49, ⟨magp, (e6.trans (e7.trans (e8.trans e9))).lookup q5,
        hmag.mono e49⟩⟩
  -- filter
  have hR : (dataOf W left right root πw yw oneB).routes.length ≤ n + 1 := by
    have hl := (ResidualListReach.explore_lengths (ResidualReachGeneric.adjTable left right W) one
      (rangeWords W n).length (ResidualListReach.initial (word W root.val))).2
    have hnl : (rangeWords W n).length = n := by simp [rangeWords]
    change (ResidualListReach.explore (ResidualReachGeneric.adjTable left right W) one
      (rangeWords W n).length (ResidualListReach.initial (word W root.val))).routes.length ≤ n + 1
    simp only [ResidualListReach.initial, List.length_cons, List.length_nil] at hl ⊢
    omega
  have hL : ∀ x, (RegisterRouteLookup.lookup x (dataOf W left right root πw yw oneB).routes).length
      ≤ n := by
    intro x
    have hl := ResidualListReach.search_lookup_length (ResidualReachGeneric.adjTable left right W)
      one (rangeWords W n) (word W root.val) x
    simpa [dataOf, routesOf, rangeWords] using hl
  obtain ⟨out, q, e10, v10, hq, frun⟩ := RegisterThresholdVertices.compiled code d.vertices hvert
    v9 hR hL ((hnodes.mono e14).mono e49) hdata
  refine ⟨out, q, e14.trans (e49.trans e10), v10, ?_, ?_⟩
  · rw [← filter_eq hn left right root πw yw oneB hone hfit heven]
    exact hq
  -- the run
  let regs := initialRegisters [Value.pointer ep, .pointer np, .pointer rp, .pointer ap,
    .pointer yp, .pointer op1, .pointer opB, .pointer zp]
  let s1 := bindResults regs [8] [.pointer recp]
  let s2 := bindResults s1 [9] [.pointer tp]
  let s3 := bindResults s2 [10, 11] [.pointer seenp, .pointer routep]
  let s4 := bindResults s3 [12, 13] [.flag rw.1, .pointer magp]
  let t1 := Function.update s4 14 (.pointer H4.length)
  let t2 := Function.update t1 15 (.pointer H5.length)
  let t3 := Function.update t2 12 (.pointer H6.length)
  let t4 := Function.update t3 13 (.pointer H7.length)
  let t5 := Function.update t4 14 (.pointer H8.length)
  let t6 := bindResults t5 [15] [.pointer q]
  have last : Within code out t6 (.ret [.register 15]) [.pointer q] out 3 := by
    simpa [t6, bindResults, values, Atom.eval] using Within.ret code out t6 [.register 15]
  have fargs : values t5 [.register 1, .register 14] = [.pointer np, .pointer H8.length] := by
    simp [t5, t4, t3, t2, t1, s4, s3, s2, s1, regs, bindResults, initialRegisters, values,
      Atom.eval]
  have fcall := Within.call (procedure := d.vertices.filter) (regs := t5)
    (arguments := [.register 1, .register 14]) (results := [15])
    (by simpa only [fargs] using frun) last
  have a5 := Within.allocate (regs := t4) (dst := 14) (h := H8)
    (expr := .pair (.register 11) (.register 13)) (c := .pair routep H7.length)
    (by simp [CellExpr.eval, Atom.eval, t4, t3, t2, t1, s4, s3, bindResults, Value.asPointer])
    fcall
  have a4 := Within.allocate (regs := t3) (dst := 13) (h := H7)
    (expr := .pair (.register 12) (.register 15)) (c := .pair H6.length H5.length)
    (by simp [CellExpr.eval, Atom.eval, t3, t2, Value.asPointer]) a5
  have a3 := Within.allocate (regs := t2) (dst := 12) (h := H6)
    (expr := .pair (.register 8) (.register 7)) (c := .pair recp zp)
    (by simp [CellExpr.eval, Atom.eval, t2, t1, s4, s3, s2, s1, regs, bindResults,
      initialRegisters, Value.asPointer]) a4
  have a2 := Within.allocate (regs := t1) (dst := 15) (h := H5)
    (expr := .pair (.register 6) (.register 14)) (c := .pair opB H4.length)
    (by simp [CellExpr.eval, Atom.eval, t1, s4, s3, s2, s1, regs, bindResults,
      initialRegisters, Value.asPointer]) a3
  have a1 := Within.allocate (regs := s4) (dst := 14) (h := H4)
    (expr := .bit (.register 12) (.register 13)) (c := .bit rw.1 magp)
    (by simp [CellExpr.eval, Atom.eval, s4, bindResults, Value.asPointer, Value.asFlag]) a2
  have rargs : values s3 [.register 3, .register 4, .register 7, .register 6] =
      [.pointer ap, .pointer yp, .pointer zp, .pointer opB] := by
    simp [s3, s2, s1, regs, bindResults, initialRegisters, values, Atom.eval]
  have rcall := Within.call (procedure := d.root.self) (regs := s3)
    (arguments := [.register 3, .register 4, .register 7, .register 6]) (results := [12, 13])
    (by simpa only [rargs] using rrun) a1
  have sargs : values s2 [.register 9, .register 5, .register 1, .register 2] =
      [.pointer tp, .pointer op1, .pointer np, .pointer rp] := by
    simp [s2, s1, regs, bindResults, initialRegisters, values, Atom.eval]
  have scall := Within.call (procedure := d.searchEntry) (regs := s2)
    (arguments := [.register 9, .register 5, .register 1, .register 2]) (results := [10, 11])
    (by rw [sargs, hentry]; exact srun) rcall
  have targs : values s1 [.register 1, .register 8, .register 5] =
      [.pointer np, .pointer recp, .pointer op1] := by
    simp [s1, regs, bindResults, initialRegisters, values, Atom.eval]
  have tcall := Within.call (procedure := d.table.self) (regs := s1)
    (arguments := [.register 1, .register 8, .register 5]) (results := [9])
    (by simpa only [targs] using trun) scall
  have zargs : values regs [.register 0, .register 4, .null] =
      [.pointer ep, .pointer yp, .pointer 0] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have zcall := Within.call (procedure := d.table.edge.zip) (regs := regs)
    (arguments := [.register 0, .register 4, .null]) (results := [8])
    (by simpa only [zargs] using zrun) tcall
  rw [hself]
  refine zcall.mono ?_
  have hsb := search_budget_mono W n _ _ (adjTable_length (W := W) left right)
  have hrl : (records W left right yw).length = m := by simp [records]
  have hnl : (rangeWords W n).length = n := by simp [rangeWords]
  have hdl : (dataOf W left right root πw yw oneB).recs.length = m := by simp [dataOf, records]
  simp only [budget, CellExpr.args, List.length_cons, List.length_nil, hrl, hnl, hdl,
    List.length_map, List.length_finRange] at hsb ⊢
  omega

/-! ## Polynomial budget -/

/-- The budget definitions unfolded by the bounds below. -/
theorem budget_unfold (W B n m : ℕ) :
    budget W B n m =
      (56 * m + 23) +
        (((((150 * W + 200 + 30) * m + 15 + 80 + 27) * n + 50 + 27) * n + 40)) +
        ((((2 * ((36 * W + 60) * (n + 1) + 13) + 36 * 1 + 76 + 40) * (n * n) + 17 +
          ((36 * W + 70) * (n + 1) + 13) + 130) * n + 15) + 50) +
        (500 * (B + 1) ^ 2 * m + 210 * B + 200) +
        ((((36 * W + 70) * (n + 1) +
          (((150 * W + 200 + 30) * m + 15 + 80 + 35) * n + 13) +
          400 * (B + 1) * n + 36 * B + 150) + 35) * n + 13) + 120 := rfl

/-- The budget is monotone in all four parameters. -/
theorem budget_mono {W B n m W' B' n' m' : ℕ} (hW : W ≤ W') (hB : B ≤ B') (hn : n ≤ n')
    (hm : m ≤ m') : budget W B n m ≤ budget W' B' n' m' := by
  rw [budget_unfold, budget_unfold]
  gcongr

theorem monomial_le {X M N a b c : ℕ} (hX : 1 ≤ X) (hM : 1 ≤ M) (hN : 1 ≤ N) (ha : a ≤ 2)
    (hb : b ≤ 1) (hc : c ≤ 4) : X ^ a * M ^ b * N ^ c ≤ X ^ 2 * M * N ^ 4 := by
  have h1 := Nat.pow_le_pow_right hX ha
  have h2 := Nat.pow_le_pow_right hM hb
  have h3 := Nat.pow_le_pow_right hN hc
  simp only [pow_one] at h2
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

/-- Polynomial form of the budget. -/
theorem budget_le (W B n m : ℕ) :
    budget W B n m ≤ 6000 * (W + B + 1) ^ 2 * (m + 1) * (n + 1) ^ 4 := by
  have hmono := budget_mono (W := W) (B := B) (n := n) (m := m) (W' := W + B + 1)
    (B' := W + B + 1) (n' := n + 1) (m' := m + 1) (by omega) (by omega) (by omega) (by omega)
  refine hmono.trans ?_
  generalize hX : W + B + 1 = X
  generalize hM : m + 1 = M
  generalize hN : n + 1 = N
  have hX1 : 1 ≤ X := by omega
  have hM1 : 1 ≤ M := by omega
  have hN1 : 1 ≤ N := by omega
  rw [budget_unfold]
  nlinarith [
    monomial_le (a := 0) (b := 0) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 0) (c := 1) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 0) (c := 2) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 0) (c := 3) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 0) (c := 4) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 0) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 0) (c := 1) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 0) (c := 2) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 0) (c := 3) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 0) (c := 4) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 2) (b := 0) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 1) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 1) (c := 1) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 1) (c := 2) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 1) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 1) (c := 1) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 1) (c := 2) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 2) (b := 1) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num)]

end WeightedMIS.RegisterHardRecovery
