module

public import WeightedMIS.RegisterOddRowStep
public import WeightedMIS.ExecutableReduction

/-!
# The compiled odd row

Inputs are the stored edge endpoint words `edgeWords W left right`, the stored
edge index words `rangeWords K m`, the stored vertex words `rangeWords W n`, the
root word, the unit word of width one, and the unit and zero words of the row
width `G`. The procedure

1. builds the parity search table (`RegisterParityTable`),
2. runs the compiled residual search from the even copy of the root,
3. tests membership of the odd copy of the root in the reached words,
4. looks up the stored reverse route of the odd copy of the root,
5. maps every edge index word to the left fold of `ParityReachRefinement.stepW`
   over the route arcs, starting from the signed zero.

The output words have the values `ComputedOddRow.oddRow` (that is,
`ExecutableReduction.parityRow root`) in edge order, provided `2 n < 2 ^ G`;
the flag is the membership `(root, true) ∈ paritySearch.seen` used by
`halfSolve`.
-/

@[expose] public section

namespace WeightedMIS.RegisterOddRow

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.RegisterPotentialStep WeightedMIS.GraphReachEncoded WeightedMIS.RegisterFirstEdge
open WeightedMIS.ParityReachRefinement WeightedMIS.SignedWords
open WeightedMIS.RegisterIncidenceRows (EdgeAt eqb)

variable {W K G : ℕ} {p : ℕ}

def rowBudget (W K G M L : ℕ) : ℕ := (stepBudget W K G M + 30) * L + 80

theorem row_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code) {M L : ℕ}
    {h : Heap} (hh : Valid h) {ip dp : Ptr} {i : Bits K}
    {data : List (Record W K) × List (Arc (W + 1) 1) × Bits G × Bits G}
    (hi : BitsAt h ip i) (hd : RowDataAt M L h dp data) :
    ∃ out q, Extends h out ∧ Valid out ∧
      SignedAt out q (rowW data.1 i data.2.2.1 data.2.2.2 data.2.1) ∧
      Within code h (initialRegisters [.pointer ip, .pointer dp]) (code d.row) [.pointer q] out
        (rowBudget W K G M L) := by
  have hm' := hm
  obtain ⟨-, -, -, -, -, -, -, -, hfold, hrow, -⟩ := hm'
  obtain ⟨recs, route, oneG, zero⟩ := data
  obtain ⟨rp, r1, tp, r2, op, zp, c1, c2, c3, hr, ht, ho, hz, hl, hL⟩ := hd
  simp only at hr ht ho hz hl hL
  let H1 := h ++ [Cell.pair ip op]
  let H2 := H1 ++ [Cell.pair rp h.length]
  obtain ⟨e1, v1, q1⟩ := allocate_fits hh (pair_fits hi.allocated ho.allocated)
  obtain ⟨e2, v2, q2⟩ := allocate_fits v1 (pair_fits (h := H1) (a := rp) (b := h.length)
    (lt_of_ext e1 (ListRep.allocated hr)) (by simp [H1]))
  have e12 := e1.trans e2
  have hsd : StepDataAt M H2 H1.length (recs, i, oneG) :=
    ⟨rp, h.length, ip, op, q2, e2.lookup q1, hr.mono e12, hi.mono e12, ho.mono e12, hl⟩
  obtain ⟨out, q, e3, v3, hq, frun⟩ := RegisterListFold.compiled_const code d.fold d.step hfold
    (fun h p (a : Arc (W + 1) 1) => ArcAt h p a) (StepDataAt M) (fun h p (a : Word G) => SignedAt h p a)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun d acc a => stepW d.1 d.2.1 d.2.2 acc a) (stepBudget W K G M) v2 (ht.mono e12) hsd
    (hz.mono e12)
    (fun _ _ _ _ _ hv _ _ hx hd hs => step_compiled code d hm hv hx hd hs)
  refine ⟨out, q, e12.trans e3, v3, hq, ?_⟩
  let regs := initialRegisters [Value.pointer ip, .pointer dp]
  let s1 := loadRegisters regs 2 3 15 (.pair rp r1)
  let s2 := loadRegisters s1 4 5 15 (.pair tp r2)
  let s3 := loadRegisters s2 6 7 15 (.pair op zp)
  let t1 := Function.update s3 8 (.pointer h.length)
  let t2 := Function.update t1 9 (.pointer H1.length)
  let t3 := bindResults t2 [10] [.pointer q]
  have last : Within code out t3 (.ret [.register 10]) [.pointer q] out 3 := by
    simpa [t3, bindResults, values, Atom.eval] using Within.ret code out t3 [.register 10]
  have fargs : values t2 [.register 4, .register 9, .register 7] =
      [.pointer tp, .pointer H1.length, .pointer zp] := by
    simp [t2, t1, s3, s2, loadRegisters, decoded, values, Atom.eval]
  have fcall := Within.call (procedure := d.fold) (regs := t2)
    (arguments := [.register 4, .register 9, .register 7]) (results := [10])
    (by simpa only [fargs] using frun) last
  have a2 := Within.allocate (regs := t1) (dst := 9) (h := H1)
    (expr := .pair (.register 2) (.register 8)) (c := .pair rp h.length)
    (by simp [CellExpr.eval, Atom.eval, t1, s3, s2, s1, loadRegisters, decoded,
      Value.asPointer]) fcall
  have a1 := Within.allocate (regs := s3) (dst := 8) (h := h)
    (expr := .pair (.register 0) (.register 6)) (c := .pair ip op)
    (by simp [CellExpr.eval, Atom.eval, s3, s2, s1, regs, loadRegisters, decoded,
      initialRegisters, Value.asPointer]) a2
  have l3 := Within.load (regs := s2) (address := .register 5) (first := 6) (second := 7)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .allocate 8 (.pair (.register 0) (.register 6))
        (.allocate 9 (.pair (.register 2) (.register 8))
          (.call d.fold [.register 4, .register 9, .register 7] [10] (.ret [.register 10]))) })
    (by simp [s2, loadRegisters, decoded, Atom.eval]) c3 a1
  have l2 := Within.load (regs := s1) (address := .register 3) (first := 4) (second := 5)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 5) 6 7 15 { CompiledTrie.failCases with
        pair := .allocate 8 (.pair (.register 0) (.register 6))
          (.allocate 9 (.pair (.register 2) (.register 8))
            (.call d.fold [.register 4, .register 9, .register 7] [10]
              (.ret [.register 10]))) } })
    (by simp [s1, loadRegisters, decoded, Atom.eval]) c2 l3
  have l1 := Within.load (regs := regs) (address := .register 1) (first := 2) (second := 3)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
        pair := .load (.register 5) 6 7 15 { CompiledTrie.failCases with
          pair := .allocate 8 (.pair (.register 0) (.register 6))
            (.allocate 9 (.pair (.register 2) (.register 8))
              (.call d.fold [.register 4, .register 9, .register 7] [10]
                (.ret [.register 10]))) } } })
    (by simp [regs, initialRegisters, Atom.eval]) c1 l2
  rw [hrow]
  have hmul := Nat.mul_le_mul_left (stepBudget W K G M + 30) hL
  exact l1.mono (by simp [rowBudget, CellExpr.args]; omega)

/-! ## The whole odd row -/

/-- The edge-index records of a graph. -/
abbrev recordsOf (W K : ℕ) {n m : ℕ} (left right : Fin m → Fin n) : List (Record W K) :=
  records W left right (fun e => word K e.val)

/-- The stored reverse parity route of the odd copy of the root. -/
def routeOf (W K : ℕ) {n m : ℕ} (left right : Fin m → Fin n) (root : Fin n) :
    List (Arc (W + 1) 1) :=
  RegisterRouteLookup.lookup (parityWord true (word W root.val))
    (searchW (recordsOf W K left right) (rangeWords W n) (word W root.val)).routes

/-- The computed signed row word of an edge. -/
def rowWord (W K : ℕ) {G n m : ℕ} (left right : Fin m → Fin n) (root : Fin n)
    (oneG zero : Bits G) (e : Fin m) : Word G :=
  rowW (recordsOf W K left right) (word K e.val) oneG zero (routeOf W K left right root)

/-- The computed parity flag. -/
def flagOf (W K : ℕ) {n m : ℕ} (left right : Fin m → Fin n) (root : Fin n) : Bool :=
  RegisterMembership.found (parityWord true (word W root.val))
    (searchW (recordsOf W K left right) (rangeWords W n) (word W root.val)).seen

def budget (W K G n m : ℕ) : ℕ :=
  RegisterParityTable.budget W m n + RegisterResidualSearch.budget (W + 1) 1 (4 * n * n) (2 * n) +
    RegisterMembership.budget (W + 1) (2 * n + 1) + RegisterRouteLookup.budget (W + 1) (2 * n + 1) +
    (rowBudget W K G m (2 * n) + 35) * m + 150

theorem search_budget_mono (W k T T' : ℕ) (hT : T ≤ T') :
    RegisterResidualSearch.budget W 1 T k ≤ RegisterResidualSearch.budget W 1 T' k := by
  unfold RegisterResidualSearch.budget RegisterResidualReach.budget RegisterResidualReach.stepBudget
    RegisterResidualCrossing.budget
  have h1 := Nat.mul_le_mul_left (RegisterResidualPredicate.budget W 1 (k + 1) + 40) hT
  have h2 := Nat.mul_le_mul_right k (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right h1 17) (RegisterRouteLookup.budget W (k + 1))) 130)
  omega

section Lengths

variable {n m : ℕ} (left right : Fin m → Fin n)

theorem parityNodes_length : (ComputedOddRow.parityNodes (List.finRange n)).length = 2 * n := by
  unfold ComputedOddRow.parityNodes
  rw [show (List.finRange n).product [false, true] = (List.finRange n) ×ˢ [false, true] from rfl,
    List.length_product]
  simp [Nat.mul_comm]

theorem table_length (hn : n < 2 ^ W) :
    (parityTableW (recordsOf W K left right) (rangeWords W n)).length ≤ 4 * n * n := by
  rw [parityTable_eq left right hn, List.length_map]
  refine (List.length_filter_le _ _).trans ?_
  rw [show ∀ l : List (Fin n × Bool), l.product l = l ×ˢ l from fun _ => rfl, List.length_product,
    parityNodes_length]
  ring_nf
  exact le_refl _

theorem nodes_length : (parityNodeWords (rangeWords W n)).length = 2 * n := by
  rw [RegisterParityTable.parityNodeWords_length']
  simp [rangeWords]

theorem seen_length (root : Fin n) :
    (searchW (recordsOf W K left right) (rangeWords W n) (word W root.val)).seen.length ≤
      2 * n + 1 := by
  have h := (ResidualListReach.explore_lengths
    (parityTableW (recordsOf W K left right) (rangeWords W n)) one
    (parityNodeWords (rangeWords W n)).length
    (ResidualListReach.initial (parityWord false (word W root.val)))).1
  rw [nodes_length] at h
  have h1 : (ResidualListReach.initial (b := 1) (parityWord false (word W root.val))).seen.length
      = 1 := rfl
  unfold searchW
  rw [nodes_length]
  omega

theorem routes_length (root : Fin n) :
    (searchW (recordsOf W K left right) (rangeWords W n) (word W root.val)).routes.length ≤
      2 * n + 1 := by
  have h := (ResidualListReach.explore_lengths
    (parityTableW (recordsOf W K left right) (rangeWords W n)) one
    (parityNodeWords (rangeWords W n)).length
    (ResidualListReach.initial (parityWord false (word W root.val)))).2
  rw [nodes_length] at h
  have h1 : (ResidualListReach.initial (b := 1) (parityWord false (word W root.val))).routes.length
      = 1 := rfl
  unfold searchW
  rw [nodes_length]
  omega

end Lengths

/-- The compiled odd row: signed row words of all edges, in edge order, and the
parity flag. -/
theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {n m : ℕ} (left right : Fin m → Fin n) (root : Fin n) (oneG zero : Bits G)
    (hn : n < 2 ^ W) {h : Heap} (hh : Valid h) {ep ip np rp op1 opG zp : Ptr}
    (he : ListRep EdgeAt h ep (edgeWords W left right))
    (hi : WordsAt h ip (rangeWords K m)) (hnodes : WordsAt h np (rangeWords W n))
    (hroot : BitsAt h rp (word W root.val)) (ho1 : BitsAt h op1 one)
    (hoG : BitsAt h opG oneG) (hz : BitsAt h zp zero) :
    ∃ out q, Extends h out ∧ Valid out ∧
      ListAt out q ((List.finRange m).map (rowWord W K left right root oneG zero)) ∧
      Within code h (initialRegisters [.pointer ep, .pointer ip, .pointer np, .pointer rp,
          .pointer op1, .pointer opG, .pointer zp])
        (code d.self) [.pointer q, .flag (flagOf W K left right root)] out
        (budget W K G n m) := by
  have hm' := hm
  obtain ⟨hpt, hsearch, hentry, -, -, -, -, -, -, -, hrows, hself⟩ := hm'
  obtain ⟨-, -, -, hmember, hlookup, -, -, hcmp⟩ := hsearch
  -- parity table
  obtain ⟨H1, tp, recp, pnp, e1, v1, htable, hrec, hpn, prun⟩ :=
    RegisterParityTable.compiled code d.ptable hpt left right hh he hi hnodes ho1
  -- the even root copy
  let H2 := H1 ++ [Cell.bit false rp]
  obtain ⟨e2, v2, q2⟩ := allocate_fits v1 (bit_fits (b := false) (lt_of_ext e1 hroot.allocated))
  have hsrc : BitsAt H2 H1.length (parityWord false (word W root.val)) :=
    BitsAt.cons q2 ((hroot.mono e1).mono e2)
  -- search
  obtain ⟨H3, seenp, routep, e3, v3, hseen, hroutes, srun⟩ := RegisterResidualSearch.compiled
    code d.search hm.2.1 v2 (htable.mono e2) ((ho1.mono e1).mono e2) (hpn.mono e2) hsrc
  have e13 := e1.trans (e2.trans e3)
  -- the odd root copy
  let H4 := H3 ++ [Cell.bit true rp]
  obtain ⟨e4, v4, q4⟩ := allocate_fits v3 (bit_fits (b := true) (lt_of_ext e13 hroot.allocated))
  have hodd : BitsAt H4 H3.length (parityWord true (word W root.val)) :=
    BitsAt.cons q4 ((hroot.mono e13).mono e4)
  have mrun := RegisterMembership.compiled code d.search.member d.search.cmp hmember hcmp hodd
    (hseen.mono e4)
  obtain ⟨routeP, hroute, lrun⟩ := RegisterRouteLookup.compiled code d.search.lookup d.search.cmp
    hlookup hcmp v4 hodd (hroutes.mono e4)
  -- row data
  have e14 := e13.trans e4
  let H5 := H4 ++ [Cell.bit false zp]
  let H6 := H5 ++ [Cell.pair opG H4.length]
  let H7 := H6 ++ [Cell.pair routeP H5.length]
  let H8 := H7 ++ [Cell.pair recp H6.length]
  obtain ⟨e5, v5, q5⟩ := allocate_fits v4 (bit_fits (b := false) (lt_of_ext e14 hz.allocated))
  obtain ⟨e6, v6, q6⟩ := allocate_fits v5 (pair_fits (h := H5) (a := opG) (b := H4.length)
    (lt_of_ext (e14.trans e5) hoG.allocated) (by simp [H5]))
  obtain ⟨e7, v7, q7⟩ := allocate_fits v6 (pair_fits (h := H6) (a := routeP) (b := H5.length)
    (lt_of_ext (e5.trans e6) (ListRep.allocated hroute)) (by simp [H6, H5]))
  obtain ⟨e8, v8, q8⟩ := allocate_fits v7 (pair_fits (h := H7) (a := recp) (b := H6.length)
    (lt_of_ext (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7))))) (ListRep.allocated hrec))
    (by simp [H7, H6]))
  have e48 : Extends H4 H8 := e5.trans (e6.trans (e7.trans e8))
  have hdata : RowDataAt m (2 * n) H8 H7.length
      (recordsOf W K left right, routeOf W K left right root, oneG, zero) := by
    refine ⟨recp, H6.length, routeP, H5.length, opG, H4.length, q8, e8.lookup q7,
      (e7.trans e8).lookup q6, ((hrec.mono (e2.trans (e3.trans e4))).mono e48), hroute.mono e48,
      (hoG.mono e14).mono e48, ⟨zp, (e6.trans (e7.trans e8)).lookup q5, (hz.mono e14).mono e48⟩,
      by simp [records], ?_⟩
    exact lookup_length left right _ root _
  -- rows
  obtain ⟨out, q, e9, v9, hq, mrun'⟩ := RegisterListMap.compiled_const code d.rows d.row hrows
    (fun h p (x : Bits K) => BitsAt h p x) (RowDataAt m (2 * n)) (fun h p (x : Word G) => SignedAt h p x)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun _ hx => hx.allocated) (fun data i => rowW data.1 i data.2.2.1 data.2.2.2 data.2.1)
    (rowBudget W K G m (2 * n)) v8 ((hi.mono e14).mono e48) hdata
    (fun hv _ _ _ hx hd => row_compiled code d hm hv hx hd)
  refine ⟨out, q, e14.trans (e48.trans e9), v9, ?_, ?_⟩
  · have hmap : (rangeWords K m).map (fun i => rowW (recordsOf W K left right) i oneG zero
        (routeOf W K left right root)) =
        (List.finRange m).map (rowWord W K left right root oneG zero) := by
      rw [rangeWords, List.map_map]
      rfl
    rw [← hmap]
    exact hq
  -- the run
  let fl := flagOf W K left right root
  let regs := initialRegisters [Value.pointer ep, .pointer ip, .pointer np, .pointer rp,
    .pointer op1, .pointer opG, .pointer zp]
  let s1 := bindResults regs [7, 8, 9] [.pointer tp, .pointer recp, .pointer pnp]
  let s2 := Function.update s1 10 (.pointer H1.length)
  let s3 := bindResults s2 [11, 12] [.pointer seenp, .pointer routep]
  let s4 := Function.update s3 10 (.pointer H3.length)
  let s5 := bindResults s4 [13] [.flag fl]
  let s6 := bindResults s5 [14] [.pointer routeP]
  let s7 := Function.update s6 15 (.pointer H4.length)
  let s8 := Function.update s7 12 (.pointer H5.length)
  let s9 := Function.update s8 11 (.pointer H6.length)
  let s10 := Function.update s9 10 (.pointer H7.length)
  let s11 := bindResults s10 [12] [.pointer q]
  have last : Within code out s11 (.ret [.register 12, .register 13]) [.pointer q, .flag fl]
      out 5 := by
    simpa [s11, s10, s9, s8, s7, s6, s5, bindResults, values, Atom.eval] using
      Within.ret code out s11 [.register 12, .register 13]
  have rargs : values s10 [.register 1, .register 10] = [.pointer ip, .pointer H7.length] := by
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, regs, bindResults, initialRegisters, values,
      Atom.eval]
  have rcall := Within.call (procedure := d.rows) (regs := s10)
    (arguments := [.register 1, .register 10]) (results := [12])
    (by simpa only [rargs] using mrun') last
  have a4 := Within.allocate (regs := s9) (dst := 10) (h := H7)
    (expr := .pair (.register 8) (.register 11)) (c := .pair recp H6.length)
    (by simp [CellExpr.eval, Atom.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, bindResults,
      Value.asPointer]) rcall
  have a3 := Within.allocate (regs := s8) (dst := 11) (h := H6)
    (expr := .pair (.register 14) (.register 12)) (c := .pair routeP H5.length)
    (by simp [CellExpr.eval, Atom.eval, s8, s7, s6, bindResults, Value.asPointer]) a4
  have a2 := Within.allocate (regs := s7) (dst := 12) (h := H5)
    (expr := .pair (.register 5) (.register 15)) (c := .pair opG H4.length)
    (by simp [CellExpr.eval, Atom.eval, s7, s6, s5, s4, s3, s2, s1, regs, bindResults,
      initialRegisters, Value.asPointer]) a3
  have a1 := Within.allocate (regs := s6) (dst := 15) (h := H4)
    (expr := .bit (.flag false) (.register 6)) (c := .bit false zp)
    (by simp [CellExpr.eval, Atom.eval, s6, s5, s4, s3, s2, s1, regs, bindResults,
      initialRegisters, Value.asPointer, Value.asFlag]) a2
  have largs : values s5 [.register 10, .register 12] = [.pointer H3.length, .pointer routep] := by
    simp [s5, s4, s3, bindResults, values, Atom.eval]
  have lcall := Within.call (procedure := d.search.lookup) (regs := s5)
    (arguments := [.register 10, .register 12]) (results := [14])
    (by simpa only [largs] using lrun) a1
  have margs : values s4 [.register 10, .register 11] = [.pointer H3.length, .pointer seenp] := by
    simp [s4, s3, bindResults, values, Atom.eval]
  have mcall := Within.call (procedure := d.search.member) (regs := s4)
    (arguments := [.register 10, .register 11]) (results := [13])
    (by rw [margs]; exact mrun) lcall
  have a0 := Within.allocate (regs := s3) (dst := 10) (h := H3)
    (expr := .bit (.flag true) (.register 3)) (c := .bit true rp)
    (by simp [CellExpr.eval, Atom.eval, s3, s2, s1, regs, bindResults, initialRegisters,
      Value.asPointer, Value.asFlag]) mcall
  have sargs : values s2 [.register 7, .register 4, .register 9, .register 10] =
      [.pointer tp, .pointer op1, .pointer pnp, .pointer H1.length] := by
    simp [s2, s1, regs, bindResults, initialRegisters, values, Atom.eval]
  have scall := Within.call (procedure := d.searchEntry) (regs := s2)
    (arguments := [.register 7, .register 4, .register 9, .register 10]) (results := [11, 12])
    (by rw [sargs, hentry]; exact srun) a0
  have as := Within.allocate (regs := s1) (dst := 10) (h := H1)
    (expr := .bit (.flag false) (.register 3)) (c := .bit false rp)
    (by simp [CellExpr.eval, Atom.eval, s1, regs, bindResults, initialRegisters,
      Value.asPointer, Value.asFlag]) scall
  have pargs : values regs [.register 0, .register 1, .register 2, .register 4] =
      [.pointer ep, .pointer ip, .pointer np, .pointer op1] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have pcall := Within.call (procedure := d.ptable.self) (regs := regs)
    (arguments := [.register 0, .register 1, .register 2, .register 4]) (results := [7, 8, 9])
    (by simpa only [pargs] using prun) as
  rw [hself]
  refine pcall.mono ?_
  have hsb := search_budget_mono (W + 1) (2 * n) _ _ (table_length (K := K) left right hn)
  have hsl := seen_length (W := W) (K := K) left right root
  have hrl := routes_length (W := W) (K := K) left right root
  have hmb := Nat.mul_le_mul_left (36 * (W + 1) + 60) hsl
  have hlb := Nat.mul_le_mul_left (36 * (W + 1) + 70) hrl
  have hnl := nodes_length (W := W) (n := n)
  have hkl : (rangeWords K m).length = m := by simp [rangeWords]
  simp only [searchW, recordsOf] at hsl hrl hmb hlb hsb
  simp only [budget, RegisterMembership.budget, RegisterRouteLookup.budget, CellExpr.args,
    List.length_cons, List.length_nil, hnl, hkl] at hsb hmb hlb ⊢
  omega

/-- The machine row is the computed odd row, given `2 n < 2 ^ G`. -/
theorem rowWord_value {n m : ℕ} (left right : Fin m → Fin n) (root : Fin n) (oneG zero : Bits G)
    (hn : n < 2 ^ W) (hm : m < 2 ^ K) (hG : 2 * n < 2 ^ G) (hone : oneG.value = 1)
    (hzero : zero.value = 0) (e : Fin m) :
    value (rowWord W K left right root oneG zero e) =
      ExecutableReduction.parityRow (left := left) (right := right) root e :=
  rowW_value left right hn hm hG oneG zero hone hzero root e

/-- The machine flag is the parity membership test of `halfSolve`. -/
theorem flagOf_eq {n m : ℕ} (left right : Fin m → Fin n) (root : Fin n) (hn : n < 2 ^ W) :
    flagOf W K left right root = decide ((root, true) ∈
      (ComputedOddRow.paritySearch left right (List.finRange m) (List.finRange n) root).seen) :=
  parity_found left right hn _ root

/-- The compiled odd row in the form consumed by the recovery stage. -/
theorem oddRow_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {n m : ℕ} (left right : Fin m → Fin n) (root : Fin n) (oneG zero : Bits G)
    (hn : n < 2 ^ W) (hmK : m < 2 ^ K) (hG : 2 * n < 2 ^ G) (hone : oneG.value = 1)
    (hzero : zero.value = 0) {h : Heap} (hh : Valid h) {ep ip np rp op1 opG zp : Ptr}
    (he : ListRep EdgeAt h ep (edgeWords W left right))
    (hi : WordsAt h ip (rangeWords K m)) (hnodes : WordsAt h np (rangeWords W n))
    (hroot : BitsAt h rp (word W root.val)) (ho1 : BitsAt h op1 one)
    (hoG : BitsAt h opG oneG) (hz : BitsAt h zp zero) :
    ∃ out q, ∃ πw : Fin m → Word G, Extends h out ∧ Valid out ∧
      (∀ e, value (πw e) = ExecutableReduction.parityRow (left := left) (right := right) root e) ∧
      ListAt out q ((List.finRange m).map πw) ∧
      Within code h (initialRegisters [.pointer ep, .pointer ip, .pointer np, .pointer rp,
          .pointer op1, .pointer opG, .pointer zp])
        (code d.self) [.pointer q, .flag (decide ((root, true) ∈
          (ComputedOddRow.paritySearch left right (List.finRange m) (List.finRange n) root).seen))]
        out (budget W K G n m) := by
  obtain ⟨out, q, e, v, hq, run⟩ := compiled code d hm left right root oneG zero hn hh he hi
    hnodes hroot ho1 hoG hz
  refine ⟨out, q, rowWord W K left right root oneG zero, e, v,
    rowWord_value left right root oneG zero hn hmK hG hone hzero, hq, ?_⟩
  rw [← flagOf_eq (K := K) left right root hn]
  exact run

/-! ## Polynomial budget -/

theorem budget_mono {W K G n m W' K' G' n' m' : ℕ} (hW : W ≤ W') (hK : K ≤ K') (hG : G ≤ G')
    (hn : n ≤ n') (hm : m ≤ m') : budget W K G n m ≤ budget W' K' G' n' m' := by
  simp only [budget, RegisterParityTable.budget, RegisterAdjacencyTable.budget,
    RegisterAdjacencyTable.rowBudget, RegisterAdjacencyTable.cellBudget, findBudget, matchBudget,
    RegisterResidualSearch.budget, RegisterResidualReach.budget, RegisterResidualReach.stepBudget,
    RegisterResidualCrossing.budget, RegisterResidualPredicate.budget, RegisterMembership.budget,
    RegisterRouteLookup.budget, rowBudget, stepBudget]
  gcongr

theorem monomial_le {X M N a b c : ℕ} (hX : 1 ≤ X) (hM : 1 ≤ M) (hN : 1 ≤ N) (ha : a ≤ 1)
    (hb : b ≤ 2) (hc : c ≤ 4) : X ^ a * M ^ b * N ^ c ≤ X * M ^ 2 * N ^ 4 := by
  have h1 := Nat.pow_le_pow_right hX ha
  have h2 := Nat.pow_le_pow_right hM hb
  have h3 := Nat.pow_le_pow_right hN hc
  simp only [pow_one] at h1
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

/-- Polynomial form of the budget: linear in the widths, quadratic in the edge
count, quartic in the vertex count. -/
theorem budget_le (W K G n m : ℕ) :
    budget W K G n m ≤ 100000 * (W + K + G + 1) * (m + 1) ^ 2 * (n + 1) ^ 4 := by
  have hmono := budget_mono (W := W) (K := K) (G := G) (n := n) (m := m) (W' := W + K + G + 1)
    (K' := W + K + G + 1) (G' := W + K + G + 1) (n' := n + 1) (m' := m + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  refine hmono.trans ?_
  generalize hX : W + K + G + 1 = X
  generalize hM : m + 1 = M
  generalize hN : n + 1 = N
  have hX1 : 1 ≤ X := by omega
  have hM1 : 1 ≤ M := by omega
  have hN1 : 1 ≤ N := by omega
  simp only [budget, RegisterParityTable.budget, RegisterAdjacencyTable.budget,
    RegisterAdjacencyTable.rowBudget, RegisterAdjacencyTable.cellBudget, findBudget, matchBudget,
    RegisterResidualSearch.budget, RegisterResidualReach.budget, RegisterResidualReach.stepBudget,
    RegisterResidualCrossing.budget, RegisterResidualPredicate.budget, RegisterMembership.budget,
    RegisterRouteLookup.budget, rowBudget, stepBudget]
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
    monomial_le (a := 0) (b := 1) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 1) (c := 1) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 1) (c := 2) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 1) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 1) (c := 1) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 1) (c := 2) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 2) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 0) (b := 2) (c := 1) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 2) (c := 0) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num),
    monomial_le (a := 1) (b := 2) (c := 1) hX1 hM1 hN1 (by norm_num) (by norm_num) (by norm_num)]

end WeightedMIS.RegisterOddRow
