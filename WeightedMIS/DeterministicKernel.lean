module

public import WeightedMIS.CycleSearch
public import WeightedMIS.ComputedKernel
public import WeightedMIS.KernelArithmetic

/-!
# Deterministic bounded kernel generators

The signed support graph is traversed by first-successor search in a canonical
edge enumeration. Counting its distinct oriented arcs yields a bounded integral
kernel vector. Rational support elimination then produces bounded generators
without choosing a preexisting basis or expanding large flow multiplicities.
-/

@[expose] public section

namespace WeightedMIS.DeterministicKernel

open Matrix Walks SparseKernel

variable {n m : ℕ}

abbrev OrientedEdge (m : ℕ) := Fin m × Bool

/-- Enumerate the two orientations of each edge in numeric edge order. -/
def arcList (m : ℕ) : List (OrientedEdge m) :=
  (List.ofFn (fun i : Fin m => i)).flatMap fun e => [(e, false), (e, true)]

theorem mem_arcList (a : OrientedEdge m) : a ∈ arcList m := by
  rcases a with ⟨e, b⟩
  cases b <;> simp [arcList, List.mem_flatMap, List.mem_ofFn]

theorem arcList_length (m : ℕ) : (arcList m).length = 2 * m := by
  simp [arcList, List.length_flatMap, Function.comp_def, Nat.mul_comm]

/-- View an enumerated orientation as an arc in the signed-stub construction. -/
def liftArc (left right : Fin m → Fin n) (x : Fin m → ℚ) (a : OrientedEdge m) :
    Arc (KernelBasis.columns left right (rationalSign x)) :=
  ⟨a, Or.inl (by simp [KernelBasis.columns])⟩

def arcSource (left right : Fin m → Fin n) (x : Fin m → ℚ) (a : OrientedEdge m) : State (Fin n) :=
  source _ (liftArc left right x a)

def arcTarget (left right : Fin m → Fin n) (x : Fin m → ℚ) (a : OrientedEdge m) : State (Fin n) :=
  target _ (liftArc left right x a)

def active (x : Fin m → ℚ) (a : OrientedEdge m) : Bool := decide (x a.1 ≠ 0)

/-- The concrete cycle returned by finite supported-successor search. -/
def cycle (left right : Fin m → Fin n) (x : Fin m → ℚ) : List (OrientedEdge m) :=
  match (arcList m).find? (active x) with
  | none => []
  | some a => CycleSearch.findCycle (arcSource left right x) (arcTarget left right x)
      (active x) (arcList m) a

/-- The concrete integer generator is the signed edge count of the cycle. -/
def generator (left right : Fin m → Fin n) (x : Fin m → ℚ) : Fin m → ℤ :=
  fun e => signValue (rationalSign x e) * ((cycle left right x).map Prod.fst).count e

private theorem map_walk (left right : Fin m → Fin n) (x : Fin m → ℚ)
    {u v : State (Fin n)} (p : List (OrientedEdge m))
    (hp : ShortestPath.IsWalk (arcSource left right x) (arcTarget left right x) u v p) :
    ShortestPath.IsWalk (source (KernelBasis.columns left right (rationalSign x)))
      (target (KernelBasis.columns left right (rationalSign x))) u v
      (p.map (liftArc left right x)) := by
  induction p generalizing u with
  | nil => exact hp
  | cons a p ih => exact ⟨hp.1, ih hp.2⟩

theorem cycle_spec (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) (hne : x ≠ 0) :
    ∃ u, ShortestPath.IsWalk (arcSource left right x) (arcTarget left right x) u u
        (cycle left right x) ∧
      cycle left right x ≠ [] ∧ (cycle left right x).Nodup ∧
      (cycle left right x).length ≤ 2 * m ∧
      ∀ a ∈ cycle left right x, x a.1 ≠ 0 := by
  have hex : ∃ e, x e ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨e, he⟩ := hex
  have hs : ((arcList m).find? (active x)).isSome :=
    List.find?_isSome.mpr ⟨(e, false), mem_arcList _, by simpa [active] using he⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
  have hac := List.find?_some ha
  have hnxt (b : OrientedEdge m) (hb : active x b = true) :
      ∃ c ∈ arcList m, active x c = true ∧ arcSource left right x c = arcTarget left right x b := by
    have hb' : x b.1 ≠ 0 := by simpa [active] using hb
    obtain ⟨c, hc, hs⟩ := supported_successor left right x hx (liftArc left right x b) hb'
    exact ⟨c.val, mem_arcList _, by simpa [active] using hc, hs⟩
  obtain ⟨u, hp, hne', hnd, hlen, hsupp⟩ := CycleSearch.findCycle_spec
    (arcSource left right x) (arcTarget left right x) (active x) (arcList m)
    (fun b _ => mem_arcList b) hnxt a hac
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [cycle, ha] using hp
  · simpa only [cycle, ha] using hne'
  · simpa only [cycle, ha] using hnd
  · simpa only [cycle, ha, arcList_length] using hlen
  · intro b hb
    have h := hsupp b (by simpa only [cycle, ha] using hb)
    simpa [active] using h

/-- Correctness of the deterministic support-generator routine. -/
theorem generator_spec (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) (hne : x ≠ 0) :
    KernelBasis.IntegralKernel left right (generator left right x) ∧
      (∀ e, |generator left right x e| ≤ 2) ∧ generator left right x ≠ 0 ∧
      ∀ e, x e = 0 → generator left right x e = 0 := by
  obtain ⟨u, hp, hne', hnd, _, hsupp⟩ := cycle_spec left right x hx hne
  let C := KernelBasis.columns left right (rationalSign x)
  obtain ⟨w, hw⟩ := BoundedCycles.walk_of_arcs C _ (map_walk left right x _ hp)
  have hlabels : w.labels = (cycle left right x).map Prod.fst := by
    rw [BoundedCycles.labels_eq_map_arcs, hw, List.map_map]
    rfl
  have hnd' : (BoundedCycles.arcs w).Nodup := by
    rw [hw]
    apply hnd.map
    intro a b hab
    exact congrArg Subtype.val hab
  have hbounds := BoundedCycles.projection_le_two C w hnd'
  have hkernel := KernelBasis.signed_projection_kernel left right (rationalSign x) ⟨u, w⟩
  have hgen : generator left right x =
      fun e => signValue (rationalSign x e) * (projection w.labels e : ℤ) := by
    funext e
    unfold generator
    simp only [projection, hlabels]
  rw [hgen]
  refine ⟨hkernel, KernelBasis.signed_projection_bound _ _ hbounds, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne'
    have hpos : 0 < projection w.labels a.1 := by
      apply List.count_pos_iff.mpr
      rw [hlabels]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    intro hzero
    have hz := congrFun hzero a.1
    cases rationalSign x a.1 <;> simp [signValue] at hz <;> omega
  · intro e he
    have hnot : e ∉ w.labels := by
      rw [hlabels]
      intro hm
      obtain ⟨a, ha, hae⟩ := List.mem_map.mp hm
      exact hsupp a ha (by simpa only [hae] using he)
    have hpzero : projection w.labels e = 0 := List.count_eq_zero.mpr hnot
    simp [hpzero]

/-- Store integer generator coordinates before subsequent pivot operations. -/
def materializeInt (g : Fin m → ℤ) : Fin m → ℤ :=
  let a := Vector.ofFn g
  fun i => a[i.val]

@[simp] theorem materializeInt_eq (g : Fin m → ℤ) : materializeInt g = g := by
  funext i
  simp [materializeInt]

/-- Store every residual rational coordinate before the next support search. -/
def materializeRat (x : Fin m → ℚ) : Fin m → ℚ :=
  StoredElimination.decode (StoredElimination.encode x)

@[simp] theorem materializeRat_eq (x : Fin m → ℚ) : materializeRat x = x :=
  StoredElimination.decode_encode x

/-- First nonzero coordinate of an integral row. -/
def pivot (g : Fin m → ℤ) : Option (Fin m) :=
  (List.ofFn (fun i : Fin m => i)).find? fun i => decide (g i ≠ 0)

theorem pivot_some (g : Fin m → ℤ) (hg : g ≠ 0) : ∃ e, pivot g = some e := by
  have hex : ∃ e, g e ≠ 0 := by
    by_contra! h
    exact hg (funext h)
  apply Option.isSome_iff_exists.mp
  apply List.find?_isSome.mpr
  obtain ⟨e, he⟩ := hex
  exact ⟨e, List.mem_ofFn.mpr ⟨e, rfl⟩, by simpa using he⟩

theorem pivot_ne_zero (g : Fin m → ℤ) (e : Fin m) (he : pivot g = some e) : g e ≠ 0 := by
  simpa using List.find?_some he

@[simp] theorem generator_zero (left right : Fin m → Fin n) : generator left right 0 = 0 := by
  have hf : (arcList m).find? (active (0 : Fin m → ℚ)) = none := by
    apply List.find?_eq_none.mpr
    intro a _
    simp [active]
  funext e
  simp only [generator, cycle, hf, List.map_nil, List.count_nil, Nat.cast_zero, mul_zero, Pi.zero_apply]

@[simp] theorem pivot_zero : pivot (0 : Fin m → ℤ) = none := by
  apply List.find?_eq_none.mpr
  intro e _
  simp

/-- Deterministic support elimination, using a fixed numeric round bound. -/
def decompose (left right : Fin m → Fin n) : ℕ → (Fin m → ℚ) → List (Term (Fin m))
  | 0, _ => []
  | fuel + 1, x =>
      let g := materializeInt (generator left right x)
      match pivot g with
      | none => []
      | some e =>
          let a := x e / (g e : ℚ)
          let r := materializeRat (KernelArithmetic.eliminate x (g, e))
          (a, g) :: decompose left right fuel r

@[simp] theorem decompose_zero (left right : Fin m → Fin n) (fuel : ℕ) :
    decompose left right fuel 0 = [] := by
  cases fuel <;> simp only [decompose, generator_zero, materializeInt_eq, pivot_zero]

/-- Exact deterministic decomposition with at most one generator per initial
support coordinate. Every returned integral row is an actual bounded kernel row. -/
theorem decompose_spec (left right : Fin m → Fin n) (fuel : ℕ) (x : Fin m → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (hfuel : (support x).card ≤ fuel) :
    ((decompose left right fuel x).map termVector).sum = x ∧
      (decompose left right fuel x).length ≤ (support x).card ∧
      ∀ t ∈ decompose left right fuel x,
        KernelBasis.IntegralKernel left right t.2 ∧ ∀ e, |t.2 e| ≤ 2 := by
  induction fuel generalizing x with
  | zero =>
      have hzero : x = 0 := by
        funext e
        by_contra he
        have hmem : e ∈ support x := (mem_support x e).mpr he
        have hpos := Finset.card_pos.mpr ⟨e, hmem⟩
        omega
      subst x
      simp
  | succ fuel ih =>
      by_cases hzero : x = 0
      · subst x
        simp
      · let g := materializeInt (generator left right x)
        have hg := generator_spec left right x hx hzero
        have hgspec : KernelBasis.IntegralKernel left right g ∧ (∀ e, |g e| ≤ 2) ∧
            g ≠ 0 ∧ ∀ e, x e = 0 → g e = 0 := by
          simpa only [g, materializeInt_eq] using hg
        obtain ⟨e, he⟩ := pivot_some g hgspec.2.2.1
        have hgne := pivot_ne_zero g e he
        have hge : (g e : ℚ) ≠ 0 := by exact_mod_cast hgne
        let a : ℚ := x e / (g e : ℚ)
        let r := materializeRat (KernelArithmetic.eliminate x (g, e))
        have hrdef : r = x - a • (fun f => (g f : ℚ)) := by
          change materializeRat (KernelArithmetic.eliminate x (g, e)) = _
          rw [materializeRat_eq]
          ext f
          rfl
        have hr : r ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
          rw [hrdef]
          exact (LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin).sub_mem hx
            ((LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin).smul_mem a
              ((KernelBasis.integralKernel_iff left right g).mp hgspec.1))
        have hre : r e = 0 := by simp [hrdef, a, div_mul_cancel₀ _ hge]
        have hxe : x e ≠ 0 := fun h => hgne (hgspec.2.2.2 e h)
        have hsubset : support r ⊆ support x := by
          intro f hf
          simp only [mem_support] at hf ⊢
          intro hxf
          have hgf := hgspec.2.2.2 f hxf
          exact hf (by simp [hrdef, hxf, hgf])
        have hlt : (support r).card < (support x).card := by
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
          intro heq
          have hmem : e ∈ support r := heq.symm ▸ (mem_support x e).mpr hxe
          exact (mem_support r e).mp hmem hre
        obtain ⟨heq, hlen, hb⟩ := ih r hr (by omega)
        have hdec : decompose left right (fuel + 1) x = (a, g) :: decompose left right fuel r := by
          change (match pivot g with
            | none => []
            | some j => (x j / (g j : ℚ), g) :: decompose left right fuel
                (materializeRat (KernelArithmetic.eliminate x (g, j)))) = _
          rw [he]
        rw [hdec]
        refine ⟨?_, by simp only [List.length_cons]; omega, ?_⟩
        · rw [List.map_cons, List.sum_cons, heq]
          ext f
          simp [termVector, hrdef]
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨hgspec.1, hgspec.2.1⟩
          · exact hb t ht

/-- Store the actual incidence transpose as the input matrix of elimination. -/
def incidenceArray (left right : Fin m → Fin n) : Vector (Vector ℚ m) n :=
  Vector.ofFn fun v => Vector.ofFn fun e => Incidence.unsigned left right e v

/-- Compute and materialize the rational incidence-kernel generators. -/
def initial (left right : Fin m → Fin n) : List (Fin m → ℚ) :=
  (StoredElimination.kernelGenerators (incidenceArray left right)).map StoredElimination.decode

theorem initial_eq (left right : Fin m → Fin n) :
    initial left right = ComputedKernel.rationalGenerators left right := by
  rw [initial, StoredElimination.decode_kernelGenerators]
  unfold ComputedKernel.rationalGenerators
  congr 1
  ext v e
  have hget {k : ℕ} {α : Type} (f : Fin k → α) (i : Fin k) :
      (Vector.ofFn f).get i = f i := by
    change (Vector.ofFn f)[i.val] = f i
    simp
  simp only [incidenceArray, hget, Matrix.transpose_apply]

/-- Deterministically generate the bounded integral candidate rows. -/
def candidates (left right : Fin m → Fin n) : List (Fin m → ℤ) :=
  (initial left right).flatMap fun x => (decompose left right m x).map Prod.snd

/-- The actual computed candidate list is quadratically bounded, consists of
bounded integral kernel rows, and spans the whole incidence kernel. -/
theorem candidates_spec (left right : Fin m → Fin n) :
    (candidates left right).length ≤ m * m ∧
      (∀ g ∈ candidates left right,
        KernelBasis.IntegralKernel left right g ∧ ∀ e, |g e| ≤ 2) ∧
      RationalElimination.listSpan ((candidates left right).map ComputedKernel.rationalRow) =
        LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  have hispan : RationalElimination.listSpan (initial left right) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
    rw [initial_eq]
    exact ComputedKernel.rationalGenerators_span left right
  have hilen : (initial left right).length = m := by
    rw [initial_eq]
    exact ComputedKernel.rationalGenerators_length left right
  have hkernel (x : Fin m → ℚ) (hx : x ∈ initial left right) :
      x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
    rw [← hispan]
    exact Submodule.subset_span hx
  have hspec (x : Fin m → ℚ) (hx : x ∈ initial left right) :=
    decompose_spec left right m x (hkernel x hx) (by simpa using Finset.card_le_univ (support x))
  have hb : ∀ g ∈ candidates left right,
      KernelBasis.IntegralKernel left right g ∧ ∀ e, |g e| ≤ 2 := by
    intro g hg
    obtain ⟨x, hx, hgx⟩ := List.mem_flatMap.mp hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hgx
    exact (hspec x hx).2.2 t ht
  refine ⟨?_, hb, ?_⟩
  · have hlength (l : List (Fin m → ℚ)) (hl : l ⊆ initial left right) :
        (l.flatMap fun x => (decompose left right m x).map Prod.snd).length ≤ l.length * m := by
      induction l with
      | nil => simp
      | cons x l ih =>
          have hx := hspec x (hl List.mem_cons_self)
          have hcard : (support x).card ≤ m := by simpa using Finset.card_le_univ (support x)
          have htail := ih (fun y hy => hl (List.mem_cons_of_mem x hy))
          simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
          nlinarith [hx.2.1]
    simpa only [candidates, hilen] using hlength (initial left right) (fun _ h => h)
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
      exact (KernelBasis.integralKernel_iff left right g).mp (hb g hg).1
    · rw [← hispan]
      apply Submodule.span_le.mpr
      intro x hx
      rw [← (hspec x hx).1]
      apply SparseKernel.term_sum_mem
      intro t ht
      apply Submodule.subset_span
      apply List.mem_map.mpr
      refine ⟨t.2, ?_, rfl⟩
      exact List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨t, ht, rfl⟩⟩

/-- The final integral complement, computed by the verified candidate scan. -/
def complement (left right : Fin m → Fin n) (rows : List (Fin m → ℚ)) : List (Fin m → ℤ) :=
  ComputedKernel.selectInteger rows (candidates left right)

/-- Deterministic construction of the exact number of bounded complement rows. -/
theorem complement_spec (left right : Fin m → Fin n)
    (hconn : Incidence.Connected left right) (hnot : ¬ Incidence.Bipartite left right)
    (rows : List (Fin m → ℚ))
    (hrows : RationalElimination.listSpan rows ≤
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    (∀ w ∈ complement left right rows,
      KernelBasis.IntegralKernel left right w ∧ ∀ e, |w e| ≤ 2) ∧
      (complement left right rows).length =
        m - n - Module.finrank ℚ (RationalElimination.listSpan rows) ∧
      RationalElimination.listSpan rows ⊔
          RationalElimination.listSpan ((complement left right rows).map ComputedKernel.rationalRow) =
        LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  have hspec := candidates_spec left right
  have hall : RationalElimination.listSpan (rows ++ (candidates left right).map ComputedKernel.rationalRow) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
    rw [DeterministicComplement.listSpan_append, hspec.2.2, sup_eq_right.mpr hrows]
  have hlen := DeterministicComplement.select_length rows
    ((candidates left right).map ComputedKernel.rationalRow)
  have hspan := DeterministicComplement.select_span rows
    ((candidates left right).map ComputedKernel.rationalRow)
  rw [← ComputedKernel.rational_selectInteger, List.length_map, hall,
    Incidence.left_kernel_finrank left right hconn hnot] at hlen
  rw [← ComputedKernel.rational_selectInteger, hall] at hspan
  refine ⟨?_, by simpa only [complement, Fintype.card_fin] using hlen, hspan⟩
  intro w hw
  exact hspec.2.1 w ((ComputedKernel.selectInteger_sublist rows _).subset hw)

end WeightedMIS.DeterministicKernel
