module

public import Mathlib

/-!
# A binary radix priority queue

Keys are explicitly stored binary words.  Insertion follows one bit at a time;
minimum extraction follows the leftmost occupied branch.  The returned counter
counts recursive trie-node inspections, including inspections of empty children.
Payloads are opaque and are linked into leaf lists without copying them.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch

inductive Bits : ℕ → Type
  | nil : Bits 0
  | cons {n : ℕ} (bit : Bool) (tail : Bits n) : Bits (n + 1)
  deriving DecidableEq, Repr

namespace Bits

def value : {n : ℕ} → Bits n → ℕ
  | _, .nil => 0
  | n + 1, .cons b tail => (if b then 2 ^ n else 0) + value tail

theorem value_lt : {n : ℕ} → (k : Bits n) → k.value < 2 ^ n
  | _, .nil => by simp [value]
  | n + 1, .cons b tail => by
    have ih := value_lt tail
    cases b <;> simp only [value, Bool.false_eq_true, ↓reduceIte,
      pow_succ] <;> omega

end Bits

/-- An uncompressed binary trie.  Empty subtrees have one shared constructor. -/
inductive Radix (α : Type*) : ℕ → Type _
  | empty {n : ℕ} : Radix α n
  | bucket (xs : List α) : Radix α 0
  | fork {n : ℕ} (left right : Radix α n) : Radix α (n + 1)

namespace Radix

variable {α : Type*}

def emptyRoot : {n : ℕ} → Radix α n → Bool
  | _, .empty => true
  | _, _ => false

def canonical : {n : ℕ} → Radix α n → Prop
  | _, .empty => True
  | _, .bucket xs => xs ≠ []
  | _, .fork l r => canonical l ∧ canonical r ∧
      (emptyRoot l = false ∨ emptyRoot r = false)

def leaf (xs : List α) : Radix α 0 :=
  match xs with
  | [] => .empty
  | _ :: _ => .bucket xs

def join {n : ℕ} (l r : Radix α n) : Radix α (n + 1) :=
  if emptyRoot l && emptyRoot r then .empty else .fork l r

def elements : {n : ℕ} → Radix α n → List (Bits n × α)
  | _, .empty => []
  | _, .bucket xs => xs.map (fun x => (Bits.nil, x))
  | _, .fork l r =>
      (elements l).map (fun x => (Bits.cons false x.1, x.2)) ++
      (elements r).map (fun x => (Bits.cons true x.1, x.2))

@[simp] theorem elements_leaf (xs : List α) :
    elements (leaf xs) = xs.map (fun x => (Bits.nil, x)) := by
  cases xs <;> rfl

theorem emptyRoot_elements {n : ℕ} (t : Radix α n) (h : emptyRoot t = true) :
    elements t = [] := by
  cases t <;> simp_all [emptyRoot, elements]

@[simp] theorem elements_join {n : ℕ} (l r : Radix α n) :
    elements (join l r) =
      (elements l).map (fun x => (Bits.cons false x.1, x.2)) ++
      (elements r).map (fun x => (Bits.cons true x.1, x.2)) := by
  unfold join
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    simp [elements, emptyRoot_elements l h.1, emptyRoot_elements r h.2]
  · rfl

theorem canonical_leaf (xs : List α) : canonical (leaf xs) := by
  cases xs <;> simp [leaf, canonical]

theorem canonical_join {n : ℕ} {l r : Radix α n}
    (hl : canonical l) (hr : canonical r) : canonical (join l r) := by
  unfold join
  split
  · trivial
  · rename_i h
    simp only [Bool.and_eq_true, not_and_or, Bool.not_eq_true] at h
    exact ⟨hl, hr, h⟩

/-- Each recursive call inspects one stored key bit and one trie node. -/
def insert : {n : ℕ} → Bits n → α → Radix α n → Radix α n × ℕ
  | 0, .nil, a, .empty => (.bucket [a], 1)
  | 0, .nil, a, .bucket xs => (.bucket (a :: xs), 1)
  | n + 1, .cons b key, a, .empty =>
      let result :=  insert key a (.empty : Radix α n)
      (if b then .fork .empty result.1 else .fork result.1 .empty, result.2 + 1)
  | _ + 1, .cons b key, a, .fork l r =>
      if b then
        let result :=  insert key a r
        (.fork l result.1, result.2 + 1)
      else
        let result :=  insert key a l
        (.fork result.1 r, result.2 + 1)

theorem insert_steps {n : ℕ} (key : Bits n) (a : α) (t : Radix α n) :
    (insert key a t).2 = n + 1 := by
  induction key with
  | nil => cases t <;> rfl
  | @cons n b key ih =>
    cases t with
    | empty => simp [insert, ih]
    | fork l r => cases b <;> simp [insert, ih]

theorem insert_nonempty {n : ℕ} (key : Bits n) (a : α) (t : Radix α n) :
    emptyRoot (insert key a t).1 = false := by
  cases key with
  | nil => cases t <;> rfl
  | cons b key =>
    cases t with
    | empty => cases b <;> rfl
    | fork l r => cases b <;> rfl

theorem insert_canonical {n : ℕ} (key : Bits n) (a : α) (t : Radix α n)
    (ht : canonical t) : canonical (insert key a t).1 := by
  induction key with
  | nil => cases t <;> simp [insert, canonical]
  | @cons n b key ih =>
    cases t with
    | empty =>
      have hi := ih (.empty : Radix α n) trivial
      have hn := insert_nonempty key a (.empty : Radix α n)
      cases b <;> simp [insert, canonical, hi, hn]
    | fork l r =>
      obtain ⟨hl, hr, _⟩ := ht
      have hil := ih l hl
      have hir := ih r hr
      have hnl := insert_nonempty key a l
      have hnr := insert_nonempty key a r
      cases b <;> simp [insert, canonical, hl, hr, hil, hir, hnl, hnr]

/-- Minimum extraction; the counter includes a failed inspection of an empty
left child before descending through the right child. -/
def pop : {n : ℕ} → Radix α n → Option (Bits n × α × Radix α n) × ℕ
  | _, .empty => (none, 1)
  | _, .bucket [] => (none, 1)
  | _, .bucket (a :: xs) => (some (.nil, a, leaf xs), 1)
  | _, .fork l r =>
      let lp := pop l
      match lp.1 with
      | some (key, a, l') => (some (.cons false key, a, join l' r), lp.2 + 1)
      | none =>
          let rp := pop r
          match rp.1 with
          | some (key, a, r') => (some (.cons true key, a, join l r'), lp.2 + rp.2 + 1)
          | none => (none, lp.2 + rp.2 + 1)

theorem pop_none {n : ℕ} (t : Radix α n) :
    (pop t).1 = none ↔ elements t = [] := by
  induction t with
  | empty => simp [pop, elements]
  | bucket xs => cases xs <;> simp [pop, elements]
  | fork l r ihl ihr =>
    simp only [pop, elements]
    split
    · rename_i hl
      have hel : elements l ≠ [] := by
        intro he
        have hnl := ihl.mpr he
        rw [hl] at hnl
        contradiction
      simp [hel]
    · rename_i hl
      have hel := ihl.mp hl
      split
      · rename_i hr
        have her : elements r ≠ [] := by
          intro he
          have hnr := ihr.mpr he
          rw [hr] at hnr
          contradiction
        simp [hel, her]
      · rename_i hr
        simp [hel, ihr.mp hr]

theorem canonical_empty {n : ℕ} (t : Radix α n) (ht : canonical t)
    (he : elements t = []) : t = .empty := by
  induction t with
  | empty => rfl
  | bucket xs =>
    have hx : xs = [] := by simpa [elements] using he
    exact (ht hx).elim
  | fork l r ihl ihr =>
    simp only [elements, List.append_eq_nil_iff, List.map_eq_nil_iff] at he
    have hl := ihl ht.1 he.1
    have hr := ihr ht.2.1 he.2
    subst l
    subst r
    simp [canonical, emptyRoot] at ht

theorem pop_steps {n : ℕ} (t : Radix α n) (ht : canonical t) :
    (pop t).2 ≤ 2 * n + 1 := by
  induction t with
  | empty => simp [pop]
  | bucket xs => cases xs <;> simp [pop]
  | @fork n l r ihl ihr =>
    have hcl := ihl ht.1
    have hcr := ihr ht.2.1
    cases hl : (pop l).1 with
    | some result =>
      obtain ⟨key, a, l'⟩ := result
      simp only [pop, hl]
      omega
    | none =>
      have hel := canonical_empty l ht.1 ((pop_none l).mp hl)
      subst l
      cases hr : (pop r).1 with
      | some result =>
        obtain ⟨key, a, r'⟩ := result
        simp only [pop, hr]
        omega
      | none =>
        have her := canonical_empty r ht.2.1 ((pop_none r).mp hr)
        subst r
        simp [canonical, emptyRoot] at ht

theorem pop_canonical {n : ℕ} (t : Radix α n) (ht : canonical t)
    {key : Bits n} {a : α} {t' : Radix α n}
    (hpop : (pop t).1 = some (key, a, t')) : canonical t' := by
  induction t with
  | empty => simp [pop] at hpop
  | bucket xs =>
    cases xs with
    | nil => simp [pop] at hpop
    | cons x xs =>
      simp only [pop, Option.some.injEq, Prod.mk.injEq] at hpop
      rw [← hpop.2.2]
      exact canonical_leaf xs
  | fork l r ihl ihr =>
    simp only [pop] at hpop
    split at hpop
    · rename_i key₀ a₀ l' hl
      simp only [Option.some.injEq, Prod.mk.injEq] at hpop
      rcases hpop with ⟨rfl, rfl, rfl⟩
      exact canonical_join (ihl ht.1 hl) ht.2.1
    · split at hpop
      · rename_i key₀ a₀ r' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hpop
        rcases hpop with ⟨rfl, rfl, rfl⟩
        exact canonical_join ht.1 (ihr ht.2.1 hr)
      · simp at hpop

theorem pop_elements {n : ℕ} (t : Radix α n)
    {key : Bits n} {a : α} {t' : Radix α n}
    (hpop : (pop t).1 = some (key, a, t')) :
    elements t = (key, a) :: elements t' := by
  induction t with
  | empty => simp [pop] at hpop
  | bucket xs =>
    cases xs with
    | nil => simp [pop] at hpop
    | cons x xs =>
      simp only [pop, Option.some.injEq, Prod.mk.injEq] at hpop
      rcases hpop with ⟨rfl, rfl, rfl⟩
      simp [elements]
  | fork l r ihl ihr =>
    simp only [pop] at hpop
    split at hpop
    · rename_i key₀ a₀ l' hl
      simp only [Option.some.injEq, Prod.mk.injEq] at hpop
      rcases hpop with ⟨rfl, rfl, rfl⟩
      simp [elements, ihl hl]
    · rename_i hl
      have hel := (pop_none l).mp hl
      split at hpop
      · rename_i key₀ a₀ r' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hpop
        rcases hpop with ⟨rfl, rfl, rfl⟩
        simp [elements, hel, ihr hr]
      · simp at hpop

theorem insert_size {n : ℕ} (key : Bits n) (a : α) (t : Radix α n) :
    (elements (insert key a t).1).length = (elements t).length + 1 := by
  induction key with
  | nil => cases t <;> simp [insert, elements]
  | cons b key ih =>
    cases t with
    | empty => cases b <;> simp [insert, elements, ih]
    | fork l r =>
      cases b <;> simp [insert, elements, ih] <;> omega

theorem elements_sorted {n : ℕ} (t : Radix α n) :
    (elements t).Pairwise (fun x y => x.1.value ≤ y.1.value) := by
  induction t with
  | empty => simp [elements]
  | bucket xs =>
    simp only [elements, List.pairwise_map, Bits.value]
    exact List.pairwise_of_forall (by intro a b; exact le_rfl)
  | @fork n l r ihl ihr =>
    simp only [elements, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact ihl.map _ (by intro a b hab; simpa [Bits.value] using hab)
    · exact ihr.map _ (by intro a b hab; simpa [Bits.value] using hab)
    · intro a ha b hb
      obtain ⟨a₀, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b₀, _, rfl⟩ := List.mem_map.mp hb
      have ha₀ := Bits.value_lt a₀.1
      simp only [Bits.value, Bool.false_eq_true, ↓reduceIte, zero_add]
      omega

theorem pop_minimum {n : ℕ} (t : Radix α n)
    {key : Bits n} {a : α} {t' : Radix α n}
    (hpop : (pop t).1 = some (key, a, t'))
    {other : Bits n × α} (hother : other ∈ elements t) :
    key.value ≤ other.1.value := by
  have hs := elements_sorted t
  rw [pop_elements t hpop] at hs hother
  rcases List.mem_cons.mp hother with heq | hmem
  · rw [heq]
  · exact (List.pairwise_cons.mp hs).1 other hmem

theorem mem_insert {n : ℕ} (key : Bits n) (a : α) (t : Radix α n)
    (q : Bits n × α) :
    q ∈ elements (insert key a t).1 ↔ q = (key, a) ∨ q ∈ elements t := by
  induction key with
  | nil =>
    obtain ⟨qkey, qa⟩ := q
    cases qkey
    cases t <;> simp [insert, elements, eq_comm]
  | @cons n b key ih =>
    obtain ⟨qkey, qa⟩ := q
    cases qkey with
    | cons qb qkey =>
      cases t with
      | empty =>
        cases b <;> cases qb <;>
          simp [insert, elements, List.mem_map, Bits.cons.injEq, ih, eq_comm]
      | fork l r =>
        cases b <;> cases qb <;>
          simp [insert, elements, List.mem_map, Bits.cons.injEq, ih, eq_comm, or_comm]

/-- Trie lookup examines at most one branch for each bit of the key. -/
def lookup : {n : ℕ} → Bits n → Radix α n → List α × ℕ
  | _, _, .empty => ([], 1)
  | 0, .nil, .bucket xs => (xs, 1)
  | _ + 1, .cons b key, .fork l r =>
      let result := lookup key (if b then r else l)
      (result.1, result.2 + 1)

theorem lookup_steps {n : ℕ} (key : Bits n) (t : Radix α n) :
    (lookup key t).2 ≤ n + 1 := by
  induction key with
  | nil => cases t <;> simp [lookup]
  | cons b key ih =>
    cases t with
    | empty => simp [lookup]
    | fork l r =>
      cases b <;> simp only [lookup, Bool.false_eq_true, ↓reduceIte]
      · have h := ih l; omega
      · have h := ih r; omega

theorem mem_lookup {n : ℕ} (key : Bits n) (t : Radix α n) (a : α) :
    a ∈ (lookup key t).1 ↔ (key, a) ∈ elements t := by
  induction key with
  | nil => cases t <;> simp [lookup, elements]
  | cons b key ih =>
    cases t with
    | empty => simp [lookup, elements]
    | fork l r =>
      cases b <;> simp [lookup, elements, List.mem_map, Bits.cons.injEq, ih, eq_comm]

theorem lookup_insert_empty {n : ℕ} (key query : Bits n) (a : α) (t : Radix α n) :
    (lookup query (insert key a t).1).1 = [] ↔
      query ≠ key ∧ (lookup query t).1 = [] := by
  simp only [List.eq_nil_iff_forall_not_mem, mem_lookup, mem_insert, Prod.mk.injEq]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro heq
      exact h a (Or.inl ⟨heq, rfl⟩)
    · intro x hx
      exact h x (Or.inr hx)
  · rintro ⟨hne, hnil⟩ x (⟨heq, _⟩ | hmem)
    · exact hne heq
    · exact hnil x hmem

theorem lookup_insert {n : ℕ} (key query : Bits n) (a : α) (t : Radix α n) :
    (lookup query (insert key a t).1).1 =
      if query = key then a :: (lookup query t).1 else (lookup query t).1 := by
  induction key with
  | nil => cases query; cases t <;> rfl
  | cons b key ih =>
    cases query with
    | cons qb query =>
      cases t with
      | empty =>
        cases b <;> cases qb <;> simp [insert, lookup, ih, Bits.cons.injEq]
      | fork l r =>
        cases b <;> cases qb <;> simp [insert, lookup, ih, Bits.cons.injEq]

theorem lookup_length {n : ℕ} (key : Bits n) (t : Radix α n) :
    (lookup key t).1.length = ((elements t).filter (fun x => x.1 == key)).length := by
  induction key with
  | nil => cases t <;> simp [lookup, elements, List.filter_map, Function.comp_def]
  | cons b key ih =>
    cases t with
    | empty => simp [lookup, elements]
    | fork l r =>
      cases b <;>
        simp [lookup, elements, List.filter_append, List.filter_map,
          Bits.cons.injEq, ih, List.length_map, Function.comp_def, Bool.beq_eq_decide_eq]

/-- Count entries without materializing keys or concatenating flattened lists.
The counter charges each trie node and each payload-list cell. -/
def countEntries : {n : ℕ} → Radix α n → ℕ × ℕ
  | _, .empty => (0, 1)
  | _, .bucket xs => (xs.length, xs.length + 1)
  | _, .fork l r =>
      let lc := countEntries l
      let rc := countEntries r
      (lc.1 + rc.1, lc.2 + rc.2 + 1)

theorem countEntries_value {n : ℕ} (t : Radix α n) :
    (countEntries t).1 = (elements t).length := by
  induction t <;> simp [countEntries, elements, *]

theorem countEntries_steps {n : ℕ} (t : Radix α n) (ht : canonical t) :
    (countEntries t).2 ≤ (2 * n + 1) * (elements t).length + 1 := by
  induction t with
  | empty => simp [countEntries, elements]
  | bucket xs => simp [countEntries, elements]
  | @fork n l r ihl ihr =>
    have hl := ihl ht.1
    have hr := ihr ht.2.1
    have hnonempty : (elements l).length + (elements r).length ≥ 1 := by
      by_contra h
      have hel : elements l = [] := List.length_eq_zero_iff.mp (by omega)
      have her : elements r = [] := List.length_eq_zero_iff.mp (by omega)
      have hl0 := canonical_empty l ht.1 hel
      have hr0 := canonical_empty r ht.2.1 her
      subst l
      subst r
      simp [canonical, emptyRoot] at ht
    simp only [countEntries, elements, List.length_append, List.length_map]
    nlinarith

end Radix

end WeightedMIS.EfficientSearch
