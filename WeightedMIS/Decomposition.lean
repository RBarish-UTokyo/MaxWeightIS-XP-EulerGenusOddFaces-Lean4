module

public import WeightedMIS.Walks

/-!
# Decomposition of nonnegative integral signed-stub flows

The converse direction of Lemma 9 is proved by consuming a finite list of edge
copies. An open walk can always continue unless it has returned to its anchor:
the unused column sum records the difference of the endpoint potentials.
-/

@[expose] public section

namespace WeightedMIS.Decomposition

open WeightedMIS.Walks

variable {Row Edge : Type*} [DecidableEq Row]

/-- An arc with the indicated original-edge label starts at the given state. -/
def HasSource (C : Edge → Column Row) (e : Edge) (v : State Row) : Prop :=
  ∃ a : Arc C, a.val.1 = e ∧ source C a = v

omit [DecidableEq Row] in
private theorem one_hub_source (C : Edge → Column Row) (e : Edge) (s : Stub Row)
    (hc : C e = .one s) : HasSource C e none := by
  exact ⟨⟨(e, false), Or.inr rfl⟩, rfl, by simp [source, hc]⟩

omit [DecidableEq Row] in
private theorem one_stub_source (C : Edge → Column Row) (e : Edge) (s : Stub Row)
    (hc : C e = .one s) : HasSource C e (some (opposite s)) := by
  exact ⟨⟨(e, true), Or.inl (by simp [hc])⟩, rfl, by simp [source, hc]⟩

omit [DecidableEq Row] in
private theorem two_first_source (C : Edge → Column Row) (e : Edge) (s t : Stub Row)
    (hc : C e = .two s t) : HasSource C e (some (opposite s)) := by
  exact ⟨⟨(e, false), Or.inr rfl⟩, rfl, by simp [source, hc]⟩

omit [DecidableEq Row] in
private theorem two_second_source (C : Edge → Column Row) (e : Edge) (s t : Stub Row)
    (hc : C e = .two s t) : HasSource C e (some (opposite t)) := by
  exact ⟨⟨(e, true), Or.inl (by simp [hc])⟩, rfl, by simp [source, hc]⟩

private theorem stub_nonneg (s : Stub Row) (r : Row)
    (h : some (opposite s) ≠ some (r, true)) : 0 ≤ potential (some s) r := by
  rcases s with ⟨v, b⟩
  cases b <;> by_cases hr : r = v <;> simp_all [potential, opposite, signValue]

private theorem stub_nonpos (s : Stub Row) (r : Row)
    (h : some (opposite s) ≠ some (r, false)) : potential (some s) r ≤ 0 := by
  rcases s with ⟨v, b⟩
  cases b <;> by_cases hr : r = v <;> simp_all [potential, opposite, signValue]

private theorem column_nonneg_of_no_source (C : Edge → Column Row) (e : Edge) (r : Row)
    (h : ¬ HasSource C e (some (r, true))) : 0 ≤ columnVector (C e) r := by
  cases hc : C e with
  | zero => simp [columnVector]
  | one s =>
    apply stub_nonneg
    intro hs
    exact h (hs ▸ one_stub_source C e s hc)
  | two s t =>
    apply add_nonneg
    · apply stub_nonneg
      intro hs
      exact h (hs ▸ two_first_source C e s t hc)
    · apply stub_nonneg
      intro hs
      exact h (hs ▸ two_second_source C e s t hc)

private theorem column_nonpos_of_no_source (C : Edge → Column Row) (e : Edge) (r : Row)
    (h : ¬ HasSource C e (some (r, false))) : columnVector (C e) r ≤ 0 := by
  cases hc : C e with
  | zero => simp [columnVector]
  | one s =>
    apply stub_nonpos
    intro hs
    exact h (hs ▸ one_stub_source C e s hc)
  | two s t =>
    apply add_nonpos
    · apply stub_nonpos
      intro hs
      exact h (hs ▸ two_first_source C e s t hc)
    · apply stub_nonpos
      intro hs
      exact h (hs ▸ two_second_source C e s t hc)

private theorem potential_lt_one (u : State Row) (r : Row)
    (h : u ≠ some (r, true)) : potential u r < 1 := by
  cases u with
  | none => simp [potential]
  | some s =>
    rcases s with ⟨v, b⟩
    cases b <;> by_cases hr : r = v <;> simp_all [potential, signValue]

private theorem neg_one_lt_potential (u : State Row) (r : Row)
    (h : u ≠ some (r, false)) : -1 < potential u r := by
  cases u with
  | none => simp [potential]
  | some s =>
    rcases s with ⟨v, b⟩
    cases b <;> by_cases hr : r = v <;> simp_all [potential, signValue]

private theorem potential_sum_some [Fintype Row] (s : Stub Row) :
    (∑ r, potential (some s) r) = signValue s.2 := by
  simp [potential]

private theorem column_total_even [Fintype Row] (C : Edge → Column Row) (e : Edge)
    (h : ¬ HasSource C e none) : (∑ r, columnVector (C e) r) % 2 = 0 := by
  cases hc : C e with
  | zero => simp [columnVector]
  | one s => exact False.elim (h (one_hub_source C e s hc))
  | two s t =>
    simp only [columnVector, Finset.sum_add_distrib, potential_sum_some]
    rcases s with ⟨r, b⟩
    rcases t with ⟨v, c⟩
    cases b <;> cases c <;> norm_num [signValue]

private theorem sum_rows_list [Fintype Row] (C : Edge → Column Row) (l : List Edge) :
    (∑ r, (l.map (fun e => columnVector (C e) r)).sum) =
      (l.map (fun e => ∑ r, columnVector (C e) r)).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp [Finset.sum_add_distrib, ih]

private theorem list_total_even [Fintype Row] (C : Edge → Column Row) (l : List Edge)
    (h : ∀ e ∈ l, ¬ HasSource C e none) :
    (l.map (fun e => ∑ r, columnVector (C e) r)).sum % 2 = 0 := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have he := column_total_even C e (h e List.mem_cons_self)
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem e ha))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- If unused columns equal the difference between the anchor potential and
current potential, a nonclosed partial walk has an unused outgoing arc. -/
theorem exists_outgoing [Fintype Row] (C : Edge → Column Row) (l : List Edge)
    (u v : State Row) (hne : u ≠ v)
    (hsum : ∀ r, (l.map (fun e => columnVector (C e) r)).sum =
      potential u r - potential v r) :
    ∃ e ∈ l, HasSource C e v := by
  by_contra! hn
  cases v with
  | none =>
    have heven := list_total_even C l hn
    rw [← sum_rows_list] at heven
    simp_rw [hsum] at heven
    cases u with
    | none => exact hne rfl
    | some s =>
      simp only [potential, sub_zero] at heven
      have hp := potential_sum_some s
      change (∑ r, potential (some s) r) % 2 = 0 at heven
      rw [hp] at heven
      rcases s with ⟨r, b⟩
      cases b <;> norm_num [signValue] at heven
  | some s =>
    rcases s with ⟨r, b⟩
    cases b with
    | false =>
      have hnonpos : (l.map (fun e => columnVector (C e) r)).sum ≤ 0 := by
        have hh : ∀ e ∈ l, columnVector (C e) r ≤ 0 :=
          fun e he => column_nonpos_of_no_source C e r (hn e he)
        clear hsum hne hn
        induction l with
        | nil => simp
        | cons e l ih =>
          simp only [List.map_cons, List.sum_cons]
          exact add_nonpos (hh e List.mem_cons_self)
            (ih (fun a ha => hh a (List.mem_cons_of_mem e ha)))
      have hp := neg_one_lt_potential u r hne
      have hs := hsum r
      have hv : potential (some (r, false)) r = -1 := by simp [potential, signValue]
      rw [hv] at hs
      omega
    | true =>
      have hnonneg : 0 ≤ (l.map (fun e => columnVector (C e) r)).sum := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact column_nonneg_of_no_source C e r (hn e he)
      have hp := potential_lt_one u r hne
      have hs := hsum r
      have hv : potential (some (r, true)) r = 1 := by simp [potential, signValue]
      rw [hv] at hs
      omega

/-- Complete an open walk using some of the unused edge copies. The remaining
copies have zero column sum. Multiplicities are preserved by a list permutation. -/
theorem complete_walk [Fintype Row] [DecidableEq Edge]
    (C : Edge → Column Row) (l : List Edge) (u v : State Row)
    (hsum : ∀ r, (l.map (fun e => columnVector (C e) r)).sum =
      potential u r - potential v r) :
    ∃ w : Walk C v u, ∃ rest : List Edge,
      l.Perm (w.labels ++ rest) ∧
      ∀ r, (rest.map (fun e => columnVector (C e) r)).sum = 0 := by
  by_cases huv : u = v
  · subst v
    refine ⟨.nil u, l, ?_, ?_⟩
    · simp [Walk.labels]
    · intro r
      simpa using hsum r
  · obtain ⟨e, he, a, ha, hv⟩ := exists_outgoing C l u v huv hsum
    subst e
    subst v
    have hp := List.perm_cons_erase he
    have hrem : ∀ r, ((l.erase a.val.1).map
        (fun e => columnVector (C e) r)).sum =
        potential u r - potential (target C a) r := by
      intro r
      have hh := (hp.map (fun e => columnVector (C e) r)).sum_eq
      simp only [List.map_cons, List.sum_cons] at hh
      have hs := hsum r
      have hc := arc_potential C a r
      omega
    obtain ⟨w, rest, hw, hz⟩ :=
      complete_walk C (l.erase a.val.1) u (target C a) hrem
    refine ⟨.cons a w, rest, ?_, hz⟩
    simpa [Walk.labels] using hp.trans (List.Perm.cons a.val.1 hw)
termination_by l.length
decreasing_by
  have hlen := List.length_erase_of_mem he
  have hpos : 0 < l.length := List.length_pos_of_mem he
  omega

/-- Converse of Lemma 9 for a list of distinct edge copies represented by
possibly repeated labels. Every copy occurs in exactly one closed walk. -/
theorem decompose_balanced_list [Fintype Row] [DecidableEq Edge]
    (C : Edge → Column Row) (l : List Edge)
    (hzero : ∀ r, (l.map (fun e => columnVector (C e) r)).sum = 0) :
    ∃ ws : List (ClosedWalk C), l.Perm (ws.flatMap (fun w => w.2.labels)) := by
  cases l with
  | nil => exact ⟨[], by simp⟩
  | cons e l =>
    let a : Arc C := ⟨(e, false), Or.inr rfl⟩
    have hrem : ∀ r, (l.map (fun e => columnVector (C e) r)).sum =
        potential (source C a) r - potential (target C a) r := by
      intro r
      have hz := hzero r
      simp only [List.map_cons, List.sum_cons] at hz
      have hc := arc_potential C a r
      change columnVector (C e) r = _ at hc
      omega
    obtain ⟨w, rest, hp, hz⟩ :=
      complete_walk C l (source C a) (target C a) hrem
    obtain ⟨ws, hws⟩ := decompose_balanced_list C rest hz
    refine ⟨⟨source C a, .cons a w⟩ :: ws, ?_⟩
    have hfirst := List.Perm.cons e hp
    have hsecond := List.Perm.append_left (e :: w.labels) hws
    simpa [List.flatMap_cons, Walk.labels, a] using hfirst.trans hsecond
termination_by l.length
decreasing_by
  have hlen := hp.length_eq
  simp_all only [List.length_cons, List.length_append]
  omega

/-- A finite list containing the prescribed nonnegative multiplicity of each
edge. The order is irrelevant to the decomposition statement. -/
noncomputable def edgeCopies [Fintype Edge] (y : Edge → ℕ) : List Edge :=
  Finset.univ.toList.flatMap (fun e => List.replicate (y e) e)

/-- The edge-copy list has exactly the prescribed multiplicities. -/
theorem edgeCopies_projection [Fintype Edge] [DecidableEq Edge]
    (y : Edge → ℕ) (e : Edge) : projection (edgeCopies y) e = y e := by
  simp only [projection, edgeCopies, List.count_flatMap, Function.comp_def,
    List.count_replicate, beq_iff_eq]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
  simp

/-- The full nonnegative integral converse of Lemma 9: each edge appears
exactly `y e` times, and the total number of arcs is exactly `∑ e, y e`.
The existence of a decomposition is proved, not supplied as a hypothesis. -/
theorem decompose_flow [Fintype Row] [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (y : Edge → ℕ)
    (hzero : ∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0) :
    ∃ ws : List (ClosedWalk C),
      (∀ e, projection (ws.flatMap (fun w => w.2.labels)) e = y e) ∧
      (ws.map (fun w => w.2.labels.length)).sum = ∑ e, y e := by
  have hz : ∀ r, ((edgeCopies y).map (fun e => columnVector (C e) r)).sum = 0 := by
    intro r
    rw [← sum_mul_projection]
    simp_rw [edgeCopies_projection]
    exact hzero r
  obtain ⟨ws, hp⟩ := decompose_balanced_list C (edgeCopies y) hz
  have hc : ∀ e, projection (ws.flatMap (fun w => w.2.labels)) e = y e := by
    intro e
    have he := hp.count_eq e
    change projection (edgeCopies y) e = _ at he
    rw [edgeCopies_projection] at he
    exact he.symm
  refine ⟨ws, hc, ?_⟩
  rw [← List.length_flatMap, ← sum_projection_eq_length]
  simp_rw [hc]

/-- Exact equivalence between nonnegative integral local flows and projections
of finite families of directed closed walks. -/
theorem flow_iff_decomposition [Fintype Row] [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (y : Edge → ℕ) :
    (∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0) ↔
      ∃ ws : List (ClosedWalk C),
        ∀ e, projection (ws.flatMap (fun w => w.2.labels)) e = y e := by
  constructor
  · intro hz
    obtain ⟨ws, hp, _⟩ := decompose_flow C y hz
    exact ⟨ws, hp⟩
  · rintro ⟨ws, hp⟩ r
    have hz := closed_walks_projection_kernel ws r
    simp_rw [hp] at hz
    exact hz

end WeightedMIS.Decomposition
