import PEqualNP.Defs

namespace PEqualNP.Contributions.WireSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The support construction and oneEach identity are from L_meta_19123.
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

/-- Only the wires of a set of at most `|R| + |gs|` wires decide the wires in `R`. -/
theorem cone (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    ∃ R' : Finset ℕ, R'.card ≤ R.card + gs.length ∧ ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R', x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => exact ⟨R, by simp, fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ g.inputs.toFinset else R
    obtain ⟨R', hc, hR'⟩ := ih hg' R0
    refine ⟨R', ?_, ?_⟩
    · have : R0.card ≤ R.card + 1 := by
        simp only [R0]; split_ifs with ht
        · have := Finset.card_union_le (R.erase t) g.inputs.toFinset
          have := Finset.card_erase_of_mem ht
          have := List.toFinset_card_le g.inputs
          have : 0 < R.card := Finset.card_pos.2 ⟨t, ht⟩
          omega
        · omega
      simp; omega
    · intro x y hx hy hxy w hw
      have e := hR' x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      rw [getD_snoc, getD_snoc, len, len, hx, hy]
      split_ifs with h1 h3
      · exact e w (by simp only [R0]; split_ifs <;> simp_all; omega)
      · have ht : t ∈ R := by simp only [t]; rw [← h3]; exact hw
        congr 1
        refine List.map_congr_left fun i hi => e i ?_
        simp [R0, ht, hi]
      · rfl

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

end PEqualNP.Contributions.WireSupport

open PEqualNP.Contributions.WireSupport PEqualNP.Represents in
theorem PEqualNP.Contributions.distinctTableLowerBound : ∀ (n : ℕ) (A : Fin n → Fin n → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ n → (∀ u u' : Fin n, u ≠ u' → ∃ v, A u v ≠ A u' v) → (∀ v v' : Fin n, v ≠ v' → ∃ u, A u v ≠ A u v') → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → 2 * n - 3 ≤ C.size := by
  intro n A C hn hr hc hf rep
  classical
  obtain ⟨R, hcard, hdep⟩ := cone (n+n) C.gates (fun g hg => (hf g hg).2) {C.output}
  have dep (u v u' v' : Fin n)
      (agree : ∀ k ∈ R, (k = u.val ∨ k = n+v.val) ↔ (k = u'.val ∨ k = n+v'.val)) :
      A u v = A u' v' := by
    rw [← rep u v, ← rep u' v']
    apply hdep _ _ (by simp [oneEach]) (by simp [oneEach]) _ _ (by simp)
    intro k hk
    exact Bool.eq_iff_iff.mpr (by simpa only [oe] using agree k hk)
  have left (a b : Fin n) (ha : a.val ∉ R) (hb : b.val ∉ R) : a = b := by
    by_contra ne
    obtain ⟨v, hv⟩ := hr a b ne
    apply hv
    apply dep
    intro k hk
    have ea : k ≠ a.val := fun e => ha (e ▸ hk)
    have eb : k ≠ b.val := fun e => hb (e ▸ hk)
    simp [ea, eb]
  have right (a b : Fin n) (ha : n + a.val ∉ R) (hb : n + b.val ∉ R) : a = b := by
    by_contra ne
    obtain ⟨u, hu⟩ := hc a b ne
    apply hu
    apply dep
    intro k hk
    have ea : k ≠ n+a.val := fun e => ha (e ▸ hk)
    have eb : k ≠ n+b.val := fun e => hb (e ▸ hk)
    simp [ea, eb]
  have exceptional (f : Fin n → ℕ) (ht : ∀ a b, f a ∉ R → f b ∉ R → a = b) :
      ∃ e : Fin n, ∀ a : Fin n, f a ∉ R → a = e := by
    by_cases h : ∃ a, f a ∉ R
    · obtain ⟨e, he⟩ := h
      exact ⟨e, fun a ha => ht a e ha he⟩
    · exact ⟨⟨0, by omega⟩, fun a ha => False.elim (h ⟨a, ha⟩)⟩
  obtain ⟨i, hi⟩ := exceptional (fun a => a.val) left
  obtain ⟨j, hj⟩ := exceptional (fun b => n+b.val) right
  have sub : Finset.range (n+n) ⊆ insert i.val (insert (n+j.val) R) := by
    intro k hk
    have hlt := Finset.mem_range.mp hk
    by_cases inside : k ∈ R
    · simp [inside]
    by_cases small : k < n
    · have h := hi ⟨k,small⟩ inside
      have eqv := congrArg Fin.val h
      simp only at eqv
      simp [eqv]
    · let b : Fin n := ⟨k-n, by omega⟩
      have hb : n+b.val = k := by dsimp [b]; omega
      have h := hj b (by simpa only [hb] using inside)
      have eqv := congrArg Fin.val h
      have : k = n+j.val := by omega
      simp [this]
  have hcount := Finset.card_le_card sub
  have h1 := Finset.card_insert_le i.val (insert (n+j.val) R)
  have h2 := Finset.card_insert_le (n+j.val) R
  simp only [Finset.card_singleton] at hcard
  rw [Finset.card_range] at hcount
  change 2*n-3 ≤ C.gates.length
  omega

theorem PEqualNP.Contributions.noSixGateFiveByFive : ¬ (∃ (A : Fin 5 → Fin 5 → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ u u' : Fin 5, u ≠ u' → ∃ v, A u v ≠ A u' v) ∧ (∀ v v' : Fin 5, v ≠ v' → ∃ u, A u v ≠ A u v') ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents A C) := by
  rintro ⟨A,C,hr,hc,hf,hs,rep⟩
  have h := PEqualNP.Contributions.distinctTableLowerBound 5 A C (by decide) hr hc hf rep
  omega

namespace PEqualNP.Contributions.DiagonalMatching
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def gs (n : ℕ) : ℕ → List Gate
  | 0 => [⟨.and, [0, n]⟩]
  | k+1 => gs n k ++ [⟨.and, [k+1, n+(k+1)]⟩, ⟨.or, [n+n+2*k, n+n+2*k+1]⟩]

def circ (n k : ℕ) : Circuit := ⟨gs n k, n+n+2*k⟩

theorem glen (n k : ℕ) : (gs n k).length = 2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [gs, ih]; omega

theorem good (n k : ℕ) : Monotone2 (circ n k) := by
  induction k with
  | zero => intro g hg; change g ∈ [_] at hg; simp only [List.mem_singleton] at hg; subst g; simp
  | succ k ih =>
    intro g hg
    change g ∈ gs n k ++ [_,_] at hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl
    · exact ih g h
    · simp
    · simp

def push (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem and_push (w : List Bool) (a b : ℕ) : push w ⟨.and,[a,b]⟩ =
    w ++ [w.getD a false && w.getD b false] := by simp [push,GateOp.eval]

theorem or_push (w : List Bool) (a b : ℕ) : push w ⟨.or,[a,b]⟩ =
    w ++ [w.getD a false || w.getD b false] := by simp [push,GateOp.eval]

theorem kept (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl push w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (push w g) (by simp [push]; omega)]
    exact List.getD_append _ _ _ _ h

theorem sizeFold (gs : List Gate) (w : List Bool) :
    (gs.foldl push w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, push]; omega

theorem lin {n : ℕ} (u v i : Fin n) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem rin {n : ℕ} (u v i : Fin n) :
    (oneEach u v).getD (n+i.val) false = decide (i = v) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem acc {n : ℕ} (u v : Fin n) (k : ℕ) (h : k < n) :
    ((gs n k).foldl push (oneEach u v)).getD (n+n+2*k) false = true ↔
    u.val = v.val ∧ u.val ≤ k := by
  have hlen : (oneEach u v).length = n+n := by simp [oneEach]
  induction k with
  | zero =>
    let i : Fin n := ⟨0,h⟩
    have l := lin u v i
    have r := rin u v i
    change (oneEach u v).getD 0 false = _ at l
    change (oneEach u v).getD (n+0) false = _ at r
    simp only [Nat.add_zero] at r
    simp only [gs, List.foldl_cons, List.foldl_nil, and_push, Nat.mul_zero]
    change ((oneEach u v) ++ [(oneEach u v).getD 0 false && (oneEach u v).getD n false]).getD (n+n+0) false = true ↔ _
    rw [Nat.add_zero, ← hlen, List.getD_append_right _ _ _ _ le_rfl]
    simp only [Nat.sub_self,List.getD_cons_zero,Bool.and_eq_true,l,r,decide_eq_true_eq,Fin.ext_iff]
    dsimp [i]
    omega
  | succ k ih =>
    let w := (gs n k).foldl push (oneEach u v)
    have hw : w.length = n+n+2*k+1 := by simp [w,sizeFold,hlen,glen]; omega
    let i : Fin n := ⟨k+1,h⟩
    have l : w.getD (k+1) false = decide (i = u) := by
      rw [kept _ _ _ (by omega)]; exact lin u v i
    have r : w.getD (n+(k+1)) false = decide (i = v) := by
      rw [kept _ _ _ (by omega)]; exact rin u v i
    let bit := w.getD (k+1) false && w.getD (n+(k+1)) false
    let t := w ++ [bit]
    have ht : t.length = n+n+2*(k+1) := by simp [t,hw]; omega
    have hread : t.getD (n+n+2*k) false = w.getD (n+n+2*k) false :=
      List.getD_append _ _ _ _ (by omega)
    have hbit : t.getD (n+n+2*k+1) false = bit := by
      rw [← hw]; simp [t,List.getD_eq_getElem?_getD]
    simp only [gs, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [and_push, or_push]
    change (t ++ [t.getD (n+n+2*k) false || t.getD (n+n+2*k+1) false]).getD (n+n+2*(k+1)) false = true ↔ _
    rw [← ht, List.getD_append_right _ _ _ _ le_rfl]
    have wk : w.getD (n+n+2*k) false = true ↔ _ := ih (by omega)
    simp only [Nat.sub_self, List.getD_cons_zero, Bool.or_eq_true, hread, hbit, bit,
      Bool.and_eq_true, wk, l, r, decide_eq_true_eq, Fin.ext_iff]
    dsimp [i]
    omega

end PEqualNP.Contributions.DiagonalMatching

open PEqualNP.Contributions.DiagonalMatching in
theorem PEqualNP.Contributions.diagonalMatchingUpperBound : ∀ (n : ℕ), 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u.val = v.val ∧ u.val + 1 < n)) (2 * n - 3) := by
  intro n hn
  refine ⟨circ n (n-2), good _ _, ?_, ?_⟩
  · change (gs n (n-2)).length ≤ _
    rw [glen]
    omega
  · intro u v
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    change ((gs n (n-2)).foldl push _).getD (n+n+2*(n-2)) false = true ↔ _
    rw [acc u v (n-2) (by omega)]
    omega
namespace PEqualNP.Contributions.DistinctTable
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def table (n : ℕ) (u v : Fin n) : Bool := decide (u.val = v.val ∧ u.val+1 < n)

theorem distinct_rows {n : ℕ} (u w : Fin n) (hne : u ≠ w) :
    ∃ v : Fin n, table n u v ≠ table n w v := by
  have hv : u.val ≠ w.val := fun h => hne (Fin.ext h)
  by_cases h : u.val+1 < n
  · exact ⟨u, by simp [table,h,Ne.symm hv]⟩
  · have h' : w.val+1 < n := by have := u.isLt; have := w.isLt; omega
    exact ⟨w, by simp [table,h',hv]⟩

theorem distinct_cols {n : ℕ} (v z : Fin n) (hne : v ≠ z) :
    ∃ u : Fin n, table n u v ≠ table n u z := by
  have hv : v.val ≠ z.val := fun h => hne (Fin.ext h)
  by_cases h : v.val+1 < n
  · exact ⟨v, by simp [table,h,hv]⟩
  · have h' : z.val+1 < n := by have := v.isLt; have := z.isLt; omega
    exact ⟨z, by simp [table,h',Ne.symm hv]⟩

theorem optimum (n : ℕ) (hn : 2 ≤ n) :
    (∀ A : Fin n → Fin n → Bool, ∀ C : Circuit,
      (∀ u w, u ≠ w → ∃ v, A u v ≠ A w v) →
      (∀ v z, v ≠ z → ∃ u, A u v ≠ A u z) →
      FanInTwo C → Represents A C → 2*n-3 ≤ C.size) ∧
    ((∀ u w : Fin n, u ≠ w → ∃ v, table n u v ≠ table n w v) ∧
     (∀ v z : Fin n, v ≠ z → ∃ u, table n u v ≠ table n u z) ∧
     ∃ C : Circuit, FanInTwo C ∧ Monotone2 C ∧ Represents (table n) C ∧ C.size = 2*n-3) := by
  refine ⟨fun A C => PEqualNP.Contributions.distinctTableLowerBound n A C hn, distinct_rows, distinct_cols, ?_⟩
  obtain ⟨C, hm, hs, hr⟩ := PEqualNP.Contributions.diagonalMatchingUpperBound n hn
  have hf : FanInTwo C := by
    intro g hg
    obtain ⟨op, ar⟩ := hm g hg
    refine ⟨?_, ar⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    tauto
  have low := PEqualNP.Contributions.distinctTableLowerBound n (table n) C hn distinct_rows distinct_cols hf hr
  exact ⟨C, hf, hm, hr, le_antisymm hs low⟩

end PEqualNP.Contributions.DistinctTable
