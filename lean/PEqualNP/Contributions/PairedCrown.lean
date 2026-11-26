import PEqualNP.Defs

namespace PEqualNP.Contributions.PairedCrown
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
-- The fold monotonicity and oneEach identity are from L_meta_19123.
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

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl stp x).getD i false = true → (gs.foldl stp y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa using hxy
  | append_singleton gs g ih =>
    have ih := ih fun g' h => hg g' (by simp [h])
    intro i
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [getD_snoc, getD_snoc, len, len, hl]
    split_ifs
    · exact ih i
    · rcases hg g (by simp) with h | h
      · simp only [h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
        exact fun hh a ha => ih a (hh a ha)
      · simp only [h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact fun ⟨a, ha, hh⟩ => ⟨a, ha, ih a hh⟩
    · simp


theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

def paired {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  List.ofFn fun k : Fin (n+n) => decide (∃ u ∈ S, k.val = u.val ∨ k.val = n+u.val)

theorem paired_bit {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    (paired S).getD k false = true ↔ ∃ u ∈ S, k = u.val ∨ k = n+u.val := by
  by_cases h : k < n+n
  · simp [paired, List.getD_eq_getElem?_getD, h]
  · have no : ¬ ∃ u ∈ S, k = u.val ∨ k = n+u.val := by
      rintro ⟨u, _, h' | h'⟩ <;> have := u.isLt <;> omega
    simp [paired, List.getD_eq_getElem?_getD, h, no]

theorem paired_crown {n : ℕ} (hn : 0 < n) (C : Circuit) (hM : Monotone2 C)
    (rep : Represents (fun u v : Fin n => decide (u ≠ v)) C) (S : Finset (Fin n)) :
    C.eval (paired S) = true ↔ ∃ u ∈ S, ∃ v ∈ S, u ≠ v := by
  have increasing (x y : List Bool) (hl : x.length = y.length)
      (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
      C.eval x = true → C.eval y = true :=
    mono C.gates (fun g hg => by simpa using (hM g hg).1) x y hl hxy C.output
  constructor
  · intro ht
    by_contra no
    have small : ∃ a : Fin n, ∀ b ∈ S, b = a := by
      by_cases h : S.Nonempty
      · obtain ⟨a, ha⟩ := h
        exact ⟨a, fun b hb => by by_contra hne; exact no ⟨b, hb, a, ha, hne⟩⟩
      · exact ⟨⟨0, hn⟩, fun b hb => False.elim (h ⟨b, hb⟩)⟩
    obtain ⟨a, ha⟩ := small
    have hdiag := increasing (paired S) (oneEach a a) (by simp [paired, oneEach]) (by
      intro k hk
      obtain ⟨b, hb, e⟩ := (paired_bit S k).mp hk
      exact (oe a a k).mpr (ha b hb ▸ e)) ht
    have hfalse := rep a a
    simp at hfalse
    rw [hfalse] at hdiag
    contradiction
  · rintro ⟨u, hu, v, hv, hne⟩
    apply increasing (oneEach u v) (paired S) (by simp [paired, oneEach])
    · intro k hk
      apply (paired_bit S k).mpr
      rcases (oe u v k).mp hk with h | h
      · exact ⟨u, hu, Or.inl h⟩
      · exact ⟨v, hv, Or.inr h⟩
    · simpa [hne] using rep u v

end PEqualNP.Contributions.PairedCrown
