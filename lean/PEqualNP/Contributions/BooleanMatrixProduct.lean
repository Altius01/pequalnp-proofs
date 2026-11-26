import Mathlib.Data.Fintype.Pigeonhole
import PEqualNP.MetaComplexity.Helpers.RunQATools
import PEqualNP.MetaComplexity.Helpers.OneNotEval

/-!
# A lower bound from the first wire with multiple readers
Output taps are separate terminal vertices. An input observed by two outputs
must meet a fork before either output. If two such inputs can be varied to
produce three distinct output vectors with all other inputs fixed, their
first forks are distinct. Counting incoming and outgoing edges then gives
one extra binary gate per shared input beyond the tree bound.

The finite instance below selects the six off-diagonal entries of a 3 by 3
Boolean matrix product. In this selection every one of the 18 inputs is
observed twice.
-/

namespace MatrixProductForks

inductive Path {V : Type} (R : V → V → Prop) : V → V → Prop where
  | nil (x : V) : Path R x x
  | cons {x y z : V} : R x y → Path R y z → Path R x z

def Fork {V : Type} (R : V → V → Prop) (v : V) :=
  ∃ p q, R v p ∧ R v q ∧ p ≠ q

def Avoid {V : Type} (R : V → V → Prop) (w a b : V) :=
  R a b ∧ a ≠ w ∧ b ≠ w

def Blocks {V : Type} (R : V → V → Prop) (out : V → Prop) (w a : V) :=
  ∀ z, out z → a ≠ w → ¬ Path (Avoid R w) a z

theorem path_from_sink {V : Type} {R : V → V → Prop} {a b : V}
    (sink : ∀ x, ¬ R a x) (p : Path R a b) : a = b := by
  cases p with
  | nil => rfl
  | cons h _ => exact False.elim (sink _ h)

theorem reach_first_fork {n : ℕ} (R : Fin n → Fin n → Prop) (out : Fin n → Prop)
    (ordered : ∀ a b, R a b → a.val < b.val)
    (terminal : ∀ a, out a → ∀ b, ¬ R a b)
    (x y z : Fin n) (oy : out y) (oz : out z) (ne : y ≠ z)
    (py : Path R x y) (pz : Path R x z) :
    ∃ w, Fork R w ∧ Blocks R out w x := by
  classical
  by_cases f : Fork R x
  · exact ⟨x, f, fun _ _ h => False.elim (h rfl)⟩
  have nx : ¬ out x := by
    intro ox
    exact ne ((path_from_sink (terminal x ox) py).symm.trans (path_from_sink (terminal x ox) pz))
  have next {t : Fin n} (ot : out t) (p : Path R x t) :
      ∃ v, R x v ∧ Path R v t := by
    cases p with
    | nil => exact False.elim (nx ot)
    | cons h q => exact ⟨_, h, q⟩
  obtain ⟨a, ha, pa⟩ := next oy py
  obtain ⟨b, hb, pb⟩ := next oz pz
  have unique : ∀ c, R x c → a = c := fun c hc => by
    by_contra h
    exact f ⟨a,c,ha,hc,h⟩
  obtain rfl := unique b hb
  obtain ⟨w, hw, block⟩ := reach_first_fork R out ordered terminal a y z oy oz ne pa pb
  refine ⟨w,hw,?_⟩
  intro t ot _ p
  cases p with
  | nil => exact nx ot
  | cons h q =>
    obtain rfl := unique _ h.1
    exact block _ ot h.2.2 q
termination_by n - x.val
decreasing_by have := ordered _ _ ha; have := a.isLt; omega

theorem changed_path {n : ℕ} {R : Fin n → Fin n → Prop} {isInput : Fin n → Prop}
    (ord : ∀ a b, R a b → a.val < b.val) (s t : Fin n → Bool)
    (localRule : ∀ v, ¬ isInput v → (∀ u, R u v → s u = t u) → s v = t v)
    (z : Fin n) (diff : s z ≠ t z) :
    ∃ a, isInput a ∧ s a ≠ t a ∧
      Path (fun u v => R u v ∧ s u ≠ t u ∧ s v ≠ t v) a z := by
  classical
  by_cases hi : isInput z
  · exact ⟨z, hi, diff, Path.nil z⟩
  have h : ∃ u, R u z ∧ s u ≠ t u := by
    by_contra! h
    exact diff (localRule z hi h)
  obtain ⟨u, hu, du⟩ := h
  obtain ⟨a, ia, da, p⟩ := changed_path ord s t localRule u du
  refine ⟨a, ia, da, ?_⟩
  have append {x y : Fin n} (q : Path (fun u v => R u v ∧ s u ≠ t u ∧ s v ≠ t v) x y) :
      ∀ z, R y z → s y ≠ t y → s z ≠ t z →
        Path (fun u v => R u v ∧ s u ≠ t u ∧ s v ≠ t v) x z := by
    induction q with
    | nil v => intro v' e h1 h2; exact .cons ⟨e,h1,h2⟩ (.nil v')
    | cons e _ ih => intro v' e' h1 h2; exact .cons e (ih _ e' h1 h2)
  exact append p z hu du diff
termination_by z.val
decreasing_by exact ord _ _ hu

theorem Path.map_rel {V : Type} {R S : V → V → Prop} {x y : V}
    (p : Path R x y) (h : ∀ a b, R a b → S a b) : Path S x y := by
  induction p with
  | nil => exact .nil _
  | cons e _ ih => exact .cons (h _ _ e) ih

theorem same_at_block {n : ℕ} {R : Fin n → Fin n → Prop} {out isInput : Fin n → Prop}
    (ord : ∀ a b, R a b → a.val < b.val) (a b w : Fin n)
    (ba : Blocks R out w a) (bb : Blocks R out w b)
    (s t : Fin n → Bool)
    (localRule : ∀ v, ¬ isInput v → (∀ u, R u v → s u = t u) → s v = t v)
    (fixed : ∀ v, isInput v → s v ≠ t v → v = a ∨ v = b)
    (same : s w = t w) (z : Fin n) (oz : out z) : s z = t z := by
  by_contra diff
  obtain ⟨u, i, d, p⟩ := changed_path ord s t localRule z diff
  have away : ∀ v, s v ≠ t v → v ≠ w := by
    intro v dv eq; exact dv (eq ▸ same)
  have p' : Path (Avoid R w) u z := p.map_rel fun _ _ h => ⟨h.1, away _ h.2.1, away _ h.2.2⟩
  rcases fixed _ i d with rfl | rfl
  · exact ba _ oz (away _ d) p'
  · exact bb _ oz (away _ d) p'


/-- Three pairwise distinguishable output settings obtained by varying just the indicated inputs. -/
def Separate {n : ℕ} (actual : (Fin n → Bool) → Prop) (inputs outputs : Finset (Fin n))
    (a b : Fin n) : Prop :=
  ∃ s : Fin 3 → Fin n → Bool, (∀ i, actual (s i)) ∧
    (∀ i j v, v ∈ inputs → s i v ≠ s j v → v = a ∨ v = b) ∧
    ∀ i j, i ≠ j → ∃ v ∈ outputs, s i v ≠ s j v

theorem gate_count {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (actual : (Fin n → Bool) → Prop) (inputs outputs shared binary active : Finset (Fin n))
    (order : ∀ u v, R u v → u.val < v.val)
    (terminal : ∀ v ∈ outputs, ∀ u, ¬ R v u)
    (live : ∀ v ∈ active, v ∉ outputs → ∃ u, R v u)
    (fanIn : ∀ v, (Finset.univ.filter (fun u => R u v)).card + (if v ∈ inputs then 1 else 0)
      ≤ (if v ∈ active then 1 else 0) + (if v ∈ binary then 1 else 0))
    (localRule : ∀ s t, actual s → actual t → ∀ v, v ∉ inputs →
      (∀ u, R u v → s u = t u) → s v = t v)
    (feeds : ∀ a ∈ shared, ∃ y ∈ outputs, ∃ z ∈ outputs, y ≠ z ∧ Path R a y ∧ Path R a z)
    (sep : ∀ a ∈ shared, ∀ b ∈ shared, a ≠ b → Separate actual inputs outputs a b) :
    inputs.card + shared.card ≤ binary.card + outputs.card := by
  classical
  let forks := Finset.univ.filter (Fork R)
  have witness : ∀ a ∈ shared, ∃ w ∈ forks, Blocks R (· ∈ outputs) w a := by
    intro a ha
    obtain ⟨y,oy,z,oz,ne,p,q⟩ := feeds a ha
    obtain ⟨w,fw,block⟩ := reach_first_fork R _ order terminal a y z oy oz ne p q
    exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fw⟩,block⟩
  let f (a : Fin n) := if h : a ∈ shared then (witness a h).choose else a
  have hf (a : Fin n) (ha : a ∈ shared) : f a ∈ forks ∧ Blocks R (· ∈ outputs) (f a) a := by
    simpa [f,ha] using (witness a ha).choose_spec
  have card : shared.card ≤ forks.card := by
    apply Finset.card_le_card_of_injOn f (fun a ha => (hf a ha).1)
    intro a ha b hb eq
    by_contra ne
    obtain ⟨s,real,fixed,dist⟩ := sep a ha b hb ne
    obtain ⟨i,j,hij,e⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => s i (f a)) (by decide)
    obtain ⟨z,oz,d⟩ := dist i j hij
    exact d (same_at_block order a b (f a) (hf a ha).2 (eq ▸ (hf b hb).2)
      _ _ (localRule _ _ (real i) (real j)) (fixed i j) e z oz)
  have fanOut (u : Fin n) :
      (if u ∈ active then 1 else 0) + (if u ∈ forks then 1 else 0) ≤ (Finset.univ.filter (R u)).card +
        (if u ∈ outputs then 1 else 0) := by
    by_cases f : u ∈ forks
    · obtain ⟨v,w,hv,hw,ne⟩ := (Finset.mem_filter.mp f).2
      have sub : ({v,w} : Finset (Fin n)) ⊆ Finset.univ.filter (R u) := by
        intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with rfl|rfl <;> simp [*]
      have sz := Finset.card_le_card sub
      rw [Finset.card_pair ne] at sz
      simp only [f,ite_true]; split <;> omega
    · by_cases o : u ∈ outputs
      · simp only [f,o,ite_true,ite_false]; split <;> omega
      · by_cases m : u ∈ active
        · obtain ⟨v,e⟩ := live u m o
          have pos : 0 < (Finset.univ.filter (R u)).card := Finset.card_pos.mpr ⟨v,by simp [e]⟩
          simp only [f,o,m,ite_true,ite_false,Nat.add_zero]; omega
        · simp [m,f]
  have edgeCount : (∑ u, (Finset.univ.filter (R u)).card) =
      ∑ v, (Finset.univ.filter (fun u => R u v)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have flags (s : Finset (Fin n)) : (∑ v : Fin n, if v ∈ s then 1 else 0) = s.card := by simp
  have h₁ := Finset.sum_le_sum (s := Finset.univ) (fun v _ => fanIn v)
  have h₂ := Finset.sum_le_sum (s := Finset.univ) (fun v _ => fanOut v)
  simp only [Finset.sum_add_distrib, flags] at h₁ h₂
  omega

-- Six selected outputs, in row-major order, omitting the diagonal.
def cells : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]
/-- Encodes a selector assignment and two tap indices as 36 * assignment + 6 * first + second. -/
def routes : List (List ℕ) := [
  [0, 626689, 4755457, 55298, 184322, 1216514, 55300, 184324, 1216516, 37154, 76043, 37155, 37442, 78347, 37443, 38018, 82955, 38019],
  [368641, 0, 5013505, 313346, 442370, 1474562, 313348, 442372, 1474564, 295202, 592139, 295203, 295490, 594443, 295491, 296066, 599051, 296067],
  [2433025, 2949121, 0, 2377730, 2506754, 3538946, 2377732, 2506756, 3538948, 2359586, 4720907, 2359587, 2359874, 4723211, 2359875, 2360450, 4727819, 2360451],
  [55308, 313356, 2377740, 0, 608271, 4737039, 18448, 313361, 2377745, 76054, 18480, 18481, 78358, 18516, 18517, 82966, 18588, 18589],
  [184332, 442380, 2506764, 221199, 0, 4866063, 184337, 147472, 2506769, 592150, 147504, 147505, 594454, 147540, 147541, 599062, 147612, 147613],
  [1216524, 1474572, 3538956, 1253391, 1769487, 0, 1216529, 1474577, 1179664, 4720918, 1179696, 1179697, 4723222, 1179732, 1179733, 4727830, 1179804, 1179805],
  [55320, 313368, 2377752, 18458, 608283, 4737051, 0, 313373, 2377757, 37184, 18492, 18493, 37472, 18528, 18529, 38048, 18600, 18601],
  [184344, 442392, 2506776, 221211, 147482, 4866075, 184349, 0, 2506781, 295232, 147516, 147517, 295520, 147552, 147553, 296096, 147624, 147625],
  [1216536, 1474584, 3538968, 1253403, 1769499, 1179674, 1216541, 1474589, 0, 2359616, 1179708, 1179709, 2359904, 1179744, 1179745, 2360480, 1179816, 1179817],
  [37164, 295212, 2359596, 76059, 592155, 4720923, 37169, 295217, 2359601, 0, 336, 337, 4912, 372, 373, 9520, 444, 445],
  [76063, 592159, 4720927, 18470, 147494, 1179686, 18472, 147496, 1179688, 326, 0, 37, 614, 4649, 615, 1190, 9257, 1191],
  [37170, 295218, 2359602, 18476, 147500, 1179692, 18478, 147502, 1179694, 332, 42, 0, 620, 4655, 621, 1196, 9263, 1197],
  [37452, 295500, 2359884, 78363, 594459, 4723227, 37457, 295505, 2359889, 2896, 624, 625, 0, 660, 661, 9808, 732, 733],
  [78367, 594463, 4723231, 18506, 147530, 1179722, 18508, 147532, 1179724, 362, 2381, 363, 650, 0, 73, 1226, 9293, 1227],
  [37458, 295506, 2359890, 18512, 147536, 1179728, 18514, 147538, 1179730, 368, 2387, 369, 656, 78, 0, 1232, 9299, 1233],
  [38028, 296076, 2360460, 82971, 599067, 4727835, 38033, 296081, 2360465, 3472, 1200, 1201, 5776, 1236, 1237, 0, 1308, 1309],
  [82975, 599071, 4727839, 18578, 147602, 1179794, 18580, 147604, 1179796, 434, 2453, 435, 722, 4757, 723, 1298, 0, 145],
  [38034, 296082, 2360466, 18584, 147608, 1179800, 18586, 147610, 1179802, 440, 2459, 441, 728, 4763, 729, 1304, 150, 0]]
/-- Two single-bit sensitivity witnesses per input, encoding 6 * assignment + tap. -/
def probes : List (List ℕ) := [
  [6144, 12289],
  [49152, 98305],
  [393216, 786433],
  [3074, 12291],
  [24578, 98307],
  [196610, 786435],
  [3076, 6149],
  [24580, 49157],
  [196612, 393221],
  [50, 388],
  [6, 389],
  [7, 51],
  [98, 772],
  [12, 773],
  [13, 99],
  [194, 1540],
  [24, 1541],
  [25, 195]]

abbrev Input := Fin 18
abbrev Tap := Fin 6

def productBit (x : Input → Bool) (y : Tap) : Bool :=
  let rc := cells.getD y.val (0,0)
  [0,1,2].any (fun k => x ⟨(3*rc.1+k)%18, by omega⟩ &&
                         x ⟨(9+3*k+rc.2)%18, by omega⟩)

def readCode (a b : Input) := (routes.getD a.val []).getD b.val 0
def rowTap (a b : Input) : Tap := ⟨readCode a b / 6 % 6, by omega⟩
def colTap (a b : Input) : Tap := ⟨readCode a b % 6, by omega⟩
def setting (a b : Input) (i : Fin 3) (v : Input) : Bool :=
  if v = a then decide (i.val=1) else if v=b then decide (i.val=2)
  else (readCode a b / 36).testBit v.val

def probeCode (a : Input) (k : Fin 2) := (probes.getD a.val []).getD k.val 0
def probeTap (a : Input) (k : Fin 2) : Tap := ⟨probeCode a k % 6, by omega⟩
def probeSetting (a : Input) (k : Fin 2) (val : Bool) (v : Input) : Bool :=
  if v=a then val else (probeCode a k / 6).testBit v.val

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem route_verified : ∀ a b : Input, a ≠ b → ∀ i : Fin 3,
    productBit (setting a b i) (rowTap a b) = decide (i.val=1) ∧
    productBit (setting a b i) (colTap a b) = decide (i.val=2) := by decide +kernel

set_option maxRecDepth 16000 in
theorem probes_verified : ∀ a : Input, probeTap a 0 ≠ probeTap a 1 ∧
    ∀ (k : Fin 2) (v : Bool), productBit (probeSetting a k v) (probeTap a k) = v := by decide +kernel

noncomputable def reaching {n : ℕ} (R : Fin n → Fin n → Prop) (tap : Tap ↪ Fin n)
    (binary : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact binary ∩ Finset.univ.filter fun u => ∃ t : Tap, Path R u (tap t)

/-- Each of the counted gates has a path to a selected output. -/
theorem thirty_binary_gates {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (input : Input ↪ Fin n) (tap : Tap ↪ Fin n)
    (run : (Input → Bool) → Fin n → Bool) (binary : Finset (Fin n))
    (order : ∀ u v, R u v → u.val < v.val)
    (terminal : ∀ i u, ¬ R (tap i) u)
    (fanIn : ∀ v, (Finset.univ.filter (fun u => R u v)).card +
      (if v ∈ Finset.univ.image input then 1 else 0) ≤ 1 + (if v ∈ binary then 1 else 0))
    (localRule : ∀ x x' v, v ∉ Finset.univ.image input →
      (∀ u, R u v → run x u = run x' u) → run x v = run x' v)
    (hi : ∀ x a, run x (input a) = x a)
    (ho : ∀ x j, run x (tap j) = productBit x j) : 30 ≤ (reaching R tap binary).card := by
  classical
  let I := Finset.univ.image input
  let O := Finset.univ.image tap
  have memI (a : Input) : input a ∈ I := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have memO (y : Tap) : tap y ∈ O := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have getPath (a : Input) (k : Fin 2) : Path R (input a) (tap (probeTap a k)) := by
    let x := probeSetting a k false
    let x' := probeSetting a k true
    have d : run x (tap (probeTap a k)) ≠ run x' (tap (probeTap a k)) := by
      rw [ho,ho,(probes_verified a).2 k false,(probes_verified a).2 k true]; decide
    obtain ⟨u,iu,du,p⟩ := changed_path order _ _ (localRule x x') _ d
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp iu
    have eq : b = a := by
      by_contra h; apply du; simp [hi,x,x',probeSetting,h]
    subst b; exact p.map_rel fun _ _ h => h.1
  have feeds : ∀ v ∈ I, ∃ y ∈ O, ∃ z ∈ O, y ≠ z ∧ Path R v y ∧ Path R v z := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨_,memO _,_,memO _,fun e => (probes_verified a).1 (tap.injective e),getPath _ 0,getPath _ 1⟩
  let actual := fun s => ∃ x, run x = s
  have separates : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → Separate actual I O u v := by
    intro u hu v hv ne
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hv
    have ab : a ≠ b := fun e => ne (congrArg input e)
    refine ⟨fun i => run (setting a b i), fun _ => ⟨_,rfl⟩, ?_, ?_⟩
    · intro i j w hw d
      obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hw
      by_cases ac : c=a
      · exact Or.inl (congrArg input ac)
      by_cases bc : c=b
      · exact Or.inr (congrArg input bc)
      exact False.elim (d (by simp [hi,setting,ac,bc]))
    · intro i j ij
      by_contra! h
      have h1 := h _ (memO (rowTap a b))
      have h2 := h _ (memO (colTap a b))
      simp only [ho, (route_verified a b ab _).1, (route_verified a b ab _).2] at h1 h2
      fin_cases i <;> fin_cases j <;> simp_all
  let active := Finset.univ.filter fun u => ∃ t : Tap, Path R u (tap t)
  let S := fun u v => R u v ∧ v ∈ active
  have memA (a : Fin n) : a ∈ active ↔ ∃ t : Tap, Path R a (tap t) := by simp [active]
  have tapA (j : Tap) : tap j ∈ active := (memA _).2 ⟨j, .nil _⟩
  have inputA (a : Input) : input a ∈ active := (memA _).2 ⟨_, getPath a 0⟩
  have prevActive {u v : Fin n} (e : R u v) (av : v ∈ active) : u ∈ active := by
    obtain ⟨t,p⟩ := (memA _).1 av; exact (memA _).2 ⟨t,.cons e p⟩
  have trim {u v : Fin n} (p : Path R u v) : v ∈ active → u ∈ active ∧ Path S u v := by
    induction p with
    | nil => exact fun h => ⟨h,.nil _⟩
    | cons e _ ih =>
      intro av; obtain ⟨b,q⟩ := ih av; exact ⟨prevActive e b, .cons ⟨e,b⟩ q⟩
  let cut (s : Fin n → Bool) (v : Fin n) := if v ∈ active then s v else false
  let good := fun s => ∃ x, cut (run x) = s
  have localCut : ∀ s t, good s → good t → ∀ v, v ∉ I →
      (∀ u, S u v → s u = t u) → s v=t v := by
    rintro s t ⟨x,rfl⟩ ⟨y,rfl⟩ v hv same
    by_cases av : v ∈ active
    · simp only [cut,av,ite_true]
      apply localRule x y v hv
      intro u e; simpa only [cut,prevActive e av,ite_true] using same u ⟨e,av⟩
    · simp [cut,av]
  have fixedCut (a b : Fin n) (sep : Separate actual I O a b) : Separate good I O a b := by
    obtain ⟨s,real,fix,dist⟩ := sep
    refine ⟨fun i => cut (s i), ?_, ?_, ?_⟩
    · intro i; obtain ⟨x,hx⟩ := real i; exact ⟨x,congrArg cut hx⟩
    · intro i j u iu d; apply fix i j u iu; intro e; exact d (by simp [cut,e])
    · intro i j ne; obtain ⟨v,hv,d⟩ := dist i j ne
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨_,memO _,by simpa [cut,tapA] using d⟩
  have h := gate_count S good I O I (binary ∩ active) active (fun u v e => order u v e.1) (by
    intro v hv; obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hv; exact fun u e => terminal k u e.1)
    (by
      intro v av no; obtain ⟨k,p⟩ := (memA v).1 av
      have q := (trim p (tapA k)).2
      cases q with
      | nil => exact False.elim (no (memO _))
      | cons e _ => exact ⟨_,e⟩)
    (by
      intro v; by_cases av : v ∈ active
      · simpa [S,av,I] using fanIn v
      · have no : v ∉ I := fun hv => by
          obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
          exact av (inputA j)
        simp [S,av,no])
    localCut (by
      intro a ha; obtain ⟨y,oy,z,oz,ne,p,q⟩ := feeds a ha
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp oy
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp oz
      exact ⟨_,memO _,_,memO _,ne,(trim p (tapA j)).2,(trim q (tapA k)).2⟩)
    (fun a ha b hb ne => fixedCut _ _ (separates a ha b hb ne))
  simpa [I,O,reaching,active,Finset.card_image_of_injective, input.injective,tap.injective] using h

end MatrixProductForks

/-! Adapt the fork-counting bound to the project's gate-list interpreter, including
out-of-range reads, dead gates, repeated operands, and NOT gates reading their
first operand. -/

namespace MatrixProductForks.ProjectCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.RunFour2 PEqualNP.MetaComplexity.OneNot

abbrev stop (C : Circuit) := 18 + C.gates.length
abbrev V (C : Circuit) := Fin (stop C + 6)

def primary (C : Circuit) : Input ↪ V C where
  toFun i := ⟨i.val, by have := i.isLt; dsimp [stop]; omega⟩
  inj' := fun _ _ e => Fin.ext (congrArg (fun v : V C => v.val) e)

def output (C : Circuit) : Tap ↪ V C where
  toFun i := ⟨stop C + i.val, by have := i.isLt; omega⟩
  inj' := fun a b e => Fin.ext (by have eq : stop C + a.val = stop C + b.val := congrArg Fin.val e; omega)

def args (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

theorem args_length (g : Gate) : (args g).length ≤ g.inputs.length := by
  cases g with
  | mk op ins => cases op <;> simp [args]

theorem args_agree (g : Gate) (s t : ℕ → Bool) (agree : ∀ i ∈ args g, s i = t i) :
    g.op.eval (g.inputs.map s) = g.op.eval (g.inputs.map t) := by
  cases g with
  | mk op ins =>
    cases op <;> simp only [args] at agree
    all_goals first
      | exact congrArg _ (List.map_congr_left agree)
      | cases ins with
        | nil => rfl
        | cons i is => simp [GateOp.eval, agree i (by simp)]

def gate (C : Circuit) (v : V C) := C.gates.getD (v.val - 18) ⟨.or,[]⟩

def sources (C : Circuit) (o : Tap → ℕ) (v : V C) :=
  if v.val<18 then [] else if v.val<stop C then args (gate C v)
  else [o ⟨(v.val-stop C)%6,by omega⟩]

def edge (C : Circuit) (o : Tap → ℕ) (u v : V C) : Prop :=
  u.val < v.val ∧ u.val < stop C ∧ u.val ∈ sources C o v

instance (C : Circuit) (o : Tap → ℕ) : DecidableRel (edge C o) := fun _ _ => by
  unfold edge; infer_instance

def binary (C : Circuit) (o : Tap → ℕ) :=
  Finset.univ.filter fun v : V C => 2 ≤ (sources C o v).length

def raw (C : Circuit) (x : Input → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false

def values (C : Circuit) (o : Tap → ℕ) (x : Input → Bool) (v : V C) :=
  if v.val<stop C then raw C x v.val else raw C x (o ⟨(v.val-stop C)%6,by omega⟩)

theorem valid_gate (C : Circuit) (v : V C) (lo : 18 ≤ v.val) (lt : v.val < stop C) :
    C.gates[v.val-18]? = some (gate C v) := by
  have h : v.val-18 < C.gates.length := by dsimp [stop] at lt; omega
  simp [gate,List.getD_eq_getElem?_getD,h]

theorem raw_gate (C : Circuit) (v : V C) (lo : 18 ≤ v.val) (lt : v.val < stop C)
    (x : Input → Bool) : raw C x v.val = (gate C v).op.eval ((gate C v).inputs.map
      fun i => if i < v.val then raw C x i else false) := by
  have h := qa_val_gate C.gates (List.ofFn x) _ _ (valid_gate C v lo lt)
  have eq : 18 + (v.val-18) = v.val := by omega
  simpa only [raw,on1_wires_output,List.length_ofFn,eq,wires_eq] using h

theorem raw_out (C : Circuit) (x : Input → Bool) (j : ℕ) (h : stop C ≤ j) :
    raw C x j = false := on1_getD_wires_of_ge _ _ _ (by simpa using h)

theorem indegree (C : Circuit) (o : Tap → ℕ) (v : V C) :
    (Finset.univ.filter (fun u => edge C o u v)).card ≤ (sources C o v).length := by
  apply le_trans _ (List.toFinset_card_le _)
  exact Finset.card_le_card_of_injOn Fin.val
    (fun _ h => List.mem_toFinset.mpr (Finset.mem_filter.mp h).2.2.2)
    (fun _ _ _ _ eq => Fin.ext eq)

theorem fanIn (C : Circuit) (o : Tap → ℕ) (hm : FanInTwo C) (v : V C) :
    (Finset.univ.filter (fun u => edge C o u v)).card +
      (if v ∈ Finset.univ.image (primary C) then 1 else 0)
    ≤ 1 + (if v ∈ binary C o then 1 else 0) := by
  have card := indegree C o v
  by_cases less : v.val < 18
  · have h : sources C o v = [] := by simp [sources,less]
    rw [h] at card; simp only [List.length_nil] at card
    split <;> omega
  have hv : v ∉ Finset.univ.image (primary C) := by
    rintro h; obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h; exact less a.isLt
  simp only [hv,ite_false,Nat.add_zero]
  have len : (sources C o v).length ≤ 2 := by
    by_cases mid : v.val < stop C
    · simpa [sources,less,mid] using (args_length (gate C v)).trans
        (hm _ (List.mem_of_getElem? (valid_gate C v (by omega) mid))).2
    · simp [sources,less,mid]
  by_cases b : 2 ≤ (sources C o v).length <;> simp [binary,b] <;> omega

theorem localValues (C : Circuit) (o : Tap → ℕ) (x y : Input → Bool) (v : V C)
    (notInput : v ∉ Finset.univ.image (primary C))
    (same : ∀ u, edge C o u v → values C o x u=values C o y u) :
    values C o x v=values C o y v := by
  have lo : 18 ≤ v.val := by
    by_contra! h
    apply notInput; exact Finset.mem_image.mpr ⟨⟨v.val,h⟩,Finset.mem_univ _,Fin.ext rfl⟩
  by_cases mid : v.val < stop C
  · simp only [values,mid,ite_true]
    rw [raw_gate C v lo mid x,raw_gate C v lo mid y]
    apply args_agree
    intro j hj
    by_cases early : j<v.val
    · let u : V C := ⟨j,by omega⟩
      have valid : u.val < stop C := by dsimp [u]; omega
      have e : edge C o u v := ⟨early,valid,by simpa [sources,show ¬v.val<18 by omega,mid,u] using hj⟩
      simpa [values,early,valid,u] using same u e
    · simp [early]
  · let j := o ⟨(v.val-stop C)%6,by omega⟩
    change (if v.val < stop C then _ else raw C x j) = (if v.val < stop C then _ else raw C y j)
    simp only [mid,ite_false]
    by_cases valid : j<stop C
    · let u : V C := ⟨j,by omega⟩
      have e : edge C o u v := ⟨by dsimp [u]; omega,valid,by simp [sources,show ¬v.val<18 by omega,mid,u,j]⟩
      simpa [values,u,valid] using same u e
    · rw [raw_out _ _ _ (by omega),raw_out _ _ _ (by omega)]

theorem six_output_bound (C : Circuit) (o : Tap → ℕ) (hm : FanInTwo C)
    (correct : ∀ x i, (C.wires (List.ofFn x)).getD (o i) false = productBit x i) :
    30 ≤ (reaching (edge C o) (output C) (binary C o)).card := by
  apply thirty_binary_gates (edge C o) (primary C) (output C) (values C o) (binary C o)
  · exact fun _ _ e => e.1
  · intro i v e; have h := e.2.1; change stop C+i.val < stop C at h; omega
  · exact fanIn C o hm
  · exact localValues C o
  · intro x a
    have h : (primary C a).val < stop C := by change a.val < 18+_; have := a.isLt; omega
    simp only [values,h,ite_true]; exact on1_getD_wires_input C x a.val a.isLt
  · intro x i
    have h : ¬ (output C i).val < stop C := by change ¬ stop C+i.val<stop C; omega
    simp only [values,h,ite_false]
    have eq : ((output C i).val-stop C)%6=i.val := by change (stop C+i.val-stop C)%6=i.val; simp [Nat.mod_eq_of_lt i.isLt]
    have idx : (⟨((output C i).val-stop C)%6,by omega⟩ : Tap)=i := Fin.ext eq
    rw [idx]; exact correct x i

/-- Positions of the physical gates with two effective operands. -/
def twoInputPositions (C : Circuit) := (Finset.range C.gates.length).filter fun j =>
  2 ≤ (args (C.gates.getD j ⟨.or,[]⟩)).length

theorem physical_gate_bound (C : Circuit) (o : Tap → ℕ) (hm : FanInTwo C)
    (correct : ∀ x i, (C.wires (List.ofFn x)).getD (o i) false = productBit x i) :
    30 ≤ (twoInputPositions C).card := by
  classical
  apply (six_output_bound C o hm correct).trans
  have sub : reaching (edge C o) (output C) (binary C o) ⊆ binary C o :=
    Finset.inter_subset_left
  apply (Finset.card_le_card sub).trans
  have info (v : V C) (h : v ∈ binary C o) : 18 ≤ v.val ∧ v.val < stop C ∧
      2 ≤ (args (gate C v)).length := by
    have h' := (Finset.mem_filter.mp h).2
    by_cases small : v.val < 18
    · simp [sources,small] at h'
    by_cases mid : v.val < stop C
    · exact ⟨by omega,mid,by simpa [sources,small,mid] using h'⟩
    · simp [sources,small,mid] at h'
  apply Finset.card_le_card_of_injOn (fun v : V C => v.val-18)
  · intro v hv; obtain ⟨lo,hi,sz⟩ := info v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by change v.val-18 < C.gates.length; dsimp [stop] at hi; omega),sz⟩
  · intro a ha b hb eq
    have x := (info a ha).1; have y := (info b hb).1
    apply Fin.ext; change a.val-18=b.val-18 at eq; omega

end MatrixProductForks.ProjectCircuit
