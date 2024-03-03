import Std

class ZFC (set : Type) [Membership set set] [EmptyCollection set] where
  /-- Axiom 1 -/
  extensionality {a b: set} (h: ∀x, x ∈ a ↔ x ∈ b): a = b
  pair (a b: set): set
  mem_pair_iff {a b x: set}: x ∈ pair a b ↔ (x = a ∨ x = b)
  set_union (a: set): set
  mem_set_union_iff {a x: set}: x ∈ set_union a ↔ ∃y ∈ a, x ∈ y
  powerset (a: set): set
  mem_powerset_iff {a x: set}: x ∈ powerset a ↔ (∀y ∈ x, y ∈ a)
  separation (P: set → Prop) (a: set): set
  mem_separation_iff {P} {a x: set}: x ∈ separation P a ↔ (x ∈ a ∧ P x)
  replacement (f: set → set) (a: set): set
  mem_replacement_iff {f} {a x: set}: x ∈ replacement f a ↔ ∃y ∈ a, f y = x
  not_mem_empty {x: set}: x ∉ (∅ :set)
  weak_regularity {x a: set} (non_empty: x ∈ a): ∃ x ∈ a, ∀ y ∈ a, y ∉ x

namespace ZFC
variable {set : Type} [Membership set set] [EmptyCollection set] [ZFC set]
open ZFC
open Classical
/-- Definition 3.1 + Axiom 1 combined -/
theorem eq_iff_mem_iff (a b: set): a = b ↔ (∀x: set, a ∈ x ↔ b ∈ x) :=
  ⟨fun h x => by simp only [h], fun h => by specialize h (pair b b); rw[mem_pair_iff (x:= b), mem_pair_iff (x:= a)] at h; simp at h; exact h ⟩

@[ext]
theorem extensionality' {a b: set} (h: ∀x, x ∈ a ↔ x ∈ b): a = b := extensionality h

theorem eq_iff_ext (a b: set): (∀x: set, x ∈ a ↔ x ∈ b) ↔ a = b :=
  ⟨extensionality, fun h _ => iff_of_eq $ congrArg _ h⟩

def classes := set → Prop

@[ext]
theorem classes_extensionality {A B: classes} (h: ∀x:set, A x ↔ B x): A = B := by funext; rw [h]

scoped instance : Coe set (classes (set := set)) where
  coe x y := y ∈ x

def reprs_set (A : classes (set := set)) := ∃x:set, ↑x = A

abbrev is_proper_class (A : classes (set := set)) := ¬ reprs_set A

@[simp] theorem coe_reprs_set (a : set): reprs_set (set := set) a := by simp only [reprs_set, exists_apply_eq_apply]

def russell_class : classes (set := set) := fun x => x ∉ x

theorem russell_is_proper_class: is_proper_class (russell_class (set := set))
  | ⟨x, h⟩ => iff_not_self $ iff_of_eq $ congrFun h x

instance : Singleton set set where
  singleton (a: set) := pair a a

theorem singleton_def {a : set}: {a} = pair a a := Eq.refl _

theorem pair_class_reprs_set {a b : set}: reprs_set (fun x => x = a ∨ x = b) := ⟨pair a b, by simp only [mem_pair_iff]⟩

def ordered_pair (a: set) b := pair (singleton a) (pair a b)

notation:max "⟪" a "," b "⟫" => ordered_pair a b

@[simp] theorem mem_pair_iff' {a b x: set}: x ∈ pair a b ↔ (x = a ∨ x = b) := mem_pair_iff

@[simp] theorem mem_pair_left {a b: set}: a ∈ pair a b := by simp only [mem_pair_iff', true_or]

@[simp] theorem mem_pair_right {a b: set}: b ∈ pair a b := by simp only [mem_pair_iff', or_true]

@[simp] theorem mem_singleton_iff {a x: set}: x ∈ (singleton a: set) ↔ x = a := by simp only [singleton,
  mem_pair_iff', or_self]

@[simp] theorem mem_singleton {a: set}: a ∈ (singleton a: set) := by simp only [mem_singleton_iff]

theorem mem_ordered_pair_iff {a b x: set}: x ∈ ordered_pair a b ↔ (x = {a} ∨ x = pair a b) := by simp only [ordered_pair,
  mem_pair_iff']

@[simp] theorem singleton_inj {a b: set}: {a} = ({b} : set) ↔ a = b := ⟨fun h => by rw[← eq_iff_ext] at h; specialize h a; simp at h; exact h,
  congrArg _⟩

@[simp] theorem singleton_eq_pair_iff {a b c: set}: {a} = pair b c ↔ (a = b ∧ a = c) := by
  apply Iff.intro
  · intro h
    rw[← eq_iff_ext] at h
    have h2:=h b
    specialize h c
    simp at *
    exact ⟨h2.symm, h.symm⟩
  · rintro ⟨hb, hc⟩
    rw[← hb, ← hc]
    dsimp only [singleton]

theorem pair_right_inj {a b c: set}: pair a b = pair a c ↔ b = c := by
  rw[← eq_iff_ext]
  apply Iff.intro
  · intro h
    let hb := h b
    let hc := h c
    simp only [mem_pair_iff', or_true, true_iff, iff_true] at hb hc
    rcases hb with ⟨rfl|rfl⟩
    · simp only [or_self] at hc
      exact Eq.symm hc
    · assumption
  · intro h x
    rw[h]

@[simp] theorem pair_eq_singleton_iff {a b c: set}: pair b c = {a} ↔ (a = b ∧ a = c) := Iff.trans eq_comm singleton_eq_pair_iff

@[simp] theorem ordered_pair_inj {a b c d: set}: ⟪a,b⟫ = ⟪c,d⟫ ↔ (a = c ∧ b = d) := by
  apply Iff.intro
  · intro h
    let h2 := h
    rw[← eq_iff_ext] at h
    have ha := h {a}
    have hb := h (pair a b)
    simp only [mem_ordered_pair_iff, singleton_eq_pair_iff, true_and, true_or, singleton_inj,
      true_iff, or_true] at ha hb
    rcases ha with ac | ⟨ac, ad⟩
    · rcases hb with abc | pair_eq
      · rw[pair_eq_singleton_iff] at abc
        simp only [ac, abc.2, ordered_pair] at h2
        rw[← singleton_def, ← singleton_def, singleton_eq_pair_iff] at h2
        simp at h2
        exact ⟨ac, h2⟩
      · rw[ac, pair_right_inj] at pair_eq
        exact ⟨ac, pair_eq⟩
    · rcases hb with abc | pair_eq
      · rw[pair_eq_singleton_iff] at abc
        exact ⟨ac, abc.2.symm.trans (ac.symm.trans ad)⟩
      · rw[← ac, ← ad, ← singleton_def, pair_eq_singleton_iff] at pair_eq
        exact ⟨ac, pair_eq.2.symm.trans ad⟩
  · rintro ⟨h1,h2⟩
    simp only[*]

prefix:110 "⋃ " => set_union

instance: Union set where
  union a b := ⋃ (pair a b)

theorem union_def {a b: set}: a ∪ b = ⋃ (pair a b) := Eq.refl _


@[simp] theorem mem_set_union_iff' {a x: set}: x ∈ set_union a ↔ ∃y ∈ a, x ∈ y := mem_set_union_iff
@[simp] theorem mem_separation_iff' {P} {a x: set}: x ∈ separation P a ↔ (x ∈ a ∧ P x) := mem_separation_iff

instance: Insert set set where
  insert a b := {a} ∪ b

theorem insert_def {a b: set}: insert a b = {a} ∪ b := Eq.refl _

instance: Inter set where
  inter a b := separation (fun x => x ∈ b) a

theorem inter_def {a b: set}: a ∩ b = separation (fun x => x ∈ b) a := Eq.refl _

@[simp] theorem mem_union_iff {a b x: set}: x ∈ a ∪ b ↔ (x ∈ a ∨ x ∈ b) := by simp only [union_def,
  mem_set_union_iff', mem_pair_iff', exists_eq_or_imp, exists_eq_left]

@[simp] theorem mem_inter_iff {a b x: set}: x ∈ a ∩ b ↔ (x ∈ a ∧ x ∈ b) := by simp only [inter_def,
  mem_separation_iff']

theorem mem_union_self_singleton_iff {a x: set}: x ∈ a ∪ {a} ↔ (x ∈ a ∨ x = a) := by simp only [mem_union_iff,
  mem_singleton_iff]

theorem union_comm {a b: set}: a ∪ b = b ∪ a := by ext; simp only [mem_union_iff, or_comm]

theorem inter_comm {a b: set}: a ∩ b = b ∩ a := by ext; simp only [mem_inter_iff, and_comm]

theorem union_assoc {a b c: set}: (a ∪ b) ∪ c = a ∪ (b ∪ c) := by ext; simp only [mem_union_iff,
  or_assoc]

theorem inter_assoc {a b c: set}: (a ∩ b) ∩ c = a ∩ (b ∩ c) := by ext; simp only [mem_inter_iff, and_assoc]

theorem inter_distrib_left_union {a b c: set}: a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by ext; simp only [mem_inter_iff,
  mem_union_iff, and_or_left]
theorem inter_distrib_right_union {a b c: set}: (b ∪ c) ∩ a = (b ∩ a) ∪ (c ∩ a) := by ext; simp only [mem_inter_iff,
  mem_union_iff, or_and_right]

theorem union_distrib_left_inter {a b c: set}: a ∪ (b ∩ c) = (a ∪ b) ∩ (a ∪ c) := by ext; simp only [mem_union_iff,
  mem_inter_iff, or_and_left]

theorem union_distrib_right_inter {a b c: set}: (b ∩ c) ∪ a = (b ∪ a) ∩ (c ∪ a) := by ext; simp only [mem_union_iff,
  mem_inter_iff, and_or_right]

instance: HasSubset set where
  Subset a b := ∀x, x ∈ a → x ∈ b

theorem Subset.from {a b: set} (h: ∀ x, x ∈ a → x ∈ b): a ⊆ b := h
theorem Subset.def {a b: set}: a ⊆ b ↔ (∀ x, x ∈ a → x ∈ b) := Iff.refl _

instance: HasSSubset set where
  SSubset a b := a ⊆ b ∧ a ≠ b

theorem SSubset.def {a b: set}: a ⊂ b ↔ (a ⊆ b ∧ a ≠ b) := Iff.refl _

@[simp] theorem mem_powerset_iff_subset {a b: set}: a ∈ powerset b ↔ a ⊆ b := by rw[mem_powerset_iff, Subset.def]

theorem Subset.trans {a b c: set} (h: a ⊆ b) (h2: b ⊆ c): a ⊆ c := fun x h3 => h2 x (h x h3)

theorem inter_subset_inter_right {a b c: set} (h: a ⊆ b): c ∩ a ⊆ c ∩ b :=
  fun x h2 => by rw[mem_inter_iff] at *; exact And.imp_right (h x) h2

theorem inter_subset_inter_left {a b c: set} (h: a ⊆ b): a ∩ c ⊆ b ∩ c := fun x h2 => by rw[mem_inter_iff] at *; exact And.imp_left (h x) h2

theorem inter_subset_inter {a b c d: set} (h : a ⊆ c) (h2 : b ⊆ d): a ∩ b ⊆ c ∩ d :=
    fun x h3 => by rw[mem_inter_iff] at *; exact And.imp (h x) (h2 x) h3

theorem union_subset_union_right {a b c: set} (h: a ⊆ b): c ∪ a ⊆ c ∪ b :=
  fun x h2 => by rw[mem_union_iff] at *; exact Or.imp_right (h x) h2

theorem union_subset_union_left {a b c: set} (h: a ⊆ b): a ∪ c ⊆ b ∪ c :=
  fun x h2 => by rw[mem_union_iff] at *; exact Or.imp_left (h x) h2

theorem union_subset_union {a b c d: set} (h : a ⊆ c) (h2 : b ⊆ d): a ∪ b ⊆ c ∪ d :=
    fun x h3 => by rw[mem_union_iff] at *; exact Or.imp (h x) (h2 x) h3

@[simp] theorem union_right_self_eq_iff_subset {a b: set}: a ∪ b = b ↔ a ⊆ b :=
  by rw[Subset.def, ←eq_iff_ext]; apply forall_congr'; intro x; simp only [mem_union_iff,
    or_iff_right_iff_imp]

@[simp] theorem union_left_self_eq_iff_subset {a b: set}: b ∪ a = b ↔ a ⊆ b :=
  by rw[Subset.def, ←eq_iff_ext]; apply forall_congr'; intro x; simp only [mem_union_iff,
    or_iff_left_iff_imp]

@[simp] theorem inter_right_self_eq_iff_subset {a b: set}: a ∩ b = b ↔ b ⊆ a :=
    by rw[Subset.def, ←eq_iff_ext]; apply forall_congr'; intro x; simp only [mem_inter_iff,
      and_iff_right_iff_imp]

@[simp] theorem inter_left_self_eq_iff_subset {a b: set}: b ∩ a = b ↔ b ⊆ a :=
    by rw[Subset.def, ←eq_iff_ext]; apply forall_congr'; intro x; simp only [mem_inter_iff,
      and_iff_left_iff_imp]

@[refl, simp] theorem Subset.refl {a: set}: a ⊆ a := fun _ => id

theorem Subset.antisymm {a b: set} (h: a ⊆ b) (h2 : b ⊆ a): a = b := extensionality (fun x => ⟨h x, h2 x⟩)

theorem Subset.antisymm_iff {a b: set}: (a ⊆ b ∧ b ⊆ a) ↔ a = b :=
  Iff.intro (fun x => Subset.antisymm x.1 x.2) (fun x => by rw[x]; simp only [refl, and_self])

theorem SSubset.irrfl {a : set}: ¬ a ⊂ a := fun h => h.2 (Eq.refl _)

theorem SSubset.iff_exists_mem_left {a b: set}: a ⊂ b ↔ (a ⊆ b ∧ ∃x, (x ∈ b ∧ x ∉ a)) := by
  apply Iff.intro
  · intro h
    apply And.intro h.1
    by_contra h2
    rw[not_exists] at h2
    apply h.2
    apply Subset.antisymm h.1
    intro x h3
    specialize h2 x
    apply not_not.mp
    intro h4
    exact h2 ⟨h3, h4⟩
  · apply And.imp_right
    intro h h2
    rw[h2] at h
    simp only [and_not_self, exists_false] at *

theorem SSubset.trans {a b c: set} (h: a ⊂ b) (h2: b ⊂ c): a ⊂ c := by
  rw[SSubset.iff_exists_mem_left] at *
  apply And.intro $ Subset.trans h.1 h2.1
  rcases h2 with ⟨_, ⟨x, ⟨xc,xb⟩⟩⟩
  exists x
  apply And.intro xc
  intro xa
  exact xb $ h.1 x xa

theorem SSubset.asymm {a b: set} (h: a ⊂ b) (h2: b ⊂ a): False := SSubset.irrfl $ SSubset.trans h h2

@[simp] theorem subset_left_union {a b: set}: a ⊆ a ∪ b := fun x h => by simp only [mem_union_iff]; exact Or.inl h
@[simp] theorem subset_right_union {a b: set}: b ⊆ a ∪ b := fun x h => by simp only [mem_union_iff]; exact Or.inr h

@[simp] theorem left_inter_subset {a b: set}: a ∩ b ⊆ a := fun x h => by simp only [mem_inter_iff] at h; exact h.1
@[simp] theorem right_inter_subset {a b: set}: a ∩ b ⊆ b := fun x h => by simp only [mem_inter_iff] at h; exact h.2

theorem set_union_subset_set_union {a b: set} (h: a ⊆ b): ⋃ a ⊆ ⋃ b := by
  intro x h2
  simp only [mem_set_union_iff'] at *
  rcases h2 with ⟨y, ⟨h3,h4⟩⟩
  exact ⟨y, ⟨h y h3, h4⟩⟩

@[simp] theorem self_mem_powerset {a: set}: a ∈ powerset a := by simp only [mem_powerset_iff_subset,
  Subset.refl]

@[simp] theorem singleton_subset_iff_mem {a b: set}: {a} ⊆ b ↔ a ∈ b := by simp only [Subset.def,
  mem_singleton_iff, forall_eq]

@[simp] theorem singleton_mem_powerset_iff_mem {a b: set}: {a} ∈ powerset b ↔ a ∈ b := by simp only [mem_powerset_iff_subset,
  singleton_subset_iff_mem]

@[simp] theorem set_union_singleton {a: set}: ⋃ {a} = a := by ext x; simp only [mem_set_union_iff', mem_singleton_iff, exists_eq_left]

@[simp] theorem set_union_powerset_eq_self {a: set}: ⋃(powerset a) = a := by
  apply Subset.antisymm
  · intro x h
    simp only [mem_set_union_iff', mem_powerset_iff_subset] at h
    rcases h with ⟨y, ⟨ya,xy⟩⟩
    exact ya x xy
  · rw[← set_union_singleton (a := a)]
    apply set_union_subset_set_union
    simp only [set_union_singleton, singleton_subset_iff_mem, mem_powerset_iff_subset, Subset.refl]

@[simp] theorem powerset_subset_powerset_iff_subset {a b: set}: powerset a ⊆ powerset b ↔ a ⊆ b := by
  apply Iff.intro
  · intro h x xa
    rw[← singleton_mem_powerset_iff_mem] at *
    apply h _ xa
  · intro h x
    simp only [mem_powerset_iff_subset]
    exact fun h2 => Subset.trans h2 h

@[simp] theorem powerset_injective {a b: set}: powerset a = powerset b ↔ a = b := by
  apply Iff.intro
  · intro h
    apply Subset.antisymm
    · have fact := self_mem_powerset (a := a)
      rwa[h, mem_powerset_iff_subset] at fact
    · have fact := self_mem_powerset (a := b)
      rwa[← h, mem_powerset_iff_subset] at fact
  · exact congr_arg powerset

@[simp] theorem powerset_sSubset_powerset_iff_sSubset {a b: set}: powerset a ⊂ powerset b ↔ a ⊂ b := by
  rw[SSubset.def, SSubset.def]
  simp only [powerset_subset_powerset_iff_subset, ne_eq, powerset_injective]

@[simp] theorem mem_replacement_iff' {f} {a x: set} : x ∈ replacement f a ↔ ∃y ∈ a, f y = x := mem_replacement_iff

@[simp] theorem mem_replacement_of_mem {f} {a x: set} (h : x ∈ a) : f x ∈ replacement f a := by simp only [mem_replacement_iff']; exists x

instance : SDiff set where
  sdiff a b := separation (fun x => x ∉ b) a

theorem sdiff_def {a b: set}: a \ b = separation (fun x => x ∉ b) a := Eq.refl _

@[simp] theorem mem_sdiff_iff {a b x: set}: x ∈ a \ b ↔ (x ∈ a ∧ x ∉ b) := by simp only [sdiff_def, mem_separation_iff']
@[simp] theorem not_mem_empty' {x: set}: x ∉ (∅: set) := not_mem_empty
@[simp] theorem mem_empty_iff {x: set}: x ∈ (∅: set) ↔ False := by simp only [not_mem_empty]

@[simp] theorem sdiff_self_eq_empty {a: set}: a \ a = ∅ := by ext; simp only [mem_sdiff_iff,
  and_not_self, mem_empty_iff]

theorem iff_iff_not_iff {p q: Prop}: (p ↔ q) ↔ ((¬ p) ↔ (¬ q)) := by
  apply Iff.intro not_congr
  intro h
  rw[← not_not (a := p), ← not_not (a := q)]
  exact not_congr h


theorem ne_empty_iff_exists_mem {a: set}: a ≠ ∅ ↔ ∃x, x ∈ a := by
  rw[iff_iff_not_iff]
  simp only [ne_eq, not_not, not_exists]
  apply Iff.intro (by rintro rfl; simp only [mem_empty_iff, not_false_eq_true, implies_true])
  intro h
  ext x
  simp only [h, mem_empty_iff]

@[simp] theorem not_mem_self {a: set}: a ∉ a := by
  intro h
  rcases weak_regularity (mem_singleton (a := a)) with ⟨x,⟨xa, h2⟩⟩
  simp only [mem_singleton_iff] at xa
  specialize h2 a (mem_singleton (a := a))
  rw[xa] at h2
  exact h2 h

@[simp] theorem mem_asymm {a b: set} (h: a ∈ b) (h2: b ∈ a): False := by
  rcases weak_regularity (mem_pair_right (a := a) (b := b)) with ⟨x,⟨xa, h3⟩⟩
  simp only [mem_pair_iff'] at xa
  rcases xa with l|r
  · specialize h3 b mem_pair_right
    rw[l] at h3
    exact h3 h2
  · specialize h3 a mem_pair_left
    rw[r] at h3
    exact h3 h

theorem univ_proper_class: is_proper_class (fun (_: set) => True)
| ⟨x,h⟩ => not_mem_self $ of_eq_true $ congrFun h x

@[simp] theorem empty_subset {a: set}: ∅ ⊆ a := by simp only [Subset.def, mem_empty_iff,
  false_implies, implies_true]

@[simp] theorem subset_empty_iff_eq_empty {a: set}: a ⊆ ∅ ↔ a = ∅ := by rw[← Subset.antisymm_iff]; simp only [empty_subset,
  and_true]

theorem reprs_set_from_contained_in_set {a: set} {A: classes} (h: ∀x, A x → x ∈ a): reprs_set A := by
  exists separation A a
  ext x
  specialize h x
  simpa only [mem_separation_iff', and_iff_right_iff_imp]

theorem mem_russell {a: set}: russell_class a := not_mem_self
theorem eq_empty_iff_not_mem {a: set}: a = ∅ ↔ (∀x, x ∉ a) := by
  apply Iff.intro
  · intro h x
    simp only [h, mem_empty_iff, not_false_eq_true]
  · intro h
    ext x
    specialize h x
    simp only [h, mem_empty_iff]

  
@[simp] theorem sdiff_empty_iff_subset {a b: set}: a \ b = ∅ ↔ a ⊆ b := by
  simp only [eq_empty_iff_not_mem, mem_sdiff_iff, not_and, not_not, Subset.def]



theorem sdiff_distrib_left_union {a b c: set}: a \ (b ∪ c) = (a \ b) ∩ (a \ c) := by
  ext x; simp only [mem_sdiff_iff, mem_union_iff, mem_inter_iff]
  rw[Decidable.or_iff_not_and_not, not_not, and_assoc]
  apply and_congr_right
  simp only [and_congr_right_iff, iff_and_self]
  exact fun h _ _ => h

theorem sdiff_distrib_left_inter {a b c: set}: a \ (b ∩ c) = (a \ b) ∪ (a \ c) := by
  ext x; simp only [mem_sdiff_iff, mem_inter_iff, mem_union_iff]
  rw[Decidable.not_and_iff_or_not, and_or_left]

theorem sdiff_distrib_right_union {a b c: set}: (a ∪ b) \ c = a \ c ∪ b \ c := by
  ext x; simp only [mem_sdiff_iff, mem_union_iff]
  rw[or_and_right]

theorem sdiff_distrib_right_inter {a b c: set}: (a ∩ b) \ c = (a \ c) ∩ (b \ c) := by
  ext x; simp only [mem_sdiff_iff, mem_inter_iff]
  rw[and_and_right]

@[simp] theorem sdiff_cancel_right {a b: set}: a \ (b \ a) = a := by
  ext x; simp only [mem_sdiff_iff, not_and, not_not, and_iff_left_iff_imp]
  exact fun x _ => x

theorem inter_distrib_left_sdiff {a b c: set}: a ∩ (b \ c) = (a ∩ b) \ (a ∩ c) := by
  ext x; simp only [mem_inter_iff, mem_sdiff_iff, not_and]
  rw[and_assoc]
  apply and_congr_right
  intro h
  simp only [h, forall_const]

theorem sdiff_distrib_right_inter' {a b c: set}: (a ∩ b) \ c = (a ∩ b) \ (a ∩ c) := by
  ext x; simp only [mem_sdiff_iff, mem_inter_iff, not_and, and_congr_right_iff, and_imp]
  intro h _
  simp only [h, forall_const]

theorem union_sdiff_eq_union_diff_diff {a b c: set}: a ∪ (b \ c) = (a ∪ b) \ (c \ a) := by
  ext x; simp only [mem_union_iff, mem_sdiff_iff, not_and, not_not]
  rw[or_and_right]
  apply Iff.intro
  · rintro (h|h)
    · simp only [h, implies_true, and_self, and_true, true_or]
    · exact Or.inr ⟨h.1, False.elim ∘ h.2⟩
  · rintro (h|h)
    · exact Or.inl h.1
    · rcases em $ x ∈ c with h2|h2
      · exact Or.inl (h.2 h2)
      · exact Or.inr ⟨h.1,h2⟩

theorem union_sdiff_eq_union_sdiff_inter_sdiff {a b c: set}: a ∪ (b \ c) = (a ∪ b) \ ((b ∩ c) \ a) := by
  ext x; simp only [mem_union_iff, mem_sdiff_iff, mem_inter_iff, not_and, not_not, and_imp]
  apply Iff.intro
  · rintro (h|h)
    · exact ⟨Or.inl h, fun _ _ => h⟩
    · exact ⟨Or.inr h.1, fun _ a => False.elim $ h.2 a⟩
  · rintro ⟨(h|h),h2⟩
    · exact Or.inl h
    · rcases em $ x ∈ c with h3|h3
      · exact Or.inl (h2 h h3)
      · exact Or.inr ⟨h, h3⟩

@[simp] theorem sdiff_empty {a: set}: a \ ∅ = a := by ext x; simp only [mem_sdiff_iff,
  mem_empty_iff, not_false_eq_true, and_true]

@[simp] theorem sdiff_subset_self {a b: set}: a \ b ⊆ a := by intro x; simp only [mem_sdiff_iff, and_imp]; exact fun a _ => a

@[simp] theorem sdiff_sdiff_eq_sdiff_union {a b c: set}: (a \ b) \ c = a \ (b ∪ c) := by
  rw[sdiff_distrib_left_union]
  ext x; simp only [mem_sdiff_iff, mem_inter_iff, and_congr_right_iff, iff_and_self, and_imp]
  exact fun a _ _ => a

@[simp] theorem pair_subset_iff {a b x: set}: pair a b ⊆ x ↔ (a ∈ x ∧ b ∈ x) := by
  apply Iff.intro
  · exact fun h => ⟨h a mem_pair_left, h b mem_pair_right⟩
  · rintro ⟨ha, hb⟩ w hw
    simp only [mem_pair_iff'] at hw
    rcases hw with hw|hw
    · rwa[hw]
    · rwa[hw]

@[simp] theorem union_subset_iff {a b c: set}: a ∪ b ⊆ c ↔ (a ⊆ c ∧ b ⊆ c) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro x hx
      apply h x
      simp only [mem_union_iff, hx, true_or]
    · intro x hx
      apply h x
      simp only [mem_union_iff, hx, or_true]
  · rintro ⟨ha,hb⟩ x y
    simp only [mem_union_iff] at y
    rcases y with y|y
    · exact ha _ y
    · exact hb _ y

@[simp] theorem subset_inter_iff {a b c: set}: a ⊆ b ∩ c ↔ (a ⊆ b ∧ a ⊆ c) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · apply Subset.trans h left_inter_subset
    · apply Subset.trans h right_inter_subset
  · rintro ⟨hb, hc⟩ x hx
    simp only [mem_inter_iff]
    exact ⟨hb _ hx, hc _ hx⟩
-- TODO 5.22 (requires strong induction)
end ZFC
