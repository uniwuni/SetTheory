import Std

class ZFC (set : Type) [Membership set set] where
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

namespace ZFC
variable {set : Type} [Membership set set] [ZFC set]
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

@[simp] theorem mem_singleton_iff {a x: set}: x ∈ (singleton a: set) ↔ x = a := by simp only [singleton,
  mem_pair_iff', or_self]

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

@[refl] theorem Subset.refl {a: set}: a ⊆ a := fun _ => id

theorem Subset.antisymm {a b: set} (h: a ⊆ b) (h2 : b ⊆ a): a = b := extensionality (fun x => ⟨h x, h2 x⟩)

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
end ZFC
