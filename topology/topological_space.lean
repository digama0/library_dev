/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of topological spaces.
-/
import algebra.lattice.filter
open set filter lattice

universes u v w

def vimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}

section vimage
variables {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ}

@[simp] lemma vimage_empty : vimage f ∅ = ∅ := rfl

@[simp] lemma vimage_univ : vimage f univ = univ := rfl

@[simp] lemma vimage_inter {s t : set β} : vimage f (s ∩ t) = vimage f s ∩ vimage f t := rfl

@[simp] lemma vimage_union {s t : set β} : vimage f (s ∪ t) = vimage f s ∪ vimage f t := rfl

@[simp] lemma vimage_compl {s : set β} : vimage f (- s) = - vimage f s := rfl

@[simp] lemma vimage_Union {ι : Sort w} {f : α → β} {s : ι → set β} :
  vimage f (⋃i, s i) = (⋃i, vimage f (s i)) :=
set.ext $ by simp [vimage]

@[simp] lemma vimage_sUnion {f : α → β} {s : set (set β)} :
  vimage f (⋃₀ s) = (⋃t ∈ s, vimage f t) :=
set.ext $ by simp [vimage]

lemma vimage_id {s : set α} : vimage id s = s := rfl

lemma vimage_comp {s : set γ} : vimage (g ∘ f) s = vimage f (vimage g s) := rfl

end vimage

@[simp]
lemma not_not_mem_iff {α : Type u} {a : α} {s : set α} : ¬ (a ∉ s) ↔ a ∈ s :=
classical.not_not_iff _

@[simp]
lemma singleton_neq_emptyset {α : Type u} {a : α} : {a} ≠ (∅ : set α) :=
take h, 
have a ∉ ({a} : set α),
  by simp [h],
this $ mem_singleton a

@[simp]
lemma principal_eq_bot_iff {α : Type u} {s : set α} : principal s = ⊥ ↔ s = ∅ :=
principal_eq_iff_eq

@[simp]
lemma return_neq_bot {α : Type u} {a : α} : return a ≠ (⊥ : filter α) :=
by simp [return, pure]

lemma not_imp_iff_not_imp {a b : Prop} :
  (¬ a → ¬ b) ↔ (b → a) :=
⟨take h hb, classical.by_contradiction $ take na, h na hb, 
  contrapos⟩

lemma eq_of_sup_eq_inf_eq {α : Type u} [distrib_lattice α] {a b c : α}
  (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
le_antisymm
  (calc b ≤ (c ⊓ a) ⊔ b     : le_sup_right
    ... = (c ⊔ b) ⊓ (a ⊔ b) : sup_inf_right
    ... = c ⊔ (c ⊓ a)       : by rw [-h₁, sup_inf_left, -h₂]; simp [sup_comm]
    ... = c                 : sup_inf_self)
  (calc c ≤ (b ⊓ a) ⊔ c     : le_sup_right
    ... = (b ⊔ c) ⊓ (a ⊔ c) : sup_inf_right
    ... = b ⊔ (b ⊓ a)       : by rw [h₁, sup_inf_left, h₂]; simp [sup_comm]
    ... = b                 : sup_inf_self)

lemma inf_eq_bot_iff_le_compl {α : Type u} [bounded_distrib_lattice α] {a b c : α}
  (h₁ : b ⊔ c = ⊤) (h₂ : b ⊓ c = ⊥) : a ⊓ b = ⊥ ↔ a ≤ c :=
⟨suppose a ⊓ b = ⊥, 
  calc a ≤ a ⊓ (b ⊔ c) : by simp [h₁]
    ... = (a ⊓ b) ⊔ (a ⊓ c) : by simp [inf_sup_left]
    ... ≤ c : by simp [this, inf_le_right],
  suppose a ≤ c,
  bot_unique $
    calc a ⊓ b ≤ b ⊓ c : by rw [inf_comm]; exact inf_le_inf (le_refl _) this
      ... = ⊥ : h₂⟩

lemma compl_image_set_of {α : Type u} {p : set α → Prop} :
  compl ' {x | p x} = {x | p (- x)} :=
set.ext $ take x, ⟨take ⟨y, (hy : p y), (h_eq : -y = x)⟩,
  show p (- x), by rw [-h_eq, lattice.neg_neg]; assumption,
  assume h : p (-x), ⟨_, h, lattice.neg_neg⟩⟩

lemma neg_subset_neg_iff_subset {α : Type u} {x y : set α} : - y ⊆ - x ↔ x ⊆ y :=
@neg_le_neg_iff_le (set α) _ _ _

lemma sUnion_eq_Union {α : Type u} {s : set (set α)} :
  (⋃₀ s) = (⋃ (i : set α) (h : i ∈ s), i) :=
set.ext $ by simp

structure topological_space (α : Type u) :=
(open'       : set α → Prop)
(open_univ   : open' univ)
(open_inter  : ∀s t, open' s → open' t → open' (s ∩ t))
(open_sUnion : ∀s, (∀t∈s, open' t) → open' (⋃₀ s))

attribute [class] topological_space

section topological_space

variables {α : Type u} {β : Type v} {ι : Sort w} {a a₁ a₂ : α} {s s₁ s₂ : set α}

section
variables [t : topological_space α]
include t

/- open -/
def open' (s : set α) : Prop := topological_space.open' t s

@[simp]
lemma open_univ : open' (univ : set α) := topological_space.open_univ t

lemma open_inter (h₁ : open' s₁) (h₂ : open' s₂) : open' (s₁ ∩ s₂) := topological_space.open_inter t s₁ s₂ h₁ h₂

lemma open_sUnion {s : set (set α)} (h : ∀t ∈ s, open' t) : open' (⋃₀ s) := topological_space.open_sUnion t s h

end

variables [topological_space α]

lemma open_Union {f : ι → set α} (h : ∀i, open' (f i)) : open' (⋃i, f i) :=
open_sUnion $ take t ⟨i, (heq : t = f i)⟩, heq^.symm ▸ h i

@[simp]
lemma open_empty : open' (∅ : set α) :=
have open' (⋃₀ ∅ : set α), from open_sUnion (take a, false.elim),
by simp at this; assumption

/- closed -/
def closed (s : set α) : Prop := open' (-s)

@[simp]
lemma closed_empty : closed (∅ : set α) := by simp [closed]

@[simp]
lemma closed_univ : closed (univ : set α) := by simp [closed]

lemma closed_union : closed s₁ → closed s₂ → closed (s₁ ∪ s₂) :=
by simp [closed]; exact open_inter

lemma closed_sInter {s : set (set α)} : (∀t ∈ s, closed t) → closed (⋂₀ s) :=
by simp [closed, compl_sInter]; exact take h, open_Union $ take t, open_Union $ take ht, h t ht

lemma closed_Inter {f : ι → set α} (h : ∀i, closed (f i)) : closed (⋂i, f i ) :=
closed_sInter $ take t ⟨i, (heq : t = f i)⟩, heq^.symm ▸ h i

@[simp]
lemma closed_compl_iff_open {s : set α} : open' (-s) ↔ closed s :=
by refl

@[simp]
lemma open_compl_iff_closed {s : set α} : closed (-s) ↔ open' s :=
by rw [-closed_compl_iff_open, compl_compl]

lemma open_diff {s t : set α} (h₁ : open' s) (h₂ : closed t) : open' (s - t) :=
open_inter h₁ $ closed_compl_iff_open^.mpr h₂

/- interior -/
def interior (s : set α) : set α := ⋃₀ {t | open' t ∧ t ⊆ s}

@[simp]
lemma open_interior {s : set α} : open' (interior s) :=
open_sUnion $ take t ⟨h₁, h₂⟩, h₁

lemma interior_subset {s : set α} : interior s ⊆ s :=
sUnion_subset $ take t ⟨h₁, h₂⟩, h₂

lemma interior_maximal {s t : set α} (h₁ : t ⊆ s) (h₂ : open' t) : t ⊆ interior s :=
subset_sUnion_of_mem ⟨h₂, h₁⟩

lemma interior_eq_of_open {s : set α} (h : open' s) : interior s = s :=
subset.antisymm interior_subset (interior_maximal (subset.refl s) h)

lemma interior_eq_iff_open {s : set α} : interior s = s ↔ open' s :=
⟨take h, h ▸ open_interior, interior_eq_of_open⟩

lemma subset_interior_iff_subset_of_open {s t : set α} (h₁ : open' s) :
  s ⊆ interior t ↔ s ⊆ t :=
⟨take h, subset.trans h interior_subset, take h₂, interior_maximal h₂ h₁⟩

lemma interior_mono {s t : set α} (h : s ⊆ t) : interior s ⊆ interior t :=
interior_maximal (subset.trans interior_subset h) open_interior

@[simp]
lemma interior_empty : interior (∅ : set α) = ∅ :=
interior_eq_of_open open_empty

@[simp]
lemma interior_univ : interior (univ : set α) = univ :=
interior_eq_of_open open_univ

@[simp]
lemma interior_interior {s : set α} : interior (interior s) = interior s :=
interior_eq_of_open open_interior

@[simp]
lemma interior_inter {s t : set α} : interior (s ∩ t) = interior s ∩ interior t :=
subset.antisymm
  (subset_inter (interior_mono $ inter_subset_left s t) (interior_mono $ inter_subset_right s t))
  (interior_maximal (inter_subset_inter interior_subset interior_subset) $ by simp [open_inter])

lemma interior_union_closed_of_interior_empty {s t : set α} (h₁ : closed s) (h₂ : interior t = ∅) :
  interior (s ∪ t) = interior s :=
have interior (s ∪ t) ⊆ s, from 
  take x ⟨u, ⟨(hu₁ : open' u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩, 
  classical.by_contradiction $ assume hx₂ : x ∉ s,
    have u - s ⊆ t,
      from take x ⟨h₁, h₂⟩, or.resolve_left (hu₂ h₁) h₂,
    have u - s ⊆ interior t,
      by simp [subset_interior_iff_subset_of_open, this, open_diff hu₁ h₁],
    have u - s ⊆ ∅,
      by rw [h₂] at this; assumption,
    this ⟨hx₁, hx₂⟩,
subset.antisymm
  (interior_maximal this open_interior)
  (interior_mono $ subset_union_left _ _)

/- closure -/
def closure (s : set α) : set α := ⋂₀ {t | closed t ∧ s ⊆ t}

@[simp]
lemma closed_closure {s : set α} : closed (closure s) :=
closed_sInter $ take t ⟨h₁, h₂⟩, h₁

lemma subset_closure {s : set α} : s ⊆ closure s :=
subset_sInter $ take t ⟨h₁, h₂⟩, h₂

lemma closure_minimal {s t : set α} (h₁ : s ⊆ t) (h₂ : closed t) : closure s ⊆ t :=
sInter_subset_of_mem ⟨h₂, h₁⟩

lemma closure_eq_of_closed {s : set α} (h : closed s) : closure s = s :=
subset.antisymm (closure_minimal (subset.refl s) h) subset_closure

lemma closure_eq_iff_closed {s : set α} : closure s = s ↔ closed s :=
⟨take h, h ▸ closed_closure, closure_eq_of_closed⟩

lemma closure_subset_iff_subset_of_closed {s t : set α} (h₁ : closed t) :
  closure s ⊆ t ↔ s ⊆ t :=
⟨subset.trans subset_closure, take h, closure_minimal h h₁⟩

lemma closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_minimal (subset.trans h subset_closure) closed_closure

@[simp]
lemma closure_empty : closure (∅ : set α) = ∅ :=
closure_eq_of_closed closed_empty

@[simp]
lemma closure_univ : closure (univ : set α) = univ :=
closure_eq_of_closed closed_univ

@[simp]
lemma closure_closure {s : set α} : closure (closure s) = closure s :=
closure_eq_of_closed closed_closure

@[simp]
lemma closure_union {s t : set α} : closure (s ∪ t) = closure s ∪ closure t :=
subset.antisymm
  (closure_minimal (union_subset_union subset_closure subset_closure) $ by simp [closed_union])
  (union_subset (closure_mono $ subset_union_left _ _) (closure_mono $ subset_union_right _ _))

lemma interior_subset_closure {s : set α} : interior s ⊆ closure s :=
subset.trans interior_subset subset_closure

lemma closure_eq_compl_interior_compl {s : set α} : closure s = - interior (- s) :=
begin
  simp [interior, closure],
  rw [compl_sUnion, compl_image_set_of],
  simp [neg_subset_neg_iff_subset]
end

@[simp]
lemma interior_compl_eq {s : set α} : interior (- s) = - closure s :=
by simp [closure_eq_compl_interior_compl]

@[simp]
lemma closure_compl_eq {s : set α} : closure (- s) = - interior s :=
by simp [closure_eq_compl_interior_compl]

/- neighbourhood filter -/
def nhds (a : α) : filter α := (⨅ s ∈ {s : set α | a ∈ s ∧ open' s}, principal s)

lemma nhds_sets {a : α} : (nhds a)^.sets = {s | ∃t⊆s, open' t ∧ a ∈ t} := 
calc (nhds a)^.sets = (⋃s∈{s : set α| a ∈ s ∧ open' s}, (principal s)^.sets) : infi_sets_eq'
    begin
      simp,
      exact take x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨_, ⟨open_inter hx₁ hy₁, ⟨hx₂, hy₂⟩⟩,
        ⟨inter_subset_left _ _, inter_subset_right _ _⟩⟩
    end
    ⟨univ, by simp⟩
  ... = {s | ∃t⊆s, open' t ∧ a ∈ t} :
   le_antisymm
     (supr_le $ take i, supr_le $ take ⟨hi₁, hi₂⟩ t ht, ⟨i, ht, hi₂, hi₁⟩)
     (take t ⟨i, hi₁, hi₂, hi₃⟩, begin simp; exact ⟨i, hi₂, hi₁, hi₃⟩ end)

lemma return_le_nhds : return ≤ (nhds : α → filter α) :=
take a, le_infi $ take s, le_infi $ take ⟨h₁, _⟩, principal_mono^.mpr $ by simp [h₁]

@[simp]
lemma nhds_neq_bot {a : α} : nhds a ≠ ⊥ :=
suppose nhds a = ⊥,
have return a = (⊥ : filter α),
  from lattice.bot_unique $ this ▸ return_le_nhds a,
return_neq_bot this

lemma interior_eq_nhds {s : set α} : interior s = {a | nhds a ≤ principal s} :=
set.ext $ by simp [interior, nhds_sets]

lemma open_iff_nhds {s : set α} : open' s ↔ (∀a∈s, nhds a ≤ principal s) :=
calc open' s ↔ interior s = s : by rw [interior_eq_iff_open]
  ... ↔ s ⊆ interior s : ⟨take h, by simph [subset.refl], subset.antisymm interior_subset⟩
  ... ↔ (∀a∈s, nhds a ≤ principal s) : by rw [interior_eq_nhds]; refl

lemma closure_eq_nhds {s : set α} : closure s = {a | nhds a ⊓ principal s ≠ ⊥} :=
calc closure s = - interior (- s) : closure_eq_compl_interior_compl
  ... = {a | ¬ nhds a ≤ principal (-s)} : by rw [interior_eq_nhds]; refl
  ... = {a | nhds a ⊓ principal s ≠ ⊥} : set.ext $ take a, not_congr
    (inf_eq_bot_iff_le_compl
      (show principal s ⊔ principal (-s) = ⊤, by simp [principal_univ])
      (by simp))^.symm

lemma closed_iff_nhds {s : set α} : closed s ↔ (∀a, nhds a ⊓ principal s ≠ ⊥ → a ∈ s) :=
calc closed s ↔ closure s = s : by rw [closure_eq_iff_closed]
  ... ↔ closure s ⊆ s : ⟨take h, by simph [subset.refl], take h, subset.antisymm h subset_closure⟩
  ... ↔ (∀a, nhds a ⊓ principal s ≠ ⊥ → a ∈ s) : by rw [closure_eq_nhds]; refl

end topological_space

section constructions

variables {α : Type u} {β : Type v}

lemma topological_space_eq : 
  ∀{f g : topological_space α}, f^.open' = g^.open' → f = g :=
begin
  intros f g h', cases f with a, cases g with b,
  assert h : a = b, assumption,
  clear h',
  subst h
end

instance : weak_order (topological_space α) :=
{ weak_order .
  le            := λt s, t^.open' ≤ s^.open',
  le_antisymm   := take t s h₁ h₂, topological_space_eq $ le_antisymm h₁ h₂,
  le_refl       := take t, le_refl t^.open',
  le_trans      := take a b c h₁ h₂, @le_trans _ _ a^.open' b^.open' c^.open' h₁ h₂ }

instance : has_Inf (topological_space α) :=
⟨take (tt : set (topological_space α)), { topological_space .
  open' := λs, ∀t∈tt, topological_space.open' t s,
  open_univ   := take t h, t^.open_univ,
  open_inter  := take s₁ s₂ h₁ h₂ t ht, t^.open_inter s₁ s₂ (h₁ t ht) (h₂ t ht),
  open_sUnion := take s h t ht, t^.open_sUnion _ $ take s' hss', h _ hss' _ ht }⟩

private lemma Inf_le {tt : set (topological_space α)} {t : topological_space α} (h : t ∈ tt) :
  Inf tt ≤ t :=
take s hs, hs t h

private lemma le_Inf {tt : set (topological_space α)} {t : topological_space α} (h : ∀t'∈tt, t ≤ t') :
  t ≤ Inf tt :=
take s hs t' ht', h t' ht' s hs

def topological_space.induced {α : Type u} {β : Type v} (f : α → β) (t : topological_space β) :
  topological_space α :=
{ topological_space .
  open'       := λs, ∃s', t^.open' s' ∧ s = vimage f s',
  open_univ   := ⟨univ, by simp; exact t^.open_univ⟩,
  open_inter  := take s₁ s₂ ⟨s'₁, hs₁, eq₁⟩ ⟨s'₂, hs₂, eq₂⟩,
    ⟨s'₁ ∩ s'₂, by simp [eq₁, eq₂]; exact t^.open_inter _ _ hs₁ hs₂⟩,
  open_sUnion := take s h,
  begin
    simp [classical.skolem] at h,
    cases h with f hf,
    apply exists.intro (⋃(x : set α) (h : x ∈ s), f x h),
    simp [sUnion_eq_Union, (λx h, (hf x h)^.right^.symm)],
    exact (@open_Union β _ t _ $ take i,
      show open' (⋃h, f i h), from @open_Union β _ t _ $ take h, (hf i h)^.left)
  end }

def topological_space.coinduced {α : Type u} {β : Type v} (f : α → β) (t : topological_space α) :
  topological_space β :=
{ topological_space .
  open'       := λs, t^.open' (vimage f s),
  open_univ   := by simp; exact t^.open_univ,
  open_inter  := take s₁ s₂ h₁ h₂, by simp; exact t^.open_inter _ _ h₁ h₂,
  open_sUnion := take s h, by simp; exact (@open_Union _ _ t _ $ take i,
    show open' (⋃ (H : i ∈ s), vimage f i), from
      @open_Union _ _ t _ $ take hi, h i hi) }

instance : has_inf (topological_space α) :=
⟨take t₁ t₂ : topological_space α, { topological_space .
  open'       := λs, t₁.open' s ∧ t₂.open' s,
  open_univ   := ⟨t₁^.open_univ, t₂^.open_univ⟩,
  open_inter  := take s₁ s₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩, ⟨t₁.open_inter s₁ s₂ h₁₁ h₂₁, t₂.open_inter s₁ s₂ h₁₂ h₂₂⟩,
  open_sUnion := take s h, ⟨t₁.open_sUnion _ $ take t ht, (h t ht).left, t₂.open_sUnion _ $ take t ht, (h t ht).right⟩ }⟩

instance : has_top (topological_space α) :=
⟨{topological_space .
  open'       := λs, true,
  open_univ   := trivial,
  open_inter  := take a b ha hb, trivial,
  open_sUnion := take s h, trivial }⟩

instance {α : Type u} : complete_lattice (topological_space α) :=
{ topological_space.weak_order with
  sup           := λa b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left   := take a b, le_Inf $ take x, assume h : a ≤ x ∧ b ≤ x, h^.left,
  le_sup_right  := take a b, le_Inf $ take x, assume h : a ≤ x ∧ b ≤ x, h^.right,
  sup_le        := take a b c h₁ h₂, Inf_le $ show c ∈ {x | a ≤ x ∧ b ≤ x}, from ⟨h₁, h₂⟩,
  inf           := inf,
  le_inf        := take a b h h₁ h₂ s hs, ⟨h₁ s hs, h₂ s hs⟩,
  inf_le_left   := take a b s ⟨h₁, h₂⟩, h₁,
  inf_le_right  := take a b s ⟨h₁, h₂⟩, h₂,
  top           := top,
  le_top        := take a t ht, trivial,
  bot           := Inf univ,
  bot_le        := take a, Inf_le $ mem_univ a,
  Sup           := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup        := take s f h, le_Inf $ take t ht, ht _ h,
  Sup_le        := take s f h, Inf_le $ take t ht, h _ ht,
  Inf           := Inf,
  le_Inf        := take s a, le_Inf,
  Inf_le        := take s a, Inf_le }

instance inhabited_topological_space {α : Type u} : inhabited (topological_space α) :=
⟨⊤⟩

instance : topological_space empty := ⊤
instance : topological_space unit := ⊤
instance : topological_space bool := ⊤
instance : topological_space ℕ := ⊤
instance : topological_space ℤ := ⊤

instance sierpinski_space : topological_space Prop :=
{ topological_space .
  open'       := take s, false ∈ s → true ∈ s,
  open_univ   := take h, mem_univ true,
  open_inter  := take s t, and.imp,
  open_sUnion := take s hs, by simp; exact take ⟨t, ht, hts⟩, ⟨t, hs t hts ht, hts⟩ }

instance {p : α → Prop} [t : topological_space α] : topological_space (subtype p) :=
topological_space.induced subtype.val t

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α × β) :=
topological_space.induced prod.fst t₁ ⊔ topological_space.induced prod.snd t₂

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α ⊕ β) :=
topological_space.coinduced sum.inl t₁ ⊓ topological_space.coinduced sum.inr t₂

/- Fiber bundles?
instance {β : α → Type v} [t : Π(a:α), topological_space (β a)] : topological_space (sigma β) :=
_
-/

end constructions
