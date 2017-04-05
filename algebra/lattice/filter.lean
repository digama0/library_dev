/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of filters on sets.
-/
import .complete_lattice ...data.set

open lattice set

universes u v w

namespace lattice
variables {α : Type u} [complete_lattice α]

lemma Inf_eq_finite_sets {s : set α} :
  Inf s = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t) :=
le_antisymm 
  (le_infi $ take t, le_infi $ take ⟨_, h⟩, Inf_le_Inf h)
  (le_Inf $ take b h, infi_le_of_le {b} $ infi_le_of_le (by simp [h]) $ Inf_le $ by simp)

end lattice

section order
variables {α : Type u} (r : α → α → Prop)
local infix `≼` : 50 := r

def directed {ι : Sort v} (f : ι → α) := ∀x, ∀y, ∃z, f z ≼ f x ∧ f z ≼ f y
def directed_on (s : set α) := ∀x ∈ s, ∀y ∈ s, ∃z ∈ s, z ≼ x ∧ z ≼ y

lemma directed_on_Union {r} {ι : Sort v} {f : ι → set α} (hd : directed (⊇) f)
  (h : ∀x, directed_on r (f x)) : directed_on r (⋃x, f x) :=
by simp [directed_on]; exact
  take a₁ ⟨b₁, fb₁⟩ a₂ ⟨b₂, fb₂⟩,
  let
    ⟨z, zb₁, zb₂⟩ := hd b₁ b₂,
    ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂) 
  in
    ⟨x, xa₁, xa₂, z, xf⟩

def upwards (s : set α) := ∀{x y}, x ∈ s → x ≼ y → y ∈ s

end order

section applicative
variables {f : Type u → Type v} [applicative f] {α β : Type u}

lemma pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x :=
@applicative.pure_seq_eq_map f _

end applicative

section monad
variables {α β γ : Type u} {m : Type u → Type v} [monad m]

theorem map_bind (x : m α) {g : α → m β} {f : β → γ} : f <$> (x >>= g) = (x >>= λa, f <$> g a) :=
show monad.map f (monad.bind x g) = monad.bind x (λa, monad.map f (g a)),
  by rw [-monad.bind_pure_comp_eq_map]; simp [monad.bind_pure_comp_eq_map, monad.bind_assoc]

theorem seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} : (f <$> x) >>= g = (x >>= g ∘ f) :=
show monad.bind (monad.map f x) g = monad.bind x (g ∘ f),
by rw [-monad.bind_pure_comp_eq_map, monad.bind_assoc]; simp [monad.pure_bind]

theorem seq_eq_bind_map {x : m α} {f : m (α → β)} : f <*> x = (f >>= (<$> x)) :=
(monad.bind_map_eq_seq m f x)^.symm

theorem bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),
  x >>= f >>= g = x >>= λ x, f x >>= g :=
@monad.bind_assoc m _

end monad

structure filter (α : Type u) :=
(sets           : set (set α))
(inhabited      : ∃x, x ∈ sets)
(upwards_sets   : upwards (⊆) sets)
(directed_sets  : directed_on (⊆) sets)

namespace filter
variables {α : Type u} {β : Type v} {ι : Sort w}

lemma filter_eq : ∀{f g : filter α}, f^.sets = g^.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl

lemma univ_mem_sets' {f : filter α} {s : set α} (h : ∀ a, a ∈ s): s ∈ f^.sets :=
let ⟨x, x_in_s⟩ := f^.inhabited in
f^.upwards_sets x_in_s (take x _, h x)

lemma univ_mem_sets {f : filter α} : univ ∈ f^.sets :=
univ_mem_sets' mem_univ

lemma inter_mem_sets {f : filter α} {x y : set α} (hx : x ∈ f^.sets) (hy : y ∈ f^.sets) :
  x ∩ y ∈ f^.sets :=
let ⟨z, ⟨z_in_s, z_le_x, z_le_y⟩⟩ := f^.directed_sets _ hx _ hy in
f^.upwards_sets z_in_s (subset_inter z_le_x z_le_y)

lemma exists_sets_subset_iff {f : filter α} {x : set α} :
  (∃y∈f^.sets, y ⊆ x) ↔ x ∈ f^.sets :=
⟨take ⟨y, hy, yx⟩, f^.upwards_sets hy yx,
  take hx, ⟨x, hx, subset.refl _⟩⟩

def principal (s : set α) : filter α :=
{ filter .
  sets          := {t | s ⊆ t},
  inhabited     := ⟨s, subset.refl _⟩,
  upwards_sets  := take x y hx hy, subset.trans hx hy,
  directed_sets := take x hx y hy, ⟨s, subset.refl _, hx, hy⟩ }

def join (f : filter (filter α)) : filter α :=
{ filter .
  sets          := {s | {t | s ∈ filter.sets t} ∈ f^.sets},
  inhabited     := ⟨univ, by simp [univ_mem_sets]; exact univ_mem_sets⟩,
  upwards_sets  := take x y hx xy, f^.upwards_sets hx $ take a h, a^.upwards_sets h xy,
  directed_sets := take x hx y hy, ⟨x ∩ y,
    f^.upwards_sets (inter_mem_sets hx hy) $ take z ⟨h₁, h₂⟩, inter_mem_sets h₁ h₂, 
    inter_subset_left _ _,  inter_subset_right _ _⟩ }

def map (m : α → β) (f : filter α) : filter β :=
{ filter .
  sets          := {s | {x | m x ∈ s} ∈ f^.sets},
  inhabited     := ⟨univ, univ_mem_sets⟩,
  upwards_sets  := take s t hs st, f^.upwards_sets hs (take x h, st h),
  directed_sets := take s hs t ht, ⟨s ∩ t, inter_mem_sets hs ht,
    inter_subset_left _ _,  inter_subset_right _ _⟩ }

protected def sup (f g : filter α) : filter α :=
{ filter .
  sets          := f^.sets ∩ g^.sets,
  inhabited     := ⟨univ, by simp [univ_mem_sets]; exact univ_mem_sets⟩,
  upwards_sets  := take x y hx xy,
    and.imp (take h, f^.upwards_sets h xy) (take h, g^.upwards_sets h xy) hx,
  directed_sets := take x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨x ∩ y,
    ⟨inter_mem_sets hx₁ hy₁, inter_mem_sets hx₂ hy₂⟩,
    inter_subset_left _ _,  inter_subset_right _ _⟩ }

protected def inf (f g : filter α) :=
{ filter .
  sets          := {s | ∃ a ∈ f^.sets, ∃ b ∈ g^.sets, a ∩ b ⊆ s },
  inhabited     := ⟨univ, univ, univ_mem_sets, univ, univ_mem_sets, subset_univ _⟩,
  upwards_sets  := take x y ⟨a, ha, b, hb, h⟩ xy,
    ⟨a, ha, b, hb, subset.trans h xy⟩,
  directed_sets := take x ⟨a₁, ha₁, b₁, hb₁, h₁⟩ y ⟨a₂, ha₂, b₂, hb₂, h₂⟩,
    ⟨x ∩ y, 
      ⟨_, inter_mem_sets ha₁ ha₂, _, inter_mem_sets hb₁ hb₂,
        calc (a₁ ⊓ a₂) ⊓ (b₁ ⊓ b₂) = (a₁ ⊓ b₁) ⊓ (a₂ ⊓ b₂) : by ac_refl
                                ... ≤ x ∩ y : inf_le_inf h₁ h₂ ⟩,
      inter_subset_left _ _, inter_subset_right _ _⟩ }  

def cofinite : filter α :=
{ filter .
  sets          := {s | finite (- s)},
  inhabited     := ⟨univ, by simp⟩,
  upwards_sets  := take s t, assume hs : finite (-s), assume st: s ⊆ t,
    finite_subset hs $ @lattice.neg_le_neg (set α) _ _ _ st,
  directed_sets := take s, assume hs : finite (-s), take t, assume ht : finite (-t),
    ⟨s ∩ t, by simp [compl_inter, finite_union, ht, hs], 
      inter_subset_left _ _, inter_subset_right _ _⟩ }

instance weak_order_filter : weak_order (filter α) :=
{ weak_order .
  le            := λf g, g^.sets ⊆ f^.sets,
  le_antisymm   := take a b h₁ h₂, filter_eq $ subset.antisymm h₂ h₁,
  le_refl       := take a, subset.refl _,
  le_trans      := take a b c h₁ h₂, subset.trans h₂ h₁ }

instance : has_Sup (filter α) := ⟨join ∘ principal⟩

instance inhabited' : _root_.inhabited (filter α) :=
⟨principal ∅⟩

protected lemma le_Sup {s : set (filter α)} {f : filter α} : f ∈ s → f ≤ Sup s :=
take f_in_s t' h, h f_in_s

protected lemma Sup_le {s : set (filter α)} {f : filter α} : (∀g∈s, g ≤ f) → Sup s ≤ f :=
take h a ha g hg, h g hg ha

@[simp]
lemma mem_join_sets {s : set α} {f : filter (filter α)} : s ∈ (join f)^.sets = ({t | s ∈ filter.sets t} ∈ f^.sets) :=
rfl

@[simp]
lemma mem_principal_sets {s t : set α} : s ∈ (principal t)^.sets = (t ⊆ s) :=
rfl

@[simp]
lemma le_principal_iff {s : set α} {f : filter α} : f ≤ principal s ↔ s ∈ f^.sets :=
show (∀{t}, s ⊆ t → t ∈ f^.sets) ↔ s ∈ f^.sets,
  from ⟨take h, h (subset.refl s), take hs t ht, f^.upwards_sets hs ht⟩

lemma principal_mono {s t : set α} : principal s ≤ principal t ↔ s ⊆ t :=
by simp

@[simp]
lemma principal_eq_iff_eq {s t : set α} : principal s = principal t ↔ s = t :=
by simp [eq_iff_le_and_le]; refl

instance complete_lattice_filter : complete_lattice (filter α) :=
{ filter.weak_order_filter with
  sup           := filter.sup,
  le_sup_left   := take a b, inter_subset_left _ _,
  le_sup_right  := take a b, inter_subset_right _ _,
  sup_le        := take a b c h₁ h₂, subset_inter h₁ h₂,
  inf           := filter.inf,
  le_inf        := take f g h fg fh s ⟨a, ha, b, hb, h⟩,
    f^.upwards_sets (inter_mem_sets (fg ha) (fh hb)) h,
  inf_le_left   := take f g s h, ⟨s, h, univ, univ_mem_sets, inter_subset_left _ _⟩,
  inf_le_right  := take f g s h, ⟨univ, univ_mem_sets, s, h, inter_subset_right _ _⟩,
  top           := principal univ,
  le_top        := take a, by simp [top]; apply univ_mem_sets,
  bot           := principal ∅,
  bot_le        := take a, show a^.sets ⊆ {x | ∅ ⊆ x}, by simp; apply subset_univ,
  Sup           := Sup,
  le_Sup        := take s f, filter.le_Sup,
  Sup_le        := take s f, filter.Sup_le,
  Inf           := λs, Sup {x | ∀y∈s, x ≤ y},
  le_Inf        := take s a h, filter.le_Sup h,
  Inf_le        := take s a ha, filter.Sup_le $ take b h, h _ ha }

@[simp]
lemma map_principal {s : set α} {f : α → β} :
  map f (principal s) = principal (set.image f s) :=
filter_eq $ set.ext $ take a, image_subset_iff_subset_vimage^.symm

@[simp]
lemma join_principal_eq_Sup {s : set (filter α)} : join (principal s) = Sup s :=
rfl

instance monad_filter : monad filter :=
{ monad .
  bind       := λα β f m, join (map m f),
  pure       := λα x, principal {x},
  map        := λα β, filter.map,
  id_map     := take α f, filter_eq $ rfl,
  pure_bind  := take α β a f, by simp [Sup_image],
  bind_assoc := take α β γ f m₁ m₂, filter_eq $ rfl,
  bind_pure_comp_eq_map := take α β f x, filter_eq $ by simp [join, map, principal] }

instance : alternative filter :=
{ filter.monad_filter with
  failure := λα, bot,
  orelse  := λα x y, x ⊔ y }

def at_top [weak_order α] : filter α := ⨅ a, principal {b | a ≤ b}
def at_bot [weak_order α] : filter α := ⨅ a, principal {b | b ≤ a}

/- lattice equations -/

@[simp]
lemma mem_bot_sets {s : set α} : s ∈ (⊥ : filter α)^.sets :=
take x, false.elim

@[simp]
lemma mem_sup_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊔ g)^.sets = (s ∈ f^.sets ∧ s ∈ g^.sets) :=
by refl

@[simp]
lemma mem_inf_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊓ g)^.sets = (∃t₁∈f^.sets, ∃t₂∈g^.sets, t₁ ∩ t₂ ⊆ s) :=
by refl

lemma infi_sets_eq {f : ι → filter α} (h : directed (≤) f) (ne : nonempty ι) :
  (infi f)^.sets = (⋃ i, (f i)^.sets) :=
let
  ⟨i⟩          := ne,
  u           := { filter .
    sets          := (⋃ i, (f i)^.sets),
    inhabited     := ⟨univ, begin simp, exact ⟨i, univ_mem_sets⟩ end⟩,
    directed_sets := directed_on_Union (show directed (≤) f, from h) (take i, (f i)^.directed_sets),
    upwards_sets  := by simp [upwards]; exact take x y ⟨j, xf⟩ xy, ⟨j, (f j)^.upwards_sets xf xy⟩ }
in
  subset.antisymm
    (show u ≤ infi f, from le_infi $ take i, le_supr (λi, (f i)^.sets) i)
    (Union_subset $ take i, infi_le f i)

lemma infi_sets_eq' {f : β → filter α} {s : set β} (h : directed_on (λx y, f x ≤ f y) s) (ne : ∃i, i ∈ s) :
  (⨅ i∈s, f i)^.sets = (⋃ i ∈ s, (f i)^.sets) :=
let ⟨i, hi⟩ := ne in
calc (⨅ i ∈ s, f i)^.sets  = (⨅ t : {t // t ∈ s}, (f t^.val))^.sets : by simp [infi_subtype]; refl
  ... = (⨆ t : {t // t ∈ s}, (f t^.val)^.sets) : infi_sets_eq
    (take ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end )
    ⟨⟨i, hi⟩⟩
  ... = (⨆ t ∈ {t | t ∈ s}, (f t)^.sets) : by simp [supr_subtype]; refl

lemma Inf_sets_eq_finite {s : set (filter α)} :
  (complete_lattice.Inf s)^.sets = (⋃ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t)^.sets) :=
calc (Inf s)^.sets = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t)^.sets : by rw [lattice.Inf_eq_finite_sets]
  ... = (⨆ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t)^.sets) : infi_sets_eq'
    (take x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨x ∪ y, ⟨finite_union hx₁ hy₁, union_subset hx₂ hy₂⟩,
      Inf_le_Inf $ subset_union_left _ _, Inf_le_Inf $ subset_union_right _ _⟩)
    ⟨∅, by simp⟩

lemma supr_sets_eq {f : ι → filter α} : (supr f)^.sets = (⋂i, (f i)^.sets) :=
set.ext $ take s, 
show s ∈ (join (principal {a : filter α | ∃i : ι, a = f i}))^.sets ↔ s ∈ (⋂i, (f i)^.sets),
begin
  rw [mem_join_sets],
  simp,
  exact ⟨take h i, h (f i) ⟨_, rfl⟩, take h x ⟨i, eq⟩, eq^.symm ▸ h i⟩
end

@[simp]
lemma sup_join {f₁ f₂ : filter (filter α)} : (join f₁ ⊔ join f₂) = join (f₁ ⊔ f₂) :=
filter_eq $ set.ext $ take x, by simp [supr_sets_eq, join]

@[simp]
lemma supr_join {ι : Sort w} {f : ι → filter (filter α)} : (⨆x, join (f x)) = join (⨆x, f x) :=
filter_eq $ set.ext $ take x, by simp [supr_sets_eq, join]

instance : bounded_distrib_lattice (filter α) :=
{ filter.complete_lattice_filter with
  le_sup_inf := take x y z s h,
  begin
    cases h with h₁ h₂, revert h₂,
    simp,
    exact take ⟨t₁, ht₁, t₂, ht₂, hs⟩, ⟨s ∪ t₁, 
      x^.upwards_sets h₁ $ subset_union_left _ _,
      y^.upwards_sets ht₁ $ subset_union_right _ _,
      s ∪ t₂, 
      x^.upwards_sets h₁ $ subset_union_left _ _,
      z^.upwards_sets ht₂ $ subset_union_right _ _,
      subset.trans (@le_sup_inf (set α) _ _ _ _) (union_subset (subset.refl _) hs)⟩
  end }

private theorem infi_finite_distrib {s : set (filter α)} {f : filter α} (h : finite s) :
  (⨅ a ∈ s, f ⊔ a) = f ⊔ (Inf s) :=
begin
  induction h with a s hn hs hi,
  { simp, exact infi_const bot },
  { simp [hi, sup_inf_left] }
end

/- the complementary version with ⨆ g∈s, f ⊓ g does not hold! -/
lemma infi_sup_eq { f : filter α } {s : set (filter α)} :
  (⨅ g∈s, f ⊔ g) = f ⊔ complete_lattice.Inf s :=
le_antisymm
  begin
    intros t h,
    cases h with h₁ h₂,
    rw [Inf_sets_eq_finite] at h₂,
    simp at h₂,
    cases h₂ with s' hs', cases hs' with hs' hs'', cases hs'' with hs's ht',
    assert ht : t ∈ (⨅ a ∈ s', f ⊔ a)^.sets,
    { rw [infi_finite_distrib], exact ⟨h₁, ht'⟩, exact hs' },
    clear h₁ ht',
    revert ht t,
    change (⨅ a ∈ s, f ⊔ a) ≤ (⨅ a ∈ s', f ⊔ a),
    apply infi_le_infi2 _,
    exact take i, ⟨i, infi_le_infi2 $ take h, ⟨hs's h, le_refl _⟩⟩
  end
  (le_infi $ take g, le_infi $ take h, sup_le_sup (le_refl f) $ Inf_le h)

/- principal equations -/

@[simp]
lemma inf_principal {s t : set α} : principal s ⊓ principal t = principal (s ∩ t) :=
le_antisymm
  (by simp; exact ⟨s, subset.refl s, t, subset.refl t, subset.refl _⟩)
  (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp]
lemma sup_principal {s t : set α} : principal s ⊔ principal t = principal (s ∪ t) :=
filter_eq $ set.ext $ by simp [union_subset_iff]

@[simp]
lemma supr_principal {ι : Sort w} {s : ι → set α} : (⨆x, principal (s x)) = principal (Union s) :=
filter_eq $ set.ext $ take x, by simp [supr_sets_eq]; exact (@supr_le_iff (set α) _ _ _ _)^.symm

lemma principal_univ : principal (univ : set α) = top :=
rfl

lemma principal_empty : principal (∅ : set α) = bot :=
rfl

/- map equations -/

@[simp]
lemma mem_map {f : filter α} {s : set β} {m : α → β} :
  (s ∈ (map m f)^.sets) = ({x | m x ∈ s} ∈ f^.sets) :=
by refl

@[simp]
lemma map_id {f : filter α} : filter.map id f = f :=
filter_eq $ rfl

@[simp]
lemma map_compose {γ : Type w} {f : α → β} {g : β → γ} :
  filter.map g ∘ filter.map f = filter.map (g ∘ f) :=
funext $ take _, filter_eq $ rfl

@[simp]
lemma map_sup {f g : filter α} {m : α → β} : map m (f ⊔ g) = map m f ⊔ map m g :=
filter_eq $ set.ext $ take x, by simp

@[simp]
lemma supr_map {ι : Sort w} {f : ι → filter α} {m : α → β} : (⨆x, map m (f x)) = map m (⨆x, f x) :=
filter_eq $ set.ext $ take x, by simp [supr_sets_eq, map]

@[simp]
lemma map_bot {m : α → β} : map m ⊥ = ⊥ :=
filter_eq $ set.ext $ take x, by simp

lemma map_mono {f g : filter α} {m : α → β} (h : f ≤ g) : map m f ≤ map m g :=
le_of_sup_eq $ calc
  map m f ⊔ map m g = map m (f ⊔ g) : map_sup
                ... = map m g : congr_arg (map m) $ sup_of_le_right h

-- this is a generic rule for monotone functions:
lemma map_infi_le {f : ι → filter α} {m : α → β} :
  map m (infi f) ≤ (⨅ i, map m (f i)) :=
le_infi $ take i, map_mono $ infi_le _ _

/- bind equations -/

lemma mem_bind_sets {β : Type u} {s : set β} {f : filter α} {m : α → filter β} :
  s ∈ (f >>= m)^.sets ↔ (∃t ∈ f^.sets, ∀x ∈ t, s ∈ (m x)^.sets) :=
calc s ∈ (f >>= m)^.sets ↔ {a | s ∈ (m a)^.sets} ∈ f^.sets : by simp [bind]
                     ... ↔ (∃t ∈ f^.sets, t ⊆ {a | s ∈ (m a)^.sets}) : exists_sets_subset_iff^.symm
                     ... ↔ (∃t ∈ f^.sets, ∀x ∈ t, s ∈ (m x)^.sets) : iff.refl _

lemma bind_mono {β : Type u} {f : filter α} {g h : α → filter β} (h₁ : {a | g a ≤ h a} ∈ f^.sets) :
  f >>= g ≤ f >>= h :=
take x h₂, f^.upwards_sets (inter_mem_sets h₁ h₂) $ take s ⟨gh', h'⟩, gh' h'

lemma bind_sup {β : Type u} {f g : filter α} {h : α → filter β} :
  (f ⊔ g) >>= h = (f >>= h) ⊔ (g >>= h) :=
by simp [bind]

lemma bind_mono2 {β : Type u} {f g : filter α} {h : α → filter β} (h₁ : f ≤ g) :
  f >>= h ≤ g >>= h :=
take s h', h₁ h'

/- requires choice -- prove later
lemma bind_comm_le {β γ : Type u} {f : filter α} {g : filter β} {h : α → β → filter γ} :
  (f >>= (λx, g >>= h x)) ≤ (g >>= (λy, f >>= (λx, h x y))) :=
take x, begin simp [mem_bind_sets] end
-/
 
lemma principal_bind {β : Type u} {s : set α} {f : α → filter β} :
  (principal s >>= f) = (⨆x ∈ s, f x) :=
show join (map f (principal s)) = (⨆x ∈ s, f x),
  by simp [Sup_image]

lemma seq_mono {β : Type u} {f₁ f₂ : filter (α → β)} {g₁ g₂ : filter α}
  (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁ <*> g₁ ≤ f₂ <*> g₂ :=
le_trans (bind_mono2 hf) (bind_mono $ univ_mem_sets' $ take f, map_mono hg)

/- towards -/

def towards (f : α → β) (l₁ : filter α) (l₂ : filter β) :=
filter.map f l₁ ≤ l₂

@[simp]
lemma fmap_principal {β : Type u} {s : set α} {f : α → β} :
  f <$> principal s = principal (set.image f s) :=
filter_eq $ set.ext $ take a, image_subset_iff_subset_vimage^.symm

end filter
