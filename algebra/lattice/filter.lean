import .complete_lattice ...data.set.basic

open lattice set

universes u v w

lemma or_imp_iff_and_imp {a b c : Prop} : ((a ∨ b) → c) ↔ ((a → c) ∧ (b → c)) :=
⟨take h, ⟨take ha, h (or.inl ha), take hb, h (or.inr hb)⟩,
  take ⟨ha, hb⟩, or.rec ha hb⟩

lemma forall_and_comm {α : Type u} {p q : α → Prop} : (∀a, p a ∧ q a) ↔ ((∀a, p a) ∧ (∀a, q a)) :=
⟨take h, ⟨take a, (h a)^.left, take a, (h a)^.right⟩,
  take ⟨ha, hb⟩ a, ⟨ha a, hb a⟩⟩

lemma forall_eq_elim {α : Type u} {p : α → Prop} {a' : α} : (∀a, a = a' → p a) ↔ p a' :=
⟨take h, h a' rfl, take h a eq, eq^.symm ▸ h⟩

lemma eq_iff_le_and_le {α : Type u} [weak_order α] {a b : α} : a = b ↔ (a ≤ b ∧ b ≤ a) :=
⟨take eq, eq ▸ ⟨le_refl a, le_refl a⟩, take ⟨ab, ba⟩, le_antisymm ab ba⟩

section set
variables {α : Type u} {β : Type v}

theorem Union_subset {α : Sort u} {s : α → set β} {t : set β} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
-- TODO: should be simpler when sets' order is based on lattices
@supr_le (set β) _ set.lattice_set _ _ h

theorem Union_subset_iff {α : Sort u} {s : α → set β} {t : set β} : (⋃ i, s i) ⊆ t ↔ (∀ i, s i ⊆ t):=
⟨take h i, subset.trans (le_supr s _) h, Union_subset⟩

theorem mem_Inter {α : Sort u} {x : β} {s : α → set β} : (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) :=
take h t ⟨a, (eq : t = s a)⟩, eq^.symm ▸ h a

@[simp]
lemma set_of_subset_set_of {p q : α → Prop} : {a | p a} ⊆ {a | q a} = (∀a, p a → q a) :=
rfl

/- image and vimage are a Galois connection -/
theorem image_subset_iff_subset_vimage {s : set α} {t : set β} {f : α → β} :
  set.image f s ⊆ t ↔ s ⊆ {x | f x ∈ t} :=
⟨take h x hx, h (mem_image_of_mem f hx),
  take h x hx, match x, hx with ._, ⟨y, hy, rfl⟩ := h hy end⟩

lemma union_subset_iff {s t u : set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
@sup_le_iff (set α) _ s t u

@[simp]
lemma singelton_subset_iff {a : α} {s : set α} : {a} ⊆ s ↔ a ∈ s :=
by simp [subset, set.subset, forall_eq_elim]

end set

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

instance weak_order_filter : weak_order (filter α) :=
{ weak_order .
  le            := λf g, g^.sets ⊆ f^.sets,
  le_antisymm   := take a b h₁ h₂, filter_eq $ subset.antisymm h₂ h₁,
  le_refl       := take a, subset.refl _,
  le_trans      := take a b c h₁ h₂, subset.trans h₂ h₁ }

instance : has_Sup (filter α) := ⟨join ∘ principal⟩

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
  s ∈ (f ⊔ g)^.sets ↔ s ∈ f^.sets ∧ s ∈ g^.sets :=
by refl

@[simp]
lemma mem_inf_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊓ g)^.sets ↔ (∃t₁∈f^.sets, ∃t₂∈g^.sets, t₁ ∩ t₂ ⊆ s) :=
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

lemma bind_mono {β : Type u} {f : filter α} {g h : α → filter β} (h₁ : {a | g a ≤ h a} ∈ f^.sets) :
  f >>= g ≤ f >>= h :=
take x h₂, f^.upwards_sets (inter_mem_sets h₁ h₂) $ take s ⟨gh', h'⟩, gh' h'

lemma bind_sup {β : Type u} {f g : filter α} {h : α → filter β} :
  (f ⊔ g) >>= h = (f >>= h) ⊔ (g >>= h) :=
by simp [bind]

lemma bind_mono2 {β : Type u} {f g : filter α} {h : α → filter β} (h₁ : f ≤ g) :
  f >>= h ≤ g >>= h :=
take s h', h₁ h'

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

/- uniformity -/

class uniform_space (α : Type u) :=
(uniformity              : filter (α × α))
(principal_le_uniformity : principal {p : α × α | p.1 = p.2} ≤ uniformity)
(swap_uniformity_le      : (λx : α × α, (x.2, x.1)) <$> uniformity ≤ uniformity)
(transitive              :
  (do p₁ ← uniformity, p₂ ← uniformity, principal {p | p = (p₁.1, p₂.2) ∧ p₁.2 = p₂.1}) ≤ uniformity)

namespace uniform_space
section
variables [uniform_space α]

lemma uniformity_le_swap : uniformity α ≤ (λx : α × α, (x.2, x.1)) <$> uniformity α :=
calc
  uniformity α = id <$> uniformity α : (monad.id_map _)^.symm
           ... = ((λx : α × α, (x.2, x.1)) ∘ (λx : α × α, (x.2, x.1))) <$> uniformity α :
    congr_arg (λf, f <$> (uniformity α)) (by apply funext; intro x; cases x; refl)
           ... = (map (λx : α × α, (x.2, x.1)) ∘ map (λx : α × α, (x.2, x.1))) (uniformity α) :
    congr map_compose rfl 
           ... ≤ (λx : α × α, (x.2, x.1)) <$> uniformity α : map_mono (swap_uniformity_le α)

lemma uniformity_eq_swap : uniformity α = (λx : α × α, (x.2, x.1)) <$> uniformity α :=
le_antisymm uniformity_le_swap (swap_uniformity_le α)

/- neighbourhood -/
definition nhds (x : α) : filter α := uniformity α >>= λp, principal {y | p = (x, y)}

lemma pure_le_nhds {x : α} : pure x ≤ nhds x :=
calc pure x ≤ (principal {p : α × α | p.1 = p.2} >>= λp, principal {y | p = (x, y)}) : 
     by simp [pure, principal_bind]; exact ⟨(x, x), rfl, rfl⟩
  ... <= nhds x : bind_mono2 (principal_le_uniformity α)

/- cauchy filters -/
definition cauchy (f : filter α) : Prop := prod.mk <$> f <*> f ≤ uniformity α

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
le_trans (seq_mono (map_mono h_le) h_le) h_c

lemma cauchy_sup {f g : filter α} (h_f : cauchy f) (h_f : cauchy g) (h_inf : f ⊓ g ≠ ⊥) :
  cauchy (f ⊔ g) :=
show map (@prod.mk α α) (f ⊔ g) <*> (f ⊔ g) ≤ uniformity α,
begin
  rw [map_sup]
end

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
calc prod.mk <$> nhds a <*> nhds a ≤
    do { p₁ ← (λx : α × α, (x.2, x.1)) <$> uniformity α, p₂ ← uniformity α, 
      principal {p | p = (p₁.2, p₂.2) ∧ p₁.1 = a ∧ p₂.1 = a} } :
  begin -- should be done by auto
    rw [-uniformity_eq_swap],
    simp [nhds, map_bind, bind_assoc, seq_eq_bind_map, principal_bind],
    apply bind_mono,
    apply univ_mem_sets',
    simp [supr_le_iff, image_subset_iff_subset_vimage, bounded_forall_image_iff],
    intros p₁ a₁ h₁,
    apply bind_mono,
    apply univ_mem_sets',
    simp [image_subset_iff_subset_vimage, bounded_forall_image_iff],
    intros p₂ a₂ h₂,
    simp [h₁, h₂]
  end
  ... ≤ (do p₁ ← uniformity α, p₂ ← uniformity α, principal {p | p = (p₁.1, p₂.2) ∧ p₁.2 = p₂.1}) :
  begin -- should be done by auto
    simp [seq_bind_eq],
    apply bind_mono, apply univ_mem_sets', intro p₁,
    apply bind_mono, apply univ_mem_sets', intro p₂,
    simp,
    cc
  end
  ... ≤ uniformity α : transitive _

end

end uniform_space

end filter
