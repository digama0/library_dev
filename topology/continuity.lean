/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Continuous functions.
-/
import .topological_space
open set filter lattice

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

theorem classical.cases {p : Prop → Prop} (h1 : p true) (h2 : p false) : ∀a, p a :=
take a, classical.cases_on a h1 h2

lemma univ_eq_true_false : univ = ({true, false} : set Prop) :=
eq.symm $ top_unique $ classical.cases (by simp) (by simp)

@[simp]
lemma false_neq_true : false ≠ true :=
begin intro h, rw [h], trivial end

lemma subtype.val_image {p : α → Prop} {s : set (subtype p)} :
  subtype.val ' s = {x | ∃h : p x, (⟨x, h⟩ : subtype p) ∈ s} :=
set.ext $ take a,
⟨ take ⟨⟨a', ha'⟩, in_s, (h_eq : a' = a)⟩, h_eq ▸ ⟨ha', in_s⟩,
  take ⟨ha, in_s⟩, ⟨⟨a, ha⟩, in_s, rfl⟩⟩

section 
variables [topological_space α] [topological_space β] [topological_space γ]

def continuous (f : α → β) := ∀s, open' s → open' (vimage f s)

lemma continuous_id : continuous (id : α → α) :=
take s h, h

lemma continuous_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g):
  continuous (g ∘ f) :=
take s h, hf _ (hg s h)

lemma continuous_iff_towards {f : α → β} :
  continuous f ↔ (∀x, towards f (nhds x) (nhds (f x))) :=
⟨ assume hf : continuous f, take x s, 
  show s ∈ (nhds (f x))^.sets → s ∈ (map f (nhds x))^.sets,
    by simp [nhds_sets];
      exact take ⟨t, t_open, t_subset, fx_in_t⟩,
        ⟨vimage f t, hf t t_open, fx_in_t, vimage_mono t_subset⟩
, assume hf : ∀x, towards f (nhds x) (nhds (f x)), 
  take s, assume hs : open' s,
  have ∀a, f a ∈ s → s ∈ (nhds (f a))^.sets,
    by simp [nhds_sets]; exact take a ha, ⟨s, hs, subset.refl s, ha⟩,
  show open' (vimage f s),
    by simp [open_iff_nhds]; exact take a ha, hf a (this a ha)⟩

end

section constructions
local notation `cont` := @continuous _ _
local notation `tspace` := topological_space
open topological_space

variable {f : α → β}

lemma continuous_iff_induced_le {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ (induced f t₂ ≤ t₁) :=
⟨ take hc s ⟨t, ht, s_eq⟩, s_eq^.symm ▸ hc t ht
, take hle s h, hle _ ⟨_, h, rfl⟩⟩

lemma continuous_eq_le_coinduced {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f = (t₂ ≤ coinduced f t₁) :=
rfl

lemma continuous_induced_dom {t : tspace β} : cont (induced f t) t f :=
take s h, ⟨_, h, rfl⟩

lemma continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ}
  (h : cont t₁ t₂ (f ∘ g)) : cont t₁ (induced f t₂) g :=
take s ⟨t, ht, s_eq⟩, s_eq^.symm ▸ h t ht

lemma continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f :=
take s h, h

lemma continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ}
  (h : cont t₁ t₂ (g ∘ f)) : cont (coinduced f t₁) t₂ g :=
take s hs, h s hs

lemma continuous_inf_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : cont t₁ t₃ f) (h₂ : cont t₂ t₃ f) : cont (t₁ ⊓ t₂) t₃ f :=
take s h, ⟨h₁ s h, h₂ s h⟩

lemma continuous_inf_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β}
  (h : cont t₁ t₂ f) : cont t₁ (t₂ ⊓ t₃) f :=
take s hs, h s hs^.left

lemma continuous_inf_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β}
  (h : cont t₁ t₃ f) : cont t₁ (t₂ ⊓ t₃) f :=
take s hs, h s hs^.right

lemma continuous_Inf_dom {t₁ : set (tspace α)} {t₂ : tspace β}
  (h : ∀t∈t₁, cont t t₂ f) : cont (Inf t₁) t₂ f :=
take s hs t ht, h t ht s hs

lemma continuous_Inf_rng {t₁ : tspace α} {t₂ : set (tspace β)}
  {t : tspace β} (h₁ : t ∈ t₂) (hf : cont t₁ t f) : cont t₁ (Inf t₂) f :=
take s hs, hf s $ hs t h₁

lemma continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β}
  (h : ∀i, cont (t₁ i) t₂ f) : cont (infi t₁) t₂ f :=
continuous_Inf_dom $ take t ⟨i, (t_eq : t = t₁ i)⟩, t_eq^.symm ▸ h i

lemma continuous_infi_rng {t₁ : tspace α} {t₂ : ι → tspace β}
  {i : ι} (h : cont t₁ (t₂ i) f) : cont t₁ (infi t₂) f :=
continuous_Inf_rng ⟨i, rfl⟩ h

lemma continuous_top {t : tspace β} : cont ⊤ t f :=
take s h, trivial

lemma continuous_bot {t : tspace α} : cont t ⊥ f :=
continuous_Inf_rng (mem_univ $ coinduced f t) continuous_coinduced_rng

lemma continuous_sup_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : cont t₁ t₂ f) (h₂ : cont t₁ t₃ f) : cont t₁ (t₂ ⊔ t₃) f :=
continuous_Inf_rng
  (show t₂ ≤ coinduced f t₁ ∧ t₃ ≤ coinduced f t₁, from ⟨h₁, h₂⟩)
  continuous_coinduced_rng

lemma continuous_sup_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h : cont t₁ t₃ f) : cont (t₁ ⊔ t₂) t₃ f :=
continuous_Inf_dom $ take t ⟨h₁, h₂⟩ s hs, h₁ _ $ h s hs

lemma continuous_sup_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h : cont t₂ t₃ f) : cont (t₁ ⊔ t₂) t₃ f :=
continuous_Inf_dom $ take t ⟨h₁, h₂⟩ s hs, h₂ _ $ h s hs

end constructions

section induced
open topological_space

variables [t : topological_space β] {a : α} {f : α → β}

lemma map_nhds_induced_eq (h : image f univ ∈ (nhds (f a))^.sets) :
  map f (@nhds α (induced f t) a) = nhds (f a) :=
le_antisymm
  ((@continuous_iff_towards α β (induced f t) _ _)^.mp continuous_induced_dom a)
  ( take s, assume hs : vimage f s ∈ (@nhds α (induced f t) a)^.sets,
    let ⟨t', t_subset, open_t, a_in_t⟩ := mem_nhds_sets_iff^.mp h in
    let ⟨s', s'_subset, ⟨s'', open_s'', s'_eq⟩, a_in_s'⟩ := (@mem_nhds_sets_iff _ (induced f t) _ _)^.mp hs in
    by subst s'_eq; exact (mem_nhds_sets_iff^.mpr $
      ⟨ t' ∩ s''
      , take x ⟨h₁, h₂⟩, match x, h₂, t_subset h₁ with
        | x, h₂, ⟨y, _, y_eq⟩ := begin subst y_eq, exact s'_subset h₂ end
        end
      , open_inter open_t open_s''
      , ⟨a_in_t, a_in_s'⟩⟩))

end induced

section sierpinski
variables [topological_space α]

@[simp]
lemma open_singleton_true : open' ({true} : set Prop) :=
take h, show true ∈ {true}, by simp

lemma continuous_Prop {p : α → Prop} : continuous p ↔ open' {x | p x} :=
⟨ assume h : continuous p,
  have open' (vimage p {true}),
    from h _ open_singleton_true,
  by simp [vimage, eq_true] at this; assumption
, assume h : open' {x | p x}, take s, assume hs : open' s,
  classical.by_cases
  ( suppose false ∈ s,
    have s = univ,
      from top_unique $ classical.cases (take _, hs this) (take _, this),
    by simp [this])
  ( assume nf : false ∉ s,
    classical.by_cases
    ( suppose true ∈ s,
      have s = {true},
        from set.ext $ classical.cases (by simp [this]) (by simp [nf]),
      by simp [this, vimage, eq_true, h])
    ( suppose true ∉ s, 
      have s = {},
        from set.ext $ classical.cases (by simp [this]) (by simp [nf]),
      by simp [this]) ) ⟩

end sierpinski

section prod
variables [topological_space α] [topological_space β] [topological_space γ]

lemma continuous_fst : continuous (@prod.fst α β) :=
continuous_sup_dom_left continuous_induced_dom

lemma continuous_snd : continuous (@prod.snd α β) :=
continuous_sup_dom_right continuous_induced_dom

lemma continuous_prod_mk {f : γ → α} {g : γ → β} 
  (hf : continuous f) (hg : continuous g) : continuous (λx, prod.mk (f x) (g x)) :=
continuous_sup_rng (continuous_induced_rng hf) (continuous_induced_rng hg)

end prod

section sum
variables [topological_space α] [topological_space β] [topological_space γ]

lemma continuous_inl : continuous (@sum.inl α β) :=
continuous_inf_rng_left continuous_coinduced_rng

lemma continuous_inr : continuous (@sum.inr α β) :=
continuous_inf_rng_right continuous_coinduced_rng

lemma continuous_sum_rec {f : α → γ} {g : β → γ}
  (hf : continuous f) (hg : continuous g) : @continuous (α ⊕ β) γ _ _ (@sum.rec α β (λ_, γ) f g) :=
continuous_inf_dom hf hg

end sum

section subtype
variables [topological_space α] [topological_space β] {p : α → Prop}

lemma continuous_subtype_val : continuous (@subtype.val α p) :=
continuous_induced_dom

lemma continuous_subtype_mk {f : β → α}
  (hp : ∀x, p (f x)) (h : continuous f) : continuous (λx, (⟨f x, hp x⟩ : subtype p)) :=
continuous_induced_rng h

lemma map_nhds_subtype_val_eq {a : α} {ha : p a} (h : {a | p a} ∈ (nhds a)^.sets) :
  map (@subtype.val α p) (nhds ⟨a, ha⟩) = nhds a :=
map_nhds_induced_eq (by simp [subtype.val_image, h])

lemma continuous_subtype_nhds_cover {f : α → β} {c : ι → α → Prop}
  (c_cover : ∀x, ∃i, c i x ∧ {x | c i x} ∈ (nhds x)^.sets)
  (f_cont  : ∀i, continuous (λ(x : subtype (c i)), f x.val)) :
  continuous f :=
continuous_iff_towards^.mpr $ take x, 
  let ⟨i, (hi : c i x), (c_sets : {x | c i x} ∈ (nhds x)^.sets)⟩ := c_cover x in
  calc map f (nhds x) = map f (map (@subtype.val α (c i)) (nhds ⟨x, hi⟩)) :
      congr_arg (map f) (map_nhds_subtype_val_eq $ c_sets)^.symm
    ... = map (λ(x : subtype (c i)), f x.val) (nhds ⟨x, hi⟩) : rfl
    ... ≤ (nhds (f x)) : continuous_iff_towards^.mp (f_cont i) ⟨x, hi⟩

end subtype


