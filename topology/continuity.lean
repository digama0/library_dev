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

section 
variables [topological_space α] [topological_space β] [topological_space γ]

def continuous (f : α → β) := ∀s, open' s → open' (vimage f s)

lemma continuous_id : continuous (id : α → α) :=
take s h, h

lemma continuous_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g):
  continuous (g ∘ f) :=
take s h, hf _ (hg s h)

end

section constructions
local notation `cont` := @continuous _ _
local notation `tspace` := topological_space
open topological_space

variable {f : α → β}

lemma continuous_iff_induced_le {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ (induced f t₂ ≤ t₁) :=
⟨take hc s ⟨t, ht, s_eq⟩, s_eq^.symm ▸ hc t ht, 
  take hle s h, hle _ ⟨_, h, rfl⟩⟩

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

end subtype
