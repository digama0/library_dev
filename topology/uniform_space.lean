/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of uniform spaces.
-/
import algebra.lattice.filter
open set lattice filter

universes u v

section
variables {α : Type u} {β : Type v}

def refl_rel {α : Type u} := {p : α × α | p.1 = p.2}

def trans_rel {α : Type u} (r₁ r₂ : set (α×α)) :=
{p : α × α | ∃z:α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂}

lemma monotone_trans_rel [weak_order β] {f g : β → set (α×α)}
  (hf : monotone f) (hg : monotone g) : monotone (λx, trans_rel (f x) (g x)) :=
take a b h p ⟨z, h₁, h₂⟩, ⟨z, hf h h₁ , hg h h₂⟩

lemma empty_in_sets_eq_bot {f : filter α} : ∅ ∈ f^.sets ↔ f = ⊥ :=
⟨take h, bot_unique $ take s _, f.upwards_sets h (empty_subset s),
  suppose f = ⊥, this.symm ▸ mem_bot_sets⟩

lemma inhabited_of_mem_sets {f : filter α} {s : set α} (hf : f ≠ ⊥) (hs : s ∈ f^.sets) :
  ∃x, x ∈ s :=
have ∅ ∉ f^.sets, from take h, hf $ empty_in_sets_eq_bot.mp h,
have s ≠ ∅, from take h, this (h ▸ hs),
exists_mem_of_ne_empty this

@[simp]
lemma vimage_set_of_eq {p : α → Prop} {f : β → α} :
  vimage f {a | p a} = {a | p (f a)} :=
rfl

@[simp] -- copied from parser
lemma prod.mk.eta : ∀{p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

def prod.swap : (α×β) → (β×α) := λp, (p.2, p.1)

@[simp]
lemma prod.swap_swap : ∀x:α×β, prod.swap (prod.swap x) = x
| ⟨a, b⟩ := rfl

@[simp]
lemma prod.fst_swap {p : α×β} : (prod.swap p).1 = p.2 := rfl

@[simp]
lemma prod.snd_swap {p : α×β} : (prod.swap p).2 = p.1 := rfl

@[simp]
lemma prod.swap_prod_mk {a : α} {b : β} : prod.swap (a, b) = (b, a) := rfl

@[simp]
lemma set_of_mem_eq {s : set α} : {x | x ∈ s} = s :=
rfl

lemma mem_image_iff_of_inverse (f : α → β) (g : β → α) {b : β} {s : set α} 
  (h₁ : ∀a, g (f a) = a ) (h₂ : ∀b, f (g b) = b ) : b ∈ f ' s ↔ g b ∈ s :=
⟨take ⟨a, ha, fa_eq⟩, fa_eq ▸ (h₁ a)^.symm ▸ ha,
  take h, ⟨g b, h, h₂ b⟩⟩

lemma image_eq_vimage_of_inverse (f : α → β) (g : β → α)
  (h₁ : ∀a, g (f a) = a ) (h₂ : ∀b, f (g b) = b ) : image f = vimage g :=
funext $ take s, set.ext $ take b, mem_image_iff_of_inverse f g h₁ h₂

lemma image_swap_eq_vimage_swap : image (@prod.swap α β) = vimage prod.swap :=
image_eq_vimage_of_inverse (@prod.swap α β) (@prod.swap β α)
  begin simp; intros; trivial end
  begin simp; intros; trivial end

lemma monotone_set_of [weak_order α] {p : α → β → Prop} 
  (hp : ∀b, monotone (λa, p a b)) : monotone (λa, {b | p a b}) :=
take a a' h b, hp b h

@[simp] -- should be handled by implies_true_iff
lemma implies_implies_true_iff {α : Sort u} {β : Sort v} : (α → β → true) ↔ true :=
⟨take _, trivial, take _ _ _ , trivial⟩

/- uniformity -/

class uniform_space (α : Type u) :=
(uniformity : filter (α × α))
(refl       : principal refl_rel ≤ uniformity)
(symm       : prod.swap <$> uniformity ≤ uniformity)
(trans      : uniformity^.lift (λs, uniformity^.lift' (trans_rel s)) ≤ uniformity)

section uniform_space
variables [uniform_space α]

def uniformity : filter (α × α) := uniform_space.uniformity α

lemma refl_le_uniformity : principal {p : α × α | p^.1 = p^.2} ≤ uniformity :=
uniform_space.refl α

lemma symm_le_uniformity : map (@prod.swap α α) uniformity ≤ uniformity :=
uniform_space.symm α

lemma trans_le_uniformity :
  uniformity^.lift (λs:set (α×α), uniformity^.lift' (trans_rel s)) ≤ uniformity :=
uniform_space.trans α

lemma uniformity_le_symm : uniformity ≤ map (@prod.swap α α) uniformity :=
calc uniformity = id <$> uniformity : (monad.id_map _)^.symm
  ... = (prod.swap.{u u} ∘ prod.swap) <$> uniformity :
    congr_arg (λf : (α×α)→(α×α), f <$> uniformity) (by apply funext; intro x; cases x; refl)
  ... = (map prod.swap ∘ map prod.swap) uniformity :
    congr map_compose rfl
  ... ≤ prod.swap.{u u} <$> uniformity : map_mono symm_le_uniformity

lemma uniformity_eq_symm : uniformity = (@prod.swap α α) <$> uniformity :=
le_antisymm uniformity_le_symm symm_le_uniformity

/- neighbourhood -/
definition nhds (x : α) : filter α := uniformity^.lift' (λs:set (α×α), {y | (x, y) ∈ s})

lemma mem_nhds_left {x : α} {s : set (α×α)} (h : s ∈ (uniformity.sets : set (set (α×α)))) :
  {y : α | (x, y) ∈ s} ∈ (nhds x)^.sets :=
have nhds x ≤ principal {y : α | (x, y) ∈ s},
  from infi_le_of_le s (infi_le _ h),
by simp at this; assumption

lemma mem_nhds_right {y : α} {s : set (α×α)} (h : s ∈ (uniformity.sets : set (set (α×α)))) :
  {x : α | (x, y) ∈ s} ∈ (nhds y)^.sets :=
mem_nhds_left (symm_le_uniformity h)

lemma pure_le_nhds {x : α} : pure x ≤ nhds x :=
le_infi $ take s, le_infi $ take hs,
  have {p : α × α | p^.1 = p^.2} ⊆ s,
    from refl_le_uniformity hs,
  principal_mono.mpr $ take x',
  begin
    simp,
    intro h,
    subst h,
    exact @this (x', x') rfl
  end

lemma nhds_neq_bot {x : α} : nhds x ≠ ⊥ :=
take h,
have {x} = (∅:set α),
  from principal_eq_iff_eq.mp $ bot_unique $ h ▸ pure_le_nhds,
have x ∉ ({x} : set α),
  from this.symm ▸ not_mem_empty _,
this $ mem_singleton _

lemma lift_nhds_eq {x : α} {g : set α → filter β} (hg : monotone g) :
  (nhds x)^.lift g = uniformity^.lift (λs:set (α×α), g {y | (x, y) ∈ s}) :=
eq.trans
  (filter.lift_assoc $ monotone_comp monotone_id $ monotone_comp monotone_vimage monotone_principal)
  (congr_arg _ $ funext $ take s, filter.lift_principal hg)

lemma uniformity_lift_le_swap {g : set (α×α) → filter β} {f : filter β} (hg : monotone g)
  (h : uniformity^.lift (λs, g (vimage prod.swap s)) ≤ f) : uniformity^.lift g ≤ f :=
le_trans
  (lift_mono uniformity_le_symm (le_refl _))
  (by rw [map_lift_eq2 hg, image_swap_eq_vimage_swap]; exact h)

lemma uniformity_lift_le_trans {f : set (α×α) → filter β} (h : monotone f):
  uniformity.lift (λs, uniformity.lift (λt, f (trans_rel s t))) ≤ uniformity.lift f :=
calc uniformity.lift (λs, uniformity.lift (λt, f (trans_rel s t))) =
    (uniformity.lift (λs:set (α×α), uniformity.lift' (λt:set (α×α), trans_rel s t)))^.lift f :
  begin
    rw [lift_assoc],
    apply congr_arg, apply funext, intro s,
    rw [lift_lift'_assoc],
    exact monotone_trans_rel monotone_const monotone_id,
    exact h,
    exact (monotone_lift' monotone_const $ monotone_lam $
      take t, monotone_trans_rel monotone_id monotone_const)
  end
  ... ≤ uniformity.lift f : lift_mono trans_le_uniformity (le_refl _)

/- uniform continuity -/

definition uniform [uniform_space α] [uniform_space β] (f : α → β) :=
filter.map (λx:α×α, (f x.1, f x.2)) uniformity ≤ uniformity

/- cauchy filters -/
definition cauchy (f : filter α) : Prop := filter.prod f f ≤ uniformity

definition complete : Prop :=
∀f:filter α, cauchy f → ∃x, f ≤ nhds x

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
le_trans (filter.prod_mono h_le h_le) h_c

lemma nhds_nhds_le_uniformity_prod {a b : α} : filter.prod (nhds a) (nhds b) ≤
  uniformity^.lift (λs:set (α×α), uniformity^.lift' (λt:set(α×α),
    set.prod {y : α | (y, a) ∈ s} {y : α | (b, y) ∈ t})) :=
begin
  delta nhds,
  rw [prod_lift'_lift'],
  apply uniformity_lift_le_swap _,
  apply lift_mono (le_refl uniformity), intro s,
  apply lift'_mono (le_refl uniformity), intro t,
  exact le_refl _,
  exact (monotone_lift' monotone_const $ monotone_lam $
    take t, monotone_prod monotone_vimage monotone_const),
  exact monotone_vimage,
  exact monotone_vimage
end

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
calc filter.prod (nhds a) (nhds a) ≤
  uniformity^.lift (λs:set (α×α), uniformity^.lift' (λt:set(α×α),
    set.prod {y : α | (y, a) ∈ s} {y : α | (a, y) ∈ t})) : nhds_nhds_le_uniformity_prod
  ... ≤ uniformity^.lift (λs:set (α×α), uniformity^.lift' (trans_rel s)) :
    lift_mono' $ take s hs, lift'_mono' $ take t ht, take ⟨b, c⟩ ⟨ha, hb⟩, ⟨a, ha, hb⟩
  ... ≤ uniformity : trans_le_uniformity

def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f ∧ f ≠ bot }


end uniform_space
end

namespace uniform_space.Cauchy

section
parameters {α : Type u} [uniform_space α]

def gen (s : set (α × α)) : set (Cauchy α × Cauchy α) :=
{p | s ∈ (filter.prod (p.1^.val) (p.2^.val))^.sets }

lemma monotone_gen : monotone gen :=
monotone_set_of $ take p, @monotone_mem_sets (α×α) (filter.prod (p.1^.val) (p.2^.val))

private lemma symm_gen : map prod.swap (uniformity^.lift' gen) ≤ uniformity^.lift' gen :=
calc map prod.swap (uniformity^.lift' gen) =
  uniformity^.lift' (λs:set (α×α), {p | s ∈ (filter.prod (p.2^.val) (p.1^.val))^.sets }) :
  begin
    delta gen,
    simp [map_lift'_eq, monotone_set_of, monotone_mem_sets,
          function.comp, image_swap_eq_vimage_swap]
  end
  ... ≤ uniformity^.lift' gen :
    uniformity_lift_le_swap
      (monotone_comp (monotone_set_of $ take p,
        @monotone_mem_sets (α×α) ((filter.prod ((p.2).val) ((p.1).val)))) monotone_principal)
      begin
        note h := λ(p:Cauchy α×Cauchy α), @filter.prod_comm _ _ (p.2.val) (p.1.val),
        simp [function.comp, h],
        exact le_refl _
      end

private lemma trans_rel_gen_gen_subset_gen_trans_rel {s t : set (α×α)} : trans_rel (gen s) (gen t) ⊆
  (gen (trans_rel s t) : set (Cauchy α × Cauchy α)) :=
take ⟨f, g⟩ ⟨h, h₁, h₂⟩,
let ⟨t₁, (ht₁ : t₁ ∈ f.val.sets), t₂, (ht₂ : t₂ ∈ h.val.sets), (h₁ : set.prod t₁ t₂ ⊆ s)⟩ :=
  mem_prod_iff^.mp h₁ in
let ⟨t₃, (ht₃ : t₃ ∈ h.val.sets), t₄, (ht₄ : t₄ ∈ g.val.sets), (h₂ : set.prod t₃ t₄ ⊆ t)⟩ :=
  mem_prod_iff^.mp h₂ in
have t₂ ∩ t₃ ∈ h.val.sets,
  from inter_mem_sets ht₂ ht₃,
let ⟨x, xt₂, xt₃⟩ :=
  inhabited_of_mem_sets (h.property.right) this in
(filter.prod f^.val g^.val).upwards_sets
  (prod_mem_prod ht₁ ht₄)
  (take ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩,
    ⟨x,
      h₁ (show (a, x) ∈ set.prod t₁ t₂, from ⟨ha, xt₂⟩),
      h₂ (show (x, b) ∈ set.prod t₃ t₄, from ⟨xt₃, hb⟩)⟩)

private lemma trans_gen :
    (uniformity^.lift' gen)^.lift (λs, (uniformity^.lift' gen)^.lift' (trans_rel s)) ≤
    uniformity^.lift' gen :=
calc (uniformity^.lift' gen)^.lift (λs, (uniformity^.lift' gen)^.lift' (trans_rel s)) =
    uniformity^.lift (λs, uniformity^.lift' (λt, trans_rel (gen s) (gen t))) :
  begin
    rw [lift_lift'_assoc],
    apply congr_arg, apply funext, intro x,
    rw [lift'_lift'_assoc],
    exact monotone_gen,
    exact (monotone_trans_rel monotone_const monotone_id),
    exact monotone_gen,
    exact monotone_lift' monotone_const
      (monotone_lam $ take t, monotone_trans_rel monotone_id monotone_const),
  end
  ... ≤ uniformity^.lift (λs, uniformity^.lift' $ λt, gen $ trans_rel s t) :
    lift_mono' $ take s hs, lift'_mono' $ take t ht, trans_rel_gen_gen_subset_gen_trans_rel
  ... = (uniformity^.lift $ λs:set(α×α), uniformity^.lift' $ trans_rel s)^.lift' gen : 
  begin
    rw [lift'_lift_assoc],
    apply congr_arg, apply funext, intro x,
    rw [lift'_lift'_assoc],
    exact (monotone_trans_rel monotone_const monotone_id),
    exact monotone_gen,
    exact monotone_lift' monotone_const
      (monotone_lam $ take t, monotone_trans_rel monotone_id monotone_const)
  end
  ... ≤ uniformity^.lift' gen : lift'_mono trans_le_uniformity (le_refl _)

def completion_space : uniform_space (Cauchy α) :=
{ uniformity := uniformity^.lift' gen,
  refl       := principal_le_lift' $ take s hs ⟨a, b⟩ (a_eq_b : a = b),
    a_eq_b ▸ a^.property^.left hs,
  symm       := symm_gen,
  trans      := trans_gen }

local attribute [instance] completion_space

def nhds_cauchy (a : α) : Cauchy α :=
⟨nhds a, cauchy_nhds, nhds_neq_bot⟩

lemma uniform_nhds_cauchy : uniform (nhds_cauchy : α → Cauchy α) :=
calc map (λx:α×α, (nhds_cauchy x.1, nhds_cauchy x.2)) uniformity ≤
  (uniformity^.lift $ λs₁, uniformity^.lift $ λs₂, uniformity^.lift' $ λs₃,
    gen (trans_rel s₁ (trans_rel s₂ s₃))) :
    le_infi $ take s₁, le_infi $ take hs₁, le_infi $ take s₂, le_infi $ take hs₂, le_infi $ take s₃, le_infi $ take hs₃,
    begin
      simp [gen, nhds_cauchy],
      apply uniformity.upwards_sets hs₂,
      intros p hp, cases p with a b,
      apply (filter.prod (nhds a) (nhds b)).upwards_sets,
      show set.prod {x:α | (x, a) ∈ s₁} {y:α | (b, y) ∈ s₃} ∈ (filter.prod (nhds a) (nhds b)).sets,
        from @prod_mem_prod α α {x:α | (x, a) ∈ s₁} {y:α | (b, y) ∈ s₃} (nhds a) (nhds b)
          (mem_nhds_right hs₁)
          (mem_nhds_left hs₃),
      show set.prod {x:α | (x, a) ∈ s₁} {y:α | (b, y) ∈ s₃} ⊆ trans_rel s₁ (trans_rel s₂ s₃),
        from take ⟨x, y⟩ ⟨hx, hy⟩, ⟨a, hx, b, hp, hy⟩
    end
  ... ≤ (uniformity^.lift $ λs:set(α×α), uniformity^.lift' $ λt, gen (trans_rel s t)) :
    lift_mono (le_refl _) $ take s,
      @uniformity_lift_le_trans α (Cauchy α × Cauchy α) _ (principal ∘ (λ (t : set (α × α)), gen (trans_rel s t)))
        (monotone_comp (monotone_comp (monotone_trans_rel monotone_const monotone_id) monotone_gen) monotone_principal)
  ... ≤ uniformity :
    @uniformity_lift_le_trans  α (Cauchy α × Cauchy α) _ (principal ∘ gen)
      (monotone_comp monotone_gen monotone_principal)

lemma complete_completion_space : @complete (Cauchy α) completion_space :=
take f hf,
_

end

end uniform_space.Cauchy
