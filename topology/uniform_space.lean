/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of uniform spaces.
-/
import algebra.lattice.filter
open set lattice filter

universes u v
variables {α : Type u} {β : Type u}

def refl_rel {α : Type u} := {p : α × α | p.1 = p.2}

def trans_rel {α : Type u} (r₁ r₂ : set (α×α)) :=
{p : α × α | ∃z:α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂}

@[simp]
lemma vimage_set_of_eq {p : α → Prop} {f : β → α} :
  vimage f {a | p a} = {a | p (f a)} :=
rfl

def prod.swap : (α×β) → (β×α) := λp, (p.2, p.1)

@[simp]
lemma prod.swap_swap : ∀x:α×β, prod.swap (prod.swap x) = x
| ⟨a, b⟩ := rfl

@[simp]
lemma prod.fst_swap {p : α×β} : (prod.swap p).1 = p.2 := rfl

@[simp]
lemma prod.snd_swap {p : α×β} : (prod.swap p).2 = p.1 := rfl

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

lemma monotone_mem_sets {f : filter α} : monotone (λs, s ∈ f^.sets) :=
take s t hst h, f^.upwards_sets h hst

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
  ... = (prod.swap ∘ prod.swap) <$> uniformity :
    congr_arg (λf : (α×α)→(α×α), f <$> uniformity) (by apply funext; intro x; cases x; refl)
  ... = (map prod.swap ∘ map prod.swap) uniformity :
    congr map_compose rfl
  ... ≤ prod.swap <$> uniformity : map_mono symm_le_uniformity

lemma uniformity_eq_symm : uniformity = (@prod.swap α α) <$> uniformity :=
le_antisymm uniformity_le_symm symm_le_uniformity

/- neighbourhood -/
definition nhds (x : α) : filter α := uniformity^.lift' (λs:set (α×α), {y | (x, y) ∈ s})

lemma pure_le_nhds {x : α} : pure x ≤ nhds x :=
have m : monotone (λ (s : set (α × α)), {y : α | (x, y) ∈ s}),
  from take s t h a ha, h ha,
have set_of (eq x) = {x},
  by apply set.ext; simp [eq_comm],
calc pure x = (principal {p : α × α | p^.1 = p^.2})^.lift' (λs:set (α×α), {y | (x, y) ∈ s}) :
    by rw [lift'_principal m]; simp [this, pure]
  ... ≤ nhds x : lift'_mono refl_le_uniformity (le_refl _)

lemma lift_nhds_eq {x : α} {g : set α → filter β} (hg : monotone g) :
  (nhds x)^.lift g = uniformity^.lift (λs:set (α×α), g {y | (x, y) ∈ s}) :=
eq.trans
  (filter.lift_assoc $ monotone_comp monotone_id $ monotone_comp monotone_vimage monotone_principal)
  (congr_arg _ $ funext $ take s, filter.lift_principal hg)

lemma uniformity_lift_le {g : set (α×α) → filter β} {f : filter β} (hg : monotone g)
  (h : uniformity^.lift (λs, g (vimage prod.swap s)) ≤ f) : uniformity^.lift g ≤ f :=
le_trans
  (lift_mono uniformity_le_symm (le_refl _))
  (by rw [map_lift_eq2 hg, image_swap_eq_vimage_swap]; exact h)

/- cauchy filters -/
definition cauchy (f : filter α) : Prop := filter.prod f f ≤ uniformity

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
le_trans (filter.prod_mono h_le h_le) h_c

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
calc (nhds a)^.lift (λs, (nhds a)^.lift (λt, principal (set.prod s t))) ≤
    uniformity^.lift (λs:set (α×α), uniformity^.lift' (trans_rel s)) :
  begin
    rw [lift_nhds_eq],
    apply le_trans (lift_mono uniformity_le_symm (le_refl _)) _,
    rw [map_lift_eq2],
    apply lift_mono (le_refl _),
    intro s,
    dsimp,
    simp [image_swap_eq_vimage_swap],
    rw [lift_nhds_eq],
    apply lift_mono (le_refl _),
    intro t,
    simp,
    exact take ⟨x, y⟩ ⟨h₁, h₂⟩, ⟨a, h₁, h₂⟩,
    exact monotone_comp (monotone_prod monotone_const monotone_id) monotone_principal,
    exact (monotone_lift' monotone_const $ monotone_lam $ take x, monotone_prod monotone_vimage monotone_const),
    exact (monotone_lift' monotone_const $ monotone_lam $ take x, monotone_prod monotone_id monotone_const)
  end
  ... ≤ uniformity : trans_le_uniformity

def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f ∧ f ≠ bot }

def Cauchy.uniformity (α : Type u) [uniform_space α] : filter (Cauchy α × Cauchy α) :=
uniformity^.lift' $ λs, {p : Cauchy α × Cauchy α | s ∈ (filter.prod (p.1^.val) (p.2^.val))^.sets }

def completion_space : uniform_space (Cauchy α) :=
{ uniformity := Cauchy.uniformity α,
  refl       := principal_le_lift' $ take s hs ⟨a, b⟩ (a_eq_b : a = b),
    a_eq_b ▸ a^.property^.left hs,
  symm       :=
    calc map prod.swap (Cauchy.uniformity α) =
          uniformity^.lift' (λs:set (α×α), {p | s ∈ (filter.prod (p.2^.val) (p.1^.val))^.sets }) :
        by simp [Cauchy.uniformity, map_lift'_eq, monotone_set_of, monotone_mem_sets,
                 function.comp, image_swap_eq_vimage_swap]
      ... ≤ Cauchy.uniformity α : _,
  trans      := _ }

end uniform_space
