import .open_subspace
import .lifts
import tactic
import algebraic_topology.fundamental_groupoid.basic
import category_theory.limits.shapes.comm_sq
import topology.unit_interval


noncomputable theory


universe u

variables {X : Type u} [topological_space X]
variables {X₁ : top_subspace X} {X₂ : top_subspace X}
variables {G : category_theory.Groupoid.{u u}}

def p₁ : proj_grpd X₁ (πₓ (Top.of X₁)) := self_grpd X₁
#print p₁
def p₂ : proj_grpd X₂ (πₓ (Top.of X₂)) := self_grpd X₂

#check πₓ (Top.of X₁)

-- def w (v₁ : (πₓ ↑X₁) ⟶ G) (v₂ : (πₓ ↑X₂) ⟶ G): proj_grpd (X₁ ∩ X₂) G := { 
--   obj := 
--   begin
--     let i : (X₁ ∩ X₂) → X₁ := @open_incl X _ (X₁∩X₂) X₁ inter_sub,
--     refine _ ∘ i,
--     exact v₁.obj,
--   end,
--   path := 
--   begin
    
--   end 
--   }

#check ![1,2]

def set.union_lift {α β} {s t : set α} 
  (f : s → β) (g : t → β) : s ∪ t → β :=
begin
  classical,
  exact λ x, x.prop.by_cases (λ hx, f ⟨_, hx⟩) (λ hx, g ⟨_, hx⟩) 
end
-- def set.union_lift {α β} {s t : set α} [decidable_pred (∈ s)] [decidable_pred (∈ t)]
--   (f : s → β) (g : t → β) : s ∪ t → β :=
-- begin
--   intro x, apply or.by_cases x.prop,
-- end

-- def setfunc_to_func {H : top_subspace X} {K : Type} (f : (H.carrier) → K) : H → K :=
-- begin
--   exact f,
-- end
#check category_theory.comm_sq

variables {f : X₁ → G} {g : X₂ → G} 

def coincide {K : Type*} (f : X₁ → K) (g : X₂ → K):= ∀(y : X) (h1 : y ∈ X₁) (h2 : y ∈ X₂), f (b_incl y h1) = g (b_incl y h2)
#print coincide

lemma union_def_eq {x : X₁ ∪ X₂} (h : incl x ∈ X₁): (set.union_lift f g) x = f (b_incl (incl x) h) :=
begin
  rw set.union_lift, unfold_coes, have p : x.val ∈ X₁.carrier, cases x, exact h,
  rw or.by_cases, split_ifs, rotate, contradiction, rw b_incl, simp_rw incl, cases x, simp, refl,
end

lemma union_def_eq₂ {x : X₁ ∪ X₂} (h : incl x ∈ X₂) (pp : @coincide X _ X₁ X₂ G f g): 
(set.union_lift f g) x = g (b_incl (incl x) h) :=
begin
  rw set.union_lift, unfold_coes, have p : x.val ∈ X₂.carrier, cases x, exact h,
  rw or.by_cases, split_ifs, 
  {
    rw b_incl, simp_rw incl,have p2 : x.val ∈ (X₁∩X₂).carrier, split,assumption, assumption,
    cases x, simp, 
    have s : ∀y:X, y ∈ X₁ → y ∈ X₂ →  f (b_incl y _)= g (b_incl y _), rotate 3,assumption, rotate 2, assumption,
    rw coincide at pp, exact pp, simp_rw b_incl at s,apply s, assumption, assumption,
  },rw b_incl, simp_rw incl, cases x, simp, refl,
end

-- Todo : commutative diagram --

notation `πₓ` := fundamental_groupoid.fundamental_groupoid_functor.obj
notation `π` := fundamental_groupoid.fundamental_groupoid_functor
notation `πₘ` := fundamental_groupoid.fundamental_groupoid_functor.map

theorem comm_px : 
(@open_incl X _ X₁ (X₁∪X₂) union_sub) ∘ (@open_incl X _ (X₁∩X₂) X₁ inter_sub) = 
(@open_incl X _ X₂ (X₁∪X₂) union_sub2) ∘ (@open_incl X _ (X₁∩X₂) X₂ inter_sub2) :=
begin
  ext1,simp_rw open_incl, rw function.comp, simp, cases x, simp,
end

theorem comm_πₓ : category_theory.comm_sq 
 (grpd_induced_incl (@inter_sub X _ X₁ X₂))  
 (grpd_induced_incl (@inter_sub2 X _ X₁ X₂)) 
 (grpd_induced_incl (@union_sub X _ X₁ X₂))
 (grpd_induced_incl (@union_sub2 X _ X₁ X₂)) :=
begin
  apply category_theory.functor.map_comm_sq,
  fconstructor, simp_rw top_subspace_incl, simp_rw open_incl, ext, simp only [Top.comp_app, continuous_map.coe_mk],
  unfold_coes, cases a, simp only [eq_self_iff_true],
end

def w₁ (v₁ : (πₓ ↑X₁) ⟶ G) (v₂ : (πₓ ↑X₂) ⟶ G) (a b: ↥(X₁ ∪ X₂))
(pab: path a b ) (h : ↑(set.range pab) ⊆ X₁.carrier ):
 set.union_lift v₁.obj v₂.obj a ⟶ set.union_lift v₁.obj v₂.obj b:=
begin
    rw path_incl_range_eq at h,
    let pXab := subspace_path_lift pab,
    let b₁ := path_lift_def pXab h,
    let s := v₁.map (p₁.path b₁), 
    have aX1 : incl a ∈ X₁ := range_in_init pXab h,
    have bX2 : incl b ∈ X₁ := range_in_end pXab h,
    rw union_def_eq aX1, rw union_def_eq bX2, assumption,
end

def w₂ (v₁ : (πₓ ↑X₁) ⟶ G) (v₂ : (πₓ ↑X₂) ⟶ G) (a b: ↥(X₁ ∪ X₂))
(pab: path a b ) (h : ↑(set.range pab) ⊆ X₂.carrier )
(comm_v : category_theory.comm_sq (grpd_induced_incl (@inter_sub X _ X₁ X₂))  (grpd_induced_incl (@inter_sub2 X _ X₁ X₂)) v₁ v₂)
: set.union_lift v₁.obj v₂.obj a ⟶ set.union_lift v₁.obj v₂.obj b:=
begin
    rw path_incl_range_eq at h,
    let pXab := subspace_path_lift pab,
    let b₂ := path_lift_def pXab h,
    let s := v₂.map (p₂.path b₂), 
    have aX1 : incl a ∈ X₂ := range_in_init pXab h,
    have bX2 : incl b ∈ X₂ := range_in_end pXab h,
    have ph : coincide v₁.obj v₂.obj,
    {
      rw coincide, intros y hy1 hy2, cases comm_v,
      have hy12 : y ∈ X₁∩X₂ := ⟨hy1,hy2⟩,
      have p1 : b_incl y hy1 = (grpd_induced_incl (@inter_sub X _ X₁ X₂)).obj (b_incl y hy12),
      {
        rw grpd_induced_incl, tauto,
      },
      have p2 : b_incl y hy2 = (grpd_induced_incl (@inter_sub2 X _ X₁ X₂)).obj (b_incl y hy12),
      {
        rw grpd_induced_incl, finish,
      },
      rw p1, rw p2, simp_rw ←category_theory.functor.comp_obj, 
      have k: grpd_induced_incl inter_sub ⋙ v₁ = grpd_induced_incl inter_sub2 ⋙ v₂:= by assumption,
      rw k,
    },
    rw union_def_eq₂ aX1 ph, rw union_def_eq₂ bX2 ph, assumption,
end

notation `I` := unit_interval

lemma uniformity_metric_space {X: Type} [metric_space X] (V : set (X × X)): V ∈ uniformity X ↔ ∃ ε > 0, { p : X × X | dist p.1 p.2 < ε } ⊆ V :=
begin
  rw ← filter.has_basis.mem_iff,
  apply metric.uniformity_basis_dist,
end

def w (v₁ : (πₓ ↑X₁) ⟶ G) (v₂ : (πₓ ↑X₂) ⟶ G)
(comm_v : category_theory.comm_sq (grpd_induced_incl (@inter_sub X _ X₁ X₂)) (grpd_induced_incl (@inter_sub2 X _ X₁ X₂)) v₁ v₂)
: proj_grpd (X₁ ∪ X₂) G := 
{
  obj := set.union_lift v₁.obj v₂.obj,
  path := begin
  {
    intros a b pab, 
    set S₁ := {x : I | ↑(pab.to_fun x) ∈ X₁.carrier} with hs1,
    set S₂ := {x : I | ↑(pab.to_fun x) ∈ X₂.carrier} with hs2,
    have pcover : set.univ ⊆ (S₁ ∪ S₂),
    sorry{
       intro s,intro hs, 
       set S₃ := S₁ ∪ S₂ with hs3,
       have hs3 : S₃ = {x : I | ↑(pab.to_fun x) ∈ X₁∪X₂}:= by tauto,
       rw hs3, simp only [set.mem_union_eq, set.mem_set_of_eq], unfold_coes,
       have k : ∀p, @incl X _ (X₁∪X₂) p ∈ X₁∪X₂,
       {
        intro p, cases p, rw incl, tauto,
       }, apply k,
    },
    have popen1 : is_open S₁,
    sorry{
      have k: S₁ = pab.to_fun ⁻¹' (incl ⁻¹' X₁.carrier),
      {
        rw hs1, rw set.preimage, rw set.preimage, refl,
      }, rw k, apply is_open.preimage, cases pab, cases pab__to_continuous_map, assumption,
      apply is_open.preimage, exact incl_continuous, exact X₁.univ_open,
    },
    have popen2 : is_open S₂,
    sorry{
      have k: S₂ = pab.to_fun ⁻¹' (incl ⁻¹' X₂.carrier),
      {
        rw hs2, rw set.preimage, rw set.preimage, refl,
      }, rw k, apply is_open.preimage, cases pab, cases pab__to_continuous_map, assumption,
      apply is_open.preimage, exact incl_continuous, exact X₂.univ_open,
    },
    set c := ![S₁, S₂] with hc,
    have hc₁ : ∀ (i) , is_open (c i),
    sorry{
      intro i, fin_cases i, assumption, assumption,
    },
    have hc₂ : set.univ ⊆ ⋃ i, c i,
    sorry{
      have k : (⋃ i, c i) = S₁ ∪ S₂,
      {
        rw hc, simp only [], ext, simp [fin.exists_fin_two],
      },
      rw k, assumption,
    },
    have hcover := lebesgue_number_lemma (compact_univ) hc₁ hc₂,
    choose n H pn using hcover,
    sorry,
    
    -- have n : set (↥I × ↥I) := sorry,
    -- have H : n ∈ uniformity ↥I := sorry,
    -- have pn : ∀ (x : ↥I), x ∈ set.univ → (∃ (i : fin (1:ℕ).succ), {y : ↥I | (x, y) ∈ n} ⊆ (λ (i : fin (1:ℕ).succ), c i) i) := sorry,
  },
end
}

#print w