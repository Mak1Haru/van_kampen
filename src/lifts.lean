import .open_subspace

variables {X : Type*} [topological_space X]
variables {H : top_subspace X}
variables {G : top_subspace X} (h : H ≤ G)
variables {a b : H}

noncomputable theory

#check topological_space.opens

open_locale classical topological_space filter unit_interval
open filter set function unit_interval

def subspace_path_lift (p : path a b) : path (incl a) (incl b) :=
begin
  fconstructor,
  {
    exact { to_fun := i ∘ p.to_continuous_map,
            continuous_to_fun := continuous_induced_dom.comp (map_continuous p.to_continuous_map)}
  }, 
  {
    simp only [path.coe_to_continuous_map, function.comp_app, path.source], unfold i, unfold incl, refl,
  },
  {
    simp only [path.target, path.coe_to_continuous_map, function.comp_app], unfold i, unfold incl, refl,
  }
end

def  subspace_path_incl (p : path a b) : path (open_incl h a) (open_incl h b) :=
begin
  fconstructor, exact continuous_map.comp (top_subspace_incl h) p.to_continuous_map,
  simp only [path.coe_to_continuous_map, continuous_map.comp_apply, path.source, continuous_map.to_fun_eq_coe],
  unfold top_subspace_incl, simp only [continuous_map.coe_mk, eq_self_iff_true], 
  simp only [path.target, path.coe_to_continuous_map, continuous_map.comp_apply, continuous_map.to_fun_eq_coe],
  unfold top_subspace_incl, simp only [continuous_map.coe_mk, eq_self_iff_true],
end


notation `πₓ` := fundamental_groupoid.fundamental_groupoid_functor.obj
notation `π` := fundamental_groupoid.fundamental_groupoid_functor
notation `πₘ` := fundamental_groupoid.fundamental_groupoid_functor.map

def grpd_induced_incl : πₓ (Top.of H) ⟶ πₓ (Top.of G) := πₘ (top_subspace_incl h)

-- projection of a subspace to a subspace --

structure proj_subspace {H G : top_subspace X} (h : H ≤ G) :=
(obj : C(H, G))
(path : ∀ (a b : H), path a b → path (obj a) (obj b))

def Id {H G : top_subspace X} (h : H ≤ G) : proj_subspace h :=
{
  obj := top_subspace_incl h,
  path := λa b, subspace_path_incl h
}

-- projection of a space to a groupoid --

local attribute [instance] path.homotopic.setoid

structure proj_grpd (H : top_subspace X) (G : category_theory.Groupoid):= 
(obj : H → G)
(path {a b : H} : path a b → (obj a ⟶ obj b))

def self_grpd (H : top_subspace X) : proj_grpd H (πₓ (Top.of H)):= 
{ 
  obj := λx, x,
  path := 
  begin
    intros a b pab, exact ⟦pab⟧
  end,
}

-- lift of a path to subspace from inclusion --

def b_incl (a : X) (ha : a ∈ H) : H := 
begin
  fconstructor, exact a, exact ha,
end

@[simp] lemma incl_inv (a : H) : b_incl (incl a) (incl_carrier a) = a :=
begin
  simp_rw b_incl, simp_rw incl,cases a,simp,
end

lemma bincl_open (a : H) : b_incl (incl a) (openincl_carrier h a) = open_incl h a :=
begin
  simp_rw open_incl, rw b_incl, simp_rw incl, cases a, simp,
end


def path_lift_func {a b : X} (p : path a b) (hp : set.range p ⊆ H.carrier)
: I → H :=
begin
  intro x, let fx := p.to_fun x,
  have pfx : fx ∈ H.carrier,
  {
    apply hp, have hfx : fx = p.to_fun x, tauto,rw hfx, simp only [path.coe_to_continuous_map, set.mem_range_self, continuous_map.to_fun_eq_coe]
  }, exact b_incl fx pfx,
end

lemma path_lift_eq {a b : X} (p : path a b) (hp : set.range p ⊆ H) : incl ∘ (path_lift_func p hp) = p :=
begin
  ext1, rw function.comp, simp only [], rw path_lift_func, simp only [path.coe_to_continuous_map, continuous_map.to_fun_eq_coe],
  simp_rw b_incl,
end

lemma continuous_lift {a b : X} (p : path a b) (hp : set.range p ⊆ H) : continuous (path_lift_func p hp) :=
begin
  fconstructor, intro s, intro hs, 
  have hp : path_lift_func p hp ⁻¹' s = (incl ∘ path_lift_func p hp) ⁻¹' (incl '' s),
  {
    rw @set.preimage_comp _ _ _ (path_lift_func p hp) incl (incl '' s), 
    rw set.preimage_image_eq, exact incl_inj,
  },
  rw path_lift_eq at hp, rw hp,
  have hp2 : is_open (incl '' s),
  {
    apply incl_open_map, assumption,
  },
  have hp3 : continuous p,
  {
    continuity,
  },
  set k := incl ''s, cases hp3, apply hp3, assumption,
end

lemma range_in_init {a b : X} (p : path a b) (hp : set.range p ⊆ H) : a ∈ H :=
begin
  apply hp, rw range, simp only [set.mem_set_of_eq], use 0, exact p.source,
end 

lemma range_in_end {a b : X} (p : path a b) (hp : set.range p ⊆ H) : b ∈ H :=
begin
  apply hp, rw range, simp only [set.mem_set_of_eq], use 1, exact p.target,
end 

def path_lift_def {a b : X} (p : path a b) (hp : set.range p ⊆ H) : path (b_incl a (range_in_init p hp)) (b_incl b (range_in_end p hp)) := 
{ to_fun := path_lift_func p hp,
  continuous_to_fun := continuous_lift p hp ,
  source' := 
  begin
    simp only [],rw path_lift_func, rw b_incl, simp only [path.coe_to_continuous_map, path.source, continuous_map.to_fun_eq_coe],
    rw b_incl,
  end,
  target' := 
  begin
    simp only [],rw path_lift_func, rw b_incl, simp only [path.target, path.coe_to_continuous_map, continuous_map.to_fun_eq_coe],
    rw b_incl,
  end
}

theorem path_lift_def_eq {a b : X} (p : path a b) (hp : set.range p ⊆ H.carrier) : subspace_path_lift (path_lift_def p hp) = p :=
begin
  rw subspace_path_lift, rw path_lift_def, simp, cases p,simp, ext1, finish,
end

theorem path_incl_point_eq {a b : H} (p : path a b) (x : I) : ↑(p x) = (subspace_path_lift p) x :=
begin
  rw subspace_path_lift, unfold_coes, simp,
end

-- lemma t {K : Type} (f : K → H) (s : set K) : (f '' s) = incl ''

theorem path_incl_set_eq {a b : H} (p : path a b) (s : set I) : ↑(p '' s) = (subspace_path_lift p) '' s :=
begin
  unfold_coes, rw ←set.image_comp, apply set.image_congr', simp_rw path_incl_point_eq, rw subspace_path_lift, simp,
  --  cases p with p _ _, cases p  with p _, simp_rw set.image,unfold_coes, simp,
end

theorem path_incl_range_eq {a b : H} (p : path a b) : ↑(set.range p) = set.range (subspace_path_lift p) :=
begin
  unfold_coes, rw ←set.image_univ, rw ← set.image_univ, apply path_incl_set_eq,
  --  cases p with p _ _, cases p  with p _, simp_rw set.image,unfold_coes, simp,
end

theorem path_incl_range {a b : H} (p : path a b) (K : set X) (hp : ↑(set.range p) ⊆ K) :
set.range (subspace_path_lift p) ⊆ K :=
begin
  rw path_incl_range_eq at *, assumption,
end


