import LowDegree.Asymptotics.NoShortCycles
import LowDegree.ForestTruncation
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Order.Floor.Div

namespace LowDegree

open Asymptotics Filter Topology
open scoped SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace PercolatedAcyclic

variable {V : Type*} {G : SimpleGraph V}

private theorem isCycle_adj_of_fin_sub_eq_one
    {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    (i j : Fin p.length) (hsub : (i - j).val = 1) :
    G.Adj (p.getVert i.val) (p.getVert j.val) := by
  have hlen : 3 ≤ p.length := hp.three_le_length
  by_cases hji : j ≤ i
  · have hvals : i.val = j.val + 1 := by
      have hcast := Fin.intCast_val_sub_eq_sub_add_ite i j
      rw [if_pos hji, hsub] at hcast
      norm_num at hcast ⊢
      omega
    have hadj := p.adj_getVert_succ j.isLt
    rw [hvals]
    exact hadj.symm
  · have hji' : i < j := lt_of_not_ge hji
    have hcast := Fin.intCast_val_sub_eq_sub_add_ite i j
    rw [if_neg hji, hsub] at hcast
    norm_num at hcast
    have hi : i.val = 0 := by omega
    have hj : j.val + 1 = p.length := by omega
    have hadj := p.adj_getVert_succ j.isLt
    have hend : p.getVert (j.val + 1) = v := by
      calc
        p.getVert (j.val + 1) = p.getVert p.length :=
          congrArg p.getVert hj
        _ = v := p.getVert_length
    have hadj' : G.Adj v (p.getVert j.val) := by
      simpa only [hend] using hadj.symm
    have hstart : p.getVert i.val = v := by
      calc
        p.getVert i.val = p.getVert 0 := congrArg p.getVert hi
        _ = v := p.getVert_zero
    simpa only [hstart] using hadj'

noncomputable def cycleCopyOfIsCycle
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph p.length) G where
  toHom :=
    { toFun := fun i ↦ p.getVert i.val
      map_rel' := by
        intro i j hij
        rw [SimpleGraph.cycleGraph_adj'] at hij
        rcases hij with hij | hij
        · exact isCycle_adj_of_fin_sub_eq_one hp i j hij
        · exact (isCycle_adj_of_fin_sub_eq_one hp j i hij).symm }
  injective' := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hij

private def pathUnionGraph {u w : V}
    (p q : G.Path u w) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet
    ({e | e ∈ (p : G.Walk u w).edges} ∪
      {e | e ∈ (q : G.Walk u w).edges})

private theorem pathUnionGraph_le {u w : V}
    (p q : G.Path u w) : pathUnionGraph p q ≤ G := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  intro e he
  rw [pathUnionGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
  rcases he.1 with he | he
  · exact (p : G.Walk u w).edges_subset_edgeSet he
  · exact (q : G.Walk u w).edges_subset_edgeSet he

private theorem path_edges_subset_pathUnionGraph_left {u w : V}
    (p q : G.Path u w) :
    ∀ e ∈ (p : G.Walk u w).edges, e ∈ (pathUnionGraph p q).edgeSet := by
  intro e he
  rw [pathUnionGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨Or.inl he,
    G.not_isDiag_of_mem_edgeSet ((p : G.Walk u w).edges_subset_edgeSet he)⟩

private theorem path_edges_subset_pathUnionGraph_right {u w : V}
    (p q : G.Path u w) :
    ∀ e ∈ (q : G.Walk u w).edges, e ∈ (pathUnionGraph p q).edgeSet := by
  intro e he
  rw [pathUnionGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨Or.inr he,
    G.not_isDiag_of_mem_edgeSet ((q : G.Walk u w).edges_subset_edgeSet he)⟩

private theorem card_pathUnionGraph_edgeFinset_le
    [Fintype V] [DecidableEq V] {u w : V}
    (p q : G.Path u w) :
    (pathUnionGraph p q).edgeFinset.card ≤
      (p : G.Walk u w).length + (q : G.Walk u w).length := by
  let H := pathUnionGraph p q
  have hsubset : H.edgeFinset ⊆
      (p : G.Walk u w).edges.toFinset ∪
        (q : G.Walk u w).edges.toFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    change e ∈ (pathUnionGraph p q).edgeSet at he
    rw [pathUnionGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
    rcases he.1 with he | he
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr he)
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr he)
  calc
    H.edgeFinset.card ≤
        ((p : G.Walk u w).edges.toFinset ∪
          (q : G.Walk u w).edges.toFinset).card :=
      Finset.card_le_card hsubset
    _ ≤ (p : G.Walk u w).edges.toFinset.card +
        (q : G.Walk u w).edges.toFinset.card := Finset.card_union_le _ _
    _ ≤ (p : G.Walk u w).edges.length +
        (q : G.Walk u w).edges.length :=
      Nat.add_le_add
        (List.toFinset_card_le (p : G.Walk u w).edges)
        (List.toFinset_card_le (q : G.Walk u w).edges)
    _ = (p : G.Walk u w).length + (q : G.Walk u w).length := by
      rw [SimpleGraph.Walk.length_edges, SimpleGraph.Walk.length_edges]

theorem path_eq_of_no_cycle_copy_le
    [Fintype V] [DecidableEq V] {D : ℕ}
    (hshort : ∀ l : ℕ, 3 ≤ l → l ≤ D →
      ¬(SimpleGraph.cycleGraph l ⊑ G))
    {u w : V} (p q : G.Path u w)
    (hlength : (p : G.Walk u w).length +
      (q : G.Walk u w).length ≤ D) : p = q := by
  let H := pathUnionGraph p q
  let hpH : ∀ e ∈ (p : G.Walk u w).edges, e ∈ H.edgeSet :=
    path_edges_subset_pathUnionGraph_left p q
  let hqH : ∀ e ∈ (q : G.Walk u w).edges, e ∈ H.edgeSet :=
    path_edges_subset_pathUnionGraph_right p q
  let pH : H.Path u w :=
    ⟨(p : G.Walk u w).transfer H hpH, p.property.transfer hpH⟩
  let qH : H.Path u w :=
    ⟨(q : G.Walk u w).transfer H hqH, q.property.transfer hqH⟩
  by_contra hpq
  have hHcycle : ¬H.IsAcyclic := by
    intro hacyclic
    have hpHqH : pH = qH := hacyclic.path_unique pH qH
    apply hpq
    apply Subtype.ext
    apply SimpleGraph.Walk.support_injective
    have hsupp := congrArg
      (fun r : H.Path u w ↦ (r : H.Walk u w).support) hpHqH
    simpa [pH, qH] using hsupp
  obtain ⟨a, cycle, hcycle, _hgirth⟩ :=
    SimpleGraph.exists_girth_eq_length.mpr hHcycle
  have hcycle_card : cycle.length ≤ H.edgeFinset.card := by
    have hedgeSubset : cycle.edges.toFinset ⊆ H.edgeFinset := by
      intro e he
      rw [List.mem_toFinset] at he
      rw [SimpleGraph.mem_edgeFinset]
      exact cycle.edges_subset_edgeSet he
    calc
      cycle.length = cycle.edges.toFinset.card := by
        rw [List.toFinset_card_of_nodup hcycle.isTrail.edges_nodup,
          SimpleGraph.Walk.length_edges]
      _ ≤ H.edgeFinset.card := Finset.card_le_card hedgeSubset
  have hcycleD : cycle.length ≤ D :=
    hcycle_card.trans
      ((card_pathUnionGraph_edgeFinset_le p q).trans hlength)
  have hcopyH : SimpleGraph.cycleGraph cycle.length ⊑ H :=
    ⟨cycleCopyOfIsCycle hcycle⟩
  have hcopyG : SimpleGraph.cycleGraph cycle.length ⊑ G :=
    hcopyH.trans ⟨SimpleGraph.Copy.ofLE H G (pathUnionGraph_le p q)⟩
  exact hshort cycle.length hcycle.three_le_length hcycleD hcopyG

private def forwardWalk {l : ℕ} [NeZero l] (hl : 2 < l) (a : Fin l) :
    (s : ℕ) → (SimpleGraph.cycleGraph l).Walk a (a + Fin.ofNat l s)
  | 0 => SimpleGraph.Walk.nil.copy rfl (by
      have hzero : Fin.ofNat l 0 = 0 := by
        apply Fin.ext
        simp
      rw [hzero, add_zero])
  | s + 1 => by
      have hadj : (SimpleGraph.cycleGraph l).Adj a (a + 1) := by
        rw [SimpleGraph.cycleGraph_adj']
        right
        have heq : a + 1 - a = (1 : Fin l) := by abel
        simp [heq, Nat.mod_eq_of_lt (by omega : 1 < l)]
      exact SimpleGraph.Walk.cons hadj
        ((forwardWalk hl (a + 1) s).copy rfl (by
          rw [show Fin.ofNat l (s + 1) = Fin.ofNat l s + 1 by
            apply Fin.ext
            simp [Fin.val_add, Nat.add_mod]]
          abel))

@[simp] private theorem forwardWalk_length {l : ℕ} [NeZero l]
    (hl : 2 < l) (a : Fin l) (s : ℕ) : (forwardWalk hl a s).length = s := by
  induction s generalizing a with
  | zero => simp [forwardWalk]
  | succ s ih => simp [forwardWalk, ih]

private theorem forwardWalk_getVert {l : ℕ} [NeZero l]
    (hl : 2 < l) (a : Fin l) (s i : ℕ) (hi : i ≤ s) :
    (forwardWalk hl a s).getVert i = a + Fin.ofNat l i := by
  induction s generalizing a i with
  | zero => simp_all [forwardWalk]
  | succ s ih =>
      by_cases hi0 : i = 0
      · subst i
        simp [forwardWalk]
      · have his : i - 1 ≤ s := by omega
        rw [forwardWalk]
        simp only [SimpleGraph.Walk.getVert_cons _ _ hi0,
          SimpleGraph.Walk.getVert_copy]
        rw [ih (a := a + 1) (i := i - 1) his]
        have hiEq : Fin.ofNat l i = 1 + Fin.ofNat l (i - 1) := by
          rw [show i = 1 + (i - 1) by omega]
          apply Fin.ext
          simp [Fin.val_add, Nat.add_mod]
        rw [hiEq]
        simp [add_assoc]

private theorem forwardWalk_isPath {l : ℕ} [NeZero l]
    (hl : 2 < l) (a : Fin l) (s : ℕ) (hs : s < l) :
    (forwardWalk hl a s).IsPath := by
  rw [← SimpleGraph.Walk.IsPath.getVert_injOn_iff]
  intro i hi j hj hij
  simp only [Set.mem_setOf_eq, forwardWalk_length] at hi hj
  rw [forwardWalk_getVert hl a s i hi, forwardWalk_getVert hl a s j hj] at hij
  have hc : Fin.ofNat l i = Fin.ofNat l j := by
    exact add_left_cancel hij
  simpa [Nat.mod_eq_of_lt (lt_of_le_of_lt hi hs),
    Nat.mod_eq_of_lt (lt_of_le_of_lt hj hs)] using congrArg Fin.val hc

private def forwardPath {l : ℕ} [NeZero l]
    (hl : 2 < l) (a : Fin l) (s : ℕ) (hs : s < l) :
    (SimpleGraph.cycleGraph l).Path a (a + Fin.ofNat l s) :=
  ⟨forwardWalk hl a s, forwardWalk_isPath hl a s hs⟩

private theorem getVert_map {V' : Type*} {G' : SimpleGraph V'}
    (f : G →g G') {u v : V} (p : G.Walk u v) (i : ℕ) :
    (p.map f).getVert i = f (p.getVert i) := by
  induction p generalizing i with
  | nil => simp
  | @cons u w v hadj p ih =>
      by_cases hi : i = 0
      · subst i
        simp
      · simp only [SimpleGraph.Walk.map_cons,
          SimpleGraph.Walk.getVert_cons _ _ hi]
        rw [ih]

private def checkpointCode {l r : ℕ} [NeZero l]
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph l) G) :
    Fin (l ⌈/⌉ r) → V :=
  fun j ↦ f (Fin.ofNat l (j.val * r))

private theorem ofNat_add {l : ℕ} [NeZero l] (a b : ℕ) :
    Fin.ofNat l (a + b) = Fin.ofNat l a + Fin.ofNat l b := by
  apply Fin.ext
  simp [Fin.val_add, Nat.add_mod]

theorem cycleCopy_card_le_checkpoint_pow
    [Fintype V] [DecidableEq V] {l r D : ℕ}
    (hl : 3 ≤ l) (hr : 0 < r) (hdouble : 2 * r ≤ D) (hDl : D < l)
    (hshort : ∀ k : ℕ, 3 ≤ k → k ≤ D →
      ¬(SimpleGraph.cycleGraph k ⊑ G)) :
    Fintype.card (SimpleGraph.Copy (SimpleGraph.cycleGraph l) G) ≤
      Fintype.card V ^ (l ⌈/⌉ r) := by
  letI : NeZero l := ⟨by omega⟩
  let t := l ⌈/⌉ r
  have ht_mul : l ≤ r * t := by
    exact (ceilDiv_le_iff_le_mul hr).mp le_rfl
  have hrlt : r < l := by omega
  have hcode : Function.Injective
      (checkpointCode (G := G) (l := l) (r := r)) := by
    intro f g hfg
    apply SimpleGraph.Copy.ext
    intro x
    let i := x.val
    let jNat := i / r
    have hstart_le : r * jNat ≤ i := Nat.mul_div_le i r
    have hjlt : jNat < t := by
      by_contra hj
      have htj : t ≤ jNat := Nat.le_of_not_gt hj
      have hlj : l ≤ r * jNat :=
        (ceilDiv_le_iff_le_mul hr).mp htj
      omega
    let j : Fin t := ⟨jNat, hjlt⟩
    let a := jNat * r
    let s := min r (l - a)
    let k := i - a
    have ha : a = r * jNat := by simp [a, Nat.mul_comm]
    have halt : a < l := by omega
    have hs_le_r : s ≤ r := Nat.min_le_left _ _
    have hslt : s < l := hs_le_r.trans_lt hrlt
    have hk_le_s : k ≤ s := by
      have hk_lt_r : k < r := by
        have hmod : i % r < r := Nat.mod_lt _ hr
        have hka : k = i % r := by
          dsimp [k, a, jNat]
          have hdiv := Nat.div_add_mod i r
          have hcomm : i / r * r = r * (i / r) := Nat.mul_comm _ _
          omega
        omega
      have hk_lt_rest : k < l - a := by omega
      exact le_min (Nat.le_of_lt hk_lt_r) (Nat.le_of_lt hk_lt_rest)
    let start : Fin l := Fin.ofNat l a
    let endpoint : Fin l := start + Fin.ofNat l s
    have hstart : f start = g start := by
      have hc := congrFun hfg j
      simpa [checkpointCode, start, a, j, jNat, Nat.mul_comm] using hc
    have hend : f endpoint = g endpoint := by
      by_cases hnext : jNat + 1 < t
      · let j' : Fin t := ⟨jNat + 1, hnext⟩
        have hfull : a + r < l := by
          have hnot : ¬ l ≤ r * (jNat + 1) := by
            intro hle
            have htle : t ≤ jNat + 1 :=
              (ceilDiv_le_iff_le_mul hr).mpr hle
            omega
          have hlt : r * (jNat + 1) < l := Nat.lt_of_not_ge hnot
          simpa [a, Nat.mul_add, Nat.mul_comm] using hlt
        have hs_eq : s = r := Nat.min_eq_left (by omega)
        have hep : endpoint = Fin.ofNat l ((jNat + 1) * r) := by
          change Fin.ofNat l a + Fin.ofNat l s = _
          rw [← ofNat_add, hs_eq]
          congr 1
          simp [a, Nat.mul_add, Nat.mul_comm]
        have hc := congrFun hfg j'
        simpa [checkpointCode, j', hep] using hc
      · have hjlast : jNat + 1 = t := by omega
        have hreach : l ≤ a + r := by
          rw [ha, ← Nat.mul_succ]
          simpa [hjlast] using ht_mul
        have hs_eq : s = l - a := Nat.min_eq_right (by omega)
        have hep : endpoint = 0 := by
          change Fin.ofNat l a + Fin.ofNat l s = 0
          rw [← ofNat_add, hs_eq, Nat.add_sub_of_le halt.le]
          apply Fin.ext
          simp
        let j0 : Fin t := ⟨0, lt_of_le_of_lt (Nat.zero_le _) hjlt⟩
        have hc := congrFun hfg j0
        simpa [checkpointCode, j0, hep] using hc
    let pF : G.Path (f start) (f endpoint) :=
      (forwardPath (by omega : 2 < l) start s hslt).map
        f.toHom f.injective
    let pG0 : G.Path (g start) (g endpoint) :=
      (forwardPath (by omega : 2 < l) start s hslt).map
        g.toHom g.injective
    let pG : G.Path (f start) (f endpoint) :=
      ⟨(pG0 : G.Walk (g start) (g endpoint)).copy hstart.symm hend.symm,
        (SimpleGraph.Walk.isPath_copy _ _ _).mpr pG0.property⟩
    have hpEq : pF = pG := by
      apply path_eq_of_no_cycle_copy_le hshort
      simp [pF, pG, pG0, forwardPath]
      omega
    have hverts := congrArg
      (fun p : G.Path (f start) (f endpoint) ↦
        (p : G.Walk (f start) (f endpoint)).getVert k) hpEq
    have hsource : start + Fin.ofNat l k = x := by
      have hik : a + k = i := by omega
      change Fin.ofNat l a + Fin.ofNat l k = x
      rw [← ofNat_add, hik]
      apply Fin.ext
      simp [i]
    simp [pF, pG, pG0, SimpleGraph.Path.map, forwardPath,
      getVert_map, forwardWalk_getVert, hk_le_s] at hverts
    change f (start + Fin.ofNat l k) = g (start + Fin.ofNat l k) at hverts
    rw [hsource] at hverts
    exact hverts
  calc
    Fintype.card (SimpleGraph.Copy (SimpleGraph.cycleGraph l) G) ≤
        Fintype.card (Fin t → V) := Fintype.card_le_of_injective _ hcode
    _ = Fintype.card V ^ t := by simp
    _ = Fintype.card V ^ (l ⌈/⌉ r) := rfl

private noncomputable def restrictAmbientCopy {n l : ℕ}
    (G : SimpleGraph (Fin n))
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph l)
      (⊤ : SimpleGraph (Fin n)))
    (hsub : NoShortCycles.ambientCopyEdges f ⊆
      Finset.univ.filter fun e : AmbientEdge n ↦
        (e : Sym2 (Fin n)) ∈ G.edgeSet) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph l) G := by
  letI : DecidableRel (SimpleGraph.cycleGraph l).Adj := Classical.decRel _
  exact
    { toHom :=
        { toFun := f
          map_rel' := by
            intro x y hxy
            let e : (SimpleGraph.cycleGraph l).edgeSet :=
              ⟨s(x, y), hxy⟩
            have he : f.mapEdgeSet e ∈ NoShortCycles.ambientCopyEdges f := by
              rw [NoShortCycles.ambientCopyEdges, Finset.mem_map]
              exact ⟨e, Finset.mem_univ _, rfl⟩
            have heG := hsub he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heG
            exact heG }
      injective' := f.injective }

private theorem cycleSupports_contained_card_le_copy_card
    {n l : ℕ} (G : SimpleGraph (Fin n)) :
    ((NoShortCycles.cycleSupports n l).filter fun S ↦ S ⊆
        Finset.univ.filter fun e : AmbientEdge n ↦
          (e : Sym2 (Fin n)) ∈ G.edgeSet).card ≤
      Fintype.card (SimpleGraph.Copy (SimpleGraph.cycleGraph l) G) := by
  let supportOfCopy : SimpleGraph.Copy (SimpleGraph.cycleGraph l) G →
      Finset (AmbientEdge n) := fun f ↦
    NoShortCycles.ambientCopyEdges ((SimpleGraph.Copy.ofLE G ⊤ le_top).comp f)
  have hsubset :
      (NoShortCycles.cycleSupports n l).filter (fun S ↦ S ⊆
        Finset.univ.filter fun e : AmbientEdge n ↦
          (e : Sym2 (Fin n)) ∈ G.edgeSet) ⊆
        Finset.univ.image supportOfCopy := by
    intro S hS
    simp only [Finset.mem_filter] at hS
    rcases hS with ⟨hScycle, hSG⟩
    simp only [NoShortCycles.cycleSupports, Finset.mem_image, Finset.mem_univ,
      true_and] at hScycle
    rcases hScycle with ⟨f, rfl⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    let g := restrictAmbientCopy G f hSG
    refine ⟨g, ?_⟩
    apply Finset.ext
    intro e
    simp only [supportOfCopy, NoShortCycles.ambientCopyEdges, Finset.mem_map,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  calc
    _ ≤ (Finset.univ.image supportOfCopy).card := Finset.card_le_card hsubset
    _ ≤ Fintype.card (SimpleGraph.Copy (SimpleGraph.cycleGraph l) G) := by
      simpa using Finset.card_image_le (s := (Finset.univ :
        Finset (SimpleGraph.Copy (SimpleGraph.cycleGraph l) G)))

theorem sum_cycle_containment_le_checkpoint_pow
    {n l r D : ℕ} (plant : SimpleGraph (Fin n))
    (hl : 3 ≤ l) (hr : 0 < r) (hdouble : 2 * r ≤ D) (hDl : D < l)
    (hshort : ∀ k : ℕ, 3 ≤ k → k ≤ D →
      ¬(SimpleGraph.cycleGraph k ⊑ plant)) :
    ∑ S ∈ NoShortCycles.cycleSupports n l,
        NoShortCycles.containmentProbability plant S ≤
      (n : ℝ) ^ (l ⌈/⌉ r) := by
  have hperm_card : 0 < Fintype.card (Equiv.Perm (Fin n)) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin n)⟩
  have hperm_real : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast hperm_card
  have hpermutation (σ : Equiv.Perm (Fin n)) :
      ((NoShortCycles.cycleSupports n l).filter fun S ↦
        S ⊆ permutedPlantEdges plant σ).card ≤ n ^ (l ⌈/⌉ r) := by
    have hcard := cycleSupports_contained_card_le_copy_card
      (G := permutedPlant plant σ) (l := l)
    have hedges : (Finset.univ.filter fun e : AmbientEdge n ↦
          (e : Sym2 (Fin n)) ∈ (permutedPlant plant σ).edgeSet) =
        permutedPlantEdges plant σ := by
      rfl
    rw [hedges] at hcard
    refine hcard.trans ?_
    have hshortPerm : ∀ k : ℕ, 3 ≤ k → k ≤ D →
        ¬(SimpleGraph.cycleGraph k ⊑ permutedPlant plant σ) := by
      intro k hk hkD hcopy
      apply hshort k hk hkD
      rcases hcopy with ⟨f⟩
      exact ⟨(SimpleGraph.Iso.map σ plant).symm.toCopy.comp f⟩
    simpa using (cycleCopy_card_le_checkpoint_pow
      (V := Fin n) (G := permutedPlant plant σ)
      hl hr hdouble hDl hshortPerm)
  have hcount :
      ∑ S ∈ NoShortCycles.cycleSupports n l,
          permutationContainmentCount plant S =
        ∑ σ : Equiv.Perm (Fin n),
          ((NoShortCycles.cycleSupports n l).filter fun S ↦
            S ⊆ permutedPlantEdges plant σ).card := by
    unfold permutationContainmentCount
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hcount_bound :
      ∑ S ∈ NoShortCycles.cycleSupports n l,
          permutationContainmentCount plant S ≤
        Fintype.card (Equiv.Perm (Fin n)) * n ^ (l ⌈/⌉ r) := by
    rw [hcount]
    calc
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), n ^ (l ⌈/⌉ r) := by
        exact Finset.sum_le_sum fun σ _ ↦ hpermutation σ
      _ = _ := by simp
  unfold NoShortCycles.containmentProbability
  calc
    (∑ S ∈ NoShortCycles.cycleSupports n l,
        (permutationContainmentCount plant S : ℝ) /
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) =
        ((∑ S ∈ NoShortCycles.cycleSupports n l,
          permutationContainmentCount plant S : ℕ) : ℝ) /
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast rfl
    _ ≤ (n : ℝ) ^ (l ⌈/⌉ r) := by
      rw [div_le_iff₀ hperm_real]
      exact_mod_cast (by simpa [Nat.mul_comm] using hcount_bound)

theorem retainedPlantContainmentProbability_eq {n : ℕ}
    (ε : NoiseRate) (plant : SimpleGraph (Fin n))
    (S : Finset (AmbientEdge n)) :
    randomPlantContainmentProbability (retainedPlantLaw ε plant) S =
      (1 - (ε : ℝ)) ^ S.card *
        NoShortCycles.containmentProbability plant S := by
  let θ : BernoulliParameter := ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  have hcoeff := congrArg (fun f ↦ fourierCoeff θ f S)
    (randomForcedLikelihood_retainedPlantLaw_eq_noisedLikelihood θ ε plant)
  change fourierCoeff θ
      (randomForcedLikelihood θ (retainedPlantLaw ε plant)) S =
    fourierCoeff θ (noisedLikelihood θ ε plant) S at hcoeff
  rw [fourierCoeff_randomForcedLikelihood,
    fourierCoeff_noisedLikelihood] at hcoeff
  apply mul_right_cancel₀ (pow_ne_zero _ θ.forcedWeight_pos.ne')
  simpa [NoShortCycles.containmentProbability, mul_assoc] using hcoeff

theorem FiniteLaw.prob_finset_biUnion_le'
    {Ω I : Type*} [Fintype Ω]
    [DecidableEq Ω] [DecidableEq I]
    (q : FiniteLaw Ω) (s : Finset I) (event : I → Finset Ω) :
    q.prob (s.biUnion event) ≤ ∑ i ∈ s, q.prob (event i) := by
  induction s using Finset.induction_on with
  | empty => simp [FiniteLaw.prob]
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      have hunion :
          q.prob (event i ∪ s.biUnion event) ≤
            q.prob (event i) + q.prob (s.biUnion event) := by
        have hidentity := Finset.sum_union_inter
          (s₁ := event i) (s₂ := s.biUnion event) (f := q.mass)
        have hinter : 0 ≤ ∑ ω ∈ event i ∩ s.biUnion event, q.mass ω :=
          Finset.sum_nonneg fun ω _ ↦ q.mass_nonneg ω
        unfold FiniteLaw.prob
        linarith
      exact hunion.trans (add_le_add_left ih _)

private def cycleContainmentEvent {n : ℕ}
    (S : Finset (AmbientEdge n)) :
    Finset (Finset (AmbientEdge n)) :=
  Finset.univ.filter fun A ↦ S ⊆ A

private def cycleContainmentUnion (n : ℕ) :
    Finset (Finset (AmbientEdge n)) :=
  (Finset.Icc 3 n).biUnion fun l ↦
    (NoShortCycles.cycleSupports n l).biUnion cycleContainmentEvent

private theorem cyclicEvent_subset_cycleContainmentUnion (n : ℕ) :
    (Finset.univ : Finset (Finset (AmbientEdge n))).filter
        (fun A ↦ ¬IsForestEdgeSet A) ⊆
      cycleContainmentUnion n := by
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
  obtain ⟨v, c, hc, _⟩ := SimpleGraph.exists_girth_eq_length.mpr hA
  let fG : SimpleGraph.Copy (SimpleGraph.cycleGraph c.length)
      (graphOfAmbientEdges A) := cycleCopyOfIsCycle hc
  let fTop : SimpleGraph.Copy (SimpleGraph.cycleGraph c.length)
      (⊤ : SimpleGraph (Fin n)) :=
    (SimpleGraph.Copy.ofLE (graphOfAmbientEdges A) ⊤ le_top).comp fG
  let S := NoShortCycles.ambientCopyEdges fTop
  have hlen_le : c.length ≤ n :=
    NoShortCycles.cycle_length_le_ambient fTop
  have hS_cycle : S ∈ NoShortCycles.cycleSupports n c.length := by
    simp only [NoShortCycles.cycleSupports, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact ⟨fTop, rfl⟩
  have hS_sub : S ⊆ A := by
    have hsubset := NoShortCycles.ambientCopyEdges_ofLE_subset fG
    intro e he
    have heGraph := hsubset he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heGraph
    exact (mem_graphOfAmbientEdges_edgeSet_iff A e).mp heGraph
  simp only [cycleContainmentUnion, Finset.mem_biUnion]
  refine ⟨c.length, Finset.mem_Icc.mpr ⟨hc.three_le_length, hlen_le⟩, ?_⟩
  refine ⟨S, hS_cycle, ?_⟩
  simp [cycleContainmentEvent, hS_sub]

private theorem containmentProbability_eq_zero_of_no_cycle_copy
    {n l : ℕ} (plant : SimpleGraph (Fin n))
    (hno : ¬(SimpleGraph.cycleGraph l ⊑ plant))
    {S : Finset (AmbientEdge n)}
    (hS : S ∈ NoShortCycles.cycleSupports n l) :
    NoShortCycles.containmentProbability plant S = 0 := by
  simp only [NoShortCycles.cycleSupports, Finset.mem_image,
    Finset.mem_univ, true_and] at hS
  rcases hS with ⟨f, rfl⟩
  unfold NoShortCycles.containmentProbability permutationContainmentCount
  have hempty :
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) ↦
        NoShortCycles.ambientCopyEdges f ⊆
          permutedPlantEdges plant σ) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hedges : permutedPlantEdges plant σ =
        Finset.univ.filter fun e : AmbientEdge n ↦
          (e : Sym2 (Fin n)) ∈ (permutedPlant plant σ).edgeSet := by
      rfl
    rw [hedges] at hσ
    let g := restrictAmbientCopy (permutedPlant plant σ) f hσ
    exact hno ⟨(SimpleGraph.Iso.map σ plant).symm.toCopy.comp g⟩
  rw [hempty]
  simp

theorem retainedPlantCycleProbability_le_cycle_sum {n : ℕ}
    (ε : NoiseRate) (plant : SimpleGraph (Fin n)) :
    retainedPlantCycleProbability ε plant ≤
      ∑ l ∈ Finset.Icc 3 n,
        ∑ S ∈ NoShortCycles.cycleSupports n l,
          (1 - (ε : ℝ)) ^ S.card *
            NoShortCycles.containmentProbability plant S := by
  let q := retainedPlantLaw ε plant
  calc
    retainedPlantCycleProbability ε plant ≤
        q.prob (cycleContainmentUnion n) := by
      unfold retainedPlantCycleProbability
      exact q.prob_mono (cyclicEvent_subset_cycleContainmentUnion n)
    _ ≤ ∑ l ∈ Finset.Icc 3 n,
        q.prob ((NoShortCycles.cycleSupports n l).biUnion
          cycleContainmentEvent) := by
      exact FiniteLaw.prob_finset_biUnion_le' q
        (Finset.Icc 3 n) (fun l ↦
          (NoShortCycles.cycleSupports n l).biUnion cycleContainmentEvent)
    _ ≤ ∑ l ∈ Finset.Icc 3 n,
        ∑ S ∈ NoShortCycles.cycleSupports n l,
          q.prob (cycleContainmentEvent S) := by
      apply Finset.sum_le_sum
      intro l _hl
      exact FiniteLaw.prob_finset_biUnion_le' q
        (NoShortCycles.cycleSupports n l) cycleContainmentEvent
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _hl
      apply Finset.sum_congr rfl
      intro S _hS
      change randomPlantContainmentProbability (retainedPlantLaw ε plant) S = _
      exact retainedPlantContainmentProbability_eq ε plant S

theorem retainedPlantCycleProbability_le_checkpoint_sum
    {n D r : ℕ} (ε : NoiseRate) (plant : SimpleGraph (Fin n))
    (hr : 0 < r) (hdouble : 2 * r ≤ D)
    (hshort : ∀ l : ℕ, 3 ≤ l → l ≤ D →
      ¬(SimpleGraph.cycleGraph l ⊑ plant)) :
    retainedPlantCycleProbability ε plant ≤
      ∑ l ∈ Finset.Icc 3 n,
        if D < l then
          (1 - (ε : ℝ)) ^ l * (n : ℝ) ^ (l ⌈/⌉ r)
        else 0 := by
  refine (retainedPlantCycleProbability_le_cycle_sum ε plant).trans ?_
  apply Finset.sum_le_sum
  intro l hlIcc
  have hl : 3 ≤ l := (Finset.mem_Icc.mp hlIcc).1
  have hcard (S : Finset (AmbientEdge n))
      (hS : S ∈ NoShortCycles.cycleSupports n l) : S.card = l := by
    simp only [NoShortCycles.cycleSupports, Finset.mem_image,
      Finset.mem_univ, true_and] at hS
    rcases hS with ⟨f, rfl⟩
    exact NoShortCycles.card_ambientCycleCopyEdges hl f
  have hfactor :
      (∑ S ∈ NoShortCycles.cycleSupports n l,
          (1 - (ε : ℝ)) ^ S.card *
            NoShortCycles.containmentProbability plant S) =
        (1 - (ε : ℝ)) ^ l *
          ∑ S ∈ NoShortCycles.cycleSupports n l,
            NoShortCycles.containmentProbability plant S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [hcard S hS]
  rw [hfactor]
  by_cases hlong : D < l
  · rw [if_pos hlong]
    apply mul_le_mul_of_nonneg_left
      (sum_cycle_containment_le_checkpoint_pow plant hl hr hdouble hlong hshort)
    exact pow_nonneg (sub_nonneg.mpr ε.2.2.le) _
  · rw [if_neg hlong]
    have hlD : l ≤ D := Nat.le_of_not_gt hlong
    have hsumzero :
        (∑ S ∈ NoShortCycles.cycleSupports n l,
          NoShortCycles.containmentProbability plant S) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      exact containmentProbability_eq_zero_of_no_cycle_copy
        plant (hshort l hl hlD) hS
    rw [hsumzero, mul_zero]

theorem checkpoint_sum_le_exponential_envelope
    {n D r : ℕ} (ε : NoiseRate) (hn : 0 < n)
    (hr : 0 < r) (hdouble : 2 * r ≤ D)
    (hratio : (n : ℝ) * (1 - (ε : ℝ)) ^ r ≤ 1) :
    (∑ l ∈ Finset.Icc 3 n,
        if D < l then
          (1 - (ε : ℝ)) ^ l * (n : ℝ) ^ (l ⌈/⌉ r)
        else 0) ≤
      (n : ℝ) ^ 4 * (1 - (ε : ℝ)) ^ (2 * r) := by
  let q : ℝ := 1 - (ε : ℝ)
  have hq0 : 0 ≤ q := sub_nonneg.mpr ε.2.2.le
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [ε.2.1]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  let B : ℝ := (n : ℝ) * ((n : ℝ) * q ^ r) ^ 2
  have hB0 : 0 ≤ B := by positivity
  have hterm (l : ℕ) (hlmem : l ∈ Finset.Icc 3 n) :
      (if D < l then q ^ l * (n : ℝ) ^ (l ⌈/⌉ r) else 0) ≤ B := by
    by_cases hlong : D < l
    · rw [if_pos hlong]
      let t := l ⌈/⌉ r
      have ht : 3 ≤ t := by
        by_contra hnot
        have ht2 : t ≤ 2 := by omega
        have hl2r : l ≤ r * 2 :=
          (ceilDiv_le_iff_le_mul hr).mp ht2
        omega
      have hrt : r * (t - 1) ≤ l := by
        have hnot : ¬ l ≤ r * (t - 1) := by
          intro hle
          have htle : t ≤ t - 1 :=
            (ceilDiv_le_iff_le_mul hr).mpr hle
          omega
        exact (Nat.lt_of_not_ge hnot).le
      have hqpow : q ^ l ≤ q ^ (r * (t - 1)) :=
        pow_le_pow_of_le_one hq0 hq1 hrt
      calc
        q ^ l * (n : ℝ) ^ t ≤
            q ^ (r * (t - 1)) * (n : ℝ) ^ t :=
          mul_le_mul_of_nonneg_right hqpow (pow_nonneg hn0 _)
        _ = (n : ℝ) * ((n : ℝ) * q ^ r) ^ (t - 1) := by
          have ht_eq : t = (t - 1) + 1 := by omega
          have hnpow : (n : ℝ) ^ t =
              (n : ℝ) ^ (t - 1) * (n : ℝ) := by
            rw [ht_eq, pow_add]
            simp
          rw [pow_mul, hnpow, mul_pow]
          ring
        _ ≤ B := by
          apply mul_le_mul_of_nonneg_left _ hn0
          exact pow_le_pow_of_le_one (mul_nonneg hn0 (pow_nonneg hq0 _))
            hratio (by omega)
    · rw [if_neg hlong]
      exact hB0
  calc
    (∑ l ∈ Finset.Icc 3 n,
        if D < l then q ^ l * (n : ℝ) ^ (l ⌈/⌉ r) else 0) ≤
        (Finset.Icc 3 n).card • B :=
      Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((Finset.Icc 3 n).card : ℝ) * B := by
      simp [nsmul_eq_mul]
    _ ≤ (n : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB0
      exact_mod_cast (show (Finset.Icc 3 n).card ≤ n by simp)
    _ = (n : ℝ) ^ 4 * q ^ (2 * r) := by
      have hpow : q ^ (2 * r) = (q ^ r) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hpow]
      dsimp [B]
      ring

private theorem pow_eq_exp_mul_log {q : ℝ} (hq : 0 < q) (k : ℕ) :
    q ^ k = Real.exp (Real.log q * (k : ℝ)) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_def_of_pos hq _

private theorem natPow_mul_qPow_eq_exp
    {q : ℝ} (hq : 0 < q) {n k m : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ k * q ^ m =
      Real.exp ((k : ℝ) * Real.log (n : ℝ) +
        Real.log q * (m : ℝ)) := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hnpow : (n : ℝ) ^ k =
      Real.exp ((k : ℝ) * Real.log (n : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hn_real]
  rw [hnpow, pow_eq_exp_mul_log hq, ← Real.exp_add]

theorem exponential_envelope_vanishes_of_log_isLittleO
    (ε : NoiseRate) {D : ℕ → ℕ}
    (hD : LittleO (fun n ↦ Real.log (n : ℝ))
      (fun n ↦ (D n : ℝ))) :
    Vanishes fun n ↦ (n : ℝ) ^ 4 *
      (1 - (ε : ℝ)) ^ (2 * (D n / 2)) := by
  let q : ℝ := 1 - (ε : ℝ)
  let a : ℝ := -Real.log q
  have hqpos : 0 < q := sub_pos.mpr ε.2.2
  have hqlt : q < 1 := by dsimp [q]; linarith [ε.2.1]
  have ha : 0 < a := neg_pos.mpr (Real.log_neg hqpos hqlt)
  have hdomNorm := hD.bound (div_pos ha (by norm_num : (0 : ℝ) < 10))
  have hdom : ∀ᶠ n : ℕ in atTop,
      10 * Real.log (n : ℝ) ≤ a * (D n : ℝ) := by
    filter_upwards [hdomNorm] with n hn
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg n),
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (D n))] at hn
    nlinarith
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ n : ℕ in atTop,
      a / 4 ≤ Real.log (n : ℝ) :=
    (Filter.tendsto_atTop.1 hlogTop) (a / 4)
  have hnegativeLog : Tendsto
      (fun n : ℕ ↦ -2 * Real.log (n : ℝ)) atTop atBot := by
    apply Filter.tendsto_atBot.2
    intro b
    filter_upwards [(Filter.tendsto_atTop.1 hlogTop) (-b / 2)] with n hn
    linarith
  have hupper : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 4 * q ^ (2 * (D n / 2)) ≤
        Real.exp (-2 * Real.log (n : ℝ)) := by
    filter_upwards [hdom, hlogLarge, eventually_ge_atTop 1]
      with n hnDom hnLog hnOne
    have hn : 0 < n := by omega
    have hDpos : 0 < D n := by
      by_contra hnot
      have hDzero : D n = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hDzero] at hnDom
      norm_num at hnDom
      nlinarith
    have hfloorNat : D n - 1 ≤ 2 * (D n / 2) := by omega
    have hfloor : (D n : ℝ) - 1 ≤
        (2 * (D n / 2) : ℕ) := by
      rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ D n)]
      exact_mod_cast hfloorNat
    have hlogq : Real.log q = -a := by simp [a]
    have hexponent :
        (4 : ℝ) * Real.log (n : ℝ) +
            Real.log q * (2 * (D n / 2) : ℕ) ≤
          -2 * Real.log (n : ℝ) := by
      rw [hlogq]
      nlinarith
    rw [natPow_mul_qPow_eq_exp hqpos hn]
    exact Real.exp_le_exp.mpr hexponent
  have hnonneg : ∀ n : ℕ,
      0 ≤ (n : ℝ) ^ 4 * q ^ (2 * (D n / 2)) := by
    intro n
    positivity
  change Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 4 * q ^ (2 * (D n / 2)))
    atTop (nhds 0)
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper
    (Real.tendsto_exp_atBot.comp hnegativeLog)

theorem eventually_halfCutoff_good_of_log_isLittleO
    (ε : NoiseRate) {D : ℕ → ℕ}
    (hD : LittleO (fun n ↦ Real.log (n : ℝ))
      (fun n ↦ (D n : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      0 < D n / 2 ∧
        (n : ℝ) * (1 - (ε : ℝ)) ^ (D n / 2) ≤ 1 := by
  let q : ℝ := 1 - (ε : ℝ)
  have hq0 : 0 ≤ q := sub_nonneg.mpr ε.2.2.le
  have hboundNorm := hD.bound (by norm_num : (0 : ℝ) < 1)
  have hbound : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ (D n : ℝ) := by
    filter_upwards [hboundNorm] with n hn
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg n),
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (D n))] at hn
    simpa using hn
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hDtwo : ∀ᶠ n : ℕ in atTop, 2 ≤ D n := by
    filter_upwards [hbound,
      (Filter.tendsto_atTop.1 hlogTop) 2] with n hnBound hnLog
    exact_mod_cast hnLog.trans hnBound
  have henv := exponential_envelope_vanishes_of_log_isLittleO ε hD
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 4 * q ^ (2 * (D n / 2)) < 1 := by
    exact (tendsto_order.1 henv).2 1 zero_lt_one
  filter_upwards [hDtwo, hsmall, eventually_ge_atTop 1]
    with n hnD hnSmall hnOne
  have hrpos : 0 < D n / 2 := by omega
  refine ⟨hrpos, ?_⟩
  let x : ℝ := (n : ℝ) * q ^ (D n / 2)
  have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hq0 _)
  have hpow : q ^ (2 * (D n / 2)) = (q ^ (D n / 2)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hxsq : x ^ 2 ≤ (n : ℝ) ^ 4 * q ^ (2 * (D n / 2)) := by
    rw [hpow]
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
    calc
      x ^ 2 = (n : ℝ) ^ 2 * (q ^ (D n / 2)) ^ 2 := by
        dsimp [x]
        ring
      _ ≤ (n : ℝ) ^ 4 * (q ^ (D n / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hnreal (by omega)) (sq_nonneg _)
  change x ≤ 1
  nlinarith [sq_nonneg (x - 1)]

theorem retainedPlantCycleProbability_vanishes_of_no_short_cycles
    (ε : NoiseRate) {D : ℕ → ℕ}
    (plant : ∀ n, SimpleGraph (Fin n))
    (hD : LittleO (fun n ↦ Real.log (n : ℝ))
      (fun n ↦ (D n : ℝ)))
    (hshort : ∀ᶠ n : ℕ in atTop, ∀ l : ℕ,
      3 ≤ l → l ≤ D n →
        ¬(SimpleGraph.cycleGraph l ⊑ plant n)) :
    Vanishes fun n ↦ retainedPlantCycleProbability ε (plant n) := by
  have hgood := eventually_halfCutoff_good_of_log_isLittleO ε hD
  have hupper : ∀ᶠ n : ℕ in atTop,
      retainedPlantCycleProbability ε (plant n) ≤
        (n : ℝ) ^ 4 *
          (1 - (ε : ℝ)) ^ (2 * (D n / 2)) := by
    filter_upwards [hshort, hgood, eventually_ge_atTop 1]
      with n hnShort hnGood hnOne
    have hn : 0 < n := by omega
    have hsum := retainedPlantCycleProbability_le_checkpoint_sum
      ε (plant n) hnGood.1 (Nat.mul_div_le (D n) 2) hnShort
    exact hsum.trans (checkpoint_sum_le_exponential_envelope
      ε hn hnGood.1 (Nat.mul_div_le (D n) 2) hnGood.2)
  have hnonneg : ∀ n : ℕ,
      0 ≤ retainedPlantCycleProbability ε (plant n) := by
    intro n
    exact (retainedPlantLaw ε (plant n)).prob_nonneg _
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper
    (exponential_envelope_vanishes_of_log_isLittleO ε hD)

namespace BoundedTreewidthPlantModel

/-- **Paper Lemma 4.6 for the concrete retained plant.**

For a fixed deletion rate, `Dₙ = ω(log n)` and the concrete low-degree
norm hypothesis force the independently retained planted graph to be acyclic
with probability `1 - o(1)`.  No treewidth-scale premise is used here. -/
theorem retainedPlantCycleProbability_vanishes
    (M : BoundedTreewidthPlantModel)
    (hc_one : M.backgroundDensity ≤ 1) (ε : NoiseRate)
    (hD : Omega (fun n ↦ (M.degreeCutoff n : ℝ))
      (fun n ↦ Real.log (n : ℝ)))
    (hlow : TendsToOne M.lowDegreeNormSq) :
    Vanishes fun n ↦ retainedPlantCycleProbability ε (M.plant n) := by
  exact retainedPlantCycleProbability_vanishes_of_no_short_cycles
    ε M.plant hD (M.no_shortCycles_of_lowDegree hc_one hlow)

end BoundedTreewidthPlantModel

end PercolatedAcyclic

end

end LowDegree
