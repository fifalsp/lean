import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

/-!
# Finite isomorphism-triple counting

This file isolates the finite combinatorial kernel used in Lemmas 4.1 and
4.2 of the paper.  It intentionally does not define graph copies or graph
isomorphisms.  Instead, a caller supplies:

* a finite type of concrete copies;
* a type of automorphisms of one abstract shape; and
* for each ordered pair of copies, a type of isomorphisms explicitly
  equivalent to that automorphism type.

The graph-specific construction of these types, and the proof that
restriction transports a graph isomorphism to compatible piece
isomorphisms, belong in graph-facing modules.  The results here only use
the finite types and recovery laws that those modules provide.
-/

namespace LowDegree

open scoped BigOperators

universe uCopy uAut uHom

/-- A family of abstract "isomorphisms" between concrete copies.

The equivalence `fiberEquiv x y` is the precise abstract replacement for
the paper's fact that the isomorphisms between any two copies of `F` are in
bijection with `Aut(F)`.  No graph structure is asserted here. -/
structure IsomorphismFamily (Copy : Type uCopy) (Aut : Type uAut) where
  Hom : Copy → Copy → Type uHom
  fiberEquiv : ∀ x y, Hom x y ≃ Aut

/-- A pair of concrete copies together with one member of the supplied
isomorphism fiber.  This is the generic finite analogue of `Tri(F)`. -/
structure IsomorphismTriple {Copy : Type uCopy} {Aut : Type uAut}
    (family : IsomorphismFamily Copy Aut) where
  source : Copy
  target : Copy
  hom : family.Hom source target

namespace IsomorphismFamily

variable {Copy : Type uCopy} {Aut : Type uAut}
variable (family : IsomorphismFamily Copy Aut)

/-- Isomorphism triples are equivalent to two independent copies and one
automorphism. -/
def tripleEquiv : IsomorphismTriple family ≃ Copy × Copy × Aut where
  toFun triple :=
    (triple.source, triple.target,
      family.fiberEquiv triple.source triple.target triple.hom)
  invFun data :=
    ⟨data.1, data.2.1,
      (family.fiberEquiv data.1 data.2.1).symm data.2.2⟩
  left_inv triple := by
    rcases triple with ⟨source, target, hom⟩
    simp
  right_inv data := by
    rcases data with ⟨source, target, aut⟩
    simp

/-- Each supplied isomorphism fiber is finite whenever the automorphism
type is finite. -/
noncomputable instance instFintypeHom [Fintype Aut] (source target : Copy) :
    Fintype (family.Hom source target) :=
  Fintype.ofEquiv Aut (family.fiberEquiv source target).symm

/-- The isomorphism-triple type is finite whenever the copy and
automorphism types are finite. -/
noncomputable instance instFintypeTriple [Fintype Copy] [Fintype Aut] :
    Fintype (IsomorphismTriple family) :=
  Fintype.ofEquiv (Copy × Copy × Aut) family.tripleEquiv.symm

/-- Every isomorphism fiber has exactly as many elements as the supplied
automorphism type. -/
theorem card_hom [Fintype Aut] (source target : Copy) :
    Fintype.card (family.Hom source target) = Fintype.card Aut :=
  Fintype.card_congr (family.fiberEquiv source target)

end IsomorphismFamily

/-- **Paper Lemma 4.1, finite kernel.**  For a generic copy type and an
isomorphism family whose fibers are equivalent to `Aut`, the number of
isomorphism triples is `|Copy|² |Aut|`.

The graph-facing specialization sets `Copy` to the concrete copies of an
abstract graph inside the plant. -/
theorem card_isomorphismTriples
    {Copy : Type uCopy} {Aut : Type uAut}
    [Fintype Copy] [Fintype Aut]
    (family : IsomorphismFamily Copy Aut) :
    Fintype.card (IsomorphismTriple family) =
      Fintype.card Copy ^ 2 * Fintype.card Aut := by
  rw [Fintype.card_congr family.tripleEquiv]
  simp [pow_two, mul_assoc]

universe uIndex uPieceCopy uPieceAut uPieceHom

/-- The dependent tuple of piece triples produced by restriction and
transport. -/
abbrev PieceTripleTuple
    {ι : Type uIndex}
    {PieceCopy : ι → Type uPieceCopy}
    {PieceAut : ι → Type uPieceAut}
    (piece : ∀ i, IsomorphismFamily (PieceCopy i) (PieceAut i)) : Type _ :=
  ∀ i, IsomorphismTriple (piece i)

/-- Abstract data for restricting a global triple to a tuple of piece
triples and recovering the original triple from every tuple in the image.

`recover` is option-valued because inconsistent tuples need not glue to a
global object.  A graph-facing module must construct `restrictTransport`
by restricting the global isomorphism to each edge piece and prove
`recover_restrict`; this file assumes no graph semantics. -/
structure RestrictionTransportFamily
    {GlobalCopy : Type uCopy} {GlobalAut : Type uAut}
    (global : IsomorphismFamily GlobalCopy GlobalAut)
    {ι : Type uIndex}
    {PieceCopy : ι → Type uPieceCopy}
    {PieceAut : ι → Type uPieceAut}
    (piece : ∀ i, IsomorphismFamily (PieceCopy i) (PieceAut i)) where
  restrictTransport :
    IsomorphismTriple global → PieceTripleTuple piece
  recover :
    PieceTripleTuple piece → Option (IsomorphismTriple global)
  recover_restrict : ∀ triple,
    recover (restrictTransport triple) = some triple

namespace RestrictionTransportFamily

variable
    {GlobalCopy : Type uCopy} {GlobalAut : Type uAut}
    {global : IsomorphismFamily GlobalCopy GlobalAut}
    {ι : Type uIndex}
    {PieceCopy : ι → Type uPieceCopy}
    {PieceAut : ι → Type uPieceAut}
    {piece : ∀ i, IsomorphismFamily (PieceCopy i) (PieceAut i)}

/-- **Paper Lemma 4.2, finite kernel.**  A restriction/transport map with
the stated recovery law is injective. -/
theorem restrictIsomorphismTriples_injective
    (data : RestrictionTransportFamily global piece) :
    Function.Injective data.restrictTransport := by
  intro left right equality
  have recovered := congrArg data.recover equality
  have some_left_eq_some_right : some left = some right := by
    simpa only [data.recover_restrict] using recovered
  exact Option.some.inj some_left_eq_some_right

/-- Cardinality consequence of the restriction/transport injection. -/
theorem card_isomorphismTriples_le_prod
    [Fintype ι]
    [Fintype GlobalCopy] [Fintype GlobalAut]
    [∀ i, Fintype (PieceCopy i)]
    [∀ i, Fintype (PieceAut i)]
    (data : RestrictionTransportFamily global piece) :
    Fintype.card (IsomorphismTriple global) ≤
      ∏ i, Fintype.card (IsomorphismTriple (piece i)) := by
  classical
  calc
    Fintype.card (IsomorphismTriple global) ≤
        Fintype.card (PieceTripleTuple piece) :=
      Fintype.card_le_of_injective data.restrictTransport
        data.restrictIsomorphismTriples_injective
    _ = ∏ i, Fintype.card (IsomorphismTriple (piece i)) :=
      Fintype.card_pi

/-- The preceding product bound with all triple cardinalities expanded.
This is the generic cardinal version of
`N_Γ(F)^2 |Aut(F)| ≤ ∏ᵢ N_Γ(Tᵢ)^2 |Aut(Tᵢ)|`. -/
theorem card_copy_sq_mul_aut_le_prod
    [Fintype ι]
    [Fintype GlobalCopy] [Fintype GlobalAut]
    [∀ i, Fintype (PieceCopy i)]
    [∀ i, Fintype (PieceAut i)]
    (data : RestrictionTransportFamily global piece) :
    Fintype.card GlobalCopy ^ 2 * Fintype.card GlobalAut ≤
      ∏ i, (Fintype.card (PieceCopy i) ^ 2 *
        Fintype.card (PieceAut i)) := by
  simpa only [card_isomorphismTriples] using
    data.card_isomorphismTriples_le_prod

end RestrictionTransportFamily

universe uGlobal uPiece

/-- A recoverable encoding of a global finite family into dependent
tuples.  In the paper's aggregate summation, `Global` can be the tagged
disjoint union of triples over every support graph `F`, while each
`Piece i` can itself be a tagged union over possible piece shapes.

This abstraction records only the recovery property.  It does not claim
that either side consists of graphs. -/
structure AggregateRestriction
    (Global : Type uGlobal)
    {ι : Type uIndex}
    (Piece : ι → Type uPiece) where
  encode : Global → ∀ i, Piece i
  recover : (∀ i, Piece i) → Option Global
  recover_encode : ∀ global, recover (encode global) = some global

namespace AggregateRestriction

variable
    {Global : Type uGlobal}
    {ι : Type uIndex}
    {Piece : ι → Type uPiece}

/-- A recoverable aggregate restriction is injective.  This is the
stronger, globally tagged injection needed when the paper sums the
pointwise Lemma 4.2 bound over all support shapes `F`. -/
theorem aggregateRestriction_injective
    (data : AggregateRestriction Global Piece) :
    Function.Injective data.encode := by
  intro left right equality
  have recovered := congrArg data.recover equality
  have some_left_eq_some_right : some left = some right := by
    simpa only [data.recover_encode] using recovered
  exact Option.some.inj some_left_eq_some_right

/-- Cardinality bound for a recoverable aggregate restriction. -/
theorem card_le_prod
    [Fintype Global] [Fintype ι] [∀ i, Fintype (Piece i)]
    (data : AggregateRestriction Global Piece) :
    Fintype.card Global ≤ ∏ i, Fintype.card (Piece i) := by
  classical
  calc
    Fintype.card Global ≤ Fintype.card (∀ i, Piece i) :=
      Fintype.card_le_of_injective data.encode
        data.aggregateRestriction_injective
    _ = ∏ i, Fintype.card (Piece i) := Fintype.card_pi

end AggregateRestriction

/-- A weighted aggregate injection bound.

If every global object's weight is at most the product of the weights of
its encoded pieces, and all piece weights are nonnegative, injectivity
allows summing over global objects and then enlarging to all tuples.  The
last equality is the finite product-of-sums identity.  This is the exact
finite-sum mechanism required by the aggregate step in the proof of
Lemma 4.5; graph-specific weights and encodings are supplied elsewhere. -/
theorem weighted_sum_le_prod_sum_of_injective
    {Global : Type uGlobal}
    {ι : Type uIndex}
    {Piece : ι → Type uPiece}
    [Fintype Global] [Fintype ι] [∀ i, Fintype (Piece i)]
    (encode : Global → ∀ i, Piece i)
    (encode_injective : Function.Injective encode)
    (globalWeight : Global → ℝ)
    (pieceWeight : ∀ i, Piece i → ℝ)
    (pieceWeight_nonneg : ∀ i piece, 0 ≤ pieceWeight i piece)
    (globalWeight_le : ∀ global,
      globalWeight global ≤ ∏ i, pieceWeight i (encode global i)) :
    ∑ global, globalWeight global ≤
      ∏ i, ∑ piece, pieceWeight i piece := by
  classical
  calc
    ∑ global, globalWeight global ≤
        ∑ global, ∏ i, pieceWeight i (encode global i) := by
      exact Finset.sum_le_sum fun global _ ↦ globalWeight_le global
    _ = ∑ encoded ∈ Finset.univ.image encode,
          ∏ i, pieceWeight i (encoded i) := by
      rw [Finset.sum_image encode_injective.injOn]
    _ ≤ ∑ encoded : (∀ i, Piece i),
          ∏ i, pieceWeight i (encoded i) := by
      exact Finset.sum_le_univ_sum_of_nonneg fun encoded ↦
        Finset.prod_nonneg fun i _ ↦ pieceWeight_nonneg i (encoded i)
    _ = ∏ i, ∑ piece, pieceWeight i piece := by
      exact (Fintype.prod_sum pieceWeight).symm

/-- The weighted inequality specialized to a recoverable aggregate
restriction. -/
theorem AggregateRestriction.weighted_sum_le_prod_sum
    {Global : Type uGlobal}
    {ι : Type uIndex}
    {Piece : ι → Type uPiece}
    [Fintype Global] [Fintype ι] [∀ i, Fintype (Piece i)]
    (data : AggregateRestriction Global Piece)
    (globalWeight : Global → ℝ)
    (pieceWeight : ∀ i, Piece i → ℝ)
    (pieceWeight_nonneg : ∀ i piece, 0 ≤ pieceWeight i piece)
    (globalWeight_le : ∀ global,
      globalWeight global ≤ ∏ i, pieceWeight i (data.encode global i)) :
    ∑ global, globalWeight global ≤
      ∏ i, ∑ piece, pieceWeight i piece :=
  weighted_sum_le_prod_sum_of_injective
    data.encode data.aggregateRestriction_injective
    globalWeight pieceWeight pieceWeight_nonneg globalWeight_le

/-- Constant-piece specialization: an injection into `m`-tuples bounds
the total weight by the `m`-th power of the one-piece total weight. -/
theorem weighted_sum_le_sum_pow_of_injective
    {Global : Type uGlobal} {Piece : Type uPiece}
    [Fintype Global] [Fintype Piece]
    (m : ℕ)
    (encode : Global → Fin m → Piece)
    (encode_injective : Function.Injective encode)
    (globalWeight : Global → ℝ)
    (pieceWeight : Piece → ℝ)
    (pieceWeight_nonneg : ∀ piece, 0 ≤ pieceWeight piece)
    (globalWeight_le : ∀ global,
      globalWeight global ≤ ∏ i, pieceWeight (encode global i)) :
    ∑ global, globalWeight global ≤
      (∑ piece, pieceWeight piece) ^ m := by
  simpa using weighted_sum_le_prod_sum_of_injective
    (ι := Fin m) (Piece := fun _ ↦ Piece)
    encode encode_injective globalWeight (fun _ ↦ pieceWeight)
    (fun _ ↦ pieceWeight_nonneg) globalWeight_le

end LowDegree
