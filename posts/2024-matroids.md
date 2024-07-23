---
author: 'Peter Nelson'
category: 'New in mathlib'
date: 2024-07-23 07:42:45+00:00
description: ''
has_math: false
link: ''
slug: matroid
tags: ''
title: Designing Matroids
type: text
---

On the design of matroids and the pattern of a structure within a type.

<!-- TEASER_END -->
# Matroids

The definition of [closure in matroids](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matroid/Closure.html#Matroid.closure) has just been merged. 
This is the latest a step in my continuing efforts to move the formalization of matroid theory in lean from [my own repo](https://github.com/apnelson1/Matroid) into mathlib.
I'm making this post to discuss a particular design pattern used for matroids in lean that goes against the grain of much of mathlib,
the design concerns that led me to this pattern, the advantages and tradeoffs it has led to, and how it has affected the definition of matroid closure.
I'd also like to discuss potential future uses for this design in graph theory. 

But first, I am aware that matroids are not exactly familiar to many of us, so I think that a brief, purely informal, introduction to matroid theory is in order! 

## The mathematics

Matroids are notorious for having many different definitions, but we only need one here. A _matroid_ is a pair $M = (E,\mathcal{I})$,
where $E$ is a finite set, and $\mathcal{I}$ is a collection of subsets of $E$ called the _independent_ sets, satisfying three axioms: 

(1) $\varnothing \in \mathcal{I}$.

(2) If $J \subseteq I$ and $I \in \mathcal{I}$, then $J \in \mathcal{I}$.

(3) If $I,J \in \mathcal{I}$ and $|I| < |J|$, then there exists $e \in J \setminus I$ for which $I \cup \{e\} \in \mathcal{I}$. 

That is, the empty set is independent, the property of independence is downwards-closed, and a smaller independent set can always be 'augmented' into a large one
in a way that keeps it independent. 

The terminology 'independent' immediately suggests a model of these axioms. If $E$ is a set of vectors in a vector space $V$,
then declaring the 'independent' subsets of $E$ to be the precisely the linearly independent sets can be readily checked to 
give rise to a matroid on $E$. Such 'representable' or ('linear') matroids are what Whitney had in mind when first defining these objects in the 1930's:
a nice slogan is that the definition of a matroid abstracts the intuitive notion of independence just as a group abstracts the intuitive notion of symmetry. 
Even though most matroids aren't linear, in practice, thinking of a matroid as simply a set of vectors gives very good intuition. 

Matroids have close links to graph theory (the $E$ notation even comes from the standard notation for the edge set of a graph), 
and have been studied by combinatorialists for years for their ability to both generalize
and give insight into theorems about graphs, especially with the minor order. More recently, matroids have seen a rise to prominence
in algebraic geometry, and were fundamental to the work cited for [June Huh's fields medal](https://www.mathunion.org/fileadmin/IMU/Prizes/Fields/2022/IMU_Fields22_Huh_citation.pdf).

(One quick remark: the original definition, and most matroids that people study have $E$ finite, 
but one can generalize the definition to allow for infinite $E$, at the expense of making the definition a little more complicated to avoid mention of set cardinality. 
We do do this in mathlib, but the added complexity is orthogonal to everything I'll discuss here, so just pretend all matroids are finite for today). 

**Minors**

The main culprit behind the thorny design issue we will encounter is the standard notion of a substructure in matroid theory - a *minor*. 
If $M = (E, \mathcal{I})$ is a matroid, and $X \subseteq E$, then we can remove the elements of $X$ from $E$
in two distinct ways. 

The first is the easy one: the *deletion* $M \backslash X$ of $X$ in $M$ is just the
matroid $(E \setminus X, \mathcal{I}')$, where $\mathcal{I}' = \mathcal{I} \cap 2^X$. This is trivially still a matroid.

The other way we can remove $X$ is by *contracting* it. The contraction $M / X$ is a certain matroid $(E \setminus X, \mathcal{I}')$, 
which in the linear case corresponds to applying to $E \ X$ the quotient map whose kernel is the span of $X$. 
Writing down the definition of $\mathcal{I}'$ in the abstract, and showing that it satisfies the matroid axioms,
is a little fiddly but quite doable - I'll leave it to the motivated reader.

The important thing is that contraction and deletion are two different ways to remove $X$ from a matroid.
A matroid obtained from $M$ by some combination of contraction and deletions is called a *minor* of $M$.
So if $C_1, C_2, D_1, D_2$ are pairwise-disjoint subsets of $E$, 
then $M' = (((M / C_1) \setminus D_1) / C_2) \setminus D_2$ is an example of a minor of $M$.
But we don't need all the parentheses; it turns out that contraction/deletion commute in the sense that
we also have $M' = M / (C_1 \cup C_2) \setminus (D_1 \cup D_2)$, and thus every minor has the form $M / C \setminus D$
for disjoint $C, D \subseteq E$. 

Partly because matroid theorists are induction-loving combinatorialists, it is very common to contract and delete single elements.
To this end, we abbreviate $M / {e}$ by $M / e$, and do the same for deletion. 
It's also partly for this reason that it's so common to think about deletion rather than
the equivalent notion of the 'restriction of $M$ to $R$' defined by $M | R = M \setminus (E \setminus R)$. 
We are removing a screw from the engine, rather than considering the set of everything in the engine that's not the screw. 

There are two important points here from a formalization perspective. The first is that,
if $N = (E', \mathcal{I}')$ is a minor of $M = (E, \mathcal{I})$, then $N$ is not determined by
just by $M$ and $E'$. For instance, we could have got to $N$ by either contracting $E \setminus E'$ or deleting $E \setminus E'$, 
and those operations would give different $N$. This makes the notion of a minor quite unlike a subgroup/module/graph. 

The second is that the aforementioned fact that $(((M / C_1) \setminus D_1) / C_2) \setminus D_2 = M / (C_1 \cup C_2) \setminus (D_1 \cup D_2)$ 
is a perfect example of a statement that is hard to formalize. In a type theory framework, we will pay dearly for that $=$ sign. 

## A minor problem

It is clear enough how one can crib from existing mathlib designs to come up with an idiomatic definition of `Matroid` in lean, 
as follows (again, don't worry about the finiteness thing): 

```
structure Matroid (E : Type*) where
  Indep : Set E → Prop
  indep_mono : ∀ I J, Indep J → I ⊆ J → Indep I
  [...],
```

where the remainder of fields are also propositional.

For a lot of things, this worked great. Back in the lean 3 days, I used something like this as my definition, and got fairly far.
But there was a sticking point: it was very difficult to work with minors. If `M : Matroid E` and `X : Set E`,
it is easy enough to define `M.delete X : Matroid (Xᶜ)` and `M.contract X : Matroid Xᶜ`, but this isn't the point. 

Think about a simple statement like $(M \setminus D) / C = (M / C) \setminus D$.
This is easy to prove with set theory, but type-theoretically, it's very hard to even state in terms of the definition above in a way that typechecks;
the LHS has type `Matroid E₁` for a certain subtype `E₁` of `Dᶜ`, and the RHS has type `Matroid E₂` for a subtype `E₂` of `Cᶜ`.
There is of course a canonical isomorphism between thes types, but this is cold comfort if we want to
state and formalize $(((M / C_1) \setminus D_1) / C_2) \setminus D_2 = M / (C_1 \cup C_2) \setminus (D_1 \cup D_2)$ instead. 
That last equality is not contrived, either; it's literally the content of the crucial statement 
'we never care about the order of deletions and contractions', which anyone doing research in matroid theory has internalized. 
I feel fairly strongly that no workable formalization of matroids can settle for anything less than `Eq` for that $=$, either. 
An isomorphism or `heq`-like notion would make big parts of mathlib inaccessible to anyone working with minors of matroids.

To solve this issue, the next port of call in standard mathlib design is the `Submodule`/`Subgraph`-pattern. For `M : Matroid E`, we would define 

```
structure Matroid.Minor {E : Type} (M : Matroid E) where
  carrier : Set E
  contractSet : Set E
  deleteSet : Set E
  [..]
```

where the rest is propositional; for instance, it would be enough to assert that `contractSet`, `deleteSet` and `carrier` form a partition of `univ`. 
The fact that minors are themselves matroids would be encoded via a function `minor.toMatroid (M : Matroid E) (N : M.Minor) : Matroid ↑(N.carrier)` 
with all the API linking the two, such as a predicate `Minor.Indep {M : Matroid E} (N : M.Minor) : Set E → Prop` such that `Matroid.Indep` 
and `Minor.Indep` have the right mathematical relationship. 

We can't use `toMatroid` to formalize the statement of $(M \setminus D) / C = (M / C) \setminus D$ with equality, because things still wouldn't typecheck.
But we can do something if we define `Matroid.Minor.contract {M : Matroid E} (N : M.Minor) (C : Set E) : M.Minor` and `Matroid.Minor.delete` analogously. 
Then the statement `Minor.contract (Matroid.delete M D) C = Minor.delete (Matroid.contract M C) D` typechecks just fine, 
with both sides having type `Matroid.Minor M`. It's also easy enough to prove, though we probably need disjointness assumptions.

So we can use `rw` to change `(M / C) \ D` to `(M \ D) / C`. That's great! 
Once I had this working, I was gung ho about proving theorems about minors. 
And that opens lots of doors - probably well over half the literature on matroids uses the theory of minors, and now it was available to formalize. 
My repo had a subfolder `Minor` which grew fast. In fact, it turned out for many purposes, it was more important to have a theorem formalized
as a statement about `N : Minor M` for some fixed `M` that in was to have a theorem about `M : Matroid E` itself.
Statements were usually just as nice, and proofs went much more smoothly. 
The common idiom 'contract an element, and apply the induction hypothesis to the resulting minor' became straightforward,
rather than a matter of wrestling with `Fintype.card`. 
It became slowly apparent that the `Matroid.Minor` namespace was the natural home for so many proofs, that I started neglecting the original namespace. 
It was easy enough to go between statements in one world and statements in the other, 
but it was duplication that doubled the size of the API - why do this? 

The salient point, which was creeping up on me crystallized in a conversation in Banff I had last year with Johan Commelin.
When I asked him for advice on the matter, his question was why `Matroid` existed in the first place, rather than just `Minor`.
I realized I didn't have a good answer. 

## Embedded ground sets

Taking the above process to its logical conclusion, one asks what you get if you do everything only for `Minor`.
And it becomes clear that the 'host' matroid `M` in `Minor M` isn't what's important. What makes `Minor` nice is that 
you can contract and delete elements and stay in the same type, and that you can do set theory with ground sets. 
(I haven't really touched on this, but it's not at all unusual in real-world proofs to make statements like 
$E_N \cup {f} \subseteq E_M \setminus X$ for matroids $M$ and $N$; this becomes horrible to formalize quickly if
the ground sets of $M$ and $N$ are types, but is easy if they are common minors of some larger matroid). 

What you need for these two things is that you have a `carrier`-like field, and contract/delete operations
whose domain and codomain are the same. This suggests the following definition, which is a simplified version
of what appears in mathlib. 

```
structure (α : Type) : Matroid α where
  carrier : Set α
  Indep : Set α → Prop
  [..]
  support : ∀ I, Indep I → I ⊆ carrier
```

again, the `[..]` hides propositional/mathematical stuff that makes `Indep` actually encode a matroid.
Then `Matroid.contract (M : Matroid α) (C : Set α) : Matroid α` makes perfect sense to define, and 
`(M.contract C).delete D = (M.delete D).contract C` typechecks and proves just fine, with no `Minor`-like type involved.

In fact, this is much more versatile than the `Minor` type. It allows two distinct matroids to be manipulated
as peers, even if they aren't common minors of such larger matroid. This is a less common use case, but it does occur.
The title of this section - 'embedded ground sets', refers to this particular design pattern, where the ground set
of a matroid is formalized as a carrier set embedded within a type, rather than a type itself. 

The `support` axiom is to ensure that all the fun in the matroid is happening *within* the ground set;
there are no junk independent sets containing nonelements of the matroid. 

As a side note, it might seem plausible that the `carrier` field is unneccessary and can be reconstructed
just from the information in `Indep`, but sadly this isn't the case.
Matroids can have elements that are in no independent set: 
these elements, called 'loops', have mathematical significance as a part of the matroid,
and cannot be safely ignored. 

**Tradeoffs**

The embedded ground set pattern isn't all wine and roses. The way I see it, there are two main tradeoffs : 

First, we suddenly have to care in many theorem hypotheses about whether a set is actually supported.
In practice, hypotheses of the form `X ⊆ M.carrier` are by far the most common in my repo, 
and are always there because dropping them allows for trivial counterexamples.
Of course, proving that `X ⊆ M.carrier` is often very easy. For instance, if `M.Indep X` holds,
then `support` implies `X ⊆ M.carrier`. In fact, we have an `aesop_mat` tactic whose only
job is to prove goals of the form `X ⊆ M.carrier` in an `autoparam`. For instance, if 
`M.Indep X` and `M.Indep Y`, then `aesop_mat` will be able to prove that `M.Indep (X ∪ Y)`.
I see this as being conceptually similar to `positivity`/`continuity`. 

Second, in some places we lose seamless compatibility with the utopia of type theory and functional
programming. One place things get a little ugly is in the API for 
[maps between matroids](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matroid/Map.html#Matroid.map). 
Mathematically, this is all the standard boilerplate you see everywhere, and the details aren't so important: 
if I have a matroid on one type, I can move it to another type using an injective function. 
But now I have to throw set theory into the mix. If I have a matroid `M` with carrier set `E : Set α`,
then I could reasonably ask to transfer `M` to another type using a function `f` with domain `α`,
or just as reasonably with a function whose domain is the subtype `↑E`. Similar things go
for codomain. So `Matroid/Matroid/Map` ends up definining at least four ways to move matroids
between types, all with the same nearly trivial mathematical content, differing only in whether (co)domains are
types or subtypes. Whenever functions are involved, the embedded ground set will rear its ugly head in this kind of way.
(Another example is the recent mathlib definition of a function `Matroid.closure : Set α -> Set α` which
needs to be defined in a way that handles junk elements; there are two potential ways to do this,
and both come with drawbacks). 

The first tradeoff certainly isn't ideal. Using automation to discharge trivial goals is easy enough
(and will improve as things like `aesop` grow more powerful), but what is also annoying
is giving any nonzero thought to whether 'non-junk' assumptions are actually needed for a given theorem, 
and writing proofs in a way that handle junk elements as invisibly as possible. My working intuition for
matroids serves me reasonably well here, but I'd rather it weren't neccessary. 

There isn't much of a silver lining with this second tradeoff - it is a genuine difficulty,
and I don't think there is much that can be done with the current design. 
If we were working with an objects in the algebraic heirarchy rather than a matroid,
this would be a deal-breaker. You can't have algebra without structure-preserving maps.

I think though, that in a similar way, you can't have combinatorics without set theory.
It's for this reason that I'm willing to put up with maps being awkward. Functions between matroids
will crop up in a text on matroids, but somewhere in the middle. 
They aren't fundamental to the subject. 
What is fundamental is the fact that two minors obtained in different ways are still objects 
of exactly the same type, and have ground sets and independence predicates that can be seamlessly
manipulated and compared without composing with 'invisible' functions. 

(Said invisible functions, such as subtype coercion, are especially bad to handle for matroid theory,
since they usually take the form of set images and preimages rather than just function application).

What I really hope, though, is to have my cake and eat it too. I hope that there is a better design that allows
the ground set of a matroid to be ambient and boundaryless, and at the same time allows pairs of different matroids
to be manipulated without coercions and images functions blowing up every term. 

## Graph Theory

If I have a graph $G = (V,E)$ and an edge $e \in E$, I can identify the endpoints of $e$ in $G$ to get
a new graph $H = G / e$. This is called 'contracting' the edge. 

This definition is intuitively clear enough if one thinks of a graph topologically, 
but is fraught from a formal perspective. Can a graph have loops at a vertex or multiple 'parallel' edges between a pair of vertices?
What happens if $e$ is a loop? Exactly what type of object is the identified vertex?
If the two ends of $e$ have edges $f,f'$ to a common neighbour $x$, does $f, f'$ become a parallel pair of edges?

These questions have multiple valid answers that give different formalisms.
Suppose that we settle on allowing $G$ to be a 'multigraph', possibly having loops and parallel edges. 
A graph obtained from a subgraph of $G$ via a sequence of edge-contractions is a 'minor' of $G$.
(The common terminology with matroid minors is not a coincidence; the connection between them can be made precise 
via a standard construction that produces a matroid from a graph.)
The minor order on graphs has been extensively studied for over a century. 
A seminal [result due to Wagner/Kuratowksi](https://en.wikipedia.org/wiki/Wagner%27s_theorem) characterizes which graphs
can be drawn in the plane in terms of two particular forbidden minors,
and [Robertson and Seymour's graph minors structure theorem](https://en.wikipedia.org/wiki/Graph_structure_theorem)
is widely viewed as the deepest and most influential theorem in graph theory. 

Minors, and indeed non-simple graphs, are nowhere to be seen in mathlib.











