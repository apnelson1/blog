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

Matroids have close links to graph theory, and have been studied by combinatorialists for years for their ability to both generalize
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
But we don't need all the brackets; it turns out that contraction/deletion commute in the sense that
we also have $M' = M / (C_1 \cup C_2) \setminus (D_1 \cup D_2)$, and thus every minor has the form $M / C \setminus D$
for disjoint $C, D \subseteq E$. 

There are two important points here from a formalization perspective. The first is that,
if $N = (E', \mathcal{I}')$ is a minor of $M = (E, \mathcal{I})$, then $N$ is not determined by
just by $M$ and $E'$. For instance, we could have got to $N$ by either contracting $E \setminus E'$ or deleting $E \setminus E'$, 
and those operations would give different $N$. This makes the notion of a minor quite unlike a subgroup/module/graph. 

The second is that the aforementioned fact that $(((M / C_1) \setminus D_1) / C_2) \setminus D_2 = M / (C_1 \cup C_2) \setminus (D_1 \cup D_2)$ 
is a perfect example of a statement that is hard to formalize. In a type theory framework, we will pay dearly for that $=$ sign. 

**Closure** 

We need one more thing, mathematically. If $M = (E, \mathcal{I})$ is a matroid and $I \in \mathcal{I}$,
then the *closure* of $I$ in $M$ is the set $\mathrm{cl}_M(I)$ of all $e \in E$ such that either $e \in I$ or $I \cup \{e\} \notin \mathcal{I}$.
If the matroid is linear, then $\mathrm{cl}_M(I)$ is simply the intersection of $E$ with the linear span of $I$.
In this spirit, we can define $\mathrm{cl}_M(X)$ even in $X \not\subseteq I$, but I omit the definition here.

Closure lives up to its name in that it is idempotent, inflationary and monotone; 
that is, we have $\mathrm{cl}_M(\mathrm{cl}_M(X)) = $\mathrm{cl}_M(X)$ and 
$X \subseteq \mathrm{cl}_M(X) \subseteq \mathrm{cl}_M(Y)$ for all $X \subseteq Y \subseteq E$.







**Matroid Design**

In formalizing matroids, one's first instinct is probably to define a matroid as a structure (or class) `Matroid α` consisting of a predicate `Indep : Set α → Prop`, with appropriate rules constraining the behaviour of `Indep`. This mimics the design of objects in the algebraic hierarchy. Doing this would make `Matroid.closure` an example of a `ClosureOperator (Set α)`, and give access to a lot of nice API for these objects, such as Galois insertions. 

Unfortunately, this design has huge drawbacks to do with the way matroids are used. Unlike algebraic objects, the ground set $$E$$ of a matroid is really treated like a set. A matroid on a set $$E$$ gives rise to many related matroids (minors) on subsets of $$E$$ in different and nonisomorphic ways, and it is not unusual to consider multiple matroids on the same set $$E$$, or to make assertions about, say, the interection of the ground sets of two different matroids.  Modelling the ground set of a matroid with a type (let alone using typeclasses) is a complete non-starter for this - even very basic theorems about minors of matroids having statements that include an `=` sign become horrible piles of canonical isomorphisms, which are paralyzing in practice. 

I know this because I tried doing things this way for a long time, before @**Johan Commelin** suggested the current design to me. It works as follows: For `α : Type*`,  a `Matroid α` consists of a set `E : Set α`, and a predicate `Indep : Set α → Prop`, satisfying certain axioms that define a matroid, together with an extra rule `h_support : `∀ I, Indep I → I ⊆ E`. In other words, the ground set of a matroid is not a type, but a set within a type, and the independence predicate is defined on all sets in the type, and happens to only hold for subsets of `E`. 

This may seem unwieldy. The real disadvantage is that it sometimes requires unmathematical bookkeeping to make sure that sets are contained in the ground set. The hypothesis `X ⊆ M.E` appears all over the API, where it would have been simply true by definition if the ground set were a type. The advantage is that it allows meaningful assertions that two matroids are `Eq`. 

It's not that the disadvantage isn't bad (it is certainly quite annoying to constantly have to care about sets being 'supported'), but it's that one can't do basic matroid theory in any other way that I know. The 1000 or so lines of API in [the basic file on minors in my matroid repo](https://github.com/apnelson1/Matroid/blob/main/Matroid/Minor/Basic.lean) would be complete DTT hell if ground sets were types, and it's only the very beginning of the theory. Typical proofs involve multiple `rw`s involving lemmas like the following : 
``
  lemma contract_cl_eq_contract_delete (M : Matroid α) (C : Set α) :
    M ／ M.cl C = M ／ C ＼ (M.cl C \ C)`M ／ M.cl C = M ／ C ＼ (M.cl C \ C)
``
If that `=` isn't really formalized as `Eq`, such proofs become effectively impossible. 

So as far as I know, there is no other option than to suck it up, to keep track of sets being contained in the ground set, and to devote mental energy to the junk elements outside the ground set when stating lemmas. One thing that helps is the tactic `aesop_mat`, which works pretty well to automatically discharge goals of the form `X ⊆ M.E` when this follows from things in the context. 

**Closure**

There are many other natural predicates on sets in a matroid; a set $$X \subseteq E$$ may be a 'circuit', 'base', 'basis', 'flat', 'cocircuit', ... of $$M$$, and mostly they follow a similar design to `Indep`. For instance, we have a predicate `Base : Set α → Prop` which is defined in such a way that `Base B → B ⊆ M.E` is a theorem; bases of a matroid only exist as subsets of its ground set. Formalizing closure is different, though. Since `cl : 2^E \to 2^E`, we need to formalize it s `Matroid.closure : Set α → Set α`, so we are forced to say where the junk goes. That is, if `X` is not a subset of `M.E`, then how should `M.closure X` be defined? 

There are quite a few potential choices. For instance, we could declare that `M.closure X = ∅` whenever `X` isn't a subset of `M.E`. This choice would be bad, though, since it necessitates adding a lot of support assumption to theorems about closure; we would need to know that `Y ⊆ M.E` for `X ⊆ Y` to imply `M.closure X ⊆ M.closure Y`, so `M.closure` would fail to be monotone. 

After discarding the chaff like the above, there are two reasonable choices that remain. Suppose that `M.closure X` has been defined as the mathematics dictates for every subset `X` of `M.E`.  When `X` is not a subset of `M.E`, we can either

(1) : Define `M.closure X` so that `M.closure X = M.closure (X ∩ M.E)`, or 
(2) : Define `M.closure X = M.closure (X ∩ M.E) ∪ X`. 

And this choice is why I'm making this post. Originally my repo used (1), and the PR initially did. But Johan suggested (2) for the PR, giving some quite good arguments for it. 
I gave it some thought, and it's a hard choice! Both (1) and (2) are good and bad for different reasons, and it felt very annoying to be forced to settle on one or the other. 
I'll summarize the points here. 

(1) is nice for two reasons. First, it guarantees that `M.closure X ⊆ M.E` for all `X`, even when `X` contains junk outside the ground set. This is great for `aesop_mat`; in general knowing that things are contained in the ground set is very useful, since it's needed so often as an assumption. The second reason is that when proving something about `M.closure X` with no assumptions on `X`, one can quickly `rw` the term to `M.closure (X ∩ M.E)`, and obtain a statement that is only about subsets of ground set (i.e. sets which are mathematically meaningful in the context of this matroid). This reduces cognitive load; thinking about junk elements is unmathematical and annoying. 

(2) is nice for reasons that probably appear more attractive. The statement that `M.closure X ⊆ M.E` is no longer unconditionally true (it needs `X ⊆ M.E`), but the statement that `X ⊆ M.closure X` *is* unconditionally true. This turns out to imply that `Matroid.closure` is actually an example of docs#ClosureOperator. This opens up access to a lot of nice API, giving a `GaloisInsertion`, for example. A side benefit is that a function satisfying (2) is actually the closure function of a different matroid with ground set `univ`, which can simplify proofs in a few places. 

So I made a branch of my repo, and refactored the whole thing so that `closure` was defined as `ClosureOperator`, satisfying (2). This affected countless lemmas across dozens of files, and it was a few days work adding/removing 'non-junk' assumptions before I had (2) working almost everywhere.

It was a close thing, but the slightly less mathematically principled and more hacky solution won out: I decided that (1) was better. The nice API was tempting, reduced duplication a little and was in some places useful, but having access to `M.closure X ⊆ M.E` and being able to easily `rw` away junk elements was too much to give up. A common idiom with (2) was having a term `M.closure X` with no assumptions on `X`, then rewriting it to `M.closure (X ∩ M.E) ∪ (X \ M.E)` to separate the non-junk and junk parts of the term. But this expression still contains the unmathematical junk `X \ M.E`; any time and keystrokes spent dealing with those elements is a waste and arguably a failure of the design. And of course the term `M.closure (X ∩ M.E) ∪ (X \ M.E)` itself is horrible, especially if `X` itself is a complicated expression. Losing the API was difficult, but in fact it was still available in a different guise. With (1), we do still get a `ClosureOperator` on the subtype `{X // X ⊆ M.E}`, through which the API lemmas can be (a little clunkily) transferred from the subtype to the type. 

**Conclusion** 

I don't know what the lesson is here, but it is clear that the 'embedded ground set' design was consequential. It forced me to decide between (1) and (2), and it would have been really nice to have the advantages of both. If the ground set were a type, we could have had both (1) and (2), but we would then be unable to assert that two different-looking matroids are `Eq`, which is central enough to the combinatorial theory that it is a deal-breaker. 

This isn't the only time that embedded ground sets have caused me pain. Whenever functions in and out of matroids crop up, they make things a little more difficult. The material in Docs#Data.Matroid.Map is forced to consider many different flavours of maps between matroids involving subtypes of subsets, and this is because ground sets are not types. When formalizing the heavily studied subject of linear representations of a matroid, you need to consider functions `f : M.E → W` for a vector space `W`; this would be much easier if the domain were a plain type rather than a coerced set. 

But none of this pain is as bad as the alternative: being unable to consider different matroids on related ground sets as terms in a common type.

So going forward, I'm putting up with the pain, using subtypes once functions get involved, and using automation tactics like `aesop_mat` with autoparams to minimize manually keeping track of `X ⊆ M.E` proofs. (by the way, I hacked `aesop_mat` together a year ago and it's doing something quite simple not particularly quickly; anyone that knows how to speed up specialized `aesop`-like tactics that would be willing to have a look with me would have my gratitude!) Maybe there is a good design I'm unaware of that would make my life much easier, and maybe HOTT has something to offer. But in the meantime I think this is what matroid theory looks like in lean.  
