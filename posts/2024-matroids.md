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

(2) If $J \subseteq I$ and $I \in \mathcal{I}$, then $J \in ]mathcal{I}$.

(3) If $I,J \in \mathcal{I}$ and $|I| < |J|$, then there exists $e \in J \setminus I$ for which $I \cup \{e\} \in \mathcal{I}$. 

That is, the empty set is independent, the property of independence is downwards-closed, and a smaller independent set can always be 'augmented' into a large one
in a way that keeps it independent. 

The terminology 'independent' immediately suggests a model of these axioms. If $E$ is a set of vectors in a vector space $V$,
then declaring the 'independent' subsets of $E$ to be the precisely the linearly independent sets can be readily checked to 
give rise to a matroid on $E$. Such 'representable' or ('linear') matroids are what Whitney had in mind when first defining these objects.
A nice slogan is that the definition of a matroid abstracts the intuitive notion of independence just as a group abstracts the intuitive notion of symmetry. 

Matroids have close links to graph theory, and 



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
