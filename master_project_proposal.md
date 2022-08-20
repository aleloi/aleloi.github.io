# Automating formal theorem proving with AI and ML
Possible other titles: Something along the lines of "Generating proof
terms in dependent type theory with Machine Learning". Or "Automating
formalized proof steps with ML".

## Project proposal
Should contain:
* This is a (vague and broad) project proposal
* Target audience are potential academic supervisors at KTH that are experts
  in verification methods or machine learning (I'd like one that works
  in both, but guess that it is unrealistic).
* TLDR: 
	* I want to work on automatic theorem proving with AI / ML. 
	* I have read up on published papers on ML methods for automation
      for the proof assistant Coq, and more broadly about Coq
      automation in general.
    * I have done a [[smallish Coq project]](#friendship) (2000
      loc, a bit over 2 weeks of work from start to `Qed` not
      including time spent learning the system) that formalized a
      theorem and tried existing automation methods on it.
    * The current automation methods mostly did not help in my case;
      what helped most was `sauto` and basic rewriting databases with
      `simpl`.

## Intro to formal verification
Formalized theorem proving or /formal verification/ is when a
mathematical proof is written in a specific format where each step can
be checked by a computer [[LeanIntro]](#leanintro). Proof steps could
be axioms or the application of a previously proved results. When high
confidence in the truth of a logical statement is desired, and a
"normal" human written proof is for some reason not enough, one can
employ formal verification methods. Examples include verifying that
cryptographic algoritms are secure [[CertiCript]](#certicript),
[[CryptoSE]](https://crypto.stackexchange.com/a/34326), blockchain contracts
[[Nielsen19]](#nielsen19) or that a digital hardware circuit performs according
to its specification [Braibant 2013]. Generally, when cost of bugs is
high, and a pen-and-paper human written proof is difficult to produce
or verify, formal verification methods can reduce expected costs [Kern
99 survey, sec 1; TODO not what article says]

A different motivation for the need of formal verification is that
even the field of Mathematics is undergoing what has been called a
replication crisis [replication crisis paper]. Published proofs often
have gaps, and are shown to sometimes be false
[https://www.andrew.cmu.edu/user/avigad/meetings/fomm2020/slides/fomm_buzzard.pdf]. [replication
crisis paper], [https://www.nature.com/articles/d41586-020-00998-2]
and [https://www.math.columbia.edu/~woit/wordpress/?p=12220] describe
the case of Shinichi Mochizuki that has published what he claims is a
proof of the abc conjecture
[https://en.wikipedia.org/wiki/Abc_conjecture]. Leading matematicians
claim to have found a hole in the proof, while Mochizuki claims that
they have misunderstood it. [replication crisis paper] describes the
situation as 

> [...] we end up now with the absurd situation that abc is a theorem
> in Japan while still an open conjecture in Germany.

[https://www.andrew.cmu.edu/user/avigad/meetings/fomm2020/slides/fomm_buzzard.pdf]
has examples of famous proofs which still have unfilled gaps including
Fermats Last theorem by Wiles, and the classification of finite simple
groups

Even though many logical statements have been formalized, developing
formal proofs is time consuming and tedious [Hammer paper, page 2, introduction]. Since [19?0s; ref] research has been done
on automating parts of this process.

An ambitious long-term vision that I would like to contribute to is a
system that reads human written mathematical text, automatically
translates theorem and lemma formulations into computer-readable form,
and attempts to also translate the proofs. [I think I saw this in a
quora post]. Google is rumored to be working on a system like this [https://www.andrew.cmu.edu/user/avigad/meetings/fomm2020/slides/fomm_buzzard.pdf, Markus Rabe, Kevin Buzzard page 24].

### Intro
Should cover:
* why formalized math is important (smart contracts / mad Japanese
  mathematician / replication crisis in math / bugs in software)
* that much of it is tedious (cite CoqHammer and Tactician; find
  something more to cite; link to case study / example section)
* the "vision" - system reads math article, extracts claims and
  definitions in formalized form and PROVES implication steps *by
  itself*.

## Formalized mathematics
*What's the point of this section? Originally to motivate the choice
of Coq before Lean and the HOL systems, but that's not its content.*

Formal verification systems are not based on the Zermelo-Frankel+Choice (ZFC)
axiom system that has been accepted to be a foundation of
mathematics. ZFC has a short number of axioms (about 10, [TODO source: Freddie's logic textbook alt Napkin, but napkin has mistakes...]),
with statements like "there exists an empty set", "two sets are equal if their elements are equal", "given two sets, there is a set that is their union that contains elements of each and nothing else". 

[Brujin 95] explains why there are better choices than ZFC: ZF is a theory of
untyped sets, but humans working with formal verifications think in
categories which are called types. To me, adding types on top of ZF
seems much harder than starting with a system that has types as
primitive concepts. A proof assistant should let users reason about
e.g. sets of functions or sets of group objects. [Brujin 95] has this
example on the lack of types in ZFC:

> Theoretically, it seems to be perfectly legitimate to ask whether
> the union of the cosine function and the number e (the basis on
> natural logarithms) contains a finite geometry.
	 
Typed systems forbid asking questions like this. [Note: Coq is
powerful enough to define Von Neumann sets and define an encoding of
the cosine function and the number $$e$$ as sets. Type theory does
not strictly /forbid/ asking this question; it just requires repeating
the construction of real analysis and (a few layers of) the Von
Neumann universe on top of Coq types. Ref: [SetTypeTypeSet]]

Popular formal verification systems use some form of typed lambda
calculi [Hales 2008]. I am only familiar with Martin-Löf Dependent
Type Theory as it is used in the Coq and Lean proof assistants [TODO
link].

### Isn't HOL/Isabelle easier?
I know only Coq/Lean because that is what I learned in type theory
class and then worked on independently. It seems that HOL-based
systems (HOL-light, Isabelle) have more difficult theorems formalized
[e.g. 100 theorems, https://www.cs.ru.nl/~freek/100/]. 
Unsanswered questions (by me):
* is the state of automation in HOL / Isabelle better than Coq / Lean?
* would it be considerably easier to formalize a reasonably complex
  (100 pages of proof) theorem in HOL / Isabelle rather than Coq /
  Lean?
* is there a logic difference in between HOL and Coq logic (CIC). That
  is: is there a theorem that cannot be stated or proven in one but
  can in the other?
	* I think I know the answer to this: NO, both are similarly
      powerful. https://www.isa-afp.org/entries/ZFC_in_HOL.html is a
      construction of ZFC in HOL; and [SetTypeTypeSet] shows that Coq
      can encode ZFC with infinitely many inacessible ordinals.

### Coq example
The example below shows a proof of $$(\exists (a\in A): \neg B(a)) \Rightarrow \neg (\forall (a\in A): B(a))$$ in the Coq system.

```coq
Lemma exists_impl_forall (A: Type) (B: A -> Prop) :
  {a: A & ~(B a)} -> ~(forall a: A, B a).
Proof.
  (* first proof; full proof term *)
  exact (fun anBa allB => let (a, nBa) := anBa in nBa (allB a)).
  
  (* second proof; automated *)
  Restart.
  firstorder.

  (* third proof; using interactive proof management *)
  Restart.
  intros anBa allB.
  destruct anBa as [a nBa].
  apply nBa.
  apply allB.

  (* fourth proof; a mix *)
  Restart.
  intros anBa allB.
  exact (match anBa with
         | existT _ a nBa => (nBa (allB a))
         end).
Qed.
```

In Coq (and in Martin-Löf Type Theory in general), every logical
statement $$P$$ can be converted to a type $$T(P)$$ though the
[Curry-Howard
correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence). A
proof of the logical statement $$P$$ is a lambda calculus term whose
type is $$T(P)$$.  To prove $$P$$, one can either explicitly type the
proof term and have the type checker of the system accept is type as
$$T(P)$$, or construct it interactively though a higher level proof
language.

The example above shows 4 ways to prove the implication with $$\exists$$
and $$\forall$$. The first constructs the full proof term `fun anBa allB
=> let (a, nBa) := anBa in nBa (allB a)`. The second instructs Coq to
automatically construct the proof term with `firstorder` that only
works for some proofs. The third example shows the commands of the
*tactic language*.  The fourth is a mix between constructing proof
terms and using proof tactics.

### Formalized maths
* There is DT-TT and HOL; link to ACM survey article. Can be viewed as
  alternative axiomatic systems for foundation of Mathematics compared
  to ZF+Choice. [Need to talk to a logician!] More suited for
  computer-formalized maths because of the structure [TODO: explain
  this to others and myself: ZFC+Choice only talks about sets, sets of
  sets, sets of sets of sets ... There is no structure; one can take
  the union of the function *sin* and the number 2 and ask whether the
  result has a particular topology (survey article)]
* Why is DT-TT and not HOL: I *think* that DT-TT is more
  powerful. Should look it up. Practically, I learned Coq in type
  theory class. In a choice between Coq and Lean I chose Coq because
  it seemed to have a more active community, more published articles.
  [TODO: read about DT-TT vs HOL vs 'normal' math axioms.]
  

## Case study, Friendship Theorem and automation
The Friendship theorem states that in a party of n persons, if every
pair of persons has exactly one common friend, then there is someone
in the party who is everyone else's friend
[[Friendship72]](#friendship72). Frendship is assumed to be
irreflexive (no one is a friend of themselves) and symmetric (if `x`
is friends with `y`, then `y` is friends with `x`). `n` has to be
finite and nonzero. A Coq formulation of this theorem is

```coq
Theorem Friendship
  (T: finType) (T_nonempty: [set: T] != set0)
  (F : rel T) (Fsym: symmetric F) (Firr: irreflexive F) :
  (forall (u v: T), u != v -> #|[set w | F u w  &  F v w]| == 1) ->
  {u : T | forall v : T, u != v -> F u v}.
```

I formalized the proof in [[BookProof]](#FriendshipBook) which is
claimed to be identical to the first published proof by Erdös et. al.
[[ErdosProof]](#ErdosProof). The proof goes as follows:
* Assume that there is *no* person that knows all others. [[link]](https://aleloi.github.io/coq-friendship-theorem/coqdoc/Friendship.combinatorics.html#no_hub':56)
* Under the assumption, the friendship graph is
  *k*-regular. [[link]](https://aleloi.github.io/coq-friendship-theorem/coqdoc/Friendship.combinatorics.html#regular)
* Under the assumption, $$n=k^2-k+1$$. [[link]](https://aleloi.github.io/coq-friendship-theorem/coqdoc/Friendship.combinatorics.html#nk)
* Under the assumption, $$A^2 = \mathbb{1}\mathbb{1}^\intercal + (k-1)I$$ and $$\operatorname{tr} A = 0$$ where $$A$$ is the $$n\times n$$ adjacency matrix of the graph. [[link]](https://aleloi.github.io/coq-friendship-theorem/coqdoc/Friendship.combinatorics.html#adj2_eq)
*  $$A^2 = \mathbb{1}\mathbb{1}^\intercal + (k-1)I$$,  $$\operatorname{tr} A = 0$$, $$k\in \mathbb{N}$$, $$n=k^2-k+1$$ implies $$(k-1)| k^2$$ by linear algebra. [[link]](https://aleloi.github.io/coq-friendship-theorem/coqdoc/Friendship.divisibility.html#tr_adj_rel_nat)
* $$k\in \mathbb{N}, (k-1)| k^2$$ implies $$k=2$$. [[link]](https://aleloi.github.io/coq-friendship-theorem/coqdoc/Friendship.divisibility.html#k_is_2)
* $$k=2$$, $$n=k^2-k+1$$ and a $$k$$-regular graph contradict the assumption that no person knows all others. [[link]](https://aleloi.github.io/coq-friendship-theorem/coqdoc/Friendship.combinatorics.html#fls)

A good example of a non-automated proof is [`Lemma
k_not_2`](https://aleloi.github.io/coq-friendship-theorem/coqdoc/Friendship.combinatorics.html#k_not_2),
which shows the level of detail required for a basic combinatorial
proof. The lemma states that whenever the friendship graph contains no
person is a friend of all others, and and is $$k$$-regular with
$$n=k^2-k+1$$, then $$k\neq 2$$. A human written proof would be to assume
$$k=2$$ for contradiction, compute $$n=2^2-2+1=3$$, take any person and
observe that the person together with its two friends form the full
graph, so the person is a friend of all others which is a
contradiction. The linked Coq proof starts with a comment that
restates the proof in much more detail, and then proves the lemma
interspersed with lines of the human-written proof from the top.

### Automation
There are several automation systems for simplifying the process of
writing Coq proofs. [[Czaika18]](#czajka18) argues the case for more automation:

> Interactive Theorem Proving (ITP) systems [44] become more important
> in certifying mathematical proofs and properties of software and
> hardware. A large part of the process of proof formalisation
> consists of providing justifications for smaller goals. Many of such
> goals would be considered trivial by mathematicians. Still, modern
> ITPs require users to spend an important part of the formalisation
> effort on such easy goals. The main points that constitute this
> effort are usually library search, minor transformations on the
> already proved theorems (such as reordering assumptions or reasoning
> modulo associativity-commutativity), as well as combining a small
> number of simple known lemmas.

#### Autorewrite
Automatic rewriting has been implemented in Coq since at least 1999 [[CoqEarlyHistory]](https://coq.inria.fr/refman/history.html#version-6-3). Do demonstrate how it works, 
suppose we want e.g. `-(-x)` to automatically simplify to `x` for integers `x`. One can define a *rewrite hint database* of previously proven equalities. The Coq syntax is

```coq
(* Definitions of integers and unary int negation '-x' *)
From Coq Require Import ZArith.ZArith.

(* Notation to avoid writing `opp (opp x)` for `-(-x)` *)
Local Open Scope Z_scope.

(* Rewrite hint database. Contains `-(-x) = x` and `x+0=x`. *)
#[local] Hint Rewrite Z.opp_involutive Z.add_0_r: z_rew.

(* Example lemma *)
Lemma opp_opp_0 (x: Z): -(-x)+0 = x.
  (* transforms goal from `-(-x)+0=x` into `x=x`. *)
  autorewrite with z_rew.
```

I used this type of automation successfully in
[[AutomationBranch]](https://github.com/aleloi/coq-friendship-theorem/blob/more_automation/theories/adj2_matrix.v#L25-L32). 

On one hand, it is simple and well understood. On the other, the user
has to do manual work in finding which rewriting lemmas should be
added to the hint database. It does not help at all with *lemma
discovery*: when you don't know the name or possibly the statement of
the lemma you need. In addition, *autorewrite* only works with
rewriting lemmas, and only for those for which the rewriting is always
a simplification. It would not help when you want to rewrite
`a+b=b+a`: if you add `addC : forall a b: a+b=b+a` to the rewrite
database, it would always flip [NOTE: haven't tried] every addition.

One issue with autorewrite and `mathcomp` was that some lemmas did not
automatically rewrite. E.g. 

```coq
det_mx11 : forall [R : comRingType] (M : 'cV_1), \det M = M 0 0
```

is not automatically simplified, possibly because the structure `algC`
that I was using it with has `algC: Type` and not
`algC: comRingType`. Rather, `mathcomp` uses a mechanism of *canonical
structures* [[[MathCompBook]](#mathcompbook) chapter 7] that somehow
converts `algC` to `Algebraics.Implementation.comRingType`, but that
mechanism does not work with `autorewrite`. [Note I don't fully
understand this].

#### CoqHammer
[[Czaika18]](#czajka18) is a general purpose automation tool. It works
by first scanning though all premises (that can be named entities like
definitions or lemmas) in the environment, and filters out the top
$$N=1024$$ that it deems most likely to be used in the proof of the
current goal. The filtering can be done with a Naive Bayes relevance
filter. I don't know what the features for Naive Bayes nor what
distance is used for k-Nearest Neighbours [Note: it's in section 4 of
[[Czaika18]](#czajka18), but I have not read that far].

The $$N$$ chosen premises are converted to first order  logic in the TPTP
format [[THFo]](#THFo). When I first read [[Czaika18]](#czajka18) I
got the impression that the output of this step is quantified boolean
formulas (making all questions about them decidable), while Coq is
most certainly not decidable. Then I learned that that TPTP is not
limited to QBF, and that a statement that is provable in Coq need not
be provable after the translation. [[[Czaika18]](#czajka18) sec 5 says
that the translation is neither sound nor complete].

The TPTP output is then sent to external provers like
[[Eprover]](#eprover).

I tried to use CoqHammer for the Friendship Theorem project, but found
that for some reason, it could not solve even simple goals. Below is
an example. I am to prove that $$\det(-I)$$ is an invertible ring
element in the ring of complex algebraic numbers. I already know that
$$-I$$ is an invertible matrix, and there is a lemma `unitmxE` that says
that invertible matrices have invertible determinants. The prediction
step finds the lemma `unitmxE` among the top 50 candidates. Then
`CoqHammer` uses all available cores and all available memory until it
times out or crashes due to OOM.

```coq
  n : nat  (* size of goal matrix *)
  nge1 : 0 < n
  neg1M_unit : forall m : nat, (-1)%:M \in unitmx
  ============================
  \det (-1)%:M \is a GRing.unit
```

```coq
  unitmxE :
forall [R : comUnitRingType] [n : nat] (A : 'M_n),
(A \in unitmx) = (\det A \is a GRing.unit)
```

I suspect that the translation does not result in a provable
formula. I saved the TPTP file in
[coqhammer_input.p](coqhammer_input.p) with the hope of investigating
and eventually contacting the CoqHammer author.

Since this happens on all goals that I tested on, I suspect this has
to do with the `mathcomp` library. I that that some combination of
packed classes, implicit conversions or boolean reflection makes the
translation have "insufficient completeness" which leads to the
situation where nothing can be proven.

#### Coq Tactician
[[CoqTactician]](#coqtactician) aspieres to be a useable proof
automation framework that learns from earlier proofs.  It builds a
database of triples $$(\Gamma_1 \vdash \sigma_1, \texttt{tactic}, \Gamma_2 \vdash \sigma_2)$$ where $$\Gamma_1, \Gamma_2$$ are proof
contexts before and after application of `tactic`, and
$$\sigma_1, \sigma_2$$ are goals before and after `tactic`.
From this database of triples, the Tactician can then suggest possible
tactics by matching the current context and goal. It can also do a
tree search for proofs by applying tactic candidates, and searching
again from the resulting proof states.

TODO: actually try; I read the Github issue and the article sentence
and it doesn't work, but maybe it helps a little?


Unfortunately, it doesn't work with SSReflect / mathcomp, because
SSReflect uses a different tactic language.

## ML


  
  
## TODOs
* Finish reading about HOL in the survey article
* Find something about Coq/Lean vs HOL; is Coq more powerful?
* CIC / HOL vs ZFC - is there a difference?
* Gödel's theorem: 'False' is not inhabited, so you can't prove it in
  CIC. CIC is definitely powerful enough to encode Peano numbers. By
  Gödel it shouldn't be possible to prove CIC consistent. But
	  shouldn't consistency mean that you cannot prove False? Check 

## References
* <a id="friendship">[smallish Coq project]</a> 
https://github.com/aleloi/coq-friendship-theorem.
Alex Loiko, 2022.  Proof of the Frendship Theorem in Coq.

* <a id="leanintro">[LeanIntro]</a>
https://leanprover.github.io/theorem_proving_in_lean/introduction.html.
Jeremy Avigad, Leonardo de Moura, Soonho Kong, 2017. Introduction
to theorem proving in Lean.

* <a id="certicrypt">[CertiCrypt]</a>
Barthe Gilles , Benjamin Grégoire,   Santiago Zanella Béguelin, 2009.
Formal Certification of Code-Based Cryptographic Proofs. 
https://doi.org/10.1145/1594834.1480894.
ACM SIGPLAN Notices, Volume 44, Issue 1, January 2009, pp 90–101.

* <a id="CryptoSE">https://crypto.stackexchange.com/a/34326</a>
Biv, 2016. Comprehensive StackExchange answer on the use of formal
methods in cryptography.

* <a id="Nielsen19">[Nielsen19] </a>
  Jakob Botsch Nielsen, Bas Spitters. 2019. https://arxiv.org/abs/1911.04732.
  Smart Contract Interactions in Coq.
  
* <a id="Friendship72">[Friendship72] </a>
Judith Q Longyear, T.D Parsons. 1972. https://doi.org/10.1016/1385-7258(72)90063-7. 
The Friendship Theorem.

* <a id="FriendshipBook">[BookProof] </a>
Aigner et. al. 2010. Proofs from THE BOOK, 4th ed.,  pp. 257-259.
*Note:* The book proof identical to https://math.mit.edu/~apost/courses/18.204-2016/18.204_Elizabeth_Walker_final_paper.pdf.

* <a id="ErdosProof">[ErdosProof] </a>
P. Erdös, A. Rényi, V. T. Sós. On a Problem in Graph Theory. 1966.
Studia Math. Hungar. 1, 215-235, Theorem 6. 
*Note:* To me it's not the same as the book proof; it reformulates to lines in the projective plane and cites [[Baer66]](#Baer66) for the implication of $$n=k^2-k+1$$ to $$(k-1)\ | k^2$$. Skimming the Baer66 article I couldn't find the linear algebra I used; I didn't read it but it could just as well be a counting argument like in [[Friendship72]](#Friendship72).

* <a id="Baer66">[Baer66] </a>
R. Baer. 1946. Polarities in finite projective planes, Bulletin of the American Math. Soc. 52., pp. 77-93.

* <a id="Czaika18"> [Czaika18] </a>
Łukasz Czajka, Cezary Kaliszyk. 2018. Hammer for Coq: Automation for Dependent Type Theory. *Journal of Automated Reasoning*  volume 61, pp. 423–453. 
Documentation available on https://coqhammer.github.io.

* <a id="THFo"> [THFo] </a>
Christoph Benzmüller, Florian Rabe, Geoff Sutcliffe. 2008.
THF0 – The Core of the TPTP Language for Higher-Order Logic.
*International Joint Conference on Automated Reasoning*. pp. 491-506.

* <a id="eprover"> [Eprover] </a>
Stephan Schulz, Simon Cruanes, Petar Vukmirovic. 2019.
Faster, Higher, Stronger: E 2.3.
*Proceedings of the 27th Conference on Automated Deduction (CADE'19)*. 
Volume 11716 of LNAI.

* <a id="mathcompbook"> [MathCompBook] </a>
Yves Bertot, Georges Gonthier, Assia Mahboubi, Enrico Tassi. 2020.
Mathematical Components.
https://math-comp.github.io/mcb/

* <a id="coqtactician"> [CoqTactician] </a>
Lasse Blaauwbroek, Josef Urban1, Herman Geuvers2. 2020.
The Tactician (extended version)
A Seamless, Interactive Tactic Learner and Prover for Coq. 
https://arxiv.org/abs/2008.00120v1.




* [Braibant 2013] @InProceedings{10.1007/978-3-642-39799-8_14,
author="Braibant, Thomas
and Chlipala, Adam",
editor="Sharygina, Natasha
and Veith, Helmut",
title="Formal Verification of Hardware Synthesis",
booktitle="Computer Aided Verification",
year="2013",
publisher="Springer Berlin Heidelberg",
address="Berlin, Heidelberg",
pages="213--228",
abstract="We report on the implementation of a certified compiler for a high-level hardware description language (HDL) called Fe-Si (FEatherweight SynthesIs). Fe-Si is a simplified version of Bluespec, an HDL based on a notion of guarded atomic actions. Fe-Si is defined as a dependently typed deep embedding in Coq. The target language of the compiler corresponds to a synthesisable subset of Verilog or VHDL. A key aspect of our approach is that input programs to the compiler can be defined and proved correct inside Coq. Then, we use extraction and a Verilog back-end (written in OCaml) to get a certified version of a hardware design.",
isbn="978-3-642-39799-8"
}


* [Kern 99 survey] @article{10.1145/307988.307989,
author = {Kern, Christoph and Greenstreet, Mark R.},
title = {Formal Verification in Hardware Design: A Survey},
year = {1999},
issue_date = {April 1999},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
volume = {4},
number = {2},
issn = {1084-4309},
url = {https://doi.org/10.1145/307988.307989},
doi = {10.1145/307988.307989},
abstract = {In recent years, formal methods have emerged as an alternative approach to ensuring the quality and correctness of hardware designs, overcoming some of the limitations of traditional validation techniques such as simulation and testing.There are two main aspects to the application of formal methods in a design process: the formal framework used to specify desired properties of a design and the verification techniques and tools used to reason about the relationship between a specification and a corresponding implementation. We survey a variety of frameworks and techniques proposed in the literature and applied to actual designs. The specification frameworks we describe include temporal logics, predicate logic, abstraction and refinement, as well as containment between ω-regular languages. The verification techniques presented include model checking, automata-theoretic techniques, automated theorem proving, and approaches that integrate the above methods.In order to provide insight into the scope and limitations of currently available techniques, we present a selection of case studies where formal methods were applied to industrial-scale designs, such as microprocessors, floating-point hardware, protocols, memory subsystems, and communications hardware.},
journal = {ACM Trans. Des. Autom. Electron. Syst.},
month = {apr},
pages = {123–193},
numpages = {71},
keywords = {case studies, model checking, formal verification, formal methods, survey, hardware verification, language containment, theorem proving}
}
* [replication crisis paper] TY  - JOUR
AU  - Bordg, Anthony
PY  - 2021
DA  - 2021/12/01
TI  - A Replication Crisis in Mathematics?
JO  - The Mathematical Intelligencer
SP  - 48
EP  - 52
VL  - 43
IS  - 4
SN  - 1866-7414
UR  - https://doi.org/10.1007/s00283-020-10037-7
DO  - 10.1007/s00283-020-10037-7
ID  - Bordg2021
ER  - 
* [Hales 2008] @article{article,
author = {Hales, Thomas},
year = {2008},
month = {01},
pages = {},
title = {Formal Proof},
volume = {55},
journal = {Notices of the American Mathematical Society}
}

* [Brujin 95] 
@inbook{7f386bbf005243388ff0cb9efc2183ef,
title = "On the roles of types in mathematics",
author = "{Bruijn, de}, N.G.",
year = "1995",
language = "English",
isbn = "2-87209-363-X",
series = "Cahiers du centre de logique",
publisher = "Academia-Erasme",
pages = "27--54",
booktitle = "The Curry-Howard isomorphism / ed. by P. de Groote",

}

* [SetTypeTypeSet] @inbook{inbook,
author = {Werner, Benjamin},
year = {2006},
month = {10},
pages = {530-546},
title = {Sets in types, types in sets},
isbn = {978-3-540-63388-4},
doi = {10.1007/BFb0014566}
}
