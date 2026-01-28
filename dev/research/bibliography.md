# Bibliography

Comprehensive bibliography of all literature referenced in the CALC research documents.

---

## Foundational Papers

### Belnap (1982) — Display Logic
**Citation:** Belnap, N.D. (1982). Display Logic. *Journal of Philosophical Logic*, 11(4), 375-417.

**Summary:** Introduced display calculus as a generalization of Gentzen's sequent calculus. Proved that any display calculus satisfying 8 syntactic conditions (C1-C8) admits cut elimination generically.

**Tags:** `display-calculus` `cut-elimination` `proof-theory` `foundational`

**Referenced in:** [[display-calculus]], [[QnA]], [[exponential-display-problem]], [[ANKI]]

---

### Gentzen (1935) — Sequent Calculus
**Citation:** Gentzen, G. (1935). Untersuchungen über das logische Schließen. *Mathematische Zeitschrift*, 39, 176-210, 405-431.

**Summary:** Introduced the sequent calculus (LK for classical, LJ for intuitionistic logic) and proved the Hauptsatz (cut-elimination theorem).

**Tags:** `sequent-calculus` `cut-elimination` `foundational`

**Referenced in:** [[proof-calculi-foundations]], [[display-calculus]]

---

### Girard (1987) — Linear Logic
**Citation:** Girard, J.-Y. (1987). Linear Logic. *Theoretical Computer Science*, 50(1), 1-102.

**Summary:** Introduced linear logic, decomposing classical/intuitionistic connectives based on resource sensitivity. Introduced the exponentials (!, ?) and the tensor/par distinction.

**Tags:** `linear-logic` `resource-semantics` `foundational`

**Referenced in:** [[logics-overview]], [[QTT]], [[residuation]]

---

## Display Calculus & Multi-Type Systems

### Greco & Palmigiano (2023) — Linear Logic Properly Displayed
**Citation:** Greco, G., & Palmigiano, A. (2023). Linear Logic Properly Displayed. *ACM Transactions on Computational Logic*, 24(2), Article 13, 1-56.

**URL:** https://dl.acm.org/doi/10.1145/3570919 | https://arxiv.org/abs/1611.04181

**Summary:** Introduced *proper* display calculi for linear logic with exponentials. Key innovation: properness (closure under uniform substitution) enables smoothest cut elimination. Uses multi-type methodology to handle exponentials via adjoint decomposition.

**Tags:** `display-calculus` `linear-logic` `exponentials` `multi-type` `cut-elimination`

**Referenced in:** [[exponential-display-problem]], [[logics-overview]], [[QnA]], [[ANKI]]

---

### Benton (1994) — LNL (Linear/Non-Linear) Logic
**Citation:** Benton, P.N. (1994). A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models. In *Computer Science Logic (CSL'94)*, LNCS 933, 121-135. Springer.

**URL:** https://link.springer.com/chapter/10.1007/BFb0022251

**Summary:** Showed that the ! modality can be decomposed into two adjoint functors: F (Lin) and G (Mny), where ! = F ∘ G. Established the LNL model as a symmetric monoidal adjunction between cartesian and linear categories.

**Tags:** `linear-logic` `exponentials` `adjunction` `categorical-semantics` `LNL`

**Referenced in:** [[exponential-display-problem]], [[ANKI]], [[QTT]]

---

### Restall (1991) — Display Calculus for Classical Linear Logic
**Citation:** Restall, G. (1991). A Display Calculus for Classical Linear Logic.

**URL:** https://greg.restall.net/papers/dcll.html

**Summary:** Extended Belnap's display logic with all connectives of classical linear logic. Showed the systems are modular.

**Tags:** `display-calculus` `linear-logic` `classical`

**Referenced in:** [[display-calculus]], [[logics-overview]]

---

### Ciabattoni et al. (2014) — Hypersequent and Display Calculi
**Citation:** Ciabattoni, A., Ramanayake, R., & Wansing, H. (2014). Hypersequent and Display Calculi – a Unified Perspective. *Studia Logica*, 102, 1245-1294.

**URL:** https://link.springer.com/article/10.1007/s11225-014-9566-z

**Summary:** Comprehensive comparison of hypersequent and display calculi. Shows how both extend standard sequent calculus and their relative expressiveness.

**Tags:** `hypersequent` `display-calculus` `comparison` `modal-logic`

**Referenced in:** [[display-calculus]], [[proof-calculi-foundations]]

---

### Frittella et al. (2016) — Multi-Type Display Calculus for Dynamic Epistemic Logic
**Citation:** Frittella, S., Greco, G., Kurz, A., Palmigiano, A., & Sikimic, V. (2016). Multi-type Display Calculus for Dynamic Epistemic Logic. *Journal of Logic and Computation*, 26(6), 2017-2065.

**URL:** https://academic.oup.com/logcom/article-abstract/26/6/2017/2743523

**Summary:** Applied multi-type display calculus methodology to dynamic epistemic logic (D.EAK). Shows how different types (agents, propositions, actions) interact.

**Tags:** `multi-type` `display-calculus` `epistemic-logic` `modal-logic`

**Referenced in:** [[display-calculus]], [[logics-overview]], [[multi-type-display-calculus]]

---

### Frittella et al. (2014) — Multi-type Sequent Calculi
**Citation:** Frittella, S., Greco, G., Kurz, A., & Palmigiano, A. (2014). Multi-type sequent calculi. In *Trends in Logic XIII*, pp. 81–93. Łódź University Press.

**Summary:** Foundational paper on multi-type sequent calculi methodology, establishing the framework for handling logics with multiple sorts of formulas.

**Tags:** `multi-type` `sequent-calculus` `methodology`

**Referenced in:** [[multi-type-display-calculus]]

---

### nLab — !-modality
**Citation:** nLab authors. !-modality.

**URL:** https://ncatlab.org/nlab/show/!-modality

**Summary:** Comprehensive categorical treatment of the bang modality as a comonad. Explains linear-nonlinear adjunction and how ! = F ∘ G.

**Tags:** `exponentials` `comonad` `categorical-semantics` `LNL`

**Referenced in:** [[multi-type-display-calculus]], [[exponential-display-problem]]

---

### Blog: A Simplification to LNL Models
**Citation:** Blog post. (2020). A Simplification to LNL Models.

**URL:** https://blog.hde.design/published/2020-04-02-A-Simplification-to-LNL-Models.html

**Summary:** Presents a simplified definition of LNL models, removing the requirement that the adjunction be monoidal while preserving expressive power.

**Tags:** `LNL` `categorical-semantics` `exponentials`

**Referenced in:** [[multi-type-display-calculus]]

---

### Calculus-Toolbox-2
**Citation:** goodlyrottenapple. Calculus-Toolbox-2.

**URL:** https://github.com/goodlyrottenapple/calculus-toolbox-2

**Summary:** Updated display calculus tool supporting multi-type calculi at runtime. Uses DSL for specification with explicit type parameters.

**Tags:** `tool` `display-calculus` `multi-type` `implementation`

**Referenced in:** [[multi-type-display-calculus]], [[DSL-approaches]]

---

### Pfenning — Adjoint SAX Lecture Notes
**Citation:** Pfenning, F. Adjoint SAX Lecture Notes. CMU 15-836.

**URL:** https://www.cs.cmu.edu/~fp/courses/15836-f23/lectures/15-adjsax.pdf

**Summary:** Lecture notes on adjoint logic, generalizing LNL to arbitrary preorders of modes with adjunctions between them.

**Tags:** `adjoint-logic` `LNL` `sequent-calculus` `CMU`

**Referenced in:** [[multi-type-display-calculus]]

---

### Pruiksma & Pfenning (2020) — A Message-Passing Interpretation of Adjoint Logic
**Citation:** Pruiksma, K., & Pfenning, F. (2020). A Message-Passing Interpretation of Adjoint Logic. *Journal of Logical and Algebraic Methods in Programming*.

**Summary:** Gives operational semantics for adjoint logic via message passing, connecting multi-modal type systems with concurrent computation.

**Tags:** `adjoint-logic` `session-types` `concurrency`

**Referenced in:** [[multi-type-display-calculus]]

---

## Curry-Howard & Type Theory

### Wadler (2015) — Propositions as Types
**Citation:** Wadler, P. (2015). Propositions as Types. *Communications of the ACM*, 58(12), 75-84.

**URL:** https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf

**Summary:** Accessible exposition of the Curry-Howard correspondence. Explains the "mystery" of why natural deduction and lambda calculus are the same. Discusses extensions to linear, modal, and other logics.

**Tags:** `curry-howard` `type-theory` `tutorial` `foundational`

**Referenced in:** [[proof-calculi-foundations]], [[ANKI]]

---

### Howard (1980) — Formulae-as-Types
**Citation:** Howard, W.A. (1980). The Formulae-as-Types Notion of Construction. In *To H.B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, 479-490. Academic Press.

**Summary:** The original paper establishing the Curry-Howard correspondence for intuitionistic logic.

**Tags:** `curry-howard` `foundational`

**Referenced in:** [[proof-calculi-foundations]]

---

## Quantitative & Graded Types

### Orchard et al. (2019) — Granule: Quantitative Program Reasoning with Graded Modal Types
**Citation:** Orchard, D., Liepelt, V., & Eades, H. (2019). Quantitative Program Reasoning with Graded Modal Types. *Proceedings of the ACM on Programming Languages*, 3(ICFP), Article 110.

**URL:** https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf

**Summary:** Introduced graded modal types (□_r) indexed by semiring elements. Combines linear types with coeffect tracking. Implemented in the Granule language.

**Tags:** `graded-types` `linear-logic` `semiring` `granule` `implementation`

**Referenced in:** [[QTT]], [[logics-overview]], [[ANKI]]

---

### Atkey (2018) — Syntax and Semantics of Quantitative Type Theory
**Citation:** Atkey, R. (2018). Syntax and Semantics of Quantitative Type Theory. In *LICS 2018*, 56-65.

**URL:** https://bentnib.org/quantitative-type-theory.html

**Summary:** Fixed McBride's original QTT by properly handling substitution. Gave categorical semantics.

**Tags:** `QTT` `dependent-types` `semiring` `categorical-semantics`

**Referenced in:** [[QTT]]

---

### McBride (2016) — I Got Plenty o' Nuttin'
**Citation:** McBride, C. (2016). I Got Plenty o' Nuttin'. In *A List of Successes That Can Change the World*, LNCS 9600, 207-233. Springer.

**URL:** https://personal.cis.strath.ac.uk/conor.mcbride/PlentyO-CR.pdf

**Summary:** Original proposal for QTT. Used semiring annotations on binders to track resource usage.

**Tags:** `QTT` `dependent-types` `semiring`

**Referenced in:** [[QTT]]

---

### Brady (2021) — Idris 2: Quantitative Type Theory in Practice
**Citation:** Brady, E. (2021). Idris 2: Quantitative Type Theory in Practice. In *ECOOP 2021*.

**URL:** https://arxiv.org/abs/2104.00480

**Summary:** Describes the implementation of QTT in Idris 2. Uses the {0, 1, ω} semiring.

**Tags:** `QTT` `idris` `implementation`

**Referenced in:** [[QTT]]

---

### Moon et al. (2021) — Graded Modal Dependent Type Theory
**Citation:** Moon, B., Eades, H., & Orchard, D. (2021). Graded Modal Dependent Type Theory. In *ESOP 2021*, LNCS 12648.

**URL:** https://link.springer.com/chapter/10.1007/978-3-030-72019-3_17

**Summary:** Combines graded modalities with dependent types (Grtt). State of the art for combining all features.

**Tags:** `graded-types` `dependent-types` `granule`

**Referenced in:** [[QTT]]

---

## Proof Search & Focusing

### Andreoli (1992) — Logic Programming with Focusing Proofs
**Citation:** Andreoli, J.-M. (1992). Logic Programming with Focusing Proofs in Linear Logic. *Journal of Logic and Computation*, 2(3), 297-347.

**Summary:** Introduced focusing for linear logic. Alternating invertible/non-invertible phases reduces proof search non-determinism.

**Tags:** `focusing` `proof-search` `linear-logic`

**Referenced in:** [[display-calculus]], [[proof-calculi-foundations]]

---

### Pfenning — CMU Course Notes
**Citation:** Pfenning, F. Various lecture notes from CMU courses.

**URLs:**
- 15-836 Substructural Logics: https://www.cs.cmu.edu/~fp/courses/15836-f23/
- 15-317 Constructive Logic: https://www.cs.cmu.edu/~fp/courses/15317-f17/
- 15-816 Modal Logic: https://www.cs.cmu.edu/~fp/courses/15816-s10/

**Summary:** Comprehensive lecture notes on sequent calculus, cut elimination, linear logic, substructural logics, and modal logic.

**Tags:** `tutorial` `sequent-calculus` `linear-logic` `modal-logic` `CMU`

**Referenced in:** [[proof-calculi-foundations]], [[display-calculus]], [[ANKI]]

---

## Proof Nets

### Girard (1996) — Proof Nets: The Parallel Syntax for Proof Theory
**Citation:** Girard, J.-Y. (1996). Proof Nets: The Parallel Syntax for Proof Theory.

**URL:** https://girard.perso.math.cnrs.fr/Proofnets.pdf

**Summary:** Graphical representation of proofs eliminating "bureaucracy." Cut elimination is local graph rewriting.

**Tags:** `proof-nets` `linear-logic`

**Referenced in:** [[display-calculus]]

---

## Deep Inference

### Guglielmi — Calculus of Structures
**Citation:** Guglielmi, A. Deep Inference and the Calculus of Structures.

**URL:** http://alessio.guglielmi.name/res/cos/

**Summary:** Proof formalism where rules apply anywhere inside structures. Eliminates need for display postulates.

**Tags:** `deep-inference` `proof-theory`

**Referenced in:** [[display-calculus]]

---

## Other References

### Boolos (1984) — Don't Eliminate Cut!
**Citation:** Boolos, G. (1984). Don't Eliminate Cut! *Journal of Philosophical Logic*, 13, 373-378.

**Summary:** Showed that cut elimination can cause super-exponential proof size explosion.

**Tags:** `cut-elimination` `complexity`

**Referenced in:** [[QnA]], [[proof-calculi-foundations]]

---

### Clouston et al. (2013) — Annotation-Free Sequent Calculi for FILL
**Citation:** Clouston, R., Dawson, J., Goré, R., & Tiu, A. (2013). Annotation-Free Sequent Calculi for Full Intuitionistic Linear Logic.

**URL:** https://arxiv.org/abs/1307.0289

**Summary:** Display calculus for Full Intuitionistic Linear Logic with exclusion connective.

**Tags:** `display-calculus` `linear-logic` `FILL`

**Referenced in:** [[logics-overview]]

---

### Dawson & Goré — From Display Calculi to Deep Nested Sequent Calculi
**Citation:** Dawson, J., & Goré, R. From Display Calculi to Deep Nested Sequent Calculi. In *TABLEAUX 2014*, LNCS 8123.

**URL:** https://link.springer.com/chapter/10.1007/978-3-662-44602-7_20

**Summary:** Translation between display and nested sequent calculi.

**Tags:** `display-calculus` `nested-sequent`

**Referenced in:** [[display-calculus]], [[logics-overview]]

---

## Encyclopedias & Tutorials

### Stanford Encyclopedia of Philosophy
- [Linear Logic](https://plato.stanford.edu/entries/logic-linear/)
- [Type Theory](https://plato.stanford.edu/entries/type-theory/)
- [Intuitionistic Type Theory](https://plato.stanford.edu/entries/type-theory-intuitionistic/)
- [Substructural Logics](https://plato.stanford.edu/entries/logic-substructural/)
- [Proof-Theoretic Semantics](https://plato.stanford.edu/entries/proof-theoretic-semantics/)

**Tags:** `encyclopedia` `tutorial`

---

### nLab
- [propositions as types](https://ncatlab.org/nlab/show/propositions+as+types)
- [sequent calculus](https://ncatlab.org/nlab/show/sequent+calculus)
- [display logic](https://ncatlab.org/nlab/show/display+logic)
- [linear logic](https://ncatlab.org/nlab/show/linear+logic)
- [type theory](https://ncatlab.org/nlab/show/type+theory)
- [!-modality](https://ncatlab.org/nlab/show/!-modality)

**Tags:** `encyclopedia` `categorical`

---

### Wikipedia
- [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)
- [Sequent calculus](https://en.wikipedia.org/wiki/Sequent_calculus)
- [Cut-elimination theorem](https://en.wikipedia.org/wiki/Cut-elimination_theorem)
- [Proof net](https://en.wikipedia.org/wiki/Proof_net)
- [Hypersequent](https://en.wikipedia.org/wiki/Hypersequent)
- [Residuated lattice](https://en.wikipedia.org/wiki/Residuated_lattice)
- [Galois connection](https://en.wikipedia.org/wiki/Galois_connection)

**Tags:** `encyclopedia`

---

## Session Types & Process Calculi

### Caires & Pfenning (2010) — Session Types via Propositions as Types
**Citation:** Caires, L., & Pfenning, F. (2010). Session Types as Intuitionistic Linear Propositions. In *CONCUR 2010*, LNCS 6269.

**URL:** https://www.cs.cmu.edu/~fp/papers/concur10.pdf

**Summary:** Discovered Curry-Howard correspondence between intuitionistic linear logic and session types. Linear propositions = session types, cut = communication.

**Tags:** `session-types` `linear-logic` `curry-howard` `process-calculus`

**Referenced in:** [[nomos]], [[ANKI]]

---

### Wadler (2012) — Propositions as Sessions
**Citation:** Wadler, P. (2012). Propositions as Sessions. In *ICFP 2012*.

**URL:** https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf

**Summary:** Classical linear logic version of session types. Alternative to Caires-Pfenning's intuitionistic formulation.

**Tags:** `session-types` `linear-logic` `classical` `curry-howard`

**Referenced in:** [[nomos]]

---

### Das et al. (2019, 2021) — Nomos
**Citation:** Das, A., Balzer, S., Hoffmann, J., Pfenning, F., & Santurkar, I. (2021). Resource-Aware Session Types for Digital Contracts. In *CSF 2021*.

**URLs:**
- https://arxiv.org/abs/1902.06056
- https://www.cs.cmu.edu/~janh/assets/pdf/DasBHP19.pdf
- https://github.com/ankushdas/Nomos

**Summary:** Programming language for smart contracts combining session types, linear types, and automatic amortized resource analysis. Statically bounds gas consumption.

**Tags:** `session-types` `linear-types` `blockchain` `smart-contracts` `resource-analysis` `implementation`

**Referenced in:** [[nomos]], [[ANKI]]

---

### Toninho et al. (2013) — Linear Logic Propositions as Session Types
**Citation:** Toninho, B., Caires, L., & Pfenning, F. (2013). Higher-Order Processes, Functions, and Sessions: A Monadic Integration. In *MSCS*.

**URL:** https://www.cs.cmu.edu/~fp/papers/mscs13.pdf

**Summary:** Extended session types with higher-order features. Shows tight correspondence between linear logic and process calculus.

**Tags:** `session-types` `linear-logic` `higher-order`

**Referenced in:** [[nomos]]

---

## Logic Programming & FFI

### Pfenning & Schürmann (1999) — Twelf
**Citation:** Pfenning, F., & Schürmann, C. (1999). System Description: Twelf — A Meta-Logical Framework for Deductive Systems. In *CADE-16*.

**URL:** https://www.cs.cmu.edu/~fp/papers/cade99.pdf

**Summary:** Implementation of the LF logical framework. No built-in arithmetic or FFI — everything derived from axioms. Pure but impractical for computation.

**Tags:** `twelf` `LF` `logic-programming` `metatheory`

**Referenced in:** [[ffi-logics]], [[ANKI]]

---

### Twelf User's Guide — Modes
**Citation:** Pfenning, F. Twelf User's Guide - Modes.

**URL:** https://www.cs.cmu.edu/~twelf/guide-1-4/twelf_7.html

**Summary:** Mode declarations specify information flow: + (input, must be ground), - (output, will be ground), * (unrestricted). Enables termination checking and optimization.

**Tags:** `twelf` `mode-checking` `logic-programming`

**Referenced in:** [[ffi-logics]]

---

### Schack-Nielsen & Schürmann (2008) — Celf
**Citation:** Schack-Nielsen, A., & Schürmann, C. (2008). Celf — A Logical Framework for Deductive and Concurrent Systems. In *IJCAR 2008*.

**URL:** https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28

**Summary:** Extends LF with linear types and a monad for concurrency. Combines backward chaining (outside monad) with forward chaining (inside monad).

**Tags:** `celf` `LF` `linear-logic` `logic-programming` `forward-chaining`

**Referenced in:** [[ffi-logics]]

---

### Martens (2015) — Ceptre
**Citation:** Martens, C. (2015). Ceptre: A Language for Modeling Generative Interactive Systems. In *AIIDE 2015*.

**URL:** https://www.cs.cmu.edu/~cmartens/ceptre.pdf

**Summary:** Linear logic programming for game mechanics and narrative generation. Forward-chaining state transitions. Shows correspondence between gameplay and proof search.

**Tags:** `ceptre` `linear-logic` `game-mechanics` `forward-chaining` `implementation`

**Referenced in:** [[ffi-logics]]

---

### Necula & Lee (2001) — Oracle-Based Proof Checking
**Citation:** Necula, G., & Lee, P. (2001). Oracle-Based Checking of Untrusted Software. In *POPL 2001*.

**URL:** https://dl.acm.org/doi/10.1145/360204.360216

**Summary:** Proof-Carrying Code variant where proofs are replaced by oracles (bit streams). Oracles guide nondeterministic proof search without being verified.

**Tags:** `proof-carrying-code` `oracle` `trusted-computation`

**Referenced in:** [[ffi-logics]]

---

### Constraint Logic Programming
**Citation:** Various.

**URLs:**
- https://en.wikipedia.org/wiki/Constraint_logic_programming
- https://www.swi-prolog.org/pldoc/man?section=clp

**Summary:** Extends Prolog with constraint solvers over domains (CLP(FD), CLP(R), CLP(Q)). Solver is external "trusted oracle" for arithmetic constraints.

**Tags:** `CLP` `constraint-solving` `logic-programming` `oracle`

**Referenced in:** [[ffi-logics]], [[ANKI]]

---

### Agda FFI Documentation
**Citation:** Agda Development Team.

**URLs:**
- https://agda.readthedocs.io/en/latest/language/foreign-function-interface.html
- https://agda.readthedocs.io/en/latest/language/postulates.html

**Summary:** Agda FFI via postulates and COMPILE pragmas. Postulates treated as axioms at type-check time; external code at runtime. No verification that they match.

**Tags:** `agda` `FFI` `postulates` `trusted-computation`

**Referenced in:** [[ffi-logics]], [[ANKI]]

---

### VeriFFI (2023)
**Citation:** Princeton PL Group.

**URL:** https://www.cs.princeton.edu/~appel/papers/VeriFFI.pdf

**Summary:** Verified FFI between Coq and C. Connects specifications and proofs across languages, not just operational glue.

**Tags:** `coq` `FFI` `verified` `trusted-computation`

**Referenced in:** [[ffi-logics]]

---

## Tools & Implementations

### Calculus Toolbox
**URL:** https://goodlyrottenapple.github.io/calculus-toolbox/

**Summary:** Haskell-based tool for defining and working with display calculi. Supports Isabelle export.

**Tags:** `tool` `display-calculus` `isabelle`

**Referenced in:** [[display-calculus]], [[DSL-approaches]]

---

### Granule
**URL:** https://granule-project.github.io/

**Summary:** Functional programming language with graded modal types.

**Tags:** `tool` `graded-types` `implementation`

**Referenced in:** [[QTT]], [[logics-overview]]

---

### Idris 2
**URL:** https://idris2.readthedocs.io/

**Summary:** Dependently-typed language implementing QTT.

**Tags:** `tool` `QTT` `implementation`

**Referenced in:** [[QTT]]

---

## Index by Tag

### `display-calculus`
Belnap (1982), Greco & Palmigiano (2023), Restall (1991), Ciabattoni et al. (2014), Frittella et al. (2016), Clouston et al. (2013), Dawson & Goré

### `linear-logic`
Girard (1987), Greco & Palmigiano (2023), Benton (1994), Restall (1991), Orchard et al. (2019), Andreoli (1992), Girard (1996), Caires & Pfenning (2010), Wadler (2012), Das et al. (2021)

### `cut-elimination`
Belnap (1982), Gentzen (1935), Greco & Palmigiano (2023), Boolos (1984)

### `curry-howard`
Wadler (2015), Howard (1980), Caires & Pfenning (2010), Wadler (2012)

### `graded-types` / `QTT`
Orchard et al. (2019), Atkey (2018), McBride (2016), Brady (2021), Moon et al. (2021)

### `exponentials` / `LNL`
Greco & Palmigiano (2023), Benton (1994)

### `multi-type`
Greco & Palmigiano (2023), Frittella et al. (2016)

### `foundational`
Belnap (1982), Gentzen (1935), Girard (1987), Howard (1980)

### `session-types`
Caires & Pfenning (2010), Wadler (2012), Das et al. (2021), Toninho et al. (2013)

### `blockchain` / `smart-contracts`
Das et al. (2021) — Nomos

### `logic-programming`
Pfenning & Schürmann (1999), Twelf Modes, Schack-Nielsen & Schürmann (2008), Martens (2015), CLP

### `FFI` / `trusted-computation`
Agda FFI, VeriFFI (2023), Necula & Lee (2001), CLP

### `implementation` / `tool`
Calculus Toolbox, Granule, Idris 2, Nomos, Twelf, Celf, Ceptre

---

## Interactive Proving & Prover Orchestration

### Milner — LCF Theorem Prover
**Citation:** Milner, R., et al. (1970s). Edinburgh LCF.

**Summary:** Introduced the LCF architecture: theorems as abstract data type, only constructible through inference rules in trusted kernel. ML type system enforces soundness.

**Tags:** `LCF` `trusted-kernel` `foundational`

**Referenced in:** [[interactive_proving]]

---

### Gordon (2000) — From LCF to HOL: a short history
**Citation:** Gordon, M. (2000). From LCF to HOL: a short history. In *The History of Programming Languages*.

**URL:** https://www.cl.cam.ac.uk/archive/mjcg/papers/HolHistory.pdf

**Summary:** Historical account of the evolution from LCF to HOL theorem provers, documenting design decisions and their rationale.

**Tags:** `LCF` `HOL` `history`

**Referenced in:** [[interactive_proving]]

---

### Harrison — HOL Light
**Citation:** Harrison, J. HOL Light Theorem Prover.

**URL:** https://github.com/jrh13/hol-light

**Summary:** Minimalist LCF-style prover with ~400 lines of trusted kernel, 3 axioms, 10 inference rules.

**Tags:** `HOL-Light` `LCF` `trusted-kernel` `implementation`

**Referenced in:** [[interactive_proving]]

---

### Abrahamsson et al. (2022) — Candle: A Verified Implementation of HOL Light
**Citation:** Abrahamsson, O., et al. (2022). Candle: A Verified Implementation of HOL Light. In *ITP 2022*.

**URL:** https://cakeml.org/itp22-candle.pdf

**Summary:** Fully verified clone of HOL Light compiled to machine code via CakeML. Provides end-to-end correctness theorem.

**Tags:** `HOL-Light` `verified` `CakeML` `trusted-kernel`

**Referenced in:** [[interactive_proving]]

---

### Paulson (2022) — The de Bruijn Criterion vs the LCF Architecture
**Citation:** Paulson, L.C. (2022). The de Bruijn Criterion vs the LCF Architecture. Blog post.

**URL:** https://lawrencecpaulson.github.io/2022/01/05/LCF.html

**Summary:** Comparison of two fundamental approaches to proof assistant correctness: LCF (abstract types) vs de Bruijn (proof certificates).

**Tags:** `LCF` `de-Bruijn` `trusted-kernel` `comparison`

**Referenced in:** [[interactive_proving]]

---

### Paulson — Three Years of Experience with Sledgehammer
**Citation:** Paulson, L.C., & Blanchette, J.C. (2010). Three Years of Experience with Sledgehammer, a Practical Link between Automatic and Interactive Theorem Provers.

**URL:** https://www.cl.cam.ac.uk/~lp15/papers/Automation/paar.pdf

**Summary:** Empirical evaluation of Sledgehammer. Key finding: "Running E, SPASS, and Vampire in parallel for five seconds solves as many problems as running a single theorem prover for two minutes."

**Tags:** `sledgehammer` `parallel-provers` `empirical` `isabelle`

**Referenced in:** [[interactive_proving]]

---

### Paulson (2022) — Sledgehammer: Some History, Some Tips
**Citation:** Paulson, L.C. (2022). Sledgehammer: Some History, Some Tips. Blog post.

**URL:** https://lawrencecpaulson.github.io/2022/04/13/Sledgehammer.html

**Summary:** Practical guide to Sledgehammer with historical context. Documents the evolution from 2003 Metis integration to modern parallel prover architecture.

**Tags:** `sledgehammer` `isabelle` `practical`

**Referenced in:** [[interactive_proving]]

---

### Isabelle Team — Sledgehammer User's Guide
**Citation:** Isabelle Development Team. Sledgehammer User's Guide.

**URL:** https://isabelle.in.tum.de/dist/doc/sledgehammer.pdf

**Summary:** Official documentation covering parallel prover execution, relevance filters (MePo, MaSh), proof reconstruction, and configuration.

**Tags:** `sledgehammer` `isabelle` `documentation`

**Referenced in:** [[interactive_proving]]

---

### Lean Community — Metaprogramming in Lean 4
**Citation:** Lean Community. Metaprogramming in Lean 4.

**URL:** https://leanprover-community.github.io/lean4-metaprogramming-book/

**Summary:** Comprehensive guide to Lean4 metaprogramming covering the monad hierarchy (CoreM → MetaM → TermElabM → TacticM), custom tactic implementation, and quotations.

**Tags:** `lean4` `metaprogramming` `TacticM` `tutorial`

**Referenced in:** [[interactive_proving]]

---

### Pédrot (2019) — Ltac2: Tactical Warfare
**Citation:** Pédrot, P.-M. (2019). Ltac2: Tactical Warfare. In *CoqPL 2019*.

**URL:** https://www.xn--pdrot-bsa.fr/articles/coqpl2019.pdf

**Summary:** Design document for Ltac2, explaining the move from dynamically-typed Ltac1 to a statically-typed ML-style language with explicit effects.

**Tags:** `coq` `ltac2` `tactic-language` `design`

**Referenced in:** [[interactive_proving]]

---

### Rocq Team — Ltac2 Documentation
**Citation:** Rocq Prover Documentation. Ltac2.

**URL:** https://rocq-prover.org/doc/V8.19.0/refman/proof-engine/ltac2.html

**Summary:** Official Ltac2 documentation covering type system, effects model, quotations, and FFI with Ltac1.

**Tags:** `coq` `ltac2` `documentation`

**Referenced in:** [[interactive_proving]]

---

### Czajka & Kaliszyk (2018) — Hammer for Coq
**Citation:** Czajka, Ł., & Kaliszyk, C. (2018). Hammer for Coq: Automation for Dependent Type Theory. *Journal of Automated Reasoning*, 61, 423-453.

**URL:** https://link.springer.com/article/10.1007/s10817-018-9458-4

**Summary:** CoqHammer architecture: translation to FOL, external ATP invocation, proof reconstruction. Achieves 39.1% success rate on Coq libraries with 87-97% reconstruction success.

**Tags:** `coqhammer` `coq` `ATP-integration` `proof-reconstruction`

**Referenced in:** [[interactive_proving]]

---

### Twelf Wiki — Theorem Prover
**Citation:** Twelf Project. Theorem Prover.

**URL:** https://twelf.org/wiki/theorem-prover/

**Summary:** Documentation on Twelf's theorem prover for ∀∃-statements, including %theorem, %prove, and relation to totality checking.

**Tags:** `twelf` `theorem-prover` `totality`

**Referenced in:** [[interactive_proving]]

---

### Twelf Wiki — Coverage Checking
**Citation:** Twelf Project. Coverage Checking.

**URL:** https://twelf.org/wiki/coverage-checking/

**Summary:** Explains input/output coverage in Twelf's totality checking: input coverage (exhaustiveness), output coverage (generality).

**Tags:** `twelf` `coverage` `totality`

**Referenced in:** [[interactive_proving]]

---

## Index by Tag (Extended)

### `LCF` / `trusted-kernel`
Milner (LCF), Gordon (2000), Harrison (HOL Light), Abrahamsson (Candle), Paulson (de Bruijn vs LCF)

### `sledgehammer` / `parallel-provers`
Paulson (Three Years), Paulson (Sledgehammer Tips), Isabelle Sledgehammer Guide

### `lean4` / `metaprogramming`
Lean Community (Metaprogramming Book)

### `coq` / `tactic-language`
Pédrot (Ltac2 Tactical Warfare), Rocq Team (Ltac2 Documentation), Czajka & Kaliszyk (CoqHammer)

### `twelf` / `totality`
Twelf Wiki (Theorem Prover, Coverage Checking), Pfenning & Schürmann (1999)

---

*Last updated: 2026-01-28*
