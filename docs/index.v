(*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(**
#
<body>
<h1>Coq mechanization of the Pattern Calculus for Rule
Languages</h1>
<h2>by <a href="mailto:shinnar@us.ibm.com">Avraham
Shinnar</a>, <a href="mailto:simeon@us.ibm.com">Jerome Simeon</a>, and
<a href="mailto:hirzel@us.ibm.com">Martin Hirzel</a></h2> <p>This
mechanization is meant as an accompaniment to the ECOOP 2015
paper(59): "A Pattern Calculus for Rule Languages: Expressiveness,
Compilation, and Mechanization".</p>

<p><b>WARNING: This documentation is outdated, and reflect early versions of the compiler.</b></p>

<p>It contains source files for a mechanization of the four languages
presented in the paper: CAMP (Calculus for Aggregating Matching
Patterns), Rules built on top of CAMP, NRA (Nested Relational Algebra)
and NNRC (Named Nested Relational Calculus).  Translations between all
three languages and their attendant proofs of correctness are
included. Additionally, type systems for all the languages and
bidirectional proofs of type preservation are verified.

This is all done using the semi-interactive theorem prover <a
href="http://coq.inria.fr/">Coq</a>.
</p>

<p>The mechanization includes proofs of all the theorems in the paper
except for the proof of NP-completeness of NNRC, for which we rely on
related work, and proofs of the time complexity of the various
compilers.</p>

<p>The mechanization also inclues various results (such as different
forms of subtyping for the type system) that are not required for the
paper but may be of interest to the reader.</p>

<h2>Building</h2>

To build the source, <a href="http://coq.inria.fr/download">Coq
8.4pl5</a> is required.  This is available for a number of platforms,
and can be obtained <a href="http://coq.inria.fr/download">here</a>.

The proofs can be built (type-checked/verified) by running make.

Note that building simply verifies the proofs, and is not otherwise
required to understand the development.

<h2>Relationship to the paper</h2>

<p>We give an overview of some of the main components in the code, as
well as their relationship to the paper. A full description of the
code structure is given in the following Section for completeness.</p>

<p>We focus here on the part of the code that is central to the paper:
the data model, the three languages presented (CAMP, NRA, NNRC), the
translations between them, and their type systems. We notably point to
the corresponding proofs of correctness for the key theorems.</p>

<p>For space and presentation purposes, the paper describes a subset
of what is available in the code, but the corresponding additions
should be relatively straightforward for the reader to
understand. Some of the notations in the code differ from those in the
paper to fit within the lexical constraints of Coq. We also point out
here some of those differences to facilitate the task of the
reader.</p>

<h3>Section 2: CAMP</h3>

<ul><li>Besides bags and records, the data model (Section 2.2, File <a
href="html/CAMP.Basic.Data.RData.html">Basic/Data/RData.v</a>) supports a
range of atomic types (natural numbers, booleans and strings), as well
as a notion of null value (denoted dunit in the code).</li>
<li>Unary and Binary Operators (Section 2.2, Definition 2.2, Files <a
href="html/CAMP.Basic.Operators.RUnaryOps.html">Basic/Operators/RUnaryOps.v</a>
and <a
href="html/CAMP.Basic.Operators.RBinaryOps.html">Basic/Operators/RBinaryOps.v</a>)
are shared among all the three languages. In addition to those
operators listed in the paper, the implementation includes a few
additional ones used in some code examples (e.g., distinct, sum, and,
or).</li>
<li>CAMP Patterns and their Semantics (Section 2.3, Definition 2.1,
and Figure 3, File <a
href="html/CAMP.Rules.Pattern.html">Rules/Pattern.v</a>). The definition
and semantics corresponds very directly to the text in the paper. One
important note is that patterns evaluation results not only in either
a match success or err (match failure), but also may return terminal
failures corresponding to cases where the semantics isn't
defined.</li>
</ul>

<h3>Section 3: Rules</h3>

<ul>
<li>Full rules and their Semantics (Section 3, Definition 3.1, Figures
7&amp;8, File <a href="html/CAMP.Rules.Rule.html">Rules/Rule.v</a>. Those
show how rules from a language similar to ILOG jRules can be encoded
in CAMP Patterns.</li> </ul>

<h3>Section 4: CAMP to NRA</h3>

<ul><li>The Nested Relational Algebra Syntax and Semantics (Section
4.1, Section 4.2, Figure 9, File <a
href="html/CAMP.NRA.Algebra.RAlg.html">NRA/Algebra/RAlg.v</a>) is identical
to the one in the paper. The reader interested in completeness and its
relationship to a real database algebra can consult the additional
code in <a
href="html/CAMP.NRA.Algebra.RAlgExt.html">NRA/Algebra/RAlgExt.v</a> which
encodes all operators (to the exception of a few specific joins that
involve null values) from [8] Cluet and Moerkotte. DBPL 1993.</li>
<li>The translation from CAMP to NRA and its proof of correctness
(Section 4.3, Section 4.4, Figure 10, and Theorem 4.2, File <a
href="html/CAMP.Translation.PatterntoNRA.html">Translation/PatterntoNRA.v</a>)
is provided along with additional corollaries derived from the main
lemma (pat_trans_correct). (pat_trans_top_correct_r) corresponds to
Theorem 4.2 and (pat_trans_size) to the proof for the result regarding
the size of the translation ().</li> </ul>

<h3>Section 5: NRA to NNRC</h3>

<ul><li>The Named Nested Relational Calculus Syntax and Semantics
(Section 5.1, Section 5.2, Definition 5.1, Figure 11, File <a
href="html/CAMP.NNRC.NNRC.html">NNRC/NNRC.v</a>) is identical to the one in
the paper.</li>
<li>The translation from NRA to NNRC and its proof of correctness
(Section 5.3, Section 5.4, Figure 12, Theorem 5.2. File <a
href="html/CAMP.Translation.NRAtoNNRC.html">Translation/NRAtoNNRC.v</a>) is
provided along with additional corollaries derived from the main theorem
(nra_sem_correct), and a proof for the result regarding the size of
the translation (nraToNNRC_size).</li> </ul>

<h3>Section 6: NNRC to CAMP</h3>

<ul><li>The translation from NNRC to CAMP and its proof of correctness
(Section 6.1, Figure 13, Section 6.2, Theorem 6.1. File <a
href="html/CAMP.Translation.NNRCtoPattern.html">Translation/NNRCtoPattern.v</a>)
is provided along with additional corollaries derived from the main
theorem (nrcToPat_let_sem_correct_top), and a proof for the result
regarding the size of the translation (nrcToPat_let_size).</li> </ul>

<h3>Section 7: Type Checking</h3>

<ul><li>Types (Section 7.1, File <a
href="html/CAMP.Basic.Typing.RType.html">Basic/Typing/RType.v</a>) carry
additional complexity in the code as it ensures that records are well
formed, i.e., that record fields are distinct. The types used
throughout the code carry a proof of well-formedness.</li>

<li>Typing for Data (Section 7.1, File <a
href="html/CAMP.Basic.Typing.TData.html">Basic/Typing/TData.v</a>, include
a large amount of code for reasoning about typed data which is used in
various proofs of type correctness throughout the code. An in-depth
understanding of that code isn't required on first reading.</li>
<li>Typing for unary and binary operators (Section 7.1, File <a
href="html/CAMP.Basic.Typing.TOps.html">Basic/Typing/TOps.v</a>) is
straightforward, and also includes proofs of type soudness as well as
typing rules for additional operators provided in the code.</li>
<li>Typing and type soudness theorems for CAMP are provided (Section
7.2, Figure 14, Theorem 7.1, File <a
href="html/CAMP.Rules.TPattern.html">Rules/TPattern.v</a>). The main lemma
(typed_pat_success_or_recoverable) appears slightly more involved that
for the other two languages as we need to account for the possibility
of recoverable erros. It essentially expresses that a well typed
pattern either succeeds with a value of the right type, or returns a
recoverable error.</li>
<li>Typing rules and a type soundness proof for NRA are provided
(Section 7.3, Figure 15, Theorem 7.2, File <a
href="html/CAMP.NRA.Typing.TAlg.html">NRA/Typing/TAlg.v</a>).</li>
<li>Typing rules and a type soundness proof for NNRC are provided
(Section 7.4, Figure 16, Theorem 7.3, File <a
href="html/CAMP.NNRC.TNRC.html">NNRC/TNRC.v</a>).</li>
<li>Mechanization for the type preservation theorem 7.4 is split into
three distinct parts, one for the translation from CAMP Patterns to
NRA (File <a
href="html/CAMP.Translation.TPatternToNRA.html">Translation/TPatternToNRA.v</a>),
one for the translation from NRA to NNRC (File <a
href="html/CAMP.Translation.TNRAtoNNRC.html">Translation/TNRAtoNNRC.v</a>),
one for the translation from NNRC back to CAMP Patterns (File <a
href="html/CAMP.Translation.TNNRCtoPattern.html">Translation/TNNRCtoPattern.v</a>). Those
include some of the mode involved part of the mechanization, but we
list the final theorem in each case at the end of the code for
convenience.</li> </ul>

<h2>Code Structure</h2>
Here we give a list of the files in the development, ordered bottom-up
(so dependencies are listed first), along with a description of
their content.  When applicable, we also indicate which
sections/theorems in the paper correspond to the content of a file.
<ul>
  <li>Basic: Basic definitions, lemmas, and utilities shared by all the language developments
  <ul>
    <li>Util: Basic definitions and properties (e.g. of lists and strings) that
    are not specific to our domain.
    <ul>
      <li>RLift.v: defines some basic operations to simplify writing
      computations with optional types.  These are variants of the
      monadic lift operator.</li>
      <li>RUtil.v: Basic operations and lemmas that are not specific
      to our work, but are generally useful.  Basically a dumping
      ground for miscellaneous stuff that is not specific to our domain.
      </li>
      <li>RList.v: Some lemmas about lists that are not in the
      standard library.  There are also assorted list lemmas in RUtil.v,
      the division is murky.</li>
      <li>RString.v: Defines various ascii string related operations.  This
      includes a total order for strings as well as methods to
      reversibly convert a number into an ascii string. </li>
      <li>RSort.v: Defines insertion_sort and a computational
      is_list_sorted predicate.  Proves theorems about their
      behavior.  Both are parameterized by the comparison relation.</li>
      <li>RRecSort.v: extends the sorting defined in RSort to sort a
      list of key/value pairs using the key, where the key is a string.</li>
    </ul>
  </li>
  <li>Data: Definition and properties of the shared data model.
  <ul>
    <li>RData.v: Defines the data model D (Section 2.1).
    <ul>
      <li>Defines the type of data, which includes</li>
      <li>Derives a stronger induction principle for data than the one automatically
      derived by Coq.</li>
      <li>Proves that equality of data is computable (and decidable) </li>
      <li>Defines a type class that enables simplified notation for
      lifting constants into data </li>
    </ul>
  </li>
  <li>RDataNorm.v: Defines a procedure to normalize data and verifies
  that it is correct.  In normalized data, all records are sorted by
  key. </li>
  <li>RBag.v: Defines many operations (and proofs about them) over
  bags represented as lists.</li>
  <li>RDomain.v: Defines various operations (and properties of them)
  that manipulate the domain of records represented as a lists of
  key/value pairs, where the key is a string</li>
  <li>RRelation.v: Defines operations various operations over
  records and over data.  Defines the compatible predicate and the
  merge_bindings operation defined in Section 2.1 and uses it to
  the "+" operation over records, called merge_bindings in the mechanization.</li>
  </ul>
</li>
<li>Operators: Definition and properties of the shared operators.
<ul>
  <li>RUtilOps.v: Utility methods used in the definition of some of
  the operators.  Includes a dataToString conversion routine. </li>
  <li>RUnaryOps.v: Defines the set of unary operators shared by
  all the languages (Definition 2). </li>
  <li>RUnaryOpsSem.v: Defines the semantics of unary
  operators. (Section 2.1).</li>
  <li>RBinnaryOps.v: Defines the set of binary operators shared by
  all the languages. (Definition 2). </li>
  <li>RBinaryOpsSem.v: Defines the semantics of binary
  operators. (Section 2.1).</li>
  <li>ROps.v: Helper file that re-exports the other modules,
  simplifying imports.</li>
</ul>
</li>
<li>Typing: Definition and development of types for data and operators. (Section 6.1)
<ul>
  <li>RType.v: Defines the structure of types
  <ul>
    <li>First defines rtyp<sub>0</sub> with accompanying constructors
    and induction principle.  These provide non-canonical types.</li>
    <li>Next defines the notion of a well formed type.  Record types
    contain a list of string/type pairs, mapping each field in the
    record to its type.  A type is well
    formed if all (including nested) records types have these lists
    sorted by key (in lexicographic order).</li>
    <li>Next, rtype is defined, which is a dependent pair of a base
    rtype<sub>0</sub> and a proof that it is well formed.</li>
    <li>"Smart" Constructors and induction / elimination principles
    are derived for rtype, enabling most reasoning to be one without
    "looking" at the underlying rtype<sub>0</sub>.</li>
    <li>Using well formed types simplifies later reasoning, ensuring
    that well typed records have unique keys (in sorted order).
    </li>
  </ul>
  </li>
  <li>TData.v: Defines data_type, the typing relation for data, and
  establishes some basic properties of the relation.  Also verifies
  that well-typed data is normalized. </li>
  <li>TDataInfer.v: Provides (and proves correct and complete)
  a type inference algorithm for data.</li>
  <li>TOps.v: Defines the typing relation for both unary and binary
  operators.  Proves that well-typed operators applied to data with
  appropriate types succeed with data of the associated type.</li>
  <li>Full: Defines a "full" join and subtype relation for the type
  system, which allows for width and depth subtyping for records.</li>
  <ul>
    <li>RJoin.v: Defines a total join operation that joins two types.
    The join operations is proven to be idempotent, commutative, and associative.
    </li>
    <li>RSubtype.v: Defines a subtyping relation on types, which is
    proven to be a preorder.</li>
    <li>RConsistentSubtype.v: Proves that the subtype relation and
    join relation are related.  In particular, subtype a b <-> join a b = b. </li>
    <li>RFullTyping.v: Convenience module that re-exports the other
    modules.</li>
  </ul>
  <li>TUnify.v: Provides a unify operation that takes two types and
  unifies structurally coresponding elements where one or both contain
  bottom.  This form of unification is partial, and only relates
  structurally similar types.  In particular, it does not enable
  "width" subtyping.  Also proves the when defined, unification is the
  same as "full" join (but unlike "full" join, it is not always defined).</li>
</ul>
</li>
</ul>
<li>Rules: Defines CAMP and the rule language (Sections 2 and 6.2)</li>
<ul>
  <li>Pattern.v: Defines the pattern language (Section 2)
  <ul>
    <li>As mentioned in the paper, the semantics are given computationally.</li>
    <li>To model the partiality of the rules (that they can get
    stuck), as well as the possibility for recoverable errors
    (<b>err</b>), the interpreter returns a presult.  A presult is either Success
    (with the answer), a TerminalError (with an error string for debugging), or a
    RecoverableError (with an error string for debugging)</li>
  </ul>
  <li>PatternExt.v: Defines useful derived patterns and notations. </li>
  <li>Rule.v: Defines the rule language (Section 2). </li>
  <li>PatSize.v: Defines a code size metric for CAMP patterns.</li>
  <li>TPattern.v: Defines the type system for CAMP and proves that
  well-typed CAMP programs, when run on appropriately typed data, in
  an appropriately typed context,
  evaluates to either a recoverable error (<b>err</b>) or to
  appropriately typed data. (Section 6.2 and Theorem 4)</li>
  <li>TPatternExt.v: Derives types for some of the derived patterns
  (defined in PatternExt.v)</li>
  <li>JPattern.v: provides some derived patterns useful for encoding
  java objects as records in our model</li>
  <li>PatternTest.v: Provides some useful for definitions for testing
  patterns
  <ul>
    <li>Defines the validate method, which checks if two lists of data
    are equivalent (upto permutation).  This is useful to check if the
    set of results from a rule are equivalent to the expected result
    (since the order of the results is not defined, as it is a set).</li>
    <li>Defines definitions and notations used in our unit tests</li>
  </ul>
</li>
  <li>JExample.v: provides some manually translated JRules, along with
  an encoding of the "official" result, and verifies that our
  interpreter yields the same result.</li>
</ul>
<li>NRA: The Nested Relational Algebra (Sections 3.1, 3.2, and 6.3)</li>
<ul>
  <li>Algebra: The NRA
  <ul>
    <li>RAlg.v: Defines our variant of the NRA and its semantics,
    along with a bunch of notations for NRA queries. (Sections 3.1
    and 3.2)</li>
    <li>RAlgEq.v: Defines an equivalence relation between NRA
    queries.  Two NRA queries are related under this equivalance if,
    for all input data, they both return the same result (or both
    fail to evaluate). </li>
    <li>RAlgExt.v: Defines various derived NRA queries.  These include
    forms of join, group by, and the unnesting operation introduced in
    Section 3.3. They are all defined using the base NRA operations.
    </li>
    <li>RAlgSize.v: Defines a code size metric for NRA queries</li>
  </ul>
  </li>
  <li>Typing: Type system for the NRA (Section 6.3)
  <ul>
    <li>TAlg.v: Type system for NRA queries. Proves that
    well-typed NRA queries, when run on appropriately typed data,
    successfully evaluate to an appropriately typed data. (Section 6.3
    and Theorem 5)</li>
    <li>TAlgEq.v: </li>
    <li>TDomain.v: Typed version of various record field and domain
    manipulating operations</li>
  </ul>
  </li>
  <li>Example
  <ul>
    <li>RExample.v: Some example NRA queries evaluated on sample data</li>
    <li>TExample.v: Some example well-typed NRA queries evaluated on well-typed data</li>
  </ul>
</li>

</ul>
<li>NNRC: The named nested relational calculus (Sections 4.1, 4.2, and
6.4)</li>
<ul>
  <li>NEnv.v: Defines the environment used by NNRC</li>
  <li>NNRC.v: Defined the syntax and semantics of NNRC expressions. </li>
  <li>NNRCSize.v: Defines a code size metric for NNRC expressions.</li>
  <li>Shadow.v: (touched upon in Section 5.2)
  <ul>
    <li>Defines free and bound variables of an NNRC expressions.</li>
    <li>Defines capture avoiding substitution for NNRC
    expressions. </li>
    <li>Defines various freshness conditions for NNRC and provides a
    way to generate a fresh variable, given a list of variables
    already used. </li>
    <li>Defines the shadow_free predicate, which asserts that an NNRC
    expression does not contain any shadowed bindings.</li>
    <li>Defines an unshadow transformation which transforms any NNRC
    expression into an equivalent one that does not contain any
    shadowed bindings. This transformation is proven
    semantics-preserving (and the output is proven to be shadow free).
    </li>
  </ul>
  </li>
  <li>TEnv.v: Defines type environments for NNRC (this is the type analogue of
  RType.v) </li>
  <li>TNRC.v: Type system for NNRC expressions queries. Proves that
    well-typed NNRC expressions queries, when run in an appropriately
  typed context successfully evaluate to appropriately typed
  data. (Section 6.4 and Theorem 6)</li>
  <li>TShadow.v: Proves that the unshadow tranformation is type preserving.</li>
</li>
</ul>
<li>Translation: Translations between the languages, as well as
their accompanying correctness and type preservation results.
<ul>
  <li>PatterntoNRA.v: <ul>
  <li>Defines the translation from CAMP to NRA (Section 3.3)</li>
  <li>Proves that the translation is semantics preserving (Section 3.4
  and Theorem 1)</li>
  <li>Proves that the translation results in code at most a constant
  factor larger than the input code. (Section 3.4)</li>
    </ul>
  </li>
<li>RuletoNRA.v: Extends the translation defined in PatterntoNRA.v to
  the rule framework. <ul>
<li>TPatternToNRA.v: Proves that the translation from CAMP to NRA is
  forward and backwards) type preserving (Section 6.5 and Theorem 7).</li>
<li>NRAtoNNRC.v: <ul>
  <li>Defines the translation from NRA to NNRC (Section 4.3)</li>
  <li>Proves that the translation is semantics preserving (Section 4.4
  and Theorem 2)</li>
  <li>Proves that the translation results in code at most a constant
  factor larger than the input code. (Section 4.4)</li>
</ul>
</li>
<li>TNRAtoNNRC.v: Proves that the translation from NRA to NNRC is
  forward and backwards) type preserving (Section 6.5 and Theorem 7).</li>
<li>NNRCtoPattern.v: <ul>
  <li>Defines the translation from NNRC to CAMP (Section 5.1)</li>
  <li>Proves that the translation is semantics preserving (Section 5.2
  and Theorem 3)</li>
  <li>Proves that the translation results in code at most a constant
  factor larger than the input code. (Section 5.2)</li>
</ul>
</li>
<li>TNNRCtoPattern.v: Proves that the translation from NNRC to CAMP is
  forward and backwards) type preserving (Section 6.5 and Theorem 7).</li>
</ul>
</li>
</ul>

<hr>
<address></address>
<!-- hhmts start -->Last modified: Tue Mar 10 12:00:28 EDT 2015 <!-- hhmts end -->
</body>
#
*)

