\documentclass[dvipsnames, fleqn]{jfp}
\usepackage{url}
\let\Bbbk\relax  % avoiding error "Bbbk' already defined."
\usepackage{tikz}
\usepackage{chngcntr} % for \counterwithout
\usepackage{caption}
\usepackage{subcaption}
\usepackage{scalerel}

%% lhs2Tex sublists.lhs | pdflatex --jobname=sublists

%if False
\begin{code}
import Prelude hiding (repeat)
(===) :: a -> a -> a
(===) = undefined

infixr 0 ===
\end{code}
%endif

%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include exists.fmt

%include common/Formatting.fmt

%%\email{scm@iis.sinica.edu.tw}

\usepackage{common/doubleequals}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}

\def\commentbegin{\quad$\{$~}
\def\commentend{$\}$}
\mathindent=\parindent
\addtolength{\mathindent}{0.3cm}
%\setlength{\mathindent}{0.8cm}
\allowdisplaybreaks

\newcommand{\tagx}[1][]{\refstepcounter{equation}(\theequation)\label{#1}}
\newcommand\numberthis{\refstepcounter{equation}\tag{\theequation}}


\counterwithout{equation}{section}

%format rep' (k) f = "{"f"}^{"k"}"

\begin{document}

\righttitle{Bottom-Up Computation Using Trees of Sublists}
\lefttitle{S-C. Mu}

\title{Bottom-Up Computation Using Trees of Sublists}
\begin{authgrp}
\author{Shin-Cheng Mu}
\affiliation{Institute of Information Science, Academia Sinica%\\
%Nankang, Taipei 11529, Taiwan
}
\end{authgrp}

\date{}
\journaltitle{JFP}
\cpr{Cambridge University Press}
\doival{yyyy/xxxxx}
\jnlDoiYr{2023}

\begin{abstract}
Some top-down problem specifications, if executed, may compute sub-problems repeatedly. Instead, we may want a bottom-up algorithm that stores solutions of sub-problems in a table to be reused.
How the table can be represented and efficiently maintained, however, can be tricky.
We study a special case: computing a function |h| taking lists as inputs such that |h xs| is defined in terms of all immediate sublists of |xs|.
Richard Bird studied this problem in 2008, and presented a concise but cryptic algorithm without much explanation.
We give this algorithm a proper derivation, and discovered a key property that allows it to work.
The algorithm builds trees that have certain shapes --- the sizes along the left spine is a prefix of a diagonal in Pascal's triangle.
The crucial function we derive transforms one diagonal to the next.
\end{abstract}

\maketitle[F]

\section{Introduction}

A list |ys| is said to be an \emph{immediate sublist} of |xs| if |ys| can be obtained by removing exactly one element from |xs|.
For example, the four immediate sublists of |"abcd"| are |"abc"|, |"abd"|, |"acd"|, and |"bcd"|.
%
Consider computing a function |h| that takes a list as input, with the property that the value of |h xs| depends on values of |h| at all the immediate sublists of |xs|.
%
For example, as seen in Figure \ref{fig:td-call-tree}, |h "abcd"| depends on |h "abc"|, |h "abd"|, |h "acd"|, and |h "bcd"|.
%
In this top-down manner, to compute |h "abc"| we make calls to |h "ab"|, |h "ac"|, and |h "bc"|; to compute |h "abd"|, we make a call to |h "ab"| as well --- many values end up being re-computed.
%
One would like to instead proceed in a bottom-up manner, storing computed values so that they can be reused.
%
For this problem, one might want to build a lattice-like structure, like that in Figure~\ref{fig:ch-lattice}, from bottom to top, such that each level reuses values computed in the level below it.

\begin{figure}[h]
\centering
\includegraphics[width=0.5\textwidth]{pics/td-call-tree.pdf}
\caption{Computing |h "abcd"| top-down. String constants are shown using monospace font but without quotes, to save space.}
\label{fig:td-call-tree}
\end{figure}

\cite{Bird:08:Zippy} presented a study of the relationship between top-down and bottom-up algorithms.
It was shown that if an algorithm can be written in a specific top-down style,
with ingredients that satisfy certain properties,
there is an equivalent bottom-up algorithm that stores intermediate results in a table.
The ``all immediate sublists'' instance was the last example of the paper.
To tackle the problem, however, Bird had to introduce, out of the blue, a binary tree and a concise but cryptic four-line function.
The tree appears to obey some shape constraints, but that was not explicitly stated.
Regarding the four-line function, which lies at the core of the bottom-up algorithm,
we know from its type that it turns a tree into a tree of lists,
and that is probably all one can say with confidence.
Not only is it hard to see what the function exactly does,
it is even not easy to see why the function, involving use of partial operations such as zipping trees of the same shape, always succeeds.
Given limited space, Bird did not offer much rationale or explanation, nor did he prove that the function satisfies the said properties that should be met by a bottom-up algorithm.

\begin{figure}
\centering
\includegraphics[width=0.85\textwidth]{pics/ch-lattice.pdf}
\caption{Computing |h "abcde"| bottom-up. The numbers on the left denote the levels.}
\label{fig:ch-lattice}
\end{figure}

The author finds this algorithm fascinating, and struggled to understand it.
As Bird would agree, a good way to understand an algorithm is to calculate it, thus this pearl came into being.
In this pearl we review this problem,
reveal a connection between ``|n| choose |k|'' and ``|n| choose |1+k|'' that was not explicit in \cite{Bird:08:Zippy},
motivate the introduction of the tree,
and finally construct a formal specification of the four-line function (which we call |up| in this pearl).
Once we have a specification, |up| can be calculated --- not without some tricky eureka that made the calculation fun.
It then turns out that there is a formula describing the role of |up| in the bottom-up algorithm that is different and simpler than that in \cite{Bird:08:Zippy}.

One might ask: are there actually such problems, whose solution of input |xs| depends on solutions of immediate sublists of |xs|?
It turns out that it is well-known in the algorithm community that,
while problems such as \emph{minimum edit distance} or \emph{longest common subsequence} are defined on two lists,
with clever encoding, they can be rephrased as problems defined on one list whose solution depends on immediate sublists.
Many problems in additive combinatorics \citep{TaoVu:12:Additive} can also be cast into this form.

But those are just bonuses.
The application of a puzzle is being solved, and a functional pearl is a story about solving a puzzle.
One sees a problem, wonders whether there is an elegant solution,
finds the right specification,
tries to calculate it,
encounters some head-scratching moments and surprising twists alone the way,
but eventually overcomes the obstacle and comes up with a concise and beautiful algorithm.
One then writes about the adventure, to share the fun.

%if False
\begin{code}
type L a = [a]
map' :: (a -> b) -> L a -> L b
map' = map
\end{code}
%endif

%%format map' = "\Varid{L}"
%format map' = map

\section{Specification}
\label{sec:spec}

We use a Haskell-like notation throughout the paper.
Like in Haskell, if a function is defined by multiple clauses, the patterns and guards are matched in the order they appear.
Differences from Haskell include that we allow |n+k| pattern, and that we denote the type of list by |L|,
equipped with its |map| function |map' :: (a -> b) -> L a -> L b|.
% Since we will use natural transformations and |map| a lot, for brevity we denote the |map| function of lists as |map' :: (a -> b) -> L a -> L b| (note that |map'| is written in italic font, to be distinguished from the type constructor |L|).

The immediate sublists of a list can be specified in many ways.
We use the definition below because it allows the proofs of this pearl to proceed in terms of cons-lists, which is familiar to most readers, while it also generates sublists in an order that is more intuitive:
% for the readers:
\begin{code}
subs :: L a -> L (L a)
subs []      = []
subs (x:xs)  = map' (x:) (subs xs) ++ [xs] {-"~~."-}
\end{code}
For example, |subs "abcde"| yields |["abcd","abce","abde","acde","bcde"]|.

Denote the function we wish to compute by |h :: L X -> Y| for some types |X| and |Y|.
We assume that it is a partial function defined on non-empty lists, and can be computed top-down as below:
%if False
\begin{code}
data X
data Y
f :: X -> Y
f = undefined
g :: L Y -> Y
g = undefined

type Nat = Int
\end{code}
%endif
\begin{code}
h :: L X -> Y
h [x]  = f x
h xs   = (g . map' h . subs) xs {-"~~,"-}
\end{code}
where |f :: X -> Y| is used in the base case when the input is a singleton list,
and |g :: L Y -> Y| is for the inductive case.
%The operator |($)| denotes function application, which binds looser than function composition |(.)|.
%We sometimes use |($)| to reduce the number of parentheses.

For this pearl, it is convenient to use an equivalent definition.
Let |td| (referring to ``top-down'') be a family of functions indexed by natural numbers (denoted by |Nat|):
\begin{spec}
td :: Nat -> L X -> Y
td 0      = f . ex
td (1+n)  = g . map' (td n) . subs {-"~~,"-}
\end{spec}
%if False
\begin{code}
td :: Nat -> L X -> Y
td 0  = f . ex
td n  = g . map' (td (n-1)) . subs {-"~~,"-}

ex :: L a -> a
ex [x] = x
\end{code}
%endif
Here the function |ex :: L a -> a| takes a singleton list and extracts the only component.
The intention is that |td n| is a function defined on lists of length exactly |1+n|.
The call |td n| in the body of |td (1+n)| is defined because |subs|, given an input of length |1+n|, returns lists of length |n|.
Given input |xs|, the value we aim to compute is |h xs = td (length xs - 1) xs|.
%This definition will be handy later.

The function |repeat k| composes a function with itself |k| times:
\begin{spec}
repeat :: Nat -> (a -> a) -> a -> a
repeat 0      f = id
repeat (1+k)  f = repeat k f . f {-"~~."-}
\end{spec}
%if False
\begin{code}
repeat :: Nat -> (a -> a) -> a -> a
repeat 0  f = id
repeat k  f = repeat (k-1) f . f {-"~~."-}

rep' :: Nat -> (a -> a) -> a -> a
rep' = repeat
\end{code}
%endif
For brevity, we will write |repeat k f| as |rep' k f| for the rest of this pearl.
We aim to construct a bottom-up algorithm having the following form:
\begin{spec}
bu n = post . rep' n step . pre {-"~~,"-}
\end{spec}
where |pre| preprocesses the input and builds the lowest level in Figure \ref{fig:ch-lattice},
and each |step| builds a level from the one below.
For input of length |1+n| we repeat |n| times and, by then, we can extract the singleton value by |post|.

Our aim is to construct |pre|, |step|, and |post| such that |td = bu|.

\section{Building a New Level}
\label{sec:build-level}

To find out what |step| might be, we need to figure out how to specify a level, and what happens when a level is built from the one below it.
We use Figure~\ref{fig:ch-lattice} as our motivating example.
As one can see, level |2| in Figure~\ref{fig:ch-lattice} consists of sublists of |"abcde"| that have length |2|, and level |3| consists of sublists having length |3|, etc.
Let |choose k xs| denote choosing |k| elements from the list |xs|:
\begin{spec}
choose :: Nat -> L a -> L (L a)
choose 0      _       =  [[]]
choose k      xs      |  k == length xs = [xs]
choose (1+k)  (x:xs)  =  map' (x:) (choose k xs) ++ choose (1+k) xs{-"~~."-}
\end{spec}
%if False
\begin{code}
choose :: Nat -> L a -> L (L a)
choose 0  _       =  [[]]
choose k  xs      |  k == length xs = [xs]
choose k  (x:xs)  =  map' (x:) (choose (k-1) xs) ++ choose k xs{-"~~."-}
\end{code}
%endif
Its definition follows basic combinatorics: the only way to choose |0| elements from a list is |[]|; if |length xs = k|, the only way to choose |k| elements is |xs|. Otherwise, to choose |1+k| elements from |x:xs|, one can either keep |x| and choose |k| from |xs|, or choose |1+k| elements from |xs|.
For example, |choose 3 "abcde"| yields
|["abc","abd","abe","acd","ace","ade","bcd","bce","bde","cde"]|.
Note that |choose k xs| is defined only when |k <= length xs|.
% Note also that, for non-empty inputs, |subs| is a special case of |choose| --- we have |subs xs = choose (length xs -1) xs| for non-empty |xs|, a property we will need later.

If the levels in Figure~\ref{fig:ch-lattice} were to be represented as lists,
each level |k| is given by |map' h (choose k xs)|.
For example, level |2| in Figure~\ref{fig:ch-lattice} is (string literals are shown in typewriter font; double quotes are omitted to reduce noise in the presentation):
%{
%subst string a = "\mathtt{" a "}"
\begin{spec}
map' h (choose 2 "abcde") = [h "ab", h "ac", h "ad", h "ae", h "bc", h "bd", h "be", h "cd", h "ce", h "de"] {-"~~."-}
\end{spec}
To build level |3| from level |2|,
we wish to have a function |upgrade :: L Y -> L (L Y)| that is able to somehow bring together the relevant entries from level |2|:
\begin{spec}
  upgrade (map' h (choose 2 "abcde")) =
   [[h "ab", h "ac", h "bc"], [h "ab", h "ad", h "bd"], [h "ab", h "ae", h "be"] ...] {-"~~."-}
\end{spec}
With |[h "ab", h "ac", h "bc"]| one can compute |h "abc"|, and with
|[h "ab", h "ad", h "bd"]| one can compute |h "abd"|, etc.
That is, if we apply |map' g| to the result of |upgrade| above, we get:
\begin{spec}
   [h "abc", h "abd", h "abe", h "acd"...] {-"~~,"-}
\end{spec}
which is level |3|, or |map' h (choose 3 "abcde")|.
The function |upgrade| need not inspect the values of each element, but rearrange them by position --- it is a natural transformation |L a -> L (L a)|.
As far as |upgrade| is concerned, it does not matter whether |h| is applied or not.
Letting |h = id|, observe that |upgrade (choose 2 "abcde") =|
|[["ab", "ac", "bc"], ["ab", "ad", "bd"]...]| and
|choose 3 "abcde" =|  |["abc", "abd", "abe", "acd"...]|
are related by |map' subs|.
%% Observe that, letting |h = id|, the lists |[["ab", "ac", "bc"], ["ab", "ad", "bd"]...]| and |["abc", "abd", "abe", "acd"...]| are related by |map' subs|.
%}
%% Furthermore, |upgrade| need not inspect the contents of its input ---
%% it can be a natural transformation |L a -> L (L a)|.
%% If such a function |upgrade| can be constructed,
Each |step| we perform in the bottom-up algorithm could be |map' g . upgrade|.

Formalising the observations above, we want |upgrade :: L a -> L (L a)| to satisfy:
\begin{equation}
\label{eq:up-spec-list}
\begin{split}
&  |(forall xs, k : 2 <= 1+k <= length xs :|\\
&   \qquad |upgrade (choose k xs) = map' subs (choose (1+k) xs)) {-"~~."-}|
\end{split}
\end{equation}
Given \eqref{eq:up-spec-list}, we may let each step in the bottom-up algorithm be |map' g . upgrade|.

Equation \eqref{eq:up-spec-list} is a specification of |upgrade|, constructed by observation and generalisation.
We want it to serve two purposes: 1. we wish to calculate from it a definition of |upgrade|, and 2. it plays a central role in proving that the bottom-up algorithm, also to be constructed, equals the top-down algorithm.
That \eqref{eq:up-spec-list} (in fact, a stronger version of it) does meet the purposes above will be formally justified later.
For now, we try to gain some intuition by demonstrating below that, with \eqref{eq:up-spec-list} satisfied, |map' g . upgrade| builds level |k+1| from level |k|.
Let the input be |xs|. If |xs| is a singleton list, the bottom-up algorithm has finished, so we consider |xs| having length at least |2|.
Recall that level |k| is |map' h (choose k xs)|. Applying |map' g . upgrade| to level |k|:
%if False
\begin{code}
upgrade :: L a -> L (L a)
upgrade = undefined

derUpgradeHelp :: Nat -> L X -> L Y
derUpgradeHelp k xs =
\end{code}
%endif
\begin{code}
    map' g (upgrade (map' h (choose k xs)))
 ===    {- |upgrade| natural -}
    map' g (map' (map' h) (upgrade (choose k xs)))
 ===    {- by \eqref{eq:up-spec-list}, |map|-fusion -}
    map' (g . map' h . subs) (choose (1+k) xs)
 ===    {- definition of |h| -}
    map' h (choose (1+k) xs) {-"~~."-}
\end{code}
We get level |1+k|.

The constraints on |k| in \eqref{eq:up-spec-list} may need some explanation.
For |choose (1+k) xs| on the RHS to be defined, we need |1+k <= length xs|.
%
Meanwhile, no |upgrade| could satisfy \eqref{eq:up-spec-list} when |k = 0|:
on the LHS, |upgrade| cannot distinguish between |choose 0 "ab"| and |choose 0 "abc"|,
both evaluating to |[[]]|, while on the RHS |choose 1 "ab"| and |choose 1 "abc"| have different shapes.
%
Therefore we only demand \eqref{eq:up-spec-list} to hold when |1 <= k|,
which is sufficient because we only apply |upgrade| to level |1| and above.
Together, the constraint is |2 <= 1+k <= length xs| --- |xs| should have at least |2| elements.

Can we construct such an |upgrade|?

\section{Building Levels Represented By Trees}

We may proceed with \eqref{eq:up-spec-list} and construct |upgrade|.
We will soon meet a small obstacle: in an inductive case
|upgrade| will receive a list computed by |choose (1+k) (x:xs)| that
needs to be split into |map' (x:) (choose k xs)| and |choose (1+k) xs|.
This can be done, but it is rather tedious.
%
This is a hint that some useful information has been lost when we represent levels by lists.
To make the job of |upgrade| easier, we switch to a more informative data structure.

\subsection{Binomial Trees}

Instead of lists, we define the following tip-valued binary tree:
\begin{code}
data B a = T a | N (B a) (B a) {-"~~."-}
\end{code}
We assume that |B| is equipped with two functions derivable from its definition:
\begin{spec}
mapB   :: (a -> b) -> B a -> B b {-"~~,"-}
zipBW  :: (a -> b -> c) -> B a -> B b -> B c {-"~~."-}
\end{spec}
%if False
\begin{code}
mapB   :: (a -> b) -> B a -> B b {-"~~,"-}
mapB = undefined
zipBW  :: (a -> b -> c) -> B a -> B b -> B c {-"~~."-}
zipBW = undefined
\end{code}
%endif
The function |mapB f| applies |f| to every tip of the given tree.
% Like that with lists, we also write |mapB| as $\Varid{B}$.
Given two trees |t| and |u| having the same shape,
|zipBW f t u| ``zips'' the trees together, applying |f| to values on the tips --- the name stands for ``zip |B|-trees with''.
If |t| and |u| have different shapes, |zipBW f t u| is undefined.
Furthermore, for the purpose of specification we assume a function |flatten :: B a -> L a| that ``flattens'' a tree to a list by collecting all the values on the tips left-to-right.

%%format mapB = "\Varid{B}"

Having |B| allows us to define an alternative to |choose|:
\begin{spec}
ch :: Nat -> L a -> B (L a)
ch 0      _       =  T []
ch k      xs      |  k == length xs = T xs
ch (1+k)  (x:xs)  =  N (mapB (x:) (ch k xs)) (ch (1+k) xs) {-"~~."-}
\end{spec}
%if False
\begin{code}
ch :: Nat -> L a -> B (L a)
ch 0  _       =  T []
ch k  xs      |  k == length xs = T xs
ch k  (x:xs)  =  N (mapB (x:) (ch (k-1) xs)) (ch k xs) {-"~~."-}
\end{code}
%endif
The function |ch| resembles |choose|.
In the first two clauses, |T| corresponds to a singleton list.
In the last clause, |ch| is like |choose| but, instead of appending the results of the two recursive calls, we store the results in the two branches of the binary tree, thus recording how the choices were made:
if |ch _ (x:xs) = N t u|, the subtree |t| contains all the tips with |x| chosen, while |u| contains all the tips with |x| discarded.
See Figure~\ref{fig:ch-examples} for some examples.
We have |flatten (ch k xs) = choose k xs|, that is, |choose| forgets the information retained by |ch|.

\begin{figure}
\centering
\begin{subfigure}[b]{0.25\textwidth}
  \centering
  \includegraphics[width=0.6\textwidth]{pics/ch-1-5.pdf}
  \caption{|ch 1 "abcde"|.}
  \label{fig:ch-1-5}
\end{subfigure}
%\hfill
\qquad
\begin{subfigure}[b]{0.45\textwidth}
  \centering
  \includegraphics[width=0.8\textwidth]{pics/ch-3-5.pdf}
  \caption{|ch 3 "abcde"|.}
  \label{fig:ch-3-5}
\end{subfigure}
\caption{Results of |ch|.}
\label{fig:ch-examples}
\end{figure}

The counterpart of |upgrade| on trees, which we will call |up|, will be a natural transformation of type |B a -> B (L a)|.
Its relationship to |upgrade| is given by |flatten (up (ch k xs)) = upgrade (choose k xs)|.
The function |up| should satisfy the following specification:
\begin{equation}
\label{eq:up-spec-B}
\begin{split}
&  |(forall xs, k: 2 <= 1+k <= length xs| \,: \\
&   \qquad |up (ch k xs) = mapB subs (ch (1+k) xs) ){-"~~."-}|
\end{split}
\end{equation}
%if False
\begin{code}
up_ch_subs :: Nat -> L a -> B (L (L a))
up_ch_subs k xs =
    up (ch k xs) === mapB subs (ch (1+k) xs)
\end{code}
%endif
It is a stronger version of \eqref{eq:up-spec-list} --- \eqref{eq:up-spec-B} reduces to \eqref{eq:up-spec-list} if we apply |flatten| to both sides.

Now we are ready to derive |up|.

\subsection{The Derivation}
\label{sec:up-derivation}

The derivation proceeds by trying to construct a proof of \eqref{eq:up-spec-B} and, when stuck, pausing to think about how |up| should be defined to allow the proof to go through.
That is, the definition of |up| and a proof that it satisfies \eqref{eq:up-spec-B} are developed hand-in-hand.

The proof, if constructed, will be an induction on |xs|.
The case analysis follows the shape of |ch (1+k) xs| (on the RHS of \eqref{eq:up-spec-B}).
Therefore, there is a base case, a case when |xs| is non-empty and |1+k = length xs|, and a case when |1+k < length xs|.
However, since the constraints demand that |xs| has at least two elements, the base case will be lists of length |2|, and in the inductive cases the length of the list will be at least |3|.

\paragraph*{Case 1.~~} |xs := [y,z]|.\footnote{The (|:=|) denotes substitution: we mean that the property being proved is \eqref{eq:up-spec-B} with |[y,z]| substituted for |xs|.}\\
The constraints force |k| to be |1|.
We simplify the RHS of \eqref{eq:up-spec-B}:
%if False
\begin{code}
derUp1R :: a -> a -> B (L (L a))
derUp1R y z =
\end{code}
%endif
\begin{code}
    mapB subs (ch 2 [y,z])
  ===  {- def. of |ch| -}
    mapB subs (T [y,z])
  ===  {- def. of |mapB| and |subs| -}
    T [[y],[z]] {-"~~."-}
\end{code}
Now consider the LHS:
%if False
\begin{code}
derUp1L :: a -> a -> B (L (L a))
derUp1L y z =
\end{code}
%endif
\begin{code}
    up (ch 1 [y,z])
  ===  {- def. of |ch| -}
    up (N (T [y]) (T [z])) {-"~~."-}
\end{code}
The two sides can be made equal if we let |up (N (T p) (T q)) = T [p,q]|.

\paragraph*{\bf Case 2.~~} |xs := x:xs| where |length xs >= 2|, and |1+k = length (x:xs)|.\\
We leave details of this case to the readers as an exercise, since we would prefer giving more attention to the next case.
For this case we will construct
\begin{spec}
up (N t (T q)) = T (unT (up t) ++ [q]) {-"~~."-}
\end{spec}
In this case, |up t| always returns a |T|.
The function |unT (T p) = p| removes the constructor and exposes the list it contains.
While the correctness of this case is established by the constructed proof, a complementary explanation why |up t| always returns a singleton tree and thus |unT| always succeeds is given in Section~\ref{sec:deptypes}.

\paragraph*{\bf Case 3.~~} |xs := x:xs|, |k := 1+k|, where |length xs >= 2|, and |1+(1+k) < length (x:xs)|.
\\
The constraints become |2 <= 2+k < length (x:xs)|.
Again we start with the RHS, and try to reach the LHS:
%if False
\begin{code}
derUp3R :: Nat -> a -> L a -> B (L (L a))
derUp3R k x xs =
\end{code}
% code hidden and duplicated to allow numbering
\begin{code}
     mapB subs (ch (2+k) (x:xs))
   ===   {- def. of |ch|, since |2+k < length (x:xs)| -}
     mapB subs (N (mapB (x:) (ch (1+k) xs)) (ch (2+k) xs))
   ===   {- def. of |mapB|, |mapB|-fusion -}
     N (mapB (subs . (x:)) (ch (1+k) xs)) (mapB subs (ch (2+k) xs))
   ===   {- induction -}
     N (mapB (subs . (x:)) (ch (1+k) xs)) (up (ch (1+k) xs)) {-"~~."-}
\end{code}
%endif
\addtolength\jot{-2.2pt}
\begin{align*}
  & |mapB subs (ch (2+k) (x:xs))| \\
=~& \mbox{\quad\{ def. of |ch|, since |2+k < length (x:xs)| \}} \\
  & |mapB subs (N (mapB (x:) (ch (1+k) xs)) (ch (2+k) xs))| \\
=~& \mbox{\quad\{ def. of |mapB|, |mapB|-fusion \}}\\
  & |N (mapB (subs . (x:)) (ch (1+k) xs)) (mapB subs (ch (2+k) xs))|\\
=~& \mbox{\quad\{ induction \}}\\
  & |N (mapB (subs . (x:)) (ch (1+k) xs)) (up (ch (1+k) xs))|
    \mbox{~~.} \numberthis \label{eq:up3R}
\end{align*}
\addtolength\jot{2.2pt}%
Note that the induction step is valid because we are performing induction on |xs|, and thus |k| in \eqref{eq:up-spec-B} is universally quantified.
We now look at the LHS:
%if False
\begin{code}
derUp3L :: Nat -> a -> L a -> B (L (L a))
derUp3L k x xs =
\end{code}
% code hidden and duplicated to allow numbering
\begin{code}
   up (ch (1+k) (x:xs))
 ===   {- def. of |ch|, since |1+k < length (x:xs)| -}
   up (N (mapB (x:) (ch k xs)) (ch (1+k) xs)) {-"~~."-}
\end{code}
%endif
\addtolength\jot{-2.2pt}
\begin{align*}
  & |up (ch (1+k) (x:xs))| \\
=~& \mbox{\quad\{ def. of |ch|, since |1+k < length (x:xs)| \}}\\
  & |up (N (mapB (x:) (ch k xs)) (ch (1+k) xs))|
     \mbox{~~.} \numberthis \label{eq:up3L}
\end{align*}
\addtolength\jot{2.2pt}%
Expressions \eqref{eq:up3R} and \eqref{eq:up3L} can be unified if we define
\begin{spec}
     up (N t u) = N ??? (up u) {-"~~."-}
\end{spec}
The missing part |???| shall be an expression that is allowed to use only the two subtrees |t| and |u| that |up| receives.
Given |t = mapB (x:) (ch k xs)| and |u = ch (1+k) xs| (from \eqref{eq:up3L})
this expression shall evaluate to the subexpression in \eqref{eq:up3R} (let us call it (\ref{eq:up3R}.1)):
\begin{equation*}
    |mapB (subs . (x:)) (ch (1+k) xs) {-"~~."-}| \tag{\ref{eq:up3R}.1}
\end{equation*}

It may appear that, now that |up| already has |u = ch (1+k) xs|, the |???| may simply be |mapB (subs . (x:)) u|. The problem is that the |up| does not know what |x| is --- unless |k = 0|.

\paragraph*{Case 3.1.~~} |k = 0|.
We can recover |x| from |mapB (x:) (ch 0 xs)| if |k| happens to be |0| because:
%if False
\begin{code}
derUp31a :: a -> L a -> B (L a)
derUp31a x xs =
\end{code}
%endif
\begin{code}
          mapB (x:) (ch 0 xs)
     ===  mapB (x:) (T [])
     ===  T [x] {-"~~."-}
\end{code}
That is, the left subtree |up| receives must have the form |T [x]|,
from which we can retrieve |x| and apply |mapB (subs . (x:))| to the other subtree.
We can furthermore simplify |mapB (subs . (x:)) (ch (1+0) xs)| a bit:
%if False
\begin{code}
derUp31b :: a -> L a -> B (L (L a))
derUp31b x xs =
\end{code}
%endif
\begin{code}
          mapB (subs . (x:)) (ch (1+0) xs)
     ===  mapB (\q -> [[x],q]) (ch 1 xs) {-"~~."-}
\end{code}
The equality above holds because every tip in |ch 1 xs| contains singleton lists and, for a singleton list |[z]|, we have |subs (x:[z]) = [[x],[z]]|.
In summary, we have established
\begin{spec}
      up (N (T p) u) = N (mapB (\q -> [p,q]) u) (up u) {-"~~."-}
\end{spec}

\paragraph*{Case 3.2.~~} |0 < k| (and |k < length xs - 1|).
In this case, we have to construct (\ref{eq:up3R}.1), that is |mapB (subs . (x:)) (ch (1+k) xs)|, out of the two subtrees, |mapB (x:) (ch k xs)| and |ch (1+k) xs|, without knowing what |x| is.

What follows is perhaps the most tricky part of the derivation.
Starting from |mapB (subs . (x:)) (ch (1+k) xs)|,
we expect to use induction somewhere, therefore a possible strategy is to move |mapB subs| rightwards, next to |ch|, in order to apply \eqref{eq:up-spec-B}.
Let us consider |mapB (subs . (x:)) u| for a general |u|, and try to move |mapB subs| next to |u|.
%
\begin{itemize}
\item By definition, |subs (x:xs) = map' (x:) (subs xs) ++ [xs]|.
That is, |subs . (x:) = \xs -> snoc (map' (x:) (subs xs)) xs| ---
it duplicates the argument |xs| and applies |map' (x:) . subs| to one of them, before calling |snoc|.
\item |mapB (subs . (x:))| does the above to \emph{each} value in the tree |u|.
\item Equivalently, we may also duplicate each values in u to pairs, before applying |\(xs,xs') -> snoc (map' (x:) (subs xs)) xs'| to each pair.
\item Values in |u| can be duplicated by zipping |u| to itself, that is, |zipBW (\xs -> (xs,xs)) u u|.
\end{itemize}
With the idea above in mind, we calculate:
\begin{spec}
     mapB (subs . (x:)) u
===    {- definition of |subs| -}
     mapB (\xs -> snoc (map' (x:) (subs xs)) xs) u
===    {- discussion above -}
     mapB (\(xs,xs') -> snoc (map' (x:) (subs xs)) xs') (zipBW (\xs -> (xs,xs)) u u)
===    {- |zipBW| natural -}
     zipBW snoc (mapB (map' (x:) . subs) u) u {-"~~."-}
\end{spec}
We have shown that
\begin{equation}
\label{eq:map-sub-zipBW}
  |mapB (subs . (x:)) u = zipBW snoc (mapB (map' (x:) . subs) u) u {-"~~,"-}|
\end{equation}
which brings |mapB subs| next to |u|.
The naturality of |zipBW| in the last step is the property that,
provided that |h (f x y) = k (g x) (r y)|, we have:
\begin{spec}
  mapB h (zipBW f t u) = zipBW k (mapB g t) (mapB r u) {-"~~."-}
\end{spec}

Back to (\ref{eq:up3R}.1), we may then calculate:
%if False
\begin{code}
derUp32 :: Nat -> a -> L a -> B (L (L a))
derUp32 k x xs =
\end{code}
%endif
\begin{code}
        mapB (subs . (x:)) (ch (1+k) xs)
    ===   {- by \eqref{eq:map-sub-zipBW} -}
        zipBW snoc  (mapB (map' (x:) . subs) (ch (1+k) xs)) (ch (1+k) xs)
    ===   {- induction -}
        zipBW snoc  (mapB (map' (x:)) (up (ch k xs))) (ch (1+k) xs)
    ===   {- |up| natural -}
        zipBW snoc (up (mapB (x:) (ch k xs))) (ch (1+k) xs) {-"~~."-}
\end{code}
Recall that our aim is to find a suitable definition of |up| such that \eqref{eq:up3R} equals \eqref{eq:up3L} .
The calculation shows that we may let
\begin{spec}
       up (N t u) = N (zipBW snoc (up t) u) (up u) {-"~~."-}
\end{spec}
% Note that the induction step is allowed in this case, but not in the |k = 0| case above. The latter violates the constraint |1 <= k|.

In summary, we have constructed:
\begin{code}
up :: B a -> B (L a)
up (N (T p)  (T q)  ) = T [p,q]
up (N t      (T q)  ) = T (snoc (unT (up t)) q)
up (N (T p)  u      ) = N (mapB (\q -> [p,q]) u) (up u)
up (N t      u      ) = N (zipBW snoc (up t) u) (up u) {-"~~,"-}
\end{code}
%if False
\begin{code}
snoc :: L a -> a -> L a
snoc xs x = xs ++ [x]

unT (T x) = x
\end{code}
%endif
which is the mysterious four-line function in \cite{Bird:08:Zippy}!
There is only one slight difference: where we use |snoc|, Bird used |(:)|, which has an advantage of being more efficient.
Had we specified |subs| and |choose| differently, we would have derived the |(:)| version, but either the proofs so far would have to proceed in terms of snoc lists, or the sublists in our examples would come in a less intuitive order.
For clarity, we chose to present this version.
For curious readers, code of the |(:)| version of |up| is given in Appendix~\ref{sec:up-cons}.

\begin{figure}[th]
\centering
\includegraphics[width=0.9\textwidth]{pics/up-2-3-demo.pdf}
\caption{Applying |mapB g {-"\mathrel{\scalebox{0.6}{$\circ$}}"-} up| to |mapB h (ch 2 "abcde")|. We abbreviate |zipBW snoc| to |zip|.}
\label{fig:up-2-3-demo}
\end{figure}

%format t0
%format t1
%format t2
%format t3
%format u0
%format u1
%format u2
%format u3

\paragraph*{An Example.}~~
To demonstrate how |up| works, shown at the bottom of Figure~\ref{fig:up-2-3-demo} is the tree built by |mapB h (ch 2 "abcde")|.
If we apply |up| to this tree,
the fourth clause of |up| is matched, and we traverse along its right spine until reaching |t0|,
which matches the second clause of |up|, and a singleton tree containing |[h "cd", h "ce", h "de"]| is generated.

Traversing backwards, |up t1| generates |u0|, which shall have the same shape as |t0| and can be zipped together to form |u1|. Similarly, |up t3| generates |u2|, which shall have the same shape as |t2|. Zipping them together, we get |u3|. They constitute |mapB h (ch 3 "abcde")|, shown at the top of Figure~\ref{fig:up-2-3-demo}.

\subsection{Interlude: Shape Constraints with Dependent Types}
\label{sec:deptypes}

While the derivation guarantees that the function |up|, as defined above, satisfies \eqref{eq:up-spec-B}, the partiality of |up| still makes one uneasy.
Why is it that |up t| in the second clause always returns a |T|?
What guarantees that |up t| and |u| in the last clause always have the same shape and can be zipped together?
In this section we try to gain more understanding of the tree construction with the help of dependent types.

%% Agda stuffs
%{
%format T0
%format Tn = "\Conid{T}_{\Varid{n}}"
%format unTn = "\Varid{unT}_{\Varid{n}}"
%format Nat = "\mathbb{N}"
%format bot = "{\bot}"

Certainly, |ch| does not generate all trees of type |B|, but only those trees having certain shapes.
We can talk about the shapes formally by annotating |B| with indices, as in the following Agda datatype:
\begin{spec}
data B (a : Set) : Nat -> Nat -> Set where
  T0  : a -> B a 0 n
  Tn  : a -> B a (1 + n) (1 + n)
  N   : B a k n -> B a (1 + k) n -> B a (1 + k) (1 + n) {-"~~."-}
\end{spec}
The intention is that |B a k n| is the tree representing choosing |k| elements from a list of length |n|.
Notice that the changes of indices in |B| follow the definition of |ch|.
We now have two base cases, |T0| and |Tn|, corresponding to choosing |0| elements and all elements from a list.
A tree |N t u : B a (1+k) (1+n)| represents choosing |1+k| elements from a list of length |1+n|, and the two ways to do so are |t : B a k n| (choosing |k| from |n|) and |u : B a (1+k) n| (choosing |1+k| from |n|).
With the definition, |ch| may have type
\begin{spec}
ch : (k : Nat) -> {n : Nat} -> k <= n -> Vec a n -> B (Vec a k) k n {-"~~,"-}
\end{spec}
where |Vec a n| denotes a list (vector) of length |n|.

One can see that a pair of |(k,n)| uniquely determines the shape of the tree.
Furthermore, one can also prove that |B a k n -> k <= n|, that is,
if a tree |B a k n| can be built at all, it must be the case that |k <= n|.
% \begin{spec}
% bounded    : B a k n        -> k <= n  {-"~~."-}
% \end{spec}

The Agda implementation of |up| has the following type:
\begin{spec}
up : 0 < k -> k < n -> B a k n -> B (Vec a (1 + k)) (1 + k) n {-"~~."-}
\end{spec}
The type states that it is defined only for |0 < k < n|;
the shape of its input tree is determined by |(k,n)|; the output tree has shape determined by |(1+k,n)|, and the values in the tree are lists of length |1+k|.
One can also see from the types of its components that, for example, the two trees given to |zipBW| always have the same shape.
More details are given in Appendix~\ref{sec:agda:up}.

In {\bf Case 2} of Section~\ref{sec:up-derivation} we saw a function |unT|.
Its dependently typed version has type |B a (1 + n) (1 + n) -> a|.
It always succeeds because a tree having type |B a (1+n) (1+n)| must be constructed by |Tn| --- for |N t u| to have type |B a (1+n) (1+n)|, |u| would have type |B a (1+n) n|, an empty type.

Dependent types help us rest assured that the ``partial'' functions we use are actually safe.
The current notations, however, are designed for interactive theorem proving, not program derivation.
The author derives program on paper by equational reasoning in a more concise notation, and double-checks the details by theorem prover afterwards.
All the proofs in this pearl have been translated to Agda.%
\footnote{Available at \url{https://github.com/scmu/sublists/tree/main/supplement/Agda}~.}
For the rest of the pearl we switch back to non-dependently typed equational reasoning.

%\begin{figure}
%\centering
%%{
%\newcommand{\dash}{{\text{-}}}
%%format sses = "\scaleobj{0.8}{\mathsf{s{\leq}s}}"
%%format ssesi = "\scaleobj{0.8}{\mathsf{s{\leq}s}^{-1}}"
%%format zsen = "\scaleobj{0.8}{\mathsf{z{\leq}n}}"
%%format zsz = "\scaleobj{0.8}{0{\small <}0}"
%%format snssn = "\scaleobj{0.8}{1{+}n\!<\!1{+}n}"
%%format ssnsssn = "\scaleobj{0.8}{2{+}n\!<\!2{+}n}"
%%format skssn = "\scaleobj{0.8}{1{+}k\!<\!1{+}n}"
%%format ssksssn = "\scaleobj{0.8}{2{+}k\!<\!2{+}n}"
%%format botelim = "{\bot}\dash\Varid{elim}"
%%format serefl = "\scaleobj{0.8}{{\leq}\dash\Varid{refl}}"
%%format sirrefl = "\scaleobj{0.8}{{<}\dash\Varid{irrefl}}"
%%format (pf x) = "\textcolor{Tan}{" x "}"
%{\small
%\begin{spec}
%up : pf (0 < k) -> pf (k < n) -> B a k n -> B (Vec a (suc k)) (suc k) n
%up (pf zsz)    _    (T0 x)        = pf botelim (pf (sirrefl refl zsz))
%up _  (pf snssn)    (Tn x)        = pf botelim (pf (sirrefl refl snssn))
%up _  (pf ssnsssn)  (N (Tn _) _)  = pf botelim (pf (sirrefl refl ssnsssn))
%
%up _  _            (N (T0 p)     (Tn q)      )  = Tn (p :: q :: [])
%up _  _            (N t@(N _ _)  (Tn q)      )  = Tn (snoc (unTn (up (pf (sses zsen)) (pf (sses serefl)) t)) q)
%up _  _            (N (T0 p)     u@(N _ u')  )  = N  (mapB (\ q -> p :: q :: []) u)
%                                                     (up (pf serefl) (pf (sses (bounded u'))) u)
%up _ (pf ssksssn)  (N t@(N _ _) u@(N _ u'))     = N  (zipBW snoc (up (pf (sses zsen)) (pf (ssesi ssksssn)) t) u)
%                                                     (up (pf (sses zsen)) (pf (sses (bounded u'))) u)
%\end{spec}
%}
%%}
%\caption{An Agda implementation of |up|.}
%\label{fig:up-agda}
%\end{figure}
%}
%% Agda stuffs

\begin{figure}[t]
\centering
\includegraphics[width=0.8\textwidth]{pics/pascal-tri.pdf}
\caption{Sizes of |B| alone the right spine correspond to prefixes of diagonals in Pascal's Triangle.}
\label{fig:pascal-tri}
\end{figure}

\paragraph*{Pascal's Triangle.}~~
With so much discussion about choosing, it is perhaps not surprising that the sizes of subtrees along the right spine of a |B| tree correspond to prefixes of diagonals in Pascal's Triangle.
After all, the |k|-th diagonal (counting from zero) in Pascal's Triangle denotes binomial coefficients --- the numbers of ways to choose |k| elements from |k|, |k+1|, |k+2|... elements.
This is probably why \cite{Bird:08:Zippy} calls the data structure a \emph{binomial tree}, hence the name |B|.
\footnote{It is not directly related to the tree, having the same name, used in \emph{binomial heaps}.}
See Figure~\ref{fig:pascal-tri} for example.
The sizes along the right spine of |ch 2 "abcde"|, that is, |10,6,3,1|, is the second diagonal (in orange), while the right spine of |ch 3 "abcde"| is the fourth diagonal (in blue).
Applying |up| to a tree moves it rightwards and downwards.
In a sense, a |B| tree represents a prefix of a diagonal in Pascal's Triangle \emph{with a proof} of how it is constructed.

\section{The Bottom-Up Algorithm}

Now that we have constructed an |up| that satisfies \eqref{eq:up-spec-B}, it is time to derive the main algorithm.
%
Recall that we have defined, in Section~\ref{sec:spec}, |h xs = td (length xs - 1) xs|, where
\begin{spec}
td :: Nat -> L X -> Y
td 0      = f . ex
td (1+n)  = g . map' (td n) . subs {-"~~."-}
\end{spec}
The intention is that |td n| is a function defined for inputs of length exactly |1+n|.
%Notice that |subs :: L a -> L (L a)| can be seen as a special case of |choose|. That is, if we define |flatten :: B a -> L a| that flattens a tree into a list, we have |subs xs = flatten (ch n xs)|, where |xs| non-empty and |length xs = 1 + n|.
We also define a variation:
\begin{spec}
td' :: Nat -> L Y -> Y
td' 0      = ex
td' (1+n)  = g . map' (td' n) . subs {-"~~."-}
\end{spec}
%if False
\begin{code}
td' :: Nat -> L Y -> Y
td' 0  = ex
td' n  = g . map' (td' (n-1)) . subs {-"~~."-}
\end{code}
%endif
The difference is that |td'| calls only |ex| in the base case.
It takes only a routine induction to show that |td n = td' n . map' f|.
All the calls to |f| are thus factored to the beginning of the algorithm.
We may then focus on transforming |td'|.

Note that for |ch n xs| where |n = length xs| always results in |T xs|.
That is, we have
\begin{equation}
\label{eq:ch-all}
|unT (ch n xs) = xs| \mbox{~~, where~} |n = length xs| \mbox{.}
\end{equation}

Our main theorem is that
\begin{theorem} \label{thm:td-bu}
For all |n :: Nat| we have |td n = bu n|, where
\begin{code}
bu n = unT . rep' n (mapB g . up) . mapB ex . ch 1 . map' f {-"~~."-}
\end{code}
\end{theorem}
\noindent That is, the top-down algorithm |td n| is equivalent to a bottom-up algorithm |bu n|, where the input is preprocessed by |mapB ex . ch 1 . map' f|, followed by |n| steps of |mapB g . up|. By then we will have a singleton tree, whose content can be extracted by |unT|.
\begin{proof}
Let |length xs = 1 + n|. We reason:
%if False
\begin{code}
derMain :: Nat -> L X -> Y
derMain n xs =
\end{code}
%endif
\begin{code}
   td n xs
 ===   {- since |td n = td' n . map' f| -}
   (td' n . map' f) xs
 ===   {- by \eqref{eq:ch-all} -}
   (td' n . unT . ch (1+n) . map' f) xs
 ===   {- naturality of |unT| -}
   (unT . mapB (td' n) . ch (1+n) . map' f)  xs
 ===    {- Lemma~\ref{lma:main} -}
   (unT . rep' n (mapB g . up) . mapB ex . ch 1 . map' f) xs
 ===    {- definition of |bu| -}
   bu n xs {-"~~."-}
\end{code}
\end{proof}

The real work is done in Lemma~\ref{lma:main} below. It shows that |mapB (td' n) . ch (1+n)| can be performed by processing the input by |mapB ex . ch 1|, before |n| steps of |mapB g . up|.
This is the key lemma that relates \eqref{eq:up-spec-B} to the main algorithm.
\begin{lemma}\label{lma:main}
For inputs of length |1+n| (|n > 1|), we have
\begin{equation*}
|mapB (td' n) . ch (1+n) = rep' n (mapB g . up) . mapB ex . ch 1| \mbox{~~.}
\end{equation*}
\end{lemma}
\begin{proof}
For |n := 0| both sides simplify to |mapB ex . ch 1|. For |n := 1 + n|, we start from the LHS, assuming an input of length |2+n|:
%if False
\begin{code}
derLma :: Nat -> L Y -> B Y
derLma n =
\end{code}
%endif
\begin{code}
     mapB (td' (1+n)) . ch (2+n)
 ===    {- def. of |td'| -}
     mapB (g . map' (td' n) . subs) . ch (2+n)
 ===    {- by \eqref{eq:up-spec-B} -}
     mapB (g . map' (td' n)) . up . ch (1+n)
 ===    {- |up| natural -}
     mapB g . up . mapB (td' n) . ch (1+n)
 ===    {- induction -}
     mapB g . up . rep' n (mapB g . up) . mapB ex . ch 1
 ===    {- |(.)| associative, def. of |rep' n f| -}
     rep' (1+n) (mapB g . up) . mapB ex . ch 1 {-"~~."-}
\end{code}
\end{proof}

\section{Conclusion and Discussions}

%%format mapF = "\Varid{F}"
%format reps f = "{" f "}^{*}"

We have derived the mysterious four-line function of \cite{Bird:08:Zippy}, and built upon it a bottom-up algorithm that solves the sublists problem.
The most tricky part was to find the right specification, which we did by observing what each layer represents, thinking about what we need to construct one layer from the previous one, and introducing a datatype that preserves the internal structure to ease the construction.
Both sides of the specification \eqref{eq:up-spec-B} are expressions involving |up|, the function to be derived.
In typical program calculation, one starts with a specification of the form
|up t = rhs| where |rhs| does not involve |up|, and tries to pattern match on |t|, simplifies |rhs|, and finds an inductive definition of |up|.
The author has tried to find such a specification with no avail, before settling down on \eqref{eq:up-spec-B}.
Techniques for manipulating such specifications to find a solution for |up| is one of the lessons the author learned from this experience.

Some final notes on the previous works.
The sublists problem was one of the examples of \cite{BirdHinze:03:Trouble}, a study of memoisation of functions, with a twist: the memo table is structured according to the call graph of the function, using trees of shared nodes (which they called \emph{nexuses}).
To solve the sublists problem, \cite{BirdHinze:03:Trouble} introduced a data structure, also called a ``binomial tree''. Whereas the binomial tree in~\cite{Bird:08:Zippy} and in this pearl models the structure of the function |choose|, that in \cite{BirdHinze:03:Trouble} can be said to model the function computing \emph{all} sublists:
\begin{code}
sublists []      = [[]]
sublists (x:xs)  = map (x:) (sublists xs) ++ sublists xs {-"~~."-}
\end{code}
Such trees were then extended with up links (and became \emph{nexuses}). Trees were built in a top-down manner, creating carefully maintained links going up and down.

Bird then went on to study the relationship between top-down and bottom-up algorithms, and the sublists problem was one of the examples in \cite{Bird:08:Zippy} to be solved bottom-up.
In Bird's formulation, the function used in the top-down algorithm that decomposes problems into sub-problems (like our |subs|) is called |dc|, with type |L a -> F (L a)| for some functor |F|.
The bottom-up algorithm uses a function |cd| (like our |upgrade|), with type |L a -> L (F a)|.
One of the properties they should satisfy is |dc . cd = mapF cd . dc|, where |mapF| is the functorial mapping for |F|.

For the sublists problem, |dc = subs|, and |F = L|.
We know parts of the rest of the story:
Bird had to introduce a new datatype |B|, and a new |cd| with type |B a -> B (L a)|, the four-line function that inspired this pearl.
That was not all, however.
Bird also quickly introduced, on the last page of the paper, a new |dc' :: B a -> L (B a)|, which was as cryptic as |cd|, and claimed that |dc' . cd = mapF cd . dc'|.
The relationship between |dc'| and |dc| (and the original problem) was not clear.
In this pearl we took a shorter route, proving directly that the bottom-up algorithm works, and the step function is |mapB g . up|.

%
% In \cite{Bird:08:Zippy}, a generic top-down algorithm is defined by:
% \begin{spec}
% td :: L X -> Y
% td xs = if sg xs then f (ex xs) else g (mapF td (dc xs)) {-"~~."-}
% \end{spec}
% %where |(p -> f; g)| denotes lifted conditional branching, defined by
% %|(p -> f; g) x = if p x then f x else g x|.
% In his setting, |L| is some input data structure that is often a list in examples, but need not be so. The function |sg :: L a -> Bool| determines whether an |L| structure is a singleton, whose content can be extracted by |ex :: L a -> a|.
% The function |dc :: L a -> F (L a)| decomposes an |L| into an |F| structure of |L|s, to be recursively processed --- |mapF :: (a -> b) -> F a -> F b| is the |map| function for |F|.
% In the simplest example, |L| is the type of lists, |F a = (a,a)|, and |dc xs = (init xs, tail xs)| (e.g. |dc "abcd" = ("abc", "bcd")|).
%
% %One of the aims of~\cite{Bird:08:Zippy} was to study tabulation in bottom-up algorithms, therefore Bird introduced another data structure, the \emph{nexus} (which was not needed in the sublists example, however).
% A simplified version of Bird's generic bottom-up algorithm, without the nexus, is something like: |bu = ex . reps (map' g . cd) . map' f|.
% The pre and postprocessing are respectively |map' f| and |ex|, while |map' g . cd| is repeatedly performed (via the "|*|") until we have a singleton.
% The function |cd :: L a -> L (F a)| transforms one level to the next.
% Note that its return type is symmetric to that of |dc| (hence the name |cd|, probably). For the |dc| above, we let |cd| be the function that combines adjacent elements of a list into pairs, e.g., |cd "abcd" = [("a",b), ("b", "c"), ("c","d")]|.
%
% %format mapF2 = "{" mapF "}^2"
% %format mapF3 = "{" mapF "}^3"
% %format mapFn = "{" mapF "}^{n}"
% %format mapFn1 = "{" mapF "}^{n-1}"
%
% While diagrams such as Figure~\ref{fig:ch-lattice} may help one to see how a bottom-up algorithm works, to understand how a top-down algorithm is transformed to a bottom-up one,
% it may be more helpful to think in terms of right-to-left function composition.
% Bird's top-down algorithm, when expanded, has the form
% %{
% %format (emph (x)) = "\textcolor{orange}{" x "}"
%
% \begin{equation}
% \label{eq:td-expanded}
%  |g . mapF g {-"~"-}...{-"~"-} mapFn1 g . (emph mapFn) (f . (emph ex)) . emph (mapFn1 dc) {-"~"-}... {-"~"-} mapF2 dc . mapF dc . dc {-"~~."-}|
% \end{equation}
% Several crucial properties are needed to turn |td| into |bu|.
% Among them, Bird needed |mapF ex . dc = ex . cd| and |dc . cd = mapF cd . dc|.
% The first property turns the inner |emph (mapFn ex . mapFn1 dc)| into |mapFn1 (ex . cd)|, while the second swaps |cd| to the rightmost position.
% Function calls to |f| and |g| are shunted to the right by naturality.
% That yields \emph{one} |map' g . cd|.
% The process needs to be repeated to create more |map' g . cd|.
% Therefore Bird used two inductive proofs to show that |td = bu|.
%
% The sublists problem, however, does not fit into this framework very well.
% While |dc| (which is our |subs|) has type |L a -> L (L a)| in the specification,
% Bird noticed that we need binomial trees to enable the bottom-up construction, therefore |cd| (our |up|) has type |B a -> B (L a)|.
% Rather than constructing |cd| from a specification having |dc|,
% Bird introduced |cd| out of the blue, before introducing another equally cryptic |dc' :: B a -> L (B a)| and claiming that |dc' . cd = mapF cd . dc'|.
%
% %format mapB2 = "{" mapB "}^2"
% %format mapB3 = "{" mapB "}^3"
% %format mapBn = "{" mapB "}^{n}"
% %format mapBn1 = "{" mapB "}^{n-1}"
%
% In this pearl we reviewed this problem from the basics,
% and instead proposed \eqref{eq:up-spec-B} as a specification of |up|, as well as the property that drives the entire derivation.
% Look at the expanded top-down algorithm again:
% \begin{equation*}
%  |g . mapB g {-"~"-}...{-"~"-} mapBn1 g . mapBn (f . ex) . mapBn1 subs {-"~"-}... {-"~"-} mapB2 subs . emph (mapB subs . subs) {-"~~,"-}|
% \end{equation*}
% (The above is \eqref{eq:td-expanded} with |(mapF, dc) := (mapB, subs)|.)
% Property \eqref{eq:up-spec-B} turns the \emph{outermost}
% |emph (mapB subs . subs)|, which is |mapB subs . ch (n-1)|, into |up . ch (n-2)|.
% That is, |up| is generated from the outside, before being shunted leftwards using naturality.
% This fits the problem better: we do not need a |dc' :: B a -> L (B a)|,
% and we need only one inductive proof.
%
% %} %% emph
%
% The moral of this story is that while many bottom-up algorithms look alike --- they all have the form |post . iters step . pre|, the reason why they work could be very different.
% It is likely that there are more patterns yet to be discovered.

\paragraph*{Acknowledgements}~ The author would like to thank Hsiang-Shang Ko and Jeremy Gibbons for many in-depth discussions throughout the development of this work, Conor McBride for discussion at a WG 2.1 meeting, and Yu-Hsuan Wu and Chung-Yu Cheng for proof-reading drafts of this pearl.
The examples of how the immediate sublists problem may be put to work was suggested by Meng-Tsung Tsai.
The first version of the Agda proofs were constructed by You-Zheng Yu.

\paragraph*{Conflicts of interest}~ None.

\appendix
\renewcommand{\thesection}{\Alph{section}}

\section{Variation of |up| That Uses |(:)|}
\label{sec:up-cons}

Show below is the variation of |up| that uses |(:)|.
The function is called |cd| in \cite{Bird:08:Zippy}.
{
%{
%format up' = up

\begin{code}
up' :: B a -> B (L a)
up' (N (T p)  (T q)  ) = T [p, q]
up' (N t      (T q)  ) = N (up' t) (mapB (:[q]) t)
up' (N (T p)  u      ) = T (p : unT (up' u))
up' (N t      u      ) = N (up' t) (zipBW (:) t (up' u))
\end{code}
%}
}

\section{Agda Implementation of |up|}
\label{sec:agda:up}

The following is an Agda implementation of |up|.
The type states that it is defined only for |0 < k < n|;
the shape of its input tree is determined by |(k,n)|; the output tree has shape determined by |(1+k,n)|, and the values in the tree are lists of length |1+k|.

%% Agda stuffs
%{
%format T0
%format Tn = "\Conid{T}_{\Varid{n}}"
%format unTn = "\Varid{unT}_{\Varid{n}}"
%format Nat = "\mathbb{N}"
%format bot = "{\bot}"

\newcommand{\dash}{{\text{-}}}
%format sses = "\scaleobj{0.8}{\mathsf{s{\leq}s}}"
%format ssesi = "\scaleobj{0.8}{\mathsf{s{\leq}s}^{-1}}"
%format zsen = "\scaleobj{0.8}{\mathsf{z{\leq}n}}"
%format zsz = "\scaleobj{0.8}{0{\small <}0}"
%format snssn = "\scaleobj{0.8}{1{+}n\!<\!1{+}n}"
%format ssnsssn = "\scaleobj{0.8}{2{+}n\!<\!2{+}n}"
%format skssn = "\scaleobj{0.8}{1{+}k\!<\!1{+}n}"
%format ssksssn = "\scaleobj{0.8}{2{+}k\!<\!2{+}n}"
%format botelim = "{\bot}\dash\Varid{elim}"
%format serefl = "\scaleobj{0.8}{{\leq}\dash\Varid{refl}}"
%format sirrefl = "\scaleobj{0.8}{{<}\dash\Varid{irrefl}}"
%format (pf x) = "\textcolor{Tan}{" x "}"
{\small
\begin{spec}
up : pf (0 < k) -> pf (k < n) -> B a k n -> B (Vec a (1 + k)) (1 + k) n
up (pf zsz)    _    (T0 x)        = pf botelim (pf (sirrefl refl zsz))
up _  (pf snssn)    (Tn x)        = pf botelim (pf (sirrefl refl snssn))
up _  (pf ssnsssn)  (N (Tn _) _)  = pf botelim (pf (sirrefl refl ssnsssn))

up _  _            (N (T0 p)     (Tn q)      )  = Tn (p :: q :: [])
up _  _            (N t@(N _ _)  (Tn q)      )  = Tn (snoc (unTn (up (pf (sses zsen)) (pf (sses serefl)) t)) q)
up _  _            (N (T0 p)     u@(N _ u')  )  = N  (mapB (\ q -> p :: q :: []) u)
                                                     (up (pf serefl) (pf (sses (bounded u'))) u)
up _ (pf ssksssn)  (N t@(N _ _) u@(N _ u'))     = N  (zipBW snoc (up (pf (sses zsen)) (pf (ssesi ssksssn)) t) u)
                                                     (up (pf (sses zsen)) (pf (sses (bounded u'))) u)
\end{spec}
}

The first three clauses of |up| eliminate impossible cases.
The remaining four clauses are essentially the same as in the non-dependently typed version,
modulo the additional arguments and proof terms, shown in light brown, that are needed to prove that |k| and |n| are within bounds.
In the clause that uses |unT|, the input tree has the form |N t (Tn q)|.
The right subtree being a |Tn| forces the other subtree |t| to have type
|B a (1+k) (2+k)| --- the two indices must differ by |1|. Therefore |up t| has type |B a (2+k) (2+k)| and must be built by |Tn|.
The last clause receives inputs having type |B a (2+k) (2+n)|. Both |u| and |up t| have types |B ... (2+k) (1+n)| and, therefore, have the same shape.
%}

\bibliographystyle{common/jfplike}
\bibliography{common/bib}
%\input{sublists.bbl}

\end{document}
