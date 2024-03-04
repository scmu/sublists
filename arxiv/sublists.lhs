\documentclass[dvipsnames, fleqn, 11pt]{article}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{natbib}

\usepackage{classicthesis}

\linespread{1.05} % a bit more for Palatino
\areaset[current]{420pt}{761pt} % 686 (factor 2.2) + 33 head + 42 head \the\footskip
\setlength{\marginparwidth}{7em}%
\setlength{\marginparsep}{2em}%

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

%\def\commentbegin{\quad$\{$~}
%\def\commentend{$\}$}
\def\commentbegin{\quad\begingroup\color{SeaGreen}\{\ }
\def\commentend{\}\endgroup}

\mathindent=\parindent
\addtolength{\mathindent}{0.3cm}

\definecolor{mediumpersianblue}{rgb}{0.0, 0.4, 0.65}
\everymath{\color{mediumpersianblue}}
\apptocmd{\[}{\color{mediumpersianblue}}{}{}
\AtBeginEnvironment{equation}{\color{mediumpersianblue}}
\AtBeginEnvironment{equation*}{\color{mediumpersianblue}}

\allowdisplaybreaks

\newcommand{\tagx}[1][]{\refstepcounter{equation}(\theequation)\label{#1}}
\newcommand\numberthis{\refstepcounter{equation}\tag{\theequation}}


\counterwithout{equation}{section}

%format iter' (k) f = "{"f"}^{"k"}"

\begin{document}

\title{Functional Pearl:\\
Bottom-Up Computation Using Trees of Sublists}

\author{\color{black}Shin-Cheng Mu}
\date{%
Institute of Information Science, Academia Sinica
}

\maketitle

\begin{abstract}
Some top-down problem specifications, if executed directly, may compute sub-problems repeatedly.
Instead, we may want a bottom-up algorithm that stores solutions of sub-problems in a table to be reused.
It can be tricky, however, to figure out how the table can be represented and efficiently maintained.
We study a special case: computing a function |h| taking lists as inputs such that |h xs| is defined in terms of all immediate sublists of |xs|.
Richard Bird studied this problem in 2008, and presented a concise but cryptic algorithm without much explanation.
We give this algorithm a proper derivation, and discover a key property that allows it to work.
The algorithm builds trees that have certain shapes --- the sizes along the left spine is a diagonal in Pascal's triangle.
The crucial function we derive transforms one diagonal to the next.
\end{abstract}

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
For this problem, one might want to build a lattice-like structure, like that in Figure~\ref{fig:ch-lattice}, from bottom to top,
sharing the value on one layer that are used in constructing the next layer.

\begin{figure}[h]
\centering
\includegraphics[width=0.5\textwidth]{pics/td-call-tree.pdf}
\caption{Computing |h "abcd"| top-down. String constants are shown using monospace font but without quotes, to save space.}
\label{fig:td-call-tree}
\end{figure}

\cite{Bird:08:Zippy} presented an interesting study of the relationship between top-down and bottom-up algorithms.
It was shown that if an algorithm can be written in a specific top-down style,
with ingredients that satisfy certain properties,
there is an equivalent bottom-up algorithm that stores intermediate results in a table.
The ``all immediate sublists'' instance was the last example of the paper.
To satisfy the said properties, however, Bird had to introduce additional data structures and helper functions out of the blue.
The rationale for designing these data structures and functions was not obvious, nor was it clear why the needed properties are met.
The resulting bottom-up algorithm is concise, elegant, but also cryptic --- all the more reason to present the proper calculation it deserves.

\begin{figure}
\centering
\includegraphics[width=0.85\textwidth]{pics/ch-lattice.pdf}
\caption{Computing |h "abcde"| bottom-up.}
\label{fig:ch-lattice}
\end{figure}

In this pearl we review this problem, present an alternative specification, and derive Bird's algorithm.
It turns out that the key property we rely on is different from that in Bird's \citeyearpar{Bird:08:Zippy}.
Driven by this property, our main derivation is much more straight-forward.
This suggests that, while many bottom-up algorithms look alike, the reasons why they work may be more diverse than we thought, and there is a lot more to be discovered regarding reasoning about their correctness.

Before we start, one might ask: are there actually problems whose solution of input |xs| depends only on solutions for immediate sublists of |xs|?
It turns out that it is quite common.
While problems such as \emph{minimum editing distance} or \emph{longest common subsequence} are defined on two lists,
it is known in the algorithm community that, with clever encoding, they can be rephrased as problems defined on one list,
whose solution depends on immediate sublists.
Many problems in additive combinatorics \citep{TaoVu:12:Additive} can also be cast into this form.

%if False
\begin{code}
type L a = [a]
map' :: (a -> b) -> L a -> L b
map' = map
\end{code}
%endif

%format map' = "\Varid{L}"

\section{Specification}
\label{sec:spec}

We use a Haskell-like notation throughout the paper.
Like in Haskell, if a function is defined by multiple clauses, the patterns and guards are matched top to bottom.
Differences from Haskell include that we allow |n+k| patterns, and that we denote the type of lists by |L|.
Since we will use natural transformations and |map| a lot, for brevity we denote the |map| function of lists as |map' :: (a -> b) -> L a -> L b| (note that |map'| is written in italic font, to distinguish it from the type constructor |L|).

The immediate sublists of a list can be specified in many ways.
We use the definition below mainly because it generates sublists in an intuivite order:
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
h xs   = g . map' h . subs $ xs {-"~~,"-}
\end{code}
where |f :: X -> Y| is used in the base case when the input is a singleton list,
and |g :: L Y -> Y| is for the inductive case. The operator |($)| denotes function application, which binds looser than function composition |(.)|.
We sometimes use |($)| to reduce the number of parentheses.

For this pearl, it is convenient to use an equivalent definition.
Let |td| be a family of functions indexed by natural numbers (denoted by |Nat|):
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
Given input |xs|, the value we aim to compute is |h xs = td (length xs - 1) xs|.
This definition will be handy later.

The function |iter k| composes a function with itself |k| times:
\begin{spec}
iter :: Nat -> (a -> a) -> a -> a
iter 0      f = id
iter (1+k)  f = iter k f . f {-"~~."-}
\end{spec}
%if False
\begin{code}
iter :: Nat -> (a -> a) -> a -> a
iter 0  f = id
iter k  f = iter (k-1) f . f {-"~~."-}

iter' :: Nat -> (a -> a) -> a -> a
iter' = iter
\end{code}
%endif
For brevity, we will write |iter k f| as |iter' k f| for the rest of this pearl.
The bottom-up algorithm we aim to construct has the following form:
\begin{spec}
bu :: Nat -> L X -> Y
bu n = post . iter' n step . pre {-"~~,"-}
\end{spec}
where |pre| preprocesses the input and builds the lowest level in Figure \ref{fig:ch-lattice},
and each |step| builds a level from the one below.
For input of length |1+n| we repeat |n| times and, by then, we can extract the singleton value by |post|.

The aim of this pearl is to construct |pre|, |step|, and |post| such that |td = bu|.

%\hspace{2cm}
%\begin{minipage}{0.3\textwidth}
%\begin{code}
%wrap :: a -> List a
%wrap x = [x] {-"~~,"-}
%\end{code}
%\end{minipage}
%\begin{minipage}{0.4\textwidth}
%\begin{spec}
%apply :: Nat -> (a -> a) -> a -> a
%apply 0      f = id
%apply (1+k)  f = apply k f . f {-"~~."-}
%\end{spec}
%%if False
%\begin{code}
%apply :: Nat -> (a -> a) -> a -> a
%apply 0 f = id
%apply k f = apply (k-1) f . f {-"~~."-}
%\end{code}
%%endif
%\end{minipage}\\

\section{Building a New Level}
\label{sec:build-level}

%{
\newcommand{\dqoute}{\mathtt{"}}
%subst string a = "\mathtt{\dqoute " a "\dqoute}"

To find out what |step| might be, we need to figure out how to specify a level, and what happens when a level is built from the one below it.
We use Figure~\ref{fig:ch-lattice} as our motivating example.
As one can see, level |2| in Figure~\ref{fig:ch-lattice} consists of sublists of |"abcde"| that have length |2|, and level |3| consists of sublists having length |3|, and so on.
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
Its definition follows basic combinatorics: the only way to choose |0| elements from a list is |[]|; if |length xs = k|, the only way to choose |k| elements is |xs|. Otherwise, to choose |1+k| elements from |x:xs|, one can either keep |x| and choose |k| from |xs|, or discard |x| and choose |1+k| elements from |xs|.
For example, |choose 3 "abcde"| yields
|["abc","abd","abe","acd","ace","ade",| |"bcd","bce","bde","cde"]|.
%}

Note that |choose k xs| is defined only when |k <= length xs|.
Note also that |subs| is a special case of |choose| --- we have |subs xs = choose (length xs -1) xs|, a property we will need later.

If the levels in Figure~\ref{fig:ch-lattice} were to be represented as lists,
level |k| is given by |map' h (choose k xs)|.
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
With |[h "ab", h "ac", h "bc"]| one can compute |h "abc"|; with
|[h "ab", h "ad", h "bd"]| one can compute |h "abd"|, and so on.
That is, if we apply |map' g| to the result of |upgrade| above, we get:
\begin{spec}
   [h "abc", h "abd", h "abe", h "acd"...] {-"~~,"-}
\end{spec}
which is level |3|, or |map' h (choose 3 "abcde")|.
The function |upgrade| needs not inspect the values of each element, but rearranges them by position --- it is a natural transformation |L a -> L (L a)|.
As far as |upgrade| is concerned, it does not matter whether |h| is applied or not.
Letting |h = id|, observe that |upgrade (choose 2 "abcde") =|
|[["ab", "ac", "bc"], ["ab", "ad", "bd"]...]| and
|choose 3 "abcde" =|  |["abc", "abd", "abe", "acd"...]|
are related by |map' subs|:
each |step| we perform in the bottom-up algorithm could be |map' g . upgrade|.

Formalising the observations above, we want |upgrade :: L a -> L (L a)| to satisfy:
\begin{equation}
\label{eq:up-spec-list}
\begin{split}
&  |(forall xs, k : 2 <= 1+k <= length xs :|\\
&   \qquad |upgrade (choose k xs) = map' subs (choose (1+k) xs)) {-"~~."-}|
\end{split}
\end{equation}
With this property, each |step| we perform in the bottom-up algorithm is |map' g . upgrade|, which converts level |k| to level |k+1|:
%if False
\begin{code}
upgrade :: L a -> L (L a)
upgrade = undefined

derUpgradeHelp :: Nat -> L X -> L Y
derUpgradeHelp k =
\end{code}
%endif
\begin{code}
    map' g . upgrade . map' h . choose k
 ===    {- |upgrade| natural -}
    map' g . map' (map' h) . upgrade . choose k
 ===    {- by \eqref{eq:up-spec-list}, |map|-fusion -}
    map' (g . map' h . subs) . choose (1+k)
 ===    {- definition of |h| -}
    map' h . choose (1+k) {-"~~."-}
\end{code}

We give some explanation on the constraints on |k| in \eqref{eq:up-spec-list}.
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
We assume that |B| is equipped with two functions derived from its definition:
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
Like that with lists, we also write |mapB| as $\Varid{B}$.
Given two trees |t| and |u| having the same shape,
|zipBW f t u| ``zips'' the trees together, applying |f| to values on the tips.
If |t| and |u| have different shapes, |zipBW f t u| is undefined.

%format mapB = "\Varid{B}"

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

The counterpart of |upgrade| on trees, which we will call |up|, is a natural transformation of type |B a -> B (L a)|, satisfying the following property:
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

Now we are ready to derive |up|.

\subsection{The Derivation}

The derivation proceeds by trying to construct a proof of \eqref{eq:up-spec-B} and, when stuck, pausing to think about how |up| should be defined to allow the proof to go through.
That is, the definition of |up| and a proof that it satisfies \eqref{eq:up-spec-B} are developed hand-in-hand.

The proof, if constructed, will be an induction on |xs|.
The case analysis follows the shape of |ch (1+k) xs| (on the RHS of \eqref{eq:up-spec-B}).
Therefore, there is a base case, a case when |xs| is non-empty and |1+k = length xs|, and a case when |1+k < length xs|.
However, since the constraints demand that |xs| has at least two elements, the base case will be lists of length |2|, and in the inductive cases the length of the list will be at least |3|.

\paragraph*{Case 1.~~} |xs := [y,z]|.\\
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
   ===   {- def. of |mapB| -}
     N (mapB (subs . (x:)) (ch (1+k) xs)) (mapB subs (ch (2+k) xs))
   ===   {- induction -}
     N (mapB (subs . (x:)) (ch (1+k) xs)) (up (ch (1+k) xs)) {-"~~."-}
\end{code}
%endif
\addtolength\jot{-2.2pt}
\begin{align*}
  & |mapB subs (ch (2+k) (x:xs))| \\
=~& \mbox{\color{SeaGreen}\quad\{ def. of |ch|, since |2+k < length (x:xs)| \}} \\
  & |mapB subs (N (mapB (x:) (ch (1+k) xs)) (ch (2+k) xs))| \\
=~& \mbox{\color{SeaGreen}\quad\{ def. of |mapB| \}}\\
  & |N (mapB (subs . (x:)) (ch (1+k) xs)) (mapB subs (ch (2+k) xs))|\\
=~& \mbox{\color{SeaGreen}\quad\{ induction \}}\\
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
=~& \mbox{\color{SeaGreen}\quad\{ def. of |ch|, since |1+k < length (x:xs)| \}}\\
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
this expression shall evaluate to the subexpression in \eqref{eq:up3R}:
\begin{spec}
    mapB (subs . (x:)) (ch (1+k) xs) {-"~~."-}
\end{spec}

It may appear that, now that |up| already has |u = ch (1+k) xs|, the |???| may simply be |mapB (sub . (x:)) u|. The problem is that the |up| does not know what |x| is --- unless |k = 0|.

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
from which can retrieve |x| and apply |mapB (sub . (x:))| to the other subtree.
We can furthermore simplify |mapB (sub . (x:)) (ch (1+0) xs)| a bit:
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
In this more general case, we have to construct |mapB (subs . (x:)) (ch (1+k) xs)| out of the two subtrees, |mapB (x:) (ch k xs)| and |ch (1+k) xs|, without knowing what |x| is.

Starting calculation from |mapB (subs . (x:)) (ch (1+k) xs)|,
we expect to use induction somewhere, therefore a possible strategy is to move |mapB subs| rightwards, closer to |ch|, in order to apply \eqref{eq:up-spec-B}.
Let us consider how to compute |mapB (subs . (x:)) u| for a general |u|, and try to move |mapB subs| closer to |u|.
%
Note that
\begin{itemize}
\item by definition, |sub (x:xs) = map' (x:) (sub xs) ++ [xs]|.
\item Given a tree |u| and functions |f|, |g|, and |h|,
by naturality of |zipBW| we have:
\begin{equation}
\label{eq:map-zipBW}
 |mapB (\z -> f (g z) (h z)) u = zipBW f (mapB g u) (mapB h u) {-"~~."-}|
\end{equation}
\item Therefore, letting |g = map' (x:) . subs|, |h = id|, and |f = snoc| in \eqref{eq:map-zipBW}, where |snoc ys z = ys ++[z]|, we have:
\begin{equation}
\label{eq:map-sub-zipBW}
  |mapB (subs . (x:)) u = zipBW snoc (mapB (map' (x:) . subs) u) u {-"~~."-}|
\end{equation}
\end{itemize}

We calculate:
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
        zipBW snoc  (mapB (map' (x:)) . up . ch k $ xs) (ch (1+k) xs)
    ===   {- |up| natural -}
        zipBW snoc (up . mapB (x:) . ch k $ xs) (ch (1+k) xs) {-"~~."-}
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
up (N t      (T q)  ) = T (unT (up t) ++ [q])
up (N (T p)  u      ) = N (mapB (\q -> [p,q]) u) (up u)
up (N t      u      ) = N (zipBW snoc (up t) u) (up u) {-"~~."-}
\end{code}
%if False
\begin{code}
snoc :: L a -> a -> L a
snoc xs x = xs ++ [x]

unT (T x) = x
\end{code}
%endif
Using |(++)| and |snoc| may look inefficient, but had we specified |choose| slightly differently, the |up| we derive would use |(:)| instead.
Again, we defined |choose| this way merely to generate sublists in an intuitive order.

\begin{figure}[h]
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
  Tn  : a -> B a (suc n) (suc n)
  N   : B a k n -> B a (suc k) n -> B a (suc k) (suc n) {-"~~."-}
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
Furthermore, it can also be proved that if a tree |B a k n| can be built at all, it must be the case that |k <= n|:
\begin{spec}
bounded    : B a k n        -> k <= n  {-"~~."-}
\end{spec}
The function |unTn : B a (suc n) (suc n) -> a| extracts the contents stored in a tip, and is only applied when we know, by the type, that the tree must be |Tn|.

\begin{figure}
\centering
%{
\newcommand{\dash}{{\text{-}}}
%format sses = "\scaleobj{0.8}{\textcolor{Tan}{\mathsf{s{\leq}s}}}"
%format zsen = "\scaleobj{0.8}{\textcolor{Tan}{\mathsf{z{\leq}n}}}"
%format zsz = "\scaleobj{0.8}{\textcolor{Tan}{0{\small <}0}}"
%format snssn = "\scaleobj{0.8}{\textcolor{Tan}{1{+}n\!<\!1{+}n}}"
%format ssnsssn = "\scaleobj{0.8}{\textcolor{Tan}{2{+}n\!<\!2{+}n}}"
%format skssn = "\scaleobj{0.8}{\textcolor{Tan}{1{+}k\!<\!1{+}n}}"
%format botelim = "{\textcolor{Tan}{\bot}\dash\Varid{elim}}"
%format serefl = "\scaleobj{0.8}{\textcolor{Tan}{{\leq}\dash\Varid{refl}}}"
%format sirrefl = "\scaleobj{0.8}{\textcolor{Tan}{{<}\dash\Varid{irrefl}}}"
%format (pf x) = "\textcolor{Tan}{" x "}"
{\small
\begin{spec}
up : pf (0 < k) -> pf (k < n) -> B a k n -> B (Vec a (suc k)) (suc k) n
up (pf zsz)    _             (T0 x)        = pf botelim (pf (sirrefl refl zsz))
up _           (pf snssn)    (Tn x)        = pf botelim (pf (sirrefl refl snssn))
up _           (pf ssnsssn)  (N (Tn _) _)  = pf botelim (pf (sirrefl refl ssnsssn))

up _  _  (N (T0 p)     (Tn q)      )  = Tn (p :: q :: [])
up _  _  (N t@(N _ _)  (Tn q)      )  = Tn (snoc (unTn (up (pf (sses zsen)) (pf (sses serefl)) t)) q)
up _  _  (N (T0 p)     u@(N _ u')  )  = N  (mapB (\ q -> p :: q :: []) u) (up (pf serefl) (pf (sses (bounded u'))) u)
up _ (pf (sses skssn)) (N t@(N _ _) u@(N _ u')) =
     N  (zipBW snoc (up (pf (sses zsen)) (pf skssn) t) u) (up (pf (sses zsen)) (pf (sses (bounded u'))) u)
\end{spec}
}
%}
\caption{An Agda implementation of |up|.}
\label{fig:up-agda}
\end{figure}

Figure~\ref{fig:up-agda} shows an Agda implementation of |up|.
The type states that it is defined only for |0 < k < n|;
the shape of its input tree is determined by |(k,n)|; the output tree has shape determined by |(1+k,n)|, and the values in the tree are lists of length |1+k|.

The first three clauses of |up| eliminate impossible cases.
The remaining four clauses are essentially the same as the non-dependently typed version,
modulo the additional arguments and proof terms, shown in light brown, that are needed to prove that |k| and |n| are within bounds.
In the clause that uses |unT|, the input tree has the form |N t (Tn q)|.
The right subtree being a |Tn| forces the other subtree |t| to have type
|B a (1+k) (2+k)| --- the two indices must differ by |1|. Therefore |up t| has type |B a (2+k) (2+k)| and must be built by |Tn|.
The last clause receives inputs having type |B a (2+k) (2+n)|. Both |u| and |up t| have types |B ... (2+k) (1+n)| and, therefore, have the same shape.
%}
%% Agda stuffs

\begin{figure}[h]
\centering
\includegraphics[width=0.8\textwidth]{pics/pascal-tri.pdf}
\caption{Sizes of |B| alone the right spine correspond to diagonals in Pascal's Triangle.}
\label{fig:pascal-tri}
\end{figure}

\paragraph*{Pascal's Triangle.}~~
With so much discussion about choosing, it is perhaps not surprising that the sizes of subtrees along the right spine of a |B| tree correspond to diagonals in Pascal's Triangle.
After all, the |k|-th diagonal (counting from zero) in Pascal's Triangle denotes binomial coefficients --- the numbers of ways to choose |k| elements from |k|, |k+1|, |k+2|... elements.
This is probably why \cite{Bird:08:Zippy} calls the data structure a \emph{binomial tree}, hence the name |B|.
\footnote{It is not directly related to the tree, having the same name, used in \emph{binomial heaps}.}
See Figure~\ref{fig:pascal-tri} for example.
The sizes along the right spine of |ch 2 "abcde"|, that is, |10,6,3,1|, is the second diagonal (in orange), while the right spine of |ch 3 "abcde"| is the fourth diagonal (in blue).
Applying |up| to a tree moves it rightwards and downwards.
In a sense, a |B| tree represents a diagonal in Pascal's Triangle \emph{with a proof} of how it is constructed.


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
We will then be focusing on transforming |td'|.

Our aim is to show that |td' n| can be performed by |n| steps of |mapB g . up|, plus some pre and post processing.
%
Our derivation, however, has to introduce the last step (that is, the leftmost |mapB g . up|, when the steps are composed together) separately from the other steps.
We mentioned that |subs| is a special case of |choose|. To be more precise, for |xs| such that |length xs = 1+n| we have
\begin{align}
\label{eq:unT-up-choose}
|subs xs = unT . up . ch n $ xs {-"~~."-}|
\end{align}
For an example of \eqref{eq:unT-up-choose}, let |xs = "abcd"|. The LHS gives us |["abc","abd","acd","bcd"]|, while
in the RHS, |ch n| builds a tree with four tips, which will be joined by |up| to a singleton tree |T ["abc","abd","acd","bcd"]|.
That |up| always returns a |T| can be seen from the annotated types discussed in Section \ref{sec:deptypes}: since |ch n| yields a tree having type |B a n (1+n)|, |up| has to construct a tree of type |B a (1+n) (1+n)|, which must be a tip.

Now we calculate:
%if False
\begin{code}
derTd1 :: Nat -> L X -> Y
derTd1 n =
\end{code}
%endif
\begin{code}
     td (1+n)
 ===   {- since |td k = td' k . map' f| -}
     td' (1+n) . map' f
 ===   {- def. of |td'| -}
     g . map' (td' n) . subs . map' f
 ===   {- by \eqref{eq:unT-up-choose} -}
     g . map' (td' n) . unT . up . ch (1+n) . map' f
 ===   {- naturality of |unT| -}
     unT . mapB (g . map' (td' n)) . up . ch (1+n) . map' f
 ===   {- naturality of |up| -}
     unT . mapB g . up . mapB (td' n) . ch (1+n) . map' f {-"~~."-}
\end{code}
That gives us the last |mapB g . up|.

For the other steps, the following lemma shows that |mapB (td' n) . ch (1+n)| can be performed by |n| steps of |mapB g . up|, after some preprocessing.
This is the key lemma that relates \eqref{eq:up-spec-B} to the main algorithm.
\begin{lemma}\label{lma:main}
|mapB (td' n) . ch (1+n) = iter' n (mapB g . up) . mapB ex . ch 1|.
\end{lemma}
\begin{proof}
For |n := 0| both sides simplify to |mapB ex . ch 1|. For |n := 1 + n|:
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
     mapB g . up . iter' n (mapB g . up) . mapB ex . ch 1
 ===    {- |(.)| associative, def. of |iter' n f| -}
     iter' (1+n) (mapB g . up) . mapB ex . ch 1 {-"~~."-}
\end{code}
\end{proof}

In summary, we have shown that:
\begin{theorem} For all |n :: Nat| we have |td n = bu n|, where
\begin{code}
bu n = unT . iter' n (mapB g . up) . mapB ex . ch 1 . map' f {-"~~."-}
\end{code}
\end{theorem}
\noindent That is, the top-down algorithm |td n| is equivalent to a bottom-up algorithm |bu n|, where the input is preprocessed by |mapB ex . ch 1 . map' f|, followed by |n| steps of |mapB g . up|. By then we will get a singleton tree, whose content can be extracted by |unT|.
The proof is merely putting all the pieces together.
\begin{proof}
For |n := 0|, both sides reduce to |f . ex|.
For |n := 1+n|, we have
%if False
\begin{code}
derMain :: Nat -> L X -> Y
derMain n =
\end{code}
%endif
\begin{code}
   td (1+n)
 ===    {- calculation before -}
   unT . mapB g . up . mapB (td' n) . ch (1+n) . map' f
 ===    {- Lemma~\ref{lma:main} -}
   unT . mapB g . up . iter' n (mapB g . up) . mapB ex . ch 1 . map' f
 ===    {- |(.)| associative, def. of |iter' n f| -}
   unT . iter' (1+n) (mapB g . up) . mapB ex . ch 1 . map' f
 ===    {- definition of |bu| -}
   bu (1+n) {-"~~."-}
\end{code}
\end{proof}

\section{Conclusion and Discussions}

%format mapF = "\Varid{F}"
%format iters f = "{" f "}^{*}"


The sublists problem was one of the examples of \cite{BirdHinze:03:Trouble}, a study of memoisation of functions, with a twist: the memo table is structured according to the call graph of the function, using trees of shared nodes (which they called \emph{nexuses}).
To solve the sublists problem, \cite{BirdHinze:03:Trouble} introduced a data structure, also called a ``binomial tree''. Whereas the binomial tree in~\cite{Bird:08:Zippy} and in this pearl models the structure of the function |choose|, that in \cite{BirdHinze:03:Trouble} can be said to model the function computing \emph{all} sublists:
\begin{code}
sublists []      = [[]]
sublists (x:xs)  = map (x:) (sublists xs) ++ sublists xs {-"~~."-}
\end{code}
Such trees were then extended with up links (and became \emph{nexuses}). Trees were built in a top-down manner, creating carefully maintained links going up and down.

Bird then went on to study the relationship between top-down and bottom-up algorithms, and the sublists problem was one of the examples in \cite{Bird:08:Zippy} to be solved bottom-up. In \cite{Bird:08:Zippy}, a generic top-down algorithm is defined by:
\begin{spec}
td :: L X -> Y
td xs = if sg xs then f (ex xs) else (g . mapF td . dc $ xs) {-"~~."-}
\end{spec}
%where |(p -> f; g)| denotes lifted conditional branching, defined by
%|(p -> f; g) x = if p x then f x else g x|.
In his setting, |L| is some input data structure that is often a list in examples, but need not be so. The function |sg :: L a -> Bool| determines whether an |L| structure is a singleton, whose content can be extracted by |ex :: L a -> a|.
The function |dc :: L a -> F (L a)| decomposes an |L| into an |F| structure of |L|s, to be recursively processed.
In the simplest example, |L| is the type of lists, |F a = (a,a)|, and |dc xs = (init xs, tail xs)| (e.g. |dc "abcd" = ("abc", "bcd")|).

%One of the aims of~\cite{Bird:08:Zippy} was to study tabulation in bottom-up algorithms, therefore Bird introduced another data structure, the \emph{nexus} (which was not needed in the sublists example, however).
A simplified version of Bird's generic bottom-up algorithm, without the nexus, is something like: |bu = ex . iters (map' g . cd) . map' f|.
The pre and postprocessing are respectively |map' f| and |ex|, while |map' g . cd| is repeatedly performed (via the "|*|") until we have a singleton.
The function |cd :: L a -> L (F a)| transforms one level to the next.
Note that its return type is symmetric to that of |dc| (hence the name |cd|, probably). For the |dc| above, we let |cd| be the function that combines adjacent elements of a list into pairs, e.g., |cd "abcd" = [("a",b), ("b", "c"), ("c","d")]|.

%format mapF2 = "{" mapF "}^2"
%format mapF3 = "{" mapF "}^3"
%format mapFn = "{" mapF "}^{n}"
%format mapFn1 = "{" mapF "}^{n-1}"
While diagrams such as Figure~\ref{fig:ch-lattice} may help one to see how a bottom-up algorithm works, to understand how a top-down algorithm is transformed to a bottom-up one,
it may be it more helpful to think in terms of right-to-left function composition.
Bird's top-down algorithm, when expanded, has the form
%{
%format (emph (x)) = "\textcolor{orange}{" x "}"

\begin{equation}
\label{eq:td-expanded}
 |g . mapF g {-"~"-}...{-"~"-} mapFn1 g . (emph mapFn) (f . (emph ex)) . emph (mapFn1 dc) {-"~"-}... {-"~"-} mapF2 dc . mapF dc . dc {-"~~."-}|
\end{equation}
Several crucial properties are needed to turn |td| into |bu|.
Among them, Bird needed |mapF ex . dc = ex . cd| and |dc . cd = mapF cd . dc|.
The first property turns the inner |emph (mapFn ex . mapFn1 dc)| into |mapFn1 (ex . cd)|, while the second swaps |cd| to the rightmost position.
Function calls to |f| and |g| are shunted to the right by naturalty.
That yields \emph{one} |map' g . cd|.
The process needs to be repeated to create more |map' g . cd|.
Therefore Bird used two inductive proofs to show that |td = bu|.

The sublists problem, however, does not fit into this framework very well.
While |dc| (which is our |subs|) has type |L a -> L (L a)| in the specification,
Bird noticed that we need binomial trees to enable the bottom-up construction, therefore |cd| (our |up|) has type |B a -> B (L a)|.
Rather than constructing |cd| from a specification having |dc|,
Bird introduced |cd| out of the blue, before introducing another equally cryptic |dc' :: B a -> L (B a)| and claiming that |dc' . cd = mapF cd . dc'|.

%format mapB2 = "{" mapB "}^2"
%format mapB3 = "{" mapB "}^3"
%format mapBn = "{" mapB "}^{n}"
%format mapBn1 = "{" mapB "}^{n-1}"

In this pearl we reviewed this problem from the basics,
and instead proposed \eqref{eq:up-spec-B} as a specification of |up|, as well as the property that drives the entire derivation.
Look at the expanded top-down algorithm again:
\begin{equation*}
 |g . mapB g {-"~"-}...{-"~"-} mapBn1 g . mapBn (f . ex) . mapBn1 subs {-"~"-}... {-"~"-} mapB2 subs . emph (mapB subs . subs) {-"~~,"-}|
\end{equation*}
(The above is \eqref{eq:td-expanded} with |(mapF, dc) := (mapB, subs)|.)
Property \eqref{eq:up-spec-B} turns the \emph{outermost}
|emph (mapB subs . subs)|, which is |mapB sub . ch (n-1)|, into |up . ch (n-2)|.
That is, |up| is generated from the outside, before being shunted leftwards using naturality.
This fits the problem better: we do not need a |dc' :: B a -> L (B a)|,
and we need only one inductive proof.

%} %% emph

The moral of this story is that while many bottom-up algorithms look alike --- they all have the form |post . iters step . pre|, the reason why they work could be very different.
It is likely that there are more patterns yet to be discovered.

\paragraph*{Acknowledgements}~ The author would like to thank Hsiang-Shang Ko and Jeremy Gibbons for many in-depth discussions throughout the development of this work, Conor McBride for discussion at a WG 2.1 meeting, and Yu-Hsuan Wu and Chung-Yu Cheng for proof-reading drafts of this pearl.
The examples of how the immediate sublists problem may be put to work was suggested by Meng-Tsung Tsai.

%\paragraph*{Conflicts of interest}~ None.

%\bibliographystyle{common/jfplike}
%\bibliography{common/bib}
\input{sublists.bbl}

\end{document}
