\documentclass[dvipsnames, fleqn]{article}

%% lhs2Tex proofs.lhs | pdflatex --jobname=proofs

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

\definecolor{mediumpersianblue}{rgb}{0.0, 0.4, 0.65}
\everymath{\color{mediumpersianblue}}
\apptocmd{\[}{\color{mediumpersianblue}}{}{}
\AtBeginEnvironment{equation}{\color{mediumpersianblue}}
\AtBeginEnvironment{equation*}{\color{mediumpersianblue}}

%if False
\begin{code}
(===) :: a -> a -> a
(===) = undefined

infixr 0 ===
\end{code}
%endif

%format map' = "\Varid{L}"

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
%format mapB = "\Varid{B}"

\begin{document}

\title{Bottom-Up Computation Using Trees of Sublists: Proofs}
\author{Shin-Cheng Mu}
\author{\color{black}Shin-Cheng Mu}
\date{%
Institute of Information Science, Academia Sinica
}

\maketitle

\begin{abstract}
Proofs accompanying the paper Bottom-Up Computation Using Trees of Sublists.
\end{abstract}


\section{Definitions}

%format T0
%format Tn = "\Conid{T}_{\Varid{n}}"
%format unTn = "\Varid{unT}_{\Varid{n}}"
%format Nat = "\mathbb{N}"
%format bot = "{\bot}"

Non-dependently typed version of the binomial tree:
\begin{code}
data B a = T a | N (B a) (B a) {-"~~,"-}
\end{code}
equipped with its |map| and |zip|:
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
And we have |unT (T x) = x|.

In fact, we do not generate all trees. The shapes of trees we generate correspond to the function |ch|, a tree version of the function that chooses a given number of elements from a list:
The shape
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

We may also constraint the shape of the trees by dependent type:
\begin{spec}
data B (a : Set) : Nat -> Nat -> Set where
  T0  : a -> B a 0 n
  Tn  : a -> B a (suc n) (suc n)
  N   : B a k n -> B a (suc k) n -> B a (suc k) (suc n) {-"~~."-}
\end{spec}
For this note we will stay in the non-dependently typed world.

%if False
\begin{code}
type L a = [a]
type Nat = Int

map' :: (a -> b) -> L a -> L b
map' = map

subs :: L a -> L (L a)
subs []      = []
subs (x:xs)  = map' (x:) (subs xs) ++ [xs]

snoc :: L a -> a -> L a
snoc xs x = xs ++ [x]

unT (T x) = x
\end{code}
%endif

\section{Upgrade}

The paper derived the following function |up|:
\begin{code}
up :: B a -> B (L a)
up (N (T p)  (T q)  ) = T [p,q]
up (N t      (T q)  ) = T (unT (up t) ++ [q])
up (N (T p)  u      ) = N (mapB (\q -> [p,q]) u) (up u)
up (N t      u      ) = N (zipBW snoc (up t) u) (up u) {-"~~."-}
\end{code}
With dependent type, |up| could be typed
\begin{spec}
up : forall {a k n} -> (0 < k) -> (k < n) -> B a k n -> B (Vec a (1+k)) (1+k) n {-"~~,"-}
\end{spec}
but again, we stay in the non-dependent realm in this note.

The derivation of |up| was driven by trying to prove the following theorem:
\begin{theorem}
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
\end{theorem}
And here is the constructed proof.
\begin{proof}
The proof is is an induction on |xs|.
The case analysis follows the shape of |ch (1+k) xs| (on the RHS of \eqref{eq:up-spec-B}).
Therefore, there is a base case, a case when |xs| is non-empty and |1+k = length xs|, and a case when |1+k < length xs|.
However, since the constraints demand that |xs| has at least two elements, the base case will be lists of length |2|, and in the inductive cases the length of the list will be at least |3|.

\paragraph*{Case 1.~~} |xs := [y,z]|.\\
The constraints force |k| to be |1|.
We reason:
%if False
\begin{code}
derUp1 :: a -> a -> B (L (L a))
derUp1 y z =
\end{code}
%endif
\begin{code}
    mapB subs (ch 2 [y,z])
  ===  {- def. of |ch| -}
    mapB subs (T [y,z])
  ===  {- def. of |mapB| and |subs| -}
    T [[y],[z]]
  ===  {- definition of |up| -}
    up (N (T [y]) (T [z]))
  ===  {- def. of |ch| -}
    up (ch 1 [y,z]) {-"~~."-}
\end{code}

\paragraph*{\bf Case 2.~~} |xs := x:xs|, |k := 1+k|, where |length xs >= 2|, and |1+(1+k) = length (x:xs)|.
%if False
\begin{code}
derUp2 :: Nat -> a -> L a -> B (L (L a))
derUp2 k x xs =
\end{code}
%endif
\begin{code}
    up (ch (1+k) (x:xs))
  ===  {- def. of |ch|, since |1+k < length (x:xs)| -}
    up (N (mapB (x:) (ch k xs)) (ch (1+k) xs))
  ===  {- def. of |ch|, since |1+k = length xs| -}
    up (N (mapB (x:) (ch k xs)) (T xs))
  ===  {- def. of |up| -}
    T (unT (up (mapB (x:) (ch k xs))) ++ [xs])
  ===  {- |up| natural -}
    T (unT (mapB (map' (x:)) (up (ch k xs))) ++ [xs])
  ===  {- induction -}
    T (unT (mapB (map' (x:)) (mapB subs (ch (1+k) xs))) ++ [xs])
  ===  {- def. of |ch|, since |1+k = length xs| -}
    T (unT (mapB (map' (x:)) (mapB subs (T xs))) ++ [xs])
  ===  {- def. of |mapB| and |map'| -}
    T (map' (x:) (subs xs) ++ [xs])
  ===  {- def. of |subs| -}
    T (subs (x:xs))
  ===  {- def. of |mapB| -}
    mapB subs (T (x:xs))
  ===  {- def. of |ch|, since |2+k = length (x:xs)| -}
    mapB subs (ch (2+k) (x:xs)) {-"~~."-}
\end{code}

\paragraph*{\bf Case 3.~~} |xs := x:xs|, |k := 1+k|, where |length xs >= 2|, and |1+(1+k) < length (x:xs)|.
\\
The constraints become |2 <= 2+k < length (x:xs)|. The property to prove is:
\begin{spec}
  up (ch (1+k) (x:xs)) = mapB subs (ch (2+k) (x:xs)) {-"~~."-}
\end{spec}
We split this into two sub-cases:

\paragraph*{\bf Case 3.1~~} |k := 0|.
%if False
\begin{code}
derUp31 :: a -> L a -> B (L (L a))
derUp31 x xs =
\end{code}
%endif
\begin{code}
     up (ch 1 (x:xs))
   ===   {- def. of |ch|, since |1 < length (x:xs)| -}
     up (N (mapB (x:) (ch 0 xs)) (ch 1 xs))
   ===   {- def. of |ch| -}
     up (N (T [x]) (ch 1 xs))
   ===   {- def. of |up| -}
     N (mapB (\q -> [[x],q]) (ch 1 xs)) (up (ch 1 xs))
   ===   {- (*) see below -}
     N (mapB (subs . (x:)) (ch 1 xs)) (up (ch 1 xs))
   ===   {- induction -}
     N (mapB (subs . (x:)) (ch 1 xs)) (mapB subs (ch 2 xs))
   ===   {- def. of |mapB| -}
     mapB subs (N (mapB (x:) (ch 1 xs)) (ch 2 xs))
   ===   {- def. of |ch|, since |2 < length (x:xs)| -}
     mapB subs (ch 2 (x:xs))  {-"~~."-}
\end{code}
The step (*) holds because every tip in |ch 1 xs| is a singleton list, and for a singleton list |[z]|, we have |subs (x:[z]) = [[x],[z]]|.

\paragraph*{\bf Case 3.2~~} |0 < k| (and |k < length xs - 1|).
For this case we need the following auxiliary properties. Recall that
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

We reason:
%if False
\begin{code}
derUp32 :: Nat -> a -> L a -> B (L (L a))
derUp32 k x xs =
\end{code}
%endif
\begin{code}
     up (ch (1+k) (x:xs))
   ===   {- def. of |ch|, since |1+k < length (x:xs)| -}
     up (N (mapB (x:) (ch k xs)) (ch (1+k) xs)) {-"~~."-}
   ===   {- def. of |up|, since |k /= 0| and |1+k < length xs| -}
     N  (zipBW snoc (up . mapB (x:) . ch k $ xs) (ch (1+k) xs))
        (up (ch (1+k) xs))
\end{code}
Let us focus on the first argument to |N|:
%if False
\begin{code}
derUp32a :: Nat -> a -> L a -> B (L (L a))
derUp32a k x xs =
\end{code}
%endif
\begin{code}
        zipBW snoc (up . mapB (x:) . ch k $ xs) (ch (1+k) xs)
    ===   {- |up| natural -}
        zipBW snoc  (mapB (map' (x:)) . up . ch k $ xs) (ch (1+k) xs)
    ===   {- induction -}
        zipBW snoc  (mapB (map' (x:) . subs) (ch (1+k) xs)) (ch (1+k) xs)
    ===   {- by \eqref{eq:map-sub-zipBW} -}
        mapB (subs . (x:)) (ch (1+k) xs)  {-"~~."-}
\end{code}
We continue:
%if False
\begin{code}
derUp32b :: Nat -> a -> L a -> B (L (L a))
derUp32b k x xs =
\end{code}
%endif
\begin{code}
     N  (zipBW snoc (up . mapB (x:) . ch k $ xs) (ch (1+k) xs))
        (up (ch (1+k) xs))
   ===   {- calculation above -}
     N (mapB (subs . (x:)) (ch (1+k) xs)) (up (ch (1+k) xs))
   ===   {- induction -}
     N (mapB (subs . (x:)) (ch (1+k) xs)) (mapB subs (ch (2+k) xs))
   ===   {- def. of |mapB| -}
     mapB subs (N (mapB (x:) (ch (1+k) xs)) (ch (2+k) xs))
   ===   {- def. of |ch| -}
     mapB subs (ch (2+k) (x:xs)) {-"~~."-}
\end{code}
\end{proof}

\section{Top-Down and Bottom-Up Algorithms}

%format rep' (k) f = "{"f"}^{"k"}"

The generic top-down algorithm is defined by:
\begin{spec}
td :: Nat -> L X -> Y
td 0      = f . ex
td (1+n)  = g . map' (td n) . subs {-"~~."-}
\end{spec}
The intention is that |td n| is a function defined for inputs of length exactly |1+n|.
The aim is to show that
\begin{theorem} \label{thm:td-bu}
For all |n :: Nat| we have |td n = bu n|, where
\begin{code}
bu n = unT . rep' n (mapB g . up) . mapB ex . ch 1 . map' f {-"~~."-}
\end{code}
\end{theorem}
\noindent That is, the top-down algorithm |td n| is equivalent to a bottom-up algorithm |bu n|, where the input is preprocessed by |mapB ex . ch 1 . map' f|, followed by |n| steps of |mapB g . up|. By then we will get a singleton tree, whose content can be extracted by |unT|.

It helps to define a variation:
\begin{spec}
td' :: Nat -> L Y -> Y
td' 0      = ex
td' (1+n)  = g . map' (td' n) . subs {-"~~."-}
\end{spec}
%if False
\begin{code}
td :: Nat -> L X -> Y
td 0  = f . ex
td n  = g . map' (td (n-1)) . subs {-"~~,"-}

td' :: Nat -> L Y -> Y
td' 0  = ex
td' n  = g . map' (td' (n-1)) . subs {-"~~."-}

ex [x] = x

data X
data Y
f :: X -> Y
f = undefined
g :: L Y -> Y
g = undefined

rep :: Nat -> (a -> a) -> a -> a
rep 0  f = id
rep k  f = rep (k-1) f . f {-"~~."-}

rep' :: Nat -> (a -> a) -> a -> a
rep' = rep
\end{code}
%endif
The difference is that |td'| calls only |ex| in the base case.
It is a routine induction showing that
\begin{equation}
\label{eq:td-td'-map}
|td n = td' n . map' f|\mbox{~~.}
\end{equation}
All the calls to |f| are thus factored to the beginning of the algorithm.
We will then be focusing on transforming |td'|.

Our aim is to show that |td' n| can be performed by |n| steps of |mapB g . up|, plus some pre and post processing.
%
Our derivation, however, has to introduce the last step (that is, the leftmost |mapB g . up|, when the steps are composed together) separately from the other steps.

Note that |subs| is a special case of |choose|.
That is, for |xs| such that |length xs = 1+n| we have
\begin{equation}
\label{eq:unT-up-choose}
|subs xs = unT . up . ch n $ xs {-"~~."-}|
\end{equation}

Now we calculate:
%if False
\begin{code}
derTd1 :: Nat -> L X -> Y
derTd1 n =
\end{code}
%endif
\begin{code}
     td (1+n)
 ===   {- by\eqref{eq:td-td'-map} -}
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
We have thus established that
\begin{equation}
\label{eq:td'-fst-step}
|td (1+n) = unT . mapB g . up . mapB (td' n) . ch (1+n) . map' f|
\mbox{~~.}
\end{equation}
The intention is that we factored out the last |mapB g . up|.

For the other steps, the following lemma shows that |mapB (td' n) . ch (1+n)| can be performed by |n| steps of |mapB g . up|, after some preprocessing.
This is the key lemma that relates \eqref{eq:up-spec-B} to the main algorithm.
\begin{lemma}\label{lma:main}
|mapB (td' n) . ch (1+n) = rep' n (mapB g . up) . mapB ex . ch 1|.
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
     mapB g . up . rep' n (mapB g . up) . mapB ex . ch 1
 ===    {- |(.)| associative, def. of |rep' n f| -}
     rep' (1+n) (mapB g . up) . mapB ex . ch 1 {-"~~."-}
\end{code}
\end{proof}

Putting the pieces together, the following is a proof of Theorem~\ref{thm:td-bu}:
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
 ===    {- by \eqref{eq:td'-fst-step} -}
   unT . mapB g . up . mapB (td' n) . ch (1+n) . map' f
 ===    {- Lemma~\ref{lma:main} -}
   unT . mapB g . up . rep' n (mapB g . up) . mapB ex . ch 1 . map' f
 ===    {- |(.)| associative, def. of |rep' n f| -}
   unT . rep' (1+n) (mapB g . up) . mapB ex . ch 1 . map' f
 ===    {- definition of |bu| -}
   bu (1+n) {-"~~."-}
\end{code}
\end{proof}
\end{document}
