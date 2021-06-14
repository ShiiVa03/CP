\documentclass[a4paper]{article}
\usepackage[a4paper,left=3cm,right=2cm,top=2.5cm,bottom=2.5cm]{geometry}
\usepackage{palatino}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue]{hyperref}
\usepackage{graphicx}
\usepackage{cp2021t}
\usepackage{subcaption}
\usepackage{adjustbox}
\usepackage{color}
\definecolor{red}{RGB}{255,  0,  0}
\definecolor{blue}{RGB}{0,0,255}
\def\red{\color{red}}
\def\blue{\color{blue}}
%================= local x=====================================================%
\def\getGif#1{\includegraphics[width=0.3\textwidth]{cp2021t_media/#1.png}}
\let\uk=\emph
\def\aspas#1{``#1"}
%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const f) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
\def\ana#1{\mathopen{[\!(}#1\mathclose{)\!]}}
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format (cataA (f) (g)) = "\cata{" f "~" g "}_A"
%format (anaA (f) (g)) = "\ana{" f "~" g "}_A"
%format (cataB (f) (g)) = "\cata{" f "~" g "}_B"
%format (cata (f)) = "\cata{" f "}"
%format (anaB (f) (g)) = "\ana{" f "~" g "}_B"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textsc{nb}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format e1 = "e_1 "
%format e2 = "e_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format BTree = "\fun{BTree} "
%format LTree = "\mathsf{LTree}"
%format inNat = "\mathsf{in}"
%format (cataNat (g)) = "\cata{" g "}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%%format (bin (n) (k)) = "\Big(\vcenter{\xymatrix@R=1pt{" n "\\" k "}}\Big)"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (anaLTree (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format delta = "\Delta "

%---------------------------------------------------------------------------

\title{
       	Cálculo de Programas
\\
       	Trabalho Prático
\\
       	MiEI+LCC --- 2020/21
}

\author{
       	\dium
\\
       	Universidade do Minho
}


\date\mydate

\makeindex
\newcommand{\rn}[1]{\textcolor{red}{#1}}
\begin{document}

\maketitle

\begin{center}\large
\begin{tabular}{ll}
\textbf{Grupo} nr. & 16
\\\hline
a93322 & Tiago Costa 
\\
a93227 & Pedro Paulo Tavares 
\\
a93221 & André Vaz 
\\
\end{tabular}
\end{center}

\section{Preâmbulo}

\CP\ tem como objectivo principal ensinar
a progra\-mação de computadores como uma disciplina científica. Para isso
parte-se de um repertório de \emph{combinadores} que formam uma álgebra da
programação (conjunto de leis universais e seus corolários) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto é,
agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos dois cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell\ (sem prejuízo da sua aplicação a outras linguagens
funcionais). Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell.  Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

\section{Documentação} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma técnica de programa\-ção dita
``\litp{literária}'' \cite{Kn92}, cujo princípio base é o seguinte:
%
\begin{quote}\em Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o código fonte e a documentação de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} é
um pre-processador que faz ``pretty printing''
de código Haskell em \Latex\ e que deve desde já instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2021t.lhs
\end{Verbatim}

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (fac)
import Nat
import LTree
import Data.List hiding (find)
import Test.QuickCheck hiding ((><),choose,collect)
import qualified Test.QuickCheck as QuickCheck
import Graphics.Gloss
import Graphics.Gloss.Interface.Pure.Game
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
\end{code}
%endif

\noindent Abra o ficheiro \texttt{cp2021t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho teórico-prático deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder às questões que serão colocadas
na \emph{defesa oral} do relatório.

Em que consiste, então, o \emph{relatório} a que se refere o parágrafo anterior?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-á ainda instalar o utilitário
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
geração de gráficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invocá-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o número de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) código
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
código \Haskell\ relativo aos problemas que se seguem. Esse anexo deverá
ser consultado e analisado à medida que isso for necessário.

\subsection{Stack}

O \stack{Stack} é um programa útil para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito específica:

\begin{itemize}
\item Os módulos auxiliares encontram-se na pasta \emph{src}.
\item O módulos principal encontra-se na pasta \emph{app}.
\item A lista de depêndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as depêndencias externas serão instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados algébricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Graças à sua flexibilidade,
torna-se trivial implementar \DSL s
e até mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programação}.

Paralelamente, um tópico bastante estudado no âmbito de \DL\
é a derivação automática de expressões matemáticas, por exemplo, de derivadas.
Duas técnicas que podem ser utilizadas para o cálculo de derivadas são:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplicação sucessiva de transformações
(leia-se: funções) que sejam congruentes com as regras de derivação. O resultado
final será a expressão da derivada.

O leitor atento poderá notar um problema desta técnica: a expressão
inicial pode crescer de forma descontrolada, levando a um cálculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da expressão em todos os passos.
Para tal, é necessário calcular o valor da expressão \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de expressões matemáticas simples e
implementar as duas técnicas de derivação automática.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam operações binárias e unárias, respectivamente:

\begin{code}
data BinOp = Sum
           | Product
           deriving (Eq, Show)

data UnOp = Negate
          | E
          deriving (Eq, Show)
\end{code}

\noindent
O construtor |E| simboliza o exponencial de base $e$.

Assim, cada expressão pode ser uma variável, um número, uma operação binária
aplicada às devidas expressões, ou uma operação unária aplicada a uma expressão.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na notação matemática habitual.

\begin{enumerate}
\item A definição das funções |inExpAr| e |baseExpAr| para este tipo é a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as funções |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| são testemunhas de um isomorfismo,
    isto é,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma expressão aritmética e um escalar para substituir o |X|,
	a função

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da expressão. Na página \pageref{pg:P1}
    esta função está expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A função |eval_exp| respeita os elementos neutros das operações.
\begin{code}
prop_sum_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idr a exp = eval_exp a exp .=?=. sum_idr where
  sum_idr = eval_exp a (Bin Sum exp (N 0))

prop_sum_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idl a exp = eval_exp a exp .=?=. sum_idl where
  sum_idl = eval_exp a (Bin Sum (N 0) exp)

prop_product_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idr a exp = eval_exp a exp .=?=. prod_idr where
  prod_idr = eval_exp a (Bin Product exp (N 1))

prop_product_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idl a exp = eval_exp a exp .=?=. prod_idl where
  prod_idl = eval_exp a (Bin Product (N 1) exp)

prop_e_id :: (Floating a, Real a) => a -> Bool
prop_e_id a = eval_exp a (Un E (N 1)) == expd 1

prop_negate_id :: (Floating a, Real a) => a -> Bool
prop_negate_id a = eval_exp a (Un Negate (N 0)) == 0
\end{code}
    \end{propriedade}
    \begin{propriedade}
      Negar duas vezes uma expressão tem o mesmo valor que não fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item É possível otimizar o cálculo do valor de uma expressão aritmética tirando proveito
  dos elementos absorventes de cada operação. Implemente os genes da função
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na página \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual é a vantagem de implementar a função |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A função |optimize_eval| respeita a semântica da função |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma expressão, é necessário aplicar transformações
à expressão original que respeitem as regras das derivadas:\footnote{%
	Apesar da adição e multiplicação gozarem da propriedade comutativa,
	há que ter em atenção a ordem das operações por causa dos testes.}

\begin{itemize}
  \item Regra da soma:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)+g(x))=\frac{d}{dx}(f(x))+\frac{d}{dx}(g(x))
\end{eqnarray*}
  \item Regra do produto:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)g(x))=f(x)\cdot \frac{d}{dx}(g(x))+\frac{d}{dx}(f(x))\cdot g(x)
\end{eqnarray*}
\end{itemize}

  Defina o gene do catamorfismo que ocorre na função
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma expressão aritmética, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A função |sd| respeita as regras de derivação.
\begin{code}
prop_const_rule :: (Real a, Floating a) => a -> Bool
prop_const_rule a = sd (N a) == N 0

prop_var_rule :: Bool
prop_var_rule = sd X == N 1

prop_sum_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_sum_rule exp1 exp2 = sd (Bin Sum exp1 exp2) == sum_rule where
  sum_rule = Bin Sum (sd exp1) (sd exp2)

prop_product_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_product_rule exp1 exp2 = sd (Bin Product exp1 exp2) == prod_rule where
  prod_rule =Bin Sum (Bin Product exp1 (sd exp2)) (Bin Product (sd exp1) exp2)

prop_e_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_e_rule exp = sd (Un E exp) == Bin Product (Un E exp) (sd exp)

prop_negate_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_negate_rule exp = sd (Un Negate exp) == Un Negate (sd exp)
\end{code}
    \end{propriedade}

\item Como foi visto, \emph{Symbolic differentiation} não é a técnica
mais eficaz para o cálculo do valor da derivada de uma expressão.
\emph{Automatic differentiation} resolve este problema cálculando o valor
da derivada em vez de manipular a expressão original.

  Defina o gene do catamorfismo que ocorre na função
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma expressão aritmética e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a expressão original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| é equivalente a calcular a derivada da expressão e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) é fácil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci, recordar
o sistema
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções mutuamente recursivas.
\item	Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos, mas numa primeira leitura
dá jeito usarem-se tais nomes.}
\item	Para os resultados vão-se buscar as expressões respectivas, retirando a variável |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das funções, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol18} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos das aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b)
\end{code}
O que se pede então, nesta pergunta?
Dada a fórmula que dá o |n|-ésimo \catalan{número de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementação de $C_n$ que não calcule factoriais nenhuns.
Isto é, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta função.

\begin{propriedade}
A função proposta coincidem com a definição dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugestão}: Começar por estudar muito bem o processo de cálculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da função exponencial.


\Problema

As \bezier{curvas de Bézier}, designação dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre Bézier},
são curvas ubíquas na área de computação gráfica, animação e modelação.
Uma curva de Bézier é uma curva paramétrica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ é a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de Bézier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} é um método recursivo capaz de calcular
curvas de Bézier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo é numericamente mais estável, trocando velocidade por correção.

De forma sucinta, o valor de uma curva de Bézier de um só ponto $\{P_0\}$
(ordem $0$) é o próprio ponto $P_0$. O valor de uma curva de Bézier de ordem
$N$ é calculado através da interpolação linear da curva de Bézier dos primeiros
$N-1$ pontos e da curva de Bézier dos últimos $N-1$ pontos.

A interpolação linear entre 2 números, no intervalo $[0, 1]$, é dada pela
seguinte função:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpolação linear entre 2 pontos de dimensão $N$ é calculada através
da interpolação linear de cada dimensão.

O tipo de dados |NPoint| representa um ponto com $N$ dimensões.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimensões e um ponto de 3 dimensões podem ser
representados, respetivamente, por:
\begin{spec}
p2d = [1.2, 3.4]
p3d = [0.2, 10.3, 2.4]
\end{spec}
%
O tipo de dados |OverTime a| representa um termo do tipo |a| num dado instante
(dado por um |Float|).
\begin{code}
type OverTime a = Float -> a
\end{code}
%
O anexo \ref{sec:codigo} tem definida a função
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpolação linear entre 2 pontos, e a função
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua definição com a propriedade:
    \begin{propriedade} Definição alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a função |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de Bézier são simétricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a função |runBezier| e aprecie o seu trabalho\footnote{%
        A representação em Gloss é uma adaptação de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que é aberta (que contém, a verde, um ponto
        inicila) com o botão esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a fórmula que calcula a média de uma lista não vazia $x$,
\begin{equation}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto é, para sabermos a média de uma lista precisamos de dois catamorfismos: o que faz o somatório e o que calcula o comprimento a lista.
Contudo, é facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ está em recursividade mútua com $length$ e o par de funções pode ser expresso por um único catamorfismo, significando que a lista apenas é percorrida uma vez.

\begin{enumerate}

\item	Recorra à lei de recursividade mútua para derivar a função
|avg_aux = cata (either b q)| tal que
|avg_aux = split avg length| em listas não vazias.

\item	Generalize o raciocínio anterior para o cálculo da média de todos os elementos de uma \LTree\ recorrendo a uma única travessia da árvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas funções testando a propriedade seguinte:
\begin{propriedade}
A média de uma lista não vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 milésimas:
\begin{code}
prop_avg :: [Double] -> Property
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta questão é \textbf{opcional} e funciona como \textbf{valorização} apenas para os alunos que desejarem fazê-la.)

\vskip 1em \noindent
Existem muitas linguagens funcionais para além do \Haskell, que é a linguagem usada neste trabalho prático. Uma delas é o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os módulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede é a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execução: o código que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para além disso, os grupos podem demonstrar o código na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2tex}
Como primeiro exemplo, estudar o texto fonte deste trabalho para obter o
efeito:\footnote{Exemplos tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
	|id = split f g|
%
\just\equiv{ universal property }
%
        |lcbr(
		p1 . id = f
	)(
		p2 . id = g
	)|
%
\just\equiv{ identity }
%
        |lcbr(
		p1 = f
	)(
		p2 = g
	)|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo à \emph{package} \LaTeX\
\href{https://ctan.org/pkg/xymatrix}{xymatrix}, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Programação dinâmica por recursividade múltipla}\label{sec:recmul}
Neste anexo dão-se os detalhes da resolução do Exercício \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, página \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o cálculo da aproximação até |i=n| da função exponencial $exp\ x = e^x$,
via série de Taylor:
\begin{eqnarray}
	exp\ x
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a função que dá essa aproximação.
É fácil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
mútua. Se repetirmos o processo para |h x n| etc obteremos no total três funções nessa mesma
situação:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na página \ref{pg:regra} deste enunciado,
ter-se-á, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Definição da série de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Oráculo para inspecção dos primeiros 26 números de Catalan\footnote{Fonte:
\catalan{Wikipedia}.}:
\begin{code}
oracle = [
    1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440, 9694845,
    35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452
    ]
\end{code}

\subsection*{Problema 3}
Algoritmo:
\begin{spec}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] = nil
deCasteljau [p] = const p
deCasteljau l = \pt -> (calcLine (p pt) (q pt)) pt where
  p = deCasteljau (init l)
  q = deCasteljau (tail l)
\end{spec}
Função auxiliar:
\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine [] = const nil
calcLine(p:x) = curry g p (calcLine x) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{spec}
2D:
\begin{code}
bezier2d :: [NPoint] -> OverTime (Float, Float)
bezier2d [] = const (0, 0)
bezier2d l = \z -> (fromRational >< fromRational) . (\[x, y] -> (x, y)) $ ((deCasteljau l) z)
\end{code}
Modelo:
\begin{code}
data World = World { points :: [NPoint]
                   , time :: Float
                   }
initW :: World
initW = World [] 0

tick :: Float -> World -> World
tick dt world = world { time=(time world) + dt }

actions :: Event -> World -> World
actions (EventKey (MouseButton LeftButton) Down _ p) world =
  world {points=(points world) ++ [(\(x, y) -> map toRational [x, y]) p]}
actions (EventKey (SpecialKey KeyDelete) Down _ _) world =
    world {points = cond (== []) id init (points world)}
actions _ world = world

scaleTime :: World -> Float
scaleTime w = (1 + cos (time w)) / 2

bezier2dAtTime :: World -> (Float, Float)
bezier2dAtTime w = (bezier2dAt w) (scaleTime w)

bezier2dAt :: World -> OverTime (Float, Float)
bezier2dAt w = bezier2d (points w)

thicCirc :: Picture
thicCirc = ThickCircle 4 10

ps :: [Float]
ps = map fromRational ps' where
  ps' :: [Rational]
  ps' = [0, 0.01..1] -- interval
\end{code}
Gloss:
\begin{code}
picture :: World -> Picture
picture world = Pictures
  [ animateBezier (scaleTime world) (points world)
  , Color white . Line . map (bezier2dAt world) $ ps
  , Color blue . Pictures $ [Translate (fromRational x) (fromRational y) thicCirc | [x, y] <- points world]
  , Color green $ Translate cx cy thicCirc
  ] where
  (cx, cy) = bezier2dAtTime world
\end{code}
Animação:
\begin{code}
animateBezier :: Float -> [NPoint] -> Picture
animateBezier _ [] = Blank
animateBezier _ [_] = Blank
animateBezier t l = Pictures
  [ animateBezier t (init l)
  , animateBezier t (tail l)
  , Color red . Line $ [a, b]
  , Color orange $ Translate ax ay thicCirc
  , Color orange $ Translate bx by thicCirc
  ] where
  a@(ax, ay) = bezier2d (init l) t
  b@(bx, by) = bezier2d (tail l) t
\end{code}
Propriedades e \emph{main}:
\begin{code}
runBezier :: IO ()
runBezier = play (InWindow "Bézier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compilação e execução dentro do interpretador:\footnote{Pode ser útil em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma função
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
Código para geração de testes:
\begin{code}
instance Arbitrary UnOp where
  arbitrary = elements [Negate, E]

instance Arbitrary BinOp where
  arbitrary = elements [Sum, Product]

instance (Arbitrary a) => Arbitrary (ExpAr a) where
  arbitrary = do
    binop <- arbitrary
    unop  <- arbitrary
    exp1  <- arbitrary
    exp2  <- arbitrary
    a     <- arbitrary

    frequency . map (id >< pure) $ [(20, X), (15, N a), (35, Bin binop exp1 exp2), (30, Un unop exp1)]


infixr 5 .=?=.
(.=?=.) :: Real a => a -> a -> Bool
(.=?=.) x y = (toRational x) == (toRational y)


\end{code}

\subsection*{Outras funções auxiliares}
%----------------- Outras definições auxiliares -------------------------------------------%
Lógicas:
\begin{code}
infixr 0 .==>.
(.==>.) :: (Testable prop) => (a -> Bool) -> (a -> prop) -> a -> Property
p .==>. f = \a -> p a ==> f a

infixr 0 .<==>.
(.<==>.) :: (a -> Bool) -> (a -> Bool) -> a -> Property
p .<==>. f = \a -> (p a ==> property (f a)) .&&. (f a ==> property (p a))

infixr 4 .==.
(.==.) :: Eq b => (a -> b) -> (a -> b) -> (a -> Bool)
f .==. g = \a -> f a == g a

infixr 4 .<=.
(.<=.) :: Ord b => (a -> b) -> (a -> b) -> (a -> Bool)
f .<=. g = \a -> f a <= g a

infixr 4 .&&&.
(.&&&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
f .&&&. g = \a -> ((f a) && (g a))
\end{code}

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o "layout" que se fornece. Não podem ser
alterados os nomes ou tipos das funções dadas, mas pode ser adicionado
texto, disgramas e/ou outras funções auxiliares que sejam necessárias.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções
simples e elegantes.

\subsection*{Problema 1} \label{pg:P1}
São dadas:
\begin{code}
cataExpAr g = g . recExpAr (cataExpAr g) . outExpAr
anaExpAr g = inExpAr . recExpAr (anaExpAr g) . g
hyloExpAr h g = cataExpAr h . anaExpAr g

eval_exp :: Floating a => a -> (ExpAr a) -> a
eval_exp a = cataExpAr (g_eval_exp a)

optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
optmize_eval a = hyloExpAr (gopt a) clean

sd :: Floating a => ExpAr a -> ExpAr a
sd = p2 . cataExpAr sd_gen

ad :: Floating a => a -> ExpAr a -> a
ad v = p2 . cataExpAr (ad_gen v)
\end{code}
Definir:\par

Para definirmos a função outExpAr temos de ter em atenção o tipo de saída, ou seja, OutExpAr.
É então fácil definir esta função tal como todos os outros tipos já previamente definidos.
Para o construtor X inserimos o único elemento do tipo 1 na parte esquerda do coproduto. E seguimos 
o mesmo raciocínio para os outros construtores.\par
\begin{code}

outExpAr :: ExpAr a -> OutExpAr a 
outExpAr X = i1 ()
outExpAr (N a) = i2 . i1 $ a
outExpAr (Bin op a b) = i2 . i2 . i1 $ (op, (a, b))
outExpAr (Un op a) = i2 . i2 . i2 $ (op, a)
\end{code}

A função recExpAr é o functor do tipo ExpAr, ou seja, queremos preservar os respetivos construtores e aplicar 
a função g à expressão.\par

\begin{code}

recExpAr g = baseExpAr id id id g g id g

\end{code}

A função eval\_exp é um catamorfismo, logo temos de definir o gene desta. Assim, a função g\_eval\_exp é 
o gene deste catamorfismo. Através de um diagrama é fácil de ver o catamorfismo.


\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr A|
           \ar[d]_-{|cataNat g_eval_exp|}
&
    |OutExpAr A|
           \ar[d]^{|recExpAr eval_exp|}
           \ar[l]_-{|inNat|}
\\
     |A|
&
     |1 + (A + ((BinOp,(A,A)) + (UnOp,A)) | 
           \ar[l]^-{|g_eval_exp|}
}
\end{eqnarray*}

Através do diagrama conseguimos perceber que para avaliar uma expressão temos vários pontos :
\begin{itemize}
\item Se tivermos X, temos que dar o valor que recebemos.
\item Se tivermos uma constante (N \emph{natural}) devolvemos esse natural
\item Se tivermos uma operação binária temos de aplicar essa operação de forma \emph{uncurried} porque recebemos um par
\item Se tivermos uma operação unária basta aplicar a função
\end{itemize}

\begin{code}

g_eval_exp a = either (const a) (either id (either (uncurry binOp) (uncurry unOp))) where
    binOp Sum = uncurry (+)
    binOp Product = uncurry (*)
    unOp Negate = negate
    unOp E = expd

\end{code}

Para a otimização desta avaliação de expressões podemos implementar esta avaliação como um hilomorfismo. A vantagem
desta forma de avaliação em vez de um "gene" inteligente é o facto de se a expressão crescer de forma descontrolada 
e, por vezes, sem necessidade porque é um produto por zero.

Assim, o passo de \emph{divide} deste hilomorfismo, é a funçao \emph{clean}, que tira partido dos elemntos absorventes
das operações. Ou seja, o resultado do produto por zero de uma expressão pode ser logo zero.


\begin{code}

clean X = i1()
clean (N a) = i2(i1 a)
clean (Bin Sum (N 0) a) = clean a 
clean (Bin Sum a (N 0)) = clean a
clean (Bin Product (N 0) _) = i2(i1 0)
clean (Bin Product _ (N 0)) = i2(i1 0)
clean (Bin op a b) = i2 . i2 . i1 $ (op, (a, b))
clean (Un op a) = i2.i2.i2 $ (op,a)

gopt a = g_eval_exp a
 
\end{code}

Para a derivada de uma expressão seguindo \emph{symbolic differentiation}, alterando a expressão de forma recursiva.
Para o gene deste catamorfismo temos de obrigatoriamente dar um par de expressões porque na primeira componente do par
temos de preservar a expressão original para a regra do produto. Deste modo temos que o gene deste catamorfismo é composto 
pelas várias regras da derivação : 
\begin{itemize}
\item Se recebemos um X então a sua derivada é 1. O par é então (X,N 1)
\item Se recebemos um número natural devolvemos o par (N x, N 0)
\item Se recebemos a soma de duas expressões já derivadas é apenas darmos a soma dessas derivadas
\item Se recebemos o produto então temos de aplicar a regra do produto usando a pré-condição de termos a expressão original reservada
\item No caso quer da exponenciação quer da negção é apenas aplicar a regra da exponenciação e negar a derivada da expressão resultante respetivamente
\end{itemize}


\begin{code}
sd_gen :: Floating a =>
    Either () (Either a (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a))) (UnOp, (ExpAr a, ExpAr a)))) -> (ExpAr a, ExpAr a)
sd_gen = (either sd1 (either sd2 (either sd3 sd4))) where
      sd1 x = (X, (N 1))
      sd2 y = ((N y),(N 0))
      sd3 (Sum,((a,b),(c,d))) = (Bin Sum a c, Bin Sum b d)
      sd3 (Product,((a,b),(c,d))) = (Bin Product a c, Bin Sum (Bin Product a d) (Bin Product b c))
      sd4 (E,(a,b)) = (Un E a, Bin Product(Un E a) b)
      sd4 (Negate,(a,b)) = (Un Negate a, Un Negate b)
\end{code}

Como referido a técnica de derivação seguindo \emph{symbolic differentiation} não é a mais efeciente, havendo por isso a possibilidade de
derivar a expressão no ponto. Assim, o gene deste catamorfismo torna-se fácil de definir. Usando o mesmo diagrama definido mais acima neste 
documento basta substituir o tipo de retorno por Naturais e, assim, passamos não a lidar com expressões mas sim com números, sendo a derivação mais fácil.\par
\begin{code}
ad_gen v = (either g1 (either g2 (either g3 g4))) where
      g1 x = (v, 1)
      g2 y = (y,0)
      g3 (Sum,((a,b),(c,d))) = (a+c, b + d)
      g3 (Product,((a,b),(c,d))) = (a*c, (a*d)+(b*c))
      g4 (E,(a,b)) = ((expd a), (expd a) * b)
      g4 (Negate,(a,b)) = ((negate a), negate b)
\end{code}

\subsection*{Problema 2}
Definir
\begin{code}
c 0 = 1
c(n+1) = ((c n) * f n) `div` h n

f 0 = 2
f(n+1) = faux n + f n

faux 0 = 10
faux (n+1) = 8 + faux n

h 0 = 2
h(n+1) = haux n + h n

haux 0 = 4
haux (n+1) = 2 + haux n

    
loop(c,f,faux,h,haux) = ((c*f) `div` h, faux + f, 8 + faux, haux + h, 2 + haux)
inic = (1,2,10,2,4)
prj(c,f,faux,h,haux) = c

\end{code}
por forma a que
\begin{code}
cat = prj . (for loop inic)
\end{code}
seja a função pretendida.
\textbf{NB}: usar divisão inteira.
Apresentar de seguida a justificação da solução encontrada.

Partindo da expressão dada podemo-la expressar como uma recursão.

\begin{spec}
c 0 = 1
c(n+1) = div ((c n) * (2n +2) * (2n +1)) ((n+2)*(n+1))
\end{spec}

De notar que decidimos agrupar a chamada de C\_n com ((2n +2) * (2n +1)) e só depois realizar a divisão graças a ser a divisão inteira,
e , por isso, não realizarmos arredondamentos.\par

Seguidamente, seguindo a regra de algibeira dada, temos então de transformar estas dependências de n por funções que sejam também elas
recursivas e não dependam de n.

Definimos assim as seguintes funções : 
\begin{spec}
f n = (2n +2) * (2n +1)

faux n = 8n + 10

h n = (n+2)*(n+1)

haux n = 2n +4

\end{spec}

Após isto é apenas aplicar de forma direta a regra dada.\par

\subsection*{Problema 3}

\begin{code}


calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine = cataList h where
    h = either h1 h2
    h1 x = const nil
    h2(d,f) [] = nil
    h2(d,f) (x:xs) = \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z

\end{code}

Para definir o catamorfismo \emph{calcLine} baseamo-nos na função auxiliar dada e transformamo-la num catamorfismo.
Assim, temos que o diagrama deste catamorfismo é : 

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |NPoint|
           \ar[d]_-{|calcLine|}
&
    |1 + Q * NPoint|
           \ar[d]^{|id + id * calcLine|}
           \ar[l]_-{|in|}
\\
     |(NPoint -> OverTime NPoint)|
&
     |1 + Q * (Npoint -> OverTime NPoint) | 
           \ar[l]^-{|h|}
}
\end{eqnarray*}

Deste modo o gene torna-se fácil de compreender. Caso a lista recebida seja vazia temos dedar uma função que receba 2 argumentos 
e produza a lista vazia. Caso contrário temos o "passo de recursão" e o que temos de fazer é calcular a tal interpolação linear.

\begin{code}
deCasteljau [] = nil
deCasteljau l = (hyloAlgForm alg coalg) l where
   coalg = (id -|- (split(cons . (id >< init)) p2 )) . outNVL
   alg = either alg1 alg2 where
     alg1 x = const x
     alg2(f,g) = \pt -> calcLine (f pt) (g pt) pt

hyloAlgForm = hyloLTree
 
\end{code}

Para definirmos o hylomorfismo deste problema baseamo-nos na função auxiliar dada pelo professor.Deste modo inferimos que a estrutura 
auxiliar que o anamorfismo deveria criar era um LTree em que cada folha (Leaf) tem elementos do tipo NPoint. Assim, aquando da aplicação
do catamorfismo, basta aplicar ao Fork a função calcLine que obtemos o tipo OverTime NPoint.Partimos também do principio que a lista que recebemos
não é vazia porque fazemos primeiro essa verificação e , por isso, usamos a definiçao de outNVL para o anamorfismo. Diagrama que fundamenta melhor o esquema do 
hylomorfismo : 


Anamorfismo : 
\begin{eqnarray*}
\xymatrix@@C=3cm{
    |[NPoint]|
           \ar[d]^-{|coalg|}
           \ar[r]^-{|(id + (split(cons . (id >< init)) p2)) . outNVL|}
&
    |NPoint + [NPoint] * [NPoint]|
           \ar[d]^-{|id + coalg * coalg|}           
\\
     |LTree NPoint|
&
     |NPoint + LTree NPoint * LTree NPoint| 
        \ar[l]^-{|inLTree|}          
}
\end{eqnarray*}

Catamorfismo :

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |LTree NPoint|
           \ar[d]_-{|alg|}
&
    |NPoint + LTree NPoint * LTree NPoint|
           \ar[d]^{|id + alg * alg|}
           \ar[l]_-{|in|}
\\
     |OverTime NPoint|
&
     |NPoint + OverTime NPoint * OverTime NPoint| 
           \ar[l]^-{|either alg1 alg2|}
}
\end{eqnarray*}

\subsection*{Problema 4}

Solução para listas não vazias:
\begin{code}
avg = p1.avg_aux
\end{code}

Para este problema é necessário definir o "conjunto de leis" dos catamorfismos para listas não vazia.Assim,definimos o \emph{inNVl}, o \emph{outNVL}, o \emph{recNVL} e claro, por fim, o \emph{cataNVL} .
Depois de termos este conjunto definido temos de olhar para o gene deste catamorfismo e perceber 2 coisas :

    A função length pode ser calculada de forma pointwise seguindo o diagrama.

    \begin{eqnarray*}
\xymatrix@@C=2cm{
    |A*|
           \ar[d]_-{|<avg,length>|}
&
    |A + A * (A*)|
           \ar[d]^{|id + id * <avg,length>|}
           \ar[l]_-{|inNVL|}
\\
     |A|
&
     |A + A * (A * A)| 
           \ar[l]^-{|len_gen|}
}
\end{eqnarray*}

A partir deste podemos facilmente obter o gene (len\_gen):
\begin{spec}
len_gen = [g1, g2] where 
g1 x = [x]
g2 (x,(avg,len)) = 1 + len
\end{spec}

Mas a partir das leis do cálculo podemos tornar então em pointfree

\begin{eqnarray*}
\start
	|g1 x = [x]|
%
\just\equiv{ def. singl }
%
  | g1 x = singl x|
%
\just\equiv{ igualdade extensional }
%
  |g1 = singl|
\qed
\end{eqnarray*}

Da mesma maneira podemos então a partir de g2 derivar a sua versão pointfree

\begin{eqnarray*}
\start
	|g2(x,(avg,len)) = 1 + len|
%
\just\equiv{ def. succ }
%
  | g2(x,(avg,len)) = succ len|
%
\just\equiv{ def.comp, def.proj }
%
  |g2(x,(avg,len)) = succ.p2.p2(x,(avg,len))|
\just\equiv{ igualdade extensional}
    |g2 = succ.p2.p2|
\qed
\end{eqnarray*}

Seguindo o mesmo raciocínio e usando o mesmo diagrama, obtemos a \emph{avg}.\par
Neste momento temos então um split de eithers mas queremos um either de splits.Momento oportuno para aplicarmos
a Lei da Troca e obtermos o que abaixo está definido :
\begin{code}

inNVL = either singl cons

outNVL [x] = i1 x
outNVL (a:l) = i2(a,l)

recNVL f = id -|- id >< f

cataNVL g = g . recNVL (cataNVL g) . outNVL


avg_aux = cataNVL (either (split id (const 1)) (split algorit (succ.p2.p2)))where
       algorit(x,(avg,len)) = (x + len*avg) / (1 + len)

\end{code}

Solução para árvores de tipo \LTree:
\begin{code}
avgLTree = p1.cataLTree gene where
   gene = either (split id (const 1)) (split avgLTreeaux ((uncurry (+)).(p2 >< p2))) where
        avgLTreeaux((avgLeft,lenLeft),(avgRight,lenRight)) = 
                                ((avgLeft*lenLeft) + (avgRight*lenRight)) / (lenLeft +lenRight)
\end{code}

Para o tipo LTree podemos também, mais uma vez, aproveitar o diagrama para construirmos o gene deste catamorfismo.
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |LTree A|
           \ar[d]_-{|split avgLTree lenLTree|}
&
    |A + (LTree A * LTree A)|
           \ar[d]^{|id + (split avgLTree lenLTree, split avgLTree lenLTree)|}
           \ar[l]_-{|inLTree|}
\\
     |A * A|
&
     |A + ((A * A) * (A * A))| 
           \ar[l]^-{|tree_gen|}
}
\end{eqnarray*}

Obtemos então o seguinte gene para a len desta àrvore:
\begin{spec}
lenLTree (Leaf) = 1
lenLTree (Fork(e,d)) = lenLTree e + lenLTree d
\end{spec}

Usando as leis do cálculo obtemos então : 

\begin{eqnarray*}
\start
  |lcbr(
		lenLTree(Leaf) = 1
	 )(
    lenLTree (Fork(e,d)) = lenLTree e + lenLTree d
	)|
%
\just\equiv{ def.comp, def-const, def-x }
%
  |lcbr(
		(lenLTree . Leaf) x = (const 1) x
	 )(
    (lenLTree .Fork)(e,d) = uncurry(+) . (lenLTree * lenLTree) (e,d)
	)|
%
\just\equiv{ def.split, def.proj,igualdade extensional }
%
|lcbr(
		(lenLTree . Leaf)= (const 1)
	 )(
    (lenLTree .Fork) = uncurry(+) . (p2 . split avgLTree lenLTree , p2 . split avgLTree lenLTree)
	)|
%
\just\equiv{ def. inLtree, def.funtor-x, eq-+,def-fusao}
    |lenLTree . inLtree = either (const 1) (uncurry(+) . (p2 * p2) . (split avgLTree lenLTree ,split avgLTree lenLTree))|
%
\just\equiv{ def.absorçao-+,def-funtor,universal-cata}
    |len = cataLTree ((const 1), (uncurry(+).(p2 * p2)))|
\qed
\end{eqnarray*}

Para o gene do avgLTree decidimos deixar em versão pointwise porque é de mais fácil leitura e é a aplicação
direta do algoritmo dado.
Para finalizar, como na definição anterior, temos um split de eithers e queremos então um either de splits,usamos
por isso a Lei da troca e obtemos a definição que nós propusemos.\par

\subsection*{Problema 5}
Inserir em baixo o código \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:

\begin{verbatim}
open Cp

// (1) Datatype definition --------------------------------------------------

type BTree<'a> = Empty | Node of ('a * (BTree<'a> * BTree<'a>))

let inBTree x = either (konst Empty) Node x

let outBTree x =
    match x with
    | Empty -> i1 ()
    | Node (y,(t1,t2)) -> i2 (y,(t1,t2))


// (2) Ana + cata + hylo -------------------------------------------------------
// recBTree g = id -|- (id >< (g >< g))

let baseBTree f g x = (id -|- (f >< (g >< g))) x

let recBTree g x = baseBTree id g x        
let rec cataBTree a x = (a << (recBTree (cataBTree a)) << outBTree) x

let rec anaBTree f x = (inBTree << (recBTree (anaBTree f) ) << f) x

let hyloBTree a c x = (cataBTree a << anaBTree c) x

// (3) Map ---------------------------------------------------------------------

let fmap f x = (cataBTree ( inBTree << baseBTree f id )) x

// (4) Examples ----------------------------------------------------------------

// (4.1) Inversion (mirror) ----------------------------------------------------

let invBTree x =  cataBTree (inBTree << (id -|- (id >< swap))) x

// (4.2) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------

let inord y = 
        let join(x,(l,r))=l@[x]@r
        in either nil join y
  

let inordt x = cataBTree (inord) x

let preord x = 
           let f(x,(l,r))=x::l@r
           in (either nil f) x

let preordt x = cataBTree preord x

let postordt x = 
        let f(x,(l,r))=l@r@[x]
        in cataBTree (either nil f) x

// (4.4) Quicksort -------------------------------------------------------------

let rec part p li =
       match li with
       |[] -> ([],[])
       |(h::t) -> if not(p h) then let (s,l) = part p t in (h::s,l) else let (s,l) = part p t in (s,h::l) 


let qsep li =
    match li with
    | [] -> i1 ()
    | (h::t) -> i2(h,(part ((<) h) t) )

let qSort x = hyloBTree inord qsep x

// (4.5) Traces ----------------------------------------------------------------

let tunion(a,(l,r)) = (List.map (List.append [a]) l)@(List.map(List.append [a]) r) 

let traces x = cataBTree (either (konst [[]]) tunion) x

// (4.6) Towers of Hanoi -------------------------------------------------------

let present x = inord x

let strategy (d,x) = 
        match x with
        |0 -> Left ()
        |_ -> Right ((x-1,d),((not d,x-1),(not d,x-1)))

let hanoi x = hyloBTree present strategy x

// (5) Depth and balancing (using mutual recursion) --------------------------


let baldepth x = 
        let f((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2)) 
        let h(a,((b1,b2),(d1,d2))) = (b1 && b2 && abs(d1-d2)<=1,1+max d1 d2)
        let g x = either (konst(true,1)) (h<<(id><f)) x 
        in cataBTree g x

let depthBTree x = p2(baldepth x)
let balBTree x = p1(baldepth x)
\end{verbatim}

%----------------- Fim do anexo com soluções dos alunos ------------------------%

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
