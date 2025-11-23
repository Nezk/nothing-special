# Nothing Special

Yet another typechecker for a dependently typed language.

The primary ambition behind this project was to slightly blur the boundary between typechecking and syntax checking — i.e., making the expression syntax as correct as the host language’s type system (Haskell in this case) allows. The obvious approach here is to use GHC's type-level extensions. However, after many battles, I couldn't write something I would like with NbE. Well-scopedness is, of course, a nice property, you can see an example of NbE with well-scoped syntax [here](https://github.com/sweirich/lambda-n-ways/blob/main/lib/NBE/KovacsScoped2.hs) (though that is only for untyped lambdas). I decided not to use any type-level stuff in this implementation.

Aside from correctness, I like the syntactic separation between checkable and inferable terms, which I first saw in the paper *A Tutorial Implementation of a Dependently Typed Lambda Calculus* by Andres Löh, Conor McBride, and Wouter Swierstra (It would be interesting to discover examples of such separation elsewhere.)

```haskell
data CExp
    = Lam    LName CExp 
    | Inf    IExp 
    | LetC   LName CExp IExp CExp
    | Pair   CExp CExp 
    | Refl 
    | Contra CExp
    | Hole   HName       
    deriving Show

data IExp
    = U Ul
    | Pi    LName IExp IExp 
    | LetI  LName CExp IExp IExp 
    | Spine (Spine (Glob Ix) (Glob CExp))
    | Sigma LName IExp IExp 
    | Fst   IExp 
    | Snd   IExp
    | Nat 
    | Zero 
    | Succ  CExp 
    | Ind   Ul   CExp CExp CExp CExp
    | Eql   IExp CExp CExp 
    | J     IExp CExp Ul   CExp CExp CExp CExp
    deriving Show
```

One particular design choice has resulted in a rather restrictive syntax for function application, implemented via a `Spine` datatype.

```haskell
-- In bidirectional type checking, lambda expressions are checkable terms. 
-- The head of application spines must be inferable.
data Spine i e 
    = Head i 
    | App (Spine i e) e 
    deriving (Show, Functor)
```

The syntax strictly forbids applying arguments to non-variables. A construction such as `(λx. body) arg` is structurally impossible. In a bidirectional typechecking, a lambda abstraction is a checkable term. The head of an application spine must be inferable, and there is no other term which can be the head of application spine besides variable referencing lambda.

Variables are introduced via lambdas or `let` bindings. Since `let` expressions can appear in both checkable and inferable contexts, the syntax includes two variants: `LetC` and `LetI`. This duplication is, I admit, inelegant.

In the definition of `IExp`, one observes:
```haskell
| Spine (Spine (Glob Ix) (Glob CExp))
```
The `Glob` wrapper allows to distinguish between global definitions and local variables/terms. 

Values and normalised expressions cannot contain spines headed by a global reference that has not been evaluated — globals are looked up in the environment. However, if the head is a local variable (represented as a level in values and an index in normalised forms), the arguments of spine could be still refer to global definitions without being unfloded.

```haskell
data Neutral i e
    -- We shouldn't evaluate globals if the head of spine is neutral
    = NeSpine                 (Spine i (Glob e))
    | …
    -- If the hole is applied (for example, when typechecking J and the motive is a hole), 
    -- the head of the spine is the name of the hole, and the arguments are inside the spine.
    | NeHole                  (Spine HName (Glob e)) 
```

```haskell
data Val
    = …
    | VNeut  (Neutral Lv Val)
    | …
```    

```haskell
data NExp
    = …
    | NNeut  (Neutral Ix NExp)
    | …
```

What I haven't (yet) figured out is a nice way to express syntactically that not every expression can appear on the right side of `:`. Expressions like `n : 3` or `f : \x ...` are impossible. The separation must happen at the value level (because the terms are checked against evaluated types), and I don't know if there are theoretical obstacles to this (I don't see any; it should be implemented by simply embedding one datatype into another, but I might be wrong).

Overall, I don't know how to judge the success of this whole endeavour. I wouldn't have posted the code on GitHub at all if it weren't for my burning desire to deliver the following message to one of GitHub's users: 

**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**
**<div align="center">КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?&nbsp;&nbsp;&nbsp;&nbsp;КОЛЯ, КУДА ТЫ ПРОПАЛ!?</div>**

*<div align="center">End of message</div>*