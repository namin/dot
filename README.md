Dependent Object Types (DOT)
============================

The DOT calculus proposes a new foundation for Scala's type system.

The current model is presented in a paper
([PDF](http://lampwww.epfl.ch/~amin/dot/fool.pdf)) accepted to the
[FOOL 2012 workshop](http://www.cs.uwm.edu/~boyland/fool2012/).

The current model has been implemented in
[Coq](https://github.com/namin/dot/tree/master/src/coq) and
[PLT Redex](https://github.com/namin/dot/tree/master/src/redex). The
OTT and Scala models are out-of-date.

We are developing a proof of type-safety based on step-indexed logical
relations. The current sketch of type-safety
([PDF](http://lampwww.epfl.ch/~amin/dot/type_safety.pdf)) is still
unchecked.
