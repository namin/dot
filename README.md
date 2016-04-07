Dependent Object Types (DOT)
============================

The DOT calculus proposes a new type-theoretic foundation for languages like Scala.
The latest rules ([PDF](http://lampwww.epfl.ch/~amin/dot/current_rules.pdf)) are for a small-step variant
with full subtyping lattice, recursive types including their subtyping and dependent method types.
Here is the corresponding [mechanized soundness proof](https://github.com/TiarkRompf/minidot/blob/master/dev2016/dot.v).

Historical development:
- WadlerFest'16 ([PDF](http://infoscience.epfl.ch/record/215280/files/paper_1.pdf), [code](http://wadlerfest.namin.net))
- _From F to DOT_ ([PDF](http://arxiv.org/pdf/1510.05216.pdf), [**code**](http://github.com/TiarkRompf/minidot))
- OOPSLA'14 ([PDF](http://lampwww.epfl.ch/~amin/dot/fpdt_post.pdf), [code](http://oopsla14.namin.net))
- FOOL'12 ([PDF](http://lampwww.epfl.ch/~amin/dot/fool.pdf), [code](https://github.com/namin/dot/tree/fool))
