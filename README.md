Dependent Object Types (DOT)
============================

The DOT calculus proposes a new type-theoretic foundation for languages like Scala.
The latest rules ([PDF](http://lampwww.epfl.ch/~amin/dot/current_rules.pdf)) are for a small-step storeless variant
with full subtyping lattice, recursive types including their subtyping, and dependent method types.
Here is the corresponding [mechanized soundness proof](https://github.com/TiarkRompf/minidot/blob/master/dev2016/dot_storeless_tidy.v).

From F to DOT in Small-Step:
- [F<sub>&lt;:</sub>](https://github.com/samuelgruetter/dot-calculus/blob/master/stable/Fsub.v)
- [F<sub>&lt;:&gt;</sub>](https://github.com/samuelgruetter/dot-calculus/blob/master/stable/FsubL_alt.v)
- [D<sub>&lt;:</sub>](https://github.com/samuelgruetter/dot-calculus/blob/master/stable/Dsub.v)
- [D<sub>&lt;:&gt;</sub>](https://github.com/samuelgruetter/dot-calculus/blob/master/stable/Dsubsup.v)
- [D<sub>&lt;&gt;</sub>](https://github.com/samuelgruetter/dot-calculus/blob/master/stable/Ddia.v)
- [DOT](https://github.com/TiarkRompf/minidot/blob/master/dev2016/dot_storeless_tidy.v)

Historical development:
- OOPSLA'16 ([PDF](http://lampwww.epfl.ch/~amin/dot/soundness_oopsla16.pdf), [code](http://oopsla16.namin.net))
- WadlerFest'16 ([PDF](http://infoscience.epfl.ch/record/215280/files/paper_1.pdf), [code](http://wadlerfest.namin.net))
- _From F to DOT_ ([PDF](http://arxiv.org/pdf/1510.05216.pdf), [code](http://github.com/TiarkRompf/minidot))
- OOPSLA'14 ([PDF](http://lampwww.epfl.ch/~amin/dot/fpdt_post.pdf), [code](http://oopsla14.namin.net))
- FOOL'12 ([PDF](http://lampwww.epfl.ch/~amin/dot/fool.pdf), [code](https://github.com/namin/dot/tree/fool))
