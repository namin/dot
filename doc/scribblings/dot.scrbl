#lang scribble/sigplan @10pt @preprint

@(require
  scriblib/footnote
  scribble/manual
  scriblib/figure
  scribble/core
  racket/base
  (only-in racket/string string-join)
  redex
  "../../src/redex/dot.rkt"
  "typesetting.rkt")

@title{DOT}

@authorinfo["Nada Amin" "EPFL" "nada.amin@epfl.ch"]

@abstract{Dependent Object Types...}

@section{Calculus}

@figure*["f:os" @elem{Operational Semantics}]{
  @para{
   @(dot-judgment-form red #f)
  }
}

@figure*["f:typing" @elem{Typing}]{
  @para{
   @(dot-judgment-form typeof #f)
  }
  @para{
   @(dot-judgment-form typeok #f)
  }
}

@figure*["f:subtyping" @elem{Subtyping}]{
  @para{
   @(dot-metafunction is_subtype #f)
  }
}

@figure*["f:mem" @elem{Membership}]{
  @para{
   @(dot-metafunctions membership-type-lookup membership-value-lookup membership-method-lookup #f)
  }
}

@figure*["f:exp" @elem{Expansion}]{
  @para{
   @(dot-judgment-form expansion #f)
  }
  @para{
   @(dot-judgment-form expansion-iter #f)
  }
  @para{
   @(dot-judgment-form expansion-fix #f)
  }
}

@figure*["f:wf" @elem{Well-Formedness}]{
  @para{
   @(dot-metafunction is_wf-type #f)
  }
}