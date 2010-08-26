#lang scribble/doc
@(require scribble/base
          scribble/manual
          (for-syntax racket/base racket/path)
          (for-label scribble/base))

@title[#:tag "data"]{Data Structures}

@defmodule[data]

This manual documents data structure libraries available in the
@racketmodname[data] collection.

@local-table-of-contents[#:style 'immediate-only]

@;{--------}

@include-section["queue.scrbl"]
@include-section["skip-list.scrbl"]
@include-section["interval-map.scrbl"]

