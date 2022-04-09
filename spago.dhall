{ name = "cp-next"
, dependencies =
  [ "aff"
  , "ansi"
  , "arrays"
  , "bifunctors"
  , "console"
  , "control"
  , "datetime"
  , "effect"
  , "either"
  , "exceptions"
  , "foldable-traversable"
  , "free"
  , "identity"
  , "lists"
  , "math"
  , "maybe"
  , "newtype"
  , "node-buffer"
  , "node-fs"
  , "node-fs-aff"
  , "node-path"
  , "node-readline"
  , "now"
  , "numbers"
  , "ordered-collections"
  , "parsing"
  , "partial"
  , "prelude"
  , "purescript-js-ast"
  , "spec"
  , "strings"
  , "transformers"
  , "tuples"
  , "unicode"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
