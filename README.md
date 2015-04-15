# logic220
Implementations of some material in Moschovakis' notes for UCLA Logic courses 220 A/B/C

PrimRec.hs gives syntax and semantics for a small language for specifying primitive recursive functions http://en.wikipedia.org/wiki/Primitive_recursive_function as well as a few examples. The examples have QuickCheck tests in PrimRecTests.hs

DepTypes.hs contains some useful constructions for sneaking dependent types ala Idris into Haskell, which are used extensively in PrimRec.hs to make ill-formed terms difficult (impossible?) to write down.
