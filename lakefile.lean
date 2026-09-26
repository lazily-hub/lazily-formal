import Lake
open Lake DSL

package lazily_formal where
  license := "Apache-2.0"
  licenseFiles := #["LICENSE", "NOTICE"]

@[default_target]
lean_lib LazilyFormal where
